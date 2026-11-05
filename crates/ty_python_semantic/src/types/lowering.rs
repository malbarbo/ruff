//! Queries that tell the spython compiler the shape of each value.
//!
//! Every answer is a plain enum of the compiler's own, so the compiler never
//! names a type of ty and never compares printed names.

use ruff_db::files::File;
use ruff_python_ast as ast;
use ruff_text_size::{Ranged, TextRange};
use ty_python_core::{place_table, semantic_index};

use crate::semantic_model::{HasType, SemanticModel};
use crate::types::class::CodeGeneratorKind;
use crate::types::enums::enum_metadata;
use crate::types::literal::LiteralValueTypeKind;
use crate::types::set_theoretic::KnownUnion;
use crate::types::{ClassBase, ClassLiteral, ClassType, KnownClass, Type};
use crate::{Db, ProgramEnvironment};

/// A class, named by where it is defined.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClassId {
    pub file: File,
    pub range: TextRange,
    pub name: String,
    pub known: Option<KnownClass>,
}

/// A function, named by where it is defined.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefId {
    pub file: File,
    pub range: TextRange,
    pub name: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Shape {
    Int,
    IntLit(i64),
    /// `float`, and the `int | float` that ty reads `float` as.
    Float,
    Bool,
    BoolLit(bool),
    Str,
    StrLit(String),
    None,
    List(Box<Shape>),
    Dict(Box<Shape>, Box<Shape>),
    Set(Box<Shape>),
    Tuple(Vec<Shape>),
    TupleOf(Box<Shape>),
    Instance(ClassId, Vec<Shape>),
    Class(ClassId),
    EnumMember(ClassId, String),
    Function(DefId),
    BoundMethod(Box<Shape>, DefId),
    Callable(Vec<Shape>, Box<Shape>),
    TypeVar(String),
    Union(Vec<Shape>),
    Module(String),
    Never,
    Any,
    Other(String),
}

pub struct Param {
    pub name: String,
    pub shape: Shape,
    pub has_default: bool,
}

pub struct FunctionInfo {
    pub id: DefId,
    pub params: Vec<Param>,
    pub ret: Shape,
}

pub struct Method {
    pub name: String,
    pub def: Option<DefId>,
    /// The nearest class up the MRO that also defines the method.
    pub overrides: Option<ClassId>,
}

pub struct Field {
    pub name: String,
    pub shape: Shape,
    pub has_default: bool,
}

pub struct ClassInfo {
    pub id: ClassId,
    pub mro: Vec<ClassId>,
    pub methods: Vec<Method>,
    /// Attributes bound on `self` in a method of this class, in the order of
    /// first binding.
    pub instance_attributes: Vec<Field>,
    pub dataclass_fields: Option<Vec<Field>>,
    pub enum_members: Option<Vec<(String, Shape)>>,
    pub match_args: Option<Vec<String>>,
}

pub enum CallTarget {
    Function(DefId),
    /// A method looked up on the receiver; `class` is where the lookup found it.
    Method {
        receiver: Shape,
        class: ClassId,
        def: DefId,
    },
    Constructor(ClassId),
    Other(Shape),
}

pub struct ArgBinding {
    pub parameter: Option<usize>,
    pub parameter_name: Option<String>,
    pub parameter_shape: Option<Shape>,
}

/// The shape of `expr` at the point where it appears, after narrowing.
pub fn expr_shape(model: &SemanticModel<'_>, expr: &ast::Expr) -> Option<Shape> {
    let ty = expr.inferred_type(model)?;
    Some(shape(model.db(), &model.program_environment(), ty))
}

/// The shape that the annotation of `ann` declares.
pub fn declared_shape(model: &SemanticModel<'_>, ann: &ast::StmtAnnAssign) -> Option<Shape> {
    let db = model.db();
    let index = semantic_index(db, model.program_file());
    let ty =
        index.definitions(ann).iter().find_map(|def| {
            match crate::types::inferred_declaration(db, *def) {
                crate::types::infer::InferredDeclaration::Declared(t) => Some(t.inner_type()),
                crate::types::infer::InferredDeclaration::Rejected => None,
            }
        })?;
    Some(shape(db, &model.program_environment(), ty))
}

/// The declared shape of the place that the assignment target `target`
/// binds: the annotation of the variable, or the declared type of the
/// attribute. `None` when nothing declares the place.
pub fn slot_shape(model: &SemanticModel<'_>, target: &ast::Expr) -> Option<Shape> {
    let db = model.db();
    let env = model.program_environment();
    match target {
        ast::Expr::Name(name) => {
            let index = semantic_index(db, model.program_file());
            let def = *index.definitions(name).first()?;
            let use_def = ty_python_core::use_def_map(db, def.scope(db));
            let declared = crate::place::place_from_declarations(
                db,
                &env,
                use_def.declarations_at_binding(def),
            )
            .ignore_conflicting_declarations();
            let ty = declared.place.ignore_possibly_undefined()?;
            Some(shape(db, &env, ty))
        }
        ast::Expr::Attribute(attr) => {
            let receiver = attr.value.inferred_type(model)?;
            let ty = receiver
                .member(db, &env, attr.attr.as_str())
                .place
                .ignore_possibly_undefined()?;
            Some(shape(db, &env, ty))
        }
        _ => None,
    }
}

pub fn function_info(
    model: &SemanticModel<'_>,
    def: &ast::StmtFunctionDef,
) -> Option<FunctionInfo> {
    let db = model.db();
    let env = model.program_environment();
    let Type::FunctionLiteral(f) = def.inferred_type(model)? else {
        return None;
    };
    let sig = f.signature(db);
    let overload = sig.overloads.iter().next()?;
    let params = overload
        .parameters()
        .iter()
        .map(|p| Param {
            name: p.name().map(ToString::to_string).unwrap_or_default(),
            shape: shape(db, &env, p.annotated_type()),
            has_default: p.default_type(db).is_some(),
        })
        .collect();
    Some(FunctionInfo {
        id: def_id(db, f.definition(db), f.name(db).as_str()),
        params,
        ret: shape(db, &env, overload.return_ty),
    })
}

pub fn class_info(model: &SemanticModel<'_>, def: &ast::StmtClassDef) -> Option<ClassInfo> {
    let db = model.db();
    let env = model.program_environment();
    let Type::ClassLiteral(class) = def.inferred_type(model)? else {
        return None;
    };
    let mro: Vec<ClassLiteral> = class
        .iter_mro(db)
        .filter_map(|base| match base {
            ClassBase::Class(c) => Some(c.class_literal(db)),
            _ => None,
        })
        .collect();

    let static_class = class.as_static()?;
    let body = static_class.body_scope(db);
    let mut methods = Vec::new();
    for stmt in &def.body {
        if let ast::Stmt::FunctionDef(f) = stmt {
            let name = f.name.to_string();
            let overrides = mro[1..]
                .iter()
                .find(|c| defines(db, **c, &name))
                .map(|c| class_id(db, *c));
            let id = match f.inferred_type(model) {
                Some(Type::FunctionLiteral(ft)) => Some(def_id(db, ft.definition(db), &name)),
                _ => None,
            };
            methods.push(Method {
                name,
                def: id,
                overrides,
            });
        }
    }

    // `self.x = ...` in any method: the attributes live in the scopes of the
    // methods, as members of `self`.
    let index = semantic_index(db, model.program_file());
    let mut instance_attributes = Vec::new();
    let file_scope = body.file_scope_id(db);
    for child in index.child_scopes(file_scope) {
        let (child_id, _) = child;
        for member in index
            .place_table(child_id)
            .defined_instance_attribute_names()
        {
            let name = member.to_string();
            if instance_attributes.iter().any(|f: &Field| f.name == name) {
                continue;
            }
            let ty = Type::instance(db, &env, ClassType::NonGeneric(class))
                .member(db, &env, &name)
                .place
                .ignore_possibly_undefined()
                .unwrap_or(Type::unknown());
            instance_attributes.push(Field {
                name,
                shape: shape(db, &env, ty),
                has_default: false,
            });
        }
    }

    let dataclass_fields = match CodeGeneratorKind::from_class(db, class) {
        Some(kind @ CodeGeneratorKind::DataclassLike(_)) => Some(
            static_class
                .fields(db, None, kind)
                .iter()
                .map(|(name, field)| Field {
                    name: name.to_string(),
                    shape: shape(db, &env, field.declared_ty),
                    has_default: !field.is_required(),
                })
                .collect(),
        ),
        _ => None,
    };

    let enum_members = enum_metadata(db, class).map(|meta| {
        meta.members
            .iter()
            .map(|(name, value)| (name.to_string(), shape(db, &env, *value)))
            .collect()
    });

    let match_args = Type::ClassLiteral(class)
        .member(db, &env, "__match_args__")
        .place
        .ignore_possibly_undefined()
        .and_then(|ty| match shape(db, &env, ty) {
            Shape::Tuple(items) => Some(
                items
                    .into_iter()
                    .filter_map(|s| match s {
                        Shape::StrLit(s) => Some(s),
                        _ => None,
                    })
                    .collect(),
            ),
            _ => None,
        });

    Some(ClassInfo {
        id: class_id(db, class),
        mro: mro.iter().map(|c| class_id(db, *c)).collect(),
        methods,
        instance_attributes,
        dataclass_fields,
        enum_members,
        match_args,
    })
}

pub fn call_target(model: &SemanticModel<'_>, call: &ast::ExprCall) -> Option<CallTarget> {
    let db = model.db();
    let env = model.program_environment();
    let callee = call.func.inferred_type(model)?;
    Some(match callee {
        Type::FunctionLiteral(f) => {
            CallTarget::Function(def_id(db, f.definition(db), f.name(db).as_str()))
        }
        Type::BoundMethod(m) => {
            let f = m.function(db)?;
            let def = f.definition(db);
            CallTarget::Method {
                receiver: shape(db, &env, m.self_instance(db)),
                class: index_class_of(db, def)?,
                def: def_id(db, def, f.name(db).as_str()),
            }
        }
        Type::ClassLiteral(c) => CallTarget::Constructor(class_id(db, c)),
        Type::GenericAlias(a) => {
            CallTarget::Constructor(class_id(db, ClassLiteral::Static(a.origin(db))))
        }
        other => CallTarget::Other(shape(db, &env, other)),
    })
}

/// For each argument of `call`, the parameter that takes it, with the
/// parameter's type after the call specializes it.
pub fn call_bindings(model: &SemanticModel<'_>, call: &ast::ExprCall) -> Option<Vec<ArgBinding>> {
    let db = model.db();
    let env = model.program_environment();
    let details = crate::types::ide_support::resolved_call_signature(model, call)?;
    Some(
        details
            .argument_to_parameter_mapping
            .iter()
            .map(|m| {
                let index = m.parameters.first().map(|p| p.index);
                let param = index.and_then(|i| details.parameters.get(i));
                ArgBinding {
                    parameter: index,
                    parameter_name: param.map(|p| p.name.clone()),
                    parameter_shape: param.map(|p| shape(db, &env, p.ty)),
                }
            })
            .collect(),
    )
}

/// The class up the MRO of the receiver that defines `attr.attr`.
pub fn attribute_owner(model: &SemanticModel<'_>, attr: &ast::ExprAttribute) -> Option<ClassId> {
    let db = model.db();
    let env = model.program_environment();
    let receiver = attr.value.inferred_type(model)?;
    let class = match receiver {
        Type::NominalInstance(i) => i.class(db, &env).class_literal(db),
        Type::ClassLiteral(c) => c,
        _ => return None,
    };
    let name = attr.attr.as_str();
    let index_owner = class
        .iter_mro(db)
        .filter_map(|b| match b {
            ClassBase::Class(c) => Some(c.class_literal(db)),
            _ => None,
        })
        .find(|c| defines(db, *c, name) || defines_on_self(db, *c, name))?;
    Some(class_id(db, index_owner))
}

fn defines(db: &dyn Db, class: ClassLiteral<'_>, name: &str) -> bool {
    let Some(s) = class.as_static() else {
        return false;
    };
    let table = place_table(db, s.body_scope(db));
    table
        .symbol_id(name)
        .is_some_and(|id| table.symbol(id).is_bound() || table.symbol(id).is_declared())
}

fn defines_on_self(db: &dyn Db, class: ClassLiteral<'_>, name: &str) -> bool {
    let Some(s) = class.as_static() else {
        return false;
    };
    let body = s.body_scope(db);
    let index = semantic_index(db, body.program_file(db));
    index
        .child_scopes(body.file_scope_id(db))
        .any(|(child, _)| {
            index
                .place_table(child)
                .defined_instance_attribute_names()
                .any(|m| m == name)
        })
}

fn index_class_of(db: &dyn Db, def: ty_python_core::definition::Definition<'_>) -> Option<ClassId> {
    let scope = def.scope(db);
    let index = semantic_index(db, scope.program_file(db));
    let class_node = scope.node(db).as_class()?;
    let class_def = index.expect_single_definition(class_node);
    match crate::types::binding_type(db, class_def) {
        Type::ClassLiteral(c) => Some(class_id(db, c)),
        _ => None,
    }
}

fn class_id(db: &dyn Db, class: ClassLiteral<'_>) -> ClassId {
    ClassId {
        file: class.file(db),
        range: class.header_range(db),
        name: class.name(db).to_string(),
        known: class.known(db),
    }
}

fn def_id(db: &dyn Db, def: ty_python_core::definition::Definition<'_>, name: &str) -> DefId {
    let file = def.file(db);
    let module = ruff_db::parsed::parsed_module(db, def.scope(db).python_file(db)).load(db);
    DefId {
        file,
        range: def.focus_range(db, &module).range(),
        name: name.to_string(),
    }
}

fn shape<'db>(db: &'db dyn Db, env: &ProgramEnvironment<'db>, ty: Type<'db>) -> Shape {
    match ty {
        Type::LiteralValue(lit) => match lit.kind() {
            LiteralValueTypeKind::Int(i) => Shape::IntLit(i.as_i64()),
            LiteralValueTypeKind::Bool(b) => Shape::BoolLit(b),
            LiteralValueTypeKind::String(s) => Shape::StrLit(s.value(db).to_string()),
            LiteralValueTypeKind::LiteralString => Shape::Str,
            LiteralValueTypeKind::Enum(e) => {
                Shape::EnumMember(class_id(db, e.enum_class(db)), e.name(db).to_string())
            }
            LiteralValueTypeKind::Bytes(_) => Shape::Other("bytes".into()),
        },
        Type::NominalInstance(inst) => {
            let class = inst.class(db, env);
            let args: Vec<Shape> = match class {
                ClassType::Generic(alias) => alias
                    .specialization(db)
                    .types(db)
                    .iter()
                    .map(|t| shape(db, env, *t))
                    .collect(),
                ClassType::NonGeneric(_) => Vec::new(),
            };
            let arg = |i: usize| Box::new(args.get(i).cloned().unwrap_or(Shape::Any));
            match class.known(db) {
                Some(KnownClass::Int) => Shape::Int,
                Some(KnownClass::Float) => Shape::Float,
                Some(KnownClass::Bool) => Shape::Bool,
                Some(KnownClass::Str) => Shape::Str,
                Some(KnownClass::NoneType) => Shape::None,
                Some(KnownClass::List) => Shape::List(arg(0)),
                Some(KnownClass::Set) => Shape::Set(arg(0)),
                Some(KnownClass::Dict) => Shape::Dict(arg(0), arg(1)),
                Some(KnownClass::Tuple) => match inst.tuple_spec(db, env) {
                    Some(spec) => match spec.as_fixed_length() {
                        Some(fixed) => Shape::Tuple(
                            fixed
                                .all_elements()
                                .iter()
                                .map(|t| shape(db, env, *t))
                                .collect(),
                        ),
                        None => Shape::TupleOf(arg(0)),
                    },
                    None => Shape::TupleOf(arg(0)),
                },
                _ => Shape::Instance(class_id(db, class.class_literal(db)), args),
            }
        }
        Type::Union(u) if u.known(db) == Some(KnownUnion::Float) => Shape::Float,
        Type::Union(u) => Shape::Union(u.elements(db).iter().map(|t| shape(db, env, *t)).collect()),
        Type::ClassLiteral(c) => Shape::Class(class_id(db, c)),
        Type::GenericAlias(a) => Shape::Class(class_id(db, ClassLiteral::Static(a.origin(db)))),
        Type::FunctionLiteral(f) => {
            Shape::Function(def_id(db, f.definition(db), f.name(db).as_str()))
        }
        Type::BoundMethod(m) => match m.function(db) {
            Some(f) => Shape::BoundMethod(
                Box::new(shape(db, env, m.self_instance(db))),
                def_id(db, f.definition(db), f.name(db).as_str()),
            ),
            None => Shape::Other(ty.display(db, env).to_string()),
        },
        Type::Callable(c) => {
            let sigs: Vec<_> = c.signatures(db).iter().collect();
            match sigs.as_slice() {
                [sig] => Shape::Callable(
                    sig.parameters()
                        .iter()
                        .map(|p| shape(db, env, p.annotated_type()))
                        .collect(),
                    Box::new(shape(db, env, sig.return_ty)),
                ),
                _ => Shape::Other(ty.display(db, env).to_string()),
            }
        }
        Type::TypeVar(tv) if tv.typevar(db).is_self(db) => {
            match tv.typevar(db).upper_bound(db, env) {
                Some(bound) => shape(db, env, bound),
                None => Shape::TypeVar("Self".into()),
            }
        }
        Type::TypeVar(tv) => Shape::TypeVar(tv.typevar(db).name(db).to_string()),
        Type::ModuleLiteral(_) => Shape::Module(ty.display(db, env).to_string()),
        Type::Never => Shape::Never,
        Type::Dynamic(_) => Shape::Any,
        _ => Shape::Other(ty.display(db, env).to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::db::tests::TestDbBuilder;
    use ruff_db::files::system_path_to_file;
    use ruff_db::parsed::parsed_module;
    use ruff_python_ast::visitor::source_order::{self, SourceOrderVisitor};
    use ty_python_core::ProgramFile;

    fn with_model(source: &str, f: impl FnOnce(&SemanticModel<'_>, &ast::ModModule)) {
        let db = TestDbBuilder::new()
            .with_file("/src/main.py", source)
            .build()
            .unwrap();
        let file = system_path_to_file(&db, "/src/main.py").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let module = parsed_module(&db, file.python_file(&db)).load(&db);
        let model = SemanticModel::new(&db, file);
        f(&model, module.syntax());
    }

    /// The shape of every name `x` that the program reads, in order.
    fn shapes_of(source: &str, name: &str) -> Vec<Shape> {
        struct Names<'a, 'm> {
            model: &'a SemanticModel<'m>,
            name: &'a str,
            found: Vec<Shape>,
        }
        impl<'a> SourceOrderVisitor<'a> for Names<'_, '_> {
            fn visit_expr(&mut self, expr: &'a ast::Expr) {
                if let ast::Expr::Name(n) = expr
                    && n.id.as_str() == self.name
                    && n.ctx.is_load()
                {
                    self.found.push(expr_shape(self.model, expr).unwrap());
                }
                source_order::walk_expr(self, expr);
            }
        }
        let mut found = Vec::new();
        with_model(source, |model, module| {
            let mut names = Names {
                model,
                name,
                found: Vec::new(),
            };
            names.visit_body(&module.body);
            found = names.found;
        });
        found
    }

    fn class_def<'a>(module: &'a ast::ModModule, name: &str) -> &'a ast::StmtClassDef {
        module
            .body
            .iter()
            .find_map(|s| s.as_class_def_stmt().filter(|c| c.name.as_str() == name))
            .unwrap()
    }

    #[test]
    fn builtin_shapes() {
        let source = "\
def f(i: int, x: float, b: bool, s: str, n: None) -> None:
    i; x; b; s; n
";
        assert_eq!(shapes_of(source, "i"), [Shape::Int]);
        assert_eq!(shapes_of(source, "x"), [Shape::Float]);
        assert_eq!(shapes_of(source, "b"), [Shape::Bool]);
        assert_eq!(shapes_of(source, "s"), [Shape::Str]);
        assert_eq!(shapes_of(source, "n"), [Shape::None]);
    }

    #[test]
    fn literals() {
        assert_eq!(shapes_of("a = 3\na", "a"), [Shape::IntLit(3)]);
        assert_eq!(shapes_of("a = 'x'\na", "a"), [Shape::StrLit("x".into())]);
        assert_eq!(shapes_of("a = True\na", "a"), [Shape::BoolLit(true)]);
    }

    #[test]
    fn narrowing_removes_none() {
        let source = "\
def f(r: int | None) -> int:
    if r is None:
        return 0
    return r
";
        assert_eq!(
            shapes_of(source, "r"),
            [Shape::Union(vec![Shape::Int, Shape::None]), Shape::Int]
        );
    }

    #[test]
    fn containers() {
        let source = "\
def f(a: list[int], b: dict[str, int], c: tuple[int, str], d: tuple[int, ...]) -> None:
    a; b; c; d
";
        assert_eq!(shapes_of(source, "a"), [Shape::List(Box::new(Shape::Int))]);
        assert_eq!(
            shapes_of(source, "b"),
            [Shape::Dict(Box::new(Shape::Str), Box::new(Shape::Int))]
        );
        assert_eq!(
            shapes_of(source, "c"),
            [Shape::Tuple(vec![Shape::Int, Shape::Str])]
        );
        assert_eq!(
            shapes_of(source, "d"),
            [Shape::TupleOf(Box::new(Shape::Int))]
        );
    }

    #[test]
    fn user_class_is_named_by_definition() {
        let source = "\
class P: ...
def f(p: P, ps: list[P]) -> None:
    p; ps
";
        let [Shape::Instance(p, args)] = <[Shape; 1]>::try_from(shapes_of(source, "p")).unwrap()
        else {
            panic!()
        };
        assert_eq!(p.name, "P");
        assert!(args.is_empty());
        assert_eq!(
            shapes_of(source, "ps"),
            [Shape::List(Box::new(Shape::Instance(p, vec![])))]
        );
    }

    #[test]
    fn class_with_inheritance() {
        let source = "\
class A:
    def __init__(self, x: int) -> None:
        self.x = x
    def f(self) -> int:
        return self.x
class B(A):
    def __init__(self, x: int, y: int) -> None:
        super().__init__(x)
        self.y = y
    def f(self) -> int:
        return self.y
";
        with_model(source, |model, module| {
            let info = class_info(model, class_def(module, "B")).unwrap();
            let mro: Vec<_> = info.mro.iter().map(|c| c.name.as_str()).collect();
            assert_eq!(mro, ["B", "A", "object"]);
            assert_eq!(info.mro[2].known, Some(KnownClass::Object));
            let f = info.methods.iter().find(|m| m.name == "f").unwrap();
            assert_eq!(f.overrides.as_ref().unwrap().name, "A");
            let attrs: Vec<_> = info
                .instance_attributes
                .iter()
                .map(|a| a.name.as_str())
                .collect();
            assert_eq!(attrs, ["y"]);
        });
    }

    #[test]
    fn dataclass_fields_and_match_args() {
        let source = "\
from dataclasses import dataclass
@dataclass
class P:
    x: int
    y: float = 0.0
";
        with_model(source, |model, module| {
            let info = class_info(model, class_def(module, "P")).unwrap();
            let fields = info.dataclass_fields.unwrap();
            let fields: Vec<_> = fields
                .iter()
                .map(|f| (f.name.as_str(), f.shape.clone(), f.has_default))
                .collect();
            assert_eq!(
                fields,
                [("x", Shape::Int, false), ("y", Shape::Float, true)]
            );
            assert_eq!(info.match_args.unwrap(), ["x", "y"]);
        });
    }

    #[test]
    fn enum_members() {
        let source = "\
from enum import Enum
class Cor(Enum):
    AZUL = 1
    VERDE = 2
c = Cor.VERDE
c
";
        with_model(source, |model, module| {
            let info = class_info(model, class_def(module, "Cor")).unwrap();
            assert_eq!(
                info.enum_members.unwrap(),
                [
                    ("AZUL".to_string(), Shape::IntLit(1)),
                    ("VERDE".to_string(), Shape::IntLit(2))
                ]
            );
        });
        let [Shape::EnumMember(class, member)] =
            <[Shape; 1]>::try_from(shapes_of(source, "c")).unwrap()
        else {
            panic!()
        };
        assert_eq!((class.name.as_str(), member.as_str()), ("Cor", "VERDE"));
    }

    #[test]
    fn function_signature() {
        let source = "def f(a: int, b: str = 'x') -> list[int]: ...";
        with_model(source, |model, module| {
            let def = module.body[0].as_function_def_stmt().unwrap();
            let info = function_info(model, def).unwrap();
            let params: Vec<_> = info
                .params
                .iter()
                .map(|p| (p.name.as_str(), p.shape.clone(), p.has_default))
                .collect();
            assert_eq!(params, [("a", Shape::Int, false), ("b", Shape::Str, true)]);
            assert_eq!(info.ret, Shape::List(Box::new(Shape::Int)));
            assert_eq!(info.id.name, "f");
        });
    }

    #[test]
    fn call_targets_and_bindings() {
        let source = "\
class A:
    def m(self, k: int) -> int:
        return k
def f(x: int) -> A:
    return A()
f(1).m(k=2)
";
        with_model(source, |model, module| {
            let ast::Stmt::Expr(stmt) = &module.body[2] else {
                panic!()
            };
            let outer = stmt.value.as_call_expr().unwrap();
            let Some(CallTarget::Method { class, def, .. }) = call_target(model, outer) else {
                panic!()
            };
            assert_eq!((class.name.as_str(), def.name.as_str()), ("A", "m"));
            let bindings = call_bindings(model, outer).unwrap();
            assert_eq!(bindings[0].parameter_name.as_deref(), Some("k"));
            assert_eq!(bindings[0].parameter_shape, Some(Shape::Int));

            let ast::Expr::Attribute(attr) = &*outer.func else {
                panic!()
            };
            let inner = attr.value.as_call_expr().unwrap();
            let Some(CallTarget::Function(def)) = call_target(model, inner) else {
                panic!()
            };
            assert_eq!(def.name, "f");
            assert_eq!(attribute_owner(model, attr).unwrap().name, "A");
        });
    }

    #[test]
    fn slot_shape_is_the_declared_type() {
        let source = "\
class A: ...
class B(A): ...
q: A = B()
q = B()
";
        with_model(source, |model, module| {
            let ast::Stmt::Assign(assign) = &module.body[3] else {
                panic!()
            };
            let Some(Shape::Instance(class, _)) = slot_shape(model, &assign.targets[0]) else {
                panic!()
            };
            assert_eq!(class.name, "A");
        });
    }

    #[test]
    fn generic_function_call_is_specialized() {
        let source = "\
def first[T](xs: list[T]) -> T:
    return xs[0]
a = first([1, 2])
a
";
        assert_eq!(shapes_of(source, "a"), [Shape::Int]);
    }
}
