use crate::Db;
use crate::place::{
    ConsideredDefinitions, DefinedPlace, Place, PlaceAndQualifiers, RequiresExplicitReExport,
    TypeOrigin, place_by_id, place_from_bindings, place_from_declarations,
};
use crate::types::enums::is_enum_class_by_inheritance;
use crate::types::{
    KnownClass, ProgramEnvironment, StaticClassLiteral, Type, class::MroLookup,
    infer::nearest_enclosing_class,
};
use ruff_db::parsed::parsed_module;
use ruff_python_ast as ast;
use ty_python_core::{
    definition::DefinitionKind, place_table, scope::ScopeId, semantic_index,
    symbol::ScopedSymbolId, use_def_map,
};

/// The return type of certain member-lookup operations. Contains information
/// about the type, type qualifiers, boundness/declaredness.
#[derive(Debug, Clone, Copy, PartialEq, Eq, get_size2::GetSize, Default, salsa::SalsaValue)]
pub(super) struct Member<'db> {
    /// Type, qualifiers, and boundness information of this member
    pub(super) inner: PlaceAndQualifiers<'db>,
}

impl<'db> Member<'db> {
    pub(super) fn unbound() -> Self {
        Self {
            inner: PlaceAndQualifiers::unbound(),
        }
    }

    pub(super) fn definitely_declared(ty: Type<'db>) -> Self {
        Self {
            inner: Place::declared(ty).into(),
        }
    }

    /// Returns the type qualifiers of this member.
    pub(super) fn qualifiers(&self) -> crate::types::TypeQualifiers {
        self.inner.qualifiers
    }

    /// Returns `true` if the inner place is undefined (i.e. there is no such member).
    pub(super) fn is_undefined(&self) -> bool {
        self.inner.place.is_undefined()
    }

    /// Returns the inner type, unless it is definitely undefined.
    pub(super) fn ignore_possibly_undefined(&self) -> Option<Type<'db>> {
        self.inner.place.ignore_possibly_undefined()
    }

    /// Map a type transformation function over the type of this member.
    #[must_use]
    pub(super) fn map_type(self, f: impl FnOnce(Type<'db>) -> Type<'db>) -> Self {
        Self {
            inner: self.inner.map_type(f),
        }
    }
}

/// A class-body annotation together with the class that declares it.
///
/// The declaring class is retained even when several declarations contribute to the member's
/// type, or an unannotated default inherits the annotation through an intermediate base.
#[derive(Debug, Clone, Copy, PartialEq, Eq, get_size2::GetSize, salsa::SalsaValue)]
pub(crate) struct ClassBodyDeclaration<'db> {
    pub(super) member: PlaceAndQualifiers<'db>,
    pub(super) class: StaticClassLiteral<'db>,
}

/// Infer the public type of a class member/symbol (its type as seen from outside its scope) in the given
/// `scope`.
pub(super) fn class_member<'db>(db: &'db dyn Db, scope: ScopeId<'db>, name: &str) -> Member<'db> {
    class_member_with_symbol(db, scope, place_table(db, scope).symbol_id(name))
}

pub(super) fn class_member_with_symbol<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    symbol: Option<ScopedSymbolId>,
) -> Member<'db> {
    symbol.map_or_default(|symbol_id| {
        let mut place_and_quals = place_by_id(
            db,
            scope,
            symbol_id.into(),
            RequiresExplicitReExport::No,
            ConsideredDefinitions::EndOfScope,
        );

        if let Place::Defined(ref mut place) = place_and_quals.place
            && place.origin == TypeOrigin::Inferred
            && let Some(declaration) = inherited_class_body_declaration(db, scope, symbol_id)
                .map(|inherited| inherited.member)
                .or_else(|| literal_class_body_declaration(db, scope, symbol_id))
        {
            if let Place::Defined(declared) = declaration.place {
                // The annotation determines the public type, but the value is still supplied
                // by this class. Consumers such as Pydantic inspect that value's definition.
                *place = DefinedPlace {
                    ty: declared.ty,
                    origin: declared.origin,
                    public_type_policy: declared.public_type_policy,
                    ..*place
                };
            }
            place_and_quals.qualifiers = declaration.qualifiers;
        }

        if !place_and_quals.is_undefined() && !place_and_quals.is_init_var() {
            // Trust the declared type if we see a class-level declaration
            return Member {
                inner: place_and_quals,
            };
        }

        if let PlaceAndQualifiers {
            place:
                Place::Defined(DefinedPlace {
                    ty,
                    provenance: declared_provenance,
                    ..
                }),
            qualifiers,
        } = place_and_quals
        {
            // Otherwise, we need to check if the symbol has bindings
            let use_def = use_def_map(db, scope);
            let bindings = use_def.end_of_scope_symbol_bindings(symbol_id);
            let env = ProgramEnvironment::from_scope(scope);
            let inferred = place_from_bindings(db, &env, bindings).place;

            // TODO: we should not need to calculate inferred type second time. This is a temporary
            // solution until the notion of Boundness and Declaredness is split. See #16036, #16264
            Member {
                inner: match inferred {
                    Place::Undefined => Place::Undefined.with_qualifiers(qualifiers),
                    Place::Defined(place) => Place::Defined(DefinedPlace {
                        ty,
                        provenance: place.provenance.or(declared_provenance),
                        ..place
                    })
                    .with_qualifiers(qualifiers),
                },
            }
        } else {
            Member::unbound()
        }
    })
}

/// Returns the inherited class-body annotation governing an unannotated class attribute.
///
/// A subclass assignment such as `items = []` retains an inherited `items: list[int]`
/// declaration. Both initializer inference and public member lookup use that declaration,
/// while an explicit annotation or a new method definition supplies its own public type.
#[salsa::tracked(returns(copy), cycle_initial=|_, _, _, _| None, heap_size=ruff_memory_usage::heap_size)]
pub(crate) fn inherited_class_body_declaration<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    symbol: ScopedSymbolId,
) -> Option<ClassBodyDeclaration<'db>> {
    scope.node(db).as_class()?;
    let use_def = use_def_map(db, scope);
    let env = ProgramEnvironment::from_scope(scope);
    if !place_from_declarations(db, &env, use_def.end_of_scope_symbol_declarations(symbol))
        .ignore_conflicting_declarations()
        .is_undefined()
    {
        return None;
    }

    let class = nearest_enclosing_class(db, semantic_index(db, scope.program_file(db)), scope)?;
    let table = place_table(db, scope);
    class_body_declaration_from_bases(db, &env, class, table.symbol(symbol).name())
}

pub(super) fn class_body_declaration_from_bases<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    class: StaticClassLiteral<'db>,
    name: &str,
) -> Option<ClassBodyDeclaration<'db>> {
    let mut inherited = MroLookup::new(
        db,
        env,
        class.identity_specialization(db).iter_mro(db).skip(1),
    )
    .class_body_declaration(name)?;
    // Hash definitions are checked against the hash protocol, not inherited annotations.
    // Retain qualifiers such as `ClassVar`, which still constrain instance assignments.
    if name == "__hash__" {
        inherited.member.place = Place::Undefined;
    }
    Some(inherited)
}

/// Returns the declaration that a literal makes for the class attribute `symbol` of `scope`, or
/// `None` if the literal makes none.
///
/// Under `literal_declarations`, `name = "a"` declares `name: str`, as an annotation would, when
/// it is the only binding of the name in the class body and the body declares nothing for the
/// name. An enum is left out, because its members are literals of the enum, not of `str`.
pub(crate) fn literal_class_body_declaration<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    symbol: ScopedSymbolId,
) -> Option<PlaceAndQualifiers<'db>> {
    let env = ProgramEnvironment::from_scope(scope);
    if !env.program(db).literal_declarations(db) {
        return None;
    }
    scope.node(db).as_class()?;
    if place_table(db, scope).symbol(symbol).is_reassigned() {
        return None;
    }
    let use_def = use_def_map(db, scope);
    if !place_from_declarations(db, &env, use_def.end_of_scope_symbol_declarations(symbol))
        .ignore_conflicting_declarations()
        .is_undefined()
    {
        return None;
    }
    let mut definitions = use_def
        .end_of_scope_symbol_bindings(symbol)
        .filter_map(|binding| binding.binding.definition());
    let definition = definitions.next()?;
    if definitions.next().is_some() {
        return None;
    }
    let DefinitionKind::Assignment(assignment) = definition.kind(db) else {
        return None;
    };
    if assignment.unpack().is_some() {
        return None;
    }
    let module = parsed_module(db, definition.program_file(db).python_file(db)).load(db);
    if !assignment.target(&module).is_name_expr() {
        return None;
    }
    let ty = literal_declared_type(db, &env, assignment.value(&module))?;
    let class = nearest_enclosing_class(db, semantic_index(db, scope.program_file(db)), scope)?;
    if is_enum_class_by_inheritance(db, &env, class) {
        return None;
    }
    Some(Place::declared(ty).with_definition(definition).into())
}

/// Returns the type that `value` declares for a class attribute or the default of a lambda
/// parameter under `literal_declarations`, or `None` if `value` is not one of these literals: a
/// `str`, an `int` or a `float`, with or without a minus, a `bool`, or a tuple, list or set of
/// `str` literals that is not empty.
pub(crate) fn literal_declared_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    value: &ast::Expr,
) -> Option<Type<'db>> {
    let number = |number: &ast::Number| match number {
        ast::Number::Int(_) => Some(KnownClass::Int.to_instance(db, env)),
        ast::Number::Float(_) => Some(KnownClass::Float.to_instance(db, env)),
        ast::Number::Complex { .. } => None,
    };
    let strs = |elts: &[ast::Expr]| {
        (!elts.is_empty() && elts.iter().all(ast::Expr::is_string_literal_expr))
            .then(|| KnownClass::Str.to_instance(db, env))
    };
    match value {
        ast::Expr::StringLiteral(_) => Some(KnownClass::Str.to_instance(db, env)),
        ast::Expr::BooleanLiteral(_) => Some(KnownClass::Bool.to_instance(db, env)),
        ast::Expr::NumberLiteral(literal) => number(&literal.value),
        ast::Expr::UnaryOp(ast::ExprUnaryOp {
            op: ast::UnaryOp::USub,
            operand,
            ..
        }) => match operand.as_ref() {
            ast::Expr::NumberLiteral(literal) => number(&literal.value),
            _ => None,
        },
        ast::Expr::Tuple(tuple) => strs(&tuple.elts)
            .map(|str| Type::heterogeneous_tuple(db, env, vec![str; tuple.elts.len()])),
        ast::Expr::List(list) => {
            strs(&list.elts).map(|str| KnownClass::List.to_specialized_instance(db, env, &[str]))
        }
        ast::Expr::Set(set) => {
            strs(&set.elts).map(|str| KnownClass::Set.to_specialized_instance(db, env, &[str]))
        }
        _ => None,
    }
}
