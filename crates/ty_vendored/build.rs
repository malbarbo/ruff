//! Build script to package our vendored typeshed files
//! into a zip archive that can be included in the Ruff binary.
//!
//! This script should be automatically run at build time
//! whenever the script itself changes, or whenever any files
//! in `crates/ty_vendored/vendor/typeshed` change.

use std::fs::File;
use std::io::Write;
use std::path::Path;

use path_slash::PathExt;
use zip::CompressionMethod;
use zip::result::ZipResult;
use zip::write::{FileOptions, ZipWriter};

const TYPESHED_SOURCE_DIR: &str = "vendor/typeshed";
const TY_EXTENSIONS_STUBS: &str = "ty_extensions/ty_extensions.pyi";
const TYPESHED_ZIP_LOCATION: &str = "/zipped_typeshed.zip";

/// Recursively zip the contents of the entire typeshed directory and patch typeshed
/// on the fly to include the `ty_extensions` module.
///
/// This routine is adapted from a recipe at
/// <https://github.com/zip-rs/zip-old/blob/5d0f198124946b7be4e5969719a7f29f363118cd/examples/write_dir.rs>
fn write_zipped_typeshed_to(writer: File) -> ZipResult<File> {
    let mut zip = ZipWriter::new(writer);

    let method = if cfg!(feature = "deflate") {
        CompressionMethod::Deflated
    } else {
        CompressionMethod::Stored
    };

    let options = FileOptions::default()
        .compression_method(method)
        .compression_level(Some(9))
        .unix_permissions(0o644);

    // If TYPESHED_ALLOWLIST is set, only include stubs listed in that file.
    // Each line is a module name (e.g., "builtins", "os.path").
    // Special files (VERSIONS, @tests/) and ty_extensions are always included.
    let allowlist: Option<std::collections::HashSet<String>> =
        std::env::var("TYPESHED_ALLOWLIST")
            .ok()
            .map(|path| {
                println!("cargo:rerun-if-changed={path}");
                std::fs::read_to_string(&path)
                    .unwrap_or_default()
                    .lines()
                    .filter(|l| !l.is_empty() && !l.starts_with('#'))
                    .map(String::from)
                    .collect()
            });

    for entry in walkdir::WalkDir::new(TYPESHED_SOURCE_DIR) {
        let dir_entry = entry.unwrap();
        let absolute_path = dir_entry.path();
        let normalized_relative_path = absolute_path
            .strip_prefix(Path::new(TYPESHED_SOURCE_DIR))
            .unwrap()
            .to_slash()
            .expect("Unexpected non-utf8 typeshed path!");

        // Filter by allowlist if provided
        if let Some(ref allowed) = allowlist {
            if absolute_path.is_file() {
                let rel = normalized_relative_path.as_ref();
                // Always include VERSIONS and @tests
                let dominated = rel == "stdlib/VERSIONS"
                    || rel.starts_with("stdlib/@tests/");
                if !dominated {
                    // Convert path to module name: stdlib/os/__init__.pyi -> os
                    let module = rel
                        .strip_prefix("stdlib/")
                        .unwrap_or(rel)
                        .strip_suffix(".pyi")
                        .unwrap_or(rel)
                        .strip_suffix("/__init__")
                        .unwrap_or(
                            rel.strip_prefix("stdlib/")
                                .unwrap_or(rel)
                                .strip_suffix(".pyi")
                                .unwrap_or(rel),
                        )
                        .replace('/', ".");
                    // Check if this module or any parent is in the allowlist
                    let mut found = false;
                    let mut parts: &str = &module;
                    loop {
                        if allowed.contains(parts) {
                            found = true;
                            break;
                        }
                        match parts.rsplit_once('.') {
                            Some((parent, _)) => parts = parent,
                            None => break,
                        }
                    }
                    if !found {
                        continue;
                    }
                }
            } else if !normalized_relative_path.is_empty() {
                // For directories, check if any allowed module starts with this path
                let dir_module = normalized_relative_path
                    .strip_prefix("stdlib/")
                    .unwrap_or(&normalized_relative_path)
                    .replace('/', ".");
                if !dir_module.is_empty()
                    && !allowed.iter().any(|m| m.starts_with(&*dir_module) || dir_module.starts_with(&**m))
                    && !normalized_relative_path.starts_with("stdlib/@tests")
                    && normalized_relative_path != "stdlib"
                {
                    continue;
                }
            }
        }

        // Write file or directory explicitly
        // Some unzip tools unzip files with directory paths correctly, some do not!
        if absolute_path.is_file() {
            println!("adding file {absolute_path:?} as {normalized_relative_path:?} ...");
            zip.start_file(&*normalized_relative_path, options)?;
            let mut f = File::open(absolute_path)?;
            std::io::copy(&mut f, &mut zip).unwrap();

            // Patch the VERSIONS file to make `ty_extensions` available
            if normalized_relative_path == "stdlib/VERSIONS" {
                writeln!(&mut zip, "ty_extensions: 3.0-")?;
            }
        } else if !normalized_relative_path.is_empty() {
            // Only if not root! Avoids path spec / warning
            // and mapname conversion failed error on unzip
            println!("adding dir {absolute_path:?} as {normalized_relative_path:?} ...");
            zip.add_directory(normalized_relative_path, options)?;
        }
    }

    // Patch typeshed and add the stubs for the `ty_extensions` module
    println!("adding file {TY_EXTENSIONS_STUBS} as stdlib/ty_extensions.pyi ...");
    zip.start_file("stdlib/ty_extensions.pyi", options)?;
    let mut f = File::open(TY_EXTENSIONS_STUBS)?;
    std::io::copy(&mut f, &mut zip).unwrap();

    zip.finish()
}

fn main() {
    assert!(
        Path::new(TYPESHED_SOURCE_DIR).is_dir(),
        "Where is typeshed?"
    );
    let out_dir = std::env::var("OUT_DIR").unwrap();

    // N.B. Deliberately using `format!()` instead of `Path::join()` here,
    // so that we use `/` as a path separator on all platforms.
    // That enables us to load the typeshed zip at compile time in `module.rs`
    // (otherwise we'd have to dynamically determine the exact path to the typeshed zip
    // based on the default path separator for the specific platform we're on,
    // which can't be done at compile time.)
    let zipped_typeshed_location = format!("{out_dir}{TYPESHED_ZIP_LOCATION}");

    let zipped_typeshed_file = File::create(zipped_typeshed_location).unwrap();
    write_zipped_typeshed_to(zipped_typeshed_file).unwrap();
}
