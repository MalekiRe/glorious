//! Executable specifications are Glorious files, never Rust implementations.
use std::collections::BTreeMap;
use grandiose_stage0::{CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest,
    LogicalPath, PackageKey, SourceInput, StageZeroCompiler};

fn run(source: &str, dependencies: &[&str]) -> i64 {
    let source = format!("{}\n{}", include_str!("../../../stdlib/tests/support.glorious"), source);
    let fragments: Vec<_> = grandiose_stage0::service::STANDARD_LIBRARY_FRAGMENTS.iter().copied()
        .filter(|(path, _)| *path == "src/lib.glorious" || dependencies.contains(path) || dependencies.contains(&"*"))
        .collect();
    for dependency in dependencies {
        assert!(*dependency == "*" || fragments.iter().any(|(path, _)| path == dependency), "unknown library dependency {dependency}");
    }
    let library = fragments.iter().map(|(_, text)| *text).collect::<Vec<_>>().join("\n");
    let library_input = SourceInput::new(PackageKey("std@0.1.0".into()), LogicalPath::parse("src/lib.glorious").unwrap(), library.as_bytes());
    let library_key = library_input.key;
    let app = PackageKey("stdlib-cases@0.1.0".into());
    let request = CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"stdlib-source-cases")),
        mode: CompilationMode::Build,
        root_package: app.clone(),
        sources: vec![
            SourceInput::new(app, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes()),
            library_input,
        ],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(), codegen_options: BTreeMap::new(),
        capability_manifest: vec![], runtime_manifest: None,
    };
    let outcome = StageZeroCompiler::new().compile(request).unwrap_or_else(|error| {
        let summaries: std::collections::BTreeSet<_> = error.diagnostics().iter()
            .map(|diagnostic| {
                let location = diagnostic.primary.as_ref().map(|span| {
                    let mut offset = span.start as usize;
                    if span.file == library_key {
                        for (path, text) in &fragments {
                            if offset <= text.len() {
                                let line = text.as_bytes()[..offset].iter().filter(|byte| **byte == b'\n').count() + 1;
                                return format!("stdlib/{path}:{line}");
                            }
                            offset -= text.len() + 1;
                        }
                    }
                    format!("application byte {}", span.start)
                }).unwrap_or_default();
                format!("{}: {} {location}", diagnostic.code, diagnostic.message)
            }).collect();
        panic!("Glorious source must compile ({} diagnostics):\n{}", error.diagnostics().len(), summaries.into_iter().collect::<Vec<_>>().join("\n"));
    });
    let artifact = outcome.artifact.expect("Glorious source must produce an artifact");
    let program = grandiose_stage0::decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
    // SAFETY: locally compiled fixtures call the trusted source-owned library.
    unsafe { program.run_i64_with_unsafe(Default::default()) }.expect("Glorious case must execute")
}

#[test]
fn foundation() {
    assert_eq!(run(include_str!("../../../stdlib/tests/foundation.glorious"), &["src/foundation.glorious"]), 42);
}

#[test]
fn full_composition() {
    assert_eq!(run(include_str!("../../../stdlib/tests/foundation.glorious"), &["*"]), 42);
}

macro_rules! source_case {
    ($name:ident, $path:literal, $($dependency:literal),+ $(,)?) => {
        #[test]
        fn $name() { assert_eq!(run(include_str!($path), &[$($dependency),+]), 42); }
    };
}
source_case!(binary, "../../../stdlib/tests/binary.glorious", "src/foundation.glorious", "src/binary.glorious");
source_case!(codecs, "../../../stdlib/tests/codecs.glorious", "src/foundation.glorious", "src/integer.glorious", "src/integer_text.glorious", "src/codecs.glorious");
source_case!(heap, "../../../stdlib/tests/heap.glorious", "src/foundation.glorious", "src/algorithm.glorious", "src/heap.glorious", "src/memory.glorious");
source_case!(utf8, "../../../stdlib/tests/utf8.glorious", "src/foundation.glorious", "src/integer.glorious", "src/integer_text.glorious", "src/memory.glorious", "src/array.glorious", "src/utf8.glorious", "src/char_escape.glorious");
source_case!(storage, "../../../stdlib/tests/storage.glorious", "src/foundation.glorious", "src/storage.glorious");
source_case!(source_map, "../../../stdlib/tests/source_map.glorious", "src/foundation.glorious", "src/integer.glorious", "src/integer_text.glorious", "src/memory.glorious", "src/storage.glorious", "src/utf8.glorious", "src/source_map.glorious");
source_case!(format, "../../../stdlib/tests/format.glorious", "src/foundation.glorious", "src/integer.glorious", "src/memory.glorious", "src/array.glorious", "src/char_escape.glorious", "src/format.glorious");
source_case!(integer, "../../../stdlib/tests/integer.glorious", "src/foundation.glorious", "src/integer.glorious");
source_case!(borrowed_text_traits, "../../../stdlib/tests/borrowed_text_traits.glorious", "src/foundation.glorious");
source_case!(integer_text, "../../../stdlib/tests/integer_text.glorious", "src/foundation.glorious", "src/integer.glorious", "src/integer_text.glorious");
source_case!(integer_parse, "../../../stdlib/tests/integer_parse.glorious", "src/foundation.glorious", "src/integer.glorious", "src/integer_text.glorious");
source_case!(time, "../../../stdlib/tests/time.glorious", "src/foundation.glorious", "src/time.glorious");
source_case!(budget, "../../../stdlib/tests/budget.glorious", "src/foundation.glorious", "src/memory.glorious", "src/budget.glorious");
source_case!(random, "../../../stdlib/tests/random.glorious", "src/foundation.glorious", "src/memory.glorious", "src/array.glorious", "src/time.glorious", "src/random.glorious");
source_case!(io, "../../../stdlib/tests/io.glorious", "src/foundation.glorious", "src/memory.glorious", "src/time.glorious", "src/io.glorious");
source_case!(path, "../../../stdlib/tests/path.glorious", "src/foundation.glorious", "src/path.glorious");
source_case!(float, "../../../stdlib/tests/float.glorious", "src/foundation.glorious", "src/float.glorious");
source_case!(float_text, "../../../stdlib/tests/float_text.glorious", "src/foundation.glorious", "src/float.glorious", "src/float_text.glorious");
source_case!(ffi, "../../../stdlib/tests/ffi.glorious", "src/foundation.glorious", "src/integer.glorious", "src/integer_text.glorious", "src/utf8.glorious", "src/ffi.glorious");
source_case!(float_parse, "../../../stdlib/tests/float_parse.glorious", "src/foundation.glorious", "src/float.glorious", "src/float_parse.glorious");
source_case!(float_tail, "../../../stdlib/tests/float_tail.glorious", "src/foundation.glorious", "src/float.glorious", "src/float_parse.glorious");
source_case!(float_shortest, "../../../stdlib/tests/float_shortest.glorious", "src/foundation.glorious", "src/float.glorious", "src/float_text.glorious", "src/float_parse.glorious", "src/float_shortest.glorious");
source_case!(float_math, "../../../stdlib/tests/float_math.glorious", "src/foundation.glorious", "src/float.glorious", "src/float_parse.glorious", "src/float_math.glorious");
source_case!(float_convert, "../../../stdlib/tests/float_convert.glorious", "src/foundation.glorious", "src/integer.glorious", "src/integer_text.glorious", "src/float.glorious", "src/float_parse.glorious", "src/float_math.glorious", "src/float_convert.glorious");
source_case!(iterator, "../../../stdlib/tests/iterator.glorious", "src/foundation.glorious", "src/memory.glorious", "src/iterator.glorious");
source_case!(iterator_callbacks, "../../../stdlib/tests/iterator_callbacks.glorious", "src/foundation.glorious", "src/memory.glorious", "src/iterator.glorious", "src/iterator_callbacks.glorious");
source_case!(traversal, "../../../stdlib/tests/traversal.glorious", "src/foundation.glorious", "src/traversal.glorious");
source_case!(sorting, "../../../stdlib/tests/sorting.glorious", "src/foundation.glorious", "src/memory.glorious", "src/sorting.glorious");

#[test]
fn every_library_source_file_is_embedded_from_disk() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/src");
    let embedded = grandiose_stage0::service::STANDARD_LIBRARY_SOURCE;
    let mut paths: Vec<_> = std::fs::read_dir(&root).unwrap().map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "glorious")).collect();
    paths.sort();
    assert!(paths.len() > 1, "the library must be authored as source files");
    let fragments = grandiose_stage0::service::STANDARD_LIBRARY_FRAGMENTS;
    assert_eq!(paths.len(), fragments.len(), "every on-disk source has exactly one inventory entry");
    let mut names = std::collections::BTreeSet::new();
    let mut recomposed = String::new();
    for (path, source) in fragments {
        assert!(names.insert(*path), "duplicate fragment {path}");
        let disk = std::fs::read_to_string(root.parent().unwrap().join(path)).unwrap();
        assert_eq!(*source, disk, "fragment {path} differs from disk");
        recomposed.push_str(source);
        recomposed.push('\n');
    }
    assert_eq!(embedded, recomposed, "the composition preserves inventory ordering and exact source bytes");
    for path in paths {
        let source = std::fs::read_to_string(&path).unwrap();
        assert!(!source.trim().is_empty(), "{} must not be an empty placeholder", path.display());
        assert!(embedded.contains(&source), "{} is absent from the canonical embedding inventory", path.display());
    }
}
