//! Language §10.1: operation payloads are ordered types, not body binders.

use std::collections::BTreeMap;

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};

fn request(source: &str) -> CompilationRequest {
    let package = PackageKey("positional-effects@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"positional-effects")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn runs(source: &str) {
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    let program = outcome.artifact.unwrap();
    assert_eq!(program.run_i64().unwrap(), 42);
    let decoded = decode_and_verify_program(&program.canonical_bytes()).unwrap();
    assert_eq!(decoded.run_i64().unwrap(), 42);
}

#[test]
fn generic_positional_payloads_keep_order_and_handler_local_names() {
    runs(
        r#"
        effect Select<T> { select(i64, T) -> T; }
        pub fn main() -> i64 {
            handle Select<i64>::select(7, 42) {
                Select<i64>::select(ignored, answer) => answer
            }
        }
    "#,
    );
}

#[test]
fn positional_terminal_payload_has_no_continuation() {
    runs(
        r#"
        effect Stop<T> { stop(T) -> !; }
        pub fn main() -> i64 {
            handle Stop<i64>::stop(42) { Stop<i64>::stop(answer) => answer }
        }
    "#,
    );
}

#[test]
fn positional_borrowed_payload_retains_its_lifetime() {
    runs(
        r#"
        effect Read<'a> { read(&'a i64) -> i64; }
        fn read<'a>(value: &'a i64) -> i64 {
            handle Read<'a>::read(value) { Read<'a>::read(reference) => *reference }
        }
        pub fn main() -> i64 {
            let value = 42;
            read(&value)
        }
    "#,
    );
}

#[test]
fn positional_tuple_and_callable_payloads_are_single_slots() {
    runs(
        r#"
        effect Apply { apply((i64, i64), (i64) -> i64) -> i64; }
        fn identity(value: i64) -> i64 { value }
        pub fn main() -> i64 {
            handle Apply::apply((7, 42), identity) {
                Apply::apply((ignored, answer), callback) => callback(answer)
            }
        }
    "#,
    );
}

#[test]
fn positional_payload_type_mismatches_remain_source_errors() {
    let source = r#"
        effect Pick { pick(i64) -> i64; }
        pub fn main() -> i64 {
            handle Pick::pick(()) { Pick::pick(value) => value }
        }
    "#;
    let diagnostics = StageZeroCompiler::new()
        .compile(request(source))
        .expect_err("a positional payload must retain its declared type")
        .diagnostics();
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4154"),
        "{diagnostics:?}"
    );
}
