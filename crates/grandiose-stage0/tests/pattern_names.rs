//! Bare pattern names are constants or binders only after resolution (§4.3).

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    ServiceError, SourceInput, StageZeroCompiler, decode_and_verify_program,
};

fn request(source: &str) -> CompilationRequest {
    let package = PackageKey("pattern-names@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"pattern-names")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: Default::default(),
        codegen_options: Default::default(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn runs(source: &str) {
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(
        decode_and_verify_program(&artifact.canonical_bytes())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

fn rejects(source: &str, code: &str) {
    let Err(ServiceError::Failed(diagnostics)) = StageZeroCompiler::new().compile(request(source))
    else {
        panic!("invalid duplicate bindings were accepted");
    };
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.code == code),
        "{diagnostics:#?}"
    );
    assert!(
        !diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G7006"),
        "names must reach semantic resolution: {diagnostics:#?}"
    );
}

#[test]
fn repeated_boolean_constants_in_nested_patterns_execute() {
    runs(
        "fn flags() -> ((Bool, Bool), Bool) { ((true, true), false) } pub fn main() -> i64 { handle flags() { ((true, true), false) => 42, _ => 0 } }",
    );
}

#[test]
fn imported_constants_can_repeat_in_array_patterns() {
    runs(
        "mod values { pub let answer = 42; } use crate::values::answer; pub fn main() -> i64 { handle [42, 42] { [answer, answer] => 42, _ => 0 } }",
    );
}

#[test]
fn repeated_constants_in_record_and_enum_patterns_execute() {
    runs(
        "pub struct Pair { left: i64, right: i64 } pub enum Wrap { Item(Pair) } let answer = 42; pub fn main() -> i64 { handle Wrap::Item(Pair { left: 42, right: 42 }) { Wrap::Item(Pair { left: answer, right: answer }) => 42, _ => 0 } }",
    );
}

#[test]
fn repeated_constants_across_handler_payloads_do_not_bind() {
    runs(
        "let answer = 42; effect Choose { [1, 1] pick(i64, i64) -> i64; } pub fn main() -> i64 { handle Choose::pick(42, 42) { Choose::pick(answer, answer, k) => k(42), Choose::pick(_, _, k) => k(0) } }",
    );
}

#[test]
fn continuation_may_share_a_constant_pattern_spelling() {
    runs(
        "let answer = 42; effect Choose { [1, 1] pick(i64) -> i64; } pub fn main() -> i64 { handle Choose::pick(42) { Choose::pick(answer, answer) => answer(42), Choose::pick(_, k) => k(0) } }",
    );
}

#[test]
fn duplicate_tuple_binders_are_rejected_after_resolution() {
    rejects(
        "pub fn main() -> i64 { handle (1, 2) { (value, value) => value } }",
        "G4017",
    );
}

#[test]
fn duplicate_nested_record_binders_are_rejected_after_resolution() {
    rejects(
        "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { handle (Pair { left: 1, right: 2 }, 3) { (Pair { left: value, right: _ }, value) => value } }",
        "G4017",
    );
}

#[test]
fn duplicate_binders_across_handler_payloads_are_rejected() {
    rejects(
        "effect Choose { [1, 1] pick(i64, i64) -> i64; } pub fn main() -> i64 { handle Choose::pick(1, 2) { Choose::pick(value, value, k) => k(value) } }",
        "G4017",
    );
}

#[test]
fn continuation_cannot_shadow_an_actual_payload_binder() {
    for arm in [
        "Choose::pick(value, value) => value(42)",
        "Choose::pick(value) with value => value(42)",
    ] {
        rejects(
            &format!(
                "effect Choose {{ [1, 1] pick(i64) -> i64; }} pub fn main() -> i64 {{ handle Choose::pick(1) {{ {arm} }} }}"
            ),
            "G4160",
        );
    }
}

#[test]
fn duplicate_names_without_an_import_are_binders_not_implicit_constants() {
    rejects(
        "#![no_implicit_prelude] pub fn main() -> i64 { handle (1, 2) { (true, true) => true } }",
        "G4017",
    );
}

#[test]
fn repeated_constants_with_wrong_types_do_not_become_binders() {
    rejects(
        "let answer = 42; fn flags() -> (Bool, Bool) { (true, false) } pub fn main() -> i64 { handle flags() { (answer, answer) => 42, _ => 0 } }",
        "G4201",
    );
}
