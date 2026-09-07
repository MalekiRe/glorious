use grandiose_stage0::*;
use std::collections::BTreeMap;

fn run(source: &str) -> i64 {
    let package = PackageKey("cleanup-pipeline@0.1.0".into());
    let outcome = StageZeroCompiler::new()
        .compile(CompilationRequest {
            build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"cleanup-mir-pipeline")),
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
        })
        .unwrap();
    let artifact = outcome.artifact.unwrap();
    let result = artifact.run_i64().unwrap();
    assert_eq!(
        decode_and_verify_program(&artifact.canonical_bytes())
            .unwrap()
            .run_i64()
            .unwrap(),
        result
    );
    result
}

#[test]
fn self_assignment_prepares_a_copyable_callable_before_destroying_the_old_owner() {
    assert_eq!(
        run(
            "fn answer() -> i64 { 42 } pub fn main() -> i64 { let selected = answer; selected = selected; selected() }"
        ),
        42
    );
}

#[test]
fn projected_self_assignment_prepares_the_incoming_callable_before_cleanup() {
    assert_eq!(
        run(
            "fn answer() -> i64 { 42 } struct Slot { callback: () -> i64 } pub fn main() -> i64 { let slot = Slot { callback: answer }; slot.callback = slot.callback; slot.callback() }"
        ),
        42
    );
}

#[test]
fn nested_instances_of_one_enum_keep_complete_copy_layouts() {
    assert_eq!(
        run(
            "enum Maybe<T> { Some(T), None } struct Ticket { value: i64 } enum Phase { Ancestry(Maybe<Ticket>), Done } struct Attempt { phase: Phase } struct Engine { attempt: Maybe<Attempt> } fn set(engine: &mut Engine, phase: Phase) -> { let copy = phase; () } pub fn main() -> i64 { let engine = Engine { attempt: Maybe::Some(Attempt { phase: Phase::Done }) }; set(&mut engine, Phase::Ancestry(Maybe::Some(Ticket { value: 42 }))); 42 }"
        ),
        42
    );
}
