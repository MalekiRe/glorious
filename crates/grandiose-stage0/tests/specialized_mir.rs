use grandiose_stage0::*;
use std::collections::BTreeMap;

fn run(source: &str) -> i64 {
    let package = PackageKey("specialized-pipeline@0.1.0".into());
    let outcome = StageZeroCompiler::new()
        .compile(CompilationRequest {
            build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"specialized-mir-pipeline")),
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
fn generic_source_calls_cross_the_specialized_pipeline() {
    assert_eq!(
        run("fn identity<T>(value: T) -> T { value } pub fn main() -> i64 { identity(42) }"),
        42
    );
}
#[test]
fn two_instances_of_one_template_keep_distinct_layouts() {
    assert_eq!(
        run(
            "struct Boxed<T> { value: T } fn boxed<T>(value: T) -> Boxed<T> { Boxed { value: value } } pub fn main() -> i64 { let empty = boxed(()); let result = boxed(42); result.value }"
        ),
        42
    );
}
#[test]
fn generic_closure_instances_have_concrete_capture_abis() {
    assert_eq!(
        run(
            "fn apply<T>(value: T) -> T { let action = move (value) { value }; action() } pub fn main() -> i64 { apply(42) }"
        ),
        42
    );
}
#[test]
fn selected_trait_calls_have_concrete_targets() {
    assert_eq!(
        run(
            "trait Pick { pick(value: Self) -> i64; } impl Pick for i64 { pick(value: i64) -> i64 { value } } fn apply<T>(value: T) -> i64 where T: Pick { Pick::pick(value) } pub fn main() -> i64 { apply(42) }"
        ),
        42
    );
}
#[test]
fn first_class_functions_remain_indirect_when_reassigned() {
    assert_eq!(
        run(
            "fn initial() -> i64 { 7 } fn answer() -> i64 { 42 } pub fn main() -> i64 { let mut selected = initial; selected = answer; selected() }"
        ),
        42
    );
}

#[test]
fn generic_effect_payloads_and_cancellation_contracts_are_specialized() {
    assert_eq!(
        run(
            "effect Ask<T> { [0,1] ask(value: T) -> T; } fn relay<T>(value: T) -> T / Ask<T> { Ask<T>::ask(value) } pub fn main() -> i64 { handle relay(20) { Ask<i64>::ask(_) with _ => 42 } }"
        ),
        42
    );
}

#[test]
fn associated_effect_rows_are_closed_in_forwarded_calls() {
    assert_eq!(
        run(
            "trait Capability { type Effects: EffectRow; } struct Value { value: i64 } impl Capability for Value { type Effects = {}; } fn worker<T>(value: T) -> i64 / { <T as Capability>::Effects } where T: Capability { 42 } fn relay<T>(value: T) -> i64 / { <T as Capability>::Effects } where T: Capability { worker(value) } pub fn main() -> i64 { relay(Value { value: 0 }) }"
        ),
        42
    );
}

#[test]
fn higher_ranked_callback_rows_are_closed_inside_their_binder() {
    assert_eq!(
        run(
            "trait Capability { type Effects<'a>: EffectRow; } struct Value {} impl Capability for Value { type Effects<'a> = {}; } fn apply(callback: for<'a> (&'a i64) -> &'a i64 / { <Value as Capability>::Effects<'a> }) -> i64 { let value = 42; let result = callback(&value); *result } pub fn main() -> i64 { apply({ value => value }) }"
        ),
        42
    );
}
