mod support;

use grandiose_stage0::control_mir::{
    ControlError, ControlMir, ControlOperation, ControlTerminator,
};
use grandiose_stage0::evaluation_mir::EvaluationMir;
use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath,
    PackageKey, SourceInput, StageZeroCompiler,
};
use std::collections::BTreeMap;

fn control(source: &str) -> Result<ControlMir, ControlError> {
    let (definition, core, _) = support::frontend("control-mir@0.1.0", source, "main");
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    ControlMir::lower(&EvaluationMir::lower(definition, &core).unwrap())
}

fn run(source: &str) -> i64 {
    let package = PackageKey("control-mir@0.1.0".into());
    let outcome = StageZeroCompiler::new()
        .compile(CompilationRequest {
            build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"control-mir")),
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
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let expected = artifact.run_i64().unwrap();
    let decoded = grandiose_stage0::decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
    assert_eq!(decoded.run_i64().unwrap(), expected);
    expected
}

#[test]
fn nested_lazy_values_have_explicit_joins() {
    let mir = control("pub fn main(a: Bool, b: Bool, c: Bool) -> Bool { (a or { b }) and { c } }").unwrap();
    mir.validate().unwrap();
    assert_eq!(
        mir.blocks()
            .iter()
            .filter(|block| matches!(block.terminator, ControlTerminator::Invoke { continuation: Some(_), .. }))
            .count(),
        2
    );
    assert_eq!(
        mir.blocks()
            .iter()
            .skip(1)
            .filter(|block| block.parameters.len() == 1)
            .count(),
        2
    );
}

#[test]
fn calls_define_results_at_return_continuations() {
    let mir = control(
        "fn increment(value: i64) -> i64 { value + 1 } pub fn main() -> i64 { increment(40) + 1 }",
    )
    .unwrap();
    let call = mir
        .blocks()
        .iter()
        .find_map(|block| match &block.terminator {
            ControlTerminator::Invoke {
                result,
                continuation: Some(target),
                ..
            } => Some((*result, *target)),
            _ => None,
        })
        .unwrap();
    assert_eq!(mir.blocks()[call.1.0 as usize].parameters, vec![call.0]);
    assert_eq!(
        run(
            "fn increment(value: i64) -> i64 { value + 1 } pub fn main() -> i64 { increment(40) + 1 }"
        ),
        42
    );
}

#[test]
fn bottom_calls_have_no_return_continuation_or_enclosing_tuple() {
    let mir = control("pub fn main(halt: () -> !) -> (i64, i64) { (halt(), 7) }").unwrap();
    assert!(mir.blocks().iter().any(|block| matches!(
        block.terminator,
        ControlTerminator::Invoke {
            continuation: None,
            ..
        }
    )));
    assert!(
        !mir.blocks()
            .iter()
            .flat_map(|block| &block.instructions)
            .any(|instruction| matches!(instruction.operation, ControlOperation::Tuple(_)))
    );
}

#[test]
fn lexical_shadowing_and_direct_callable_aliases_execute_through_the_adapter() {
    let source = "fn identity(value: i64) -> i64 { value } pub fn main() -> i64 { let value = 40; let callable = identity; let nested = { let value = 1; callable(value) }; value + nested + 1 }";
    let mir = control(source).unwrap();
    assert!(mir.scopes().len() >= 2);
    assert_eq!(run(source), 42);
}

#[test]
fn statement_disposal_is_explicit_between_invocations() {
    let mir = control("fn first() -> i64 { 1 } fn second() -> i64 { 2 } pub fn main() -> i64 { first(); second() }").unwrap();
    let continuation = mir
        .blocks()
        .iter()
        .find_map(|block| match &block.terminator {
            ControlTerminator::Invoke {
                continuation: Some(target),
                ..
            } => Some(*target),
            _ => None,
        })
        .unwrap();
    assert!(
        mir.blocks()[continuation.0 as usize]
            .instructions
            .iter()
            .any(|instruction| matches!(instruction.operation, ControlOperation::Discard(_)))
    );
}

#[test]
fn handler_transition_is_not_erased_to_function_return() {
    let mir = control(
            "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => k(42) } }"
        ).unwrap();
    assert_eq!(mir.handlers().len(), 1);
    assert!(mir.blocks().iter().any(|block| matches!(block.terminator,
        ControlTerminator::Transfer(grandiose_stage0::control_mir::ControlTransfer::CompleteHandler { .. }))));
    assert_eq!(
        run(
            "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => k(42) } }"
        ),
        42
    );
}

#[test]
fn all_structured_regions_compose_without_source_shape_dispatch() {
    for source in [
        "struct Pair { first: i64, second: i64 } pub fn main(value: Pair) -> i64 { let loan = &value.second; *loan }",
        "pub fn main(target: &mut i64, rhs: () -> i64) -> i64 { *target = rhs(); 0 }",
        "pub fn main() -> i64 { let callable = (value: i64) -> i64 { value + 1 }; callable(41) }",
        "pub enum Result { Ok(i64), Err } pub fn main(value: Result) -> i64 { handle value is Result::Ok(found) { Test::Yes(_) => 1; Test::No(_) => 0 } }",
        "pub fn main() -> i64 { label done { transfer done 42 } }",
        "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { 1 + handle Ask::ask() { Ask::ask() => 41 } }",
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { 1 + handle Ask::ask() { Ask::ask() with _ => 41 } }",
    ] { control(source).unwrap_or_else(|error| panic!("{source}\n{error:?}")); }
}

#[test]
fn production_mixed_strict_and_lazy_contexts_preserve_short_circuiting() {
    for (condition, expected) in [(false, 0), (true, 1)] {
        let source = format!(
            "fn choose(value: Bool) -> i64 {{ handle value {{ true => 1; false => 0 }} }} pub fn main() -> i64 {{ let condition = {condition}; choose((condition and {{ true }}) or {{ false and {{ 1 / 0 == 0 }} }}) }}"
        );
        control(&source).unwrap();
        assert_eq!(run(&source), expected);
    }
}
