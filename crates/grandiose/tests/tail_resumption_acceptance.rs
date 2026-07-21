use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_phases_with_options,
    diagnostic::Diagnostic,
    eval::{Host, Value as InterpreterValue},
    run_source,
    span::Span,
};
use grandiose_vm::{Artifact, Instruction, Value, Vm, verify};

struct NoHost;

impl Host for NoHost {
    fn perform(
        &mut self,
        _effect: &str,
        _operation: &str,
        _args: Vec<InterpreterValue>,
        span: Span,
    ) -> Result<InterpreterValue, Diagnostic> {
        Err(Diagnostic::error(
            "unexpected host effect",
            "the lexical handler should intercept this operation",
            span,
        ))
    }
}

fn function_id(artifact: &Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

fn run_all_levels(source_name: &str, source: &str, expected: Value) {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            source_name,
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let bytes = phases.artifact.encode();
        let artifact = Artifact::decode(&bytes).expect("artifact codec round-trip");
        assert_eq!(artifact.encode(), bytes, "{optimization_level:?}");
        assert!(
            artifact
                .code
                .iter()
                .any(|instruction| matches!(instruction, Instruction::TailResume { .. })),
            "{optimization_level:?}: source tail resumption did not survive lowering"
        );
        let selected = function_id(&artifact, "selected");
        assert_eq!(
            Vm::new(verify(artifact).unwrap())
                .run(selected, vec![])
                .unwrap(),
            expected,
            "{optimization_level:?}"
        );
    }
}

fn assert_rejected(source_name: &str, source: &str, needle: &str) {
    let errors = compile_source_to_bytecode(source_name, source)
        .expect_err("invalid tail resumption unexpectedly compiled");
    assert!(
        errors.iter().any(|error| error.message.contains(needle)),
        "missing `{needle}` in {errors:#?}"
    );
    assert!(
        errors
            .iter()
            .all(|error| error.code.as_deref() != Some("G1BC999")),
        "rejection must be a source diagnostic: {errors:#?}"
    );
}

#[test]
fn exact_one_shot_tail_resume_executes_at_every_optimization_level() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            handle {
                let answer = perform Ask::ask();
                answer + 1
            } {
                Ask::ask() with continuation => tail(continuation, 41)
            }
        }
        main() -> { () }
    "#;
    run_all_levels("tail-resume-one-shot.gr", source, Value::I64(42));
}

#[test]
fn optional_one_shot_tail_resume_is_a_valid_terminal_consumption() {
    let source = r#"
        effect Maybe { [0,1] ask() -> i64 }
        selected() -> i64 {
            handle { perform Maybe::ask() + 2 } {
                Maybe::ask() with continuation => tail(continuation, 40)
            }
        }
        main() -> { () }
    "#;
    run_all_levels("tail-resume-optional.gr", source, Value::I64(42));
}

#[test]
fn tail_resume_disposes_clause_locals_before_the_terminal_transfer() {
    let source = r#"
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        impl Drop for Resource { drop(&mut self) -> { () } }
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            handle { perform Ask::ask() } {
                Ask::ask() with continuation => {
                    let resource = Resource { marker: 1 };
                    tail(continuation, 42)
                }
            }
        }
        main() -> { () }
    "#;
    run_all_levels("tail-resume-cleanup.gr", source, Value::I64(42));
}

#[test]
fn tail_resume_rejects_a_reusable_resumption() {
    let source = r#"
        effect Replay { [2,2] replay() -> i64 }
        selected() -> i64 {
            handle { perform Replay::replay() } {
                Replay::replay() with continuation => tail(continuation, 42)
            }
        }
        main() -> { () }
    "#;
    assert_rejected("tail-resume-multishot.gr", source, "one-shot");
}

#[test]
fn tail_resume_checks_the_continuation_input_type() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            handle { perform Ask::ask() } {
                Ask::ask() with continuation => tail(continuation, "wrong")
            }
        }
        main() -> { () }
    "#;
    assert_rejected(
        "tail-resume-input-type.gr",
        source,
        "expected i64, found Text",
    );
}

#[test]
fn tail_resume_outside_a_handler_clause_is_rejected_at_source_level() {
    let source = r#"
        selected() -> i64 { tail(k, 42) }
        main() -> { () }
    "#;
    assert_rejected(
        "tail-resume-outside-handler.gr",
        source,
        "active handler resumption",
    );
}

#[test]
fn recovery_evaluator_treats_tail_as_a_terminal_one_shot_resume() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        main() -> {
            handle {
                let answer = perform Ask::ask();
                ()
            } {
                Ask::ask() with continuation => tail(continuation, 42)
            }
        }
    "#;
    assert_eq!(
        run_source("tail-resume-recovery.gr", source, vec![], &mut NoHost).unwrap(),
        InterpreterValue::Unit
    );
}
