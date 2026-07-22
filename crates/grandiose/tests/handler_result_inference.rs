use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_phases_with_options};
use grandiose_vm::{Value, Vm, verify};

const LEVELS: [OptimizationLevel; 3] = [
    OptimizationLevel::O1,
    OptimizationLevel::O2,
    OptimizationLevel::O3,
];

fn run_selected(source_name: &str, source: &str, expected: Value) {
    for optimization_level in LEVELS {
        let phases = compile_source_to_phases_with_options(
            source_name,
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let selected = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == "selected")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(phases.artifact).unwrap())
                .run(selected, vec![])
                .unwrap(),
            expected,
            "{optimization_level:?}"
        );
    }
}

#[test]
fn terminal_clause_infers_a_let_bound_handler_result_without_context() {
    let source = r#"
        effect Stop { stop() -> ! }
        selected() -> i64 {
            let inferred = handle perform Stop::stop() {
                Stop::stop() => 42
            };
            inferred
        }
        main() -> { () }
    "#;
    run_selected(
        "handler-terminal-inference.glorious",
        source,
        Value::I64(42),
    );
}

#[test]
fn normal_completion_and_resumptive_clause_results_join_without_context() {
    let source = r#"
        effect Maybe { [0,1] get() -> i64 }
        selected() -> i64 {
            let inferred = handle {
                let value = perform Maybe::get();
                value + 2
            } {
                Maybe::get() with continuation => resume(continuation, 40)
            };
            inferred
        }
        main() -> { () }
    "#;
    run_selected(
        "handler-normal-clause-join.glorious",
        source,
        Value::I64(42),
    );
}

#[test]
fn inferred_handlers_nest_inside_captured_callable_computations() {
    let source = r#"
        effect Stop { stop() -> ! }
        selected() -> i64 {
            let captured = 40;
            let computation = { => {
                let inner = handle perform Stop::stop() {
                    Stop::stop() => captured + 2
                };
                inner
            } };
            computation()
        }
        main() -> { () }
    "#;
    run_selected(
        "handler-nested-capture-inference.glorious",
        source,
        Value::I64(42),
    );
}

#[test]
fn incompatible_normal_and_clause_results_are_rejected_at_every_level() {
    let source = r#"
        effect Maybe { [0,1] get() -> i64 }
        selected() -> i64 {
            let invalid = handle { perform Maybe::get() } {
                Maybe::get() with continuation => "wrong"
            };
            invalid
        }
        main() -> { () }
    "#;
    for optimization_level in LEVELS {
        let errors = compile_source_to_phases_with_options(
            "handler-result-mismatch.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .expect_err("mismatched handler results compiled");
        assert!(
            errors.iter().any(|error| {
                error.message.contains("expected") || error.message.contains("result")
            }),
            "{optimization_level:?}: {errors:#?}"
        );
    }
}
