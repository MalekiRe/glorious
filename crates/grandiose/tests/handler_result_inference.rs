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
fn complementary_generic_constructors_infer_a_let_bound_handler_result() {
    let source = r#"
        u32_value(value: u32) -> u32 { value }

        selected(kind: u8) -> Bool {
            let inferred = handle kind {
                0 => Result::Ok((u32_value(1), u32_value(2))),
                _ => Result::Err(())
            };
            handle move inferred {
                Result::Ok(found) => found.0 == u32_value(1),
                Result::Err(_) => false
            }
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode("handler-complementary-generic-result.glorious", source)
        .unwrap();
}

#[test]
fn nested_generic_handler_refines_payload_types_for_comparison() {
    let source = r#"
        same(left: Option<usize>, right: Option<usize>) -> Bool {
            handle left {
                Result::Err(_) => false,
                Result::Ok(left_index) => handle right {
                    Result::Err(_) => false,
                    Result::Ok(right_index) => left_index == right_index
                }
            }
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode(
        "handler-nested-generic-payload-comparison.glorious",
        source,
    )
    .unwrap();
}

#[test]
fn planned_generic_control_shape_contextualizes_a_sibling_literal() {
    let source = r#"
        mod helper {
            pub usize_value(value: usize) -> usize { value }
        }

        selected(flag: Bool) -> () {
            let inferred = handle flag {
                Result::Err(_) => 0,
                Result::Ok(_) => helper::usize_value(1)
            };
            inferred;
            ()
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode(
        "handler-generic-control-sibling-literal.glorious",
        source,
    )
    .unwrap();
}

#[test]
fn typed_handler_sibling_contextualizes_an_earlier_literal_at_runtime() {
    let source = r#"
        usize_value(value: usize) -> usize { value }

        selected() -> usize {
            handle true {
                Result::Err(_) => 0,
                Result::Ok(_) => usize_value(2)
            }
        }

        main() -> () { () }
    "#;
    run_selected(
        "handler-runtime-sibling-literal.glorious",
        source,
        Value::U64(2),
    );
}

#[test]
fn recursive_nondefault_handler_branch_contextualizes_outer_literal() {
    let source = r#"
        usize_value(value: usize) -> usize { value }

        depth(flag: Bool) -> usize {
            handle flag {
                Result::Ok(_) => 0,
                Result::Err(_) => handle flag {
                    Result::Err(_) => unreachable(),
                    Result::Ok(_) => usize_value(1) + depth(flag)
                }
            }
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode("handler-recursive-nondefault-sibling.glorious", source)
        .unwrap();
}

#[test]
fn annotated_result_contextualizes_a_constructor_payload_literal() {
    let source = r#"
        write_function(flag: Bool) -> Result<(), u8> {
            handle flag {
                Result::Ok(_) => Result::Ok(()),
                Result::Err(_) => Result::Err(3)
            }
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode(
        "handler-annotated-result-constructor-payload.glorious",
        source,
    )
    .unwrap();
}

#[test]
fn shared_projection_local_survives_nested_handler_control_flow() {
    let source = r#"
        struct HeaderRange { count: u32 }
        struct CallableHeader { parameters: HeaderRange }

        callable_parameters(value: &CallableHeader) -> &HeaderRange {
            &value.parameters
        }

        range_count(value: &HeaderRange) -> u32 { value.count }

        combine(value: &CallableHeader, range: &HeaderRange) -> u32 {
            range_count(&value.parameters) + range_count(range)
        }

        shared_reborrows_can_overlap(value: &mut CallableHeader) -> u32 {
            combine(&*value, &value.parameters)
        }

        collect_callable(callable: &CallableHeader, flag: Bool) -> Result<(), u8> {
            let parameters = callable_parameters(callable);
            let module_plus_one = handle flag {
                Result::Err(_) => 0,
                Result::Ok(_) => 1
            };
            handle flag {
                Result::Err(_) => Result::Err(3),
                Result::Ok(_) => {
                    module_plus_one;
                    range_count(parameters);
                    Result::Ok(())
                }
            }
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode(
        "handler-shared-projection-local-identity.glorious",
        source,
    )
    .unwrap();
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
