use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_phases,
    compile_source_to_phases_with_options, compiler_mir::Terminator,
};
use grandiose_vm::{Value, Vm, verify};

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

fn run_selected_at_every_level(source_name: &str, source: &str, expected: Value) {
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
        let selected = function_id(&phases.artifact, "selected");
        let actual = Vm::new(verify(phases.artifact).unwrap())
            .run(selected, vec![])
            .unwrap();
        assert_eq!(actual, expected, "{optimization_level:?}");
    }
}

#[test]
fn nested_resumptive_payload_composes_the_outer_evaluation_continuation() {
    let source = r#"
        effect Ask { [1,1] ask(value: i64) -> i64 }
        selected() -> i64 {
            handle perform Ask::ask(perform Ask::ask(40)) {
                Ask::ask(value) with continuation =>
                    resume(continuation, value + 1)
            }
        }
        main() -> { () }
    "#;
    run_selected_at_every_level("nested-perform-same-handler.gr", source, Value::I64(42));
}

#[test]
fn earlier_linear_payload_is_captured_by_the_inner_perform_but_not_the_outer_one() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Ask { [1,1] ask(value: i64) -> i64 }
        effect Exchange {
            [1,1] exchange(ticket: Ticket, increment: i64) -> Ticket
        }
        exchange_result() -> Ticket {
            handle perform Exchange::exchange(
                Ticket { serial: 40 },
                perform Ask::ask(1)
            ) {
                Ask::ask(value) with continuation =>
                    resume(continuation, value + 1),
                Exchange::exchange(ticket, increment) with continuation => {
                    let Ticket { serial } = move ticket;
                    resume(continuation, Ticket { serial: serial + increment })
                }
            }
        }
        selected() -> i64 {
            let returned = exchange_result();
            let Ticket { serial } = move returned;
            serial
        }
        main() -> { () }
    "#;

    let phases = compile_source_to_phases("nested-perform-linear-capture.gr", source).unwrap();
    let performs = phases.mir.functions.iter().flat_map(|function| {
        function
            .blocks
            .iter()
            .filter_map(move |block| match &block.terminator {
                Terminator::Perform {
                    payloads, capture, ..
                } => Some((function, payloads, capture)),
                _ => None,
            })
    });
    let performs = performs.collect::<Vec<_>>();
    let (_, outer_payloads, outer_capture) = performs
        .iter()
        .find(|(_, payloads, _)| payloads.len() == 2)
        .copied()
        .expect("the outer Exchange perform is present");
    let (_, _, inner_capture) = performs
        .iter()
        .find(|(_, payloads, _)| payloads.len() == 1)
        .copied()
        .expect("the inner Ask perform is present");
    assert!(
        !inner_capture.captured_owners.is_empty(),
        "the inner suspension must retain the already evaluated first payload"
    );
    assert!(outer_payloads.iter().all(|payload| {
        outer_capture
            .captured_owners
            .binary_search(&payload.register)
            .is_err()
    }));

    run_selected_at_every_level("nested-perform-linear-run.gr", source, Value::I64(42));
}

#[test]
fn nested_payload_uses_the_nearest_inner_handler_then_forwards_the_outer_operation() {
    let source = r#"
        effect Inner { [1,1] value(input: i64) -> i64 }
        effect Outer { [1,1] value(input: i64) -> i64 }
        selected() -> i64 / {Inner, Outer} {
            handle {
                handle perform Outer::value(perform Inner::value(10)) {
                    Inner::value(input) with continuation =>
                        resume(continuation, input + 1)
                }
            } {
                Outer::value(input) with continuation =>
                    resume(continuation, input + 20)
            }
        }
        main() -> { () }
    "#;
    run_selected_at_every_level("nested-perform-handler-search.gr", source, Value::I64(31));
}

#[test]
fn cancelling_inner_payload_suspension_cleans_an_earlier_zero_use_payload() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[0,1]> for Ticket {}
        effect Stop { [0,1] stop() -> i64 }
        effect Exchange {
            [1,1] exchange(ticket: Ticket, increment: i64) -> Ticket
        }
        exchange_result() -> Ticket {
            handle perform Exchange::exchange(
                Ticket { serial: 40 },
                perform Stop::stop()
            ) {
                Stop::stop() with continuation => {
                    cancel(continuation);
                    Ticket { serial: 7 }
                },
                Exchange::exchange(ticket, increment) with continuation => {
                    let Ticket { serial } = move ticket;
                    resume(continuation, Ticket { serial: serial + increment })
                }
            }
        }
        selected() -> i64 {
            let returned = exchange_result();
            let Ticket { serial } = move returned;
            serial
        }
        main() -> { () }
    "#;
    run_selected_at_every_level("nested-perform-cancel-cleanup.gr", source, Value::I64(7));
}

#[test]
fn terminal_inner_payload_abandons_the_outer_perform_and_cleans_earlier_payloads() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[0,1]> for Ticket {}
        effect Stop {
            outer(ticket: Ticket, increment: i64) -> !
            inner(value: i64) -> !
        }
        exchange_result() -> Ticket {
            handle perform Stop::outer(
                Ticket { serial: 40 },
                perform Stop::inner(9)
            ) {
                Stop::inner(value) => Ticket { serial: value },
                Stop::outer(ticket, increment) => {
                    let Ticket { serial } = move ticket;
                    Ticket { serial: serial + increment }
                }
            }
        }
        selected() -> i64 {
            let returned = exchange_result();
            let Ticket { serial } = move returned;
            serial
        }
        main() -> { () }
    "#;

    let phases = compile_source_to_phases("nested-terminal-payload-capture.gr", source).unwrap();
    let terminal_capture = phases
        .mir
        .functions
        .iter()
        .flat_map(|function| &function.blocks)
        .find_map(|block| match &block.terminator {
            Terminator::Perform {
                payloads,
                capture,
                resume: None,
                ..
            } if payloads.len() == 1 => Some(capture),
            _ => None,
        })
        .expect("the nested terminal perform has explicit cleanup capture accounting");
    assert!(!terminal_capture.captured_owners.is_empty());
    assert!(terminal_capture.cancellation_safe);

    run_selected_at_every_level("nested-terminal-payload-run.gr", source, Value::I64(9));
}
