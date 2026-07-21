use grandiose::{compile_source_to_bytecode, compile_source_to_phases};
use grandiose_vm::{Instruction, NO_RETURN, Type, Value, Vm, verify};

fn run(source_name: &str, source: &str, function_name: &str) -> Value {
    let artifact = compile_source_to_bytecode(source_name, source).unwrap();
    let function = artifact
        .functions
        .iter()
        .position(|function| function.name == function_name)
        .unwrap() as u32;
    Vm::new(verify(artifact).unwrap())
        .run(function, vec![])
        .unwrap()
}

fn assert_rejected(source_name: &str, source: &str, alternatives: &[&str]) {
    let diagnostics = compile_source_to_bytecode(source_name, source).unwrap_err();
    assert!(
        diagnostics.iter().any(|diagnostic| {
            alternatives
                .iter()
                .any(|needle| diagnostic.message.contains(needle))
        }),
        "expected one of {alternatives:?}, got {diagnostics:#?}"
    );
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code.is_some()),
        "portable diagnostics must remain structured: {diagnostics:#?}"
    );
}

#[test]
fn terminal_specialization_inside_a_handler_has_the_ground_row_and_executes() {
    let source = r#"
        cases Stops = {Stop};
        effect Stop { stop() -> ! }
        fixture_abort<T>(fallback: T) -> T / {Stops} { perform Stop::stop() }
        selected() -> i64 {
            handle { fixture_abort(0) } { Stop::stop() => 42 }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-terminal-handler.gr", source).unwrap();
    let specialized = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name.starts_with("$specialization$fixture_abort#"))
        .unwrap();
    let stop = phases
        .artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Stop")
        .unwrap() as u32;
    assert_eq!(specialized.outward_protocols, [stop]);
    assert_eq!(specialized.flags, NO_RETURN);
    assert!(
        phases.artifact.code[specialized.code_start as usize
            ..(specialized.code_start + specialized.code_len) as usize]
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Perform { dst: None, .. }))
    );
    assert_eq!(
        run("generic-terminal-handler.gr", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn resumptive_generic_relay_preserves_the_row_through_two_planned_calls() {
    let source = r#"
        cases Questions = {Ask};
        effect Ask { [1,1] ask() -> i64 }
        leaf<T>(value: T) -> T / {Questions} {
            let answer = perform Ask::ask();
            value
        }
        relay<T>(value: T) -> T / {Questions} { leaf(value) }
        selected() -> i64 {
            handle { relay(42) } { Ask::ask() with continuation => resume(continuation, 7) }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-resumptive-relay.gr", source).unwrap();
    let ask = phases
        .artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Ask")
        .expect("missing source protocol `Ask`") as u32;
    for prefix in ["$specialization$leaf#", "$specialization$relay#"] {
        let specialized = phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name.starts_with(prefix))
            .unwrap();
        assert_eq!(specialized.outward_protocols, [ask]);
    }
    assert_eq!(
        run("generic-resumptive-relay.gr", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn grounded_mandatory_outward_call_carries_exact_argument_and_result() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Ask { [1,1] ask() -> i64 }
        relay<T>(value: T) -> T / {Ask} {
            let ignored = perform Ask::ask();
            value
        }
        selected() -> i64 {
            handle {
                let returned = relay(Ticket { serial: 42 });
                let Ticket { serial } = returned;
                serial
            } {
                Ask::ask() with continuation => resume(continuation, 0)
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-mandatory-linear-edge.gr", source).unwrap();
    let relay = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name.starts_with("$specialization$relay#"))
        .unwrap();
    let ask = phases
        .artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Ask")
        .expect("missing source protocol `Ask`") as u32;
    assert_eq!(relay.outward_protocols, [ask]);
    assert_eq!(
        run("generic-mandatory-linear-edge.gr", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn grounded_two_shot_call_weights_caller_and_callee_owners_independently() {
    let source = r#"
        struct Ticket { marker: i64 }
        impl Use<[2,2]> for Ticket {}
        effect Choose { [2,2] choose() -> i64 }
        relay<T>(fallback: T) -> T / {Choose} {
            let internal = Ticket { marker: 7 };
            let selected = perform Choose::choose();
            let Ticket { marker } = internal;
            fallback
        }
        selected() -> i64 {
            handle {
                let outer = Ticket { marker: 1 };
                let answer = relay(41);
                let Ticket { marker } = outer;
                answer + marker
            } {
                Choose::choose() with k => {
                    let ignored = resume(k, 19);
                    resume(move k, 41)
                }
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-two-shot-call-capture.gr", source).unwrap();
    assert!(
        phases
            .artifact
            .functions
            .iter()
            .any(|function| function.name.starts_with("$specialization$relay#"))
    );
    assert_eq!(
        run("generic-two-shot-call-capture.gr", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn grounded_two_shot_call_rejects_non_two_use_caller_owner() {
    let source = r#"
        struct Linear { marker: i64 }
        impl Use<[1,1]> for Linear {}
        effect Choose { [2,2] choose() -> i64 }
        choose<T>(fallback: T) -> T / {Choose} {
            let selected = perform Choose::choose();
            fallback
        }
        selected() -> i64 {
            handle {
                let linear = Linear { marker: 1 };
                let answer = choose(41);
                let Linear { marker } = linear;
                answer + marker
            } {
                Choose::choose() with k => {
                    let ignored = resume(k, 19);
                    resume(move k, 41)
                }
            }
        }
        main() -> { () }
    "#;
    assert_rejected(
        "generic-two-shot-invalid-caller-capture.gr",
        source,
        &[
            "requires every live restricted owner",
            "principal Use interval [2,2]",
        ],
    );
}

#[test]
fn mandatory_specialization_call_preserves_a_live_shared_loan() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        relay<T>(marker: T) -> i64 / {Ask} { marker; perform Ask::ask() }
        borrowed_call() -> i64 / {Ask} {
            let value = 40;
            let reference = &value;
            let answer = relay(0);
            reference;
            answer
        }
        selected() -> i64 {
            handle borrowed_call() {
                Ask::ask() with continuation => resume(continuation, 42)
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run("mandatory-specialization-loan.gr", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn optional_specialization_call_cancels_a_crossing_loan_cleanly() {
    let source = r#"
        effect Ask { [0,1] ask() -> i64 }
        relay<T>(marker: T) -> i64 / {Ask} { marker; perform Ask::ask() }
        borrowed_call() -> i64 / {Ask} {
            let value = 40;
            let reference = &value;
            let answer = relay(0);
            reference;
            answer
        }
        selected() -> i64 {
            handle borrowed_call() {
                Ask::ask() with continuation => { cancel(continuation); 42 }
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run("optional-specialization-loan.gr", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn optional_generic_outward_call_rejects_exact_caller_capture() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Ask { [0,1] ask() -> i64 }
        relay<T>(value: T) -> T / {Ask} {
            let ignored = perform Ask::ask();
            value
        }
        selected() -> i64 {
            handle {
                let ticket = Ticket { serial: 2 };
                let answer = relay(40);
                let Ticket { serial } = ticket;
                answer + serial
            } {
                Ask::ask() with continuation => { cancel(continuation); 0 }
            }
        }
        main() -> { () }
    "#;
    assert_rejected(
        "generic-optional-exact-caller-capture.gr",
        source,
        &[
            "restricted-use value at an effectful call",
            "path-sensitive Use analysis",
            "cancellation/abandonment path has actual Use count 0",
        ],
    );
}

#[test]
fn optional_generic_outward_call_cancels_affine_caller_capture_cleanly() {
    let source = r#"
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        impl Drop for Resource { drop(&mut self) -> { () } }
        effect Ask { [0,1] ask() -> i64 }
        relay<T>(value: T) -> T / {Ask} {
            let ignored = perform Ask::ask();
            value
        }
        selected() -> i64 {
            handle {
                let resource = Resource { marker: 2 };
                let answer = relay(40);
                resource;
                answer + 2
            } {
                Ask::ask() with continuation => { cancel(continuation); 42 }
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run("generic-optional-affine-cancel.gr", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn generic_body_may_handle_its_effect_internally_without_leaking_a_row() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        closed<T>(value: T) -> i64 {
            value;
            handle { perform Ask::ask() } {
                Ask::ask() with continuation => resume(continuation, 9)
            }
        }
        int_value() -> i64 { closed(42) }
        text_value() -> i64 { closed("closed") }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-internal-handler.gr", source).unwrap();
    let specializations = phases
        .artifact
        .functions
        .iter()
        .filter(|function| function.name.starts_with("$specialization$closed#"))
        .collect::<Vec<_>>();
    assert_eq!(specializations.len(), 2);
    assert!(
        specializations
            .iter()
            .all(|function| function.outward_protocols.is_empty())
    );
    assert_eq!(
        run("generic-internal-handler.gr", source, "int_value"),
        Value::I64(9)
    );
    assert_eq!(
        run("generic-internal-handler.gr", source, "text_value"),
        Value::I64(9)
    );
}

#[test]
fn the_handled_computation_may_be_a_nested_planned_generic_call() {
    let source = r#"
        effect Stop { stop() -> ! }
        leaf<T>(fallback: T) -> T / {Stop} { perform Stop::stop() }
        relay<T>(fallback: T) -> T / {Stop} { leaf(fallback) }
        selected() -> i64 {
            handle { relay(1) } { Stop::stop() => 73 }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("planned-generic-handler-body.gr", source).unwrap();
    let stop = phases
        .artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Stop")
        .unwrap() as u32;
    let handler = phases
        .artifact
        .handler_defs
        .iter()
        .position(|definition| {
            definition
                .clauses
                .iter()
                .any(|clause| clause.protocol == stop)
        })
        .expect("the source Stop handler must have a descriptor");
    let handler_name = format!("$handler${handler}$body");
    let handler_body = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == handler_name)
        .expect("the source Stop handler must have a body function");
    assert_eq!(handler_body.outward_protocols, [stop]);
    assert_eq!(
        run("planned-generic-handler-body.gr", source, "selected"),
        Value::I64(73)
    );
}

#[test]
fn nested_row_aliases_and_two_ground_instances_are_order_deterministic() {
    let declarations = r#"
        cases Stops = {Stop};
        cases Control = {Stops};
        effect Stop { stop() -> ! }
        fixture_abort<T>(fallback: T) -> T / {Control} { perform Stop::stop() }
    "#;
    let first = format!(
        r#"{declarations}
            int_value() -> i64 {{ handle {{ fixture_abort(0) }} {{ Stop::stop() => 42 }} }}
            text_value() -> Text {{ handle {{ fixture_abort("") }} {{ Stop::stop() => "stopped" }} }}
            main() -> {{ () }}
        "#
    );
    let reordered = format!(
        r#"{declarations}
            text_value() -> Text {{ handle {{ fixture_abort("") }} {{ Stop::stop() => "stopped" }} }}
            int_value() -> i64 {{ handle {{ fixture_abort(0) }} {{ Stop::stop() => 42 }} }}
            main() -> {{ () }}
        "#
    );
    let first_artifact = compile_source_to_bytecode("generic-ground-order-a.gr", &first).unwrap();
    let reordered_artifact =
        compile_source_to_bytecode("generic-ground-order-b.gr", &reordered).unwrap();
    assert_eq!(first_artifact.encode(), reordered_artifact.encode());
    assert_eq!(
        first_artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$fixture_abort#"))
            .count(),
        2
    );
    assert_eq!(
        run("generic-ground-order-a.gr", &first, "int_value"),
        Value::I64(42)
    );
    assert_eq!(
        run("generic-ground-order-a.gr", &first, "text_value"),
        Value::Text("stopped".into())
    );
}

#[test]
fn caller_of_an_effectful_ground_specialization_requires_the_complete_row() {
    let source = r#"
        effect Stop { stop() -> ! }
        fixture_abort<T>(fallback: T) -> T / {Stop} { perform Stop::stop() }
        missing() -> i64 { fixture_abort(0) }
        main() -> { () }
    "#;
    assert_rejected(
        "generic-missing-caller-row.gr",
        source,
        &["requires outward effect", "outward effect"],
    );
}

#[test]
fn terminal_generic_call_transfers_an_exact_linear_payload_once() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Consume { take(ticket: Ticket) -> ! }
        fixture_abort<T>(fallback: T, ticket: Ticket) -> T / {Consume} {
            perform Consume::take(ticket)
        }
        selected() -> i64 {
            handle { fixture_abort(0, Ticket { serial: 91 }) } {
                Consume::take(ticket) => {
                    let Ticket { serial } = ticket;
                    serial
                }
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run("generic-linear-terminal-payload.gr", source, "selected"),
        Value::I64(91)
    );
}

#[test]
fn fixed_positive_lower_local_moves_through_mandatory_one_shot_capture() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Ask { [1,1] ask() -> i64 }
        suspended<T>(value: T) -> T / {Ask} {
            let ticket = Ticket { serial: 1 };
            let answer = perform Ask::ask();
            let Ticket { serial } = ticket;
            value
        }
        selected() -> i64 {
            handle { suspended(42) } {
                Ask::ask() with continuation => resume(continuation, 0)
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run("generic-fixed-linear-capture.gr", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn direct_exact_owner_is_consumed_after_mandatory_resumption() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            handle {
                let ticket = Ticket { serial: 2 };
                let answer = perform Ask::ask();
                let Ticket { serial } = ticket;
                answer + serial
            } {
                Ask::ask() with continuation => resume(continuation, 40)
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run("direct-linear-continuation-capture.gr", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn owner_moved_before_perform_is_not_falsely_captured() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            handle {
                let ticket = Ticket { serial: 2 };
                let Ticket { serial } = ticket;
                let answer = perform Ask::ask();
                answer + serial
            } {
                Ask::ask() with continuation => resume(continuation, 40)
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run("moved-before-continuation-capture.gr", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn mandatory_resumption_does_not_relax_exact_owner_underuse_or_double_use() {
    let underused = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            handle {
                let ticket = Ticket { serial: 2 };
                let answer = perform Ask::ask();
                answer
            } {
                Ask::ask() with continuation => resume(continuation, 40)
            }
        }
        main() -> { () }
    "#;
    assert_rejected(
        "underused-linear-continuation-capture.gr",
        underused,
        &[
            "actual Use count 0",
            "requires at least 1 use",
            "required use",
        ],
    );

    let doubled = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            handle {
                let ticket = Ticket { serial: 2 };
                let answer = perform Ask::ask();
                let Ticket { serial } = ticket;
                ticket;
                answer + serial
            } {
                Ask::ask() with continuation => resume(continuation, 40)
            }
        }
        main() -> { () }
    "#;
    assert_rejected(
        "double-used-linear-continuation-capture.gr",
        doubled,
        &["already moved", "cannot be used again", "at most 1 use"],
    );
}

#[test]
fn affine_custom_drop_owner_crosses_mandatory_resumption_with_one_drop_glue() {
    let source = r#"
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        impl Drop for Resource { drop(&mut self) -> { () } }
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            handle {
                let resource = Resource { marker: 2 };
                let answer = perform Ask::ask();
                resource;
                answer
            } {
                Ask::ask() with continuation => resume(continuation, 42)
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("drop-continuation-capture.gr", source).unwrap();
    let resource = phases
        .artifact
        .types
        .iter()
        .position(
            |ty| matches!(ty.representation(), Type::Struct { name, .. } if name == "Resource"),
        )
        .unwrap() as u32;
    assert_eq!(
        phases
            .artifact
            .drop_glue
            .iter()
            .filter(|glue| glue.ty == resource)
            .count(),
        1
    );
    assert_eq!(
        run("drop-continuation-capture.gr", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn drop_reachability_cannot_hide_an_effectful_generic_specialization() {
    let source = r#"
        effect Stop { stop() -> ! }
        effectful<T>(value: T) -> T / {Stop} { perform Stop::stop() }
        struct Resource { marker: i64 }
        impl Drop for Resource {
            drop(&mut self) -> { effectful(1); () }
        }
        main() -> { let resource = Resource { marker: 0 }; () }
    "#;
    assert_rejected(
        "effectful-generic-drop-root.gr",
        source,
        &[
            "effectful call from Drop::drop",
            "requires outward effect",
            "outward effect",
        ],
    );
}

#[test]
fn drop_rejects_a_generic_specialization_with_internally_closed_control() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        closed<T>(value: T) -> i64 {
            value;
            handle { perform Ask::ask() } {
                Ask::ask() with continuation => resume(continuation, 5)
            }
        }
        struct Resource { marker: i64 }
        impl Drop for Resource {
            drop(&mut self) -> { closed(1); () }
        }
        main() -> { let resource = Resource { marker: 0 }; () }
    "#;
    assert_rejected(
        "closed-effect-generic-drop-root.gr",
        source,
        &["effectful call from Drop::drop", "pure, non-suspending"],
    );
}

#[test]
fn typed_handler_payload_infers_a_generic_clause_call_and_executes() {
    let source = r#"
        effect Stop { stop(value: i64) -> ! }
        sink<T>(value: T) -> T { value }
        selected() -> i64 {
            handle { perform Stop::stop(42) } {
                Stop::stop(value) => sink(value)
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("handler-payload-generic-inference.gr", source).unwrap();
    assert_eq!(
        phases
            .artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$sink#"))
            .count(),
        1
    );
    assert_eq!(
        run("handler-payload-generic-inference.gr", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn nested_enum_payload_binder_infers_a_generic_clause_call() {
    let source = r#"
        enum Payload { Empty, Value(i64) }
        effect Stop { stop(payload: Payload) -> ! }
        sink<T>(value: T) -> T { value }
        selected() -> i64 {
            handle { perform Stop::stop(Payload::Value(42)) } {
                Stop::stop(Payload::Value(value)) => sink(value),
                Stop::stop(Payload::Empty) => 0
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("nested-handler-generic-inference.gr", source).unwrap();
    assert_eq!(
        phases
            .artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$sink#"))
            .count(),
        1
    );
    assert_eq!(
        run("nested-handler-generic-inference.gr", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn generic_clause_call_can_consume_the_result_of_resume() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        sink<T>(value: T) -> T { value }
        selected() -> i64 {
            handle { perform Ask::ask() + 2 } {
                Ask::ask() with continuation => sink(resume(continuation, 40))
            }
        }
        main() -> { () }
    "#;
    let phases =
        compile_source_to_phases("resumption-result-generic-inference.gr", source).unwrap();
    assert_eq!(
        phases
            .artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$sink#"))
            .count(),
        1
    );
    assert_eq!(
        run("resumption-result-generic-inference.gr", source, "selected"),
        Value::I64(42)
    );
}
