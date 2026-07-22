use grandiose::{compile_source_to_bytecode, compile_source_to_phases};
use grandiose_vm::{Value, Vm, verify};

fn run(source: &str, name: &str) -> Value {
    let artifact = compile_source_to_bytecode("effectful-generic.glorious", source).unwrap();
    let function = artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap() as u32;
    Vm::new(verify(artifact).unwrap())
        .run(function, vec![])
        .unwrap()
}

#[test]
fn grounded_generic_terminal_effect_forwards_its_exact_row_and_executes() {
    let source = r#"
        effect Stop { stop() -> ! }
        fail<T>(fallback: T) -> T / {Stop} { perform Stop::stop() }
        test() -> i64 { handle { fail(1) } { Stop::stop() => 42 } }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-terminal.glorious", source).unwrap();
    let specialized = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name.starts_with("$specialization$fail#"))
        .unwrap();
    let stop = phases
        .artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Stop")
        .unwrap() as u32;
    assert_eq!(specialized.outward_protocols, [stop]);
    assert_eq!(run(source, "test"), Value::I64(42));
}

#[test]
fn grounded_generic_resumptive_effect_and_transitive_wrapper_execute() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        leaf<T>(value: T) -> T / {Ask} {
            let ignored = perform Ask::ask();
            value
        }
        relay<T>(value: T) -> T / {Ask} { leaf(value) }
        test() -> i64 {
            handle { relay(42) } { Ask::ask() with k => resume(k, 7) }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-resumptive.glorious", source).unwrap();
    let ask = phases
        .artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Ask")
        .expect("missing source protocol `Ask`") as u32;
    for prefix in ["$specialization$leaf#", "$specialization$relay#"] {
        let function = phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name.starts_with(prefix))
            .unwrap();
        assert_eq!(function.outward_protocols, [ask]);
    }
    assert_eq!(run(source, "test"), Value::I64(42));
}

#[test]
fn effectful_specialization_grounds_generic_nominal_signatures() {
    let source = r#"
        struct Box<T> { value: T }
        effect Stop { stop() -> ! }
        fail<T>(fallback: Box<T>) -> Box<T> / {Stop} { perform Stop::stop() }
        select() -> Box<i64> {
            handle { fail(Box { value: 0 }) } {
                Stop::stop() => Box { value: 42 }
            }
        }
        test() -> i64 { select().value }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("generic-nominal-effect.glorious", source).unwrap();
    let specialized = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name.starts_with("$specialization$fail#"))
        .unwrap();
    let stop = phases
        .artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Stop")
        .unwrap() as u32;
    assert_eq!(specialized.outward_protocols, [stop]);
    assert_eq!(run(source, "test"), Value::I64(42));
}

#[test]
fn grounded_generic_body_may_close_an_effect_with_its_own_handler() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        closed<T>(marker: T) -> i64 {
            handle { perform Ask::ask() } {
                Ask::ask() with k => resume(k, 42)
            }
        }
        test() -> i64 { closed(0) }
        main() -> { () }
    "#;
    assert_eq!(run(source, "test"), Value::I64(42));
}

#[test]
fn effectful_specialization_ids_and_rows_are_declaration_order_independent() {
    let declarations = r#"
        effect Stop { stop() -> ! }
        relay<T>(value: T) -> T / {Stop} { perform Stop::stop() }
    "#;
    let first = format!(
        "{declarations} alpha() -> i64 / {{Stop}} {{ relay(1) }} zeta() -> Text / {{Stop}} {{ relay(\"z\") }} main() -> {{ () }}"
    );
    let second = format!(
        "{declarations} zeta() -> Text / {{Stop}} {{ relay(\"z\") }} alpha() -> i64 / {{Stop}} {{ relay(1) }} main() -> {{ () }}"
    );
    let first = compile_source_to_bytecode("generic-order-a.glorious", &first).unwrap();
    let second = compile_source_to_bytecode("generic-order-b.glorious", &second).unwrap();
    assert_eq!(first.encode(), second.encode());
}

#[test]
fn grounded_generic_effects_require_exact_outward_evidence() {
    for source in [
        "effect Stop { stop() -> ! } fail<T>(value: T) -> T { perform Stop::stop() } test() -> i64 { handle { fail(1) } { Stop::stop() => 2 } } main() -> { () }",
        "effect Stop { stop() -> ! } fail<T>(value: T) -> T / {Stop} { perform Stop::stop() } call() -> i64 { fail(1) } main() -> { () }",
    ] {
        let errors =
            compile_source_to_bytecode("generic-row-missing.glorious", source).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.message.contains("outward effect")
                    || error.message.contains("requires outward effect")
            }),
            "{errors:#?}"
        );
    }
}

#[test]
fn terminal_generic_specialization_transfers_exact_linear_payload() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Consume { take(ticket: Ticket) -> ! }
        fail<T>(fallback: T, ticket: Ticket) -> T / {Consume} {
            perform Consume::take(ticket)
        }
        test() -> i64 {
            handle { fail(0, Ticket { serial: 42 }) } {
                Consume::take(ticket) => {
                    let Ticket { serial } = ticket;
                    serial
                }
            }
        }
        main() -> { () }
    "#;
    assert_eq!(run(source, "test"), Value::I64(42));
}

#[test]
fn resumptive_generic_specialization_carries_exact_linear_owner_once() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Ask { [1,1] ask() -> i64 }
        hold<T>(value: T) -> T / {Ask} {
            let ignored = perform Ask::ask();
            value
        }
        handled() -> Ticket {
            handle { hold(Ticket { serial: 42 }) } {
                Ask::ask() with k => resume(k, 0)
            }
        }
        test() -> i64 {
            let ticket = handled();
            let Ticket { serial } = ticket;
            serial
        }
        main() -> { () }
    "#;
    assert_eq!(run(source, "test"), Value::I64(42));
}

#[test]
fn drop_cannot_hide_effect_control_inside_a_closed_generic_specialization() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        closed<T>(marker: T) -> i64 {
            handle { perform Ask::ask() } {
                Ask::ask() with k => resume(k, 1)
            }
        }
        struct Resource { marker: i64 }
        impl Drop for Resource {
            drop(&mut self) -> { closed(0); () }
        }
        main() -> { let resource = Resource { marker: 0 }; () }
    "#;
    let errors = compile_source_to_bytecode("generic-closed-drop.glorious", source).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("effectful call from Drop::drop")),
        "{errors:#?}"
    );
}
