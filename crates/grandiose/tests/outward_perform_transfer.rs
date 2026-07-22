use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_phases_with_options,
};
use grandiose_vm::{RuntimeError, Value, Vm, verify};

const LEVELS: [OptimizationLevel; 3] = [
    OptimizationLevel::O1,
    OptimizationLevel::O2,
    OptimizationLevel::O3,
];

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

#[test]
fn declared_perform_crosses_named_callers_and_transfers_its_owned_payload_at_every_level() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Deliver { [1,1] deliver(ticket: Ticket) -> i64 }

        leaf(ticket: Ticket) -> i64 / {Deliver} {
            perform Deliver::deliver(move ticket)
        }
        forward(ticket: Ticket) -> i64 / {Deliver} {
            leaf(move ticket) + 2
        }
        selected() -> i64 {
            handle forward(Ticket { value: 40 }) {
                Deliver::deliver(Ticket { value }) with continuation => {
                    resume(continuation, value)
                }
            }
        }
        main() -> { selected(); () }
    "#;

    for optimization_level in LEVELS {
        let phases = compile_source_to_phases_with_options(
            "outward-owned-payload.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let selected = function_id(&phases.artifact, "selected");
        let verified = verify(phases.artifact).unwrap_or_else(|error| {
            panic!("{optimization_level:?}: verifier rejected artifact: {error}")
        });
        assert_eq!(
            Vm::new(verified).run(selected, vec![]).unwrap(),
            Value::I64(42),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn outward_reference_payload_keeps_its_origin_through_callers_at_every_level() {
    let source = r#"
        effect Observe { [1,1] inspect(value: &i64) -> i64 }

        leaf<'a>(value: &'a i64) -> i64 / {Observe} {
            perform Observe::inspect(value)
        }
        forward<'a>(value: &'a i64) -> i64 / {Observe} {
            leaf(value) + 2
        }
        selected() -> i64 {
            let value = 40;
            handle forward(&value) {
                Observe::inspect(reference) with continuation => {
                    resume(continuation, *reference)
                }
            }
        }
        main() -> { selected(); () }
    "#;

    for optimization_level in LEVELS {
        let phases = compile_source_to_phases_with_options(
            "outward-reference-payload.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let selected = function_id(&phases.artifact, "selected");
        let verified = verify(phases.artifact).unwrap_or_else(|error| {
            panic!("{optimization_level:?}: verifier rejected artifact: {error}")
        });
        assert_eq!(
            Vm::new(verified).run(selected, vec![]).unwrap(),
            Value::I64(42),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn an_uncaught_declared_perform_reaches_the_vm_boundary_at_every_level() {
    let source = r#"
        effect Ask { [1,1] ask(value: i64) -> i64 }
        leaf() -> i64 / {Ask} { perform Ask::ask(42) }
        main() -> { () }
    "#;

    for optimization_level in LEVELS {
        let phases = compile_source_to_phases_with_options(
            "uncaught-outward-perform.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let leaf = function_id(&phases.artifact, "leaf");
        let protocol = phases
            .artifact
            .protocols
            .iter()
            .position(|protocol| protocol.display_name == "Ask")
            .unwrap() as u32;
        let verified = verify(phases.artifact).unwrap_or_else(|error| {
            panic!("{optimization_level:?}: verifier rejected artifact: {error}")
        });
        assert_eq!(
            Vm::new(verified).run(leaf, vec![]),
            Err(RuntimeError::UnhandledEffect {
                protocol,
                operation: 0,
            }),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn outward_transfer_requires_declaration_at_each_source_boundary() {
    let cases = [
        (
            "undeclared-perform.glorious",
            r#"
                effect Ask { [1,1] ask() -> i64 }
                bad() -> i64 { perform Ask::ask() }
                main() -> { () }
            "#,
            "outward effect performance",
        ),
        (
            "undeclared-caller.glorious",
            r#"
                effect Ask { [1,1] ask() -> i64 }
                leaf() -> i64 / {Ask} { perform Ask::ask() }
                bad() -> i64 { leaf() }
                main() -> { () }
            "#,
            "outward effectful call",
        ),
        (
            "wrong-effect-instance.glorious",
            r#"
                effect Fail<T> { fail(value: T) -> ! }
                bad() -> ! / {Fail<Text>} { perform Fail<i64>::fail(42) }
                main() -> { () }
            "#,
            "outward effect performance",
        ),
        (
            "reused-perform-payload.glorious",
            r#"
                struct Ticket { value: i64 }
                impl Use<[1,1]> for Ticket {}
                effect Deliver { [1,1] deliver(ticket: Ticket) -> i64 }
                bad(ticket: Ticket) -> i64 / {Deliver} {
                    let answer = perform Deliver::deliver(move ticket);
                    ticket.value + answer
                }
                main() -> { () }
            "#,
            "already moved",
        ),
        (
            "effectful-entry.glorious",
            r#"
                effect Ask { [1,1] ask() -> i64 }
                main() -> () / {Ask} { perform Ask::ask(); () }
            "#,
            "invalid bytecode entry callable",
        ),
    ];

    for (name, source, expected) in cases {
        let errors = compile_source_to_bytecode(name, source).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.title.contains(expected) || error.message.contains(expected)
            }),
            "expected `{expected}` in {errors:#?}"
        );
    }
}
