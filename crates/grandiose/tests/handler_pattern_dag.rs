use grandiose::{
    compile_bundle_to_bytecode, compile_source_to_bytecode, compile_source_to_phases,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{Instruction, Primitive, Value, Vm, verify};

fn run_function(source_name: &str, source: &str, function_name: &str) -> Value {
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

fn has_message(source_name: &str, source: &str, needles: &[&str]) {
    let diagnostics = compile_source_to_bytecode(source_name, source).unwrap_err();
    assert!(
        diagnostics.iter().any(|diagnostic| {
            needles
                .iter()
                .all(|needle| diagnostic.message.contains(needle))
        }),
        "expected one diagnostic containing {needles:?}, got {diagnostics:#?}"
    );
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code.is_some()),
        "portable diagnostics must remain structured: {diagnostics:#?}"
    );
}

const ORDERED_MATRIX: &str = r#"
    enum Inner { None, Some(i64) }
    enum Shape { Other, Wrap(Inner) }
    effect Dispatch {
        route(shape: Shape, marker: Unit, number: i64, text: Text) -> !
        emergency(marker: Unit) -> !
    }

    selected() -> i64 {
        handle perform Dispatch::route(
            Shape::Wrap(Inner::Some(40)), (), 7, "hit"
        ) {
            Dispatch::route(Shape::Wrap(Inner::Some(value)), (), 7, "hit") => value + 2,
            Dispatch::emergency(_) => 900,
            Dispatch::route(Shape::Wrap(Inner::Some(value)), _, _, _) => value + 100,
            Dispatch::route(Shape::Wrap(Inner::None), _, number, _) => number,
            Dispatch::route(Shape::Other, marker, number, text) => number
        }
    }
    main() -> { selected(); () }
"#;

#[test]
fn repeated_operation_clauses_form_one_ordered_nested_decision_dag() {
    let phases =
        compile_source_to_phases("ordered-handler-matrix.glorious", ORDERED_MATRIX).unwrap();

    // Runtime handler lookup is by protocol/operation. Repeated source rows must
    // therefore be grouped behind one descriptor for `route`, not serialized as
    // several indistinguishable runtime clauses.
    let dispatch = phases
        .artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Dispatch")
        .unwrap() as u32;
    let dispatch_handler = phases
        .artifact
        .handler_defs
        .iter()
        .find(|definition| {
            definition
                .clauses
                .iter()
                .any(|clause| clause.protocol == dispatch)
        })
        .expect("Dispatch must have a handler descriptor");
    assert_eq!(
        dispatch_handler
            .clauses
            .iter()
            .map(|clause| (clause.protocol, clause.operation))
            .collect::<Vec<_>>(),
        [(dispatch, 0), (dispatch, 1)]
    );
    assert!(
        phases
            .artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::EnumTag { .. }))
    );
    assert!(
        phases
            .artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Switch { .. }))
    );
    assert!(phases.artifact.code.iter().any(|instruction| {
        matches!(
            instruction,
            Instruction::Primitive {
                op: Primitive::IntEq | Primitive::TextEq,
                ..
            }
        )
    }));

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
        Value::I64(42)
    );
}

#[test]
fn first_matching_row_wins_over_later_nested_fallbacks() {
    assert_eq!(
        run_function(
            "ordered-handler-matrix.glorious",
            ORDERED_MATRIX,
            "selected"
        ),
        Value::I64(42)
    );
}

#[test]
fn failed_scalar_literal_tests_preserve_the_scrutinee_for_a_binding_fallback() {
    let source = r#"
        effect Select { select(number: i64, text: Text) -> ! }
        selected() -> i64 {
            handle perform Select::select(8, "miss") {
                Select::select(7, "hit") => 1,
                Select::select(8, text) => 42,
                Select::select(number, text) => number
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("scalar-pattern-fallback.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn a_closed_enum_without_all_variants_is_not_a_total_handler() {
    let source = r#"
        enum State { Cold, Hot }
        effect Stop { stop(state: State) -> ! }
        bad() -> i64 {
            handle perform Stop::stop(State::Hot) {
                Stop::stop(State::Hot) => 1
            }
        }
        main() -> { () }
    "#;
    has_message(
        "non-exhaustive-handler.glorious",
        source,
        &["non-exhaustive"],
    );
}

#[test]
fn a_non_exhaustive_matrix_is_partial_and_retains_its_outward_protocol() {
    let source = r#"
        enum State { Cold, Hot }
        effect Stop { stop(state: State) -> ! reset() -> ! }
        cold() -> ! / {Stop} { perform Stop::stop(State::Cold) }
        partial() -> i64 / {Stop} {
            handle { cold() } {
                Stop::stop(State::Hot) => 1
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("partial-pattern-handler.glorious", source).unwrap();
    let partial = artifact
        .functions
        .iter()
        .find(|function| function.name == "partial")
        .unwrap();
    let stop = artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Stop")
        .unwrap() as u32;
    let stop_handler = artifact
        .handler_defs
        .iter()
        .find(|definition| {
            definition
                .clauses
                .iter()
                .any(|clause| clause.protocol == stop)
        })
        .expect("Stop must have a handler descriptor");
    assert!(stop_handler.partial);
    assert_eq!(partial.outward_protocols, [stop]);
    verify(artifact).unwrap();
}

#[test]
fn exclusive_handler_rows_join_use_by_hull_and_discharge_must_move_payloads() {
    let source = r#"
        struct Token { marker: i64 }
        impl Use<[1,1]> for Token {}
        enum Choice { Left(Token), Right(Token) }
        impl Use<[1,1]> for Choice {}
        effect Stop { stop(choice: Choice) -> ! }

        selected() -> i64 {
            handle perform Stop::stop(Choice::Right(Token { marker: 42 })) {
                Stop::stop(Choice::Left(token)) => {
                    let Token { marker } = token;
                    marker
                },
                Stop::stop(Choice::Right(token)) => {
                    let Token { marker } = token;
                    marker
                }
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("handler-use-hull.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn wildcard_payload_destruction_cannot_erase_a_must_move_child() {
    let source = r#"
        struct Token {}
        impl Use<[1,1]> for Token {}
        enum Choice { Left(Token), Right(Token) }
        impl Use<[1,1]> for Choice {}
        effect Stop { stop(choice: Choice) -> ! }
        bad() -> Unit {
            handle perform Stop::stop(Choice::Left(Token {})) {
                Stop::stop(Choice::Left(_)) => (),
                Stop::stop(Choice::Right(token)) => { let Token {} = token; () }
            }
        }
        main() -> { () }
    "#;
    has_message(
        "handler-must-move-discard.glorious",
        source,
        &["discard", "[0,0]"],
    );
}

#[test]
fn handler_clause_bodies_preserve_the_pattern_sites_privacy_authority() {
    let same_authority = r#"
        struct Secret { private marker: i64 }
        enum Packet { Wrapped(Secret) }
        effect Stop { stop(packet: Packet) -> ! }
        selected() -> i64 {
            handle perform Stop::stop(Packet::Wrapped(Secret { marker: 42 })) {
                Stop::stop(Packet::Wrapped(secret)) => {
                    let Secret { marker } = secret;
                    marker
                }
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("private-handler-owner.glorious", same_authority, "selected"),
        Value::I64(42)
    );

    let bundle = SourceBundle::new(
        Segment::new(
            "owner.glorious",
            r#"
                struct Secret { private marker: i64 }
                enum Packet { Wrapped(Secret) }
                effect Stop { stop(packet: Packet) -> ! }
                make_packet() -> Packet { Packet::Wrapped(Secret { marker: 42 }) }
            "#,
        ),
        Segment::new(
            "outsider.glorious",
            r#"
                bad() -> i64 {
                    handle perform Stop::stop(make_packet()) {
                        Stop::stop(Packet::Wrapped(secret)) => {
                            let Secret { marker } = secret;
                            marker
                        }
                    }
                }
            "#,
        ),
        [Segment::new("entry.glorious", "main() -> { () }")],
    );
    let diagnostics = compile_bundle_to_bytecode(&bundle).unwrap_err();
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.message.contains("private")
                && diagnostic.message.contains("marker")
                && diagnostic.message.contains("authority")
        }),
        "got {diagnostics:#?}"
    );
}

#[test]
fn exhaustive_pattern_dispatch_does_not_bypass_custom_drop() {
    let source = r#"
        enum Flag { Off, On }
        impl Drop for Flag { drop(&mut self) -> { () } }
        effect Stop { stop(flag: Flag) -> ! }
        bad() -> i64 {
            handle perform Stop::stop(Flag::On) {
                Stop::stop(Flag::Off) => 0,
                Stop::stop(Flag::On) => 1
            }
        }
        main() -> { () }
    "#;
    has_message(
        "handler-custom-drop.glorious",
        source,
        &["custom Drop", "pattern"],
    );
}

#[test]
fn binders_are_unique_across_an_entire_nested_handler_row() {
    let source = r#"
        enum Pair { Both(i64, i64) }
        effect Stop { stop(pair: Pair) -> ! }
        bad() -> i64 {
            handle perform Stop::stop(Pair::Both(1, 2)) {
                Stop::stop(Pair::Both(value, value)) => value
            }
        }
        main() -> { () }
    "#;
    has_message(
        "duplicate-nested-handler-binding.glorious",
        source,
        &["binding `value`", "more than once"],
    );
}

#[test]
fn terminal_pattern_miss_forwards_exact_linear_payload_to_an_outer_handler() {
    let source = r#"
        struct Token { marker: i64 }
        impl Use<[1,1]> for Token {}
        enum Choice { Empty, Full(Token) }
        impl Use<[1,1]> for Choice {}
        effect Stop { stop(choice: Choice) -> ! }

        trigger_stop() -> i64 / {Stop} {
            perform Stop::stop(Choice::Full(Token { marker: 42 }))
        }
        inner() -> i64 / {Stop} {
            handle { trigger_stop() } {
                Stop::stop(Choice::Empty) => 0
            }
        }
        selected() -> i64 {
            handle { inner() } {
                Stop::stop(Choice::Empty) => 1,
                Stop::stop(Choice::Full(token)) => {
                    let Token { marker } = token;
                    marker
                }
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("terminal-pattern-forward.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn absent_operation_in_partial_handler_forwards_to_outer_delimiter() {
    let source = r#"
        enum State { Cold, Hot }
        effect Stop { stop(state: State) -> ! reset() -> ! }
        trigger_stop() -> i64 / {Stop} { perform Stop::reset() }
        inner() -> i64 / {Stop} {
            handle { trigger_stop() } {
                Stop::stop(State::Cold) => 0,
                Stop::stop(State::Hot) => 1
            }
        }
        selected() -> i64 {
            handle { inner() } {
                Stop::stop(State::Cold) => 2,
                Stop::stop(State::Hot) => 3,
                Stop::reset() => 77
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("missing-operation-forward.glorious", source, "selected"),
        Value::I64(77)
    );
}

#[test]
fn resumptive_pattern_miss_forwards_then_resumes_the_original_continuation() {
    let source = r#"
        enum State { Cold, Hot }
        effect Ask { [1,1] ask(state: State) -> i64 }
        request() -> i64 / {Ask} { perform Ask::ask(State::Hot) + 2 }
        inner() -> i64 / {Ask} {
            handle { request() } {
                Ask::ask(State::Cold) with k => resume(k, 1)
            }
        }
        selected() -> i64 {
            handle { inner() } {
                Ask::ask(State::Cold) with k => resume(k, 10),
                Ask::ask(State::Hot) with k => resume(k, 40)
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("resumptive-pattern-forward.glorious", source, "selected"),
        Value::I64(42)
    );
}
