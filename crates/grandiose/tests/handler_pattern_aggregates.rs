//! Recursive tuple and named-struct patterns in effect-handler clauses:
//! clause selection, nesting with variants/literals, ownership transfer and
//! discard rules, privacy, exhaustiveness, and recovery/compiled parity.

use grandiose::{
    CompileOptions, OptimizationLevel, compile_bundle_to_bytecode, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options,
    eval::{Host, Value as RecoveryValue},
    run_source,
    source_bundle::{Segment, SourceBundle},
    span::Span,
};
use grandiose_vm::{Value, Vm, verify};

#[derive(Default)]
struct NoHost;

impl Host for NoHost {
    fn perform(
        &mut self,
        _effect: &str,
        _operation: &str,
        _args: Vec<RecoveryValue>,
        span: Span,
    ) -> Result<RecoveryValue, grandiose::diagnostic::Diagnostic> {
        Err(grandiose::diagnostic::Diagnostic::error(
            "unexpected effect",
            "handler aggregate-pattern test performed a host effect",
            span,
        ))
    }
}

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
}

#[test]
fn flat_tuple_patterns_select_clauses_by_scalar_literals() {
    let source = r#"
        effect Pick { pick(pair: (i64, Text)) -> ! }
        selected() -> i64 {
            handle perform Pick::pick((8, "hit")) {
                Pick::pick((7, "hit")) => 1,
                Pick::pick((8, "miss")) => 2,
                Pick::pick((8, "hit")) => 42,
                Pick::pick((number, text)) => number
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("flat-tuple-pattern.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn deeply_nested_tuple_patterns_bind_every_leaf_once() {
    let source = r#"
        effect Pick { pick(value: ((i64, (Text, i64)), i64)) -> ! }
        selected() -> i64 {
            handle perform Pick::pick(((30, ("go", 11)), 1)) {
                Pick::pick(((a, ("stop", b)), c)) => 0 - a - b - c,
                Pick::pick(((a, ("go", b)), c)) => a + b + c,
                Pick::pick(rest) => 0
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("deep-tuple-pattern.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn struct_pattern_fields_match_in_declaration_independent_order() {
    let source = r#"
        struct Point { x: i64, y: i64, tag: Text }
        effect Pick { pick(point: Point) -> ! }
        selected() -> i64 {
            handle perform Pick::pick(Point { x: 2, y: 40, tag: "keep" }) {
                Pick::pick(Point { tag: "drop", y, x }) => 0 - y - x,
                Pick::pick(Point { y, tag: "keep", x }) => y + x,
                Pick::pick(Point { x, y, tag }) => 7
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("struct-field-order.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn structs_nest_inside_variants_and_tuples() {
    let source = r#"
        struct Point { x: i64, y: i64 }
        enum Shape { Empty, At(Point) }
        effect Pick { pick(value: (Shape, i64)) -> ! }
        selected() -> i64 {
            handle perform Pick::pick((Shape::At(Point { x: 2, y: 30 }), 10)) {
                Pick::pick((Shape::Empty, bonus)) => bonus,
                Pick::pick((Shape::At(Point { x, y }), bonus)) => x + y + bonus
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("struct-in-variant-in-tuple.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn tuple_remainder_discards_only_zero_use_middles() {
    let source = r#"
        effect Pick { pick(value: (i64, Text, Text, i64)) -> ! }
        selected() -> i64 {
            handle perform Pick::pick((40, "a", "b", 2)) {
                Pick::pick((first, .., last)) => first + last
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("tuple-remainder.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn short_tuple_patterns_implicitly_discard_the_suffix() {
    let source = r#"
        effect Pick { pick(value: (i64, Text, i64)) -> ! }
        selected() -> i64 {
            handle perform Pick::pick((42, "discarded", 99)) {
                Pick::pick((first,)) => first
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("tuple-implicit-suffix.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn variant_middle_rest_and_short_suffix_omission_match_from_the_right_places() {
    let source = r#"
        enum Packet { Data(i64, Text, Text, i64), Empty }
        effect Pick { pick(value: Packet) -> ! }
        middle() -> i64 {
            handle perform Pick::pick(Packet::Data(40, "a", "b", 2)) {
                Pick::pick(Packet::Data(first, .., last)) => first + last,
                Pick::pick(Packet::Empty) => 0
            }
        }
        short() -> i64 {
            handle perform Pick::pick(Packet::Data(42, "a", "b", 99)) {
                Pick::pick(Packet::Data(first)) => first,
                Pick::pick(Packet::Empty) => 0
            }
        }
        main() -> { middle(); short(); () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "variant-remainder-and-omission.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let artifact = verify(artifact).unwrap();
        for function_name in ["middle", "short"] {
            let function = artifact
                .artifact()
                .functions
                .iter()
                .position(|function| function.name == function_name)
                .unwrap() as u32;
            assert_eq!(
                Vm::new(artifact.clone()).run(function, vec![]).unwrap(),
                Value::I64(42),
                "{function_name} changed at {optimization_level:?}"
            );
        }
    }
}

#[test]
fn struct_remainder_discards_only_zero_use_fields() {
    let source = r#"
        struct Wide { a: i64, b: Text, c: i64, d: Text }
        effect Pick { pick(value: Wide) -> ! }
        selected() -> i64 {
            handle perform Pick::pick(Wide { a: 40, b: "x", c: 2, d: "y" }) {
                Pick::pick(Wide { a, c, .. }) => a + c
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("struct-remainder.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn exact_linear_fields_transfer_their_obligation_to_the_binding() {
    let source = r#"
        struct Token { marker: i64 }
        impl Use<[1,1]> for Token {}
        effect Stop { stop(value: (Token, i64)) -> ! }
        selected() -> i64 {
            handle perform Stop::stop((Token { marker: 40 }, 2)) {
                Stop::stop((token, bonus)) => {
                    let Token { marker } = token;
                    marker + bonus
                }
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("tuple-linear-transfer.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn exact_linear_struct_fields_transfer_through_named_patterns() {
    let source = r#"
        struct Token { marker: i64 }
        impl Use<[1,1]> for Token {}
        struct Carrier { token: Token, bonus: i64 }
        impl Use<[1,1]> for Carrier {}
        effect Stop { stop(value: Carrier) -> ! }
        selected() -> i64 {
            handle perform Stop::stop(Carrier { token: Token { marker: 40 }, bonus: 2 }) {
                Stop::stop(Carrier { bonus, token }) => {
                    let Token { marker } = token;
                    marker + bonus
                }
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("struct-linear-transfer.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn tuple_wildcard_cannot_erase_an_exact_linear_element() {
    let source = r#"
        struct Token { marker: i64 }
        impl Use<[1,1]> for Token {}
        effect Stop { stop(value: (Token, i64)) -> ! }
        bad() -> i64 {
            handle perform Stop::stop((Token { marker: 1 }, 2)) {
                Stop::stop((_, bonus)) => bonus
            }
        }
        main() -> { () }
    "#;
    has_message(
        "tuple-linear-wildcard.glorious",
        source,
        &["discard", "[0,0]"],
    );
}

#[test]
fn tuple_remainder_cannot_erase_an_exact_linear_element() {
    let source = r#"
        struct Token { marker: i64 }
        impl Use<[1,1]> for Token {}
        effect Stop { stop(value: (Token, i64)) -> ! }
        bad() -> i64 {
            handle perform Stop::stop((Token { marker: 1 }, 2)) {
                Stop::stop((.., bonus)) => bonus
            }
        }
        main() -> { () }
    "#;
    has_message(
        "tuple-linear-remainder.glorious",
        source,
        &["discarded tuple element", "zero-use disposal"],
    );
}

#[test]
fn implicit_tuple_suffix_cannot_erase_an_exact_linear_element() {
    let source = r#"
        struct Token { marker: i64 }
        impl Use<[1,1]> for Token {}
        effect Stop { stop(value: (i64, Token)) -> ! }
        bad() -> i64 {
            handle perform Stop::stop((2, Token { marker: 1 })) {
                Stop::stop((bonus,)) => bonus
            }
        }
        main() -> { () }
    "#;
    has_message(
        "tuple-linear-implicit-suffix.glorious",
        source,
        &["discarded tuple element", "zero-use disposal"],
    );
}

#[test]
fn implicit_variant_suffix_cannot_erase_an_exact_linear_element() {
    let source = r#"
        struct Token { marker: i64 }
        impl Use<[1,1]> for Token {}
        enum Packet { Data(i64, Token) }
        effect Stop { stop(value: Packet) -> ! }
        bad() -> i64 {
            handle perform Stop::stop(Packet::Data(2, Token { marker: 1 })) {
                Stop::stop(Packet::Data(bonus)) => bonus
            }
        }
        main() -> { () }
    "#;
    has_message(
        "variant-linear-implicit-suffix.glorious",
        source,
        &["discarded variant payload field", "zero-use disposal"],
    );
}

#[test]
fn struct_remainder_cannot_erase_an_exact_linear_field() {
    let source = r#"
        struct Token { marker: i64 }
        impl Use<[1,1]> for Token {}
        struct Carrier { token: Token, bonus: i64 }
        impl Use<[1,1]> for Carrier {}
        effect Stop { stop(value: Carrier) -> ! }
        bad() -> i64 {
            handle perform Stop::stop(Carrier { token: Token { marker: 1 }, bonus: 2 }) {
                Stop::stop(Carrier { bonus, .. }) => bonus
            }
        }
        main() -> { () }
    "#;
    has_message(
        "struct-linear-remainder.glorious",
        source,
        &["discarded field `token`", "zero-use disposal"],
    );
}

#[test]
fn struct_patterns_reject_unknown_fields() {
    let source = r#"
        struct Point { x: i64, y: i64 }
        effect Pick { pick(point: Point) -> ! }
        bad() -> i64 {
            handle perform Pick::pick(Point { x: 1, y: 2 }) {
                Pick::pick(Point { x, z, .. }) => x
            }
        }
        main() -> { () }
    "#;
    has_message(
        "struct-unknown-field.glorious",
        source,
        &["no field named `z`"],
    );
}

#[test]
fn struct_patterns_without_remainder_implicitly_discard_missing_fields() {
    let source = r#"
        struct Point { x: i64, y: i64 }
        effect Pick { pick(point: Point) -> ! }
        selected() -> i64 {
            handle perform Pick::pick(Point { x: 1, y: 2 }) {
                Pick::pick(Point { x }) => x
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("struct-implicit-omission.glorious", source, "selected"),
        Value::I64(1)
    );
}

#[test]
fn duplicate_struct_pattern_fields_are_rejected_at_parse_time() {
    let source = r#"
        struct Point { x: i64, y: i64 }
        effect Pick { pick(point: Point) -> ! }
        bad() -> i64 {
            handle perform Pick::pick(Point { x: 1, y: 2 }) {
                Pick::pick(Point { x, x, .. }) => x
            }
        }
        main() -> { () }
    "#;
    let diagnostics =
        compile_source_to_bytecode("struct-duplicate-field.glorious", source).unwrap_err();
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("field `x` appears more than once")
        }),
        "got {diagnostics:#?}"
    );
}

#[test]
fn tuple_pattern_arity_must_match_the_payload() {
    let source = r#"
        effect Pick { pick(pair: (i64, i64)) -> ! }
        bad() -> i64 / {Pick} {
            handle perform Pick::pick((1, 2)) {
                Pick::pick((a, b, c)) => a
            }
        }
        main() -> { () }
    "#;
    has_message(
        "tuple-arity-mismatch.glorious",
        source,
        &["expects at most 2 element(s), got 3"],
    );
}

#[test]
fn variant_pattern_rejects_excess_entries() {
    let source = r#"
        enum Packet { Data(i64, i64) }
        effect Pick { pick(value: Packet) -> ! }
        bad() -> i64 {
            handle perform Pick::pick(Packet::Data(1, 2)) {
                Pick::pick(Packet::Data(a, b, c)) => a
            }
        }
        main() -> { () }
    "#;
    has_message(
        "variant-arity-mismatch.glorious",
        source,
        &["has 2 field(s)", "supplies 3 explicit"],
    );
}

#[test]
fn implicit_omission_does_not_bypass_custom_drop() {
    let source = r#"
        struct Guard { marker: i64, spare: i64 }
        impl Drop for Guard { drop(&mut self) -> { self.marker; () } }
        effect Stop { stop(value: Guard) -> ! }
        bad() -> i64 {
            handle perform Stop::stop(Guard { marker: 1, spare: 2 }) {
                Stop::stop(Guard { marker }) => marker
            }
        }
        main() -> { () }
    "#;
    has_message("implicit-custom-drop.glorious", source, &["custom Drop"]);
}

#[test]
fn private_struct_fields_reject_handler_patterns_outside_their_segment() {
    let bundle = SourceBundle::new(
        Segment::new(
            "owner.glorious",
            r#"
                struct Secret { private marker: i64 }
                effect Stop { stop(secret: Secret) -> ! }
                make_secret() -> Secret { Secret { marker: 42 } }
            "#,
        ),
        Segment::new(
            "outsider.glorious",
            r#"
                bad() -> i64 {
                    handle perform Stop::stop(make_secret()) {
                        Stop::stop(Secret {}) => 0
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
fn private_struct_fields_match_inside_their_own_segment() {
    let source = r#"
        struct Secret { private marker: i64 }
        effect Stop { stop(secret: Secret) -> ! }
        selected() -> i64 {
            handle perform Stop::stop(Secret { marker: 42 }) {
                Stop::stop(Secret { marker }) => marker
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("private-same-segment.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn irrefutable_aggregate_rows_keep_the_handler_total() {
    // Neither callable declares `/ {Pick}`: if aggregate rows were not
    // recognized as exhaustive, the handler would be partial and the missing
    // outward-protocol declaration would fail compilation.
    let source = r#"
        struct Point { x: i64, y: i64 }
        effect Pick {
            at(point: Point) -> !
            pair(value: (i64, i64)) -> !
        }
        by_struct() -> i64 {
            handle perform Pick::at(Point { x: 40, y: 2 }) {
                Pick::at(Point { x, y }) => x + y,
                Pick::pair((a, b)) => a + b
            }
        }
        by_tuple() -> i64 {
            handle perform Pick::pair((40, 2)) {
                Pick::at(Point { x, y }) => x + y,
                Pick::pair((a, b)) => a + b
            }
        }
        main() -> { by_struct(); by_tuple(); () }
    "#;
    assert_eq!(
        run_function("aggregate-total-handler.glorious", source, "by_struct"),
        Value::I64(42)
    );
    assert_eq!(
        run_function("aggregate-total-handler.glorious", source, "by_tuple"),
        Value::I64(42)
    );
}

#[test]
fn enum_columns_inside_tuples_participate_in_exhaustiveness() {
    let source = r#"
        enum State { Cold, Hot }
        effect Pick { pick(value: (State, i64)) -> ! }
        selected() -> i64 {
            handle perform Pick::pick((State::Hot, 40)) {
                Pick::pick((State::Cold, n)) => n,
                Pick::pick((State::Hot, n)) => n + 2
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("tuple-enum-exhaustive.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn missing_enum_variant_inside_a_tuple_keeps_the_handler_partial() {
    let source = r#"
        enum State { Cold, Hot }
        effect Pick { pick(value: (State, i64)) -> ! }
        bad() -> i64 {
            handle perform Pick::pick((State::Hot, 40)) {
                Pick::pick((State::Cold, n)) => n
            }
        }
        main() -> { () }
    "#;
    has_message(
        "tuple-enum-partial.glorious",
        source,
        &["partial effect handler"],
    );
}

const PARITY_SURFACE: &str = r#"
    struct Point { x: i64, y: i64 }
    enum Shape { Empty, At(Point) }
    effect Pick { pick(value: (Shape, (i64, Text))) -> ! }
    selected() -> i64 {
        handle perform Pick::pick((Shape::At(Point { x: 2, y: 30 }), (10, "hit"))) {
            Pick::pick((Shape::Empty, (bonus, _))) => bonus,
            Pick::pick((Shape::At(Point { y, x }), (bonus, "miss"))) => 0 - x - y - bonus,
            Pick::pick((Shape::At(Point { y, x }), (bonus, "hit"))) => x + y + bonus,
            Pick::pick((shape, (bonus, text))) => bonus
        }
    }
"#;

#[test]
fn aggregate_handler_patterns_have_recovery_parity() {
    let recovery = format!("{PARITY_SURFACE}\n    main() -> i64 {{ selected() }}");
    let result = run_source(
        "aggregate-pattern-recovery.glorious",
        &recovery,
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(result, RecoveryValue::Int(42));

    let compiled = format!("{PARITY_SURFACE}\n    main() -> {{ selected(); () }}");
    assert_eq!(
        run_function("aggregate-pattern-compiled.glorious", &compiled, "selected"),
        Value::I64(42)
    );
}

#[test]
fn resumptive_clauses_select_by_aggregate_patterns_and_resume() {
    let source = r#"
        struct Query { key: i64, bump: i64 }
        effect Ask { [1,1] ask(query: (Query, i64)) -> i64 }
        request() -> i64 / {Ask} { perform Ask::ask((Query { key: 7, bump: 2 }, 30)) }
        selected() -> i64 {
            handle { request() } {
                Ask::ask((Query { key: 0, bump }, base)) with k => resume(k, base),
                Ask::ask((Query { bump, key }, base)) with k => resume(k, key + bump + base + 3)
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        run_function("resumptive-aggregate.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn recovery_path_accepts_implicit_struct_omission() {
    let source = r#"
        struct Point { x: i64, y: i64 }
        effect Pick { pick(point: Point) -> ! }
        main() -> i64 {
            handle perform Pick::pick(Point { x: 1, y: 2 }) {
                Pick::pick(Point { x }) => x
            }
        }
    "#;
    assert_eq!(
        run_source(
            "recovery-implicit-field.glorious",
            source,
            vec![],
            &mut NoHost
        )
        .unwrap(),
        RecoveryValue::Int(1)
    );
}

#[test]
fn recovery_path_matches_variant_middle_rest_and_implicit_tuple_suffix() {
    let source = r#"
        enum Packet { Data(i64, Text, i64), Empty }
        effect Pick { pick(value: (Packet, Text)) -> ! }
        main() -> i64 {
            handle perform Pick::pick((Packet::Data(40, "middle", 2), "suffix")) {
                Pick::pick((Packet::Data(first, .., last),)) => first + last,
                Pick::pick((Packet::Empty,)) => 0
            }
        }
    "#;
    assert_eq!(
        run_source(
            "recovery-pattern-omission.glorious",
            source,
            vec![],
            &mut NoHost
        )
        .unwrap(),
        RecoveryValue::Int(42)
    );
}

#[test]
fn aggregate_handler_patterns_agree_across_optimization_levels() {
    let compiled = format!("{PARITY_SURFACE}\n    main() -> {{ selected(); () }}");
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "aggregate-pattern-levels.glorious",
            &compiled,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let selected = artifact
            .functions
            .iter()
            .position(|function| function.name == "selected")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(artifact).unwrap())
                .run(selected, vec![])
                .unwrap(),
            Value::I64(42),
            "clause selection changed at {optimization_level:?}"
        );
    }
}
