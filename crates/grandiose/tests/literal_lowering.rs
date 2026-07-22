//! End-to-end lowering coverage for float, character, byte, and byte-string
//! literals: expression contexts, expected-type selection, handler-clause
//! literal patterns, escapes, boundary values, and O0–O3 agreement.

use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_phases_with_options};
use grandiose_vm::{Value, Vm, verify};

const LEVELS: [OptimizationLevel; 4] = [
    OptimizationLevel::O0,
    OptimizationLevel::O1,
    OptimizationLevel::O2,
    OptimizationLevel::O3,
];

fn run_at(source_name: &str, source: &str, name: &str, level: OptimizationLevel) -> Value {
    let phases = compile_source_to_phases_with_options(
        source_name,
        source,
        CompileOptions {
            optimization_level: level,
        },
    )
    .unwrap_or_else(|errors| panic!("{source_name} failed to compile at {level:?}: {errors:#?}"));
    let function = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32;
    Vm::new(verify(phases.artifact).unwrap_or_else(|error| {
        panic!("{source_name} failed the verifier at {level:?}: {error:?}")
    }))
    .run(function, vec![])
    .unwrap_or_else(|error| panic!("{source_name} failed to run at {level:?}: {error}"))
}

/// Runs `name` at every optimization level, requires all levels to agree, and
/// returns the shared result.
fn run_all(source_name: &str, source: &str, name: &str) -> Value {
    let mut results = LEVELS
        .iter()
        .map(|level| (*level, run_at(source_name, source, name, *level)));
    let (_, baseline) = results.next().expect("at least one level");
    for (level, result) in results {
        assert_eq!(
            result, baseline,
            "{source_name}: {level:?} diverged from O0"
        );
    }
    baseline
}

fn compile_errors(source_name: &str, source: &str) -> Vec<String> {
    compile_source_to_phases_with_options(source_name, source, CompileOptions::default())
        .err()
        .unwrap_or_else(|| panic!("{source_name} compiled but must be rejected"))
        .into_iter()
        .map(|error| error.message)
        .collect()
}

#[test]
fn float_literal_defaults_to_f64() {
    let source = r#"
        answer() -> f64 { 4.5 }
        main() -> { () }
    "#;
    assert_eq!(
        run_all("float-default.glorious", source, "answer"),
        Value::F64(4.5)
    );
}

#[test]
fn float_literal_respects_an_expected_f32() {
    let source = r#"
        answer() -> f32 { 1.5 }
        main() -> { () }
    "#;
    assert_eq!(
        run_all("float-f32.glorious", source, "answer"),
        Value::F32(1.5)
    );
}

#[test]
fn float_literal_flows_through_an_f32_parameter() {
    let source = r#"
        keep(value: f32) -> f32 { value }
        answer() -> f32 { keep(2.25) }
        main() -> { () }
    "#;
    assert_eq!(
        run_all("float-param.glorious", source, "answer"),
        Value::F32(2.25)
    );
}

#[test]
fn negative_float_literals_fold_at_both_widths() {
    let source = r#"
        wide() -> f64 { -2.25 }
        narrow() -> f32 { -0.5 }
        main() -> { () }
    "#;
    assert_eq!(
        run_all("float-negate.glorious", source, "wide"),
        Value::F64(-2.25)
    );
    assert_eq!(
        run_all("float-negate.glorious", source, "narrow"),
        Value::F32(-0.5)
    );
}

#[test]
fn float_boundary_values_survive_lowering() {
    let source = r#"
        huge() -> f64 { 1.7976931348623157e308 }
        tiny() -> f64 { 5e-324 }
        zero() -> f64 { 0.0 }
        main() -> { () }
    "#;
    assert_eq!(
        run_all("float-bounds.glorious", source, "huge"),
        Value::F64(f64::MAX)
    );
    assert_eq!(
        run_all("float-bounds.glorious", source, "tiny"),
        Value::F64(5e-324)
    );
    assert_eq!(
        run_all("float-bounds.glorious", source, "zero"),
        Value::F64(0.0)
    );
}

#[test]
fn char_literals_lower_to_their_scalar_values() {
    let source = r#"
        ascii() -> Char { 'A' }
        escaped() -> Char { '\n' }
        unicode() -> Char { '\u{1F600}' }
        ceiling() -> Char { '\u{10FFFF}' }
        main() -> { () }
    "#;
    assert_eq!(
        run_all("char-literals.glorious", source, "ascii"),
        Value::U64(u64::from(u32::from('A')))
    );
    assert_eq!(
        run_all("char-literals.glorious", source, "escaped"),
        Value::U64(10)
    );
    assert_eq!(
        run_all("char-literals.glorious", source, "unicode"),
        Value::U64(0x1F600)
    );
    assert_eq!(
        run_all("char-literals.glorious", source, "ceiling"),
        Value::U64(0x10FFFF)
    );
}

#[test]
fn byte_literals_have_u8_and_cover_the_full_range() {
    let source = r#"
        letter() -> u8 { b'A' }
        floor() -> u8 { b'\x00' }
        ceiling() -> u8 { b'\xff' }
        escaped() -> u8 { b'\n' }
        main() -> { () }
    "#;
    assert_eq!(
        run_all("byte-literals.glorious", source, "letter"),
        Value::U64(65)
    );
    assert_eq!(
        run_all("byte-literals.glorious", source, "floor"),
        Value::U64(0)
    );
    assert_eq!(
        run_all("byte-literals.glorious", source, "ceiling"),
        Value::U64(255)
    );
    assert_eq!(
        run_all("byte-literals.glorious", source, "escaped"),
        Value::U64(10)
    );
}

#[test]
fn byte_string_literals_preserve_their_exact_contents() {
    let source = r#"
        payload() -> Bytes { b"ab\x00\xff\n" }
        empty() -> Bytes { b"" }
        main() -> { () }
    "#;
    let Value::Bytes(bytes) = run_all("byte-strings.glorious", source, "payload") else {
        panic!("byte-string literal must produce a Bytes value");
    };
    assert_eq!(bytes.as_ref(), [b'a', b'b', 0x00, 0xff, b'\n']);
    let Value::Bytes(empty) = run_all("byte-strings.glorious", source, "empty") else {
        panic!("empty byte-string literal must produce a Bytes value");
    };
    assert!(empty.is_empty());
}

#[test]
fn float_handler_patterns_select_the_matching_clause() {
    let source = r#"
        effect Inspect { inspect(value: f64) -> ! }
        probe(value: f64) -> i64 {
            handle perform Inspect::inspect(value) {
                Inspect::inspect(4.5) => 1,
                Inspect::inspect(other) => 0,
            }
        }
        hit() -> i64 { probe(4.5) }
        miss() -> i64 { probe(2.0) }
        main() -> { () }
    "#;
    assert_eq!(
        run_all("float-pattern.glorious", source, "hit"),
        Value::I64(1)
    );
    assert_eq!(
        run_all("float-pattern.glorious", source, "miss"),
        Value::I64(0)
    );
}

#[test]
fn char_handler_patterns_select_the_matching_clause() {
    let source = r#"
        effect Inspect { inspect(value: Char) -> ! }
        probe(value: Char) -> i64 {
            handle perform Inspect::inspect(value) {
                Inspect::inspect('\u{1F600}') => 1,
                Inspect::inspect(other) => 0,
            }
        }
        hit() -> i64 { probe('\u{1F600}') }
        miss() -> i64 { probe('x') }
        main() -> { () }
    "#;
    assert_eq!(
        run_all("char-pattern.glorious", source, "hit"),
        Value::I64(1)
    );
    assert_eq!(
        run_all("char-pattern.glorious", source, "miss"),
        Value::I64(0)
    );
}

#[test]
fn byte_handler_patterns_select_the_matching_clause() {
    let source = r#"
        effect Inspect { inspect(value: u8) -> ! }
        probe(value: u8) -> i64 {
            handle perform Inspect::inspect(value) {
                Inspect::inspect(b'\xff') => 1,
                Inspect::inspect(other) => 0,
            }
        }
        hit() -> i64 { probe(b'\xff') }
        miss() -> i64 { probe(b'\x00') }
        main() -> { () }
    "#;
    assert_eq!(
        run_all("byte-pattern.glorious", source, "hit"),
        Value::I64(1)
    );
    assert_eq!(
        run_all("byte-pattern.glorious", source, "miss"),
        Value::I64(0)
    );
}

#[test]
fn literal_patterns_fall_through_ordered_clauses() {
    let source = r#"
        effect Inspect { inspect(value: f64) -> ! }
        probe(value: f64) -> i64 {
            handle perform Inspect::inspect(value) {
                Inspect::inspect(1.0) => 1,
                Inspect::inspect(2.0) => 2,
                Inspect::inspect(other) => 3,
            }
        }
        first() -> i64 { probe(1.0) }
        second() -> i64 { probe(2.0) }
        third() -> i64 { probe(9.5) }
        main() -> { () }
    "#;
    assert_eq!(
        run_all("float-clauses.glorious", source, "first"),
        Value::I64(1)
    );
    assert_eq!(
        run_all("float-clauses.glorious", source, "second"),
        Value::I64(2)
    );
    assert_eq!(
        run_all("float-clauses.glorious", source, "third"),
        Value::I64(3)
    );
}

#[test]
fn float_literal_rejects_a_non_float_context() {
    let errors = compile_errors(
        "float-in-int.glorious",
        r#"
            answer() -> i64 { 1.5 }
            main() -> { () }
        "#,
    );
    assert!(
        errors
            .iter()
            .any(|message| message.contains("float literal requires a floating-point context")),
        "{errors:#?}"
    );
}

#[test]
fn char_and_byte_literals_reject_mismatched_contexts() {
    assert!(
        !compile_errors(
            "char-in-int.glorious",
            r#"
            answer() -> i64 { 'a' }
            main() -> { () }
        "#,
        )
        .is_empty()
    );
    assert!(
        !compile_errors(
            "byte-in-char.glorious",
            r#"
            answer() -> Char { b'a' }
            main() -> { () }
        "#,
        )
        .is_empty()
    );
    assert!(
        !compile_errors(
            "bytestring-in-text.glorious",
            r#"
            answer() -> Text { b"raw" }
            main() -> { () }
        "#,
        )
        .is_empty()
    );
    assert!(
        !compile_errors(
            "int-in-float.glorious",
            r#"
            answer() -> f64 { 3 }
            main() -> { () }
        "#,
        )
        .is_empty()
    );
}

#[test]
fn float_pattern_rejects_a_non_float_payload() {
    let errors = compile_errors(
        "float-pattern-on-int.glorious",
        r#"
            effect Inspect { inspect(value: i64) -> ! }
            probe() -> i64 {
                handle perform Inspect::inspect(1) {
                    Inspect::inspect(4.5) => 1,
                    Inspect::inspect(other) => 0,
                }
            }
            main() -> { () }
        "#,
    );
    assert!(
        errors
            .iter()
            .any(|message| message.contains("float handler pattern")),
        "{errors:#?}"
    );
}

/// The recovery evaluator accepts the same literal forms; its untyped values
/// must agree observably with the bytecode results.
mod recovery {
    use grandiose::{
        diagnostic::Diagnostic,
        eval::{Host, Value},
        run_source,
        span::Span,
    };

    struct NoHost;

    impl Host for NoHost {
        fn perform(
            &mut self,
            effect: &str,
            operation: &str,
            _args: Vec<Value>,
            span: Span,
        ) -> Result<Value, Diagnostic> {
            Err(Diagnostic::error(
                "unexpected host effect",
                format!("literal programs perform no host effects, got {effect}::{operation}"),
                span,
            ))
        }
    }

    fn run(source_name: &str, source: &str) -> Value {
        run_source(source_name, source, vec![], &mut NoHost)
            .unwrap_or_else(|errors| panic!("{source_name} failed in recovery: {errors:#?}"))
    }

    #[test]
    fn literal_expressions_evaluate() {
        assert_eq!(
            run("recovery-float.glorious", "main() -> f64 { 4.5 }"),
            Value::Float(4.5)
        );
        assert_eq!(
            run("recovery-char.glorious", "main() -> Char { '\\u{1F600}' }"),
            Value::Char('\u{1F600}')
        );
        assert_eq!(
            run("recovery-byte.glorious", "main() -> u8 { b'\\xff' }"),
            Value::Integer {
                signed: false,
                bits: 8,
                raw: 255,
            }
        );
        let Value::Bytes(bytes) = run(
            "recovery-bytes.glorious",
            r#"main() -> Bytes { b"ab\x00" }"#,
        ) else {
            panic!("byte-string literal must produce Bytes in recovery");
        };
        assert_eq!(bytes.as_ref(), [b'a', b'b', 0x00]);
    }

    #[test]
    fn literal_handler_patterns_match() {
        let source = r#"
            effect Inspect { inspect(value: f64) -> ! }
            probe(value: f64) -> i64 {
                handle perform Inspect::inspect(value) {
                    Inspect::inspect(4.5) => 1,
                    Inspect::inspect(other) => 0,
                }
            }
            main() -> i64 { probe(4.5) * 10 + probe(2.0) }
        "#;
        assert_eq!(
            run("recovery-float-pattern.glorious", source),
            Value::Int(10)
        );
        let chars = r#"
            effect Inspect { inspect(value: Char) -> ! }
            probe(value: Char) -> i64 {
                handle perform Inspect::inspect(value) {
                    Inspect::inspect('x') => 1,
                    Inspect::inspect(other) => 0,
                }
            }
            main() -> i64 { probe('x') * 10 + probe('y') }
        "#;
        assert_eq!(run("recovery-char-pattern.glorious", chars), Value::Int(10));
        let bytes = r#"
            effect Inspect { inspect(value: u8) -> ! }
            probe(value: u8) -> i64 {
                handle perform Inspect::inspect(value) {
                    Inspect::inspect(b'\x00') => 1,
                    Inspect::inspect(other) => 0,
                }
            }
            main() -> i64 { probe(b'\x00') * 10 + probe(b'\x01') }
        "#;
        assert_eq!(run("recovery-byte-pattern.glorious", bytes), Value::Int(10));
    }
}
