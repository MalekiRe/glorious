use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_phases_with_options,
    diagnostic::Diagnostic,
    eval::{Host, Value as RecoveryValue},
    run_source,
    span::Span,
};
use grandiose_vm::{Value, Vm, verify};

const LEVELS: [OptimizationLevel; 3] = [
    OptimizationLevel::O1,
    OptimizationLevel::O2,
    OptimizationLevel::O3,
];

const F32_DIRECT_ROUND_UP: &str =
    "1.00000005960464477539062582718061255302767487140869206996285356581211090087890625";
const F64_DIRECT_ROUND_UP: &str = "1.000000000000000111022302462515654043115483193608295255099991383822237233803945956334136013765601092018187046051025390625";

#[derive(Default)]
struct NoHost;

impl Host for NoHost {
    fn perform(
        &mut self,
        _effect: &str,
        _operation: &str,
        _args: Vec<RecoveryValue>,
        span: Span,
    ) -> Result<RecoveryValue, Diagnostic> {
        Err(Diagnostic::error(
            "unexpected effect",
            "numeric-literal recovery must not reach the host",
            span,
        ))
    }
}

fn run(source: &str, name: &str, level: OptimizationLevel) -> Value {
    let phases = compile_source_to_phases_with_options(
        "source-numeric-literals.glorious",
        source,
        CompileOptions {
            optimization_level: level,
        },
    )
    .unwrap_or_else(|errors| panic!("{level:?}: {errors:#?}"));
    let function = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap() as u32;
    Vm::new(verify(phases.artifact).unwrap())
        .run(function, vec![])
        .unwrap()
}

#[test]
fn full_width_integer_literals_survive_contextual_selection_at_o1_through_o3() {
    let source = r#"
        u64_max() -> u64 { 18_446_744_073_709_551_615 }
        u128_max() -> u128 { 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff }
        i64_min() -> i64 { -9_223_372_036_854_775_808 }
        i128_max() -> i128 { 170141183460469231731687303715884105727 }
        i128_min() -> i128 { -170141183460469231731687303715884105728 }
        main() -> { () }
    "#;
    for level in LEVELS {
        assert_eq!(run(source, "u64_max", level), Value::U64(u64::MAX));
        assert_eq!(run(source, "u128_max", level), Value::U128(u128::MAX));
        assert_eq!(run(source, "i64_min", level), Value::I64(i64::MIN));
        assert_eq!(run(source, "i128_max", level), Value::I128(i128::MAX));
        assert_eq!(run(source, "i128_min", level), Value::I128(i128::MIN));
    }
}

#[test]
fn recovery_contextually_selects_full_width_integer_literals() {
    for (name, source, expected) in [
        (
            "u64-max",
            "main() -> u64 { 18_446_744_073_709_551_615 }",
            RecoveryValue::Integer {
                signed: false,
                bits: 64,
                raw: u128::from(u64::MAX),
            },
        ),
        (
            "u128-max",
            "main() -> u128 { 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff }",
            RecoveryValue::Integer {
                signed: false,
                bits: 128,
                raw: u128::MAX,
            },
        ),
        (
            "i64-min",
            "main() -> i64 { -9_223_372_036_854_775_808 }",
            RecoveryValue::Int(i64::MIN),
        ),
        (
            "i128-min",
            "main() -> i128 { -170141183460469231731687303715884105728 }",
            RecoveryValue::Integer {
                signed: true,
                bits: 128,
                raw: i128::MIN as u128,
            },
        ),
    ] {
        assert_eq!(
            run_source(
                &format!("recovery-{name}.glorious"),
                source,
                vec![],
                &mut NoHost,
            )
            .unwrap(),
            expected,
            "{name}"
        );
    }
}

#[test]
fn ieee_literals_round_once_at_the_contextual_width() {
    let source = format!(
        "direct_f32() -> f32 {{ {F32_DIRECT_ROUND_UP} }}\n\
         direct_f64() -> f64 {{ {F64_DIRECT_ROUND_UP} }}\n\
         main() -> {{ () }}"
    );
    assert_eq!(
        F32_DIRECT_ROUND_UP.parse::<f64>().unwrap() as f32,
        1.0,
        "the fixture must expose f64-then-f32 double rounding"
    );
    for level in LEVELS {
        let Value::F32(value) = run(&source, "direct_f32", level) else {
            panic!("expected f32")
        };
        assert_eq!(value.to_bits(), 0x3f80_0001, "{level:?}");
        let Value::F64(value) = run(&source, "direct_f64", level) else {
            panic!("expected f64")
        };
        assert_eq!(value.to_bits(), 0x3ff0_0000_0000_0001, "{level:?}");
    }

    let RecoveryValue::Float(value) = run_source(
        "recovery-direct-f64.glorious",
        &format!("main() -> f64 {{ {F64_DIRECT_ROUND_UP} }}"),
        vec![],
        &mut NoHost,
    )
    .unwrap() else {
        panic!("expected recovery f64")
    };
    assert_eq!(value.to_bits(), 0x3ff0_0000_0000_0001);
}

#[test]
fn full_width_integer_handler_patterns_use_typed_constants() {
    let source = r#"
        effect Inspect { inspect(value: u128) -> ! }
        probe(value: u128) -> i64 {
            handle perform Inspect::inspect(value) {
                Inspect::inspect(340282366920938463463374607431768211455) => 1,
                Inspect::inspect(other) => 0,
            }
        }
        hit() -> i64 { probe(340282366920938463463374607431768211455) }
        miss() -> i64 { probe(340282366920938463463374607431768211454) }
        main() -> { () }
    "#;
    for level in LEVELS {
        assert_eq!(run(source, "hit", level), Value::I64(1));
        assert_eq!(run(source, "miss", level), Value::I64(0));
    }
}

#[test]
fn contextual_range_failures_report_the_exact_literal_span() {
    for (source, literal, message) in [
        (
            "answer() -> u64 { 18446744073709551616 } main() -> { () }",
            "18446744073709551616",
            "out of range for u64",
        ),
        (
            "answer() -> i64 { 9223372036854775808 } main() -> { () }",
            "9223372036854775808",
            "out of range for i64",
        ),
        (
            "answer() -> i128 { -170141183460469231731687303715884105729 } main() -> { () }",
            "-170141183460469231731687303715884105729",
            "out of range for i128",
        ),
        (
            "answer() -> f32 { 3.5e38 } main() -> { () }",
            "3.5e38",
            "overflows f32",
        ),
        (
            "answer() -> f64 { 1e309 } main() -> { () }",
            "1e309",
            "overflows f64",
        ),
    ] {
        let errors = compile_source_to_phases_with_options(
            "range.glorious",
            source,
            CompileOptions::default(),
        )
        .unwrap_err();
        let error = errors
            .iter()
            .find(|error| error.message.contains(message))
            .unwrap_or_else(|| panic!("missing `{message}` in {errors:#?}"));
        let start = source.find(literal).unwrap();
        let span = error.span.unwrap();
        assert_eq!((span.start, span.end), (start, start + literal.len()));
    }
}

#[test]
fn values_beyond_u128_fail_at_the_token_span() {
    let literal = "340282366920938463463374607431768211456";
    let source = format!("answer() -> u128 {{ {literal} }} main() -> {{ () }}");
    let errors = compile_source_to_phases_with_options(
        "too-wide.glorious",
        &source,
        CompileOptions::default(),
    )
    .unwrap_err();
    let error = errors
        .iter()
        .find(|error| error.message.contains("does not fit in 128 bits"))
        .unwrap();
    let start = source.find(literal).unwrap();
    let span = error.span.unwrap();
    assert_eq!((span.start, span.end), (start, start + literal.len()));
}
