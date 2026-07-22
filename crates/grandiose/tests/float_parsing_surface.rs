use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_phases_with_options,
    diagnostic::Diagnostic,
    eval::{Host, Value as RecoveryValue},
    run_source,
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
    ) -> Result<RecoveryValue, Diagnostic> {
        Err(Diagnostic::error(
            "unexpected effect",
            "float parsing must not perform a host effect",
            span,
        ))
    }
}

const SOURCE: &str = r#"
effect F32ParseCase { inspect(value: Result<f32, FloatParseError>) -> !; }
effect F64ParseCase { inspect(value: Result<f64, FloatParseError>) -> !; }
effect FloatErrorCase { inspect(value: FloatParseError) -> !; }

f32_bits(text: String) -> u32 {
    handle perform F32ParseCase::inspect(parse_f32(&text)) {
        F32ParseCase::inspect(Result::Ok(value)) => f32_to_bits(move value),
        F32ParseCase::inspect(Result::Err(_)) => 4294967295
    }
}

f64_bits(text: String) -> u64 {
    handle perform F64ParseCase::inspect(parse_f64(&text)) {
        F64ParseCase::inspect(Result::Ok(value)) => f64_to_bits(move value),
        F64ParseCase::inspect(Result::Err(_)) => 18446744073709551615
    }
}

error_code(text: String) -> usize {
    handle perform F64ParseCase::inspect(parse_f64(&text)) {
        F64ParseCase::inspect(Result::Ok(_)) => 0,
        F64ParseCase::inspect(Result::Err(error)) =>
            handle perform FloatErrorCase::inspect(move error) {
                FloatErrorCase::inspect(FloatParseError::Empty) => 1000,
                FloatErrorCase::inspect(FloatParseError::MissingDigits(at)) =>
                    2000 + move at,
                FloatErrorCase::inspect(FloatParseError::InvalidDigit(at)) =>
                    3000 + move at,
                FloatErrorCase::inspect(FloatParseError::MisplacedSeparator(at)) =>
                    4000 + move at,
                FloatErrorCase::inspect(FloatParseError::Overflow(at)) =>
                    5000 + move at
            }
    }
}

error_code32(text: String) -> usize {
    handle perform F32ParseCase::inspect(parse_f32(&text)) {
        F32ParseCase::inspect(Result::Ok(_)) => 0,
        F32ParseCase::inspect(Result::Err(error)) =>
            handle perform FloatErrorCase::inspect(move error) {
                FloatErrorCase::inspect(FloatParseError::Empty) => 1000,
                FloatErrorCase::inspect(FloatParseError::MissingDigits(at)) =>
                    2000 + move at,
                FloatErrorCase::inspect(FloatParseError::InvalidDigit(at)) =>
                    3000 + move at,
                FloatErrorCase::inspect(FloatParseError::MisplacedSeparator(at)) =>
                    4000 + move at,
                FloatErrorCase::inspect(FloatParseError::Overflow(at)) =>
                    5000 + move at
            }
    }
}

zero32() -> u32 { f32_bits("0.0") }
negative_zero32() -> u32 { f32_bits("-0.0") }
ordinary32() -> u32 { f32_bits("1_2.5_0e-1") }
ordinary32_error() -> usize { error_code32("1_2.5_0e-1") }
separator_runs32() -> u32 { f32_bits("+1__0.0e__1") }
tie_even32() -> u32 { f32_bits("1.000000059604644775390625") }
tie_odd32() -> u32 { f32_bits("1.000000178813934326171875") }
minimum_subnormal32() -> u32 { f32_bits("1.401298464324817070923729583289916131280261941876515771757068283e-45") }
half_minimum_subnormal32() -> u32 { f32_bits("7.00649232162408535461864791644958065640130970938257885878534141944895541342930300743319094181060791015625e-46") }
above_half_minimum_subnormal32() -> u32 { f32_bits("7.00649232162408535461864791644958065640130970938257885878534141944895541342930300743319094181060791015626e-46") }
underflow32() -> u32 { f32_bits("1e-1000") }
overflow32() -> usize { error_code32("1e39") }

zero64() -> u64 { f64_bits("0.0") }
negative_zero64() -> u64 { f64_bits("-0.0") }
ordinary64() -> u64 { f64_bits("1_2.5_0e-1") }
tie_even64() -> u64 { f64_bits("1.00000000000000011102230246251565404236316680908203125") }
tie_odd64() -> u64 { f64_bits("1.00000000000000033306690738754696212708950042724609375") }
minimum_subnormal64() -> u64 { f64_bits("4.940656458412465441765687928682213723650598026143247644255856825006755072702087518652998363616359923797965647954571945773019248323615561473969987155101656458983759941599437099399598896040767960960969549422791390572631015269991639424564525486717758544026945415325048104675849673187902831473283149818815622137208128978044965497153709888025802945563647587710225938285623489250940993115378766250419352053623220669851221926496841669998283701643393219343789046271762817786855867099095607496282912427570600199120296155099994703868237636409925051091158763823463441622232013570815775301841627124422605414826238791771729166026161449438899868134274051706596635206968046798576781355271951721053766740539111504216891497396597142351e-324") }
minimum_subnormal64_short() -> u64 { f64_bits("5e-324") }
underflow64() -> u64 { f64_bits("1e-4000") }
overflow64() -> usize { error_code("1e400") }

empty_error() -> usize { error_code("") }
missing_integer_error() -> usize { error_code("-e1") }
trailing_separator_error() -> usize { error_code("1_") }
fraction_separator_error() -> usize { error_code("1.0_") }
exponent_error() -> usize { error_code("1e+") }
invalid_error() -> usize { error_code("1.0x") }

main() -> () { () }
"#;

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing function `{name}`")) as u32
}

#[test]
fn exact_decimal_parsing_executes_at_o1_through_o3() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        eprintln!("compiling exact float parser at {optimization_level:?}");
        let phases = compile_source_to_phases_with_options(
            "float-parsing-surface.glorious",
            SOURCE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let verified = verify(phases.artifact.clone()).unwrap();
        let vm = Vm::new(verified);
        let run = |name: &str| {
            vm.run(function_id(&phases.artifact, name), vec![])
                .unwrap_or_else(|error| panic!("{optimization_level:?} {name}: {error:#?}"))
        };

        assert_eq!(
            run("ordinary32_error"),
            Value::U64(0),
            "{optimization_level:?} ordinary32 parse error"
        );

        for (name, expected) in [
            ("zero32", 0_u64),
            ("negative_zero32", 0x8000_0000),
            ("ordinary32", u64::from(1.25_f32.to_bits())),
            ("separator_runs32", u64::from(100.0_f32.to_bits())),
            ("tie_even32", 0x3f80_0000),
            ("tie_odd32", 0x3f80_0002),
            ("minimum_subnormal32", 1),
            ("half_minimum_subnormal32", 0),
            ("above_half_minimum_subnormal32", 1),
            ("underflow32", 0),
        ] {
            assert_eq!(
                run(name),
                Value::U64(expected),
                "{optimization_level:?} {name}"
            );
        }
        for (name, expected) in [
            ("zero64", 0_u64),
            ("negative_zero64", 0x8000_0000_0000_0000),
            ("ordinary64", 1.25_f64.to_bits()),
            ("tie_even64", 0x3ff0_0000_0000_0000),
            ("tie_odd64", 0x3ff0_0000_0000_0002),
            ("minimum_subnormal64_short", 1),
            ("underflow64", 0),
        ] {
            assert_eq!(
                run(name),
                Value::U64(expected),
                "{optimization_level:?} {name}"
            );
        }
        for (name, expected) in [
            ("overflow32", 5003),
            ("overflow64", 5004),
            ("empty_error", 1000),
            ("missing_integer_error", 2001),
            ("trailing_separator_error", 4001),
            ("fraction_separator_error", 4003),
            ("exponent_error", 2003),
            ("invalid_error", 3003),
        ] {
            assert_eq!(
                run(name),
                Value::U64(expected),
                "{optimization_level:?} {name}"
            );
        }
        eprintln!("exact float parser passed at {optimization_level:?}");
    }
}

#[test]
fn exact_decimal_parsing_has_recovery_parity() {
    let source = SOURCE.replace("main() -> () { () }", "main() -> u64 { ordinary64() }");
    assert_eq!(
        run_source(
            "float-parsing-recovery.glorious",
            &source,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::Integer {
            signed: false,
            bits: 64,
            raw: 1.25_f64.to_bits().into(),
        },
    );
}
