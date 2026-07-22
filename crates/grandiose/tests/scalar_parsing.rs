use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_phases_with_options,
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
    ) -> Result<RecoveryValue, grandiose::diagnostic::Diagnostic> {
        Err(grandiose::diagnostic::Diagnostic::error(
            "unexpected effect",
            "scalar parsing must not perform host effects",
            span,
        ))
    }
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

const PARSING_SURFACE: &str = r#"
    effect U64ParseCase { inspect(value: Result<u64, IntParseError>) -> !; }
    effect I64ParseCase { inspect(value: Result<i64, IntParseError>) -> !; }

    unwrap_u64(value: Result<u64, IntParseError>) -> u64 {
        handle perform U64ParseCase::inspect(move value) {
            U64ParseCase::inspect(Result::Ok(parsed)) => move parsed,
            U64ParseCase::inspect(Result::Err(_)) => 0
        }
    }

    unwrap_i64(value: Result<i64, IntParseError>) -> i64 {
        handle perform I64ParseCase::inspect(move value) {
            I64ParseCase::inspect(Result::Ok(parsed)) => move parsed,
            I64ParseCase::inspect(Result::Err(_)) => 0
        }
    }

    error_score(value: Result<u64, IntParseError>) -> u64 {
        handle perform U64ParseCase::inspect(move value) {
            U64ParseCase::inspect(Result::Ok(_)) => 0,
            U64ParseCase::inspect(Result::Err(IntParseError::Empty)) => 1,
            U64ParseCase::inspect(Result::Err(IntParseError::InvalidBase)) => 2,
            U64ParseCase::inspect(Result::Err(IntParseError::InvalidDigit(at))) =>
                wrapping_convert_to_u64(at) + 100,
            U64ParseCase::inspect(Result::Err(IntParseError::Overflow(at))) =>
                wrapping_convert_to_u64(at) + 200
        }
    }

    i64_error_score(value: Result<i64, IntParseError>) -> u64 {
        handle perform I64ParseCase::inspect(move value) {
            I64ParseCase::inspect(Result::Ok(_)) => 0,
            I64ParseCase::inspect(Result::Err(IntParseError::Empty)) => 1,
            I64ParseCase::inspect(Result::Err(IntParseError::InvalidBase)) => 2,
            I64ParseCase::inspect(Result::Err(IntParseError::InvalidDigit(at))) =>
                wrapping_convert_to_u64(at) + 100,
            I64ParseCase::inspect(Result::Err(IntParseError::Overflow(at))) =>
                wrapping_convert_to_u64(at) + 200
        }
    }

    source_u64(value: String) -> Result<u64, IntParseError> {
        parse_u64(&value)
    }
    radix_u64(value: String, base: u32) -> Result<u64, IntParseError> {
        parse_u64_radix(&value, move base)
    }
    source_i64(value: String) -> Result<i64, IntParseError> {
        parse_i64(&value)
    }

    binary() -> u64 { unwrap_u64(source_u64("0b1010_1111")) }
    octal() -> u64 { unwrap_u64(source_u64("0o7_55")) }
    decimal_max() -> u64 {
        unwrap_u64(source_u64("18446744073709551615"))
    }
    hexadecimal() -> u64 { unwrap_u64(source_u64("0x__Dead_Beef")) }
    radix_36() -> u64 { unwrap_u64(radix_u64("z", 36)) }
    signed_min() -> i64 {
        unwrap_i64(source_i64("-0x8000000000000000"))
    }
    invalid_digit() -> u64 { error_score(source_u64("0b102")) }
    overflow() -> u64 { error_score(source_u64("18446744073709551616")) }
    trailing_separator() -> u64 { error_score(source_u64("12_")) }
    invalid_base() -> u64 { error_score(radix_u64("1", 1)) }
    empty() -> u64 { error_score(source_u64("")) }
    prefix_without_digit() -> u64 { error_score(source_u64("0x")) }
    prefix_separator_only() -> u64 { error_score(source_u64("0x___")) }
    leading_separator() -> u64 { error_score(source_u64("_1")) }
    radix_invalid_digit() -> u64 { error_score(radix_u64("2", 2)) }
    signed_positive_overflow() -> u64 {
        i64_error_score(source_i64("9223372036854775808"))
    }
    signed_negative_overflow() -> u64 {
        i64_error_score(source_i64("-9223372036854775809"))
    }
    sign_without_digit() -> u64 { i64_error_score(source_i64("-")) }
    main() -> () { () }
"#;

const CHAR_SURFACE: &str = r#"
    char_from_scalar(value: u32) -> u32 {
        let converted = char_from_u32(move value);
        if(converted is Result::Ok(_)) {
            char_to_u32(converted.0)
        } else {
            0
        }
    }

    decoded_scalar(value: char) -> u32 {
        let bytes = char_encode_utf8(move value);
        let decoded = char_decode_utf8(&bytes, 0);
        if(decoded is Result::Ok(_)) {
            let decoded_value = decoded.0;
            let DecodedChar { value: character, next: _ } = move decoded_value;
            char_to_u32(move character)
        } else {
            0
        }
    }

    bytes2(first: u8, second: u8) -> Bytes {
        let bytes = __g1_char_byte_vec();
        Vec::push(&mut bytes, move first);
        Vec::push(&mut bytes, move second);
        Bytes::from_vec(move bytes)
    }

    bytes3(first: u8, second: u8, third: u8) -> Bytes {
        let bytes = __g1_char_byte_vec();
        Vec::push(&mut bytes, move first);
        Vec::push(&mut bytes, move second);
        Vec::push(&mut bytes, move third);
        Bytes::from_vec(move bytes)
    }

    decode_error(value: Bytes, index: usize) -> usize {
        let decoded = char_decode_utf8(&value, move index);
        if(decoded is Result::Err(_)) {
            decoded.0.valid_up_to
        } else {
            999
        }
    }

    ascii_scalar() -> u32 { char_from_scalar(65) }
    invalid_scalar() -> u32 { char_from_scalar(55296) }
    utf8_two() -> u32 { decoded_scalar('¢') }
    utf8_three() -> u32 { decoded_scalar('€') }
    utf8_four() -> u32 { decoded_scalar('😀') }
    overlong_utf8() -> usize { decode_error(bytes2(192, 128), 0) }
    surrogate_utf8() -> usize { decode_error(bytes3(237, 160, 128), 0) }
    truncated_utf8() -> usize { decode_error(bytes3(240, 159, 152), 0) }
    decode_out_of_bounds() -> usize { decode_error(bytes2(65, 66), 2) }
    main() -> () { () }
"#;

#[test]
fn integer_source_bases_ranges_and_errors_execute_at_o1_through_o3() {
    let expected = [
        ("binary", Value::U64(175)),
        ("octal", Value::U64(493)),
        ("decimal_max", Value::U64(u64::MAX)),
        ("hexadecimal", Value::U64(0xDEAD_BEEF)),
        ("radix_36", Value::U64(35)),
        ("signed_min", Value::I64(i64::MIN)),
        ("invalid_digit", Value::U64(104)),
        ("overflow", Value::U64(219)),
        ("trailing_separator", Value::U64(102)),
        ("invalid_base", Value::U64(2)),
        ("empty", Value::U64(1)),
        ("prefix_without_digit", Value::U64(1)),
        ("prefix_separator_only", Value::U64(1)),
        ("leading_separator", Value::U64(100)),
        ("radix_invalid_digit", Value::U64(100)),
        ("signed_positive_overflow", Value::U64(218)),
        ("signed_negative_overflow", Value::U64(219)),
        ("sign_without_digit", Value::U64(1)),
    ];

    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "scalar-parsing.glorious",
            PARSING_SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let artifact = verify(phases.artifact.clone()).unwrap();
        for (name, expected) in &expected {
            assert_eq!(
                Vm::new(artifact.clone())
                    .run(function_id(&phases.artifact, name), vec![])
                    .unwrap(),
                *expected,
                "{optimization_level:?} {name}"
            );
        }
    }
}

#[test]
fn character_scalars_and_utf8_codec_execute_at_o1_through_o3() {
    let expected = [
        ("ascii_scalar", Value::U64(65)),
        ("invalid_scalar", Value::U64(0)),
        ("utf8_two", Value::U64(0xA2)),
        ("utf8_three", Value::U64(0x20AC)),
        ("utf8_four", Value::U64(0x1F600)),
        ("overlong_utf8", Value::U64(0)),
        ("surrogate_utf8", Value::U64(0)),
        ("truncated_utf8", Value::U64(0)),
        ("decode_out_of_bounds", Value::U64(2)),
    ];

    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "character-codec.glorious",
            CHAR_SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let artifact = verify(phases.artifact.clone()).unwrap();
        for (name, expected) in &expected {
            assert_eq!(
                Vm::new(artifact.clone())
                    .run(function_id(&phases.artifact, name), vec![])
                    .unwrap(),
                *expected,
                "{optimization_level:?} {name}"
            );
        }
    }
}

#[test]
fn integer_parsing_has_recovery_parity() {
    let source = PARSING_SURFACE.replace(
        "main() -> () { () }",
        "main() -> i64 { wrapping_convert_to_i64(hexadecimal()) }",
    );
    assert_eq!(
        run_source(
            "scalar-parsing-recovery.glorious",
            &source,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::Int(0xDEAD_BEEF)
    );
}

#[test]
fn character_codec_has_recovery_parity() {
    let source = CHAR_SURFACE.replace(
        "main() -> () { () }",
        "main() -> i64 { wrapping_convert_to_i64(utf8_three()) }",
    );
    assert_eq!(
        run_source(
            "character-codec-recovery.glorious",
            &source,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::Int(0x20AC)
    );
}
