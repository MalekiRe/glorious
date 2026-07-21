use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_phases_with_options,
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
            "ByteReader recovery test performed a host effect",
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

fn assert_some(value: Value, expected: Value, context: &str) {
    let Value::Aggregate(option) = value else {
        panic!("{context}: reader did not return an Option")
    };
    let option = option.borrow();
    assert_eq!(option.variant, Some(0), "{context}: expected Option::Some");
    assert_eq!(option.fields, [Some(expected)], "{context}");
}

fn assert_none(value: Value, context: &str) {
    let Value::Aggregate(option) = value else {
        panic!("{context}: reader did not return an Option")
    };
    let option = option.borrow();
    assert_eq!(option.variant, Some(1), "{context}: expected Option::None");
}

const SURFACE: &str = r#"
    effect BoolCase { inspect(value: Result<(), ()>) -> !; }
    effect U8Case { inspect(value: Result<u8, ()>) -> !; }
    effect U16Case { inspect(value: Result<u16, ()>) -> !; }
    effect U32Case { inspect(value: Result<u32, ()>) -> !; }
    effect U64Case { inspect(value: Result<u64, ()>) -> !; }
    effect U128Case { inspect(value: Result<u128, ()>) -> !; }

    bool_score(value: Bool) -> usize {
        handle perform BoolCase::inspect(move value) {
            BoolCase::inspect(Result::Ok(_)) => 1,
            BoolCase::inspect(Result::Err(_)) => 0
        }
    }

    canonical_bytes() -> Bytes {
        let bytes = ByteBuf::new();
        ByteBuf::push(&mut bytes, 171);
        ByteBuf::write_u16_le(&mut bytes, 4660);
        ByteBuf::write_u32_le(&mut bytes, wrapping_convert_to_u32(-1985229329));
        ByteBuf::write_u64_le(&mut bytes, 81985529216486895);
        ByteBuf::write_u128_le(&mut bytes, wrapping_convert_to_u128(-1));
        ByteBuf::finish(move bytes)
    }

    read_u8_answer() -> Option<u8> {
        let bytes = canonical_bytes();
        let reader = ByteReader::new(&bytes);
        ByteReader::read_u8(&mut reader)
    }

    read_u16_answer() -> Option<u16> {
        let bytes = canonical_bytes();
        let reader = ByteReader::new(&bytes);
        let _prefix = ByteReader::read_u8(&mut reader);
        ByteReader::read_u16_le(&mut reader)
    }

    read_u32_answer() -> Option<u32> {
        let bytes = canonical_bytes();
        let reader = ByteReader::new(&bytes);
        let _prefix = ByteReader::read_u8(&mut reader);
        let _prefix = ByteReader::read_u16_le(&mut reader);
        ByteReader::read_u32_le(&mut reader)
    }

    read_u64_answer() -> Option<u64> {
        let bytes = canonical_bytes();
        let reader = ByteReader::new(&bytes);
        let _prefix = ByteReader::read_u8(&mut reader);
        let _prefix = ByteReader::read_u16_le(&mut reader);
        let _prefix = ByteReader::read_u32_le(&mut reader);
        ByteReader::read_u64_le(&mut reader)
    }

    read_u128_answer() -> Option<u128> {
        let bytes = canonical_bytes();
        let reader = ByteReader::new(&bytes);
        let _prefix = ByteReader::read_u8(&mut reader);
        let _prefix = ByteReader::read_u16_le(&mut reader);
        let _prefix = ByteReader::read_u32_le(&mut reader);
        let _prefix = ByteReader::read_u64_le(&mut reader);
        ByteReader::read_u128_le(&mut reader)
    }

    metadata_answer() -> usize {
        let bytes = canonical_bytes();
        let reader = ByteReader::new(&bytes);
        let initial = ByteReader::position(&reader);
        let initial_remaining = ByteReader::remaining(&reader);
        let initially_empty = bool_score(ByteReader::is_empty(&reader));
        let _a = ByteReader::read_u8(&mut reader);
        let _b = ByteReader::read_u16_le(&mut reader);
        let _c = ByteReader::read_u32_le(&mut reader);
        let _d = ByteReader::read_u64_le(&mut reader);
        let _e = ByteReader::read_u128_le(&mut reader);
        initial + initial_remaining + initially_empty
            + ByteReader::position(&reader)
            + ByteReader::remaining(&reader)
            + bool_score(ByteReader::is_empty(&reader))
    }

    zero_u16() -> Option<u16> {
        let bytes = ByteBuf::new();
        ByteBuf::write_u16_le(&mut bytes, 0);
        let bytes = ByteBuf::finish(move bytes);
        let reader = ByteReader::new(&bytes);
        ByteReader::read_u16_le(&mut reader)
    }

    max_u16() -> Option<u16> {
        let bytes = ByteBuf::new();
        ByteBuf::write_u16_le(&mut bytes, wrapping_convert_to_u16(-1));
        let bytes = ByteBuf::finish(move bytes);
        let reader = ByteReader::new(&bytes);
        ByteReader::read_u16_le(&mut reader)
    }

    zero_u32() -> Option<u32> {
        let bytes = ByteBuf::new();
        ByteBuf::write_u32_le(&mut bytes, 0);
        let bytes = ByteBuf::finish(move bytes);
        let reader = ByteReader::new(&bytes);
        ByteReader::read_u32_le(&mut reader)
    }

    max_u32() -> Option<u32> {
        let bytes = ByteBuf::new();
        ByteBuf::write_u32_le(&mut bytes, wrapping_convert_to_u32(-1));
        let bytes = ByteBuf::finish(move bytes);
        let reader = ByteReader::new(&bytes);
        ByteReader::read_u32_le(&mut reader)
    }

    zero_u64() -> Option<u64> {
        let bytes = ByteBuf::new();
        ByteBuf::write_u64_le(&mut bytes, 0);
        let bytes = ByteBuf::finish(move bytes);
        let reader = ByteReader::new(&bytes);
        ByteReader::read_u64_le(&mut reader)
    }

    max_u64() -> Option<u64> {
        let bytes = ByteBuf::new();
        ByteBuf::write_u64_le(&mut bytes, wrapping_convert_to_u64(-1));
        let bytes = ByteBuf::finish(move bytes);
        let reader = ByteReader::new(&bytes);
        ByteReader::read_u64_le(&mut reader)
    }

    zero_u128() -> Option<u128> {
        let bytes = ByteBuf::new();
        ByteBuf::write_u128_le(&mut bytes, 0);
        let bytes = ByteBuf::finish(move bytes);
        let reader = ByteReader::new(&bytes);
        ByteReader::read_u128_le(&mut reader)
    }

    max_u128() -> Option<u128> {
        let bytes = ByteBuf::new();
        ByteBuf::write_u128_le(&mut bytes, wrapping_convert_to_u128(-1));
        let bytes = ByteBuf::finish(move bytes);
        let reader = ByteReader::new(&bytes);
        ByteReader::read_u128_le(&mut reader)
    }

    one_byte() -> Bytes {
        let bytes = ByteBuf::new();
        ByteBuf::push(&mut bytes, 1);
        ByteBuf::finish(move bytes)
    }

    empty_bytes() -> Bytes {
        let bytes = ByteBuf::new();
        ByteBuf::finish(move bytes)
    }

    truncated_u8() -> Option<u8> {
        let bytes = empty_bytes();
        let reader = ByteReader::new(&bytes);
        ByteReader::read_u8(&mut reader)
    }

    truncated_u8_position() -> usize {
        let bytes = empty_bytes();
        let reader = ByteReader::new(&bytes);
        handle perform U8Case::inspect(ByteReader::read_u8(&mut reader)) {
            U8Case::inspect(Result::Ok(_)) => 999,
            U8Case::inspect(Result::Err(_)) => ByteReader::position(&reader)
        }
    }

    three_bytes() -> Bytes {
        let bytes = ByteBuf::new();
        ByteBuf::push(&mut bytes, 1);
        ByteBuf::push(&mut bytes, 2);
        ByteBuf::push(&mut bytes, 3);
        ByteBuf::finish(move bytes)
    }

    seven_bytes() -> Bytes {
        let bytes = ByteBuf::new();
        ByteBuf::write_u32_le(&mut bytes, 1);
        ByteBuf::write_u16_le(&mut bytes, 2);
        ByteBuf::push(&mut bytes, 3);
        ByteBuf::finish(move bytes)
    }

    fifteen_bytes() -> Bytes {
        let bytes = ByteBuf::new();
        ByteBuf::write_u64_le(&mut bytes, 1);
        ByteBuf::write_u32_le(&mut bytes, 2);
        ByteBuf::write_u16_le(&mut bytes, 3);
        ByteBuf::push(&mut bytes, 4);
        ByteBuf::finish(move bytes)
    }

    truncated_u16() -> Option<u16> {
        let bytes = one_byte();
        let reader = ByteReader::new(&bytes);
        ByteReader::read_u16_le(&mut reader)
    }

    truncated_u16_position() -> usize {
        let bytes = one_byte();
        let reader = ByteReader::new(&bytes);
        handle perform U16Case::inspect(ByteReader::read_u16_le(&mut reader)) {
            U16Case::inspect(Result::Ok(_)) => 999,
            U16Case::inspect(Result::Err(_)) => ByteReader::position(&reader)
        }
    }

    truncated_u32() -> Option<u32> {
        let bytes = three_bytes();
        let reader = ByteReader::new(&bytes);
        ByteReader::read_u32_le(&mut reader)
    }

    truncated_u32_position() -> usize {
        let bytes = three_bytes();
        let reader = ByteReader::new(&bytes);
        handle perform U32Case::inspect(ByteReader::read_u32_le(&mut reader)) {
            U32Case::inspect(Result::Ok(_)) => 999,
            U32Case::inspect(Result::Err(_)) => ByteReader::position(&reader)
        }
    }

    truncated_u64() -> Option<u64> {
        let bytes = seven_bytes();
        let reader = ByteReader::new(&bytes);
        ByteReader::read_u64_le(&mut reader)
    }

    truncated_u64_position() -> usize {
        let bytes = seven_bytes();
        let reader = ByteReader::new(&bytes);
        handle perform U64Case::inspect(ByteReader::read_u64_le(&mut reader)) {
            U64Case::inspect(Result::Ok(_)) => 999,
            U64Case::inspect(Result::Err(_)) => ByteReader::position(&reader)
        }
    }

    truncated_u128() -> Option<u128> {
        let bytes = fifteen_bytes();
        let reader = ByteReader::new(&bytes);
        ByteReader::read_u128_le(&mut reader)
    }

    truncated_u128_position() -> usize {
        let bytes = fifteen_bytes();
        let reader = ByteReader::new(&bytes);
        handle perform U128Case::inspect(ByteReader::read_u128_le(&mut reader)) {
            U128Case::inspect(Result::Ok(_)) => 999,
            U128Case::inspect(Result::Err(_)) => ByteReader::position(&reader)
        }
    }

    main() -> () { () }
"#;

#[test]
fn byte_reader_decodes_bytebuf_output_and_tracks_metadata_at_o0_through_o3() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "byte-reader.glorious",
            SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(phases.artifact.clone()).unwrap());
        let run = |name| {
            vm.run(function_id(&phases.artifact, name), vec![])
                .unwrap_or_else(|error| panic!("{optimization_level:?} {name}: {error:#?}"))
        };

        assert_some(run("read_u8_answer"), Value::U64(0xab), "u8");
        assert_some(run("read_u16_answer"), Value::U64(0x1234), "u16");
        assert_some(run("read_u32_answer"), Value::U64(0x89ab_cdef), "u32");
        assert_some(
            run("read_u64_answer"),
            Value::U64(0x0123_4567_89ab_cdef),
            "u64",
        );
        assert_some(run("read_u128_answer"), Value::U128(u128::MAX), "u128");
        assert_eq!(run("metadata_answer"), Value::U64(63));
    }
}

#[test]
fn byte_reader_handles_zero_and_maximum_words_at_o0_through_o3() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "byte-reader-boundaries.glorious",
            SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(phases.artifact.clone()).unwrap());
        for (suffix, zero, maximum) in [
            ("u16", Value::U64(0), Value::U64(u16::MAX.into())),
            ("u32", Value::U64(0), Value::U64(u32::MAX.into())),
            ("u64", Value::U64(0), Value::U64(u64::MAX)),
            ("u128", Value::U128(0), Value::U128(u128::MAX)),
        ] {
            let zero_name = format!("zero_{suffix}");
            let max_name = format!("max_{suffix}");
            assert_some(
                vm.run(function_id(&phases.artifact, &zero_name), vec![])
                    .unwrap(),
                zero,
                &zero_name,
            );
            assert_some(
                vm.run(function_id(&phases.artifact, &max_name), vec![])
                    .unwrap(),
                maximum,
                &max_name,
            );
        }
    }
}

#[test]
fn truncated_word_reads_return_none_without_advancing_at_o0_through_o3() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "byte-reader-truncation.glorious",
            SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(phases.artifact.clone()).unwrap());
        for width in [8, 16, 32, 64, 128] {
            let read = format!("truncated_u{width}");
            let position = format!("truncated_u{width}_position");
            assert_none(
                vm.run(function_id(&phases.artifact, &read), vec![])
                    .unwrap(),
                &read,
            );
            assert_eq!(
                vm.run(function_id(&phases.artifact, &position), vec![])
                    .unwrap(),
                Value::U64(0),
                "{position} at {optimization_level:?}",
            );
        }
    }
}

#[test]
fn byte_reader_has_recovery_parity() {
    let result = run_source(
        "byte-reader-recovery.glorious",
        r#"
            effect ReadCase { inspect(value: Result<u16, ()>) -> !; }

            main() -> u16 {
                let bytes = ByteBuf::new();
                ByteBuf::write_u16_le(&mut bytes, 4660);
                let bytes = ByteBuf::finish(move bytes);
                let reader = ByteReader::new(&bytes);
                handle perform ReadCase::inspect(ByteReader::read_u16_le(&mut reader)) {
                    ReadCase::inspect(Result::Ok(value)) => move value,
                    ReadCase::inspect(Result::Err(_)) => 0
                }
            }
        "#,
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(result, RecoveryValue::Int(0x1234));
}

#[test]
fn byte_reader_representation_remains_private() {
    for (name, source) in [
        (
            "project-byte-reader.glorious",
            "bad(value: ByteReader) -> usize { value.cursor } main() -> () { () }",
        ),
        (
            "forge-byte-reader.glorious",
            "bad(bytes: Bytes) -> ByteReader { ByteReader { bytes: move bytes, cursor: 0 } } main() -> () { () }",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source)
            .expect_err("user code accessed ByteReader's private representation");
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("private field")),
            "{name}: unexpected diagnostics: {errors:#?}",
        );
    }
}
