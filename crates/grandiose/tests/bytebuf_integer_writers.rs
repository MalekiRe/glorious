use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options,
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
            "ByteBuf integer-writer recovery test performed a host effect",
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

const SURFACE: &str = r#"
    write_canonical(prefix: Bytes) -> Bytes {
        let bytes = ByteBuf::new();
        ByteBuf::append_bytes(&mut bytes, &prefix);
        ByteBuf::push(&mut bytes, 238);
        ByteBuf::write_u16_le(&mut bytes, 4660);
        ByteBuf::write_u32_le(&mut bytes, wrapping_convert_to_u32(-1985229329));
        ByteBuf::write_u64_le(&mut bytes, 81985529216486895);
        ByteBuf::write_u128_le(&mut bytes, wrapping_convert_to_u128(305419896));
        ByteBuf::finish(move bytes)
    }

    write_boundaries() -> Bytes {
        let bytes = ByteBuf::new();
        ByteBuf::write_u16_le(&mut bytes, 0);
        ByteBuf::write_u16_le(&mut bytes, wrapping_convert_to_u16(-1));
        ByteBuf::write_u32_le(&mut bytes, 0);
        ByteBuf::write_u32_le(&mut bytes, wrapping_convert_to_u32(-1));
        ByteBuf::write_u64_le(&mut bytes, 0);
        ByteBuf::write_u64_le(&mut bytes, wrapping_convert_to_u64(-1));
        ByteBuf::write_u128_le(&mut bytes, 0);
        ByteBuf::write_u128_le(&mut bytes, wrapping_convert_to_u128(-1));
        ByteBuf::finish(move bytes)
    }

    main() -> () { () }
"#;

#[test]
fn bytebuf_integer_writers_append_canonical_little_endian_bytes_at_o0_through_o3() {
    let mut canonical = vec![9_u8, 8, 238, 0x34, 0x12, 0xef, 0xcd, 0xab, 0x89];
    canonical.extend_from_slice(&[0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01]);
    canonical.extend_from_slice(&[0x78, 0x56, 0x34, 0x12]);
    canonical.extend_from_slice(&[0; 12]);

    let mut boundaries = Vec::new();
    boundaries.extend_from_slice(&[0, 0, 0xff, 0xff]);
    boundaries.extend_from_slice(&[0; 4]);
    boundaries.extend_from_slice(&[0xff; 4]);
    boundaries.extend_from_slice(&[0; 8]);
    boundaries.extend_from_slice(&[0xff; 8]);
    boundaries.extend_from_slice(&[0; 16]);
    boundaries.extend_from_slice(&[0xff; 16]);

    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "bytebuf-integer-writers.glorious",
            SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(artifact.clone()).unwrap());

        assert_eq!(
            vm.run(
                function_id(&artifact, "write_canonical"),
                vec![Value::Bytes(vec![9_u8, 8].into())],
            )
            .unwrap(),
            Value::Bytes(canonical.clone().into()),
            "canonical sequence at {optimization_level:?}",
        );
        assert_eq!(
            vm.run(function_id(&artifact, "write_boundaries"), vec![])
                .unwrap(),
            Value::Bytes(boundaries.clone().into()),
            "boundary sequence at {optimization_level:?}",
        );
    }
}

#[test]
fn bytebuf_integer_writers_have_recovery_parity_and_bytes_get_observability() {
    let result = run_source(
        "bytebuf-integer-writers-recovery.glorious",
        r#"
            effect ByteCase { inspect(value: Result<u8, BytesIndexError>) -> !; }

            main() -> u8 {
                let bytes = ByteBuf::new();
                ByteBuf::push(&mut bytes, 7);
                ByteBuf::write_u16_le(&mut bytes, 4660);
                let bytes = ByteBuf::finish(move bytes);
                handle perform ByteCase::inspect(Bytes::get(&bytes, 1)) {
                    ByteCase::inspect(Result::Ok(byte)) => move byte,
                    ByteCase::inspect(Result::Err(_)) => 0
                }
            }
        "#,
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(result, RecoveryValue::Int(52));
}

#[test]
fn bytebuf_representation_remains_private() {
    let errors = compile_source_to_bytecode(
        "forge-bytebuf.glorious",
        r#"
            bad(bytes: Vec<u8>) -> ByteBuf { ByteBuf { bytes: move bytes } }
            main() -> () { () }
        "#,
    )
    .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("private field")),
        "unexpected diagnostics: {errors:?}",
    );
}
