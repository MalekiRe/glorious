use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode_with_options,
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
            "ByteBuf patching recovery test performed a host effect",
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
    effect BoolCase { inspect(value: Result<(), ()>) -> !; }

    bool_score(value: Bool) -> usize {
        handle perform BoolCase::inspect(move value) {
            BoolCase::inspect(Result::Ok(_)) => 1,
            BoolCase::inspect(Result::Err(_)) => 0
        }
    }

    canonical_patches() -> Bytes {
        let bytes = ByteBuf::new();
        ByteBuf::push(&mut bytes, 170);
        ByteBuf::push(&mut bytes, 187);
        ByteBuf::push(&mut bytes, 204);
        ByteBuf::push(&mut bytes, 221);
        ByteBuf::push(&mut bytes, 238);
        ByteBuf::resize_zeroed(&mut bytes, 8);
        let _a = ByteBuf::patch_u16_le(&mut bytes, 1, 4660);
        let _b = ByteBuf::patch_u32_le(&mut bytes, 4, wrapping_convert_to_u32(-1985229329));
        let _c = ByteBuf::align_zeroed(&mut bytes, 16);
        let _d = ByteBuf::patch_u64_le(&mut bytes, 8, 81985529216486895);
        ByteBuf::finish(move bytes)
    }

    resize_shrink_and_regrow() -> Bytes {
        let bytes = ByteBuf::new();
        ByteBuf::push(&mut bytes, 10);
        ByteBuf::push(&mut bytes, 20);
        ByteBuf::push(&mut bytes, 30);
        ByteBuf::push(&mut bytes, 40);
        ByteBuf::resize_zeroed(&mut bytes, 2);
        ByteBuf::resize_zeroed(&mut bytes, 5);
        ByteBuf::finish(move bytes)
    }

    success_score() -> usize {
        let bytes = ByteBuf::new();
        ByteBuf::resize_zeroed(&mut bytes, 16);
        bool_score(ByteBuf::patch_u16_le(&mut bytes, 14, 1))
            + bool_score(ByteBuf::patch_u32_le(&mut bytes, 12, 2))
            + bool_score(ByteBuf::patch_u64_le(&mut bytes, 8, 3))
            + bool_score(ByteBuf::align_zeroed(&mut bytes, 8))
    }

    failed_operations_are_atomic() -> Bytes {
        let bytes = ByteBuf::new();
        ByteBuf::push(&mut bytes, 1);
        ByteBuf::push(&mut bytes, 2);
        ByteBuf::push(&mut bytes, 3);
        let _a = ByteBuf::patch_u16_le(&mut bytes, 2, 65535);
        let _b = ByteBuf::patch_u32_le(&mut bytes, wrapping_convert_to_usize(-1), 4294967295);
        let _c = ByteBuf::patch_u64_le(&mut bytes, wrapping_convert_to_usize(-2), 1);
        let _d = ByteBuf::align_zeroed(&mut bytes, 0);
        let _e = ByteBuf::align_zeroed(&mut bytes, 3);
        ByteBuf::finish(move bytes)
    }

    failure_score() -> usize {
        let bytes = ByteBuf::new();
        ByteBuf::push(&mut bytes, 1);
        ByteBuf::push(&mut bytes, 2);
        ByteBuf::push(&mut bytes, 3);
        bool_score(ByteBuf::patch_u16_le(&mut bytes, 2, 65535))
            + bool_score(ByteBuf::patch_u32_le(&mut bytes, wrapping_convert_to_usize(-1), 4294967295))
            + bool_score(ByteBuf::patch_u64_le(&mut bytes, wrapping_convert_to_usize(-2), 1))
            + bool_score(ByteBuf::align_zeroed(&mut bytes, 0))
            + bool_score(ByteBuf::align_zeroed(&mut bytes, 3))
    }

    main() -> () { () }
"#;

#[test]
fn bytebuf_resize_patch_and_alignment_have_canonical_results_at_o0_through_o3() {
    let mut canonical = vec![0xaa, 0x34, 0x12, 0xdd, 0xef, 0xcd, 0xab, 0x89];
    canonical.extend_from_slice(&[0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01]);

    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "bytebuf-patching.glorious",
            SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(artifact.clone()).unwrap());

        assert_eq!(
            vm.run(function_id(&artifact, "canonical_patches"), vec![])
                .unwrap(),
            Value::Bytes(canonical.clone().into()),
            "canonical patches at {optimization_level:?}",
        );
        assert_eq!(
            vm.run(function_id(&artifact, "resize_shrink_and_regrow"), vec![],)
                .unwrap(),
            Value::Bytes(vec![10_u8, 20, 0, 0, 0].into()),
            "resize at {optimization_level:?}",
        );
        assert_eq!(
            vm.run(function_id(&artifact, "success_score"), vec![])
                .unwrap(),
            Value::U64(4),
            "successful status at {optimization_level:?}",
        );
    }
}

#[test]
fn bytebuf_patch_and_alignment_failures_are_atomic_and_overflow_safe() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "bytebuf-patching-failures.glorious",
            SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(artifact.clone()).unwrap());

        assert_eq!(
            vm.run(
                function_id(&artifact, "failed_operations_are_atomic"),
                vec![],
            )
            .unwrap(),
            Value::Bytes(vec![1_u8, 2, 3].into()),
            "atomic failure bytes at {optimization_level:?}",
        );
        assert_eq!(
            vm.run(function_id(&artifact, "failure_score"), vec![])
                .unwrap(),
            Value::U64(0),
            "failure status at {optimization_level:?}",
        );
    }
}

#[test]
fn bytebuf_resize_patch_and_alignment_have_recovery_parity() {
    let result = run_source(
        "bytebuf-patching-recovery.glorious",
        r#"
            effect ByteCase { inspect(value: Result<u8, BytesIndexError>) -> !; }

            main() -> u8 {
                let bytes = ByteBuf::new();
                ByteBuf::resize_zeroed(&mut bytes, 4);
                let _patched = ByteBuf::patch_u16_le(&mut bytes, 1, 4660);
                let _aligned = ByteBuf::align_zeroed(&mut bytes, 8);
                let bytes = ByteBuf::finish(move bytes);
                handle perform ByteCase::inspect(Bytes::get(&bytes, 2)) {
                    ByteCase::inspect(Result::Ok(byte)) => move byte,
                    ByteCase::inspect(Result::Err(_)) => 0
                }
            }
        "#,
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(result, RecoveryValue::Int(18));
}
