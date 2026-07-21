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
            "Hasher recovery test performed a host effect",
            span,
        ))
    }
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| {
            function.name == name
                || function
                    .name
                    .strip_prefix("$specialization$")
                    .and_then(|wire| wire.split_once('#'))
                    .is_some_and(|(template, _)| template == name)
        })
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

const HASHER_SURFACE: &str = r#"
    abc_bytes() -> Bytes {
        let bytes = ByteBuf::with_capacity(3);
        ByteBuf::push(&mut bytes, 97);
        ByteBuf::push(&mut bytes, 98);
        ByteBuf::push(&mut bytes, 99);
        ByteBuf::finish(move bytes)
    }

    empty_hash() -> u64 {
        let hasher = Hasher::new();
        Hasher::finish(&hasher)
    }

    abc_hash() -> u64 {
        let hasher = Hasher::new();
        let bytes = abc_bytes();
        Hasher::write_bytes(&mut hasher, &bytes);
        Hasher::finish(&hasher)
    }

    abc_incremental_hash() -> u64 {
        let hasher = Hasher::new();
        Hasher::write_u8(&mut hasher, 97);
        Hasher::write_u8(&mut hasher, 98);
        Hasher::write_u8(&mut hasher, 99);
        Hasher::finish(&hasher)
    }

    u16_hash() -> u64 {
        let hasher = Hasher::new();
        Hasher::write_u16(&mut hasher, 4660);
        Hasher::finish(&hasher)
    }

    u32_hash() -> u64 {
        let hasher = Hasher::new();
        Hasher::write_u32(&mut hasher, 305419896);
        Hasher::finish(&hasher)
    }

    u64_hash() -> u64 {
        let hasher = Hasher::new();
        Hasher::write_u64(&mut hasher, 81985529216486895);
        Hasher::finish(&hasher)
    }

    u128_hash() -> u64 {
        let hasher = Hasher::new();
        Hasher::write_u128(&mut hasher, 305419896);
        Hasher::finish(&hasher)
    }

    usize_hash() -> u64 {
        let hasher = Hasher::new();
        Hasher::write_usize(&mut hasher, 305419896);
        Hasher::finish(&hasher)
    }

    main() -> () { () }
"#;

#[test]
fn hasher_executes_at_every_optimization_level() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "hash-collections.glorious",
            HASHER_SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(phases.artifact.clone()).unwrap());

        for (name, expected) in [
            ("empty_hash", 14_695_981_039_346_656_037),
            ("abc_hash", 16_654_208_175_385_433_931),
            ("abc_incremental_hash", 16_654_208_175_385_433_931),
            ("u16_hash", 571_567_958_656_141_443),
            ("u32_hash", 14_758_243_562_650_612_581),
            ("u64_hash", 4_029_383_781_087_845_461),
            ("u128_hash", 12_354_139_171_154_272_469),
            ("usize_hash", 8_132_965_955_333_539_893),
        ] {
            assert_eq!(
                vm.run(function_id(&phases.artifact, name), vec![]).unwrap(),
                Value::U64(expected),
                "{optimization_level:?} {name}"
            );
        }
    }
}

#[test]
fn hasher_state_is_private() {
    for (name, source, expected) in [
        (
            "hasher-forge.glorious",
            "bad()->Hasher{Hasher{state:0}} main()->(){()}",
            "private field",
        ),
        (
            "hasher-project.glorious",
            "bad(value:Hasher)->u64{value.state} main()->(){()}",
            "private field `state`",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source)
            .expect_err("user code accessed Hasher's private state");
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn hasher_has_recovery_parity() {
    let result = run_source(
        "hasher-recovery.glorious",
        &HASHER_SURFACE.replace("main() -> () { () }", "main() -> u64 { abc_hash() }"),
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert!(matches!(
        result,
        RecoveryValue::Integer {
            signed: false,
            bits: 64,
            raw: 16_654_208_175_385_433_931
        }
    ));
}
