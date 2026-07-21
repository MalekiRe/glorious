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
            "character execution must not perform a host effect",
            span,
        ))
    }
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing function `{name}`")) as u32
}

const SURFACE: &str = r#"
    effect BoolCase { inspect(value: Bool) -> !; }
    bool_score(value: Bool) -> u64 {
        handle perform BoolCase::inspect(move value) {
            BoolCase::inspect(Result::Ok(_)) => 1,
            BoolCase::inspect(Result::Err(_)) => 0
        }
    }
    char_length(value: char) -> usize { char_utf8_len(move value) }
    char_round_trip(value: u32) -> u32 {
        let converted = char_from_u32(move value);
        if(converted is Result::Ok(_)) {
            char_to_u32(converted.0)
        } else { 0 }
    }
    scalar_valid(value: u32) -> u64 {
        bool_score(char_is_valid_scalar(move value))
    }
    main() -> () { () }
"#;

#[test]
fn public_character_scalar_surface_executes_at_o0_through_o3() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "character-public-surface.glorious",
            SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let verified = verify(phases.artifact.clone()).unwrap();
        let run = |name, args| {
            Vm::new(verified.clone())
                .run(function_id(&phases.artifact, name), args)
                .unwrap()
        };

        for (character, width) in [('A', 1), ('¢', 2), ('€', 3), ('😀', 4)] {
            assert_eq!(
                run("char_length", vec![Value::U64(character as u64)]),
                Value::U64(width),
            );
            assert_eq!(
                run("char_round_trip", vec![Value::U64(character as u64)]),
                Value::U64(character as u64),
            );
        }
        assert_eq!(
            run("char_round_trip", vec![Value::U64(0xd800)]),
            Value::U64(0),
        );
        assert_eq!(
            run("char_round_trip", vec![Value::U64(0x11_0000)]),
            Value::U64(0),
        );
        assert_eq!(
            run("scalar_valid", vec![Value::U64(0x10_ffff)]),
            Value::U64(1),
        );
        assert_eq!(run("scalar_valid", vec![Value::U64(0xdfff)]), Value::U64(0),);
        assert_eq!(
            run("scalar_valid", vec![Value::U64(0x11_0000)]),
            Value::U64(0),
        );
    }
}

#[test]
fn public_character_scalar_surface_has_recovery_parity() {
    let source = SURFACE.replace(
        "main() -> () { () }",
        "main() -> u32 { char_round_trip(128512) }",
    );
    assert_eq!(
        run_source(
            "character-public-recovery.glorious",
            &source,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::Integer {
            signed: false,
            bits: 32,
            raw: 0x1f600,
        },
    );
}
