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
            "StringBuilder integer-format recovery test performed a host effect",
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

fn assert_ok_text(value: Value, expected: &str, context: &str) {
    let Value::Aggregate(result) = value else {
        panic!("{context}: StringBuilder::finish did not return a Result")
    };
    let result = result.borrow();
    assert_eq!(result.variant, Some(0), "{context}: expected Result::Ok");
    assert_eq!(
        result.fields,
        [Some(Value::Text(expected.into()))],
        "{context}",
    );
}

const SURFACE: &str = r#"
    unsigned_half(value: u64) -> u64 {
        value / wrapping_convert_to_u64(2)
    }

    unsigned_increment(value: u64) -> u64 {
        value + wrapping_convert_to_u64(1)
    }

    unsigned_cases() -> Result<String, Utf8Error> {
        let builder = StringBuilder::new();
        StringBuilder::append_u64(&mut builder, 0);
        StringBuilder::push_byte(&mut builder, 124);
        StringBuilder::append_u64(&mut builder, 7);
        StringBuilder::push_byte(&mut builder, 124);
        StringBuilder::append_u64(&mut builder, 42);
        StringBuilder::push_byte(&mut builder, 124);
        StringBuilder::append_u64(&mut builder, 1005);
        StringBuilder::push_byte(&mut builder, 124);
        StringBuilder::append_u64(&mut builder, wrapping_convert_to_u64(-1));
        StringBuilder::finish(move builder)
    }

    signed_cases() -> Result<String, Utf8Error> {
        let builder = StringBuilder::new();
        StringBuilder::append_i64(&mut builder, 0);
        StringBuilder::push_byte(&mut builder, 124);
        StringBuilder::append_i64(&mut builder, 7);
        StringBuilder::push_byte(&mut builder, 124);
        StringBuilder::append_i64(&mut builder, -42);
        StringBuilder::push_byte(&mut builder, 124);
        StringBuilder::append_i64(&mut builder, 9223372036854775807);
        StringBuilder::push_byte(&mut builder, 124);

        let unsigned_max = wrapping_convert_to_u64(-1);
        let minimum_magnitude = unsigned_increment(unsigned_half(move unsigned_max));
        StringBuilder::append_i64(
            &mut builder,
            wrapping_convert_to_i64(move minimum_magnitude)
        );
        StringBuilder::finish(move builder)
    }

    composed() -> Result<String, Utf8Error> {
        let prefix = "pre:";
        let middle = ":mid:";
        let middle_bytes = String::as_bytes(&middle);
        let builder = StringBuilder::new();
        StringBuilder::append_string(&mut builder, &prefix);
        StringBuilder::append_u64(&mut builder, 123);
        StringBuilder::append_bytes(&mut builder, &middle_bytes);
        StringBuilder::append_i64(&mut builder, -456);
        StringBuilder::push_byte(&mut builder, 33);
        StringBuilder::finish(move builder)
    }

    main() -> () { () }
"#;

#[test]
fn string_builder_formats_u64_and_i64_at_every_optimization_level() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "string-builder-integer-format.glorious",
            SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(artifact.clone()).unwrap());

        assert_ok_text(
            vm.run(function_id(&artifact, "unsigned_cases"), vec![])
                .unwrap(),
            "0|7|42|1005|18446744073709551615",
            &format!("unsigned cases at {optimization_level:?}"),
        );
        assert_ok_text(
            vm.run(function_id(&artifact, "signed_cases"), vec![])
                .unwrap(),
            "0|7|-42|9223372036854775807|-9223372036854775808",
            &format!("signed cases at {optimization_level:?}"),
        );
        assert_ok_text(
            vm.run(function_id(&artifact, "composed"), vec![]).unwrap(),
            "pre:123:mid:-456!",
            &format!("composition at {optimization_level:?}"),
        );
    }
}

#[test]
fn string_builder_integer_formatting_has_recovery_parity() {
    let value = run_source(
        "string-builder-integer-format-recovery.glorious",
        r#"
            effect Finished { inspect(value: Result<String, Utf8Error>) -> !; }

            main() -> String {
                let builder = StringBuilder::new();
                StringBuilder::append_string(&mut builder, &"value=");
                StringBuilder::append_i64(&mut builder, -2048);
                StringBuilder::push_byte(&mut builder, 44);
                StringBuilder::append_u64(
                    &mut builder,
                    wrapping_convert_to_u64(-1)
                );
                handle perform Finished::inspect(StringBuilder::finish(move builder)) {
                    Finished::inspect(Result::Ok(text)) => move text,
                    Finished::inspect(Result::Err(_)) => "invalid utf-8"
                }
            }
        "#,
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(
        value,
        RecoveryValue::String("value=-2048,18446744073709551615".into()),
    );
}
