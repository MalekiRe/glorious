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
            "fundamental trait execution performed a host effect",
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
    default_i16() -> i16 { Default::default() }
    default_u64() -> u64 { Default::default() }
    default_string() -> String { Default::default() }
    default_bytes() -> Bytes { Default::default() }

    take_score() -> i64 {
        let value = 41;
        let previous = take(&mut value);
        move previous + move value
    }

    defaults_score() -> u64 {
        let signed = default_i16();
        let unsigned = default_u64();
        let text = default_string();
        let bytes = default_bytes();
        wrapping_convert_to_u64(move signed)
            + move unsigned
            + wrapping_convert_to_u64(String::byte_len(&text))
            + wrapping_convert_to_u64(Bytes::len(&bytes))
    }

    main() -> () { () }
"#;

#[test]
fn fundamental_traits_execute_at_o1_through_o3() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "fundamental-traits.glorious",
            SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(artifact.clone()).unwrap());
        assert_eq!(
            vm.run(function_id(&artifact, "defaults_score"), vec![])
                .unwrap(),
            Value::U64(0),
        );
        assert_eq!(
            vm.run(function_id(&artifact, "take_score"), vec![])
                .unwrap(),
            Value::I64(41),
        );
    }
}

#[test]
fn fundamental_traits_have_recovery_parity() {
    let value = run_source(
        "fundamental-traits-recovery.glorious",
        r#"
            default_i64() -> i64 { Default::default() }
            cmp_i64(left: &i64, right: &i64) -> Ordering {
                Ord::cmp(move left, move right)
            }
            cmp_string(left: &String, right: &String) -> Ordering {
                Ord::cmp(move left, move right)
            }
            main() -> u64 {
                let value = default_i64();
                let ordering = cmp_i64(&value, &value);
                let left = "alpha";
                let right = "alphabet";
                let lexical = cmp_string(&left, &right);
                if(ordering is Ordering::Equal) {
                    if(lexical is Ordering::Less) {
                        42
                    } else { 1 }
                } else { 0 }
            }
        "#,
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(
        value,
        RecoveryValue::Integer {
            signed: false,
            bits: 64,
            raw: 42,
        },
    );

    let taken = run_source(
        "fundamental-take-recovery.glorious",
        r#"
            main() -> i64 {
                let value = 73;
                let previous = take(&mut value);
                move previous + move value
            }
        "#,
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(
        taken,
        RecoveryValue::Integer {
            signed: true,
            bits: 64,
            raw: 73,
        },
    );

    let rendered = run_source(
        "fundamental-debug-recovery.glorious",
        r#"
            effect Finished { inspect(value: Result<String, Utf8Error>) -> !; }
            debug_string(value: &String, formatter: &mut Formatter) -> () {
                Debug::fmt(move value, move formatter)
            }
            debug_bytes(value: &Bytes, formatter: &mut Formatter) -> () {
                Debug::fmt(move value, move formatter)
            }
            display_i16(value: &i16, formatter: &mut Formatter) -> () {
                Display::fmt(move value, move formatter)
            }
            main() -> String {
                let formatter = Formatter::new();
                let signed = wrapping_convert_to_i16(-12);
                let text = "line\n\"snowman=☃\"";
                let bytes = b"\0\x7f\xff";
                display_i16(&signed, &mut formatter);
                let display_separator = " ";
                Formatter::literal(&mut formatter, &display_separator);
                debug_string(&text, &mut formatter);
                let separator = " ";
                Formatter::literal(&mut formatter, &separator);
                debug_bytes(&bytes, &mut formatter);
                handle perform Finished::inspect(Formatter::finish(move formatter)) {
                    Finished::inspect(Result::Ok(output)) => move output,
                    Finished::inspect(Result::Err(_)) => "invalid"
                }
            }
        "#,
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(
        rendered,
        RecoveryValue::String("-12 \"line\\n\\\"snowman=☃\\\"\" b[0, 127, 255]".into()),
    );
}

#[test]
fn primitive_and_tuple_impl_heads_are_coherent_solver_inputs() {
    let source = r#"
        trait Marker {}
        impl Marker for f32 {}
        impl Marker for f64 {}
        impl Marker for Char {}
        impl Marker for () {}
        impl Marker for (f32, Char) {}

        main() -> () { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        compile_source_to_bytecode_with_options(
            "structural-impl-heads.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
    }
}
