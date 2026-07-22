use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_phases_with_options,
    diagnostic::Diagnostic,
    eval::{Host, Value as RecoveryValue},
    run_source,
    span::Span,
};
use grandiose_vm::{Value, Vm, verify};

const INTEGERS: [&str; 12] = [
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
];

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
            "float source execution must not perform a host effect",
            span,
        ))
    }
}

fn source() -> String {
    let mut source = String::from(
        r#"
        effect BoolCase { inspect(value: Bool) -> !; }
        bool_score(value: Bool) -> u64 {
            handle perform BoolCase::inspect(move value) {
                BoolCase::inspect(Result::Ok(_)) => 1,
                BoolCase::inspect(Result::Err(_)) => 0
            }
        }
        arithmetic_f32() -> u32 {
            f32_to_bits(f32_rem(f32_div(f32_mul(f32_add(1.5, 2.5), 3.0), 3.0), 3.0))
        }
        arithmetic_f64() -> u64 {
            f64_to_bits(f64_neg(f64_rem(f64_mul(f64_add(10.5, 0.5), 2.0), 5.0)))
        }
        comparisons() -> u64 {
            handle perform BoolCase::inspect(f32_less(1.0, 2.0)) {
                BoolCase::inspect(Result::Ok(_)) =>
                    handle perform BoolCase::inspect(
                        f64_greater_equal(2.0, 2.0)
                    ) {
                        BoolCase::inspect(Result::Ok(_)) => 2,
                        BoolCase::inspect(Result::Err(_)) => 1
                    },
                BoolCase::inspect(Result::Err(_)) => 0
            }
        }
        canonical_f32_nan() -> u32 { f32_to_bits(f32_div(0.0, 0.0)) }
        canonical_f64_nan() -> u64 { f64_to_bits(f64_div(0.0, 0.0)) }
        signed_zero_f32() -> u32 { f32_to_bits(f32_neg(0.0)) }
        signed_zero_f64() -> u64 { f64_to_bits(f64_neg(0.0)) }
        main() -> () { () }
        "#,
    );
    for integer in INTEGERS {
        source.push_str(&format!(
            "case_{integer}_f32(value: {integer}) -> u32 {{ f32_to_bits({integer}_to_f32(move value)) }}\n\
             case_{integer}_f64(value: {integer}) -> u64 {{ f64_to_bits({integer}_to_f64(move value)) }}\n\
             effect Case_{integer} {{ inspect(value: Option<{integer}>) -> !; }}\n\
             checked_f32_{integer}(value: f32) -> {integer} {{\n\
                 let result = checked_f32_to_{integer}(move value);\n\
                 handle perform Case_{integer}::inspect(move result) {{\n\
                     Case_{integer}::inspect(Result::Ok(converted)) => move converted,\n\
                     Case_{integer}::inspect(Result::Err(_)) => 0\n\
                 }}\n\
             }}\n\
             checked_f64_{integer}(value: f64) -> {integer} {{\n\
                 let result = checked_f64_to_{integer}(move value);\n\
                 handle perform Case_{integer}::inspect(move result) {{\n\
                     Case_{integer}::inspect(Result::Ok(converted)) => move converted,\n\
                     Case_{integer}::inspect(Result::Err(_)) => 0\n\
                 }}\n\
             }}\n"
        ));
    }
    source
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing function `{name}`")) as u32
}

fn integer_value(ty: &str, value: u128) -> Value {
    match ty {
        "u128" => Value::U128(value),
        "i128" => Value::I128(value as i128),
        ty if ty.starts_with('u') => Value::U64(value as u64),
        _ => Value::I64(value as i64),
    }
}

fn public_float_surface_executes_at_o1_through_o3_inner() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "float-source-surface.glorious",
            &source(),
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let verified = verify(phases.artifact.clone()).unwrap();
        let run = |name: &str, args| {
            Vm::new(verified.clone())
                .run(function_id(&phases.artifact, name), args)
                .unwrap()
        };
        assert_eq!(
            run("arithmetic_f32", vec![]),
            Value::U64(1.0_f32.to_bits().into())
        );
        assert_eq!(
            run("arithmetic_f64", vec![]),
            Value::U64((-2.0_f64).to_bits())
        );
        assert_eq!(run("comparisons", vec![]), Value::U64(2));
        assert_eq!(run("canonical_f32_nan", vec![]), Value::U64(0x7fc0_0000));
        assert_eq!(
            run("canonical_f64_nan", vec![]),
            Value::U64(0x7ff8_0000_0000_0000),
        );
        assert_eq!(run("signed_zero_f32", vec![]), Value::U64(0x8000_0000));
        assert_eq!(
            run("signed_zero_f64", vec![]),
            Value::U64(0x8000_0000_0000_0000),
        );
        for integer in INTEGERS {
            let seven = integer_value(integer, 7);
            assert_eq!(
                run(&format!("case_{integer}_f32"), vec![seven.clone()]),
                Value::U64(7.0_f32.to_bits().into()),
            );
            assert_eq!(
                run(&format!("case_{integer}_f64"), vec![seven]),
                Value::U64(7.0_f64.to_bits()),
            );
            assert_eq!(
                run(&format!("checked_f32_{integer}"), vec![Value::F32(7.75)]),
                integer_value(integer, 7),
            );
            assert_eq!(
                run(&format!("checked_f64_{integer}"), vec![Value::F64(7.75)]),
                integer_value(integer, 7),
            );
            assert_eq!(
                run(
                    &format!("checked_f32_{integer}"),
                    vec![Value::F32(f32::NAN)],
                ),
                integer_value(integer, 0),
            );
            assert_eq!(
                run(
                    &format!("checked_f64_{integer}"),
                    vec![Value::F64(f64::INFINITY)],
                ),
                integer_value(integer, 0),
            );
        }
    }
}

#[test]
fn public_float_surface_executes_at_o1_through_o3() {
    std::thread::Builder::new()
        .name("float-source-surface".into())
        .stack_size(32 * 1024 * 1024)
        .spawn(public_float_surface_executes_at_o1_through_o3_inner)
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn public_float_surface_has_recovery_parity() {
    let source = source().replace("main() -> () { () }", "main() -> u64 { arithmetic_f64() }");
    assert_eq!(
        run_source(
            "float-source-recovery.glorious",
            &source,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::Integer {
            signed: false,
            bits: 64,
            raw: (-2.0_f64).to_bits().into(),
        },
    );
}

const TRAIT_FORMAT_SURFACE: &str = r#"
    effect BoolCase { inspect(value: Bool) -> !; }
    effect OrderingCase { inspect(value: Ordering) -> !; }
    effect FinishCase { inspect(value: Result<String, Utf8Error>) -> !; }
    bool_score(value: Bool) -> u64 {
        handle perform BoolCase::inspect(move value) {
            BoolCase::inspect(Result::Ok(_)) => 1,
            BoolCase::inspect(Result::Err(_)) => 0
        }
    }
    eq_f32(left: &f32, right: &f32) -> Bool { Eq::eq(move left, move right) }
    eq_f64(left: &f64, right: &f64) -> Bool { Eq::eq(move left, move right) }
    cmp_f32(left: &f32, right: &f32) -> Ordering {
        Ord::cmp(move left, move right)
    }
    equality() -> u64 {
        let left = f32_from_bits(2143289345);
        let right = f32_from_bits(2147483647);
        bool_score(eq_f32(&left, &right))
    }
    zeros_distinct() -> u64 {
        let left = f64_from_bits(0);
        let right = f64_from_bits(9223372036854775808);
        bool_score(eq_f64(&left, &right))
    }
    zero_order() -> u64 {
        let left = f32_from_bits(2147483648);
        let right = f32_from_bits(0);
        handle perform OrderingCase::inspect(
            cmp_f32(&left, &right)
        ) {
            OrderingCase::inspect(Ordering::Less) => 1,
            OrderingCase::inspect(_) => 0
        }
    }
    default_f32() -> f32 { Default::default() }
    default_f64() -> f64 { Default::default() }
    default_f32_bits() -> u32 { f32_to_bits(default_f32()) }
    default_f64_bits() -> u64 { f64_to_bits(default_f64()) }
    hash_f32(value: f32) -> u64 {
        let hasher = Hasher::new();
        Hash::hash(&value, &mut hasher);
        Hasher::finish(&hasher)
    }
    default_char() -> char { Default::default() }
    default_char_scalar() -> u32 { char_to_u32(default_char()) }
    eq_char(left: &char, right: &char) -> Bool { Eq::eq(move left, move right) }
    char_equality() -> u64 {
        let left = '☃';
        let right = '☃';
        bool_score(eq_char(&left, &right))
    }
    hash_char(value: char) -> u64 {
        let hasher = Hasher::new();
        Hash::hash(&value, &mut hasher);
        Hasher::finish(&hasher)
    }
    display_char(value: char) -> String {
        let formatter = Formatter::new();
        Display::fmt(&value, &mut formatter);
        handle perform FinishCase::inspect(Formatter::finish(move formatter)) {
            FinishCase::inspect(Result::Ok(text)) => move text,
            FinishCase::inspect(Result::Err(_)) => ""
        }
    }
    debug_char(value: char) -> String {
        let formatter = Formatter::new();
        Debug::fmt(&value, &mut formatter);
        handle perform FinishCase::inspect(Formatter::finish(move formatter)) {
            FinishCase::inspect(Result::Ok(text)) => move text,
            FinishCase::inspect(Result::Err(_)) => ""
        }
    }
    format_f32_value(value: f32) -> String { f32_format(move value) }
    format_f64_value(value: f64) -> String { f64_format(move value) }
    main() -> () { () }
"#;

#[test]
fn float_traits_and_exact_formatting_execute() {
    let phases = compile_source_to_phases_with_options(
        "float-traits-format.glorious",
        TRAIT_FORMAT_SURFACE,
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap_or_else(|errors| panic!("{errors:#?}"));
    let verified = verify(phases.artifact.clone()).unwrap();
    let run = |name: &str, args| {
        Vm::new(verified.clone())
            .run(function_id(&phases.artifact, name), args)
            .unwrap()
    };
    assert_eq!(run("equality", vec![]), Value::U64(1));
    assert_eq!(run("zeros_distinct", vec![]), Value::U64(0));
    assert_eq!(run("zero_order", vec![]), Value::U64(1));
    assert_eq!(run("default_f32_bits", vec![]), Value::U64(0));
    assert_eq!(run("default_f64_bits", vec![]), Value::U64(0));
    assert_eq!(run("default_char_scalar", vec![]), Value::U64(0));
    assert_eq!(run("char_equality", vec![]), Value::U64(1));
    assert_eq!(
        run("hash_f32", vec![Value::F32(f32::from_bits(0x7fa0_0001))]),
        run("hash_f32", vec![Value::F32(f32::from_bits(0x7fc0_0000))]),
    );
    assert_eq!(
        run("format_f32_value", vec![Value::F32(-0.0)]),
        Value::Text("-0.0".into()),
    );
    assert_eq!(
        run("display_char", vec![Value::U64('☃' as u64)]),
        Value::Text("☃".into()),
    );
    assert_eq!(
        run("debug_char", vec![Value::U64('\n' as u64)]),
        Value::Text("'\\n'".into()),
    );
    assert_eq!(
        run("hash_char", vec![Value::U64('☃' as u64)]),
        run("hash_char", vec![Value::U64('☃' as u64)]),
    );
    assert_eq!(
        run("format_f64_value", vec![Value::F64(f64::INFINITY)]),
        Value::Text("inf".into()),
    );
    assert_eq!(
        run("format_f64_value", vec![Value::F64(1.5)]),
        Value::Text("1.5000000000000000000000000000000000000000000000000000e0".into()),
    );
}

fn exact_formatting_is_optimization_stable_inner() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "float-format-optimization.glorious",
            TRAIT_FORMAT_SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let verified = verify(phases.artifact.clone()).unwrap();
        let run = |name: &str, args| {
            Vm::new(verified.clone())
                .run(function_id(&phases.artifact, name), args)
                .unwrap()
        };
        assert_eq!(
            run("format_f64_value", vec![Value::F64(1.5)]),
            Value::Text("1.5000000000000000000000000000000000000000000000000000e0".into()),
            "{optimization_level:?}",
        );
        assert_eq!(
            run("format_f32_value", vec![Value::F32(f32::NAN)]),
            Value::Text("NaN".into()),
            "{optimization_level:?}",
        );
    }
}

#[test]
fn exact_formatting_is_optimization_stable() {
    std::thread::Builder::new()
        .name("float-format-optimization".into())
        .stack_size(32 * 1024 * 1024)
        .spawn(exact_formatting_is_optimization_stable_inner)
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn float_and_character_traits_have_recovery_parity() {
    let source = TRAIT_FORMAT_SURFACE.replace(
        "main() -> () { () }",
        "main() -> String { f64_format(1.5) }",
    );
    assert_eq!(
        run_source(
            "float-format-recovery.glorious",
            &source,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::String("1.5000000000000000000000000000000000000000000000000000e0".into(),),
    );

    let source = TRAIT_FORMAT_SURFACE.replace(
        "main() -> () { () }",
        "main() -> String { debug_char('\\n') }",
    );
    assert_eq!(
        run_source(
            "character-debug-recovery.glorious",
            &source,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::String("'\\n'".into()),
    );
}
