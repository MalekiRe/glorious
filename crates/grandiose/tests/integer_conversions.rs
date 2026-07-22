use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_phases_with_options,
    diagnostic::Diagnostic,
    eval::{Host, Value as RecoveryValue},
    run_source,
    span::Span,
};
use grandiose_vm::{Instruction, Primitive, Value, Vm, verify};

const TYPES: [&str; 12] = [
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
            "integer conversion must not reach the host",
            span,
        ))
    }
}

#[derive(Clone, Copy, Debug)]
enum Integer {
    Signed(i128),
    Unsigned(u128),
}

fn bits(ty: &str) -> u32 {
    match ty {
        "u8" | "i8" => 8,
        "u16" | "i16" => 16,
        "u32" | "i32" => 32,
        "u64" | "i64" | "usize" | "isize" => 64,
        "u128" | "i128" => 128,
        _ => unreachable!(),
    }
}

fn signed(ty: &str) -> bool {
    ty.starts_with('i')
}

fn mask(width: u32) -> u128 {
    if width == 128 {
        u128::MAX
    } else {
        (1_u128 << width) - 1
    }
}

fn source_values(ty: &str) -> Vec<Integer> {
    let width = bits(ty);
    if signed(ty) {
        let (minimum, maximum) = if width == 128 {
            (i128::MIN, i128::MAX)
        } else {
            let limit = 1_i128 << (width - 1);
            (-limit, limit - 1)
        };
        vec![
            Integer::Signed(minimum),
            Integer::Signed(-1),
            Integer::Signed(0),
            Integer::Signed(maximum),
        ]
    } else {
        vec![
            Integer::Unsigned(0),
            Integer::Unsigned(1),
            Integer::Unsigned(mask(width)),
        ]
    }
}

fn vm_value(ty: &str, value: Integer) -> Value {
    match (ty, value) {
        ("i128", Integer::Signed(value)) => Value::I128(value),
        ("i8" | "i16" | "i32" | "i64" | "isize", Integer::Signed(value)) => {
            Value::I64(value as i64)
        }
        ("u128", Integer::Unsigned(value)) => Value::U128(value),
        ("u8" | "u16" | "u32" | "u64" | "usize", Integer::Unsigned(value)) => {
            Value::U64(value as u64)
        }
        _ => unreachable!(),
    }
}

fn wrapping_result(target: &str, value: Integer) -> Integer {
    let raw = match value {
        Integer::Signed(value) => value as u128,
        Integer::Unsigned(value) => value,
    } & mask(bits(target));
    if signed(target) {
        let width = bits(target);
        let value = if width == 128 {
            raw as i128
        } else {
            ((raw << (128 - width)) as i128) >> (128 - width)
        };
        Integer::Signed(value)
    } else {
        Integer::Unsigned(raw)
    }
}

fn checked_result(target: &str, value: Integer) -> Option<Integer> {
    let width = bits(target);
    if signed(target) {
        let (minimum, maximum) = if width == 128 {
            (i128::MIN, i128::MAX)
        } else {
            let limit = 1_i128 << (width - 1);
            (-limit, limit - 1)
        };
        let value = match value {
            Integer::Signed(value) => value,
            Integer::Unsigned(value) => i128::try_from(value).ok()?,
        };
        (minimum..=maximum)
            .contains(&value)
            .then_some(Integer::Signed(value))
    } else {
        let value = match value {
            Integer::Signed(value) => u128::try_from(value).ok()?,
            Integer::Unsigned(value) => value,
        };
        (value <= mask(width)).then_some(Integer::Unsigned(value))
    }
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing function `{name}`")) as u32
}

fn matrix_source(source_ty: &str) -> String {
    let mut source = String::new();
    for target in TYPES {
        source.push_str(&format!(
            "wrap_{source_ty}_to_{target}(value: {source_ty}) -> {target} {{ wrapping_convert_to_{target}(move value) }}\n\
             check_{source_ty}_to_{target}(value: {source_ty}) -> Option<{target}> {{ checked_{source_ty}_to_{target}(move value) }}\n"
        ));
    }
    source.push_str("main() -> { () }");
    source
}

fn check_conversion_row(source_ty: &str) {
    let source = matrix_source(source_ty);
    for level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "integer-conversion-matrix.glorious",
            &source,
            CompileOptions {
                optimization_level: level,
            },
        )
        .unwrap();
        let verified = verify(phases.artifact.clone()).unwrap();
        for target in TYPES {
            let wrap = function_id(&phases.artifact, &format!("wrap_{source_ty}_to_{target}"));
            let checked = function_id(&phases.artifact, &format!("check_{source_ty}_to_{target}"));
            let option_type = phases.artifact.functions[checked as usize].return_type;
            for input in source_values(source_ty) {
                let argument = vm_value(source_ty, input);
                let wrapped = Vm::new(verified.clone())
                    .run(wrap, vec![argument.clone()])
                    .unwrap();
                assert_eq!(
                    wrapped,
                    vm_value(target, wrapping_result(target, input)),
                    "{level:?}: wrapping {source_ty} -> {target} for {input:?}"
                );

                let checked_value = Vm::new(verified.clone())
                    .run(checked, vec![argument])
                    .unwrap();
                let expected = match checked_result(target, input) {
                    Some(value) => Value::aggregate_with_variant(
                        option_type,
                        Some(0),
                        [vm_value(target, value)],
                    ),
                    None => Value::aggregate_with_variant(option_type, Some(1), [Value::Unit]),
                };
                assert_eq!(
                    checked_value, expected,
                    "{level:?}: checked {source_ty} -> {target} for {input:?}"
                );
            }
        }

        for primitive in [Primitive::IntConvertChecked, Primitive::IntConvertWrapping] {
            assert!(phases.artifact.code.iter().any(
                |instruction| matches!(instruction, Instruction::Primitive { op, .. } if *op == primitive)
            ));
        }
    }
}

macro_rules! conversion_row_test {
    ($name:ident, $source_ty:literal) => {
        #[test]
        fn $name() {
            check_conversion_row($source_ty);
        }
    };
}

conversion_row_test!(
    checked_and_wrapping_conversion_from_u8_at_o1_through_o3,
    "u8"
);
conversion_row_test!(
    checked_and_wrapping_conversion_from_u16_at_o1_through_o3,
    "u16"
);
conversion_row_test!(
    checked_and_wrapping_conversion_from_u32_at_o1_through_o3,
    "u32"
);
conversion_row_test!(
    checked_and_wrapping_conversion_from_u64_at_o1_through_o3,
    "u64"
);
conversion_row_test!(
    checked_and_wrapping_conversion_from_u128_at_o1_through_o3,
    "u128"
);
conversion_row_test!(
    checked_and_wrapping_conversion_from_usize_at_o1_through_o3,
    "usize"
);
conversion_row_test!(
    checked_and_wrapping_conversion_from_i8_at_o1_through_o3,
    "i8"
);
conversion_row_test!(
    checked_and_wrapping_conversion_from_i16_at_o1_through_o3,
    "i16"
);
conversion_row_test!(
    checked_and_wrapping_conversion_from_i32_at_o1_through_o3,
    "i32"
);
conversion_row_test!(
    checked_and_wrapping_conversion_from_i64_at_o1_through_o3,
    "i64"
);
conversion_row_test!(
    checked_and_wrapping_conversion_from_i128_at_o1_through_o3,
    "i128"
);
conversion_row_test!(
    checked_and_wrapping_conversion_from_isize_at_o1_through_o3,
    "isize"
);

#[test]
fn recovery_checked_conversion_rejects_cross_sign_and_narrowing_boundaries() {
    for (return_type, body, expected) in [
        (
            "Option<u8>",
            "checked_i16_to_u8(-1)",
            RecoveryValue::Enum {
                name: "Result".into(),
                variant: "Err".into(),
                fields: std::rc::Rc::new(vec![RecoveryValue::Unit]),
            },
        ),
        (
            "Option<i8>",
            "checked_u16_to_i8(255)",
            RecoveryValue::Enum {
                name: "Result".into(),
                variant: "Err".into(),
                fields: std::rc::Rc::new(vec![RecoveryValue::Unit]),
            },
        ),
        (
            "Option<u16>",
            "checked_i8_to_u16(127)",
            RecoveryValue::Enum {
                name: "Result".into(),
                variant: "Ok".into(),
                fields: std::rc::Rc::new(vec![RecoveryValue::Integer {
                    signed: false,
                    bits: 16,
                    raw: 127,
                }]),
            },
        ),
    ] {
        let source = format!("main() -> {return_type} {{ {body} }}");
        assert_eq!(
            run_source(
                "recovery-integer-conversion.glorious",
                &source,
                vec![],
                &mut NoHost
            )
            .unwrap(),
            expected
        );
    }
}

#[test]
fn conversion_leaf_names_do_not_grant_primitive_authority() {
    let errors = compile_source_to_phases_with_options(
        "forged-conversion-leaf.glorious",
        "probe(value: i16) -> u8 { __g1_int_convert_checked_to_u8(move value) } main() -> { () }",
        CompileOptions::default(),
    )
    .unwrap_err();
    assert!(errors.iter().any(|error| {
        error
            .message
            .contains("primitive leaves may be called only from their trusted standard-library source segment")
    }), "{errors:#?}");

    let errors = run_source(
        "forged-conversion-leaf-recovery.glorious",
        "main() -> u8 { __g1_int_convert_checked_to_u8(1) }",
        vec![],
        &mut NoHost,
    )
    .unwrap_err();
    assert!(errors.iter().any(|error| {
        error
            .message
            .contains("runtime primitive leaves may be called only from their trusted standard-library source segment")
    }));
}

#[test]
fn checked_usize_arithmetic_reports_boundaries_without_trapping() {
    for level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "checked-usize.glorious",
            "probe_add(left: usize, right: usize) -> Option<usize> { checked_usize_add(move left, move right) }
             probe_sub(left: usize, right: usize) -> Option<usize> { checked_usize_sub(move left, move right) }
             probe_mul(left: usize, right: usize) -> Option<usize> { checked_usize_mul(move left, move right) }
             main() -> { () }",
            CompileOptions {
                optimization_level: level,
            },
        )
        .unwrap();
        let verified = verify(phases.artifact.clone()).unwrap();
        for (name, left, right, expected) in [
            ("probe_add", u64::MAX, 1, None),
            ("probe_add", u64::MAX, 0, Some(u64::MAX)),
            ("probe_sub", 0, 1, None),
            ("probe_sub", 4, 3, Some(1)),
            ("probe_mul", u64::MAX, 2, None),
            ("probe_mul", 3, 4, Some(12)),
            ("probe_mul", 0, u64::MAX, Some(0)),
        ] {
            let function = function_id(&phases.artifact, name);
            let option_type = phases.artifact.functions[function as usize].return_type;
            let actual = Vm::new(verified.clone())
                .run(function, vec![Value::U64(left), Value::U64(right)])
                .unwrap();
            let expected = match expected {
                Some(value) => {
                    Value::aggregate_with_variant(option_type, Some(0), [Value::U64(value)])
                }
                None => Value::aggregate_with_variant(option_type, Some(1), [Value::Unit]),
            };
            assert_eq!(actual, expected, "{level:?} {name}({left}, {right})");
        }
    }
}

#[test]
fn trusted_conversion_wrappers_are_emitted_only_when_user_roots_reach_them() {
    let empty = compile_source_to_phases_with_options(
        "no-conversions.glorious",
        "main() -> { () }",
        CompileOptions::default(),
    )
    .unwrap();
    assert!(
        empty
            .artifact
            .functions
            .iter()
            .all(|function| !function.name.starts_with("checked_"))
    );
    assert!(empty.artifact.code.iter().all(|instruction| {
        !matches!(
            instruction,
            Instruction::Primitive {
                op: Primitive::IntConvertChecked | Primitive::IntConvertWrapping,
                ..
            }
        )
    }));

    let reached = compile_source_to_phases_with_options(
        "one-conversion.glorious",
        "probe(value: i16) -> Option<u8> { checked_i16_to_u8(move value) } main() -> { () }",
        CompileOptions::default(),
    )
    .unwrap();
    assert!(
        reached
            .artifact
            .functions
            .iter()
            .any(|function| function.name == "checked_i16_to_u8")
    );
    assert!(
        reached
            .artifact
            .functions
            .iter()
            .all(|function| function.name == "checked_i16_to_u8"
                || !function.name.starts_with("checked_"))
    );
    for primitive in [Primitive::IntConvertChecked, Primitive::IntConvertWrapping] {
        assert!(reached.artifact.code.iter().any(
            |instruction| matches!(instruction, Instruction::Primitive { op, .. } if *op == primitive)
        ));
    }
}
