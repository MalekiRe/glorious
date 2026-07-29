use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_phases_with_options,
    diagnostic::Diagnostic,
    eval::{Host, Value as RecoveryValue},
    run_source,
    span::Span,
};
use grandiose_vm::{Instruction, Primitive, Value, Vm, verify};

const INTEGER_TYPES: [&str; 12] = [
    "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize",
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
            "scalar operations must not perform host effects",
            span,
        ))
    }
}

fn source() -> String {
    let mut source = String::new();
    for ty in INTEGER_TYPES {
        source.push_str(&format!(
            "wrap_add_{ty}(a: {ty}, b: {ty}) -> {ty} {{ wrapping_add(move a, move b) }}\n\
             wrap_sub_{ty}(a: {ty}, b: {ty}) -> {ty} {{ wrapping_sub(move a, move b) }}\n\
             wrap_mul_{ty}(a: {ty}, b: {ty}) -> {ty} {{ wrapping_mul(move a, move b) }}\n\
             wrap_neg_{ty}(a: {ty}) -> {ty} {{ wrapping_neg(move a) }}\n\
             and_{ty}(a: {ty}, b: {ty}) -> {ty} {{ bit_and(move a, move b) }}\n\
             or_{ty}(a: {ty}, b: {ty}) -> {ty} {{ bit_or(move a, move b) }}\n\
             xor_{ty}(a: {ty}, b: {ty}) -> {ty} {{ bit_xor(move a, move b) }}\n\
             not_{ty}(a: {ty}) -> {ty} {{ bit_not(move a) }}\n\
             shl_{ty}(a: {ty}, count: u32) -> {ty} {{ shift_left(move a, move count) }}\n\
             shr_{ty}(a: {ty}, count: u32) -> {ty} {{ shift_right(move a, move count) }}\n"
        ));
    }
    source.push_str("main() -> { () }");
    source
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing function `{name}`")) as u32
}

fn bits(ty: &str) -> u32 {
    match ty {
        "i8" | "u8" => 8,
        "i16" | "u16" => 16,
        "i32" | "u32" => 32,
        "i64" | "u64" | "isize" | "usize" => 64,
        "i128" | "u128" => 128,
        _ => unreachable!(),
    }
}

fn value(ty: &str, raw: u128) -> Value {
    let width = bits(ty);
    let mask = if width == 128 {
        u128::MAX
    } else {
        (1_u128 << width) - 1
    };
    let raw = raw & mask;
    match ty {
        "i128" => Value::I128(raw as i128),
        "i8" | "i16" | "i32" | "i64" | "isize" => {
            let signed = if width == 64 || raw < (1_u128 << (width - 1)) {
                raw as i64
            } else {
                (raw as i128 - (1_i128 << width)) as i64
            };
            Value::I64(signed)
        }
        "u128" => Value::U128(raw),
        "u8" | "u16" | "u32" | "u64" | "usize" => Value::U64(raw as u64),
        _ => unreachable!(),
    }
}

#[test]
fn generic_integer_wrapper_contextualizes_a_literal_from_a_nested_typed_argument() {
    let source = r#"
        bits() -> u32 { 0b101101 }
        answer() -> u32 { bit_and(bits(), 0b001111) }
        comparison() -> Bool {
            __g1_integer_equal(bit_and(bits(), 0b001111), 0b001101)
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases_with_options(
        "generic-integer-wrapper-context.glorious",
        source,
        CompileOptions {
            optimization_level: OptimizationLevel::O3,
        },
    )
    .unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(verified.clone())
            .run(function_id(&phases.artifact, "answer"), vec![])
            .unwrap(),
        Value::U64(0b001101)
    );
    let comparison = function_id(&phases.artifact, "comparison");
    let bool_type = phases.artifact.functions[comparison as usize].return_type;
    assert_eq!(
        Vm::new(verified).run(comparison, vec![]).unwrap(),
        Value::aggregate_with_variant(bool_type, Some(0), [Value::Unit])
    );
}

#[test]
fn frozen_integer_surface_executes_all_widths_at_o1_through_o3() {
    for level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "scalar-surface.glorious",
            &source(),
            CompileOptions {
                optimization_level: level,
            },
        )
        .unwrap();
        let verified = verify(phases.artifact.clone()).unwrap();
        for ty in INTEGER_TYPES {
            let width = bits(ty);
            let mask = if width == 128 {
                u128::MAX
            } else {
                (1_u128 << width) - 1
            };
            let run = |name: &str, args: Vec<Value>| {
                Vm::new(verified.clone())
                    .run(function_id(&phases.artifact, &format!("{name}_{ty}")), args)
                    .unwrap()
            };
            assert_eq!(
                run("wrap_add", vec![value(ty, mask), value(ty, 1)]),
                value(ty, 0),
                "{level:?} wrapping add {ty}"
            );
            assert_eq!(
                run("wrap_sub", vec![value(ty, 0), value(ty, 1)]),
                value(ty, mask),
                "{level:?} wrapping sub {ty}"
            );
            assert_eq!(
                run("wrap_mul", vec![value(ty, mask), value(ty, 2)]),
                value(ty, mask - 1),
                "{level:?} wrapping mul {ty}"
            );
            assert_eq!(
                run("wrap_neg", vec![value(ty, 1)]),
                value(ty, mask),
                "{level:?} wrapping negation {ty}"
            );
            assert_eq!(
                run("and", vec![value(ty, 0xaa), value(ty, 0x0f)]),
                value(ty, 0x0a)
            );
            assert_eq!(
                run("or", vec![value(ty, 0xa0), value(ty, 0x0f)]),
                value(ty, 0xaf)
            );
            assert_eq!(
                run("xor", vec![value(ty, 0xaa), value(ty, 0xff)]),
                value(ty, 0x55)
            );
            assert_eq!(run("not", vec![value(ty, 0)]), value(ty, mask));
            assert_eq!(
                run("shl", vec![value(ty, 1), Value::U64(u64::from(width - 1))],),
                value(ty, 1_u128 << (width - 1))
            );
            let signed = ty.starts_with('i');
            let shifted = if signed { mask } else { 1 };
            assert_eq!(
                run(
                    "shr",
                    vec![
                        value(ty, 1_u128 << (width - 1)),
                        Value::U64(u64::from(width - 1)),
                    ]
                ),
                value(ty, shifted),
                "{level:?} right shift {ty}"
            );
            let error = Vm::new(verified.clone())
                .run(
                    function_id(&phases.artifact, &format!("shl_{ty}")),
                    vec![value(ty, 1), Value::U64(u64::from(width))],
                )
                .unwrap_err();
            assert!(
                error.to_string().contains("shift"),
                "{level:?} {ty}: {error}"
            );
        }

        for primitive in [
            Primitive::IntWrappingAdd,
            Primitive::IntWrappingSub,
            Primitive::IntWrappingMul,
            Primitive::IntBitAnd,
            Primitive::IntBitOr,
            Primitive::IntBitXor,
            Primitive::IntBitNot,
            Primitive::IntShl,
            Primitive::IntShr,
        ] {
            assert!(phases.artifact.functions.iter().any(|function| {
                phases.artifact.code[function.code_start as usize
                    ..(function.code_start + function.code_len) as usize]
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::Primitive { op, .. } if *op == primitive))
            }), "{level:?} omitted {primitive:?}");
        }
    }
}

#[test]
fn recovery_interpreter_uses_the_same_typed_wrapping_and_shift_rules() {
    for ty in INTEGER_TYPES {
        let source = format!(
            "typed(value: {ty}) -> {ty} {{ wrapping_neg(wrapping_neg(move value)) }}\n\
             main() -> {ty} {{ typed(0) }}"
        );
        let result = run_source("scalar-recovery.glorious", &source, vec![], &mut NoHost).unwrap();
        assert_eq!(
            result,
            RecoveryValue::Integer {
                signed: ty.starts_with('i'),
                bits: bits(ty) as u8,
                raw: 0,
            },
            "recovery wrapping result for {ty}"
        );
    }

    let signed_shift = run_source(
        "signed-shift-recovery.glorious",
        "typed(value: i8, count: u32) -> i8 { shift_right(move value, move count) } main() -> i8 { typed(-128, 7) }",
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(
        signed_shift,
        RecoveryValue::Integer {
            signed: true,
            bits: 8,
            raw: u8::MAX.into(),
        }
    );
}

#[test]
fn scalar_leaf_spellings_do_not_grant_user_code_primitive_authority() {
    let errors = compile_source_to_phases_with_options(
        "forged-scalar-leaf.glorious",
        "forged(value: u8) -> u8 { __g1_int_bit_not(move value) } main() -> { () }",
        CompileOptions::default(),
    )
    .unwrap_err();
    assert!(errors.iter().any(|error| {
        error
            .message
            .contains("primitive leaves may be called only from their trusted standard-library source segment")
    }), "{errors:#?}");

    let errors = run_source(
        "forged-scalar-leaf-recovery.glorious",
        "main() -> u8 { __g1_int_bit_not(0) }",
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
