//! Canonical metadata for runtime leaves supplied by the distributed library.
//!
//! These names grant no authority by themselves. Consumers must still bind a
//! declaration inside the explicitly trusted standard-library source segment.

use grandiose_vm::Primitive;

/// The semantic family of a primitive admitted by the generation-1 runtime
/// manifest.  This is the single classification used by manifest validation
/// and the recovery interpreter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RuntimePrimitiveFamily {
    Scalar,
    ArrayDependent,
    TypedFloat,
}

const SCALAR: RuntimePrimitiveFamily = RuntimePrimitiveFamily::Scalar;
const ARRAY: RuntimePrimitiveFamily = RuntimePrimitiveFamily::ArrayDependent;

pub(crate) const FIXED_RUNTIME_PRIMITIVE_LEAVES: &[(
    u64,
    &str,
    Primitive,
    RuntimePrimitiveFamily,
)] = &[
    (
        0x0030,
        "__g1_char_from_u32_checked",
        Primitive::CharFromU32Checked,
        SCALAR,
    ),
    (0x0031, "__g1_char_to_u32", Primitive::CharToU32, SCALAR),
    (0x0040, "__g1_text_byte_len", Primitive::TextByteLen, SCALAR),
    (0x0041, "__g1_text_concat", Primitive::TextConcat, SCALAR),
    (0x0042, "__g1_text_eq", Primitive::TextEq, SCALAR),
    (
        0x0043,
        "__g1_text_from_utf8_checked",
        Primitive::TextFromUtf8Checked,
        SCALAR,
    ),
    (0x0044, "__g1_text_as_bytes", Primitive::TextAsBytes, SCALAR),
    (0x0050, "__g1_bytes_len", Primitive::BytesLen, SCALAR),
    (0x0051, "__g1_bytes_concat", Primitive::BytesConcat, SCALAR),
    (0x0052, "__g1_bytes_get", Primitive::BytesGet, SCALAR),
    (0x0053, "__g1_bytes_slice", Primitive::BytesSlice, SCALAR),
    (
        0x0054,
        "__g1_bytes_from_array_move",
        Primitive::BytesFromArrayMove,
        ARRAY,
    ),
    (
        0x0055,
        "__g1_bytes_to_array",
        Primitive::BytesToArray,
        ARRAY,
    ),
    (0x0060, "__g1_array_new", Primitive::ArrayNew, ARRAY),
    (0x0061, "__g1_array_len", Primitive::ArrayLen, ARRAY),
    (
        0x0062,
        "__g1_array_get_copy",
        Primitive::ArrayGetCopy,
        ARRAY,
    ),
    (
        0x0063,
        "__g1_array_get_move",
        Primitive::ArrayGetMove,
        ARRAY,
    ),
    (
        0x0064,
        "__g1_array_get_borrow_shared",
        Primitive::ArrayGetBorrowShared,
        ARRAY,
    ),
    (
        0x0065,
        "__g1_array_get_borrow_unique",
        Primitive::ArrayGetBorrowUnique,
        ARRAY,
    ),
    (
        0x0066,
        "__g1_array_set_move",
        Primitive::ArraySetMove,
        ARRAY,
    ),
    (0x0067, "__g1_array_empty", Primitive::ArrayEmpty, ARRAY),
    (
        0x0068,
        "__g1_array_push_move",
        Primitive::ArrayPushMove,
        ARRAY,
    ),
    (
        0x0069,
        "__g1_array_pop_move",
        Primitive::ArrayPopMove,
        ARRAY,
    ),
    (
        0x006a,
        "__g1_array_capacity",
        Primitive::ArrayCapacity,
        ARRAY,
    ),
    (0x006b, "__g1_array_reserve", Primitive::ArrayReserve, ARRAY),
    (
        0x006c,
        "__g1_array_finish_drained",
        Primitive::ArrayFinishDrained,
        ARRAY,
    ),
];

pub(crate) const FLOAT_OPERATIONS: &[(&str, Primitive)] = &[
    ("add", Primitive::FloatAdd),
    ("sub", Primitive::FloatSub),
    ("mul", Primitive::FloatMul),
    ("div", Primitive::FloatDiv),
    ("rem", Primitive::FloatRem),
    ("neg", Primitive::FloatNeg),
    ("eq", Primitive::FloatEq),
    ("ne", Primitive::FloatNe),
    ("lt", Primitive::FloatLt),
    ("le", Primitive::FloatLe),
    ("gt", Primitive::FloatGt),
    ("ge", Primitive::FloatGe),
];

pub(crate) fn runtime_primitive_family(primitive: Primitive) -> Option<RuntimePrimitiveFamily> {
    if let Some((_, _, _, family)) = FIXED_RUNTIME_PRIMITIVE_LEAVES
        .iter()
        .find(|(_, _, candidate, _)| *candidate == primitive)
    {
        return Some(*family);
    }
    (FLOAT_OPERATIONS
        .iter()
        .any(|(_, candidate)| *candidate == primitive)
        || matches!(
            primitive,
            Primitive::FloatConvert
                | Primitive::IntToFloat
                | Primitive::FloatToIntChecked
                | Primitive::FloatToBits
                | Primitive::FloatFromBits
        ))
    .then_some(RuntimePrimitiveFamily::TypedFloat)
}

/// Materialize the canonical distributed table. IDs are intentionally assigned
/// here so adding a float leaf cannot update the manifest and interpreter maps
/// independently.
pub(crate) fn distributed_runtime_primitive_leaves() -> Vec<(u64, String, Primitive)> {
    let mut leaves = FIXED_RUNTIME_PRIMITIVE_LEAVES
        .iter()
        .map(|(id, name, primitive, _)| (*id, (*name).into(), *primitive))
        .collect::<Vec<_>>();
    let mut next_id = 0x0200_u64;
    let mut push = |name: String, primitive| {
        leaves.push((next_id, name, primitive));
        next_id += 1;
    };
    for width in ["f32", "f64"] {
        for &(operation, primitive) in FLOAT_OPERATIONS {
            push(format!("__g1_{width}_{operation}"), primitive);
        }
    }
    push("__g1_f32_to_f64".into(), Primitive::FloatConvert);
    push("__g1_f64_to_f32".into(), Primitive::FloatConvert);
    for target in ["f32", "f64"] {
        for &source in INTEGER_SCALAR_NAMES {
            push(format!("__g1_{source}_to_{target}"), Primitive::IntToFloat);
        }
    }
    for source in ["f32", "f64"] {
        for &target in INTEGER_SCALAR_NAMES {
            push(
                format!("__g1_{source}_to_{target}_checked"),
                Primitive::FloatToIntChecked,
            );
        }
    }
    for (name, primitive) in [
        ("__g1_f32_to_bits", Primitive::FloatToBits),
        ("__g1_f32_from_bits", Primitive::FloatFromBits),
        ("__g1_f64_to_bits", Primitive::FloatToBits),
        ("__g1_f64_from_bits", Primitive::FloatFromBits),
    ] {
        push(name.into(), primitive);
    }
    leaves
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum IntegerLeafShape {
    Unary,
    Binary,
    Shift,
}

impl IntegerLeafShape {
    pub(crate) const fn diagnostic_name(self) -> &'static str {
        match self {
            Self::Unary => "unary",
            Self::Binary => "binary",
            Self::Shift => "shift",
        }
    }
}

pub(crate) const INTEGER_PRIMITIVE_LEAVES: &[(&str, Primitive, IntegerLeafShape)] = &[
    (
        "__g1_int_wrapping_add",
        Primitive::IntWrappingAdd,
        IntegerLeafShape::Binary,
    ),
    (
        "__g1_int_wrapping_sub",
        Primitive::IntWrappingSub,
        IntegerLeafShape::Binary,
    ),
    (
        "__g1_int_wrapping_mul",
        Primitive::IntWrappingMul,
        IntegerLeafShape::Binary,
    ),
    (
        "__g1_int_bit_and",
        Primitive::IntBitAnd,
        IntegerLeafShape::Binary,
    ),
    (
        "__g1_int_bit_or",
        Primitive::IntBitOr,
        IntegerLeafShape::Binary,
    ),
    (
        "__g1_int_bit_xor",
        Primitive::IntBitXor,
        IntegerLeafShape::Binary,
    ),
    (
        "__g1_int_bit_not",
        Primitive::IntBitNot,
        IntegerLeafShape::Unary,
    ),
    ("__g1_int_shl", Primitive::IntShl, IntegerLeafShape::Shift),
    ("__g1_int_shr", Primitive::IntShr, IntegerLeafShape::Shift),
];

pub(crate) const INTEGER_SCALAR_NAMES: &[&str] = &[
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
];

pub(crate) const INTEGER_CONVERSION_KINDS: &[(&str, Primitive)] = &[
    ("checked", Primitive::IntConvertChecked),
    ("wrapping", Primitive::IntConvertWrapping),
];

pub(crate) fn integer_conversion_leaf_name(operation: &str, target: &str) -> String {
    format!("__g1_int_convert_{operation}_to_{target}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distributed_runtime_leaf_table_is_frozen_and_classified() {
        let leaves = distributed_runtime_primitive_leaves();
        assert_eq!(FIXED_RUNTIME_PRIMITIVE_LEAVES.len(), 26);
        assert_eq!(leaves.len(), 104);
        assert_eq!(
            leaves.first(),
            Some(&(
                0x0030,
                "__g1_char_from_u32_checked".into(),
                Primitive::CharFromU32Checked,
            ))
        );
        assert_eq!(
            leaves.get(26),
            Some(&(0x0200, "__g1_f32_add".into(), Primitive::FloatAdd))
        );
        for (index, id, name, primitive) in [
            (
                25,
                0x006c,
                "__g1_array_finish_drained",
                Primitive::ArrayFinishDrained,
            ),
            (37, 0x020b, "__g1_f32_ge", Primitive::FloatGe),
            (38, 0x020c, "__g1_f64_add", Primitive::FloatAdd),
            (49, 0x0217, "__g1_f64_ge", Primitive::FloatGe),
            (50, 0x0218, "__g1_f32_to_f64", Primitive::FloatConvert),
            (51, 0x0219, "__g1_f64_to_f32", Primitive::FloatConvert),
            (52, 0x021a, "__g1_u8_to_f32", Primitive::IntToFloat),
            (75, 0x0231, "__g1_isize_to_f64", Primitive::IntToFloat),
            (
                76,
                0x0232,
                "__g1_f32_to_u8_checked",
                Primitive::FloatToIntChecked,
            ),
            (
                99,
                0x0249,
                "__g1_f64_to_isize_checked",
                Primitive::FloatToIntChecked,
            ),
            (100, 0x024a, "__g1_f32_to_bits", Primitive::FloatToBits),
            (103, 0x024d, "__g1_f64_from_bits", Primitive::FloatFromBits),
        ] {
            assert_eq!(leaves.get(index), Some(&(id, name.into(), primitive)));
        }
        assert!(
            leaves
                .iter()
                .all(|(_, _, primitive)| runtime_primitive_family(*primitive).is_some())
        );
        assert_eq!(
            runtime_primitive_family(Primitive::ArrayLen),
            Some(RuntimePrimitiveFamily::ArrayDependent)
        );
        assert_eq!(
            runtime_primitive_family(Primitive::FloatNeg),
            Some(RuntimePrimitiveFamily::TypedFloat)
        );
    }

    #[test]
    fn distributed_integer_leaf_mapping_is_frozen() {
        assert_eq!(
            INTEGER_PRIMITIVE_LEAVES
                .iter()
                .map(|(name, primitive, shape)| (*name, *primitive as u32, shape.diagnostic_name()))
                .collect::<Vec<_>>(),
            vec![
                ("__g1_int_wrapping_add", 0x0005, "binary"),
                ("__g1_int_wrapping_sub", 0x0006, "binary"),
                ("__g1_int_wrapping_mul", 0x0007, "binary"),
                ("__g1_int_bit_and", 0x0008, "binary"),
                ("__g1_int_bit_or", 0x0009, "binary"),
                ("__g1_int_bit_xor", 0x000a, "binary"),
                ("__g1_int_bit_not", 0x000b, "unary"),
                ("__g1_int_shl", 0x000c, "shift"),
                ("__g1_int_shr", 0x000d, "shift"),
            ]
        );
    }

    #[test]
    fn distributed_integer_conversion_mapping_is_frozen() {
        assert_eq!(
            INTEGER_SCALAR_NAMES,
            [
                "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128",
                "isize",
            ]
        );
        assert_eq!(
            INTEGER_CONVERSION_KINDS
                .iter()
                .map(|(operation, primitive)| (*operation, *primitive as u32))
                .collect::<Vec<_>>(),
            [("checked", 0x0014), ("wrapping", 0x0015)]
        );
        let actual = INTEGER_SCALAR_NAMES
            .iter()
            .flat_map(|target| {
                INTEGER_CONVERSION_KINDS
                    .iter()
                    .map(move |(operation, primitive)| {
                        (
                            integer_conversion_leaf_name(operation, target),
                            *primitive as u32,
                        )
                    })
            })
            .collect::<Vec<_>>();
        assert_eq!(actual.len(), 24);
        assert_eq!(
            actual.first().unwrap(),
            &("__g1_int_convert_checked_to_u8".into(), 0x0014)
        );
        assert_eq!(
            actual.last().unwrap(),
            &("__g1_int_convert_wrapping_to_isize".into(), 0x0015)
        );
    }
}
