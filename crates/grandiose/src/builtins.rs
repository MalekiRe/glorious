//! Canonical metadata for runtime leaves supplied by the distributed library.
//!
//! These names grant no authority by themselves. Consumers must still bind a
//! declaration inside the explicitly trusted standard-library source segment.

use grandiose_vm::Primitive;

/// The exact, monomorphic source signature attached to a runtime leaf.
///
/// Keeping this next to the leaf registry prevents the compiler's authority
/// checks and the recovery interpreter from independently reverse-engineering
/// the ABI from primitive names and AST types.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct RuntimeLeafSignature<'a> {
    parameters: [Option<&'a str>; 3],
    result: &'a str,
}

impl<'a> RuntimeLeafSignature<'a> {
    const fn new(parameters: [Option<&'a str>; 3], result: &'a str) -> Self {
        Self { parameters, result }
    }

    pub(crate) fn parameters(self) -> impl Iterator<Item = &'a str> {
        self.parameters.into_iter().flatten()
    }

    pub(crate) const fn result(self) -> &'a str {
        self.result
    }

    pub(crate) fn matches(self, parameters: &[&str], result: Option<&str>) -> bool {
        self.parameters().eq(parameters.iter().copied()) && result == Some(self.result)
    }
}

const fn unary<'a>(value: &'a str, result: &'a str) -> RuntimeLeafSignature<'a> {
    RuntimeLeafSignature::new([Some(value), None, None], result)
}

const fn binary<'a>(left: &'a str, right: &'a str, result: &'a str) -> RuntimeLeafSignature<'a> {
    RuntimeLeafSignature::new([Some(left), Some(right), None], result)
}

const fn ternary<'a>(
    first: &'a str,
    second: &'a str,
    third: &'a str,
    result: &'a str,
) -> RuntimeLeafSignature<'a> {
    RuntimeLeafSignature::new([Some(first), Some(second), Some(third)], result)
}

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
    (
        0x0056,
        "__g1_bytes_utf8_valid_up_to",
        Primitive::BytesUtf8ValidUpTo,
        SCALAR,
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

/// Return the frozen monomorphic ABI for a manifest-bound leaf. Generic Array
/// leaves intentionally remain in the compiler because their signatures also
/// carry source-level type parameters and `Use` evidence.
pub(crate) fn runtime_leaf_signature<'a>(
    name: &'a str,
    primitive: Primitive,
) -> Option<RuntimeLeafSignature<'a>> {
    let fixed = match primitive {
        Primitive::CharFromU32Checked => unary("u32", "char"),
        Primitive::CharToU32 => unary("char", "u32"),
        Primitive::TextByteLen => unary("Text", "usize"),
        Primitive::TextConcat => binary("Text", "Text", "Text"),
        Primitive::TextEq => binary("Text", "Text", "u32"),
        Primitive::TextFromUtf8Checked => unary("Bytes", "Text"),
        Primitive::TextAsBytes => unary("Text", "Bytes"),
        Primitive::BytesLen => unary("Bytes", "usize"),
        Primitive::BytesUtf8ValidUpTo => unary("Bytes", "usize"),
        Primitive::BytesConcat => binary("Bytes", "Bytes", "Bytes"),
        Primitive::BytesGet => binary("Bytes", "usize", "u8"),
        Primitive::BytesSlice => ternary("Bytes", "usize", "usize", "Bytes"),
        _ => return typed_float_leaf_signature(name, primitive),
    };
    Some(fixed)
}

fn typed_float_leaf_signature<'a>(
    name: &'a str,
    primitive: Primitive,
) -> Option<RuntimeLeafSignature<'a>> {
    let width_for = |suffix| {
        name.strip_prefix("__g1_")
            .and_then(|name| name.strip_suffix(suffix))
            .filter(|width| matches!(*width, "f32" | "f64"))
    };
    let binary_suffix = match primitive {
        Primitive::FloatAdd => Some("_add"),
        Primitive::FloatSub => Some("_sub"),
        Primitive::FloatMul => Some("_mul"),
        Primitive::FloatDiv => Some("_div"),
        Primitive::FloatRem => Some("_rem"),
        _ => None,
    };
    if let Some(width) = binary_suffix.and_then(width_for) {
        return Some(binary(width, width, width));
    }
    if primitive == Primitive::FloatNeg {
        let width = width_for("_neg")?;
        return Some(unary(width, width));
    }
    let comparison_suffix = match primitive {
        Primitive::FloatEq => Some("_eq"),
        Primitive::FloatNe => Some("_ne"),
        Primitive::FloatLt => Some("_lt"),
        Primitive::FloatLe => Some("_le"),
        Primitive::FloatGt => Some("_gt"),
        Primitive::FloatGe => Some("_ge"),
        _ => None,
    };
    if let Some(width) = comparison_suffix.and_then(width_for) {
        return Some(binary(width, width, "u32"));
    }
    match primitive {
        Primitive::FloatConvert => match name {
            "__g1_f32_to_f64" => Some(unary("f32", "f64")),
            "__g1_f64_to_f32" => Some(unary("f64", "f32")),
            _ => None,
        },
        Primitive::IntToFloat => {
            let (source, target) = name.strip_prefix("__g1_")?.rsplit_once("_to_")?;
            (INTEGER_SCALAR_NAMES.contains(&source) && matches!(target, "f32" | "f64"))
                .then(|| unary(source, target))
        }
        Primitive::FloatToIntChecked => {
            let (source, target) = name
                .strip_prefix("__g1_")?
                .strip_suffix("_checked")?
                .split_once("_to_")?;
            (matches!(source, "f32" | "f64") && INTEGER_SCALAR_NAMES.contains(&target))
                .then(|| unary(source, target))
        }
        Primitive::FloatToBits => match name {
            "__g1_f32_to_bits" => Some(unary("f32", "u32")),
            "__g1_f64_to_bits" => Some(unary("f64", "u64")),
            _ => None,
        },
        Primitive::FloatFromBits => match name {
            "__g1_f32_from_bits" => Some(unary("u32", "f32")),
            "__g1_f64_from_bits" => Some(unary("u64", "f64")),
            _ => None,
        },
        _ => None,
    }
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
    Compare,
    Shift,
}

impl IntegerLeafShape {
    pub(crate) const fn diagnostic_name(self) -> &'static str {
        match self {
            Self::Unary => "unary",
            Self::Binary => "binary",
            Self::Compare => "comparison",
            Self::Shift => "shift",
        }
    }
}

pub(crate) const INTEGER_PRIMITIVE_LEAVES: &[(&str, Primitive, IntegerLeafShape)] = &[
    (
        "__g1_int_checked_add",
        Primitive::IntCheckedAdd,
        IntegerLeafShape::Binary,
    ),
    (
        "__g1_int_equal",
        Primitive::IntEq,
        IntegerLeafShape::Compare,
    ),
    ("__g1_int_less", Primitive::IntLt, IntegerLeafShape::Compare),
    (
        "__g1_int_greater",
        Primitive::IntGt,
        IntegerLeafShape::Compare,
    ),
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

/// Canonical generation-1 integer representation used by interpreter
/// coercions and generated conversion leaves.
pub(crate) fn integer_scalar_layout(name: &str) -> Option<(bool, u8)> {
    Some(match name {
        "u8" => (false, 8),
        "u16" => (false, 16),
        "u32" => (false, 32),
        "u64" | "usize" => (false, 64),
        "u128" => (false, 128),
        "i8" => (true, 8),
        "i16" => (true, 16),
        "i32" => (true, 32),
        "i64" | "isize" => (true, 64),
        "i128" => (true, 128),
        _ => return None,
    })
}

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
        assert_eq!(FIXED_RUNTIME_PRIMITIVE_LEAVES.len(), 27);
        assert_eq!(leaves.len(), 105);
        assert_eq!(
            leaves.first(),
            Some(&(
                0x0030,
                "__g1_char_from_u32_checked".into(),
                Primitive::CharFromU32Checked,
            ))
        );
        assert_eq!(
            leaves.get(27),
            Some(&(0x0200, "__g1_f32_add".into(), Primitive::FloatAdd))
        );
        for (index, id, name, primitive) in [
            (
                13,
                0x0056,
                "__g1_bytes_utf8_valid_up_to",
                Primitive::BytesUtf8ValidUpTo,
            ),
            (
                26,
                0x006c,
                "__g1_array_finish_drained",
                Primitive::ArrayFinishDrained,
            ),
            (38, 0x020b, "__g1_f32_ge", Primitive::FloatGe),
            (39, 0x020c, "__g1_f64_add", Primitive::FloatAdd),
            (50, 0x0217, "__g1_f64_ge", Primitive::FloatGe),
            (51, 0x0218, "__g1_f32_to_f64", Primitive::FloatConvert),
            (52, 0x0219, "__g1_f64_to_f32", Primitive::FloatConvert),
            (53, 0x021a, "__g1_u8_to_f32", Primitive::IntToFloat),
            (76, 0x0231, "__g1_isize_to_f64", Primitive::IntToFloat),
            (
                77,
                0x0232,
                "__g1_f32_to_u8_checked",
                Primitive::FloatToIntChecked,
            ),
            (
                100,
                0x0249,
                "__g1_f64_to_isize_checked",
                Primitive::FloatToIntChecked,
            ),
            (101, 0x024a, "__g1_f32_to_bits", Primitive::FloatToBits),
            (104, 0x024d, "__g1_f64_from_bits", Primitive::FloatFromBits),
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
                ("__g1_int_checked_add", 0x0000, "binary"),
                ("__g1_int_equal", 0x000e, "comparison"),
                ("__g1_int_less", 0x0010, "comparison"),
                ("__g1_int_greater", 0x0012, "comparison"),
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

    #[test]
    fn runtime_leaf_signatures_are_canonical_across_fixed_and_generated_leaves() {
        assert!(
            runtime_leaf_signature("custom_text_concat", Primitive::TextConcat)
                .unwrap()
                .matches(&["Text", "Text"], Some("Text"))
        );
        assert!(
            runtime_leaf_signature("__g1_f32_add", Primitive::FloatAdd)
                .unwrap()
                .matches(&["f32", "f32"], Some("f32"))
        );
        assert!(
            runtime_leaf_signature("__g1_i128_to_f64", Primitive::IntToFloat)
                .unwrap()
                .matches(&["i128"], Some("f64"))
        );
        assert!(
            runtime_leaf_signature("__g1_f64_to_usize_checked", Primitive::FloatToIntChecked)
                .unwrap()
                .matches(&["f64"], Some("usize"))
        );

        assert!(runtime_leaf_signature("__g1_f16_add", Primitive::FloatAdd).is_none());
        assert!(runtime_leaf_signature("__g1_u8_to_f16", Primitive::IntToFloat).is_none());
        assert!(runtime_leaf_signature("__g1_f32_add", Primitive::FloatSub).is_none());
        assert!(
            !runtime_leaf_signature("__g1_f64_from_bits", Primitive::FloatFromBits)
                .unwrap()
                .matches(&["u32"], Some("f64"))
        );
    }
}
