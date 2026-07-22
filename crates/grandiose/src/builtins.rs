//! Canonical metadata for runtime leaves supplied by the distributed library.
//!
//! These names grant no authority by themselves. Consumers must still bind a
//! declaration inside the explicitly trusted standard-library source segment.

use grandiose_vm::Primitive;

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
