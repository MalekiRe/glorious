//! Finite machine-primitive authority bound to a trusted library identity.
//!
//! Source names are never authority.  A request host supplies selectors for a
//! distinguished standard-library package; binding resolves them to exact
//! public declaration identities and freezes a digestible table.

use std::collections::BTreeMap;

use crate::signature::HostImport;
use crate::MemoryPrimitive;
use crate::{
    ElaboratedHeader, ElaboratedInterface, PackageInterface, PackageKey, Quantity, ScalarType,
    Type,
    identity::{DefKey, Digest},
    types::EffectRow,
    types::{Lifetime, Mutability},
};

/// The two IEEE-754 formats exposed by the distributed runtime.  The format
/// is part of the primitive identity; a source declaration cannot obtain
/// f32 authority merely by having an f32-shaped signature.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FloatWidth {
    F32,
    F64,
}

impl FloatWidth {
    const fn scalar(self) -> ScalarType {
        match self {
            Self::F32 => ScalarType::F32,
            Self::F64 => ScalarType::F64,
        }
    }

    const fn name(self) -> &'static str {
        match self {
            Self::F32 => "f32",
            Self::F64 => "f64",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FloatBinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

impl FloatBinaryOp {
    const fn name(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::Sub => "sub",
            Self::Mul => "mul",
            Self::Div => "div",
            Self::Rem => "rem",
        }
    }
    const fn ordinal(self) -> u8 {
        match self {
            Self::Add => 0,
            Self::Sub => 1,
            Self::Mul => 2,
            Self::Div => 3,
            Self::Rem => 4,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FloatCompareOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl FloatCompareOp {
    const fn name(self) -> &'static str {
        match self {
            Self::Eq => "eq",
            Self::Ne => "ne",
            Self::Lt => "lt",
            Self::Le => "le",
            Self::Gt => "gt",
            Self::Ge => "ge",
        }
    }
    const fn ordinal(self) -> u8 {
        match self {
            Self::Eq => 0,
            Self::Ne => 1,
            Self::Lt => 2,
            Self::Le => 3,
            Self::Gt => 4,
            Self::Ge => 5,
        }
    }
}

/// One finite, manifest-addressed floating leaf.  Keeping conversion source
/// and target types in the authority key prevents an ABI-compatible integer
/// conversion from being silently substituted at the runtime boundary.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FloatPrimitive {
    Binary {
        width: FloatWidth,
        operation: FloatBinaryOp,
    },
    Neg {
        width: FloatWidth,
    },
    Compare {
        width: FloatWidth,
        operation: FloatCompareOp,
    },
    Convert {
        from: ScalarType,
        to: ScalarType,
        checked: bool,
    },
    ToBits {
        width: FloatWidth,
    },
    FromBits {
        width: FloatWidth,
    },
}

impl FloatPrimitive {
    fn is_valid(self) -> bool {
        match self {
            Self::Convert { from, to, checked } => {
                let float_from = matches!(from, ScalarType::F32 | ScalarType::F64);
                let float_to = matches!(to, ScalarType::F32 | ScalarType::F64);
                if checked {
                    float_from && is_runtime_integer(to)
                } else {
                    float_to && (is_runtime_integer(from) || (float_from && from != to))
                }
            }
            _ => true,
        }
    }

    pub(crate) fn scalar_signature(self) -> (Vec<ScalarType>, ScalarType) {
        match self {
            Self::Binary { width, .. } => {
                let ty = width.scalar();
                (vec![ty, ty], ty)
            }
            Self::Neg { width } => {
                let ty = width.scalar();
                (vec![ty], ty)
            }
            Self::Compare { width, .. } => {
                let ty = width.scalar();
                (vec![ty, ty], ScalarType::U32)
            }
            Self::Convert { from, to, .. } => (vec![from], to),
            Self::ToBits { width } => (
                vec![width.scalar()],
                match width {
                    FloatWidth::F32 => ScalarType::U32,
                    FloatWidth::F64 => ScalarType::U64,
                },
            ),
            Self::FromBits { width } => (
                vec![match width {
                    FloatWidth::F32 => ScalarType::U32,
                    FloatWidth::F64 => ScalarType::U64,
                }],
                width.scalar(),
            ),
        }
    }

    pub(crate) fn selector_name(self) -> String {
        match self {
            Self::Binary { width, operation } => format!("{}-{}", width.name(), operation.name()),
            Self::Neg { width } => format!("{}-neg", width.name()),
            Self::Compare { width, operation } => format!("{}-{}", width.name(), operation.name()),
            Self::Convert { from, to, checked } => format!(
                "{}-to-{}{}",
                scalar_name(from),
                scalar_name(to),
                if checked { "-checked" } else { "" }
            ),
            Self::ToBits { width } => format!("{}-to-bits", width.name()),
            Self::FromBits { width } => format!("{}-from-bits", width.name()),
        }
    }

    fn ordinal(self) -> u8 {
        match self {
            Self::Binary { width, operation } => width_ordinal(width) * 5 + operation.ordinal(),
            Self::Neg { width } => 10 + width_ordinal(width),
            Self::Compare { width, operation } => {
                12 + width_ordinal(width) * 6 + operation.ordinal()
            }
            Self::Convert {
                from: ScalarType::F32,
                to: ScalarType::F64,
                checked: false,
            } => 24,
            Self::Convert {
                from: ScalarType::F64,
                to: ScalarType::F32,
                checked: false,
            } => 25,
            Self::Convert {
                from,
                to: to @ (ScalarType::F32 | ScalarType::F64),
                checked: false,
            } => {
                26 + runtime_integer_ordinal(from).expect("validated float selector") * 2
                    + width_ordinal(if to == ScalarType::F32 {
                        FloatWidth::F32
                    } else {
                        FloatWidth::F64
                    })
            }
            Self::Convert {
                from: from @ (ScalarType::F32 | ScalarType::F64),
                to,
                checked: true,
            } => {
                50 + width_ordinal(if from == ScalarType::F32 {
                    FloatWidth::F32
                } else {
                    FloatWidth::F64
                }) * 12
                    + runtime_integer_ordinal(to).expect("validated float selector")
            }
            // Selector parsing, canonicalization, and direct binding validate
            // public enum constructions before these private tag operations.
            Self::Convert { .. } => unreachable!("invalid floating runtime conversion"),
            Self::ToBits { width } => 74 + width_ordinal(width),
            Self::FromBits { width } => 76 + width_ordinal(width),
        }
    }

    fn parse_selector_name(value: &str) -> Option<Self> {
        let (head, checked) = value
            .strip_suffix("-checked")
            .map_or((value, false), |head| (head, true));
        if !checked {
            if let Some(width) = head.strip_suffix("-to-bits").and_then(parse_float_width) {
                return Some(Self::ToBits { width });
            }
            if let Some(width) = head.strip_suffix("-from-bits").and_then(parse_float_width) {
                return Some(Self::FromBits { width });
            }
        }
        if let Some((from, to)) = head.split_once("-to-") {
            let from = parse_scalar_name(from)?;
            let to = parse_scalar_name(to)?;
            let primitive = Self::Convert { from, to, checked };
            return primitive.is_valid().then_some(primitive);
        }
        for (suffix, operation) in [
            ("-add", FloatBinaryOp::Add),
            ("-sub", FloatBinaryOp::Sub),
            ("-mul", FloatBinaryOp::Mul),
            ("-div", FloatBinaryOp::Div),
            ("-rem", FloatBinaryOp::Rem),
        ] {
            if let Some(width) = head.strip_suffix(suffix).and_then(parse_float_width) {
                return Some(Self::Binary { width, operation });
            }
        }
        if let Some(width) = head.strip_suffix("-neg").and_then(parse_float_width) {
            return Some(Self::Neg { width });
        }
        for (suffix, operation) in [
            ("-eq", FloatCompareOp::Eq),
            ("-ne", FloatCompareOp::Ne),
            ("-lt", FloatCompareOp::Lt),
            ("-le", FloatCompareOp::Le),
            ("-gt", FloatCompareOp::Gt),
            ("-ge", FloatCompareOp::Ge),
        ] {
            if let Some(width) = head.strip_suffix(suffix).and_then(parse_float_width) {
                return Some(Self::Compare { width, operation });
            }
        }
        None
    }
}

const fn width_ordinal(width: FloatWidth) -> u8 {
    match width {
        FloatWidth::F32 => 0,
        FloatWidth::F64 => 1,
    }
}
const fn scalar_name(scalar: ScalarType) -> &'static str {
    match scalar {
        ScalarType::U8 => "u8",
        ScalarType::U16 => "u16",
        ScalarType::U32 => "u32",
        ScalarType::U64 => "u64",
        ScalarType::U128 => "u128",
        ScalarType::Usize => "usize",
        ScalarType::I8 => "i8",
        ScalarType::I16 => "i16",
        ScalarType::I32 => "i32",
        ScalarType::I64 => "i64",
        ScalarType::I128 => "i128",
        ScalarType::Isize => "isize",
        ScalarType::F32 => "f32",
        ScalarType::F64 => "f64",
        _ => "non-runtime-scalar",
    }
}
const fn runtime_integer_ordinal(scalar: ScalarType) -> Option<u8> {
    Some(match scalar {
        ScalarType::U8 => 0,
        ScalarType::U16 => 1,
        ScalarType::U32 => 2,
        ScalarType::U64 => 3,
        ScalarType::U128 => 4,
        ScalarType::Usize => 5,
        ScalarType::I8 => 6,
        ScalarType::I16 => 7,
        ScalarType::I32 => 8,
        ScalarType::I64 => 9,
        ScalarType::I128 => 10,
        ScalarType::Isize => 11,
        _ => return None,
    })
}
const fn is_runtime_integer(scalar: ScalarType) -> bool {
    matches!(
        scalar,
        ScalarType::U8
            | ScalarType::U16
            | ScalarType::U32
            | ScalarType::U64
            | ScalarType::U128
            | ScalarType::Usize
            | ScalarType::I8
            | ScalarType::I16
            | ScalarType::I32
            | ScalarType::I64
            | ScalarType::I128
            | ScalarType::Isize
    )
}
fn parse_float_width(value: &str) -> Option<FloatWidth> {
    match value {
        "f32" => Some(FloatWidth::F32),
        "f64" => Some(FloatWidth::F64),
        _ => None,
    }
}
fn parse_scalar_name(value: &str) -> Option<ScalarType> {
    Some(match value {
        "u8" => ScalarType::U8,
        "u16" => ScalarType::U16,
        "u32" => ScalarType::U32,
        "u64" => ScalarType::U64,
        "u128" => ScalarType::U128,
        "usize" => ScalarType::Usize,
        "i8" => ScalarType::I8,
        "i16" => ScalarType::I16,
        "i32" => ScalarType::I32,
        "i64" => ScalarType::I64,
        "i128" => ScalarType::I128,
        "isize" => ScalarType::Isize,
        "f32" => ScalarType::F32,
        "f64" => ScalarType::F64,
        _ => return None,
    })
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PrimitiveRole {
    /// The trusted terminal leaf. Only its exact manifest-bound declaration
    /// identity may lower to the VM's non-fallthrough `Trap` instruction.
    Abort,
    /// One of the finite IEEE-754 leaves declared in the canonical runtime.
    /// It is structurally parameterized solely to keep the manifest protocol
    /// auditable; each selector still binds one exact declaration identity.
    Float(FloatPrimitive),
    /// The finite control leaf used by the standard library's conventional
    /// conditional combinator. It is polymorphic in its result and receives
    /// two zero-argument callables, so source spelling alone cannot become a
    /// branch primitive.
    BranchBool,
    /// The capability-free byte-length operation for immutable UTF-8 `Text`.
    /// It is deliberately bound to one standard-library declaration identity;
    /// a source function named `text_byte_len` never receives primitive
    /// authority merely by spelling.
    TextByteLen,
    /// Capability-free concatenation over immutable UTF-8 text values.
    TextConcat,
    /// Capability-free equality predicate with the G1 `u32` boolean ABI.
    TextEq,
    /// Checked conversion from a frozen byte sequence to UTF-8 text.
    TextFromUtf8Checked,
    /// Borrow-free frozen byte snapshot of a UTF-8 text value.
    TextAsBytes,
    /// Checked Unicode scalar construction from the G1 `u32` character ABI.
    CharFromU32Checked,
    /// Canonical Unicode scalar extraction to the G1 `u32` character ABI.
    CharToU32,
    BytesLen,
    BytesConcat,
    BytesGet,
    BytesSlice,
    BytesFromArrayMove,
    BytesToArray,
    BytesUtf8ValidUpTo,
    /// Unkeyed BLAKE3 over an immutable byte snapshot. Domain separation
    /// belongs to ordinary source code; this sealed leaf returns raw bytes.
    Blake3,
    U32CheckedAdd,
    U32CheckedSub,
    U32CheckedMul,
    U32CheckedDiv,
    U32CheckedRem,
    U32WrappingAdd,
    U32WrappingSub,
    U32WrappingMul,
    U32WrappingShl,
    U32WrappingShr,
    U32CheckedShl,
    U32CheckedShr,
    U32Eq,
    U32Lt,
    U32Le,
    U32ToUsize,
    UsizeToU32Checked,
    /// Exact generic declaration `__g1_int_checked_add<T>` in distributed std.
    /// Lowering may specialize it only after the frozen type argument is i64.
    IntCheckedAdd,
    /// Exact generic declaration `__g1_int_checked_div<T>` in distributed
    /// std. Division by zero is a checked arithmetic failure.
    IntCheckedDiv,
    /// Exact generic declaration `__g1_int_wrapping_add<T>` in distributed
    /// std. Its i64 specialization has wrapping, not checked, overflow.
    IntWrappingAdd,
    IntConvertCheckedToI64,
    IntConvertWrappingToI64,
    /// Exact generic declaration `__g1_int_convert_wrapping_to_u32<T>` in
    /// distributed std. Its frozen i64 specialization truncates two's-complement bits.
    IntConvertWrappingToU32,
    /// Exact generic declaration `__g1_int_convert_wrapping_to_usize<T>` in
    /// distributed std. Its frozen i64 specialization truncates two's-complement bits.
    IntConvertWrappingToUsize,
    /// Exact generic declaration `__g1_int_convert_wrapping_to_u8<T>` in
    /// distributed std. Its frozen i64 specialization truncates two's-complement bits.
    IntConvertWrappingToU8,
    /// Exact generic declaration `__g1_int_convert_wrapping_to_u16<T>` in
    /// distributed std. Its frozen i64 specialization truncates two's-complement bits.
    IntConvertWrappingToU16,
    IntConvertWrappingToI16,
    /// Exact generic declaration `__g1_int_wrapping_sub<T>` in distributed
    /// std. Its i64 specialization has wrapping, not checked, overflow.
    IntWrappingSub,
    /// Exact generic declaration `__g1_int_wrapping_mul<T>` in distributed
    /// std. Its i64 specialization has wrapping, not checked, overflow.
    IntWrappingMul,
    /// Exact generic declaration `__g1_int_wrapping_neg<T>` in distributed
    /// std. Its i64 specialization wraps two's-complement negation.
    IntWrappingNeg,
    /// Exact generic declaration `__g1_int_equal<T>` in distributed std.
    /// Its i64 specialization returns the canonical 0-or-1 u32 predicate.
    IntEqual,
    /// Exact generic declaration `__g1_int_less<T>` in distributed std.
    /// Its i64 specialization returns the canonical 0-or-1 u32 predicate.
    IntLess,
    /// Exact generic declaration `__g1_int_greater<T>` in distributed std.
    /// Its i64 specialization returns the canonical 0-or-1 u32 predicate.
    IntGreater,
    /// Exact generic declaration `__g1_int_bit_and<T>` in distributed std.
    /// Its frozen i64 specialization is a distinct bitwise VM operation.
    IntBitAnd,
    /// Exact generic declaration `__g1_int_bit_or<T>` in distributed std.
    /// Its frozen i64 specialization is a distinct bitwise VM operation.
    IntBitOr,
    /// Exact generic declaration `__g1_int_bit_xor<T>` in distributed std.
    /// Its frozen i64 specialization is a distinct bitwise VM operation.
    IntBitXor,
    /// Exact generic declaration `__g1_int_bit_not<T>` in distributed std.
    /// Its frozen i64 specialization is a distinct unary VM operation.
    IntBitNot,
    /// Exact generic declaration `__g1_int_shr<T>` in distributed std.
    /// Its frozen i64 specialization wraps the u32 shift count modulo 64.
    IntShr,
    /// Exact generic declaration `__g1_int_shl<T>` in distributed std. Its
    /// frozen specialization accepts an i64 value and a u32 wrapping count.
    IntShl,
    IntConvertCheckedToU32,
    IntConvertCheckedToUsize,
    /// Exact generic declaration `__g1_int_convert_checked_to_u8<T>` in
    /// distributed std. Its frozen i64 specialization rejects values outside
    /// the u8 range.
    IntConvertCheckedToU8,
    /// Exact generic declaration `__g1_int_convert_checked_to_u16<T>` in
    /// distributed std. Its frozen i64 specialization rejects values outside
    /// the u16 range.
    IntConvertCheckedToU16,
    IntConvertCheckedToI16,
    /// Exact generic declaration `__g1_int_convert_checked_to_i32<T>` in
    /// distributed std. Its frozen i64 specialization rejects values outside
    /// the i32 range.
    IntConvertCheckedToI32,
    /// Exact generic declaration `__g1_int_convert_wrapping_to_i32<T>` in
    /// distributed std. Its frozen i64 specialization retains low
    /// two's-complement bits.
    IntConvertWrappingToI32,
    IntConvertCheckedToI8,
    IntConvertWrappingToI8,
    IntConvertCheckedToU64,
    IntConvertWrappingToU64,
    IntConvertCheckedToIsize,
    IntConvertWrappingToIsize,
    IntConvertCheckedToU128,
    IntConvertWrappingToU128,
    IntConvertCheckedToI128,
    IntConvertWrappingToI128,
    /// Declaration-owned generic Array runtime leaves. These are deliberately
    /// separate from syntactic array literals: the manifest binds the storage
    /// operations to the trusted distributed standard library identity.
    ArrayNew,
    ArrayLen,
    /// Validate the existing `Array<u8>` storage for `String::from_utf8`
    /// without introducing a public compiler-owned byte-buffer type.
    ArrayUtf8ValidUpTo,
    ArrayPushUtf8Char,
    /// Copy a verified range from a shared Array into a unique Array. This
    /// stays private to `std`; public `Vec::extend_from_slice` and
    /// `String::push_str` own the safe API and its duplication bound.
    ArrayExtendFromSlice,
    /// Private storage leaves. `std::Vec` owns their checked public API.
    ArrayInsertMove,
    ArrayRemoveMove,
    ArrayAppendMove,
    ArrayInsertFromSlice,
    ArrayInsertUtf8FromSlice,
    ArrayTruncateDiscard,
    ArrayReverseMove,
    ArraySplitOffMove,
    /// Consume a uniquely borrowed Array window and return two verifier-
    /// bounded, disjoint unique windows. This is private infrastructure for
    /// the standard library's `SliceMut::split_at`.
    ArraySplitBorrowUnique,
    ArrayPopUtf8Char,
    ArrayUtf8CharAt,
    ArrayGetCopy,
    ArrayGetMove,
    ArrayGetBorrowShared,
    ArrayGetBorrowUnique,
    ArraySetMove,
    ArrayEmpty,
    ArrayPushMove,
    ArrayPopMove,
    ArrayCapacity,
    ArrayReserve,
    ArrayFinishDrained,
    /// Private standard-library leaves over compiler-emitted immutable data.
    /// They are manifest-bound and remain inaccessible to ordinary packages.
    StaticLen,
    StaticSubslice,
    StaticGetShared,
    /// Reinterpret compiler-emitted immutable UTF-8 data as an immutable
    /// byte array for the standard library's ordinary `Slice` wrapper.
    /// This is a private bridge leaf; ordinary source cannot name its type.
    StaticAsArray,
    /// Raw byte specialization of the same private static-array bridge.
    /// The public result is still `Slice<'static, u8>`; this distinct
    /// manifest identity prevents raw assets from being accepted by UTF-8
    /// operations such as `Str` construction.
    StaticRawAsArray,
    /// General raw-memory mechanisms. Collection policy remains in source.
    Memory(MemoryPrimitive),
}

impl PrimitiveRole {
    fn validate(self) -> Result<(), ManifestError> {
        if matches!(self, Self::Float(primitive) if !primitive.is_valid()) {
            Err(ManifestError::InvalidRole(self))
        } else {
            Ok(())
        }
    }

    /// Stable protocol tag used by request and manifest fingerprints. The
    /// float family occupies 69..=146. Checked division was incorrectly
    /// appended to the legacy list at tag 69; its corrected tag is 182.
    /// Every other existing tag remains unchanged.
    pub(crate) fn stable_tag(self) -> u8 {
        if let Self::Memory(primitive) = self {
            return 183 + primitive.ordinal();
        }
        if let Self::Float(primitive) = self {
            return 69 + primitive.ordinal();
        }
        match self {
            Self::Abort => return 147,
            Self::ArrayNew => return 148,
            Self::ArrayLen => return 149,
            Self::ArrayUtf8ValidUpTo => return 167,
            Self::ArrayPushUtf8Char => return 168,
            Self::ArrayExtendFromSlice => return 169,
            Self::ArrayInsertMove => return 170,
            Self::ArrayRemoveMove => return 171,
            Self::ArrayAppendMove => return 172,
            Self::ArrayInsertFromSlice => return 173,
            Self::ArrayInsertUtf8FromSlice => return 174,
            Self::ArrayTruncateDiscard => return 175,
            Self::ArrayReverseMove => return 176,
            Self::ArraySplitOffMove => return 177,
            Self::ArraySplitBorrowUnique => return 180,
            Self::ArrayPopUtf8Char => return 178,
            Self::ArrayUtf8CharAt => return 179,
            Self::ArrayGetCopy => return 150,
            Self::ArrayGetMove => return 151,
            Self::ArrayGetBorrowShared => return 152,
            Self::ArrayGetBorrowUnique => return 153,
            Self::ArraySetMove => return 154,
            Self::ArrayEmpty => return 155,
            Self::ArrayPushMove => return 156,
            Self::ArrayPopMove => return 157,
            Self::ArrayCapacity => return 158,
            Self::ArrayReserve => return 159,
            Self::ArrayFinishDrained => return 160,
            Self::IntWrappingNeg => return 161,
            Self::Blake3 => return 162,
            Self::StaticLen => return 163,
            Self::StaticSubslice => return 164,
            Self::StaticGetShared => return 165,
            Self::StaticAsArray => return 166,
            Self::StaticRawAsArray => return 181,
            Self::IntCheckedDiv => return 182,
            _ => {}
        }
        const LEGACY: [&str; 69] = [
            "branch-bool",
            "text-byte-len",
            "text-concat",
            "text-eq",
            "text-from-utf8-checked",
            "text-as-bytes",
            "char-from-u32-checked",
            "char-to-u32",
            "bytes-len",
            "bytes-concat",
            "bytes-get",
            "bytes-slice",
            "bytes-from-array-move",
            "bytes-to-array",
            "bytes-utf8-valid-up-to",
            "u32-checked-add",
            "u32-checked-sub",
            "u32-checked-mul",
            "u32-checked-div",
            "u32-checked-rem",
            "u32-wrapping-add",
            "u32-wrapping-sub",
            "u32-wrapping-mul",
            "u32-wrapping-shl",
            "u32-wrapping-shr",
            "u32-checked-shl",
            "u32-checked-shr",
            "u32-eq",
            "u32-lt",
            "u32-le",
            "u32-to-usize",
            "usize-to-u32-checked",
            "int-checked-add",
            "int-wrapping-add",
            "int-equal",
            "int-wrapping-sub",
            "int-wrapping-mul",
            "int-bit-and",
            "int-less",
            "int-greater",
            "int-bit-or",
            "int-bit-xor",
            "int-bit-not",
            "int-shl",
            "int-shr",
            "int-convert-checked-to-i64",
            "int-convert-wrapping-to-i64",
            "int-convert-checked-to-u32",
            "int-convert-wrapping-to-u32",
            "int-convert-checked-to-usize",
            "int-convert-wrapping-to-usize",
            "int-convert-checked-to-u8",
            "int-convert-wrapping-to-u8",
            "int-convert-checked-to-u16",
            "int-convert-wrapping-to-u16",
            "int-convert-checked-to-i16",
            "int-convert-wrapping-to-i16",
            "int-convert-checked-to-i32",
            "int-convert-wrapping-to-i32",
            "int-convert-checked-to-i8",
            "int-convert-wrapping-to-i8",
            "int-convert-checked-to-u64",
            "int-convert-wrapping-to-u64",
            "int-convert-checked-to-isize",
            "int-convert-wrapping-to-isize",
            "int-convert-checked-to-u128",
            "int-convert-wrapping-to-u128",
            "int-convert-checked-to-i128",
            "int-convert-wrapping-to-i128",
        ];
        LEGACY
            .iter()
            .position(|name| *name == self.selector_name())
            .expect("every legacy primitive has a stable tag") as u8
    }

    pub(crate) const fn is_float(self) -> bool {
        matches!(self, Self::Float(_))
    }

    /// The closed ABI of one concrete materialization of a generic integer
    /// runtime leaf. Both MIR validation and VM verification consume this
    /// authority so a new manifest selector cannot make their contracts
    /// diverge.
    pub(crate) fn integer_scalar_signature(
        self,
        scalar: ScalarType,
    ) -> Option<(Vec<ScalarType>, ScalarType)> {
        if !matches!(
            scalar,
            ScalarType::U8
                | ScalarType::U16
                | ScalarType::U32
                | ScalarType::U64
                | ScalarType::U128
                | ScalarType::Usize
                | ScalarType::I8
                | ScalarType::I16
                | ScalarType::I32
                | ScalarType::I64
                | ScalarType::I128
                | ScalarType::Isize
        ) {
            return None;
        }
        let binary = vec![scalar, scalar];
        Some(match self {
            Self::IntCheckedAdd
            | Self::IntCheckedDiv
            | Self::IntWrappingAdd
            | Self::IntWrappingSub
            | Self::IntWrappingMul
            | Self::IntBitAnd
            | Self::IntBitOr
            | Self::IntBitXor => (binary, scalar),
            Self::IntEqual | Self::IntLess | Self::IntGreater => (binary, ScalarType::U32),
            Self::IntBitNot | Self::IntWrappingNeg => (vec![scalar], scalar),
            Self::IntShl | Self::IntShr => (vec![scalar, ScalarType::U32], scalar),
            Self::IntConvertCheckedToI64 | Self::IntConvertWrappingToI64 => {
                (vec![scalar], ScalarType::I64)
            }
            Self::IntConvertCheckedToU32 | Self::IntConvertWrappingToU32 => {
                (vec![scalar], ScalarType::U32)
            }
            Self::IntConvertCheckedToUsize | Self::IntConvertWrappingToUsize => {
                (vec![scalar], ScalarType::Usize)
            }
            Self::IntConvertCheckedToU8 | Self::IntConvertWrappingToU8 => {
                (vec![scalar], ScalarType::U8)
            }
            Self::IntConvertCheckedToU16 | Self::IntConvertWrappingToU16 => {
                (vec![scalar], ScalarType::U16)
            }
            Self::IntConvertCheckedToI16 | Self::IntConvertWrappingToI16 => {
                (vec![scalar], ScalarType::I16)
            }
            Self::IntConvertCheckedToI32 | Self::IntConvertWrappingToI32 => {
                (vec![scalar], ScalarType::I32)
            }
            Self::IntConvertCheckedToI8 | Self::IntConvertWrappingToI8 => {
                (vec![scalar], ScalarType::I8)
            }
            Self::IntConvertCheckedToU64 | Self::IntConvertWrappingToU64 => {
                (vec![scalar], ScalarType::U64)
            }
            Self::IntConvertCheckedToIsize | Self::IntConvertWrappingToIsize => {
                (vec![scalar], ScalarType::Isize)
            }
            Self::IntConvertCheckedToU128 | Self::IntConvertWrappingToU128 => {
                (vec![scalar], ScalarType::U128)
            }
            Self::IntConvertCheckedToI128 | Self::IntConvertWrappingToI128 => {
                (vec![scalar], ScalarType::I128)
            }
            _ => return None,
        })
    }

    pub fn selector_name(self) -> String {
        if let Self::Memory(primitive) = self {
            return primitive.selector_name().into();
        }
        if let Self::Float(primitive) = self {
            return primitive.selector_name();
        }
        (match self {
            Self::BranchBool => "branch-bool",
            Self::TextByteLen => "text-byte-len",
            Self::TextConcat => "text-concat",
            Self::TextEq => "text-eq",
            Self::TextFromUtf8Checked => "text-from-utf8-checked",
            Self::TextAsBytes => "text-as-bytes",
            Self::CharFromU32Checked => "char-from-u32-checked",
            Self::CharToU32 => "char-to-u32",
            Self::BytesLen => "bytes-len",
            Self::BytesConcat => "bytes-concat",
            Self::BytesGet => "bytes-get",
            Self::BytesSlice => "bytes-slice",
            Self::BytesFromArrayMove => "bytes-from-array-move",
            Self::BytesToArray => "bytes-to-array",
            Self::BytesUtf8ValidUpTo => "bytes-utf8-valid-up-to",
            Self::Blake3 => "blake3",
            Self::U32CheckedAdd => "u32-checked-add",
            Self::U32CheckedSub => "u32-checked-sub",
            Self::U32CheckedMul => "u32-checked-mul",
            Self::U32CheckedDiv => "u32-checked-div",
            Self::U32CheckedRem => "u32-checked-rem",
            Self::U32WrappingAdd => "u32-wrapping-add",
            Self::U32WrappingSub => "u32-wrapping-sub",
            Self::U32WrappingMul => "u32-wrapping-mul",
            Self::U32WrappingShl => "u32-wrapping-shl",
            Self::U32WrappingShr => "u32-wrapping-shr",
            Self::U32CheckedShl => "u32-checked-shl",
            Self::U32CheckedShr => "u32-checked-shr",
            Self::U32Eq => "u32-eq",
            Self::U32Lt => "u32-lt",
            Self::U32Le => "u32-le",
            Self::U32ToUsize => "u32-to-usize",
            Self::UsizeToU32Checked => "usize-to-u32-checked",
            Self::IntCheckedAdd => "int-checked-add",
            Self::IntCheckedDiv => "int-checked-div",
            Self::IntWrappingAdd => "int-wrapping-add",
            Self::IntConvertCheckedToI64 => "int-convert-checked-to-i64",
            Self::IntConvertWrappingToI64 => "int-convert-wrapping-to-i64",
            Self::IntConvertWrappingToU32 => "int-convert-wrapping-to-u32",
            Self::IntConvertWrappingToUsize => "int-convert-wrapping-to-usize",
            Self::IntConvertWrappingToU8 => "int-convert-wrapping-to-u8",
            Self::IntConvertWrappingToU16 => "int-convert-wrapping-to-u16",
            Self::IntConvertWrappingToI16 => "int-convert-wrapping-to-i16",
            Self::IntWrappingSub => "int-wrapping-sub",
            Self::IntWrappingMul => "int-wrapping-mul",
            Self::IntWrappingNeg => "int-wrapping-neg",
            Self::IntEqual => "int-equal",
            Self::IntLess => "int-less",
            Self::IntGreater => "int-greater",
            Self::IntBitAnd => "int-bit-and",
            Self::IntBitOr => "int-bit-or",
            Self::IntBitXor => "int-bit-xor",
            Self::IntBitNot => "int-bit-not",
            Self::IntShr => "int-shr",
            Self::IntShl => "int-shl",
            Self::IntConvertCheckedToU32 => "int-convert-checked-to-u32",
            Self::IntConvertCheckedToUsize => "int-convert-checked-to-usize",
            Self::IntConvertCheckedToU8 => "int-convert-checked-to-u8",
            Self::IntConvertCheckedToU16 => "int-convert-checked-to-u16",
            Self::IntConvertCheckedToI16 => "int-convert-checked-to-i16",
            Self::IntConvertCheckedToI32 => "int-convert-checked-to-i32",
            Self::IntConvertWrappingToI32 => "int-convert-wrapping-to-i32",
            Self::IntConvertCheckedToI8 => "int-convert-checked-to-i8",
            Self::IntConvertWrappingToI8 => "int-convert-wrapping-to-i8",
            Self::IntConvertCheckedToU64 => "int-convert-checked-to-u64",
            Self::IntConvertWrappingToU64 => "int-convert-wrapping-to-u64",
            Self::IntConvertCheckedToIsize => "int-convert-checked-to-isize",
            Self::IntConvertWrappingToIsize => "int-convert-wrapping-to-isize",
            Self::IntConvertCheckedToU128 => "int-convert-checked-to-u128",
            Self::IntConvertWrappingToU128 => "int-convert-wrapping-to-u128",
            Self::IntConvertCheckedToI128 => "int-convert-checked-to-i128",
            Self::IntConvertWrappingToI128 => "int-convert-wrapping-to-i128",
            Self::Abort => "abort",
            Self::ArrayNew => "array-new",
            Self::ArrayLen => "array-len",
            Self::ArrayUtf8ValidUpTo => "array-utf8-valid-up-to",
            Self::ArrayPushUtf8Char => "array-push-utf8-char",
            Self::ArrayExtendFromSlice => "array-extend-from-slice",
            Self::ArrayInsertMove => "array-insert-move",
            Self::ArrayRemoveMove => "array-remove-move",
            Self::ArrayAppendMove => "array-append-move",
            Self::ArrayInsertFromSlice => "array-insert-from-slice",
            Self::ArrayInsertUtf8FromSlice => "array-insert-utf8-from-slice",
            Self::ArrayTruncateDiscard => "array-truncate-discard",
            Self::ArrayReverseMove => "array-reverse-move",
            Self::ArraySplitOffMove => "array-split-off-move",
            Self::ArraySplitBorrowUnique => "array-split-borrow-unique",
            Self::ArrayPopUtf8Char => "array-pop-utf8-char",
            Self::ArrayUtf8CharAt => "array-utf8-char-at",
            Self::ArrayGetCopy => "array-get-copy",
            Self::ArrayGetMove => "array-get-move",
            Self::ArrayGetBorrowShared => "array-get-borrow-shared",
            Self::ArrayGetBorrowUnique => "array-get-borrow-unique",
            Self::ArraySetMove => "array-set-move",
            Self::ArrayEmpty => "array-empty",
            Self::ArrayPushMove => "array-push-move",
            Self::ArrayPopMove => "array-pop-move",
            Self::ArrayCapacity => "array-capacity",
            Self::ArrayReserve => "array-reserve",
            Self::ArrayFinishDrained => "array-finish-drained",
            Self::StaticLen => "static-len",
            Self::StaticSubslice => "static-subslice",
            Self::StaticGetShared => "static-get-shared",
            Self::StaticAsArray => "static-as-array",
            Self::StaticRawAsArray => "static-raw-as-array",
            Self::Float(_) | Self::Memory(_) => unreachable!("handled before the static selector table"),
        })
        .to_owned()
    }

    pub fn parse_selector_name(value: impl AsRef<str>) -> Option<Self> {
        if let Some(primitive) = MemoryPrimitive::ALL.into_iter()
            .find(|primitive| primitive.selector_name() == value.as_ref()) {
            return Some(Self::Memory(primitive));
        }
        let value = value.as_ref();
        if let Some(primitive) = FloatPrimitive::parse_selector_name(value) {
            return Some(Self::Float(primitive));
        }
        Some(match value {
            "abort" => Self::Abort,
            "branch-bool" => Self::BranchBool,
            "text-byte-len" => Self::TextByteLen,
            "text-concat" => Self::TextConcat,
            "text-eq" => Self::TextEq,
            "text-from-utf8-checked" => Self::TextFromUtf8Checked,
            "text-as-bytes" => Self::TextAsBytes,
            "char-from-u32-checked" => Self::CharFromU32Checked,
            "char-to-u32" => Self::CharToU32,
            "bytes-len" => Self::BytesLen,
            "bytes-concat" => Self::BytesConcat,
            "bytes-get" => Self::BytesGet,
            "bytes-slice" => Self::BytesSlice,
            "bytes-from-array-move" => Self::BytesFromArrayMove,
            "bytes-to-array" => Self::BytesToArray,
            "bytes-utf8-valid-up-to" => Self::BytesUtf8ValidUpTo,
            "blake3" => Self::Blake3,
            "u32-checked-add" => Self::U32CheckedAdd,
            "u32-checked-sub" => Self::U32CheckedSub,
            "u32-checked-mul" => Self::U32CheckedMul,
            "u32-checked-div" => Self::U32CheckedDiv,
            "u32-checked-rem" => Self::U32CheckedRem,
            "u32-wrapping-add" => Self::U32WrappingAdd,
            "u32-wrapping-sub" => Self::U32WrappingSub,
            "u32-wrapping-mul" => Self::U32WrappingMul,
            "u32-wrapping-shl" => Self::U32WrappingShl,
            "u32-wrapping-shr" => Self::U32WrappingShr,
            "u32-checked-shl" => Self::U32CheckedShl,
            "u32-checked-shr" => Self::U32CheckedShr,
            "u32-eq" => Self::U32Eq,
            "u32-lt" => Self::U32Lt,
            "u32-le" => Self::U32Le,
            "u32-to-usize" => Self::U32ToUsize,
            "usize-to-u32-checked" => Self::UsizeToU32Checked,
            "int-checked-add" => Self::IntCheckedAdd,
            "int-checked-div" => Self::IntCheckedDiv,
            "int-wrapping-add" => Self::IntWrappingAdd,
            "int-convert-checked-to-i64" => Self::IntConvertCheckedToI64,
            "int-convert-wrapping-to-i64" => Self::IntConvertWrappingToI64,
            "int-convert-wrapping-to-u32" => Self::IntConvertWrappingToU32,
            "int-convert-wrapping-to-usize" => Self::IntConvertWrappingToUsize,
            "int-convert-wrapping-to-u8" => Self::IntConvertWrappingToU8,
            "int-convert-wrapping-to-u16" => Self::IntConvertWrappingToU16,
            "int-convert-wrapping-to-i16" => Self::IntConvertWrappingToI16,
            "int-wrapping-sub" => Self::IntWrappingSub,
            "int-wrapping-mul" => Self::IntWrappingMul,
            "int-wrapping-neg" => Self::IntWrappingNeg,
            "int-equal" => Self::IntEqual,
            "int-less" => Self::IntLess,
            "int-greater" => Self::IntGreater,
            "int-bit-and" => Self::IntBitAnd,
            "int-bit-or" => Self::IntBitOr,
            "int-bit-xor" => Self::IntBitXor,
            "int-bit-not" => Self::IntBitNot,
            "int-shr" => Self::IntShr,
            "int-shl" => Self::IntShl,
            "int-convert-checked-to-u32" => Self::IntConvertCheckedToU32,
            "int-convert-checked-to-usize" => Self::IntConvertCheckedToUsize,
            "int-convert-checked-to-u8" => Self::IntConvertCheckedToU8,
            "int-convert-checked-to-u16" => Self::IntConvertCheckedToU16,
            "int-convert-checked-to-i16" => Self::IntConvertCheckedToI16,
            "int-convert-checked-to-i32" => Self::IntConvertCheckedToI32,
            "int-convert-wrapping-to-i32" => Self::IntConvertWrappingToI32,
            "int-convert-checked-to-i8" => Self::IntConvertCheckedToI8,
            "int-convert-wrapping-to-i8" => Self::IntConvertWrappingToI8,
            "int-convert-checked-to-u64" => Self::IntConvertCheckedToU64,
            "int-convert-wrapping-to-u64" => Self::IntConvertWrappingToU64,
            "int-convert-checked-to-isize" => Self::IntConvertCheckedToIsize,
            "int-convert-wrapping-to-isize" => Self::IntConvertWrappingToIsize,
            "int-convert-checked-to-u128" => Self::IntConvertCheckedToU128,
            "int-convert-wrapping-to-u128" => Self::IntConvertWrappingToU128,
            "int-convert-checked-to-i128" => Self::IntConvertCheckedToI128,
            "int-convert-wrapping-to-i128" => Self::IntConvertWrappingToI128,
            "array-new" => Self::ArrayNew,
            "array-len" => Self::ArrayLen,
            "array-utf8-valid-up-to" => Self::ArrayUtf8ValidUpTo,
            "array-push-utf8-char" => Self::ArrayPushUtf8Char,
            "array-extend-from-slice" => Self::ArrayExtendFromSlice,
            "array-insert-move" => Self::ArrayInsertMove,
            "array-remove-move" => Self::ArrayRemoveMove,
            "array-append-move" => Self::ArrayAppendMove,
            "array-insert-from-slice" => Self::ArrayInsertFromSlice,
            "array-insert-utf8-from-slice" => Self::ArrayInsertUtf8FromSlice,
            "array-truncate-discard" => Self::ArrayTruncateDiscard,
            "array-reverse-move" => Self::ArrayReverseMove,
            "array-split-off-move" => Self::ArraySplitOffMove,
            "array-split-borrow-unique" => Self::ArraySplitBorrowUnique,
            "array-pop-utf8-char" => Self::ArrayPopUtf8Char,
            "array-utf8-char-at" => Self::ArrayUtf8CharAt,
            "array-get-copy" => Self::ArrayGetCopy,
            "array-get-move" => Self::ArrayGetMove,
            "array-get-borrow-shared" => Self::ArrayGetBorrowShared,
            "array-get-borrow-unique" => Self::ArrayGetBorrowUnique,
            "array-set-move" => Self::ArraySetMove,
            "array-empty" => Self::ArrayEmpty,
            "array-push-move" => Self::ArrayPushMove,
            "array-pop-move" => Self::ArrayPopMove,
            "array-capacity" => Self::ArrayCapacity,
            "array-reserve" => Self::ArrayReserve,
            "array-finish-drained" => Self::ArrayFinishDrained,
            "static-len" => Self::StaticLen,
            "static-subslice" => Self::StaticSubslice,
            "static-get-shared" => Self::StaticGetShared,
            "static-as-array" => Self::StaticAsArray,
            "static-raw-as-array" => Self::StaticRawAsArray,
            _ => return None,
        })
    }
}
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PrimitiveSelector {
    pub role: PrimitiveRole,
    pub module_path: String,
    pub name: String,
}

/// An exact source declaration admitted as a host boundary by the trusted
/// runtime manifest.  Unlike a source `host` declaration, the canonical
/// self-host source materialized by an earlier seed carries an opaque `{ () }`
/// placeholder body; this selector restores the same capability-bound
/// identity without inferring authority from its spelling.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct HostImportSelector {
    pub module_path: String,
    pub name: String,
    pub capability: String,
    pub symbol: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeManifestInput {
    pub standard_library: PackageKey,
    pub selectors: Vec<PrimitiveSelector>,
    pub host_imports: Vec<HostImportSelector>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrustedRuntimeManifest {
    pub standard_library: PackageKey,
    pub primitives: BTreeMap<PrimitiveRole, DefKey>,
    /// Frozen source declaration identities that lower directly to host ABI
    /// calls, rather than elaborating their seed-only placeholder bodies.
    pub host_imports: BTreeMap<DefKey, HostImport>,
    pub digest: Digest,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ManifestError {
    InvalidRole(PrimitiveRole),
    DuplicateRole(PrimitiveRole),
    MissingDeclaration {
        module_path: String,
        name: String,
    },
    AmbiguousDeclaration {
        module_path: String,
        name: String,
    },
    DuplicateHostImport {
        module_path: String,
        name: String,
    },
    InvalidHostImport {
        module_path: String,
        name: String,
    },
    ConflictingRuntimeBinding {
        definition: DefKey,
    },
    IncompatibleSignature {
        role: PrimitiveRole,
        definition: DefKey,
    },
    IncompatibleHostImport {
        definition: DefKey,
    },
}

impl RuntimeManifestInput {
    pub fn canonicalize(&mut self) -> Result<(), ManifestError> {
        self.selectors.sort();
        for selector in &self.selectors {
            selector.role.validate()?;
        }
        for pair in self.selectors.windows(2) {
            if pair[0].role == pair[1].role {
                return Err(ManifestError::DuplicateRole(pair[0].role));
            }
        }
        self.host_imports.sort();
        for selector in &self.host_imports {
            if selector.module_path.is_empty()
                || selector.name.is_empty()
                || selector.capability.is_empty()
                || selector.symbol.is_empty()
                || selector.capability.contains('*')
                || selector.capability.chars().any(char::is_whitespace)
            {
                return Err(ManifestError::InvalidHostImport {
                    module_path: selector.module_path.clone(),
                    name: selector.name.clone(),
                });
            }
        }
        for pair in self.host_imports.windows(2) {
            if pair[0].module_path == pair[1].module_path && pair[0].name == pair[1].name {
                return Err(ManifestError::DuplicateHostImport {
                    module_path: pair[0].module_path.clone(),
                    name: pair[0].name.clone(),
                });
            }
        }
        Ok(())
    }
    pub fn bind(
        &self,
        interfaces: impl IntoIterator<Item = PackageInterface>,
        signatures: &ElaboratedInterface,
    ) -> Result<TrustedRuntimeManifest, ManifestError> {
        let interfaces = interfaces
            .into_iter()
            .filter(|interface| interface.package == self.standard_library)
            .collect::<Vec<_>>();
        let mut selectors = BTreeMap::new();
        for selector in &self.selectors {
            selector.role.validate()?;
            if selectors.insert(selector.role, selector).is_some() {
                return Err(ManifestError::DuplicateRole(selector.role));
            }
        }
        let mut primitives = BTreeMap::new();
        let mut host_imports = BTreeMap::new();
        // A manifest is an exact finite grant set, rather than a statement
        // that every primitive known to this compiler generation is present.
        // A bootstrap world can therefore expose only the leaves supplied by
        // its standard-library revision; calls to an unbound leaf remain
        // ordinary source calls and its opaque placeholder body is rejected.
        for (role, selector) in selectors {
            let candidates = interfaces
                .iter()
                .filter(|interface| interface.module.path == selector.module_path)
                .flat_map(|interface| interface.definitions.iter())
                .filter(|definition| definition.name.as_deref() == Some(selector.name.as_str()))
                .collect::<Vec<_>>();
            let definition = match candidates.as_slice() {
                [] => {
                    return Err(ManifestError::MissingDeclaration {
                        module_path: selector.module_path.clone(),
                        name: selector.name.clone(),
                    });
                }
                [definition] => *definition,
                _ => {
                    return Err(ManifestError::AmbiguousDeclaration {
                        module_path: selector.module_path.clone(),
                        name: selector.name.clone(),
                    });
                }
            };
            // Runtime authority is a host-supplied binding to one exact
            // declaration in the distinguished standard-library package.
            // It is intentionally independent of ordinary source visibility:
            // canonical layer-1 leaves are private implementation details,
            // while downstream callers reach public wrappers.  Requiring
            // `pub` here would make the bootstrap source unable to bind its
            // own trusted leaves without incorrectly exporting them.
            let Some(ElaboratedHeader::Callable(signature)) =
                signatures.definitions.get(&definition.key)
            else {
                return Err(ManifestError::IncompatibleSignature {
                    role,
                    definition: definition.key,
                });
            };
            if signature != &expected_signature(role) {
                return Err(ManifestError::IncompatibleSignature {
                    role,
                    definition: definition.key,
                });
            }
            primitives.insert(role, definition.key);
        }
        for selector in &self.host_imports {
            let candidates = interfaces
                .iter()
                .filter(|interface| interface.module.path == selector.module_path)
                .flat_map(|interface| interface.definitions.iter())
                .filter(|definition| definition.name.as_deref() == Some(selector.name.as_str()))
                .collect::<Vec<_>>();
            let definition = match candidates.as_slice() {
                [] => {
                    return Err(ManifestError::MissingDeclaration {
                        module_path: selector.module_path.clone(),
                        name: selector.name.clone(),
                    });
                }
                [definition] => *definition,
                _ => {
                    return Err(ManifestError::AmbiguousDeclaration {
                        module_path: selector.module_path.clone(),
                        name: selector.name.clone(),
                    });
                }
            };
            if !matches!(
                signatures.definitions.get(&definition.key),
                Some(ElaboratedHeader::Callable(_))
            ) {
                return Err(ManifestError::IncompatibleHostImport {
                    definition: definition.key,
                });
            }
            if primitives
                .values()
                .any(|primitive| primitive == &definition.key)
                || host_imports.contains_key(&definition.key)
                // A source `host CAP fn` is already an exact frozen boundary;
                // a runtime manifest may not replace its capability or ABI
                // symbol by selecting the same declaration a second way.
                || signatures.host_imports.contains_key(&definition.key)
            {
                return Err(ManifestError::ConflictingRuntimeBinding {
                    definition: definition.key,
                });
            }
            host_imports.insert(
                definition.key,
                HostImport {
                    capability: selector.capability.clone(),
                    symbol: selector.symbol.clone(),
                },
            );
        }
        Ok(TrustedRuntimeManifest {
            standard_library: self.standard_library.clone(),
            digest: manifest_digest(&self.standard_library, &primitives, &host_imports),
            primitives,
            host_imports,
        })
    }
}
fn expected_signature(role: PrimitiveRole) -> crate::CallableSignature {
    if let PrimitiveRole::Memory(primitive) = role {
        return primitive.signature();
    }
    if let PrimitiveRole::Float(primitive) = role {
        return expected_float_signature(primitive);
    }
    match role {
        PrimitiveRole::Abort => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![],
            result: Type::Never,
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::BranchBool => {
            let result = Type::Generic(0);
            let thunk = Type::Callable {
                safety: crate::Safety::Safe,
                lifetime_binders: 0,
                parameters: vec![],
                result: Box::new(result.clone()),
                effects: EffectRow::empty(),
                invocation: Quantity::ONCE,
            };
            crate::CallableSignature {
                safety: crate::Safety::Safe,
                generics: 1,
                generic_kinds: vec![crate::GenericKind::Type],
                parameters: vec![Type::Scalar(ScalarType::Bool), thunk.clone(), thunk],
                result,
                effects: EffectRow::empty(),
                invocation: Quantity::ONCE,
                where_bounds: vec![],
                where_associated_type_bindings: vec![],
                where_associated_effect_bindings: vec![],
            }
        }
        PrimitiveRole::TextByteLen => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::Text)],
            result: Type::Scalar(ScalarType::Usize),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::TextConcat => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![
                Type::Scalar(ScalarType::Text),
                Type::Scalar(ScalarType::Text),
            ],
            result: Type::Scalar(ScalarType::Text),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::TextEq => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![
                Type::Scalar(ScalarType::Text),
                Type::Scalar(ScalarType::Text),
            ],
            result: Type::Scalar(ScalarType::U32),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::TextFromUtf8Checked => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::Bytes)],
            result: Type::Scalar(ScalarType::Text),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::TextAsBytes => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::Text)],
            result: Type::Scalar(ScalarType::Bytes),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::CharFromU32Checked => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::U32)],
            result: Type::Scalar(ScalarType::Char),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::CharToU32 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::Char)],
            result: Type::Scalar(ScalarType::U32),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::BytesLen | PrimitiveRole::BytesUtf8ValidUpTo => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::Bytes)],
            result: Type::Scalar(ScalarType::Usize),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::Blake3 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::Bytes)],
            result: Type::Scalar(ScalarType::Bytes),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::BytesConcat => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![
                Type::Scalar(ScalarType::Bytes),
                Type::Scalar(ScalarType::Bytes),
            ],
            result: Type::Scalar(ScalarType::Bytes),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::BytesGet => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![
                Type::Scalar(ScalarType::Bytes),
                Type::Scalar(ScalarType::Usize),
            ],
            result: Type::Scalar(ScalarType::U8),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::BytesSlice => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![
                Type::Scalar(ScalarType::Bytes),
                Type::Scalar(ScalarType::Usize),
                Type::Scalar(ScalarType::Usize),
            ],
            result: Type::Scalar(ScalarType::Bytes),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::BytesFromArrayMove => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Array(Box::new(Type::Scalar(ScalarType::U8)))],
            result: Type::Scalar(ScalarType::Bytes),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::BytesToArray => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::Bytes)],
            result: Type::Array(Box::new(Type::Scalar(ScalarType::U8))),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::U32CheckedAdd
        | PrimitiveRole::U32CheckedSub
        | PrimitiveRole::U32CheckedMul
        | PrimitiveRole::U32CheckedDiv
        | PrimitiveRole::U32CheckedRem
        | PrimitiveRole::U32WrappingAdd
        | PrimitiveRole::U32WrappingSub
        | PrimitiveRole::U32WrappingMul
        | PrimitiveRole::U32WrappingShl
        | PrimitiveRole::U32WrappingShr
        | PrimitiveRole::U32CheckedShl
        | PrimitiveRole::U32CheckedShr => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::U32), Type::Scalar(ScalarType::U32)],
            result: Type::Scalar(ScalarType::U32),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::U32Eq | PrimitiveRole::U32Lt | PrimitiveRole::U32Le => {
            crate::CallableSignature {
                safety: crate::Safety::Safe,
                generics: 0,
                generic_kinds: vec![],
                parameters: vec![Type::Scalar(ScalarType::U32), Type::Scalar(ScalarType::U32)],
                result: Type::Scalar(ScalarType::Bool),
                effects: EffectRow::empty(),
                invocation: Quantity::ONCE,
                where_bounds: vec![],
                where_associated_type_bindings: vec![],
                where_associated_effect_bindings: vec![],
            }
        }
        PrimitiveRole::U32ToUsize => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::U32)],
            result: Type::Scalar(ScalarType::Usize),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::UsizeToU32Checked => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::Usize)],
            result: Type::Scalar(ScalarType::U32),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntCheckedAdd
        | PrimitiveRole::IntCheckedDiv
        | PrimitiveRole::IntWrappingAdd
        | PrimitiveRole::IntWrappingSub
        | PrimitiveRole::IntWrappingMul
        | PrimitiveRole::IntBitAnd
        | PrimitiveRole::IntBitOr
        | PrimitiveRole::IntBitXor => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0), Type::Generic(0)],
            result: Type::Generic(0),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntWrappingNeg => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Generic(0),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertCheckedToI64 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::I64),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertWrappingToI64 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::I64),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertCheckedToU32 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::U32),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertWrappingToU32 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::U32),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertCheckedToUsize => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::Usize),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertCheckedToU8 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::U8),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertCheckedToU16 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::U16),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertCheckedToI16 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::I16),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertCheckedToI32 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::I32),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertWrappingToI32 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::I32),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertCheckedToI8 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::I8),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertWrappingToI8 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::I8),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertCheckedToU64 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::U64),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertWrappingToU64 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::U64),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertCheckedToIsize => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::Isize),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertCheckedToU128 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::U128),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertWrappingToU128 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::U128),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertCheckedToI128 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::I128),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertWrappingToI128 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::I128),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertWrappingToIsize => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::Isize),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertWrappingToUsize => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::Usize),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertWrappingToU8 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::U8),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertWrappingToU16 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::U16),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntConvertWrappingToI16 => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Scalar(crate::ScalarType::I16),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntBitNot => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0)],
            result: Type::Generic(0),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntShl => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0), Type::Scalar(crate::ScalarType::U32)],
            result: Type::Generic(0),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::IntEqual | PrimitiveRole::IntLess | PrimitiveRole::IntGreater => {
            crate::CallableSignature {
                safety: crate::Safety::Safe,
                generics: 1,
                generic_kinds: vec![crate::GenericKind::Type],
                parameters: vec![Type::Generic(0), Type::Generic(0)],
                result: Type::Scalar(crate::ScalarType::U32),
                effects: EffectRow::empty(),
                invocation: Quantity::ONCE,
                where_bounds: vec![],
                where_associated_type_bindings: vec![],
                where_associated_effect_bindings: vec![],
            }
        }
        PrimitiveRole::IntShr => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![Type::Generic(0), Type::Scalar(crate::ScalarType::U32)],
            result: Type::Generic(0),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::ArrayNew => array_signature(
            vec![Type::Scalar(ScalarType::Usize), Type::Generic(0)],
            Type::Array(Box::new(Type::Generic(0))),
        )
        .with_where_bounds(array_use_bound()),
        PrimitiveRole::ArrayLen | PrimitiveRole::ArrayCapacity => array_signature(
            vec![array_reference(Mutability::Shared)],
            Type::Scalar(ScalarType::Usize),
        ),
        PrimitiveRole::ArrayUtf8ValidUpTo => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Reference {
                mutability: Mutability::Shared,
                lifetime: Lifetime::Elided,
                referent: Box::new(Type::Array(Box::new(Type::Scalar(ScalarType::U8)))),
            }],
            result: Type::Scalar(ScalarType::Usize),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::ArrayPushUtf8Char => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Reference {
                mutability: Mutability::Unique,
                lifetime: Lifetime::Elided,
                referent: Box::new(Type::Array(Box::new(Type::Scalar(ScalarType::U8)))),
            }, Type::Scalar(ScalarType::Char)],
            result: Type::Unit,
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::ArrayExtendFromSlice => array_signature(
            vec![
                array_reference(Mutability::Unique),
                array_reference(Mutability::Shared),
                Type::Scalar(ScalarType::Usize),
                Type::Scalar(ScalarType::Usize),
            ],
            Type::Unit,
        )
        .with_where_bounds(array_use_bound()),
        PrimitiveRole::ArrayInsertMove => array_signature(
            vec![
                array_reference(Mutability::Unique),
                Type::Scalar(ScalarType::Usize),
                Type::Generic(0),
            ],
            Type::Unit,
        ),
        PrimitiveRole::ArrayRemoveMove => array_signature(
            vec![
                array_reference(Mutability::Unique),
                Type::Scalar(ScalarType::Usize),
            ],
            Type::Generic(0),
        ),
        PrimitiveRole::ArrayAppendMove => array_signature(
            vec![
                array_reference(Mutability::Unique),
                Type::Array(Box::new(Type::Generic(0))),
            ],
            Type::Unit,
        ),
        PrimitiveRole::ArrayInsertFromSlice => array_signature(
            vec![
                array_reference(Mutability::Unique),
                Type::Scalar(ScalarType::Usize),
                array_reference(Mutability::Shared),
                Type::Scalar(ScalarType::Usize),
                Type::Scalar(ScalarType::Usize),
            ],
            Type::Unit,
        )
        .with_where_bounds(array_use_bound()),
        PrimitiveRole::ArrayInsertUtf8FromSlice => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![
                Type::Reference {
                    mutability: Mutability::Unique,
                    lifetime: Lifetime::Elided,
                    referent: Box::new(Type::Array(Box::new(Type::Scalar(ScalarType::U8)))),
                },
                Type::Scalar(ScalarType::Usize),
                Type::Reference {
                    mutability: Mutability::Shared,
                    lifetime: Lifetime::Elided,
                    referent: Box::new(Type::Array(Box::new(Type::Scalar(ScalarType::U8)))),
                },
                Type::Scalar(ScalarType::Usize),
                Type::Scalar(ScalarType::Usize),
            ],
            result: Type::Scalar(ScalarType::Usize),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::ArrayTruncateDiscard => array_signature(
            vec![
                array_reference(Mutability::Unique),
                Type::Scalar(ScalarType::Usize),
            ],
            Type::Unit,
        )
        .with_where_bounds(array_affine_use_bound()),
        PrimitiveRole::ArrayReverseMove => array_signature(
            vec![array_reference(Mutability::Unique)],
            Type::Unit,
        ),
        PrimitiveRole::ArraySplitOffMove => array_signature(
            vec![
                array_reference(Mutability::Unique),
                Type::Scalar(ScalarType::Usize),
            ],
            Type::Array(Box::new(Type::Generic(0))),
        ),
        PrimitiveRole::ArraySplitBorrowUnique => array_borrow_signature(
            vec![
                array_borrow_reference(Mutability::Unique),
                Type::Scalar(ScalarType::Usize),
                Type::Scalar(ScalarType::Usize),
                Type::Scalar(ScalarType::Usize),
            ],
            Type::Tuple(vec![
                Type::Reference {
                    mutability: Mutability::Unique,
                    lifetime: Lifetime::Generic(0),
                    referent: Box::new(Type::Array(Box::new(Type::Generic(1)))),
                },
                Type::Reference {
                    mutability: Mutability::Unique,
                    lifetime: Lifetime::Generic(0),
                    referent: Box::new(Type::Array(Box::new(Type::Generic(1)))),
                },
            ]),
        ),
        PrimitiveRole::ArrayPopUtf8Char => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Reference {
                mutability: Mutability::Unique,
                lifetime: Lifetime::Elided,
                referent: Box::new(Type::Array(Box::new(Type::Scalar(ScalarType::U8)))),
            }],
            result: Type::Tuple(vec![
                Type::Scalar(ScalarType::Char),
                Type::Scalar(ScalarType::Usize),
            ]),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::ArrayUtf8CharAt => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![
                Type::Reference {
                    mutability: Mutability::Shared,
                    lifetime: Lifetime::Elided,
                    referent: Box::new(Type::Array(Box::new(Type::Scalar(ScalarType::U8)))),
                },
                Type::Scalar(ScalarType::Usize),
                Type::Scalar(ScalarType::Usize),
                Type::Scalar(ScalarType::Usize),
            ],
            result: Type::Tuple(vec![
                Type::Scalar(ScalarType::Char),
                Type::Scalar(ScalarType::Usize),
            ]),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::ArrayGetCopy => array_signature(
            vec![
                array_reference(Mutability::Shared),
                Type::Scalar(ScalarType::Usize),
            ],
            Type::Generic(0),
        )
        .with_where_bounds(array_use_bound()),
        PrimitiveRole::ArrayGetMove => array_signature(
            vec![
                array_reference(Mutability::Unique),
                Type::Scalar(ScalarType::Usize),
            ],
            Type::Generic(0),
        ),
        PrimitiveRole::ArrayPopMove => {
            array_signature(vec![array_reference(Mutability::Unique)], Type::Generic(0))
        }
        PrimitiveRole::ArrayGetBorrowShared => array_borrow_signature(
            vec![
                array_borrow_reference(Mutability::Shared),
                Type::Scalar(ScalarType::Usize),
            ],
            Type::Reference {
                mutability: Mutability::Shared,
                lifetime: Lifetime::Generic(0),
                referent: Box::new(Type::Generic(1)),
            },
        ),
        PrimitiveRole::ArrayGetBorrowUnique => array_borrow_signature(
            vec![
                array_borrow_reference(Mutability::Unique),
                Type::Scalar(ScalarType::Usize),
            ],
            Type::Reference {
                mutability: Mutability::Unique,
                lifetime: Lifetime::Generic(0),
                referent: Box::new(Type::Generic(1)),
            },
        ),
        PrimitiveRole::ArraySetMove => array_signature(
            vec![
                array_reference(Mutability::Unique),
                Type::Scalar(ScalarType::Usize),
                Type::Generic(0),
            ],
            Type::Unit,
        ),
        PrimitiveRole::ArrayPushMove => array_signature(
            vec![array_reference(Mutability::Unique), Type::Generic(0)],
            Type::Unit,
        ),
        PrimitiveRole::ArrayEmpty => {
            array_signature(vec![], Type::Array(Box::new(Type::Generic(0))))
        }
        PrimitiveRole::ArrayReserve => array_signature(
            vec![
                array_reference(Mutability::Unique),
                Type::Scalar(ScalarType::Usize),
            ],
            Type::Unit,
        ),
        PrimitiveRole::ArrayFinishDrained => {
            array_signature(vec![Type::Array(Box::new(Type::Generic(0)))], Type::Unit)
        }
        PrimitiveRole::StaticLen => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![static_utf8_data()],
            result: Type::Scalar(ScalarType::Usize),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::StaticSubslice => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![
                static_utf8_data(),
                Type::Scalar(ScalarType::Usize),
                Type::Scalar(ScalarType::Usize),
            ],
            result: static_utf8_data(),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::StaticGetShared => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![static_utf8_data(), Type::Scalar(ScalarType::Usize)],
            result: Type::Reference {
                mutability: Mutability::Shared,
                lifetime: Lifetime::Static,
                referent: Box::new(Type::Scalar(ScalarType::U8)),
            },
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::StaticAsArray => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![static_utf8_data()],
            result: Type::Reference {
                mutability: Mutability::Shared,
                lifetime: Lifetime::Static,
                referent: Box::new(Type::Array(Box::new(Type::Scalar(ScalarType::U8)))),
            },
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::StaticRawAsArray => crate::CallableSignature {
            safety: crate::Safety::Safe,
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::StaticData {
                element: Box::new(Type::Scalar(ScalarType::U8)),
                tag: crate::STATIC_RAW_U8_DATA_TAG,
                alignment: 1,
            }],
            result: Type::Reference {
                mutability: Mutability::Shared,
                lifetime: Lifetime::Static,
                referent: Box::new(Type::Array(Box::new(Type::Scalar(ScalarType::U8)))),
            },
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::Float(_) | PrimitiveRole::Memory(_) => unreachable!("handled before the legacy signature table"),
    }
}

fn static_utf8_data() -> Type {
    Type::StaticData {
        element: Box::new(Type::Scalar(ScalarType::U8)),
        tag: crate::STATIC_UTF8_DATA_TAG,
        alignment: 1,
    }
}

fn expected_float_signature(primitive: FloatPrimitive) -> crate::CallableSignature {
    let (parameters, result) = primitive.scalar_signature();
    crate::CallableSignature {
        safety: crate::Safety::Safe,
        generics: 0,
        generic_kinds: vec![],
        parameters: parameters.into_iter().map(Type::Scalar).collect(),
        result: Type::Scalar(result),
        effects: EffectRow::empty(),
        invocation: Quantity::ONCE,
        where_bounds: vec![],
        where_associated_type_bindings: vec![],
        where_associated_effect_bindings: vec![],
    }
}

fn array_reference(mutability: Mutability) -> Type {
    Type::Reference {
        mutability,
        lifetime: Lifetime::Elided,
        referent: Box::new(Type::Array(Box::new(Type::Generic(0)))),
    }
}

fn array_borrow_reference(mutability: Mutability) -> Type {
    Type::Reference {
        mutability,
        lifetime: Lifetime::Generic(0),
        referent: Box::new(Type::Array(Box::new(Type::Generic(1)))),
    }
}

fn array_borrow_signature(parameters: Vec<Type>, result: Type) -> crate::CallableSignature {
    crate::CallableSignature {
        safety: crate::Safety::Safe,
        generics: 2,
        generic_kinds: vec![crate::GenericKind::Lifetime, crate::GenericKind::Type],
        parameters,
        result,
        effects: EffectRow::empty(),
        invocation: Quantity::ONCE,
        where_bounds: vec![],
        where_associated_type_bindings: vec![],
        where_associated_effect_bindings: vec![],
    }
}

fn array_signature(parameters: Vec<Type>, result: Type) -> crate::CallableSignature {
    crate::CallableSignature {
        safety: crate::Safety::Safe,
        generics: 1,
        generic_kinds: vec![crate::GenericKind::Type],
        parameters,
        result,
        effects: EffectRow::empty(),
        invocation: Quantity::ONCE,
        where_bounds: vec![],
        where_associated_type_bindings: vec![],
        where_associated_effect_bindings: vec![],
    }
}

fn array_use_bound() -> Vec<(Type, crate::ElaboratedTraitReference)> {
    vec![(
        Type::Generic(0),
        crate::ElaboratedTraitReference {
            definition: DefKey(Digest::of_bytes(
                b"grandiose-stage0-language-prelude-use-v1",
            )),
            arguments: vec![crate::GenericArgument::ConstQuantity(
                Quantity::UNRESTRICTED,
            )],
        },
    )]
}

fn array_affine_use_bound() -> Vec<(Type, crate::ElaboratedTraitReference)> {
    vec![
        (
            Type::Generic(0),
            crate::ElaboratedTraitReference {
                definition: DefKey(Digest::of_bytes(
                    b"grandiose-stage0-language-prelude-use-v1",
                )),
                arguments: vec![crate::GenericArgument::ConstQuantity(Quantity::AFFINE)],
            },
        ),
    ]
}

trait CallableSignatureExt {
    fn with_where_bounds(self, where_bounds: Vec<(Type, crate::ElaboratedTraitReference)>) -> Self;
}

impl CallableSignatureExt for crate::CallableSignature {
    fn with_where_bounds(
        mut self,
        where_bounds: Vec<(Type, crate::ElaboratedTraitReference)>,
    ) -> Self {
        self.where_bounds = where_bounds;
        self
    }
}
fn manifest_digest(
    standard_library: &PackageKey,
    primitives: &BTreeMap<PrimitiveRole, DefKey>,
    host_imports: &BTreeMap<DefKey, HostImport>,
) -> Digest {
    let mut bytes = b"grandiose-stage0-runtime-manifest-v1".to_vec();
    bytes.extend_from_slice(&(standard_library.0.len() as u64).to_le_bytes());
    bytes.extend_from_slice(standard_library.0.as_bytes());
    for (role, definition) in primitives {
        bytes.push(role.stable_tag());
        bytes.extend_from_slice(&definition.0.as_bytes());
    }
    for (definition, import) in host_imports {
        bytes.extend_from_slice(&definition.0.as_bytes());
        bytes.extend_from_slice(&(import.capability.len() as u64).to_le_bytes());
        bytes.extend_from_slice(import.capability.as_bytes());
        bytes.extend_from_slice(&(import.symbol.len() as u64).to_le_bytes());
        bytes.extend_from_slice(import.symbol.as_bytes());
    }
    Digest::of_bytes(&bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    #[test]
    fn malformed_float_self_conversion_selectors_are_rejected() {
        for name in ["f32-to-f32", "f64-to-f64", "f32-to-f64-checked", "f64-to-f32-checked"] {
            assert_eq!(PrimitiveRole::parse_selector_name(name), None, "{name}");
        }
    }

    #[test]
    fn malformed_float_conversion_roles_are_rejected_before_world_hashing() {
        let scalars = [ScalarType::Bool, ScalarType::U8, ScalarType::U16, ScalarType::U32,
            ScalarType::U64, ScalarType::U128, ScalarType::I8, ScalarType::I16, ScalarType::I32,
            ScalarType::I64, ScalarType::I128, ScalarType::Usize, ScalarType::Isize,
            ScalarType::F32, ScalarType::F64, ScalarType::Char, ScalarType::Text, ScalarType::Bytes];
        let mut admitted = 0;
        for from in scalars {
            for to in scalars {
                for checked in [false, true] {
                    let float_from = matches!(from, ScalarType::F32 | ScalarType::F64);
                    let float_to = matches!(to, ScalarType::F32 | ScalarType::F64);
                    let valid = (!checked && float_to && (is_runtime_integer(from) || (float_from && from != to)))
                        || (checked && float_from && is_runtime_integer(to));
                    let role = PrimitiveRole::Float(FloatPrimitive::Convert { from, to, checked });
                    let mut input = RuntimeManifestInput { standard_library: PackageKey("std@0.1.0".into()),
                        selectors: vec![PrimitiveSelector { role, module_path: "crate".into(), name: "leaf".into() }], host_imports: vec![] };
                    let canonicalized = input.canonicalize();
                    assert_eq!(canonicalized.is_ok(), valid, "{role:?}");
                    if valid {
                        admitted += 1;
                        assert_eq!(PrimitiveRole::parse_selector_name(role.selector_name()), Some(role));
                        assert!((69..=146).contains(&role.stable_tag()));
                    } else {
                        assert_eq!(canonicalized, Err(ManifestError::InvalidRole(role)));
                        assert_eq!(input.bind([], &ElaboratedInterface::default()), Err(ManifestError::InvalidRole(role)));
                    }
                }
            }
        }
        assert_eq!(admitted, 50);
    }

    #[test]
    fn historical_checked_float_operation_aliases_keep_their_canonical_authority() {
        for width in ["f32", "f64"] {
            for operation in ["add", "sub", "mul", "div", "rem", "neg", "eq", "ne", "lt", "le", "gt", "ge"] {
                let name = format!("{width}-{operation}");
                let canonical = PrimitiveRole::parse_selector_name(&name).unwrap();
                assert_eq!(PrimitiveRole::parse_selector_name(format!("{name}-checked")), Some(canonical));
                assert_eq!(canonical.selector_name(), name);
            }
        }
    }

    #[test]
    fn runtime_authority_tags_are_unique_across_the_complete_finite_role_inventory() {
        // Keep the non-float inventory explicit, including every declaration
        // variant. The 78 valid parameterized float leaves are added below.
        let mut roles = vec![
            PrimitiveRole::Abort,
            PrimitiveRole::BranchBool,
            PrimitiveRole::TextByteLen,
            PrimitiveRole::TextConcat,
            PrimitiveRole::TextEq,
            PrimitiveRole::TextFromUtf8Checked,
            PrimitiveRole::TextAsBytes,
            PrimitiveRole::CharFromU32Checked,
            PrimitiveRole::CharToU32,
            PrimitiveRole::BytesLen,
            PrimitiveRole::BytesConcat,
            PrimitiveRole::BytesGet,
            PrimitiveRole::BytesSlice,
            PrimitiveRole::BytesFromArrayMove,
            PrimitiveRole::BytesToArray,
            PrimitiveRole::BytesUtf8ValidUpTo,
            PrimitiveRole::Blake3,
            PrimitiveRole::U32CheckedAdd,
            PrimitiveRole::U32CheckedSub,
            PrimitiveRole::U32CheckedMul,
            PrimitiveRole::U32CheckedDiv,
            PrimitiveRole::U32CheckedRem,
            PrimitiveRole::U32WrappingAdd,
            PrimitiveRole::U32WrappingSub,
            PrimitiveRole::U32WrappingMul,
            PrimitiveRole::U32WrappingShl,
            PrimitiveRole::U32WrappingShr,
            PrimitiveRole::U32CheckedShl,
            PrimitiveRole::U32CheckedShr,
            PrimitiveRole::U32Eq,
            PrimitiveRole::U32Lt,
            PrimitiveRole::U32Le,
            PrimitiveRole::U32ToUsize,
            PrimitiveRole::UsizeToU32Checked,
            PrimitiveRole::IntCheckedAdd,
            PrimitiveRole::IntCheckedDiv,
            PrimitiveRole::IntWrappingAdd,
            PrimitiveRole::IntConvertCheckedToI64,
            PrimitiveRole::IntConvertWrappingToI64,
            PrimitiveRole::IntConvertWrappingToU32,
            PrimitiveRole::IntConvertWrappingToUsize,
            PrimitiveRole::IntConvertWrappingToU8,
            PrimitiveRole::IntConvertWrappingToU16,
            PrimitiveRole::IntConvertWrappingToI16,
            PrimitiveRole::IntWrappingSub,
            PrimitiveRole::IntWrappingMul,
            PrimitiveRole::IntWrappingNeg,
            PrimitiveRole::IntEqual,
            PrimitiveRole::IntLess,
            PrimitiveRole::IntGreater,
            PrimitiveRole::IntBitAnd,
            PrimitiveRole::IntBitOr,
            PrimitiveRole::IntBitXor,
            PrimitiveRole::IntBitNot,
            PrimitiveRole::IntShr,
            PrimitiveRole::IntShl,
            PrimitiveRole::IntConvertCheckedToU32,
            PrimitiveRole::IntConvertCheckedToUsize,
            PrimitiveRole::IntConvertCheckedToU8,
            PrimitiveRole::IntConvertCheckedToU16,
            PrimitiveRole::IntConvertCheckedToI16,
            PrimitiveRole::IntConvertCheckedToI32,
            PrimitiveRole::IntConvertWrappingToI32,
            PrimitiveRole::IntConvertCheckedToI8,
            PrimitiveRole::IntConvertWrappingToI8,
            PrimitiveRole::IntConvertCheckedToU64,
            PrimitiveRole::IntConvertWrappingToU64,
            PrimitiveRole::IntConvertCheckedToIsize,
            PrimitiveRole::IntConvertWrappingToIsize,
            PrimitiveRole::IntConvertCheckedToU128,
            PrimitiveRole::IntConvertWrappingToU128,
            PrimitiveRole::IntConvertCheckedToI128,
            PrimitiveRole::IntConvertWrappingToI128,
            PrimitiveRole::ArrayNew,
            PrimitiveRole::ArrayLen,
            PrimitiveRole::ArrayUtf8ValidUpTo,
            PrimitiveRole::ArrayPushUtf8Char,
            PrimitiveRole::ArrayExtendFromSlice,
            PrimitiveRole::ArrayInsertMove,
            PrimitiveRole::ArrayRemoveMove,
            PrimitiveRole::ArrayAppendMove,
            PrimitiveRole::ArrayInsertFromSlice,
            PrimitiveRole::ArrayInsertUtf8FromSlice,
            PrimitiveRole::ArrayTruncateDiscard,
            PrimitiveRole::ArrayReverseMove,
            PrimitiveRole::ArraySplitOffMove,
            PrimitiveRole::ArraySplitBorrowUnique,
            PrimitiveRole::ArrayPopUtf8Char,
            PrimitiveRole::ArrayUtf8CharAt,
            PrimitiveRole::ArrayGetCopy,
            PrimitiveRole::ArrayGetMove,
            PrimitiveRole::ArrayGetBorrowShared,
            PrimitiveRole::ArrayGetBorrowUnique,
            PrimitiveRole::ArraySetMove,
            PrimitiveRole::ArrayEmpty,
            PrimitiveRole::ArrayPushMove,
            PrimitiveRole::ArrayPopMove,
            PrimitiveRole::ArrayCapacity,
            PrimitiveRole::ArrayReserve,
            PrimitiveRole::ArrayFinishDrained,
            PrimitiveRole::StaticLen,
            PrimitiveRole::StaticSubslice,
            PrimitiveRole::StaticGetShared,
            PrimitiveRole::StaticAsArray,
            PrimitiveRole::StaticRawAsArray,
        ];
        for width in ["f32", "f64"] {
            for operation in ["add", "sub", "mul", "div", "rem", "neg", "eq", "ne", "lt", "le", "gt", "ge"] {
                roles.push(PrimitiveRole::parse_selector_name(format!("{width}-{operation}")).unwrap());
            }
            for direction in ["to", "from"] {
                roles.push(PrimitiveRole::parse_selector_name(format!("{width}-{direction}-bits")).unwrap());
            }
        }
        for name in ["f32-to-f64", "f64-to-f32"] {
            roles.push(PrimitiveRole::parse_selector_name(name).unwrap());
        }
        for integer in ["u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize"] {
            for width in ["f32", "f64"] {
                for name in [format!("{integer}-to-{width}"), format!("{width}-to-{integer}-checked")] {
                    roles.push(PrimitiveRole::parse_selector_name(name).unwrap());
                }
            }
        }
        roles.extend(MemoryPrimitive::ALL.into_iter().map(PrimitiveRole::Memory));
        assert_eq!(roles.len(), 199);
        assert_eq!(roles.iter().copied().collect::<BTreeSet<_>>().len(), 199);
        let mut tags = BTreeMap::new();
        for role in roles {
            assert_eq!(PrimitiveRole::parse_selector_name(role.selector_name()), Some(role));
            let previous = tags.insert(role.stable_tag(), role);
            assert!(previous.is_none(), "runtime tag {} aliases {previous:?} and {role:?}", role.stable_tag());
        }
        assert_eq!(tags.keys().copied().collect::<Vec<_>>(), (0..=198).collect::<Vec<u8>>());
        // Shared immutable witnesses for the source-owned role comparator.
        // Check exact tags here, where the native private encoding is visible;
        // the source fixture separately executes its own metadata functions.
        let mut witnessed = BTreeMap::new();
        for line in include_str!("../../../compiler/spec/runtime-authority.tsv").lines().skip(1) {
            let (name, tag) = line.split_once('\t').unwrap();
            let role = PrimitiveRole::parse_selector_name(name).unwrap();
            let tag = tag.parse::<u8>().unwrap();
            assert_eq!(role.selector_name(), name);
            assert_eq!(role.stable_tag(), tag, "{name}");
            assert!(witnessed.insert(tag, role).is_none(), "duplicate witness tag");
        }
        assert_eq!(witnessed, tags, "source witness inventory must cover every native role");
        assert_eq!(PrimitiveRole::IntCheckedDiv.stable_tag(), 182);
        assert_eq!(PrimitiveRole::parse_selector_name("f32-add").unwrap().stable_tag(), 69);
    }

    #[test]
    fn bound_manifest_fingerprints_distinguish_integer_division_and_float_addition_authority() {
        let package = PackageKey("std@0.1.0".into());
        let definition = DefKey(Digest::of_bytes(b"same-declaration"));
        let integer = BTreeMap::from([(PrimitiveRole::IntCheckedDiv, definition)]);
        let float = BTreeMap::from([(PrimitiveRole::parse_selector_name("f32-add").unwrap(), definition)]);
        assert_ne!(
            manifest_digest(&package, &integer, &BTreeMap::new()),
            manifest_digest(&package, &float, &BTreeMap::new())
        );
    }


    #[test]
    fn canonical_float_leaf_selectors_are_finite_unique_and_round_trip() {
        let mut selectors = Vec::new();
        for width in ["f32", "f64"] {
            for operation in [
                "add", "sub", "mul", "div", "rem", "neg", "eq", "ne", "lt", "le", "gt", "ge",
            ] {
                selectors.push(format!("{width}-{operation}"));
            }
            selectors.push(format!("{width}-to-bits"));
            selectors.push(format!("{width}-from-bits"));
        }
        selectors.extend(["f32-to-f64".to_owned(), "f64-to-f32".to_owned()]);
        for integer in [
            "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
        ] {
            for width in ["f32", "f64"] {
                selectors.push(format!("{integer}-to-{width}"));
                selectors.push(format!("{width}-to-{integer}-checked"));
            }
        }
        assert_eq!(selectors.len(), 78);
        let roles = selectors
            .iter()
            .map(|selector| {
                PrimitiveRole::parse_selector_name(selector).expect("canonical float role")
            })
            .collect::<Vec<_>>();
        assert!(roles.iter().all(|role| role.is_float()));
        assert_eq!(roles.iter().collect::<BTreeSet<_>>().len(), selectors.len());
        assert_eq!(
            roles
                .iter()
                .map(|role| role.stable_tag())
                .collect::<BTreeSet<_>>()
                .len(),
            selectors.len()
        );
        for (selector, role) in selectors.iter().zip(roles) {
            assert_eq!(role.selector_name(), *selector);
            let PrimitiveRole::Float(primitive) = role else {
                unreachable!()
            };
            let (parameters, result) = primitive.scalar_signature();
            assert!(!parameters.is_empty());
            assert!(matches!(
                result,
                ScalarType::F32
                    | ScalarType::F64
                    | ScalarType::U8
                    | ScalarType::U16
                    | ScalarType::U32
                    | ScalarType::U64
                    | ScalarType::U128
                    | ScalarType::Usize
                    | ScalarType::I8
                    | ScalarType::I16
                    | ScalarType::I32
                    | ScalarType::I64
                    | ScalarType::I128
                    | ScalarType::Isize
            ));
        }
    }
}
