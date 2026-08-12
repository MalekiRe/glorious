use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, VecDeque},
    error::Error,
    fmt,
    ops::Range,
    sync::Arc,
};

pub type TypeId = u32;
pub type Register = u32;
pub type FunctionId = u32;

pub const UNIT: TypeId = 0;
pub const NEVER: TypeId = 1;
pub const U8: TypeId = 2;
pub const U16: TypeId = 3;
pub const U32: TypeId = 4;
pub const U64: TypeId = 5;
pub const U128: TypeId = 6;
pub const I8: TypeId = 7;
pub const I16: TypeId = 8;
pub const I32: TypeId = 9;
pub const I64: TypeId = 10;
pub const I128: TypeId = 11;
pub const USIZE: TypeId = 12;
pub const ISIZE: TypeId = 13;
pub const F32: TypeId = 14;
pub const F64: TypeId = 15;
pub const CHAR: TypeId = 16;
pub const TEXT: TypeId = 17;
pub const BYTES: TypeId = 18;
pub const NONE32: u32 = u32::MAX;

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct Field {
    pub name: String,
    pub ty: TypeId,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct EnumVariant {
    pub name: String,
    pub fields: Vec<Field>,
    /// Explicit `= <const-expr>` runtime discriminant, when declared. When
    /// `None`, the variant's emitted runtime tag is its position (index) in the
    /// enum's variant list, preserving ordinary implicit-index behavior.
    pub tag: Option<u32>,
}

impl EnumVariant {
    /// The emitted runtime tag for this variant at position `index`.
    /// An explicit discriminant overrides the otherwise index-derived tag.
    pub fn discriminant(&self, index: u32) -> u32 {
        self.tag.unwrap_or(index)
    }
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct Signature {
    pub params: Vec<TypeId>,
    pub result: TypeId,
    pub outward_protocols: Vec<u32>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct Import {
    pub capability: String,
    pub symbol: String,
    pub signature: Signature,
    pub may_trap: bool,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct Export {
    pub name: String,
    pub function: FunctionId,
    pub signature: Signature,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct Operation {
    pub name: String,
    pub payload_signature: Signature,
    pub result_type: TypeId,
    pub resumption_lower: u32,
    pub resumption_upper: Option<u32>,
    pub terminal: bool,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct Protocol {
    pub display_name: String,
    pub type_arguments: Vec<TypeId>,
    pub operations: Vec<Operation>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct HandlerClause {
    pub protocol: u32,
    pub operation: u32,
    pub callable_signature: Signature,
    pub resumption_type: Option<TypeId>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct HandlerDef {
    pub result_type: TypeId,
    pub clauses: Vec<HandlerClause>,
    pub partial: bool,
}

const MAGIC: &[u8; 8] = b"GRBC\r\n\x1a\n";
const HEADER_LEN: usize = 64;
const DIRECTORY_ENTRY_LEN: usize = 32;
const CRITICAL: u32 = 1;
const CORE_G1: u64 = 1;
const REFERENCES_G1: u64 = 1 << 1;
const LABELS_G1: u64 = 1 << 2;
const HANDLERS_G1: u64 = 1 << 3;
const MULTISHOT_G1: u64 = 1 << 4;
const HOST_ABI_G1: u64 = 1 << 5;
const ARRAY_RESERVE_G1: u64 = 1 << 6;
const ARRAY_FINISH_DRAINED_G1: u64 = 1 << 7;
const BYTES_UTF8_VALID_UP_TO_G1: u64 = 1 << 8;
const EXECUTABLE: u32 = 1;
pub const EXPORTED: u32 = 1;
pub const DROP_HOOK: u32 = 1 << 1;
pub const NO_RETURN: u32 = 1 << 2;
const FUNCTION_FLAGS: u32 = EXPORTED | DROP_HOOK | NO_RETURN;
const DUPLICABLE: u8 = 1;
const ZERO_SIZED: u8 = 1 << 1;
const OPAQUE: u8 = 1 << 2;
const HAS_DROP: u8 = 1 << 3;
const ZERO_USE_ALLOWED: u8 = 1 << 4;
const TYPE_FLAGS: u8 = DUPLICABLE | ZERO_SIZED | OPAQUE | HAS_DROP | ZERO_USE_ALLOWED;
const USE_CAPABILITY_FLAGS: u8 = DUPLICABLE | ZERO_USE_ALLOWED;

fn maximal_capability_flags(ty: &Type) -> u8 {
    match ty.representation() {
        Type::Unit => DUPLICABLE | ZERO_USE_ALLOWED,
        Type::Never => 0,
        Type::U8
        | Type::U16
        | Type::U32
        | Type::U64
        | Type::U128
        | Type::I8
        | Type::I16
        | Type::I32
        | Type::I64
        | Type::I128
        | Type::Usize
        | Type::Isize
        | Type::F32
        | Type::F64
        | Type::Char
        | Type::Text
        | Type::Bytes => DUPLICABLE | ZERO_USE_ALLOWED,
        Type::Array { .. } => 0,
        Type::RefUnique { .. } => ZERO_USE_ALLOWED,
        Type::RefShared { .. } => DUPLICABLE | ZERO_USE_ALLOWED,
        Type::Tuple { copy, .. }
        | Type::Struct { copy, .. }
        | Type::Enum { copy, .. }
        | Type::BindingPack { copy, .. } => u8::from(*copy) * DUPLICABLE,
        Type::Callable {
            copy,
            zero_use_allowed,
            ..
        } => (u8::from(*copy) * DUPLICABLE) | (u8::from(*zero_use_allowed) * ZERO_USE_ALLOWED),
        Type::Resumption {
            copy, lower_uses, ..
        } => (u8::from(*copy) * DUPLICABLE) | (u8::from(*lower_uses == 0) * ZERO_USE_ALLOWED),
        Type::Handler { .. } => 0,
        Type::Available { .. } => 0,
        Type::Restricted { .. } => unreachable!("representation peels restrictions"),
    }
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub enum Type {
    /// The same runtime type with deliberately narrower source-level `Use`
    /// capabilities. This wrapper has no type identity of its own.
    Restricted {
        base: Box<Type>,
        duplicable: bool,
        zero_use_allowed: bool,
    },
    Unit,
    Never,
    U8,
    U16,
    U32,
    U64,
    U128,
    I8,
    I16,
    I32,
    I64,
    I128,
    Usize,
    Isize,
    F32,
    F64,
    Char,
    Text,
    Bytes,
    Array {
        element: TypeId,
    },
    RefShared {
        referent: TypeId,
    },
    RefUnique {
        referent: TypeId,
    },
    Callable {
        signature: Signature,
        capture_type: TypeId,
        /// Environment receiver access: 0 shared, 1 unique, 2 owned.
        receiver_mode: u32,
        identity_name: String,
        copy: bool,
        /// Whether abandoning the callable may destroy its environment.
        zero_use_allowed: bool,
    },
    Handler {
        handler_def: u32,
        capture_type: TypeId,
        identity_name: String,
    },
    Resumption {
        input_type: TypeId,
        output_type: TypeId,
        effect_signature: Signature,
        lower_uses: u32,
        upper_uses: Option<u32>,
        identity_name: String,
        copy: bool,
    },
    BindingPack {
        payload_type: TypeId,
        identity_name: String,
        copy: bool,
    },
    Available {
        identity_name: String,
    },
    Tuple {
        fields: Vec<TypeId>,
        copy: bool,
    },
    Struct {
        name: String,
        fields: Vec<Field>,
        copy: bool,
    },
    Enum {
        name: String,
        variants: Vec<EnumVariant>,
        copy: bool,
    },
}

impl Type {
    /// Restrict the lowered principal-`Use` capabilities of a runtime type.
    /// Requests exceeding the runtime representation's capabilities are
    /// rejected by artifact verification.
    pub fn restricted(self, duplicable: bool, zero_use_allowed: bool) -> Self {
        Self::Restricted {
            base: Box::new(self),
            duplicable,
            zero_use_allowed,
        }
    }

    /// Return the runtime representation, ignoring source-level restrictions.
    pub fn representation(&self) -> &Self {
        match self {
            Self::Restricted { base, .. } => base.representation(),
            other => other,
        }
    }

    pub fn claimed_duplicable(&self) -> bool {
        match self {
            Self::Restricted { duplicable, .. } => *duplicable,
            other => maximal_capability_flags(other) & DUPLICABLE != 0,
        }
    }

    pub fn claimed_zero_use_allowed(&self) -> bool {
        match self {
            Self::Restricted {
                zero_use_allowed, ..
            } => *zero_use_allowed,
            other => maximal_capability_flags(other) & ZERO_USE_ALLOWED != 0,
        }
    }

    fn is_integer(&self) -> bool {
        matches!(
            self.representation(),
            Self::U8
                | Self::U16
                | Self::U32
                | Self::U64
                | Self::U128
                | Self::I8
                | Self::I16
                | Self::I32
                | Self::I64
                | Self::I128
                | Self::Usize
                | Self::Isize
        )
    }

    pub fn predefined() -> Vec<Self> {
        vec![
            Self::Unit,
            Self::Never,
            Self::U8,
            Self::U16,
            Self::U32,
            Self::U64,
            Self::U128,
            Self::I8,
            Self::I16,
            Self::I32,
            Self::I64,
            Self::I128,
            Self::Usize,
            Self::Isize,
            Self::F32,
            Self::F64,
            Self::Char,
            Self::Text,
            Self::Bytes,
        ]
    }
    pub fn is_predefined(&self) -> bool {
        !matches!(
            self.representation(),
            Self::Tuple { .. }
                | Self::Struct { .. }
                | Self::Enum { .. }
                | Self::Array { .. }
                | Self::RefShared { .. }
                | Self::RefUnique { .. }
                | Self::Callable { .. }
                | Self::Handler { .. }
                | Self::Resumption { .. }
                | Self::BindingPack { .. }
                | Self::Available { .. }
        )
    }
}

pub(crate) fn construction_field_types(ty: &Type, variant: Option<u32>) -> Option<Vec<TypeId>> {
    match (ty.representation(), variant) {
        (Type::Tuple { fields, .. }, None) => Some(fields.clone()),
        (Type::Struct { fields, .. }, None) => Some(fields.iter().map(|field| field.ty).collect()),
        (Type::Enum { variants, .. }, Some(variant)) => variants
            .get(variant as usize)
            .map(|variant| variant.fields.iter().map(|field| field.ty).collect()),
        _ => None,
    }
}

pub(crate) fn projection_field_type(ty: &Type, variant: Option<u32>, field: u32) -> Option<TypeId> {
    construction_field_types(ty, variant)?
        .get(field as usize)
        .copied()
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
pub enum Constant {
    Unit,
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    Usize(u64),
    Isize(i64),
    F32(f32),
    F64(f64),
    Char(char),
    Text(String),
    Bytes(Vec<u8>),
}

/// Supported subset of the frozen, type-generic primitive table.
#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[repr(u32)]
pub enum Primitive {
    IntCheckedAdd = 0x0000,
    IntCheckedSub = 0x0001,
    IntCheckedMul = 0x0002,
    IntCheckedDiv = 0x0003,
    IntCheckedRem = 0x0004,
    IntWrappingAdd = 0x0005,
    IntWrappingSub = 0x0006,
    IntWrappingMul = 0x0007,
    IntBitAnd = 0x0008,
    IntBitOr = 0x0009,
    IntBitXor = 0x000a,
    IntBitNot = 0x000b,
    IntShl = 0x000c,
    IntShr = 0x000d,
    IntEq = 0x000e,
    IntNe = 0x000f,
    IntLt = 0x0010,
    IntLe = 0x0011,
    IntGt = 0x0012,
    IntGe = 0x0013,
    IntConvertChecked = 0x0014,
    IntConvertWrapping = 0x0015,
    IntCheckedNeg = 0x0016,
    IntWrappingNeg = 0x0017,
    FloatAdd = 0x0020,
    FloatSub = 0x0021,
    FloatMul = 0x0022,
    FloatDiv = 0x0023,
    FloatRem = 0x0024,
    FloatEq = 0x0025,
    FloatNe = 0x0026,
    FloatLt = 0x0027,
    FloatLe = 0x0028,
    FloatGt = 0x0029,
    FloatGe = 0x002a,
    FloatConvert = 0x002b,
    FloatNeg = 0x002c,
    IntToFloat = 0x002d,
    FloatToIntChecked = 0x002e,
    FloatToBits = 0x002f,
    CharFromU32Checked = 0x0030,
    CharToU32 = 0x0031,
    FloatFromBits = 0x0032,
    TextByteLen = 0x0040,
    TextConcat = 0x0041,
    TextEq = 0x0042,
    TextFromUtf8Checked = 0x0043,
    TextAsBytes = 0x0044,
    BytesLen = 0x0050,
    BytesConcat = 0x0051,
    BytesGet = 0x0052,
    BytesSlice = 0x0053,
    BytesFromArrayMove = 0x0054,
    BytesToArray = 0x0055,
    BytesUtf8ValidUpTo = 0x0056,
    ArrayNew = 0x0060,
    ArrayLen = 0x0061,
    ArrayGetCopy = 0x0062,
    ArrayGetMove = 0x0063,
    ArrayGetBorrowShared = 0x0064,
    ArrayGetBorrowUnique = 0x0065,
    ArraySetMove = 0x0066,
    ArrayEmpty = 0x0067,
    ArrayPushMove = 0x0068,
    ArrayPopMove = 0x0069,
    ArrayCapacity = 0x006a,
    ArrayReserve = 0x006b,
    ArrayFinishDrained = 0x006c,
}
impl Primitive {
    pub fn from_u32(n: u32) -> Option<Self> {
        Some(match n {
            0 => Self::IntCheckedAdd,
            1 => Self::IntCheckedSub,
            2 => Self::IntCheckedMul,
            3 => Self::IntCheckedDiv,
            4 => Self::IntCheckedRem,
            5 => Self::IntWrappingAdd,
            6 => Self::IntWrappingSub,
            7 => Self::IntWrappingMul,
            0x0008 => Self::IntBitAnd,
            0x0009 => Self::IntBitOr,
            0x000a => Self::IntBitXor,
            0x000b => Self::IntBitNot,
            0x000c => Self::IntShl,
            0x000d => Self::IntShr,
            0x000e => Self::IntEq,
            0x000f => Self::IntNe,
            0x0010 => Self::IntLt,
            0x0011 => Self::IntLe,
            0x0012 => Self::IntGt,
            0x0013 => Self::IntGe,
            0x0014 => Self::IntConvertChecked,
            0x0015 => Self::IntConvertWrapping,
            0x0016 => Self::IntCheckedNeg,
            0x0017 => Self::IntWrappingNeg,
            0x0020 => Self::FloatAdd,
            0x0021 => Self::FloatSub,
            0x0022 => Self::FloatMul,
            0x0023 => Self::FloatDiv,
            0x0024 => Self::FloatRem,
            0x0025 => Self::FloatEq,
            0x0026 => Self::FloatNe,
            0x0027 => Self::FloatLt,
            0x0028 => Self::FloatLe,
            0x0029 => Self::FloatGt,
            0x002a => Self::FloatGe,
            0x002b => Self::FloatConvert,
            0x002c => Self::FloatNeg,
            0x002d => Self::IntToFloat,
            0x002e => Self::FloatToIntChecked,
            0x002f => Self::FloatToBits,
            0x0030 => Self::CharFromU32Checked,
            0x0031 => Self::CharToU32,
            0x0032 => Self::FloatFromBits,
            0x0040 => Self::TextByteLen,
            0x0041 => Self::TextConcat,
            0x0042 => Self::TextEq,
            0x0043 => Self::TextFromUtf8Checked,
            0x0044 => Self::TextAsBytes,
            0x0050 => Self::BytesLen,
            0x0051 => Self::BytesConcat,
            0x0052 => Self::BytesGet,
            0x0053 => Self::BytesSlice,
            0x0054 => Self::BytesFromArrayMove,
            0x0055 => Self::BytesToArray,
            0x0056 => Self::BytesUtf8ValidUpTo,
            0x0060 => Self::ArrayNew,
            0x0061 => Self::ArrayLen,
            0x0062 => Self::ArrayGetCopy,
            0x0063 => Self::ArrayGetMove,
            0x0064 => Self::ArrayGetBorrowShared,
            0x0065 => Self::ArrayGetBorrowUnique,
            0x0066 => Self::ArraySetMove,
            0x0067 => Self::ArrayEmpty,
            0x0068 => Self::ArrayPushMove,
            0x0069 => Self::ArrayPopMove,
            0x006a => Self::ArrayCapacity,
            0x006b => Self::ArrayReserve,
            0x006c => Self::ArrayFinishDrained,
            _ => return None,
        })
    }
}

/// Return the result type when `args` is the exact G1 signature supported by
/// the current concrete value representation.
pub(crate) fn primitive_result_type(op: Primitive, args: &[TypeId]) -> Option<TypeId> {
    use Primitive::*;
    let integer = |ty| {
        matches!(
            ty,
            U8 | U16 | U32 | U64 | U128 | I8 | I16 | I32 | I64 | I128 | USIZE | ISIZE
        )
    };
    let float = |ty| matches!(ty, F32 | F64);
    let same_integer = || match args {
        [a, b] if a == b && integer(*a) => Some(*a),
        _ => None,
    };
    let integer_comparison = || same_integer().map(|_| U32);
    match op {
        IntCheckedAdd | IntCheckedSub | IntCheckedMul | IntCheckedDiv | IntCheckedRem
        | IntWrappingAdd | IntWrappingSub | IntWrappingMul | IntBitAnd | IntBitOr | IntBitXor => {
            same_integer()
        }
        IntBitNot | IntCheckedNeg | IntWrappingNeg => match args {
            [a] if integer(*a) => Some(*a),
            _ => None,
        },
        IntShl | IntShr => match args {
            [a, U32] if integer(*a) => Some(*a),
            _ => None,
        },
        IntEq | IntNe | IntLt | IntLe | IntGt | IntGe => integer_comparison(),
        IntConvertChecked | IntConvertWrapping | IntToFloat | FloatConvert | FloatToIntChecked => {
            None
        }
        FloatToBits => match args {
            [F32] => Some(U32),
            [F64] => Some(U64),
            _ => None,
        },
        FloatFromBits => match args {
            [U32] => Some(F32),
            [U64] => Some(F64),
            _ => None,
        },
        FloatAdd | FloatSub | FloatMul | FloatDiv | FloatRem => match args {
            [a, b] if a == b && float(*a) => Some(*a),
            _ => None,
        },
        FloatEq | FloatNe | FloatLt | FloatLe | FloatGt | FloatGe => {
            matches!(args, [a, b] if a == b && float(*a)).then_some(U32)
        }
        FloatNeg => match args {
            [a] if float(*a) => Some(*a),
            _ => None,
        },
        CharFromU32Checked => (args == [U32]).then_some(CHAR),
        CharToU32 => (args == [CHAR]).then_some(U32),
        TextByteLen => (args == [TEXT]).then_some(USIZE),
        TextConcat => (args == [TEXT, TEXT]).then_some(TEXT),
        TextEq => (args == [TEXT, TEXT]).then_some(U32),
        TextFromUtf8Checked => (args == [BYTES]).then_some(TEXT),
        TextAsBytes => (args == [TEXT]).then_some(BYTES),
        BytesLen => (args == [BYTES]).then_some(USIZE),
        BytesConcat => (args == [BYTES, BYTES]).then_some(BYTES),
        BytesGet => (args == [BYTES, USIZE]).then_some(U8),
        BytesSlice => (args == [BYTES, USIZE, USIZE]).then_some(BYTES),
        BytesUtf8ValidUpTo => (args == [BYTES]).then_some(USIZE),
        BytesFromArrayMove | BytesToArray | ArrayNew | ArrayLen | ArrayGetCopy | ArrayGetMove
        | ArrayGetBorrowShared | ArrayGetBorrowUnique | ArraySetMove | ArrayEmpty
        | ArrayPushMove | ArrayPopMove | ArrayCapacity | ArrayReserve | ArrayFinishDrained => None,
    }
}

pub(crate) fn primitive_signature(
    types: &[Type],
    op: Primitive,
    args: &[TypeId],
    result: TypeId,
) -> bool {
    if primitive_result_type(op, args).is_some_and(|expected| expected == result) {
        return true;
    }
    let ty = |id: TypeId| types.get(id as usize).map(Type::representation);
    let array_element = |id| match ty(id) {
        Some(Type::Array { element }) => Some(*element),
        _ => None,
    };
    let shared_array_element = |id| match ty(id) {
        Some(Type::RefShared { referent }) => array_element(*referent),
        _ => None,
    };
    let unique_array_element = |id| match ty(id) {
        Some(Type::RefUnique { referent }) => array_element(*referent),
        _ => None,
    };
    use Primitive::*;
    match (op, args) {
        (IntConvertChecked | IntConvertWrapping, [source]) => {
            matches!(ty(*source), Some(source) if source.is_integer())
                && matches!(ty(result), Some(result) if result.is_integer())
        }
        (FloatConvert, [source]) => {
            matches!(ty(*source), Some(Type::F32 | Type::F64))
                && matches!(ty(result), Some(Type::F32 | Type::F64))
        }
        (IntToFloat, [source]) => {
            matches!(ty(*source), Some(source) if source.is_integer())
                && matches!(ty(result), Some(Type::F32 | Type::F64))
        }
        (FloatToIntChecked, [source]) => {
            matches!(ty(*source), Some(Type::F32 | Type::F64))
                && matches!(ty(result), Some(result) if result.is_integer())
        }
        (BytesFromArrayMove, [array]) => array_element(*array) == Some(U8) && result == BYTES,
        (BytesToArray, [BYTES]) => array_element(result) == Some(U8),
        (ArrayNew, [USIZE, element]) => array_element(result) == Some(*element),
        (ArrayLen | ArrayCapacity, [array_ref]) => {
            shared_array_element(*array_ref).is_some() && result == USIZE
        }
        (ArrayGetCopy | ArrayGetBorrowShared, [array_ref, USIZE]) => {
            let Some(element) = shared_array_element(*array_ref) else {
                return false;
            };
            if op == ArrayGetCopy {
                result == element
            } else {
                matches!(ty(result), Some(Type::RefShared { referent }) if *referent == element)
            }
        }
        (ArrayGetMove | ArrayGetBorrowUnique, [array_ref, USIZE]) => {
            let Some(element) = unique_array_element(*array_ref) else {
                return false;
            };
            if op == ArrayGetMove {
                result == element
            } else {
                matches!(ty(result), Some(Type::RefUnique { referent }) if *referent == element)
            }
        }
        (ArraySetMove, [array_ref, USIZE, element]) | (ArrayPushMove, [array_ref, element]) => {
            unique_array_element(*array_ref) == Some(*element) && result == UNIT
        }
        (ArrayEmpty, []) => array_element(result).is_some(),
        (ArrayPopMove, [array_ref]) => unique_array_element(*array_ref) == Some(result),
        (ArrayReserve, [array_ref, USIZE]) => {
            unique_array_element(*array_ref).is_some() && result == UNIT
        }
        (ArrayFinishDrained, [array]) => array_element(*array).is_some() && result == UNIT,
        _ => false,
    }
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub enum Instruction {
    Nop,
    Const {
        dst: Register,
        constant: u32,
    },
    Move {
        dst: Register,
        src: Register,
    },
    Copy {
        dst: Register,
        src: Register,
    },
    BorrowShared {
        dst: Register,
        src: Register,
    },
    BorrowUnique {
        dst: Register,
        src: Register,
    },
    ReborrowShared {
        dst: Register,
        src: Register,
    },
    ReborrowUnique {
        dst: Register,
        src: Register,
    },
    DerefCopy {
        dst: Register,
        src: Register,
    },
    DerefReborrowShared {
        dst: Register,
        src: Register,
    },
    DerefReborrowUnique {
        dst: Register,
        src: Register,
    },
    DerefMove {
        dst: Register,
        src: Register,
    },
    DerefStore {
        dst: Register,
        src: Register,
    },
    EndBorrow {
        reference: Register,
    },
    Construct {
        dst: Register,
        ty: TypeId,
        variant: Option<u32>,
        fields: Vec<Register>,
    },
    ProjectMove {
        dst: Register,
        src: Register,
        field: u32,
    },
    ProjectCopy {
        dst: Register,
        src: Register,
        field: u32,
    },
    ProjectBorrowShared {
        dst: Register,
        src: Register,
        field: u32,
    },
    ProjectBorrowUnique {
        dst: Register,
        src: Register,
        field: u32,
    },
    EnumTag {
        dst: Register,
        src: Register,
    },
    Drop {
        register: Register,
    },
    Deconstruct {
        src: Register,
    },
    Primitive {
        dst: Register,
        op: Primitive,
        args: Vec<Register>,
    },
    Jump {
        target: u32,
    },
    Switch {
        discr: Register,
        cases: Vec<(u32, u32)>,
        otherwise: u32,
    },
    Call {
        dst: Option<Register>,
        function: FunctionId,
        args: Vec<Register>,
    },
    TailCall {
        function: FunctionId,
        args: Vec<Register>,
    },
    /// Invoke this frame's function again with the same receiver environment.
    /// Valid only for borrowed receiver modes; the verifier rejects mode 2.
    CallSelf {
        dst: Option<Register>,
        args: Vec<Register>,
    },
    /// Tail-invoke this frame's function, transferring its current receiver.
    TailCallSelf {
        args: Vec<Register>,
    },
    /// Invoke a statically known receiver-taking function through an explicit
    /// shared receiver capability. The target must declare receiver mode 0;
    /// the receiver register is observed, never consumed.
    CallKnownReceiver {
        dst: Option<Register>,
        function: FunctionId,
        receiver: Register,
        args: Vec<Register>,
    },
    /// Tail-invoke a statically known mode-0 function through an explicit
    /// shared receiver capability. The receiver value is retained for the
    /// replacement frame without consuming its source register.
    TailCallKnownReceiver {
        function: FunctionId,
        receiver: Register,
        args: Vec<Register>,
    },
    MakeCallable {
        dst: Register,
        callable_type: TypeId,
        function: FunctionId,
        captures: Vec<Register>,
    },
    MakeHandler {
        dst: Register,
        handler_def: u32,
        clauses: Vec<Register>,
    },
    MakeHandlerShared {
        dst: Register,
        handler_def: u32,
        functions: Vec<FunctionId>,
        captures: Vec<Register>,
    },
    MakeBindingPack {
        dst: Register,
        binding_type: TypeId,
        payloads: Vec<Register>,
    },
    CallIndirect {
        dst: Option<Register>,
        callable: Register,
        receiver_mode: u32,
        args: Vec<Register>,
    },
    TailCallIndirect {
        callable: Register,
        receiver_mode: u32,
        args: Vec<Register>,
    },
    Handle {
        dst: Register,
        handler: Register,
        body: Register,
        args: Vec<Register>,
    },
    Perform {
        dst: Option<Register>,
        protocol: u32,
        operation: u32,
        payloads: Vec<Register>,
    },
    Resume {
        dst: Register,
        resumption: Register,
        receiver_mode: u32,
        value: Register,
    },
    /// Resume a captured continuation as this frame's terminal action. The
    /// resumed continuation returns directly to this frame's caller.
    TailResume {
        resumption: Register,
        receiver_mode: u32,
        value: Register,
    },
    Cancel {
        dst: Register,
        resumption: Register,
    },
    HostCall {
        dst: Option<Register>,
        import: u32,
        args: Vec<Register>,
    },
    Abort {
        message: Option<String>,
    },
    LabelPush {
        slot: u32,
        result_register: Register,
        target: u32,
    },
    LabelPop {
        slot: u32,
    },
    Leave {
        slot: u32,
        value: Register,
    },
    Return {
        src: Option<Register>,
    },
    Unreachable,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct Function {
    pub name: String,
    pub flags: u32,
    pub params: Vec<TypeId>,
    pub return_type: TypeId,
    pub outward_protocols: Vec<u32>,
    /// `None` for direct functions, otherwise 0=shared, 1=unique, 2=move.
    pub receiver_mode: Option<u32>,
    /// Includes hidden receiver r0, which is `Unit` for direct functions.
    pub register_types: Vec<TypeId>,
    pub code_start: u32,
    pub code_len: u32,
    pub label_slot_count: u32,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct CleanupPlan {
    pub function: FunctionId,
    pub first_instruction: u32,
    pub end_instruction: u32,
    pub registers: Vec<Register>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct DropGlue {
    pub ty: TypeId,
    pub function: FunctionId,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub enum ReferenceReturnOrigin {
    Parameter { parameter: u32, path: Vec<u32> },
    Receiver { path: Vec<u32> },
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct ReferenceReturnRoute {
    pub result_path: Vec<u32>,
    pub origin: ReferenceReturnOrigin,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct ReferenceReturnContract {
    pub function: FunctionId,
    pub routes: Vec<ReferenceReturnRoute>,
}

#[repr(C)]
#[derive(Clone, Debug, PartialEq)]
pub struct Artifact {
    pub required_features: u64,
    pub entry_function: Option<FunctionId>,
    pub types: Vec<Type>,
    pub constants: Vec<Constant>,
    pub imports: Vec<Import>,
    pub protocols: Vec<Protocol>,
    pub handler_defs: Vec<HandlerDef>,
    pub cleanups: Vec<CleanupPlan>,
    pub exports: Vec<Export>,
    pub drop_glue: Vec<DropGlue>,
    pub reference_return_contracts: Vec<ReferenceReturnContract>,
    pub functions: Vec<Function>,
    pub code: Vec<Instruction>,
}

/// Decoder-owned table builder. This intentionally mirrors [`Artifact`]'s C
/// layout so verification can inspect the tables without constructing the
/// public mutable compatibility value. Only `into_artifact` crosses into that
/// representation.
#[repr(C)]
pub(crate) struct DecodedTables {
    pub(crate) required_features: u64,
    pub(crate) entry_function: Option<FunctionId>,
    pub(crate) types: Vec<Type>,
    pub(crate) constants: Vec<Constant>,
    pub(crate) imports: Vec<Import>,
    pub(crate) protocols: Vec<Protocol>,
    pub(crate) handler_defs: Vec<HandlerDef>,
    pub(crate) cleanups: Vec<CleanupPlan>,
    pub(crate) exports: Vec<Export>,
    pub(crate) drop_glue: Vec<DropGlue>,
    pub(crate) reference_return_contracts: Vec<ReferenceReturnContract>,
    pub(crate) functions: Vec<Function>,
    pub(crate) code: Vec<Instruction>,
}

pub(crate) struct DecodedArtifact {
    pub(crate) tables: DecodedTables,
    pub(crate) constant_payloads: Vec<Option<EncodedConstantPayload>>,
    pub(crate) abort_messages: Vec<Option<Range<usize>>>,
    pub(crate) strings: Vec<(String, Range<usize>)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum EncodedConstantPayload {
    Text(Range<usize>),
    Bytes(Range<usize>),
}

/// Dense immutable instruction storage used after verification. Variable
/// register lists share one operand array instead of retaining one `Vec` per
/// public [`Instruction`].
#[derive(Debug)]
pub(crate) struct PackedCode {
    words: Box<[u32]>,
    operands: Box<[u32]>,
    offsets: Box<[u32]>,
    abort_strings: Box<[String]>,
}

impl PackedCode {
    pub(crate) fn from_instructions(instructions: &[Instruction]) -> Self {
        let mut abort_strings = instructions
            .iter()
            .filter_map(|instruction| match instruction {
                Instruction::Abort {
                    message: Some(message),
                } => Some(message.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        abort_strings.sort_by(|left, right| left.as_bytes().cmp(right.as_bytes()));
        abort_strings.dedup();
        let names = abort_strings
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, name)| (name, index as u32))
            .collect::<BTreeMap<_, _>>();
        let mut words = Vec::new();
        let mut operands = Vec::new();
        let mut operand_lists = BTreeMap::new();
        let mut offsets = Vec::with_capacity(instructions.len() + 1);
        for instruction in instructions {
            offsets.push(words.len() as u32);
            encode_instruction_with_operand_lists(
                instruction,
                &names,
                &mut words,
                &mut operands,
                &mut operand_lists,
            );
        }
        offsets.push(words.len() as u32);
        Self {
            words: words.into_boxed_slice(),
            operands: operands.into_boxed_slice(),
            offsets: offsets.into_boxed_slice(),
            abort_strings: abort_strings.into_boxed_slice(),
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.offsets.len().saturating_sub(1)
    }

    pub(crate) fn instruction(&self, index: usize) -> Option<Instruction> {
        let start = *self.offsets.get(index)? as usize;
        let end = *self.offsets.get(index + 1)? as usize;
        let decoded = decode_instructions(
            self.words.get(start..end)?,
            &self.operands,
            &self.abort_strings,
        )
        .expect("verified instructions remain decodable after packing");
        decoded.into_iter().next()
    }

    pub(crate) fn materialize(&self) -> Vec<Instruction> {
        (0..self.len())
            .map(|index| self.instruction(index).expect("packed instruction exists"))
            .collect()
    }

    pub(crate) fn materialize_range(&self, range: Range<usize>) -> Arc<[Instruction]> {
        range
            .map(|index| self.instruction(index).expect("packed instruction exists"))
            .collect::<Vec<_>>()
            .into()
    }

    #[cfg(test)]
    pub(crate) fn storage_bytes(&self) -> usize {
        (self.words.len() + self.operands.len() + self.offsets.len()) * std::mem::size_of::<u32>()
            + self.abort_strings.len() * std::mem::size_of::<String>()
            + self.abort_strings.iter().map(String::len).sum::<usize>()
    }
}

impl DecodedTables {
    pub(crate) fn as_artifact(&self) -> &Artifact {
        const {
            assert!(std::mem::size_of::<DecodedTables>() == std::mem::size_of::<Artifact>());
            assert!(std::mem::align_of::<DecodedTables>() == std::mem::align_of::<Artifact>());
        }
        // SAFETY: both structs are `repr(C)` and declare the exact same field
        // types in the exact same order. The compile-time size/alignment
        // assertions catch gross drift; the field-offset regression test
        // below catches same-size reordering during development.
        unsafe { &*(std::ptr::from_ref(self).cast::<Artifact>()) }
    }

    fn into_artifact(self) -> Artifact {
        Artifact {
            required_features: self.required_features,
            entry_function: self.entry_function,
            types: self.types,
            constants: self.constants,
            imports: self.imports,
            protocols: self.protocols,
            handler_defs: self.handler_defs,
            cleanups: self.cleanups,
            exports: self.exports,
            drop_glue: self.drop_glue,
            reference_return_contracts: self.reference_return_contracts,
            functions: self.functions,
            code: self.code,
        }
    }
}
impl Default for Artifact {
    fn default() -> Self {
        Self {
            required_features: CORE_G1,
            entry_function: None,
            types: Type::predefined(),
            constants: vec![],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![],
            code: vec![],
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecodeError {
    Truncated,
    BadMagic,
    UnsupportedMajor(u16),
    UnsupportedFeatures { lo: u64, hi: u64 },
    InvalidHeader,
    InvalidDirectory,
    DuplicateSection(u32),
    MissingSection(u32),
    UnknownCriticalSection(u32),
    InvalidUtf8,
    InvalidTable(&'static str),
    UnsupportedType(u8),
    UnsupportedOpcode { at: u32, opcode: u16 },
    UnsupportedPrimitive(u32),
    NonCanonical(String),
}
impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid G1 bytecode: ")?;
        match self {
            Self::Truncated => write!(f, "truncated input"),
            Self::BadMagic => write!(f, "bad magic"),
            Self::UnsupportedMajor(x) => write!(f, "unsupported format major {x}"),
            Self::UnsupportedFeatures { lo, hi } => {
                write!(f, "unsupported required features {hi:#x}:{lo:#x}")
            }
            Self::InvalidHeader => write!(f, "invalid header"),
            Self::InvalidDirectory => write!(f, "invalid section directory"),
            Self::DuplicateSection(x) => write!(f, "duplicate section {x}"),
            Self::MissingSection(x) => write!(f, "missing section {x}"),
            Self::UnknownCriticalSection(x) => write!(f, "unknown critical section {x}"),
            Self::InvalidUtf8 => write!(f, "invalid UTF-8"),
            Self::InvalidTable(x) => write!(f, "invalid {x} table"),
            Self::UnsupportedType(x) => write!(f, "unsupported assigned type tag {x:#x}"),
            Self::UnsupportedOpcode { at, opcode } => {
                write!(f, "instruction {at} uses unsupported opcode {opcode:#x}")
            }
            Self::UnsupportedPrimitive(x) => write!(f, "unsupported primitive {x:#x}"),
            Self::NonCanonical(x) => write!(f, "noncanonical encoding: {x}"),
        }
    }
}
impl Error for DecodeError {}

#[derive(Clone)]
struct Section {
    id: u32,
    bytes: Vec<u8>,
    count: u32,
    width: u32,
}

impl Artifact {
    pub const SUPPORTED_FEATURES: u64 = CORE_G1
        | REFERENCES_G1
        | LABELS_G1
        | HANDLERS_G1
        | MULTISHOT_G1
        | HOST_ABI_G1
        | ARRAY_RESERVE_G1
        | ARRAY_FINISH_DRAINED_G1
        | BYTES_UTF8_VALID_UP_TO_G1;
    pub fn encode(&self) -> Vec<u8> {
        #[cfg(test)]
        if self.cleanups.is_empty() && !self.functions.is_empty() {
            return crate::verify::with_generated_cleanup_plans(self.clone())
                .expect("test artifact must support canonical cleanup generation")
                .encode_impl()
                .expect("attempted to encode a non-G1 in-memory artifact");
        }
        self.encode_impl()
            .expect("attempted to encode a non-G1 in-memory artifact")
    }

    /// Reorders and deduplicates the constant pool by its exact G1 wire key,
    /// repairing every instruction that refers to a constant ID.
    ///
    /// Text constants are ordered by the little-endian encoded string-table
    /// ID, not by their text bytes, and byte-string payloads include their
    /// length prefix.  Keeping this operation next to the encoder prevents a
    /// compiler writer from having to duplicate those format details.
    pub fn canonicalize_constants(&mut self) {
        let names = artifact_name_ids(self);
        let keys = self
            .constants
            .iter()
            .map(|constant| constant_wire_key(constant, &names))
            .collect::<Vec<_>>();
        let mut order = (0..self.constants.len()).collect::<Vec<_>>();
        order.sort_by(|left, right| keys[*left].cmp(&keys[*right]));

        let old = std::mem::take(&mut self.constants);
        let mut remap = vec![0_u32; old.len()];
        let mut prior_key = None;
        for old_index in order {
            let key = &keys[old_index];
            let new_id = if prior_key.as_ref() == Some(key) {
                (self.constants.len() - 1) as u32
            } else {
                self.constants.push(old[old_index].clone());
                prior_key = Some(key.clone());
                (self.constants.len() - 1) as u32
            };
            remap[old_index] = new_id;
        }
        for instruction in &mut self.code {
            match instruction {
                Instruction::Const { constant, .. } => *constant = remap[*constant as usize],
                Instruction::Switch { cases, .. } => {
                    for (constant, _) in cases {
                        *constant = remap[*constant as usize];
                    }
                }
                _ => {}
            }
        }
    }

    fn encode_impl(&self) -> Result<Vec<u8>, DecodeError> {
        if self.required_features & !Self::SUPPORTED_FEATURES != 0 {
            return Err(DecodeError::UnsupportedFeatures {
                lo: self.required_features & !Self::SUPPORTED_FEATURES,
                hi: 0,
            });
        }
        check_predefined(&self.types)?;
        validate_canonical_metadata(
            &self.protocols,
            &self.handler_defs,
            &self.types,
            &self.functions,
            &self.imports,
            &self.exports,
        )?;
        let used_features = used_features(
            &self.types,
            &self.code,
            !self.protocols.is_empty(),
            !self.imports.is_empty(),
        );
        if self.required_features | CORE_G1 != used_features {
            return Err(DecodeError::NonCanonical(
                "required feature bits do not exactly describe the artifact".into(),
            ));
        }
        let name_id = artifact_name_ids(self);
        let mut names = name_id.keys().cloned().collect::<Vec<_>>();
        names.sort_by_key(|name| name_id[name]);
        let strings = encode_strings(&names);
        let (signature_values, sig_ids) = collect_signatures(
            &self.functions,
            &self.types,
            &self.protocols,
            &self.handler_defs,
            &self.imports,
            &self.exports,
        );
        let signatures = encode_signatures(&signature_values);
        let (drop_glue, dropped_types) =
            encode_drop_glue(&self.drop_glue, self.types.len(), &self.functions)?;
        let reference_return_contracts =
            encode_reference_return_contracts(&self.reference_return_contracts, &self.functions)?;
        let types = encode_types(&self.types, &name_id, &signature_values, &dropped_types)?;
        let constants = encode_constants(&self.constants, &name_id)?;
        let protocols = encode_protocols(&self.protocols, &name_id, &signature_values)?;
        let handler_defs = encode_handler_defs(&self.handler_defs, &signature_values)?;
        let imports = encode_imports(&self.imports, &name_id, &signature_values)?;
        let exports = encode_exports(&self.exports, &self.functions, &name_id, &signature_values)?;
        validate_function_metadata(&self.functions, &self.exports, &self.drop_glue)?;
        let mut operands = Vec::new();
        let mut operand_lists = BTreeMap::new();
        let mut code = Vec::new();
        let mut spans = Vec::new();
        for f in &self.functions {
            let start = code.len() as u32;
            let range = self
                .code
                .get(f.code_start as usize..(f.code_start + f.code_len) as usize)
                .ok_or(DecodeError::InvalidTable("function"))?;
            for i in range {
                encode_instruction_with_operand_lists(
                    i,
                    &name_id,
                    &mut code,
                    &mut operands,
                    &mut operand_lists,
                );
            }
            spans.push((start, code.len() as u32 - start, range.len() as u32));
        }
        let (cleanups, cleanup_spans) = encode_cleanups(
            &self.cleanups,
            &self.functions,
            &mut operands,
            &mut operand_lists,
        )?;
        let functions = encode_functions(
            &self.functions,
            &self.types,
            &name_id,
            &sig_ids,
            &spans,
            &cleanup_spans,
        )?;
        let sections = vec![
            Section {
                id: 1,
                count: names.len() as u32,
                width: 0,
                bytes: strings,
            },
            Section {
                id: 2,
                count: self.types.len() as u32,
                width: 0,
                bytes: types,
            },
            Section {
                id: 3,
                count: self.constants.len() as u32,
                width: 0,
                bytes: constants,
            },
            Section {
                id: 4,
                count: signature_values.len() as u32,
                width: 0,
                bytes: signatures,
            },
            Section {
                id: 5,
                count: self.imports.len() as u32,
                width: 24,
                bytes: imports,
            },
            Section {
                id: 6,
                count: self.protocols.len() as u32,
                width: 0,
                bytes: protocols,
            },
            Section {
                id: 7,
                count: self.handler_defs.len() as u32,
                width: 0,
                bytes: handler_defs,
            },
            Section {
                id: 8,
                count: self.functions.len() as u32,
                width: 64,
                bytes: functions,
            },
            Section {
                id: 9,
                count: code.len() as u32,
                width: 4,
                bytes: words_bytes(&code),
            },
            Section {
                id: 10,
                count: operands.len() as u32,
                width: 4,
                bytes: words_bytes(&operands),
            },
            Section {
                id: 11,
                count: self.cleanups.len() as u32,
                width: 24,
                bytes: cleanups,
            },
            Section {
                id: 12,
                count: self.exports.len() as u32,
                width: 16,
                bytes: exports,
            },
            Section {
                id: 13,
                count: self.drop_glue.len() as u32,
                width: 16,
                bytes: drop_glue,
            },
            Section {
                id: 14,
                // Pre-release G1.0 canonical-format change: section 14 is a
                // mandatory critical table, even when empty. The decoder
                // intentionally rejects artifacts from the earlier 13-table
                // draft rather than silently discarding provenance contracts.
                count: self.reference_return_contracts.len() as u32,
                width: 0,
                bytes: reference_return_contracts,
            },
        ];
        let directory_end = HEADER_LEN + DIRECTORY_ENTRY_LEN * sections.len();
        let mut offsets = Vec::new();
        let mut cursor = align8(directory_end);
        for s in &sections {
            offsets.push(cursor);
            cursor = align8(cursor + s.bytes.len())
        }
        let mut out = Vec::with_capacity(cursor);
        out.extend(MAGIC);
        put_u16(&mut out, 1);
        put_u16(&mut out, 0);
        put_u32(&mut out, 64);
        put_u32(
            &mut out,
            if self.entry_function.is_some() {
                EXECUTABLE
            } else {
                0
            },
        );
        put_u32(&mut out, sections.len() as u32);
        put_u32(&mut out, 32);
        put_u32(&mut out, self.entry_function.unwrap_or(NONE32));
        put_u64(&mut out, self.required_features | CORE_G1);
        put_u64(&mut out, 0);
        put_u64(&mut out, 64);
        put_u64(&mut out, cursor as u64);
        for (s, &off) in sections.iter().zip(&offsets) {
            put_u32(&mut out, s.id);
            put_u32(&mut out, CRITICAL);
            put_u64(&mut out, off as u64);
            put_u64(&mut out, s.bytes.len() as u64);
            put_u32(&mut out, s.count);
            put_u32(&mut out, s.width)
        }
        out.resize(align8(out.len()), 0);
        for (s, &off) in sections.iter().zip(&offsets) {
            out.resize(off, 0);
            out.extend(&s.bytes);
            out.resize(align8(out.len()), 0)
        }
        out.resize(cursor, 0);
        Ok(out)
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, DecodeError> {
        Self::decode_impl(bytes, true, None).map(|decoded| decoded.tables.into_artifact())
    }

    /// Decode a compiler-development snapshot while preserving its explicit
    /// pre-final register types. Ordinary G1 artifacts omit these types and
    /// infer them from instructions; a pre-oracle snapshot can still contain
    /// intentionally ambiguous conversion temporaries, so replay supplies the
    /// compiler's table as checked constraints rather than weakening normal
    /// decoding.
    pub fn decode_with_register_type_hints(
        bytes: &[u8],
        register_types: &[Vec<TypeId>],
    ) -> Result<Self, DecodeError> {
        Self::decode_impl(bytes, true, Some(register_types))
            .map(|decoded| decoded.tables.into_artifact())
    }

    pub(crate) fn decode_internal(bytes: &[u8]) -> Result<DecodedArtifact, DecodeError> {
        Self::decode_impl(bytes, false, None)
    }

    fn decode_impl(
        bytes: &[u8],
        materialize_constant_payloads: bool,
        register_type_hints: Option<&[Vec<TypeId>]>,
    ) -> Result<DecodedArtifact, DecodeError> {
        if bytes.len() < HEADER_LEN {
            return Err(DecodeError::Truncated);
        }
        if &bytes[..8] != MAGIC {
            return Err(DecodeError::BadMagic);
        }
        let mut h = Reader::new(&bytes[8..64]);
        let major = h.u16()?;
        if major != 1 {
            return Err(DecodeError::UnsupportedMajor(major));
        }
        let minor = h.u16()?;
        if minor != 0 {
            return Err(DecodeError::InvalidHeader);
        }
        if h.u32() != Ok(64) {
            return Err(DecodeError::InvalidHeader);
        }
        let flags = h.u32()?;
        let count = h.u32()?;
        if h.u32() != Ok(32) {
            return Err(DecodeError::InvalidHeader);
        }
        let entry = h.u32()?;
        let lo = h.u64()?;
        let hi = h.u64()?;
        let dir = h.u64()?;
        let file = h.u64()?;
        if flags & !EXECUTABLE != 0
            || (flags & EXECUTABLE != 0) != (entry != NONE32)
            || dir != 64
            || file as usize != bytes.len()
            || lo & CORE_G1 == 0
            || lo & !Self::SUPPORTED_FEATURES != 0
            || hi != 0
        {
            return Err(if lo & !Self::SUPPORTED_FEATURES != 0 || hi != 0 {
                DecodeError::UnsupportedFeatures {
                    lo: lo & !Self::SUPPORTED_FEATURES,
                    hi,
                }
            } else {
                DecodeError::InvalidHeader
            });
        }
        if count < 14 || count as usize > (bytes.len() - 64) / 32 {
            return Err(DecodeError::InvalidDirectory);
        }
        let mut d = Reader::new(&bytes[64..]);
        let mut sections = BTreeMap::new();
        let mut prev = 0;
        let mut placement = align8(64 + count as usize * 32);
        for _ in 0..count {
            let id = d.u32()?;
            let fl = d.u32()?;
            let off = d.u64()? as usize;
            let len = d.u64()? as usize;
            let ec = d.u32()?;
            let width = d.u32()?;
            if id <= prev {
                return Err(if id == prev {
                    DecodeError::DuplicateSection(id)
                } else {
                    DecodeError::InvalidDirectory
                });
            }
            prev = id;
            if fl & !CRITICAL != 0
                || off != placement
                || off.checked_add(len).is_none_or(|x| x > bytes.len())
            {
                return Err(DecodeError::InvalidDirectory);
            }
            let end = off + len;
            let padded = checked_align8(end)
                .filter(|&padded| padded <= bytes.len())
                .ok_or(DecodeError::InvalidDirectory)?;
            if bytes[end..padded].iter().any(|&x| x != 0) {
                return Err(DecodeError::NonCanonical("nonzero padding".into()));
            }
            placement = padded;
            if id <= 14 {
                if fl != CRITICAL {
                    return Err(DecodeError::InvalidDirectory);
                }
                sections.insert(id, (&bytes[off..end], ec, width));
            } else if id == 15 || fl & CRITICAL != 0 {
                return Err(DecodeError::UnknownCriticalSection(id));
            }
        }
        if placement != bytes.len() {
            return Err(DecodeError::InvalidDirectory);
        }
        for id in 1..=14 {
            if !sections.contains_key(&id) {
                return Err(DecodeError::MissingSection(id));
            }
        }
        let (sb, sc, sw) = sections[&1];
        if sw != 0 {
            return Err(DecodeError::InvalidTable("strings"));
        }
        let (strings, string_ranges) = decode_strings(sb, sc, bytes)?;
        let (gb, gc, gw) = sections[&4];
        if gw != 0 {
            return Err(DecodeError::InvalidTable("signatures"));
        }
        let signatures = decode_signatures(gb, gc)?;
        let imports = decode_imports(sections[&5].0, &strings, &signatures)?;
        let protocols = decode_protocols(sections[&6].0, sections[&6].1, &strings, &signatures)?;
        let handler_defs = decode_handler_defs(sections[&7].0, sections[&7].1, &signatures)?;
        let drop_glue = decode_drop_glue(
            sections[&13].0,
            sections[&13].1,
            sections[&2].1 as usize,
            sections[&8].1 as usize,
        )?;
        let dropped_types = drop_glue.iter().map(|glue| glue.ty).collect();
        let (tb, tc, tw) = sections[&2];
        if tw != 0 {
            return Err(DecodeError::InvalidTable("types"));
        }
        let types = decode_types(tb, tc, &strings, &signatures, &dropped_types)?;
        check_predefined(&types)?;
        let (cb, cc, cw) = sections[&3];
        if cw != 0 {
            return Err(DecodeError::InvalidTable("constants"));
        }
        let (constants, constant_payloads) = decode_constants(
            cb,
            cc,
            &strings,
            &string_ranges,
            bytes,
            materialize_constant_payloads,
        )?;
        for &(id, width) in &[
            (5, 24),
            (8, 64),
            (9, 4),
            (10, 4),
            (11, 24),
            (12, 16),
            (13, 16),
        ] {
            let (b, c, w) = sections[&id];
            if w != width || b.len() != c as usize * width as usize {
                return Err(DecodeError::InvalidTable("fixed section"));
            }
        }
        for id in [6, 7] {
            let (b, c, w) = sections[&id];
            if w != 0 {
                return Err(DecodeError::InvalidTable("variable section"));
            }
            let records = decode_var(b)?;
            if records.len() != c as usize {
                return Err(DecodeError::InvalidTable("variable section"));
            }
        }
        let operands = decode_words(sections[&10].0)?;
        let code_words = decode_words(sections[&9].0)?;
        // Every inferred register must occur either in a signature/receiver or
        // in an encoded code/operand word. Bound the temporary register table
        // by that representation size before allocating it; otherwise a tiny
        // hostile artifact can request a multi-gigabyte zero-filled vector.
        let max_registers = signatures
            .iter()
            .try_fold(1usize, |total, signature| {
                total.checked_add(signature.params.len())
            })
            .and_then(|total| total.checked_add(code_words.len()))
            .and_then(|total| total.checked_add(operands.len()))
            .ok_or(DecodeError::InvalidTable("function registers"))?;
        let decoded_functions =
            decode_functions(sections[&8].0, &strings, &signatures, &types, max_registers)?;
        let mut functions = Vec::with_capacity(decoded_functions.len());
        let mut cleanup_ranges = Vec::with_capacity(decoded_functions.len());
        let mut code = Vec::new();
        let mut abort_messages = Vec::new();
        let mut next_word = 0usize;
        for (mut f, instruction_count, cleanup_start, cleanup_count) in decoded_functions {
            let word_start = f.code_start as usize;
            let word_end = word_start
                .checked_add(f.code_len as usize)
                .ok_or(DecodeError::InvalidTable("function code"))?;
            if word_start != next_word {
                return Err(DecodeError::InvalidTable(
                    "overlapping or unordered function code",
                ));
            }
            let words = code_words
                .get(word_start..word_end)
                .ok_or(DecodeError::InvalidTable("function code"))?;
            let ordinal_start = code.len() as u32;
            let (decoded, decoded_abort_messages) = decode_instructions_with_messages(
                words,
                &operands,
                &strings,
                &string_ranges,
                materialize_constant_payloads,
            )?;
            if decoded.len() as u32 != instruction_count {
                return Err(DecodeError::InvalidTable("function instruction count"));
            }
            f.code_start = ordinal_start;
            f.code_len = decoded.len() as u32;
            code.extend(decoded);
            abort_messages.extend(decoded_abort_messages);
            functions.push(f);
            cleanup_ranges.push((cleanup_start, cleanup_count));
            next_word = word_end;
        }
        if next_word != code_words.len() {
            return Err(DecodeError::InvalidTable("unclaimed code words"));
        }
        let (contract_bytes, contract_count, contract_width) = sections[&14];
        if contract_width != 0 {
            return Err(DecodeError::InvalidTable("reference return contracts"));
        }
        let reference_return_contracts =
            decode_reference_return_contracts(contract_bytes, contract_count, functions.len())?;
        let cleanups = decode_cleanups(
            sections[&11].0,
            sections[&11].1,
            &operands,
            &functions,
            &cleanup_ranges,
        )?;
        infer_register_types(
            &types,
            &constants,
            &protocols,
            &handler_defs,
            &imports,
            &mut functions,
            &code,
            register_type_hints,
        )?;
        let exports = decode_exports(sections[&12].0, &strings, &signatures, &functions)?;
        validate_function_metadata(&functions, &exports, &drop_glue)?;
        if used_features(&types, &code, !protocols.is_empty(), !imports.is_empty()) != lo {
            return Err(DecodeError::NonCanonical(
                "required feature bits do not exactly describe the artifact".into(),
            ));
        }
        let tables = DecodedTables {
            required_features: lo,
            entry_function: (entry != NONE32).then_some(entry),
            types,
            constants,
            imports,
            protocols,
            handler_defs,
            cleanups,
            exports,
            drop_glue,
            reference_return_contracts,
            functions,
            code,
        };
        validate_canonical_metadata(
            &tables.protocols,
            &tables.handler_defs,
            &tables.types,
            &tables.functions,
            &tables.imports,
            &tables.exports,
        )?;
        Ok(DecodedArtifact {
            tables,
            constant_payloads,
            abort_messages,
            strings: strings.into_iter().zip(string_ranges).collect(),
        })
    }
}

fn validate_canonical_metadata(
    protocols: &[Protocol],
    handler_defs: &[HandlerDef],
    types: &[Type],
    functions: &[Function],
    imports: &[Import],
    exports: &[Export],
) -> Result<(), DecodeError> {
    fn valid_row(signature: &Signature, protocol_count: usize) -> bool {
        signature
            .outward_protocols
            .iter()
            .all(|protocol| (*protocol as usize) < protocol_count)
            && signature
                .outward_protocols
                .windows(2)
                .all(|pair| pair[0] < pair[1])
    }

    if !protocols.windows(2).all(|pair| {
        (&pair[0].display_name, &pair[0].type_arguments)
            < (&pair[1].display_name, &pair[1].type_arguments)
    }) {
        return Err(DecodeError::NonCanonical(
            "protocol identities must be sorted and unique".into(),
        ));
    }
    for protocol in protocols {
        if protocol
            .type_arguments
            .iter()
            .any(|argument| *argument as usize >= types.len())
        {
            return Err(DecodeError::InvalidTable("protocol type argument"));
        }
        if protocol
            .operations
            .iter()
            .any(|operation| !valid_row(&operation.payload_signature, protocols.len()))
        {
            return Err(DecodeError::NonCanonical(
                "protocol operation outward protocol row".into(),
            ));
        }
    }
    if functions.iter().any(|function| {
        !valid_row(
            &Signature {
                params: Vec::new(),
                result: UNIT,
                outward_protocols: function.outward_protocols.clone(),
            },
            protocols.len(),
        )
    }) {
        return Err(DecodeError::NonCanonical(
            "function outward protocol row".into(),
        ));
    }
    for ty in types {
        let signature = match ty.representation() {
            Type::Callable { signature, .. } => Some(signature),
            Type::Resumption {
                effect_signature, ..
            } => Some(effect_signature),
            _ => None,
        };
        if signature.is_some_and(|signature| !valid_row(signature, protocols.len())) {
            return Err(DecodeError::NonCanonical(
                "type signature outward protocol row".into(),
            ));
        }
    }
    if handler_defs.iter().any(|definition| {
        definition
            .clauses
            .iter()
            .any(|clause| !valid_row(&clause.callable_signature, protocols.len()))
    }) {
        return Err(DecodeError::NonCanonical(
            "handler clause outward protocol row".into(),
        ));
    }
    if imports
        .iter()
        .map(|import| &import.signature)
        .chain(exports.iter().map(|export| &export.signature))
        .any(|signature| !valid_row(signature, protocols.len()))
    {
        return Err(DecodeError::NonCanonical(
            "import or export outward protocol row".into(),
        ));
    }
    Ok(())
}

fn validate_function_metadata(
    functions: &[Function],
    exports: &[Export],
    drop_glue: &[DropGlue],
) -> Result<(), DecodeError> {
    for (id, function) in functions.iter().enumerate() {
        if function.flags & !FUNCTION_FLAGS != 0 {
            return Err(DecodeError::InvalidTable("function flags"));
        }
        let exported = exports.iter().any(|export| export.function as usize == id);
        if (function.flags & EXPORTED != 0) != exported {
            return Err(DecodeError::InvalidTable("EXPORTED flag"));
        }
        let drop_hook = drop_glue.iter().any(|glue| glue.function as usize == id);
        if (function.flags & DROP_HOOK != 0) != drop_hook {
            return Err(DecodeError::InvalidTable("DROP_HOOK flag"));
        }
    }
    Ok(())
}

pub(crate) fn used_features(
    types: &[Type],
    code: &[Instruction],
    has_protocols: bool,
    has_imports: bool,
) -> u64 {
    let mut features = CORE_G1;
    if types.iter().any(|ty| {
        matches!(
            ty.representation(),
            Type::RefShared { .. } | Type::RefUnique { .. }
        )
    }) || code.iter().any(|instruction| {
        matches!(
            instruction,
            Instruction::BorrowShared { .. }
                | Instruction::BorrowUnique { .. }
                | Instruction::ReborrowShared { .. }
                | Instruction::ReborrowUnique { .. }
                | Instruction::EndBorrow { .. }
                | Instruction::ProjectBorrowShared { .. }
                | Instruction::ProjectBorrowUnique { .. }
                | Instruction::DerefCopy { .. }
                | Instruction::DerefMove { .. }
                | Instruction::DerefStore { .. }
        )
    }) {
        features |= REFERENCES_G1;
    }
    if code.iter().any(|instruction| {
        matches!(
            instruction,
            Instruction::Primitive {
                op: Primitive::ArrayCapacity | Primitive::ArrayReserve,
                ..
            }
        )
    }) {
        features |= ARRAY_RESERVE_G1;
    }
    if code.iter().any(|instruction| {
        matches!(
            instruction,
            Instruction::Primitive {
                op: Primitive::ArrayFinishDrained,
                ..
            }
        )
    }) {
        features |= ARRAY_FINISH_DRAINED_G1;
    }
    if code.iter().any(|instruction| {
        matches!(
            instruction,
            Instruction::Primitive {
                op: Primitive::BytesUtf8ValidUpTo,
                ..
            }
        )
    }) {
        features |= BYTES_UTF8_VALID_UP_TO_G1;
    }
    if code.iter().any(|instruction| {
        matches!(
            instruction,
            Instruction::LabelPush { .. }
                | Instruction::LabelPop { .. }
                | Instruction::Leave { .. }
        )
    }) {
        features |= LABELS_G1;
    }
    if has_protocols
        || types.iter().any(|ty| {
            matches!(
                ty.representation(),
                Type::Handler { .. }
                    | Type::Resumption {
                        upper_uses: Some(0 | 1),
                        ..
                    }
            )
        })
        || code.iter().any(|instruction| {
            matches!(
                instruction,
                Instruction::MakeHandler { .. }
                    | Instruction::MakeHandlerShared { .. }
                    | Instruction::Handle { .. }
                    | Instruction::Perform { .. }
                    | Instruction::Resume { .. }
                    | Instruction::TailResume { .. }
                    | Instruction::Cancel { .. }
            )
        })
    {
        features |= HANDLERS_G1;
    }
    if types.iter().any(|ty| {
        matches!(
            ty.representation(),
            Type::Resumption {
                upper_uses: None,
                ..
            }
        ) || matches!(ty.representation(), Type::Resumption { upper_uses: Some(upper), .. } if *upper > 1)
    }) {
        features |= MULTISHOT_G1;
    }
    if has_imports {
        features |= HOST_ABI_G1;
    }
    features
}

type Sig = Signature;
fn encode_strings(xs: &[String]) -> Vec<u8> {
    let mut w = Vec::new();
    put_u32(&mut w, xs.len() as u32);
    put_u32(&mut w, xs.iter().map(|x| x.len()).sum::<usize>() as u32);
    let mut at = 0;
    put_u32(&mut w, 0);
    for x in xs {
        at += x.len();
        put_u32(&mut w, at as u32)
    }
    for x in xs {
        w.extend(x.as_bytes())
    }
    w
}
fn decode_strings(
    b: &[u8],
    count: u32,
    encoded: &[u8],
) -> Result<(Vec<String>, Vec<Range<usize>>), DecodeError> {
    let mut r = Reader::new(b);
    if r.u32() != Ok(count) {
        return Err(DecodeError::InvalidTable("strings"));
    }
    let n = r.u32()? as usize;
    let mut offs = Vec::new();
    for _ in 0..=count {
        offs.push(r.u32()? as usize)
    }
    if offs.first() != Some(&0) || offs.last() != Some(&n) || offs.windows(2).any(|x| x[0] > x[1]) {
        return Err(DecodeError::InvalidTable("strings"));
    }
    let data = r.take(n)?;
    r.finish()?;
    let data_start = data.as_ptr() as usize - encoded.as_ptr() as usize;
    let mut out = Vec::new();
    let mut ranges = Vec::new();
    for x in offs.windows(2) {
        out.push(
            std::str::from_utf8(&data[x[0]..x[1]])
                .map_err(|_| DecodeError::InvalidUtf8)?
                .to_owned(),
        );
        ranges.push(data_start + x[0]..data_start + x[1]);
    }
    if out.windows(2).any(|x| x[0].as_bytes() >= x[1].as_bytes()) {
        return Err(DecodeError::NonCanonical("string order".into()));
    }
    Ok((out, ranges))
}
fn record(tag: u8, flags: u8, payload: Vec<u8>) -> Vec<u8> {
    let mut w = vec![tag, flags, 0, 0];
    put_u32(&mut w, payload.len() as u32);
    w.extend(payload);
    w
}
fn var_section(records: &[Vec<u8>]) -> Vec<u8> {
    let mut w = Vec::new();
    put_u32(&mut w, records.len() as u32);
    let mut at = 0;
    put_u32(&mut w, 0);
    for r in records {
        at += r.len();
        put_u32(&mut w, at as u32)
    }
    for r in records {
        w.extend(r)
    }
    w
}
type RawRecord<'a> = (u8, u8, &'a [u8]);
fn decode_var(b: &[u8]) -> Result<Vec<RawRecord<'_>>, DecodeError> {
    let mut r = Reader::new(b);
    let n = r.u32()? as usize;
    let mut off = Vec::new();
    for _ in 0..=n {
        off.push(r.u32()? as usize)
    }
    let data = r.take(r.bytes.len() - r.at)?;
    if off.first() != Some(&0)
        || off.last() != Some(&data.len())
        || off.windows(2).any(|x| x[0] >= x[1]) && !off.is_empty()
    {
        if n == 0 && off == [0] {
        } else {
            return Err(DecodeError::InvalidTable("variable records"));
        }
    }
    let mut out = Vec::new();
    for x in off.windows(2) {
        let mut q = Reader::new(&data[x[0]..x[1]]);
        let tag = q.u8()?;
        let flags = q.u8()?;
        if q.u16() != Ok(0) {
            return Err(DecodeError::InvalidTable("record"));
        }
        let len = q.u32()? as usize;
        let p = q.take(len)?;
        q.finish()?;
        out.push((tag, flags, p))
    }
    Ok(out)
}
fn scalar_tag(t: &Type) -> Option<u8> {
    Some(match t.representation() {
        Type::Unit => 0,
        Type::Never => 1,
        Type::U8 => 2,
        Type::U16 => 3,
        Type::U32 => 4,
        Type::U64 => 5,
        Type::U128 => 6,
        Type::I8 => 7,
        Type::I16 => 8,
        Type::I32 => 9,
        Type::I64 => 10,
        Type::I128 => 11,
        Type::Usize => 12,
        Type::Isize => 13,
        Type::F32 => 14,
        Type::F64 => 15,
        Type::Char => 16,
        Type::Text => 17,
        Type::Bytes => 18,
        _ => return None,
    })
}
fn scalar_flags(tag: u8) -> u8 {
    if tag == 0 {
        DUPLICABLE | ZERO_SIZED | ZERO_USE_ALLOWED
    } else if tag == 1 {
        ZERO_SIZED
    } else {
        DUPLICABLE | ZERO_USE_ALLOWED
    }
}

/// Returns whether the runtime representation carries no state. Owned cycles
/// are invalid independently; treating one as non-zero here keeps malformed
/// artifacts from recursing while their cycle is reported by the verifier.
fn zero_sized_type(types: &[Type], id: TypeId, visiting: &mut [bool]) -> bool {
    let Some(ty) = types.get(id as usize) else {
        return false;
    };
    if visiting[id as usize] {
        return false;
    }
    visiting[id as usize] = true;
    let result = match ty.representation() {
        Type::Unit | Type::Never | Type::Available { .. } => true,
        Type::Tuple { fields, .. } => fields
            .iter()
            .all(|&field| zero_sized_type(types, field, visiting)),
        Type::Struct { fields, .. } => fields
            .iter()
            .all(|field| zero_sized_type(types, field.ty, visiting)),
        // An uninhabited enum and a single-variant enum need no discriminant.
        // Two or more variants always carry a runtime tag, even when every
        // variant payload is empty.
        Type::Enum { variants, .. } => {
            variants.len() <= 1
                && variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .all(|field| zero_sized_type(types, field.ty, visiting))
        }
        // Binding packs are opaque identities but have their payload layout.
        Type::BindingPack { payload_type, .. } => zero_sized_type(types, *payload_type, visiting),
        _ => false,
    };
    visiting[id as usize] = false;
    result
}

fn zero_sized_types(types: &[Type]) -> Vec<bool> {
    (0..types.len())
        .map(|id| zero_sized_type(types, id as TypeId, &mut vec![false; types.len()]))
        .collect()
}
fn encode_types(
    ts: &[Type],
    names: &BTreeMap<String, u32>,
    signatures: &[Signature],
    dropped_types: &std::collections::BTreeSet<TypeId>,
) -> Result<Vec<u8>, DecodeError> {
    let mut rs = Vec::new();
    let zero_sized = zero_sized_types(ts);
    for (type_id, declared_type) in ts.iter().enumerate() {
        let t = declared_type.representation();
        if let Some(tag) = scalar_tag(t) {
            rs.push(record(tag, scalar_flags(tag), vec![]))
        } else if let Type::Tuple { fields, copy } = t {
            let mut p = Vec::new();
            put_u32(&mut p, fields.len() as u32);
            for &ty in fields {
                put_u32(&mut p, ty);
            }
            rs.push(record(0x20, if *copy { 1 } else { 0 }, p))
        } else if let Type::Struct { name, fields, copy } = t {
            let mut p = Vec::new();
            put_u32(&mut p, names[name]);
            put_u32(&mut p, fields.len() as u32);
            for field in fields {
                put_u32(&mut p, names[&field.name]);
                put_u32(&mut p, field.ty)
            }
            rs.push(record(0x22, if *copy { 1 } else { 0 }, p))
        } else if let Type::Enum {
            name,
            variants,
            copy,
        } = t
        {
            let mut p = Vec::new();
            put_u32(&mut p, names[name]);
            put_u32(&mut p, variants.len() as u32);
            for variant in variants {
                put_u32(&mut p, names[&variant.name]);
                put_u32(&mut p, variant.fields.len() as u32);
                for field in &variant.fields {
                    put_u32(&mut p, names[&field.name]);
                    put_u32(&mut p, field.ty);
                }
                // Emitted runtime tag: an explicit discriminant else `u32::MAX`
                // (the no-discriminant sentinel). `u32::MAX` is reserved: the
                // frontend rejects a source discriminant equal to it, so the
                // sentinel never collides with a real tag.
                put_u32(&mut p, variant.tag.unwrap_or(u32::MAX));
            }
            rs.push(record(0x23, if *copy { 1 } else { 0 }, p))
        } else if let Type::Array { element } = t {
            let mut p = Vec::new();
            put_u32(&mut p, *element);
            rs.push(record(0x21, 0x10, p))
        } else if let Type::RefShared { referent } = t {
            let mut p = Vec::new();
            put_u32(&mut p, *referent);
            rs.push(record(0x24, 0x11, p))
        } else if let Type::RefUnique { referent } = t {
            let mut p = Vec::new();
            put_u32(&mut p, *referent);
            rs.push(record(0x25, 0x10, p))
        } else if let Type::Callable {
            signature,
            capture_type,
            receiver_mode,
            identity_name,
            copy,
            ..
        } = t
        {
            let signature = signatures
                .iter()
                .position(|candidate| candidate == signature)
                .ok_or(DecodeError::InvalidTable("callable signature"))?;
            let mut p = Vec::new();
            put_u32(&mut p, signature as u32);
            put_u32(&mut p, *capture_type);
            put_u32(&mut p, *receiver_mode);
            put_u32(&mut p, names[identity_name]);
            rs.push(record(0x26, 0x04 | u8::from(*copy), p))
        } else if let Type::Handler {
            handler_def,
            capture_type,
            identity_name,
        } = t
        {
            let mut p = Vec::new();
            put_u32(&mut p, *handler_def);
            put_u32(&mut p, *capture_type);
            put_u32(&mut p, names[identity_name]);
            rs.push(record(0x27, 0x04, p))
        } else if let Type::Resumption {
            input_type,
            output_type,
            effect_signature,
            lower_uses,
            upper_uses,
            identity_name,
            copy,
        } = t
        {
            let mut p = Vec::new();
            put_u32(&mut p, *input_type);
            put_u32(&mut p, *output_type);
            put_u32(&mut p, signature_id(signatures, effect_signature)?);
            put_u32(&mut p, *lower_uses);
            put_u32(&mut p, u32::from(upper_uses.is_none()));
            put_u32(&mut p, upper_uses.unwrap_or(0));
            put_u32(&mut p, names[identity_name]);
            rs.push(record(0x28, 0x04 | u8::from(*copy), p))
        } else if let Type::BindingPack {
            payload_type,
            identity_name,
            copy,
        } = t
        {
            let mut p = Vec::new();
            put_u32(&mut p, *payload_type);
            put_u32(&mut p, names[identity_name]);
            rs.push(record(0x29, 0x04 | u8::from(*copy), p))
        } else if let Type::Available { identity_name } = t {
            let mut p = Vec::new();
            put_u32(&mut p, names[identity_name]);
            rs.push(record(0x2a, 0x06, p))
        } else {
            return Err(DecodeError::InvalidTable("types"));
        }
        let claims = (u8::from(declared_type.claimed_duplicable()) * DUPLICABLE)
            | (u8::from(declared_type.claimed_zero_use_allowed()) * ZERO_USE_ALLOWED);
        let flags = &mut rs.last_mut().expect("one record per type")[1];
        *flags = (*flags & !USE_CAPABILITY_FLAGS) | claims;
        if dropped_types.contains(&(type_id as TypeId)) {
            if scalar_tag(t).is_some() {
                return Err(DecodeError::InvalidTable("predefined type flags"));
            }
            rs.last_mut().expect("one record per type")[1] |= HAS_DROP;
        }
        if zero_sized[type_id] && scalar_tag(t).is_none() {
            rs.last_mut().expect("one record per type")[1] |= ZERO_SIZED;
        }
    }
    Ok(var_section(&rs))
}
fn decode_types(
    b: &[u8],
    count: u32,
    names: &[String],
    signatures: &[Signature],
    dropped_types: &std::collections::BTreeSet<TypeId>,
) -> Result<Vec<Type>, DecodeError> {
    let rs = decode_var(b)?;
    if rs.len() != count as usize {
        return Err(DecodeError::InvalidTable("types"));
    }
    if rs
        .iter()
        .skip(Type::predefined().len())
        .any(|(tag, _, _)| *tag <= 18)
    {
        return Err(DecodeError::NonCanonical(
            "predefined scalar type appears more than once".into(),
        ));
    }
    let mut structural_records = std::collections::BTreeSet::new();
    for &(tag, flags, payload) in &rs {
        if matches!(tag, 0x20 | 0x21 | 0x24 | 0x25)
            && !structural_records.insert((tag, flags, payload))
        {
            return Err(DecodeError::NonCanonical(
                "duplicate structural type encoding".into(),
            ));
        }
    }
    let mut out = Vec::new();
    let mut wire_flags = Vec::with_capacity(rs.len());
    for (type_id, (tag, mut flags, p)) in rs.into_iter().enumerate() {
        if flags & !TYPE_FLAGS != 0 {
            return Err(DecodeError::InvalidTable("type flags"));
        }
        if (flags & HAS_DROP != 0) != dropped_types.contains(&(type_id as TypeId)) {
            return Err(DecodeError::InvalidTable("HAS_DROP flag"));
        }
        if tag <= 18 && flags & HAS_DROP != 0 {
            return Err(DecodeError::InvalidTable("predefined type flags"));
        }
        flags &= !HAS_DROP;
        wire_flags.push(flags);
        if tag <= 18 {
            let expected = scalar_flags(tag);
            if flags & !USE_CAPABILITY_FLAGS != expected & !USE_CAPABILITY_FLAGS
                || flags & USE_CAPABILITY_FLAGS & !expected != 0
                || !p.is_empty()
            {
                return Err(DecodeError::InvalidTable("scalar type"));
            }
            out.push(Type::predefined().remove(tag as usize))
        } else if tag == 0x21 || tag == 0x24 || tag == 0x25 {
            let expected_flags = if tag == 0x24 { 0x11 } else { 0x10 };
            if flags & !USE_CAPABILITY_FLAGS != expected_flags & !USE_CAPABILITY_FLAGS
                || flags & USE_CAPABILITY_FLAGS & !expected_flags != 0
            {
                return Err(DecodeError::InvalidTable("type flags"));
            }
            let mut r = Reader::new(p);
            let target = r.u32()?;
            r.finish()?;
            out.push(match tag {
                0x21 => Type::Array { element: target },
                0x24 => Type::RefShared { referent: target },
                0x25 => Type::RefUnique { referent: target },
                _ => unreachable!(),
            })
        } else if tag == 0x20 {
            if flags & !(USE_CAPABILITY_FLAGS | ZERO_SIZED) != 0 {
                return Err(DecodeError::InvalidTable("tuple type"));
            }
            let mut r = Reader::new(p);
            let count = r.u32()?;
            let mut fields = Vec::new();
            for _ in 0..count {
                fields.push(r.u32()?);
            }
            r.finish()?;
            out.push(Type::Tuple {
                fields,
                copy: flags & 1 != 0,
            })
        } else if tag == 0x26 {
            if flags & !(USE_CAPABILITY_FLAGS | ZERO_SIZED) != OPAQUE {
                return Err(DecodeError::InvalidTable("callable type"));
            }
            let mut r = Reader::new(p);
            let signature = signatures
                .get(r.u32()? as usize)
                .ok_or(DecodeError::InvalidTable("callable signature"))?
                .clone();
            let capture_type = r.u32()?;
            let receiver_mode = r.u32()?;
            if receiver_mode > 2 {
                return Err(DecodeError::InvalidTable("callable receiver mode"));
            }
            let identity_name = names
                .get(r.u32()? as usize)
                .ok_or(DecodeError::InvalidTable("callable identity"))?
                .clone();
            r.finish()?;
            out.push(Type::Callable {
                signature,
                capture_type,
                receiver_mode,
                identity_name,
                copy: flags & 1 != 0,
                zero_use_allowed: flags & ZERO_USE_ALLOWED != 0,
            })
        } else if tag == 0x27 {
            if flags & !USE_CAPABILITY_FLAGS != OPAQUE || flags & DUPLICABLE != 0 {
                return Err(DecodeError::InvalidTable("handler type"));
            }
            let mut r = Reader::new(p);
            let handler_def = r.u32()?;
            let capture_type = r.u32()?;
            let identity_name = names
                .get(r.u32()? as usize)
                .ok_or(DecodeError::InvalidTable("handler identity"))?
                .clone();
            r.finish()?;
            out.push(Type::Handler {
                handler_def,
                capture_type,
                identity_name,
            })
        } else if tag == 0x28 {
            if flags & !(USE_CAPABILITY_FLAGS | ZERO_SIZED) != OPAQUE {
                return Err(DecodeError::InvalidTable("resumption type"));
            }
            let mut r = Reader::new(p);
            let input_type = r.u32()?;
            let output_type = r.u32()?;
            let effect_signature = signatures
                .get(r.u32()? as usize)
                .ok_or(DecodeError::InvalidTable("resumption signature"))?
                .clone();
            let lower_uses = r.u32()?;
            let upper_kind = r.u32()?;
            let upper_raw = r.u32()?;
            let identity_name = names
                .get(r.u32()? as usize)
                .ok_or(DecodeError::InvalidTable("resumption identity"))?
                .clone();
            r.finish()?;
            let upper_uses = match (upper_kind, upper_raw) {
                (0, upper) => Some(upper),
                (1, 0) => None,
                _ => return Err(DecodeError::InvalidTable("resumption quantity")),
            };
            out.push(Type::Resumption {
                input_type,
                output_type,
                effect_signature,
                lower_uses,
                upper_uses,
                identity_name,
                copy: flags & 1 != 0,
            })
        } else if tag == 0x29 {
            if flags & !(USE_CAPABILITY_FLAGS | ZERO_SIZED) != OPAQUE {
                return Err(DecodeError::InvalidTable("binding pack type"));
            }
            let mut r = Reader::new(p);
            let payload_type = r.u32()?;
            let identity_name = names
                .get(r.u32()? as usize)
                .ok_or(DecodeError::InvalidTable("binding pack identity"))?
                .clone();
            r.finish()?;
            out.push(Type::BindingPack {
                payload_type,
                identity_name,
                copy: flags & 1 != 0,
            })
        } else if tag == 0x2a {
            if flags & !USE_CAPABILITY_FLAGS != OPAQUE | ZERO_SIZED || flags & DUPLICABLE != 0 {
                return Err(DecodeError::InvalidTable("available type"));
            }
            let mut r = Reader::new(p);
            let identity_name = names
                .get(r.u32()? as usize)
                .ok_or(DecodeError::InvalidTable("available identity"))?
                .clone();
            r.finish()?;
            out.push(Type::Available { identity_name })
        } else if tag == 0x22 || tag == 0x23 {
            if flags & !(USE_CAPABILITY_FLAGS | ZERO_SIZED) != 0 {
                return Err(DecodeError::InvalidTable("nominal type"));
            }
            let mut r = Reader::new(p);
            let name = names
                .get(r.u32()? as usize)
                .ok_or(DecodeError::InvalidTable("type name"))?
                .clone();
            let count = r.u32()?;
            if tag == 0x22 {
                let mut fields = Vec::new();
                for _ in 0..count {
                    let field_name = names
                        .get(r.u32()? as usize)
                        .ok_or(DecodeError::InvalidTable("field name"))?
                        .clone();
                    fields.push(Field {
                        name: field_name,
                        ty: r.u32()?,
                    });
                }
                r.finish()?;
                out.push(Type::Struct {
                    name,
                    fields,
                    copy: flags & 1 != 0,
                })
            } else {
                let mut variants = Vec::new();
                for _ in 0..count {
                    let variant_name = names
                        .get(r.u32()? as usize)
                        .ok_or(DecodeError::InvalidTable("variant name"))?
                        .clone();
                    let field_count = r.u32()?;
                    let mut fields = Vec::new();
                    for _ in 0..field_count {
                        let field_name = names
                            .get(r.u32()? as usize)
                            .ok_or(DecodeError::InvalidTable("field name"))?
                            .clone();
                        fields.push(Field {
                            name: field_name,
                            ty: r.u32()?,
                        });
                    }
                    let tag = r.u32()?;
                    let tag = (tag != u32::MAX).then_some(tag);
                    variants.push(EnumVariant {
                        name: variant_name,
                        fields,
                        tag,
                    });
                }
                r.finish()?;
                out.push(Type::Enum {
                    name,
                    variants,
                    copy: flags & 1 != 0,
                })
            }
        } else {
            return Err(DecodeError::UnsupportedType(tag));
        }
        let base = out.pop().expect("one decoded type per record");
        let wire_claims = flags & USE_CAPABILITY_FLAGS;
        let ordinary_claims = maximal_capability_flags(&base) & USE_CAPABILITY_FLAGS;
        out.push(if wire_claims == ordinary_claims {
            base
        } else {
            Type::Restricted {
                base: Box::new(base),
                duplicable: wire_claims & DUPLICABLE != 0,
                zero_use_allowed: wire_claims & ZERO_USE_ALLOWED != 0,
            }
        });
    }
    let derived_zero_sized = zero_sized_types(&out);
    for (&flags, &expected) in wire_flags.iter().zip(&derived_zero_sized) {
        if (flags & ZERO_SIZED != 0) != expected {
            return Err(DecodeError::InvalidTable("ZERO_SIZED flag"));
        }
        // Scalars were checked against their exact mandated flags above. For
        // all other records OPAQUE and ZERO_USE_ALLOWED are constrained by the
        // tag-specific checks, and HAS_DROP was checked against DROP_GLUE.
    }
    Ok(out)
}
fn check_predefined(ts: &[Type]) -> Result<(), DecodeError> {
    let p = Type::predefined();
    if ts.len() < p.len()
        || ts
            .iter()
            .zip(&p)
            .take(p.len())
            .any(|(actual, expected)| actual.representation() != expected)
    {
        return Err(DecodeError::NonCanonical(
            "predefined scalar type IDs 0..18".into(),
        ));
    }
    Ok(())
}
fn constant_tag(c: &Constant) -> u8 {
    match c {
        Constant::Unit => 0,
        Constant::U8(_) => 2,
        Constant::U16(_) => 3,
        Constant::U32(_) => 4,
        Constant::U64(_) => 5,
        Constant::U128(_) => 6,
        Constant::I8(_) => 7,
        Constant::I16(_) => 8,
        Constant::I32(_) => 9,
        Constant::I64(_) => 10,
        Constant::I128(_) => 11,
        Constant::Usize(_) => 12,
        Constant::Isize(_) => 13,
        Constant::F32(_) => 14,
        Constant::F64(_) => 15,
        Constant::Char(_) => 16,
        Constant::Text(_) => 17,
        Constant::Bytes(_) => 18,
    }
}

fn artifact_name_ids(artifact: &Artifact) -> BTreeMap<String, u32> {
    let mut names = Vec::new();
    for function in &artifact.functions {
        names.push(function.name.clone());
    }
    for import in &artifact.imports {
        names.push(import.capability.clone());
        names.push(import.symbol.clone());
    }
    names.extend(artifact.exports.iter().map(|export| export.name.clone()));
    for ty in &artifact.types {
        match ty.representation() {
            Type::Struct { name, fields, .. } => {
                names.push(name.clone());
                names.extend(fields.iter().map(|field| field.name.clone()));
            }
            Type::Enum { name, variants, .. } => {
                names.push(name.clone());
                for variant in variants {
                    names.push(variant.name.clone());
                    names.extend(variant.fields.iter().map(|field| field.name.clone()));
                }
            }
            Type::Callable { identity_name, .. } => names.push(identity_name.clone()),
            Type::Handler { identity_name, .. } => names.push(identity_name.clone()),
            Type::Resumption { identity_name, .. } => names.push(identity_name.clone()),
            Type::BindingPack { identity_name, .. } | Type::Available { identity_name } => {
                names.push(identity_name.clone());
            }
            _ => {}
        }
    }
    for protocol in &artifact.protocols {
        names.push(protocol.display_name.clone());
        names.extend(
            protocol
                .operations
                .iter()
                .map(|operation| operation.name.clone()),
        );
    }
    for constant in &artifact.constants {
        if let Constant::Text(text) = constant {
            names.push(text.clone());
        }
    }
    for instruction in &artifact.code {
        if let Instruction::Abort {
            message: Some(message),
        } = instruction
        {
            names.push(message.clone());
        }
    }
    names.sort_by(|left, right| left.as_bytes().cmp(right.as_bytes()));
    names.dedup();
    names
        .into_iter()
        .enumerate()
        .map(|(index, name)| (name, index as u32))
        .collect()
}

fn constant_wire_key(c: &Constant, names: &BTreeMap<String, u32>) -> (u8, Vec<u8>) {
    let mut payload = Vec::new();
    match c {
        Constant::Unit => {}
        Constant::U8(x) => payload.push(*x),
        Constant::U16(x) => put_u16(&mut payload, *x),
        Constant::U32(x) => put_u32(&mut payload, *x),
        Constant::U64(x) => put_u64(&mut payload, *x),
        Constant::U128(x) => payload.extend(x.to_le_bytes()),
        Constant::I8(x) => payload.push(*x as u8),
        Constant::I16(x) => put_u16(&mut payload, *x as u16),
        Constant::I32(x) => put_u32(&mut payload, *x as u32),
        Constant::I64(x) | Constant::Isize(x) => put_u64(&mut payload, *x as u64),
        Constant::I128(x) => payload.extend(x.to_le_bytes()),
        Constant::Usize(x) => put_u64(&mut payload, *x),
        Constant::F32(x) => put_u32(
            &mut payload,
            if x.is_nan() { 0x7fc00000 } else { x.to_bits() },
        ),
        Constant::F64(x) => put_u64(
            &mut payload,
            if x.is_nan() {
                0x7ff8000000000000
            } else {
                x.to_bits()
            },
        ),
        Constant::Char(x) => put_u32(&mut payload, *x as u32),
        Constant::Text(x) => put_u32(&mut payload, names[x]),
        Constant::Bytes(x) => {
            put_u32(&mut payload, x.len() as u32);
            payload.extend(x);
        }
    }
    (constant_tag(c), payload)
}

fn encode_constants(
    cs: &[Constant],
    names: &BTreeMap<String, u32>,
) -> Result<Vec<u8>, DecodeError> {
    let mut rs = Vec::new();
    let mut prior = None;
    for c in cs {
        let key = constant_wire_key(c, names);
        if prior.as_ref().is_some_and(|x| x >= &key) {
            return Err(DecodeError::NonCanonical("constant order".into()));
        }
        prior = Some(key.clone());
        rs.push(record(key.0, 0, key.1))
    }
    Ok(var_section(&rs))
}
fn decode_constants(
    b: &[u8],
    count: u32,
    names: &[String],
    name_ranges: &[Range<usize>],
    encoded: &[u8],
    materialize_payloads: bool,
) -> Result<(Vec<Constant>, Vec<Option<EncodedConstantPayload>>), DecodeError> {
    let rs = decode_var(b)?;
    if rs.len() != count as usize {
        return Err(DecodeError::InvalidTable("constants"));
    }
    let mut out = Vec::new();
    let mut payloads = Vec::new();
    let mut prior = None;
    for (tag, flags, p) in rs {
        if flags != 0
            || prior
                .as_ref()
                .is_some_and(|x: &(u8, Vec<u8>)| x >= &(tag, p.to_vec()))
        {
            return Err(DecodeError::NonCanonical("constant order".into()));
        }
        prior = Some((tag, p.to_vec()));
        let mut r = Reader::new(p);
        let mut encoded_payload = None;
        let c = match tag {
            0 => Constant::Unit,
            2 => Constant::U8(r.u8()?),
            3 => Constant::U16(r.u16()?),
            4 => Constant::U32(r.u32()?),
            5 => Constant::U64(r.u64()?),
            6 => Constant::U128(u128::from_le_bytes(r.take(16)?.try_into().unwrap())),
            7 => Constant::I8(r.u8()? as i8),
            8 => Constant::I16(r.u16()? as i16),
            9 => Constant::I32(r.u32()? as i32),
            10 => Constant::I64(r.u64()? as i64),
            11 => Constant::I128(i128::from_le_bytes(r.take(16)?.try_into().unwrap())),
            12 => Constant::Usize(r.u64()?),
            13 => Constant::Isize(r.u64()? as i64),
            14 => {
                let x = r.u32()?;
                if f32::from_bits(x).is_nan() && x != 0x7fc00000 {
                    return Err(DecodeError::NonCanonical("NaN".into()));
                }
                Constant::F32(f32::from_bits(x))
            }
            15 => {
                let x = r.u64()?;
                if f64::from_bits(x).is_nan() && x != 0x7ff8000000000000 {
                    return Err(DecodeError::NonCanonical("NaN".into()));
                }
                Constant::F64(f64::from_bits(x))
            }
            16 => Constant::Char(
                char::from_u32(r.u32()?).ok_or(DecodeError::InvalidTable("character constant"))?,
            ),
            17 => {
                let name = r.u32()? as usize;
                encoded_payload = Some(EncodedConstantPayload::Text(
                    name_ranges
                        .get(name)
                        .ok_or(DecodeError::InvalidTable("text constant"))?
                        .clone(),
                ));
                Constant::Text(if materialize_payloads {
                    names
                        .get(name)
                        .ok_or(DecodeError::InvalidTable("text constant"))?
                        .clone()
                } else {
                    String::new()
                })
            }
            18 => {
                let n = r.u32()? as usize;
                let bytes = r.take(n)?;
                let start = bytes.as_ptr() as usize - encoded.as_ptr() as usize;
                encoded_payload = Some(EncodedConstantPayload::Bytes(start..start + n));
                Constant::Bytes(if materialize_payloads {
                    bytes.to_vec()
                } else {
                    Vec::new()
                })
            }
            _ => return Err(DecodeError::InvalidTable("constant tag")),
        };
        r.finish()?;
        out.push(c);
        payloads.push(encoded_payload);
    }
    Ok((out, payloads))
}
fn collect_signatures(
    fs: &[Function],
    types: &[Type],
    protocols: &[Protocol],
    handler_defs: &[HandlerDef],
    imports: &[Import],
    exports: &[Export],
) -> (Vec<Signature>, Vec<u32>) {
    let mut unique: Vec<Signature> = Vec::new();
    let mut ids = Vec::new();
    for f in fs {
        let signature = Signature {
            params: f.params.clone(),
            result: f.return_type,
            outward_protocols: f.outward_protocols.clone(),
        };
        let id = unique
            .iter()
            .position(|candidate| candidate == &signature)
            .unwrap_or_else(|| {
                unique.push(signature);
                unique.len() - 1
            });
        ids.push(id as u32)
    }
    for ty in types {
        if let Type::Callable { signature, .. } = ty
            && !unique.contains(signature)
        {
            unique.push(signature.clone());
        }
        if let Type::Resumption {
            effect_signature, ..
        } = ty
            && !unique.contains(effect_signature)
        {
            unique.push(effect_signature.clone());
        }
    }
    for signature in protocols
        .iter()
        .flat_map(|protocol| &protocol.operations)
        .map(|operation| &operation.payload_signature)
        .chain(
            handler_defs
                .iter()
                .flat_map(|definition| &definition.clauses)
                .map(|clause| &clause.callable_signature),
        )
        .chain(imports.iter().map(|import| &import.signature))
        .chain(exports.iter().map(|export| &export.signature))
    {
        if !unique.contains(signature) {
            unique.push(signature.clone());
        }
    }
    (unique, ids)
}

fn encode_signatures(unique: &[Signature]) -> Vec<u8> {
    let rs: Vec<_> = unique
        .iter()
        .map(|s| {
            let mut p = Vec::new();
            put_u32(&mut p, s.params.len() as u32);
            put_u32(&mut p, s.result);
            put_u32(&mut p, s.outward_protocols.len() as u32);
            for &x in &s.params {
                put_u32(&mut p, x)
            }
            for &x in &s.outward_protocols {
                put_u32(&mut p, x)
            }
            record(0, 0, p)
        })
        .collect();
    var_section(&rs)
}
fn decode_signatures(b: &[u8], count: u32) -> Result<Vec<Sig>, DecodeError> {
    let rs = decode_var(b)?;
    if rs.len() != count as usize {
        return Err(DecodeError::InvalidTable("signatures"));
    }
    rs.into_iter()
        .map(|(tag, flags, p)| {
            if tag != 0 || flags != 0 {
                return Err(DecodeError::InvalidTable("signature"));
            }
            let mut r = Reader::new(p);
            let n = r.u32()?;
            let result = r.u32()?;
            let outward_count = r.u32()?;
            let mut params = Vec::new();
            for _ in 0..n {
                params.push(r.u32()?)
            }
            let mut outward_protocols = Vec::new();
            for _ in 0..outward_count {
                outward_protocols.push(r.u32()?);
            }
            r.finish()?;
            Ok(Sig {
                params,
                result,
                outward_protocols,
            })
        })
        .collect()
}

fn signature_id(signatures: &[Signature], signature: &Signature) -> Result<u32, DecodeError> {
    signatures
        .iter()
        .position(|candidate| candidate == signature)
        .map(|id| id as u32)
        .ok_or(DecodeError::InvalidTable("signature reference"))
}

fn encode_imports(
    imports: &[Import],
    names: &BTreeMap<String, u32>,
    signatures: &[Signature],
) -> Result<Vec<u8>, DecodeError> {
    let mut out = Vec::with_capacity(imports.len() * 24);
    let mut previous: Option<(&[u8], &[u8], u32)> = None;
    for import in imports {
        let signature = signature_id(signatures, &import.signature)?;
        let key = (
            import.capability.as_bytes(),
            import.symbol.as_bytes(),
            signature,
        );
        if previous.as_ref().is_some_and(|prior| prior >= &key) {
            return Err(DecodeError::NonCanonical(
                "imports must be sorted and unique".into(),
            ));
        }
        previous = Some(key);
        put_u32(&mut out, names[&import.capability]);
        put_u32(&mut out, names[&import.symbol]);
        put_u32(&mut out, signature);
        put_u32(&mut out, u32::from(import.may_trap));
        put_u64(&mut out, 0);
    }
    Ok(out)
}

fn decode_imports(
    bytes: &[u8],
    strings: &[String],
    signatures: &[Signature],
) -> Result<Vec<Import>, DecodeError> {
    if !bytes.len().is_multiple_of(24) {
        return Err(DecodeError::InvalidTable("imports"));
    }
    let mut imports = Vec::with_capacity(bytes.len() / 24);
    let mut previous: Option<(&[u8], &[u8], u32)> = None;
    for record in bytes.chunks_exact(24) {
        let mut reader = Reader::new(record);
        let capability = reader.u32()? as usize;
        let symbol = reader.u32()? as usize;
        let signature = reader.u32()?;
        let flags = reader.u32()?;
        let reserved = reader.u64()?;
        reader.finish()?;
        let capability = strings
            .get(capability)
            .ok_or(DecodeError::InvalidTable("import string"))?;
        let symbol = strings
            .get(symbol)
            .ok_or(DecodeError::InvalidTable("import string"))?;
        let definition = signatures
            .get(signature as usize)
            .ok_or(DecodeError::InvalidTable("import signature"))?;
        if flags & !1 != 0 || reserved != 0 {
            return Err(DecodeError::InvalidTable("import flags"));
        }
        let key = (capability.as_bytes(), symbol.as_bytes(), signature);
        if previous.as_ref().is_some_and(|prior| prior >= &key) {
            return Err(DecodeError::NonCanonical(
                "imports must be sorted and unique".into(),
            ));
        }
        previous = Some(key);
        imports.push(Import {
            capability: capability.clone(),
            symbol: symbol.clone(),
            signature: definition.clone(),
            may_trap: flags == 1,
        });
    }
    Ok(imports)
}

fn function_signature(function: &Function) -> Signature {
    Signature {
        params: function.params.clone(),
        result: function.return_type,
        outward_protocols: function.outward_protocols.clone(),
    }
}

fn encode_exports(
    exports: &[Export],
    functions: &[Function],
    names: &BTreeMap<String, u32>,
    signatures: &[Signature],
) -> Result<Vec<u8>, DecodeError> {
    let mut out = Vec::with_capacity(exports.len() * 16);
    let mut previous: Option<&[u8]> = None;
    for export in exports {
        if previous.is_some_and(|prior| prior >= export.name.as_bytes()) {
            return Err(DecodeError::NonCanonical(
                "exports must be sorted with unique names".into(),
            ));
        }
        previous = Some(export.name.as_bytes());
        let function = functions
            .get(export.function as usize)
            .ok_or(DecodeError::InvalidTable("export function"))?;
        if export.signature != function_signature(function) {
            return Err(DecodeError::InvalidTable("export signature"));
        }
        put_u32(&mut out, names[&export.name]);
        put_u32(&mut out, export.function);
        put_u32(&mut out, signature_id(signatures, &export.signature)?);
        put_u32(&mut out, 0);
    }
    Ok(out)
}

fn decode_exports(
    bytes: &[u8],
    strings: &[String],
    signatures: &[Signature],
    functions: &[Function],
) -> Result<Vec<Export>, DecodeError> {
    if !bytes.len().is_multiple_of(16) {
        return Err(DecodeError::InvalidTable("exports"));
    }
    let mut exports = Vec::with_capacity(bytes.len() / 16);
    let mut previous: Option<&[u8]> = None;
    for record in bytes.chunks_exact(16) {
        let mut reader = Reader::new(record);
        let name = reader.u32()? as usize;
        let function = reader.u32()?;
        let signature = reader.u32()?;
        let flags = reader.u32()?;
        reader.finish()?;
        let name = strings
            .get(name)
            .ok_or(DecodeError::InvalidTable("export string"))?;
        let signature = signatures
            .get(signature as usize)
            .ok_or(DecodeError::InvalidTable("export signature"))?;
        let function_definition = functions
            .get(function as usize)
            .ok_or(DecodeError::InvalidTable("export function"))?;
        if flags != 0 || signature != &function_signature(function_definition) {
            return Err(DecodeError::InvalidTable("export signature or flags"));
        }
        if previous.is_some_and(|prior| prior >= name.as_bytes()) {
            return Err(DecodeError::NonCanonical(
                "exports must be sorted with unique names".into(),
            ));
        }
        previous = Some(name.as_bytes());
        exports.push(Export {
            name: name.clone(),
            function,
            signature: signature.clone(),
        });
    }
    Ok(exports)
}

fn encode_drop_glue(
    entries: &[DropGlue],
    type_count: usize,
    functions: &[Function],
) -> Result<(Vec<u8>, std::collections::BTreeSet<TypeId>), DecodeError> {
    let mut out = Vec::with_capacity(entries.len() * 16);
    let mut types = std::collections::BTreeSet::new();
    for entry in entries {
        if entry.ty as usize >= type_count
            || entry.function as usize >= functions.len()
            || !types.insert(entry.ty)
        {
            return Err(DecodeError::InvalidTable("drop glue"));
        }
        put_u32(&mut out, entry.ty);
        put_u32(&mut out, entry.function);
        put_u32(&mut out, 0);
        put_u32(&mut out, 0);
    }
    if !entries.windows(2).all(|pair| pair[0].ty < pair[1].ty) {
        return Err(DecodeError::NonCanonical(
            "drop glue must be sorted by unique type".into(),
        ));
    }
    Ok((out, types))
}

fn decode_drop_glue(
    bytes: &[u8],
    count: u32,
    type_count: usize,
    function_count: usize,
) -> Result<Vec<DropGlue>, DecodeError> {
    let count = usize::try_from(count).map_err(|_| DecodeError::InvalidTable("drop glue"))?;
    let expected_len = count
        .checked_mul(16)
        .ok_or(DecodeError::InvalidTable("drop glue"))?;
    if bytes.len() != expected_len {
        return Err(DecodeError::InvalidTable("drop glue"));
    }
    let mut entries = Vec::with_capacity(count);
    for record in bytes.chunks_exact(16) {
        let mut reader = Reader::new(record);
        let ty = reader.u32()?;
        let function = reader.u32()?;
        if reader.u32()? != 0 || reader.u32()? != 0 {
            return Err(DecodeError::InvalidTable("drop glue flags"));
        }
        if ty as usize >= type_count || function as usize >= function_count {
            return Err(DecodeError::InvalidTable("drop glue target"));
        }
        entries.push(DropGlue { ty, function });
    }
    if !entries.windows(2).all(|pair| pair[0].ty < pair[1].ty) {
        return Err(DecodeError::NonCanonical(
            "drop glue must be sorted by unique type".into(),
        ));
    }
    Ok(entries)
}

fn encode_reference_return_contracts(
    contracts: &[ReferenceReturnContract],
    functions: &[Function],
) -> Result<Vec<u8>, DecodeError> {
    if !contracts
        .windows(2)
        .all(|pair| pair[0].function < pair[1].function)
    {
        return Err(DecodeError::NonCanonical(
            "reference return contracts must be sorted by unique function".into(),
        ));
    }
    let records = contracts
        .iter()
        .map(|contract| {
            if contract.function as usize >= functions.len()
                || contract.routes.is_empty()
                || !contract
                    .routes
                    .windows(2)
                    .all(|pair| pair[0].result_path < pair[1].result_path)
            {
                return Err(DecodeError::InvalidTable("reference return contract"));
            }
            let mut payload = Vec::new();
            put_u32(&mut payload, contract.function);
            put_u32(&mut payload, contract.routes.len() as u32);
            for route in &contract.routes {
                put_u32(&mut payload, route.result_path.len() as u32);
                for &field in &route.result_path {
                    put_u32(&mut payload, field);
                }
                match &route.origin {
                    ReferenceReturnOrigin::Parameter { parameter, path } => {
                        put_u32(&mut payload, 0);
                        put_u32(&mut payload, *parameter);
                        put_u32(&mut payload, path.len() as u32);
                        for &field in path {
                            put_u32(&mut payload, field);
                        }
                    }
                    ReferenceReturnOrigin::Receiver { path } => {
                        put_u32(&mut payload, 1);
                        put_u32(&mut payload, path.len() as u32);
                        for &field in path {
                            put_u32(&mut payload, field);
                        }
                    }
                }
            }
            Ok(record(0, 0, payload))
        })
        .collect::<Result<Vec<_>, DecodeError>>()?;
    Ok(var_section(&records))
}

fn decode_reference_return_contracts(
    bytes: &[u8],
    count: u32,
    function_count: usize,
) -> Result<Vec<ReferenceReturnContract>, DecodeError> {
    fn path(reader: &mut Reader<'_>) -> Result<Vec<u32>, DecodeError> {
        let count = reader.u32()? as usize;
        let byte_len = count
            .checked_mul(std::mem::size_of::<u32>())
            .ok_or(DecodeError::InvalidTable("reference return path"))?;
        let bytes = reader
            .take(byte_len)
            .map_err(|_| DecodeError::InvalidTable("reference return path"))?;
        Ok(bytes
            .chunks_exact(4)
            .map(|word| u32::from_le_bytes(word.try_into().unwrap()))
            .collect())
    }
    let records = decode_var(bytes)?;
    if records.len() != count as usize {
        return Err(DecodeError::InvalidTable("reference return contracts"));
    }
    let mut contracts = Vec::with_capacity(records.len());
    for (tag, flags, payload) in records {
        if tag != 0 || flags != 0 {
            return Err(DecodeError::InvalidTable("reference return contract"));
        }
        let mut reader = Reader::new(payload);
        let function = reader.u32()?;
        let route_count = reader.u32()? as usize;
        // Even an empty receiver-origin route needs a result-path count, an
        // origin tag, and an origin-path count. Bound the compact scalar by
        // bytes that are actually present before using it as a capacity.
        const MIN_ROUTE_BYTES: usize = 3 * std::mem::size_of::<u32>();
        if function as usize >= function_count
            || route_count == 0
            || route_count > reader.remaining() / MIN_ROUTE_BYTES
        {
            return Err(DecodeError::InvalidTable("reference return contract"));
        }
        let mut routes = Vec::with_capacity(route_count);
        for _ in 0..route_count {
            let result_path = path(&mut reader)?;
            let origin = match reader.u32()? {
                0 => ReferenceReturnOrigin::Parameter {
                    parameter: reader.u32()?,
                    path: path(&mut reader)?,
                },
                1 => ReferenceReturnOrigin::Receiver {
                    path: path(&mut reader)?,
                },
                _ => return Err(DecodeError::InvalidTable("reference return origin")),
            };
            routes.push(ReferenceReturnRoute {
                result_path,
                origin,
            });
        }
        reader.finish()?;
        contracts.push(ReferenceReturnContract { function, routes });
    }
    if !contracts
        .windows(2)
        .all(|pair| pair[0].function < pair[1].function)
        || contracts.iter().any(|contract| {
            !contract
                .routes
                .windows(2)
                .all(|pair| pair[0].result_path < pair[1].result_path)
        })
    {
        return Err(DecodeError::NonCanonical(
            "reference return contracts must be sorted and unique".into(),
        ));
    }
    Ok(contracts)
}

fn encode_protocols(
    protocols: &[Protocol],
    names: &BTreeMap<String, u32>,
    signatures: &[Signature],
) -> Result<Vec<u8>, DecodeError> {
    let records = protocols
        .iter()
        .map(|protocol| {
            let mut payload = Vec::new();
            put_u32(&mut payload, names[&protocol.display_name]);
            put_u32(&mut payload, protocol.type_arguments.len() as u32);
            for &argument in &protocol.type_arguments {
                put_u32(&mut payload, argument);
            }
            put_u32(&mut payload, protocol.operations.len() as u32);
            for operation in &protocol.operations {
                put_u32(&mut payload, names[&operation.name]);
                put_u32(
                    &mut payload,
                    signature_id(signatures, &operation.payload_signature)?,
                );
                put_u32(&mut payload, operation.result_type);
                put_u32(&mut payload, operation.resumption_lower);
                put_u32(&mut payload, operation.resumption_upper.unwrap_or(NONE32));
                put_u32(&mut payload, u32::from(operation.terminal));
            }
            Ok(record(0, 0, payload))
        })
        .collect::<Result<Vec<_>, DecodeError>>()?;
    Ok(var_section(&records))
}

fn decode_protocols(
    bytes: &[u8],
    count: u32,
    names: &[String],
    signatures: &[Signature],
) -> Result<Vec<Protocol>, DecodeError> {
    let records = decode_var(bytes)?;
    if records.len() != count as usize {
        return Err(DecodeError::InvalidTable("protocols"));
    }
    records
        .into_iter()
        .map(|(tag, flags, payload)| {
            if tag != 0 || flags != 0 {
                return Err(DecodeError::InvalidTable("protocol"));
            }
            let mut reader = Reader::new(payload);
            let display_name = names
                .get(reader.u32()? as usize)
                .ok_or(DecodeError::InvalidTable("protocol name"))?
                .clone();
            let argument_count = reader.u32()?;
            let mut type_arguments = Vec::new();
            for _ in 0..argument_count {
                type_arguments.push(reader.u32()?);
            }
            let operation_count = reader.u32()?;
            let mut operations = Vec::new();
            for _ in 0..operation_count {
                let name = names
                    .get(reader.u32()? as usize)
                    .ok_or(DecodeError::InvalidTable("operation name"))?
                    .clone();
                let payload_signature = signatures
                    .get(reader.u32()? as usize)
                    .ok_or(DecodeError::InvalidTable("operation signature"))?
                    .clone();
                let result_type = reader.u32()?;
                let resumption_lower = reader.u32()?;
                let resumption_upper = reader.u32()?;
                let flags = reader.u32()?;
                if flags & !1 != 0 {
                    return Err(DecodeError::InvalidTable("operation flags"));
                }
                operations.push(Operation {
                    name,
                    payload_signature,
                    result_type,
                    resumption_lower,
                    resumption_upper: (resumption_upper != NONE32).then_some(resumption_upper),
                    terminal: flags & 1 != 0,
                });
            }
            reader.finish()?;
            Ok(Protocol {
                display_name,
                type_arguments,
                operations,
            })
        })
        .collect()
}

fn encode_handler_defs(
    definitions: &[HandlerDef],
    signatures: &[Signature],
) -> Result<Vec<u8>, DecodeError> {
    let records = definitions
        .iter()
        .map(|definition| {
            let mut payload = Vec::new();
            put_u32(&mut payload, definition.result_type);
            put_u32(&mut payload, definition.clauses.len() as u32);
            for clause in &definition.clauses {
                put_u32(&mut payload, clause.protocol);
                put_u32(&mut payload, clause.operation);
                put_u32(
                    &mut payload,
                    signature_id(signatures, &clause.callable_signature)?,
                );
                put_u32(&mut payload, clause.resumption_type.unwrap_or(NONE32));
            }
            Ok(record(0, u8::from(definition.partial), payload))
        })
        .collect::<Result<Vec<_>, DecodeError>>()?;
    Ok(var_section(&records))
}

fn decode_handler_defs(
    bytes: &[u8],
    count: u32,
    signatures: &[Signature],
) -> Result<Vec<HandlerDef>, DecodeError> {
    let records = decode_var(bytes)?;
    if records.len() != count as usize {
        return Err(DecodeError::InvalidTable("handler definitions"));
    }
    records
        .into_iter()
        .map(|(tag, flags, payload)| {
            if tag != 0 || flags & !1 != 0 {
                return Err(DecodeError::InvalidTable("handler definition"));
            }
            let mut reader = Reader::new(payload);
            let result_type = reader.u32()?;
            let clause_count = reader.u32()?;
            let mut clauses = Vec::new();
            for _ in 0..clause_count {
                let protocol = reader.u32()?;
                let operation = reader.u32()?;
                let callable_signature = signatures
                    .get(reader.u32()? as usize)
                    .ok_or(DecodeError::InvalidTable("clause signature"))?
                    .clone();
                let resumption_type = reader.u32()?;
                clauses.push(HandlerClause {
                    protocol,
                    operation,
                    callable_signature,
                    resumption_type: (resumption_type != NONE32).then_some(resumption_type),
                });
            }
            reader.finish()?;
            Ok(HandlerDef {
                result_type,
                clauses,
                partial: flags & 1 != 0,
            })
        })
        .collect()
}
fn encode_functions(
    fs: &[Function],
    types: &[Type],
    names: &BTreeMap<String, u32>,
    sigs: &[u32],
    spans: &[(u32, u32, u32)],
    cleanup_spans: &[(u32, u32)],
) -> Result<Vec<u8>, DecodeError> {
    let mut w = Vec::new();
    for (i, f) in fs.iter().enumerate() {
        let receiver = *f
            .register_types
            .first()
            .ok_or(DecodeError::InvalidTable("hidden receiver"))?;
        let capture_type = match f.receiver_mode {
            None if receiver == UNIT => UNIT,
            Some(0) => match types.get(receiver as usize).map(Type::representation) {
                Some(Type::RefShared { referent }) => *referent,
                _ => return Err(DecodeError::InvalidTable("hidden receiver")),
            },
            Some(1) => match types.get(receiver as usize).map(Type::representation) {
                Some(Type::RefUnique { referent }) => *referent,
                _ => return Err(DecodeError::InvalidTable("hidden receiver")),
            },
            Some(2) => receiver,
            _ => return Err(DecodeError::InvalidTable("hidden receiver")),
        };
        if f.register_types.get(1..1 + f.params.len()) != Some(&f.params) {
            return Err(DecodeError::InvalidTable("hidden receiver"));
        }
        put_u32(&mut w, names[&f.name]);
        put_u32(&mut w, sigs[i]);
        if f.flags & !FUNCTION_FLAGS != 0 {
            return Err(DecodeError::InvalidTable("function flags"));
        }
        put_u32(&mut w, f.flags);
        put_u32(&mut w, f.register_types.len() as u32);
        put_u32(&mut w, spans[i].0);
        put_u32(&mut w, spans[i].1);
        put_u32(&mut w, spans[i].2);
        put_u32(&mut w, cleanup_spans[i].0);
        put_u32(&mut w, cleanup_spans[i].1);
        put_u32(&mut w, f.label_slot_count);
        put_u32(&mut w, capture_type);
        put_u32(&mut w, f.receiver_mode.unwrap_or(NONE32));
        put_u64(&mut w, 0);
        put_u64(&mut w, 0)
    }
    Ok(w)
}
fn decode_functions(
    b: &[u8],
    names: &[String],
    sigs: &[Sig],
    types: &[Type],
    max_registers: usize,
) -> Result<Vec<(Function, u32, u32, u32)>, DecodeError> {
    let mut r = Reader::new(b);
    let mut out = Vec::new();
    while r.at < b.len() {
        let name = names
            .get(r.u32()? as usize)
            .ok_or(DecodeError::InvalidTable("function name"))?
            .clone();
        let sig = sigs
            .get(r.u32()? as usize)
            .ok_or(DecodeError::InvalidTable("function signature"))?
            .clone();
        let flags = r.u32()?;
        if flags & !FUNCTION_FLAGS != 0 {
            return Err(DecodeError::InvalidTable("function flags"));
        }
        let regs = r.u32()?;
        if regs as usize > max_registers {
            return Err(DecodeError::InvalidTable("function registers"));
        }
        let start = r.u32()?;
        let len = r.u32()?;
        let instruction_count = r.u32()?;
        let cleanup_start = r.u32()?;
        let cleanup_count = r.u32()?;
        let label_slots = r.u32()?;
        let capture_type = r.u32()?;
        let receiver_mode = r.u32()?;
        if r.u64() != Ok(0) || r.u64() != Ok(0) {
            return Err(DecodeError::InvalidTable("function"));
        }
        let receiver_type = match receiver_mode {
            NONE32 if capture_type == UNIT => UNIT,
            0 => unique_type(
                types,
                |ty| matches!(ty, Type::RefShared { referent } if *referent == capture_type),
            )
            .ok_or(DecodeError::InvalidTable("function receiver"))?,
            1 => unique_type(
                types,
                |ty| matches!(ty, Type::RefUnique { referent } if *referent == capture_type),
            )
            .ok_or(DecodeError::InvalidTable("function receiver"))?,
            2 => capture_type,
            _ => return Err(DecodeError::InvalidTable("function receiver")),
        };
        out.push((
            Function {
                flags,
                name,
                params: sig.params,
                return_type: sig.result,
                outward_protocols: sig.outward_protocols,
                receiver_mode: (receiver_mode != NONE32).then_some(receiver_mode),
                register_types: vec![receiver_type; regs as usize],
                code_start: start,
                code_len: len,
                label_slot_count: label_slots,
            },
            instruction_count,
            cleanup_start,
            cleanup_count,
        ))
    }
    Ok(out)
}
fn decode_cleanups(
    bytes: &[u8],
    count: u32,
    operands: &[u32],
    functions: &[Function],
    ranges: &[(u32, u32)],
) -> Result<Vec<CleanupPlan>, DecodeError> {
    let count = usize::try_from(count).map_err(|_| DecodeError::InvalidTable("cleanup count"))?;
    let expected_len = count
        .checked_mul(24)
        .ok_or(DecodeError::InvalidTable("cleanup count"))?;
    if bytes.len() != expected_len {
        return Err(DecodeError::InvalidTable("cleanup count"));
    }
    let mut reader = Reader::new(bytes);
    let mut plans = Vec::with_capacity(count);
    for _ in 0..count {
        let function = reader.u32()?;
        let first_instruction = reader.u32()?;
        let end_instruction = reader.u32()?;
        let operand_start = reader.u32()? as usize;
        let operand_count = reader.u32()? as usize;
        if reader.u32()? != 0 {
            return Err(DecodeError::InvalidTable("cleanup reserved"));
        }
        let operand_end = operand_start
            .checked_add(operand_count)
            .ok_or(DecodeError::InvalidTable("cleanup operands"))?;
        let registers = operands
            .get(operand_start..operand_end)
            .ok_or(DecodeError::InvalidTable("cleanup operands"))?
            .to_vec();
        plans.push(CleanupPlan {
            function,
            first_instruction,
            end_instruction,
            registers,
        });
    }
    reader.finish()?;
    if plans.len() != count {
        return Err(DecodeError::InvalidTable("cleanup count"));
    }
    let mut expected_start = 0u32;
    for (function, &(start, count)) in ranges.iter().enumerate() {
        if start != expected_start {
            return Err(DecodeError::InvalidTable("cleanup range order"));
        }
        let end = start
            .checked_add(count)
            .ok_or(DecodeError::InvalidTable("cleanup range"))?;
        let slice = plans
            .get(start as usize..end as usize)
            .ok_or(DecodeError::InvalidTable("cleanup range"))?;
        let mut next = 0;
        for plan in slice {
            if plan.function != function as u32
                || plan.first_instruction != next
                || plan.end_instruction <= plan.first_instruction
                || plan.end_instruction > functions[function].code_len
            {
                return Err(DecodeError::InvalidTable("cleanup coverage"));
            }
            let mut unique = std::collections::BTreeSet::new();
            if plan.registers.iter().any(|register| {
                *register as usize >= functions[function].register_types.len()
                    || !unique.insert(*register)
            }) {
                return Err(DecodeError::InvalidTable("cleanup registers"));
            }
            next = plan.end_instruction;
        }
        if next != functions[function].code_len {
            return Err(DecodeError::InvalidTable("cleanup coverage"));
        }
        expected_start = end;
    }
    if expected_start as usize != plans.len() {
        return Err(DecodeError::InvalidTable("unclaimed cleanup"));
    }
    Ok(plans)
}

type CleanupSpans = Vec<(u32, u32)>;

fn encode_cleanups(
    plans: &[CleanupPlan],
    functions: &[Function],
    operands: &mut Vec<u32>,
    operand_lists: &mut BTreeMap<Vec<u32>, u32>,
) -> Result<(Vec<u8>, CleanupSpans), DecodeError> {
    let mut w = Vec::new();
    let mut spans = Vec::with_capacity(functions.len());
    let mut at = 0usize;
    for (function_id, function) in functions.iter().enumerate() {
        let start = at as u32;
        let mut next = 0;
        let mut previous_registers: Option<(&[u32], u32)> = None;
        while at < plans.len() && plans[at].function == function_id as u32 {
            let plan = &plans[at];
            if plan.first_instruction != next
                || plan.end_instruction <= plan.first_instruction
                || plan.end_instruction > function.code_len
                || plan
                    .registers
                    .iter()
                    .any(|register| *register as usize >= function.register_types.len())
            {
                return Err(DecodeError::InvalidTable("cleanup"));
            }
            let mut unique = std::collections::BTreeSet::new();
            if !plan
                .registers
                .iter()
                .all(|register| unique.insert(*register))
            {
                return Err(DecodeError::InvalidTable("cleanup"));
            }
            // Adjacent ownership states often retain either end of their
            // predecessor. Operand ranges are immutable, so a prefix or
            // suffix can reuse the previous plan's entries without changing
            // the decoded cleanup state at either PC range.
            let shared_start = match previous_registers {
                Some((registers, operand_start))
                    if !plan.registers.is_empty() && registers.starts_with(&plan.registers) =>
                {
                    Some(operand_start)
                }
                Some((registers, operand_start))
                    if !plan.registers.is_empty() && registers.ends_with(&plan.registers) =>
                {
                    Some(operand_start + (registers.len() - plan.registers.len()) as u32)
                }
                _ => None,
            };
            let (operand_start, operand_count) = shared_start.map_or_else(
                || intern_operand_list(&plan.registers, operands, operand_lists),
                |operand_start| (operand_start, plan.registers.len() as u32),
            );
            put_u32(&mut w, plan.function);
            put_u32(&mut w, plan.first_instruction);
            put_u32(&mut w, plan.end_instruction);
            put_u32(&mut w, operand_start);
            put_u32(&mut w, operand_count);
            put_u32(&mut w, 0);
            previous_registers = Some((&plan.registers, operand_start));
            next = plan.end_instruction;
            at += 1;
        }
        if next != function.code_len {
            return Err(DecodeError::InvalidTable("cleanup coverage"));
        }
        spans.push((start, at as u32 - start));
    }
    if at != plans.len() {
        return Err(DecodeError::InvalidTable("cleanup order"));
    }
    Ok((w, spans))
}
fn intern_operand_list(
    values: &[u32],
    operands: &mut Vec<u32>,
    operand_lists: &mut BTreeMap<Vec<u32>, u32>,
) -> (u32, u32) {
    if let Some(start) = operand_lists.get(values) {
        return (*start, values.len() as u32);
    }
    let start = operands.len() as u32;
    operands.extend(values);
    operand_lists.insert(values.to_vec(), start);
    (start, values.len() as u32)
}

fn encode_instruction(
    i: &Instruction,
    names: &BTreeMap<String, u32>,
    code: &mut Vec<u32>,
    ops: &mut Vec<u32>,
) {
    let mut operand_lists = BTreeMap::new();
    encode_instruction_with_operand_lists(i, names, code, ops, &mut operand_lists);
}

fn encode_instruction_with_operand_lists(
    i: &Instruction,
    names: &BTreeMap<String, u32>,
    code: &mut Vec<u32>,
    ops: &mut Vec<u32>,
    operand_lists: &mut BTreeMap<Vec<u32>, u32>,
) {
    let list = |xs: &[u32], ops: &mut Vec<u32>, operand_lists: &mut BTreeMap<Vec<u32>, u32>| {
        intern_operand_list(xs, ops, operand_lists)
    };
    let (op, w): (u16, Vec<u32>) = match i {
        Instruction::Nop => (0x000, vec![]),
        Instruction::Const { dst, constant } => (0x001, vec![*dst, *constant]),
        Instruction::Move { dst, src } => (0x002, vec![*dst, *src]),
        Instruction::Copy { dst, src } => (0x003, vec![*dst, *src]),
        Instruction::BorrowShared { dst, src } => (0x004, vec![*dst, *src]),
        Instruction::BorrowUnique { dst, src } => (0x005, vec![*dst, *src]),
        Instruction::ReborrowShared { dst, src } => (0x006, vec![*dst, *src]),
        Instruction::ReborrowUnique { dst, src } => (0x007, vec![*dst, *src]),
        Instruction::EndBorrow { reference } => (0x008, vec![*reference]),
        Instruction::Construct {
            dst,
            ty,
            variant,
            fields,
        } => {
            let (s, n) = list(fields, ops, operand_lists);
            (0x009, vec![*dst, *ty, variant.unwrap_or(NONE32), s, n])
        }
        Instruction::ProjectMove { dst, src, field } => (0x00a, vec![*dst, *src, *field]),
        Instruction::ProjectCopy { dst, src, field } => (0x00b, vec![*dst, *src, *field]),
        Instruction::ProjectBorrowShared { dst, src, field } => (0x00c, vec![*dst, *src, *field]),
        Instruction::ProjectBorrowUnique { dst, src, field } => (0x00d, vec![*dst, *src, *field]),
        Instruction::EnumTag { dst, src } => (0x00e, vec![*dst, *src]),
        Instruction::DerefCopy { dst, src } => (0x014, vec![*dst, *src]),
        Instruction::DerefMove { dst, src } => (0x015, vec![*dst, *src]),
        Instruction::DerefStore { dst, src } => (0x016, vec![*dst, *src]),
        Instruction::DerefReborrowShared { dst, src } => (0x017, vec![*dst, *src]),
        Instruction::DerefReborrowUnique { dst, src } => (0x018, vec![*dst, *src]),
        Instruction::Drop { register } => (0x011, vec![*register]),
        Instruction::Deconstruct { src } => (0x013, vec![*src]),
        Instruction::Primitive { dst, op, args } => {
            let (s, n) = list(args, ops, operand_lists);
            (0x045, vec![*dst, *op as u32, s, n])
        }
        Instruction::Jump { target } => (0x020, vec![*target]),
        Instruction::Switch {
            discr,
            cases,
            otherwise,
        } => {
            let mut pairs = Vec::new();
            for &(c, t) in cases {
                pairs.extend([c, t])
            }
            let (s, _) = list(&pairs, ops, operand_lists);
            (0x021, vec![*discr, s, cases.len() as u32, *otherwise])
        }
        Instruction::Call {
            dst,
            function,
            args,
        } => {
            let (s, n) = list(args, ops, operand_lists);
            (0x022, vec![dst.unwrap_or(NONE32), *function, s, n])
        }
        Instruction::TailCall { function, args } => {
            let (s, n) = list(args, ops, operand_lists);
            (0x024, vec![*function, s, n])
        }
        Instruction::CallSelf { dst, args } => {
            let (s, n) = list(args, ops, operand_lists);
            (0x02b, vec![dst.unwrap_or(NONE32), s, n])
        }
        Instruction::TailCallSelf { args } => {
            let (s, n) = list(args, ops, operand_lists);
            (0x02c, vec![s, n])
        }
        Instruction::CallKnownReceiver {
            dst,
            function,
            receiver,
            args,
        } => {
            let (s, n) = list(args, ops, operand_lists);
            (
                0x02d,
                vec![dst.unwrap_or(NONE32), *function, *receiver, s, n],
            )
        }
        Instruction::TailCallKnownReceiver {
            function,
            receiver,
            args,
        } => {
            let (s, n) = list(args, ops, operand_lists);
            (0x02e, vec![*function, *receiver, s, n])
        }
        Instruction::MakeCallable {
            dst,
            callable_type,
            function,
            captures,
        } => {
            let (s, n) = list(captures, ops, operand_lists);
            (0x00f, vec![*dst, *callable_type, *function, s, n])
        }
        Instruction::MakeHandler {
            dst,
            handler_def,
            clauses,
        } => {
            let (s, n) = list(clauses, ops, operand_lists);
            (0x010, vec![*dst, *handler_def, s, n])
        }
        Instruction::MakeHandlerShared {
            dst,
            handler_def,
            functions,
            captures,
        } => {
            let (fs, fn_) = list(functions, ops, operand_lists);
            let (cs, cn) = list(captures, ops, operand_lists);
            (0x047, vec![*dst, *handler_def, fs, fn_, cs, cn])
        }
        Instruction::MakeBindingPack {
            dst,
            binding_type,
            payloads,
        } => {
            let (s, n) = list(payloads, ops, operand_lists);
            (0x012, vec![*dst, *binding_type, s, n])
        }
        Instruction::CallIndirect {
            dst,
            callable,
            receiver_mode,
            args,
        } => {
            let (s, n) = list(args, ops, operand_lists);
            (
                0x023,
                vec![dst.unwrap_or(NONE32), *callable, *receiver_mode, s, n],
            )
        }
        Instruction::TailCallIndirect {
            callable,
            receiver_mode,
            args,
        } => {
            let (s, n) = list(args, ops, operand_lists);
            (0x025, vec![*callable, *receiver_mode, s, n])
        }
        Instruction::Handle {
            dst,
            handler,
            body,
            args,
        } => {
            let (s, n) = list(args, ops, operand_lists);
            (0x040, vec![*dst, *handler, *body, s, n])
        }
        Instruction::Perform {
            dst,
            protocol,
            operation,
            payloads,
        } => {
            let (s, n) = list(payloads, ops, operand_lists);
            (
                0x041,
                vec![dst.unwrap_or(NONE32), *protocol, *operation, s, n],
            )
        }
        Instruction::Resume {
            dst,
            resumption,
            receiver_mode,
            value,
        } => (0x042, vec![*dst, *resumption, *receiver_mode, *value]),
        Instruction::TailResume {
            resumption,
            receiver_mode,
            value,
        } => (0x048, vec![*resumption, *receiver_mode, *value]),
        Instruction::Cancel { dst, resumption } => (0x043, vec![*dst, *resumption]),
        Instruction::HostCall { dst, import, args } => {
            let (s, n) = list(args, ops, operand_lists);
            (0x044, vec![dst.unwrap_or(NONE32), *import, s, n])
        }
        Instruction::Abort { message } => (
            0x046,
            vec![message.as_ref().map_or(NONE32, |message| names[message])],
        ),
        Instruction::LabelPush {
            slot,
            result_register,
            target,
        } => (0x028, vec![*slot, *result_register, *target]),
        Instruction::LabelPop { slot } => (0x029, vec![*slot]),
        Instruction::Leave { slot, value } => (0x02a, vec![*slot, *value]),
        Instruction::Return { src } => (0x026, vec![src.unwrap_or(NONE32)]),
        Instruction::Unreachable => (0x027, vec![]),
    };
    code.push(op as u32 | ((w.len() as u32) << 12));
    code.extend(w)
}
fn decode_instructions(
    words: &[u32],
    ops: &[u32],
    strings: &[String],
) -> Result<Vec<Instruction>, DecodeError> {
    decode_instructions_with_messages(words, ops, strings, &[], true).map(|(code, _)| code)
}

type DecodedInstructions = (Vec<Instruction>, Vec<Option<Range<usize>>>);

fn decode_instructions_with_messages(
    words: &[u32],
    ops: &[u32],
    strings: &[String],
    string_ranges: &[Range<usize>],
    materialize_messages: bool,
) -> Result<DecodedInstructions, DecodeError> {
    let mut at = 0;
    let mut ordinal = 0;
    let mut out = Vec::new();
    let mut abort_messages = Vec::new();
    while at < words.len() {
        let h = words[at];
        let op = (h & 0xfff) as u16;
        let n = ((h >> 12) & 0xff) as usize;
        if h >> 20 != 0 || at + 1 + n > words.len() {
            return Err(DecodeError::InvalidTable("code"));
        }
        let w = &words[at + 1..at + 1 + n];
        let fixed = |x| {
            if n == x {
                Ok(())
            } else {
                Err(DecodeError::InvalidTable("instruction operands"))
            }
        };
        let range = |s: u32, c: u32| {
            let start = usize::try_from(s).map_err(|_| DecodeError::InvalidTable("operands"))?;
            let count = usize::try_from(c).map_err(|_| DecodeError::InvalidTable("operands"))?;
            let end = start
                .checked_add(count)
                .ok_or(DecodeError::InvalidTable("operands"))?;
            ops.get(start..end)
                .ok_or(DecodeError::InvalidTable("operands"))
        };
        let mut abort_message = None;
        let i = match op {
            0x000 => {
                fixed(0)?;
                Instruction::Nop
            }
            0x001 => {
                fixed(2)?;
                Instruction::Const {
                    dst: w[0],
                    constant: w[1],
                }
            }
            0x002 => {
                fixed(2)?;
                Instruction::Move {
                    dst: w[0],
                    src: w[1],
                }
            }
            0x003 => {
                fixed(2)?;
                Instruction::Copy {
                    dst: w[0],
                    src: w[1],
                }
            }
            0x004 => {
                fixed(2)?;
                Instruction::BorrowShared {
                    dst: w[0],
                    src: w[1],
                }
            }
            0x005 => {
                fixed(2)?;
                Instruction::BorrowUnique {
                    dst: w[0],
                    src: w[1],
                }
            }
            0x006 => {
                fixed(2)?;
                Instruction::ReborrowShared {
                    dst: w[0],
                    src: w[1],
                }
            }
            0x007 => {
                fixed(2)?;
                Instruction::ReborrowUnique {
                    dst: w[0],
                    src: w[1],
                }
            }
            0x008 => {
                fixed(1)?;
                Instruction::EndBorrow { reference: w[0] }
            }
            0x009 => {
                fixed(5)?;
                Instruction::Construct {
                    dst: w[0],
                    ty: w[1],
                    variant: (w[2] != NONE32).then_some(w[2]),
                    fields: range(w[3], w[4])?.to_vec(),
                }
            }
            0x00a => {
                fixed(3)?;
                Instruction::ProjectMove {
                    dst: w[0],
                    src: w[1],
                    field: w[2],
                }
            }
            0x00b => {
                fixed(3)?;
                Instruction::ProjectCopy {
                    dst: w[0],
                    src: w[1],
                    field: w[2],
                }
            }
            0x00c => {
                fixed(3)?;
                Instruction::ProjectBorrowShared {
                    dst: w[0],
                    src: w[1],
                    field: w[2],
                }
            }
            0x00d => {
                fixed(3)?;
                Instruction::ProjectBorrowUnique {
                    dst: w[0],
                    src: w[1],
                    field: w[2],
                }
            }
            0x00e => {
                fixed(2)?;
                Instruction::EnumTag {
                    dst: w[0],
                    src: w[1],
                }
            }
            0x014 => {
                fixed(2)?;
                Instruction::DerefCopy {
                    dst: w[0],
                    src: w[1],
                }
            }
            0x015 => {
                fixed(2)?;
                Instruction::DerefMove {
                    dst: w[0],
                    src: w[1],
                }
            }
            0x016 => {
                fixed(2)?;
                Instruction::DerefStore {
                    dst: w[0],
                    src: w[1],
                }
            }
            0x017 => {
                fixed(2)?;
                Instruction::DerefReborrowShared {
                    dst: w[0],
                    src: w[1],
                }
            }
            0x018 => {
                fixed(2)?;
                Instruction::DerefReborrowUnique {
                    dst: w[0],
                    src: w[1],
                }
            }
            0x00f => {
                fixed(5)?;
                Instruction::MakeCallable {
                    dst: w[0],
                    callable_type: w[1],
                    function: w[2],
                    captures: range(w[3], w[4])?.to_vec(),
                }
            }
            0x010 => {
                fixed(4)?;
                Instruction::MakeHandler {
                    dst: w[0],
                    handler_def: w[1],
                    clauses: range(w[2], w[3])?.to_vec(),
                }
            }
            0x047 => {
                fixed(6)?;
                Instruction::MakeHandlerShared {
                    dst: w[0],
                    handler_def: w[1],
                    functions: range(w[2], w[3])?.to_vec(),
                    captures: range(w[4], w[5])?.to_vec(),
                }
            }
            0x012 => {
                fixed(4)?;
                Instruction::MakeBindingPack {
                    dst: w[0],
                    binding_type: w[1],
                    payloads: range(w[2], w[3])?.to_vec(),
                }
            }
            0x011 => {
                fixed(1)?;
                Instruction::Drop { register: w[0] }
            }
            0x013 => {
                fixed(1)?;
                Instruction::Deconstruct { src: w[0] }
            }
            0x045 => {
                fixed(4)?;
                Instruction::Primitive {
                    dst: w[0],
                    op: Primitive::from_u32(w[1]).ok_or(DecodeError::UnsupportedPrimitive(w[1]))?,
                    args: range(w[2], w[3])?.to_vec(),
                }
            }
            0x020 => {
                fixed(1)?;
                Instruction::Jump { target: w[0] }
            }
            0x021 => {
                fixed(4)?;
                let pair_words = w[2]
                    .checked_mul(2)
                    .ok_or(DecodeError::InvalidTable("operands"))?;
                let p = range(w[1], pair_words)?;
                Instruction::Switch {
                    discr: w[0],
                    cases: p.chunks_exact(2).map(|x| (x[0], x[1])).collect(),
                    otherwise: w[3],
                }
            }
            0x022 => {
                fixed(4)?;
                Instruction::Call {
                    dst: (w[0] != NONE32).then_some(w[0]),
                    function: w[1],
                    args: range(w[2], w[3])?.to_vec(),
                }
            }
            0x023 => {
                fixed(5)?;
                Instruction::CallIndirect {
                    dst: (w[0] != NONE32).then_some(w[0]),
                    callable: w[1],
                    receiver_mode: w[2],
                    args: range(w[3], w[4])?.to_vec(),
                }
            }
            0x024 => {
                fixed(3)?;
                Instruction::TailCall {
                    function: w[0],
                    args: range(w[1], w[2])?.to_vec(),
                }
            }
            0x025 => {
                fixed(4)?;
                Instruction::TailCallIndirect {
                    callable: w[0],
                    receiver_mode: w[1],
                    args: range(w[2], w[3])?.to_vec(),
                }
            }
            0x02b => {
                fixed(3)?;
                Instruction::CallSelf {
                    dst: (w[0] != NONE32).then_some(w[0]),
                    args: range(w[1], w[2])?.to_vec(),
                }
            }
            0x02c => {
                fixed(2)?;
                Instruction::TailCallSelf {
                    args: range(w[0], w[1])?.to_vec(),
                }
            }
            0x02d => {
                fixed(5)?;
                Instruction::CallKnownReceiver {
                    dst: (w[0] != NONE32).then_some(w[0]),
                    function: w[1],
                    receiver: w[2],
                    args: range(w[3], w[4])?.to_vec(),
                }
            }
            0x02e => {
                fixed(4)?;
                Instruction::TailCallKnownReceiver {
                    function: w[0],
                    receiver: w[1],
                    args: range(w[2], w[3])?.to_vec(),
                }
            }
            0x026 => {
                fixed(1)?;
                Instruction::Return {
                    src: (w[0] != NONE32).then_some(w[0]),
                }
            }
            0x027 => {
                fixed(0)?;
                Instruction::Unreachable
            }
            0x040 => {
                fixed(5)?;
                Instruction::Handle {
                    dst: w[0],
                    handler: w[1],
                    body: w[2],
                    args: range(w[3], w[4])?.to_vec(),
                }
            }
            0x041 => {
                fixed(5)?;
                Instruction::Perform {
                    dst: (w[0] != NONE32).then_some(w[0]),
                    protocol: w[1],
                    operation: w[2],
                    payloads: range(w[3], w[4])?.to_vec(),
                }
            }
            0x042 => {
                fixed(4)?;
                Instruction::Resume {
                    dst: w[0],
                    resumption: w[1],
                    receiver_mode: w[2],
                    value: w[3],
                }
            }
            0x043 => {
                fixed(2)?;
                Instruction::Cancel {
                    dst: w[0],
                    resumption: w[1],
                }
            }
            0x048 => {
                fixed(3)?;
                Instruction::TailResume {
                    resumption: w[0],
                    receiver_mode: w[1],
                    value: w[2],
                }
            }
            0x044 => {
                fixed(4)?;
                Instruction::HostCall {
                    dst: (w[0] != NONE32).then_some(w[0]),
                    import: w[1],
                    args: range(w[2], w[3])?.to_vec(),
                }
            }
            0x046 => {
                fixed(1)?;
                Instruction::Abort {
                    message: if w[0] == NONE32 {
                        None
                    } else {
                        let index = w[0] as usize;
                        abort_message = string_ranges.get(index).cloned();
                        if !materialize_messages && abort_message.is_none() {
                            return Err(DecodeError::InvalidTable("abort message"));
                        }
                        Some(if materialize_messages {
                            strings
                                .get(index)
                                .ok_or(DecodeError::InvalidTable("abort message"))?
                                .clone()
                        } else {
                            String::new()
                        })
                    },
                }
            }
            0x028 => {
                fixed(3)?;
                Instruction::LabelPush {
                    slot: w[0],
                    result_register: w[1],
                    target: w[2],
                }
            }
            0x029 => {
                fixed(1)?;
                Instruction::LabelPop { slot: w[0] }
            }
            0x02a => {
                fixed(2)?;
                Instruction::Leave {
                    slot: w[0],
                    value: w[1],
                }
            }
            _ => {
                return Err(DecodeError::UnsupportedOpcode {
                    at: ordinal,
                    opcode: op,
                });
            }
        };
        out.push(i);
        abort_messages.push(abort_message);
        at += 1 + n;
        ordinal += 1
    }
    Ok((out, abort_messages))
}
/// Recover equality constraints between label result slots and the values
/// transferred by their statically resolved LEAVEs.
fn infer_label_result_constraints(
    code: &[Instruction],
) -> Result<Vec<(Register, Register)>, DecodeError> {
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Label {
        slot: u32,
        result: Register,
        target: u32,
    }

    if code.is_empty() {
        return Err(DecodeError::InvalidTable("function code"));
    }
    let mut states = vec![None::<Vec<Label>>; code.len()];
    states[0] = Some(Vec::new());
    let mut work = VecDeque::from([0usize]);
    let mut constraints = Vec::new();
    while let Some(pc) = work.pop_front() {
        let mut labels = states[pc]
            .clone()
            .ok_or(DecodeError::InvalidTable("label state"))?;
        let instruction = &code[pc];
        let successors = match instruction {
            Instruction::LabelPush {
                slot,
                result_register,
                target,
            } => {
                labels.push(Label {
                    slot: *slot,
                    result: *result_register,
                    target: *target,
                });
                vec![pc + 1]
            }
            Instruction::LabelPop { slot } => {
                if labels.last().map(|label| label.slot) != Some(*slot) {
                    return Err(DecodeError::InvalidTable("label state"));
                }
                labels.pop();
                vec![pc + 1]
            }
            Instruction::Leave { slot, value } => {
                let index = labels
                    .iter()
                    .rposition(|label| label.slot == *slot)
                    .ok_or(DecodeError::InvalidTable("label state"))?;
                let label = labels[index].clone();
                constraints.push((label.result, *value));
                labels.truncate(index);
                vec![label.target as usize]
            }
            Instruction::Jump { target } => vec![*target as usize],
            Instruction::Switch {
                cases, otherwise, ..
            } => cases
                .iter()
                .map(|(_, target)| *target as usize)
                .chain(std::iter::once(*otherwise as usize))
                .collect(),
            Instruction::Return { .. }
            | Instruction::TailCall { .. }
            | Instruction::TailCallSelf { .. }
            | Instruction::TailCallKnownReceiver { .. }
            | Instruction::TailCallIndirect { .. }
            | Instruction::TailResume { .. }
            | Instruction::Perform { dst: None, .. }
            | Instruction::Unreachable
            | Instruction::Abort { .. } => Vec::new(),
            _ => vec![pc + 1],
        };
        for successor in successors {
            let state = states
                .get_mut(successor)
                .ok_or(DecodeError::InvalidTable("label target"))?;
            match state {
                Some(existing) if existing != &labels => {
                    return Err(DecodeError::InvalidTable("label state"));
                }
                Some(_) => {}
                None => {
                    *state = Some(labels.clone());
                    work.push_back(successor);
                }
            }
        }
    }
    constraints.sort_unstable();
    constraints.dedup();
    Ok(constraints)
}

fn infer_register_types(
    types: &[Type],
    constants: &[Constant],
    protocols: &[Protocol],
    handler_defs: &[HandlerDef],
    imports: &[Import],
    fs: &mut [Function],
    code: &[Instruction],
    register_type_hints: Option<&[Vec<TypeId>]>,
) -> Result<(), DecodeError> {
    if fs.iter().any(|function| function.register_types.is_empty()) {
        return Err(DecodeError::InvalidTable("register count"));
    }
    let sigs: Vec<_> = fs
        .iter()
        .map(|f| {
            (
                f.params.clone(),
                f.return_type,
                f.outward_protocols.clone(),
                f.receiver_mode,
                f.register_types[0],
            )
        })
        .collect();
    if register_type_hints.is_some_and(|hints| hints.len() != fs.len()) {
        return Err(DecodeError::InvalidTable("register type hints"));
    }
    for (function_index, f) in fs.iter_mut().enumerate() {
        let mut t: Vec<Option<u32>> = match register_type_hints {
            Some(hints) => {
                let hints = &hints[function_index];
                if hints.len() != f.register_types.len()
                    || hints.iter().any(|ty| *ty as usize >= types.len())
                {
                    return Err(DecodeError::InvalidTable("register type hints"));
                }
                hints.iter().copied().map(Some).collect()
            }
            None => vec![None; f.register_types.len()],
        };
        if t.is_empty() {
            return Err(DecodeError::InvalidTable("register count"));
        }
        t[0] = f.register_types.first().copied();
        for (i, &x) in f.params.iter().enumerate() {
            *t.get_mut(i + 1)
                .ok_or(DecodeError::InvalidTable("parameters"))? = Some(x)
        }
        let ins = &code[f.code_start as usize..(f.code_start + f.code_len) as usize];
        let enum_variants = infer_enum_variant_facts(constants, t.len(), ins)?;
        let label_constraints = infer_label_result_constraints(ins)?;
        let set = |t: &mut [Option<u32>], r: u32, x: u32| -> Result<(), DecodeError> {
            let s = t
                .get_mut(r as usize)
                .ok_or(DecodeError::InvalidTable("register"))?;
            if s.is_some_and(|y| y != x) {
                return Err(DecodeError::InvalidTable("register type"));
            }
            *s = Some(x);
            Ok(())
        };
        for _ in 0..t.len() + 1 {
            let old = t.clone();
            for &(result, value) in &label_constraints {
                let result_ty = t
                    .get(result as usize)
                    .copied()
                    .ok_or(DecodeError::InvalidTable("register"))?;
                let value_ty = t
                    .get(value as usize)
                    .copied()
                    .ok_or(DecodeError::InvalidTable("register"))?;
                match (result_ty, value_ty) {
                    (Some(ty), _) => set(&mut t, value, ty)?,
                    (_, Some(ty)) => set(&mut t, result, ty)?,
                    _ => {}
                }
            }
            for (pc, i) in ins.iter().enumerate() {
                match i {
                    Instruction::Const { dst, constant } => set(
                        &mut t,
                        *dst,
                        const_type(
                            constants
                                .get(*constant as usize)
                                .ok_or(DecodeError::InvalidTable("constant"))?,
                        ),
                    )?,
                    Instruction::Move { dst, src } | Instruction::Copy { dst, src } => {
                        match (t[*dst as usize], t[*src as usize]) {
                            (Some(x), _) => set(&mut t, *src, x)?,
                            (_, Some(x)) => set(&mut t, *dst, x)?,
                            _ => {}
                        }
                    }
                    Instruction::BorrowShared { dst, src }
                    | Instruction::BorrowUnique { dst, src } => {
                        if let Some(dst_ty) = t[*dst as usize] {
                            let referent =
                                match types.get(dst_ty as usize).map(Type::representation) {
                                    Some(Type::RefShared { referent })
                                        if matches!(i, Instruction::BorrowShared { .. }) =>
                                    {
                                        *referent
                                    }
                                    Some(Type::RefUnique { referent })
                                        if matches!(i, Instruction::BorrowUnique { .. }) =>
                                    {
                                        *referent
                                    }
                                    _ => return Err(DecodeError::InvalidTable("borrow type")),
                                };
                            set(&mut t, *src, referent)?;
                        } else if let Some(src_ty) = t[*src as usize] {
                            let wanted = types.iter().position(|ty| match (i, ty) {
                                (
                                    Instruction::BorrowShared { .. },
                                    Type::RefShared { referent },
                                ) => *referent == src_ty,
                                (
                                    Instruction::BorrowUnique { .. },
                                    Type::RefUnique { referent },
                                ) => *referent == src_ty,
                                _ => false,
                            });
                            if let Some(wanted) = wanted {
                                set(&mut t, *dst, wanted as u32)?;
                            }
                        }
                    }
                    Instruction::DerefCopy { dst, src } => {
                        if let Some(src_ty) = t[*src as usize] {
                            let referent =
                                match types.get(src_ty as usize).map(Type::representation) {
                                    Some(Type::RefShared { referent })
                                    | Some(Type::RefUnique { referent }) => *referent,
                                    _ => {
                                        return Err(DecodeError::InvalidTable(
                                            "deref-copy source type",
                                        ));
                                    }
                                };
                            set(&mut t, *dst, referent)?;
                        } else if let Some(dst_ty) = t[*dst as usize]
                            && let Some(reference) = unique_type(types, |ty| {
                                matches!(
                                    ty,
                                    Type::RefShared { referent }
                                        | Type::RefUnique { referent }
                                        if *referent == dst_ty
                                )
                            })
                        {
                            set(&mut t, *src, reference)?;
                        }
                    }
                    Instruction::DerefMove { dst, src } => {
                        if let Some(src_ty) = t[*src as usize] {
                            let referent =
                                match types.get(src_ty as usize).map(Type::representation) {
                                    Some(Type::RefUnique { referent }) => *referent,
                                    _ => {
                                        return Err(DecodeError::InvalidTable(
                                            "deref-move source type",
                                        ));
                                    }
                                };
                            set(&mut t, *dst, referent)?;
                        } else if let Some(dst_ty) = t[*dst as usize]
                            && let Some(reference) = unique_type(
                                types,
                                |ty| matches!(ty, Type::RefUnique { referent } if *referent == dst_ty),
                            )
                        {
                            set(&mut t, *src, reference)?;
                        }
                    }
                    Instruction::DerefStore { dst, src } => {
                        if let Some(dst_ty) = t[*dst as usize] {
                            let referent =
                                match types.get(dst_ty as usize).map(Type::representation) {
                                    Some(Type::RefUnique { referent }) => *referent,
                                    _ => {
                                        return Err(DecodeError::InvalidTable(
                                            "deref-store destination type",
                                        ));
                                    }
                                };
                            set(&mut t, *src, referent)?;
                        } else if let Some(src_ty) = t[*src as usize]
                            && let Some(reference) = unique_type(
                                types,
                                |ty| matches!(ty, Type::RefUnique { referent } if *referent == src_ty),
                            )
                        {
                            set(&mut t, *dst, reference)?;
                        }
                    }
                    Instruction::Construct {
                        dst,
                        ty,
                        variant,
                        fields,
                    } => {
                        set(&mut t, *dst, *ty)?;
                        let wanted = construction_field_types(
                            types
                                .get(*ty as usize)
                                .ok_or(DecodeError::InvalidTable("type"))?,
                            *variant,
                        )
                        .ok_or(DecodeError::InvalidTable("construct"))?;
                        let wanted = wanted
                            .into_iter()
                            .filter(|&field| {
                                !matches!(
                                    types.get(field as usize).map(Type::representation),
                                    Some(Type::Available { .. })
                                )
                            })
                            .collect::<Vec<_>>();
                        if fields.len() != wanted.len() {
                            return Err(DecodeError::InvalidTable("construct"));
                        }
                        for (&r, &x) in fields.iter().zip(&wanted) {
                            set(&mut t, r, x)?
                        }
                    }
                    Instruction::ProjectMove { dst, src, field }
                    | Instruction::ProjectCopy { dst, src, field } => {
                        if let Some(st) = t[*src as usize] {
                            let base = match types[st as usize].representation() {
                                Type::RefShared { referent } | Type::RefUnique { referent } => {
                                    *referent
                                }
                                _ => st,
                            };
                            let projected = match types[base as usize].representation() {
                                Type::Tuple { .. } | Type::Struct { .. } => {
                                    projection_field_type(&types[base as usize], None, *field)
                                }
                                Type::Enum { variants, .. } => enum_variants[pc][*src as usize]
                                    .and_then(|variant| variants.get(variant as usize))
                                    .and_then(|variant| variant.fields.get(*field as usize))
                                    .map(|field| field.ty)
                                    .or_else(|| {
                                        let mut candidates =
                                            variants.iter().filter_map(|variant| {
                                                variant
                                                    .fields
                                                    .get(*field as usize)
                                                    .map(|field| field.ty)
                                            });
                                        let first = candidates.next();
                                        first.filter(|first| {
                                            candidates.all(|candidate| candidate == *first)
                                        })
                                    }),
                                _ => None,
                            };
                            if let Some(projected) = projected {
                                set(&mut t, *dst, projected)?;
                            } else if let Some(dst_ty) = t[*dst as usize] {
                                let valid = match types[base as usize].representation() {
                                    Type::Enum { variants, .. } => variants.iter().any(|variant| {
                                        variant
                                            .fields
                                            .get(*field as usize)
                                            .is_some_and(|field| field.ty == dst_ty)
                                    }),
                                    _ => false,
                                };
                                if !valid {
                                    return Err(DecodeError::InvalidTable("field"));
                                }
                            }
                        }
                    }
                    Instruction::ReborrowShared { dst, src }
                    | Instruction::ReborrowUnique { dst, src } => {
                        if let Some(src_ty) = t[*src as usize] {
                            let referent = match types[src_ty as usize].representation() {
                                Type::RefShared { referent }
                                    if matches!(i, Instruction::ReborrowShared { .. }) =>
                                {
                                    *referent
                                }
                                Type::RefUnique { referent } => *referent,
                                _ => return Err(DecodeError::InvalidTable("reborrow")),
                            };
                            let wanted = unique_type(types, |ty| match (i, ty) {
                                (
                                    Instruction::ReborrowShared { .. },
                                    Type::RefShared { referent: actual },
                                ) => *actual == referent,
                                (
                                    Instruction::ReborrowUnique { .. },
                                    Type::RefUnique { referent: actual },
                                ) => *actual == referent,
                                _ => false,
                            });
                            if let Some(wanted) = wanted {
                                set(&mut t, *dst, wanted)?;
                            }
                        }
                    }
                    Instruction::DerefReborrowShared { dst, src }
                    | Instruction::DerefReborrowUnique { dst, src } => {
                        if let Some(src_ty) = t[*src as usize] {
                            let (outer_unique, inner) =
                                match types[src_ty as usize].representation() {
                                    Type::RefShared { referent } => (false, *referent),
                                    Type::RefUnique { referent } => (true, *referent),
                                    _ => {
                                        return Err(DecodeError::InvalidTable(
                                            "stored-reference reborrow source",
                                        ));
                                    }
                                };
                            let (inner_unique, referent) =
                                match types[inner as usize].representation() {
                                    Type::RefShared { referent } => (false, *referent),
                                    Type::RefUnique { referent } => (true, *referent),
                                    _ => {
                                        return Err(DecodeError::InvalidTable(
                                            "stored-reference reborrow target",
                                        ));
                                    }
                                };
                            let requested_unique =
                                matches!(i, Instruction::DerefReborrowUnique { .. });
                            if requested_unique && (!outer_unique || !inner_unique) {
                                return Err(DecodeError::InvalidTable(
                                    "stored-reference unique reborrow",
                                ));
                            }
                            if let Some(wanted) = unique_type(types, |ty| match ty {
                                Type::RefShared { referent: actual } => {
                                    !requested_unique && *actual == referent
                                }
                                Type::RefUnique { referent: actual } => {
                                    requested_unique && *actual == referent
                                }
                                _ => false,
                            }) {
                                set(&mut t, *dst, wanted)?;
                            }
                        }
                    }
                    Instruction::ProjectBorrowShared { dst, src, field }
                    | Instruction::ProjectBorrowUnique { dst, src, field } => {
                        if let Some(src_ty) = t[*src as usize] {
                            let base_ty = match types[src_ty as usize].representation() {
                                Type::RefShared { referent } | Type::RefUnique { referent } => {
                                    *referent
                                }
                                _ => src_ty,
                            };
                            let projected = match types[base_ty as usize].representation() {
                                Type::Tuple { .. } | Type::Struct { .. } => {
                                    projection_field_type(&types[base_ty as usize], None, *field)
                                }
                                Type::Enum { variants, .. } => enum_variants[pc][*src as usize]
                                    .and_then(|variant| variants.get(variant as usize))
                                    .and_then(|variant| variant.fields.get(*field as usize))
                                    .map(|field| field.ty)
                                    .or_else(|| {
                                        let mut candidates =
                                            variants.iter().filter_map(|variant| {
                                                variant
                                                    .fields
                                                    .get(*field as usize)
                                                    .map(|field| field.ty)
                                            });
                                        let first = candidates.next();
                                        first.filter(|first| {
                                            candidates.all(|candidate| candidate == *first)
                                        })
                                    }),
                                _ => None,
                            };
                            let unique = matches!(i, Instruction::ProjectBorrowUnique { .. });
                            if let Some(projected) = projected {
                                if let Some(reference) = unique_type(types, |ty| match ty {
                                    Type::RefShared { referent } => {
                                        !unique && *referent == projected
                                    }
                                    Type::RefUnique { referent } => {
                                        unique && *referent == projected
                                    }
                                    _ => false,
                                }) {
                                    set(&mut t, *dst, reference)?;
                                }
                            } else if let Some(dst_ty) = t[*dst as usize] {
                                let referent = match types[dst_ty as usize].representation() {
                                    Type::RefShared { referent } if !unique => Some(*referent),
                                    Type::RefUnique { referent } if unique => Some(*referent),
                                    _ => None,
                                };
                                let valid =
                                    match (types[base_ty as usize].representation(), referent) {
                                        (Type::Enum { variants, .. }, Some(referent)) => {
                                            variants.iter().any(|variant| {
                                                variant
                                                    .fields
                                                    .get(*field as usize)
                                                    .is_some_and(|field| field.ty == referent)
                                            })
                                        }
                                        _ => false,
                                    };
                                if !valid {
                                    return Err(DecodeError::InvalidTable("project borrow"));
                                }
                            }
                        }
                    }
                    Instruction::EnumTag { dst, src } => {
                        set(&mut t, *dst, U32)?;
                        if let Some(src_ty) = t[*src as usize] {
                            let source = types
                                .get(src_ty as usize)
                                .map(Type::representation)
                                .ok_or(DecodeError::InvalidTable("enum tag"))?;
                            let source = match source {
                                Type::RefShared { referent } | Type::RefUnique { referent } => {
                                    types
                                        .get(*referent as usize)
                                        .map(Type::representation)
                                        .ok_or(DecodeError::InvalidTable("enum tag"))?
                                }
                                source => source,
                            };
                            if !matches!(source, Type::Enum { .. }) {
                                return Err(DecodeError::InvalidTable("enum tag"));
                            }
                        }
                    }
                    Instruction::Primitive { dst, op, args } => {
                        infer_primitive_types(types, *op, *dst, args, &mut t)?;
                        let arg_types = args
                            .iter()
                            .map(|&r| t.get(r as usize).copied().flatten())
                            .collect::<Option<Vec<_>>>();
                        if let Some(arg_types) = arg_types {
                            if let Some(result) = primitive_result_type(*op, &arg_types) {
                                set(&mut t, *dst, result)?;
                            } else if let Some(result) = t[*dst as usize]
                                && !primitive_signature(types, *op, &arg_types, result)
                            {
                                return Err(DecodeError::InvalidTable("primitive signature"));
                            }
                        }
                    }
                    Instruction::Switch { discr, cases, .. } => {
                        if let Some((c, _)) = cases.first() {
                            set(&mut t, *discr, const_type(&constants[*c as usize]))?
                        }
                    }
                    Instruction::Call {
                        dst,
                        function,
                        args,
                    } => {
                        let (s, r, _, _, _) = sigs
                            .get(*function as usize)
                            .ok_or(DecodeError::InvalidTable("callee"))?;
                        for (&a, &x) in args.iter().zip(s) {
                            set(&mut t, a, x)?
                        }
                        if let Some(dst) = dst {
                            set(&mut t, *dst, *r)?
                        } else if !matches!(
                            types.get(*r as usize).map(Type::representation),
                            Some(Type::Unit | Type::Never)
                        ) {
                            return Err(DecodeError::InvalidTable("call destination"));
                        }
                    }
                    Instruction::TailCall { function, args } => {
                        let (s, _, _, _, _) = sigs
                            .get(*function as usize)
                            .ok_or(DecodeError::InvalidTable("callee"))?;
                        for (&a, &x) in args.iter().zip(s) {
                            set(&mut t, a, x)?
                        }
                    }
                    Instruction::CallSelf { dst, args } => {
                        for (&a, &x) in args.iter().zip(&f.params) {
                            set(&mut t, a, x)?
                        }
                        if let Some(dst) = dst {
                            set(&mut t, *dst, f.return_type)?
                        } else if !matches!(
                            types.get(f.return_type as usize).map(Type::representation),
                            Some(Type::Unit | Type::Never)
                        ) {
                            return Err(DecodeError::InvalidTable("self-call destination"));
                        }
                    }
                    Instruction::TailCallSelf { args } => {
                        for (&a, &x) in args.iter().zip(&f.params) {
                            set(&mut t, a, x)?
                        }
                    }
                    Instruction::CallKnownReceiver {
                        dst,
                        function,
                        receiver,
                        args,
                    } => {
                        let (params, result, _, mode, receiver_type) = sigs
                            .get(*function as usize)
                            .ok_or(DecodeError::InvalidTable("known receiver callee"))?;
                        if *mode != Some(0) {
                            return Err(DecodeError::InvalidTable("known receiver mode"));
                        }
                        set(&mut t, *receiver, *receiver_type)?;
                        for (&argument, &ty) in args.iter().zip(params) {
                            set(&mut t, argument, ty)?;
                        }
                        if let Some(dst) = dst {
                            set(&mut t, *dst, *result)?;
                        } else if !matches!(
                            types.get(*result as usize).map(Type::representation),
                            Some(Type::Unit | Type::Never)
                        ) {
                            return Err(DecodeError::InvalidTable(
                                "known receiver call destination",
                            ));
                        }
                    }
                    Instruction::TailCallKnownReceiver {
                        function,
                        receiver,
                        args,
                    } => {
                        let (params, _, _, mode, receiver_type) = sigs
                            .get(*function as usize)
                            .ok_or(DecodeError::InvalidTable("known receiver callee"))?;
                        if *mode != Some(0) {
                            return Err(DecodeError::InvalidTable("known receiver mode"));
                        }
                        set(&mut t, *receiver, *receiver_type)?;
                        for (&argument, &ty) in args.iter().zip(params) {
                            set(&mut t, argument, ty)?;
                        }
                    }
                    Instruction::MakeCallable {
                        dst,
                        callable_type,
                        function,
                        captures,
                    } => {
                        let (params, result, outward_protocols, mode, receiver_type) = sigs
                            .get(*function as usize)
                            .ok_or(DecodeError::InvalidTable("callable target"))?;
                        let Some(mode) = mode else {
                            return Err(DecodeError::InvalidTable("callable target"));
                        };
                        let capture_type = receiver_capture_type(types, *mode, *receiver_type)?;
                        let Some(Type::Callable {
                            signature,
                            capture_type: actual_capture,
                            receiver_mode,
                            ..
                        }) = types.get(*callable_type as usize).map(Type::representation)
                        else {
                            return Err(DecodeError::InvalidTable("callable descriptor"));
                        };
                        if signature.params != *params
                            || signature.result != *result
                            || signature.outward_protocols != *outward_protocols
                            || *actual_capture != capture_type
                            || *receiver_mode != *mode
                        {
                            return Err(DecodeError::InvalidTable("callable descriptor"));
                        }
                        set(&mut t, *dst, *callable_type)?;
                        let fields = callable_capture_fields(types, capture_type, captures.len())?;
                        for (&capture, field_type) in captures.iter().zip(fields) {
                            set(&mut t, capture, field_type)?;
                        }
                    }
                    Instruction::MakeHandler {
                        dst,
                        handler_def,
                        clauses,
                    } => {
                        let definition = handler_defs
                            .get(*handler_def as usize)
                            .ok_or(DecodeError::InvalidTable("handler definition"))?;
                        if definition.clauses.len() != clauses.len() {
                            return Err(DecodeError::InvalidTable("handler clauses"));
                        }
                        let handler_type = unique_type(types, |ty| {
                            matches!(ty, Type::Handler { handler_def: actual, .. }
                                if *actual == *handler_def)
                        })
                        .ok_or(DecodeError::InvalidTable("handler descriptor"))?;
                        set(&mut t, *dst, handler_type)?;
                        let Type::Handler { capture_type, .. } =
                            types[handler_type as usize].representation()
                        else {
                            unreachable!()
                        };
                        let fields = callable_capture_fields(types, *capture_type, clauses.len())?;
                        for (&clause, field_type) in clauses.iter().zip(fields) {
                            set(&mut t, clause, field_type)?;
                        }
                    }
                    Instruction::MakeHandlerShared {
                        dst,
                        handler_def,
                        functions,
                        captures,
                    } => {
                        let definition = handler_defs
                            .get(*handler_def as usize)
                            .ok_or(DecodeError::InvalidTable("handler definition"))?;
                        if definition.clauses.len() != functions.len() || functions.is_empty() {
                            return Err(DecodeError::InvalidTable("handler clauses"));
                        }
                        let handler_type = unique_type(types, |ty| {
                            matches!(ty, Type::Handler { handler_def: actual, .. }
                                if *actual == *handler_def)
                        })
                        .ok_or(DecodeError::InvalidTable("handler descriptor"))?;
                        set(&mut t, *dst, handler_type)?;
                        let Type::Handler { capture_type, .. } =
                            types[handler_type as usize].representation()
                        else {
                            unreachable!()
                        };
                        let callable_types =
                            callable_capture_fields(types, *capture_type, functions.len())?;
                        let mut environment_type = None;
                        for (&function, callable_type) in functions.iter().zip(callable_types) {
                            let Type::Callable {
                                capture_type: described_environment,
                                receiver_mode: described_mode,
                                ..
                            } = types[callable_type as usize].representation()
                            else {
                                return Err(DecodeError::InvalidTable("handler clause callable"));
                            };
                            let (_, _, _, mode, receiver_type) = sigs
                                .get(function as usize)
                                .ok_or(DecodeError::InvalidTable("handler clause target"))?;
                            let receiver_matches = match mode {
                                Some(2) => *receiver_type == *described_environment,
                                Some(0) => matches!(
                                    types[*receiver_type as usize].representation(),
                                    Type::RefShared { referent } if *referent == *described_environment
                                ),
                                Some(1) => matches!(
                                    types[*receiver_type as usize].representation(),
                                    Type::RefUnique { referent } if *referent == *described_environment
                                ),
                                _ => false,
                            };
                            if *mode != Some(*described_mode)
                                || !receiver_matches
                                || environment_type
                                    .replace(*described_environment)
                                    .is_some_and(|known| known != *described_environment)
                            {
                                return Err(DecodeError::InvalidTable("handler clause target"));
                            }
                        }
                        let environment_type = environment_type
                            .ok_or(DecodeError::InvalidTable("handler clause target"))?;
                        let fields =
                            callable_capture_fields(types, environment_type, captures.len())?;
                        for (&capture, field_type) in captures.iter().zip(fields) {
                            set(&mut t, capture, field_type)?;
                        }
                    }
                    Instruction::MakeBindingPack {
                        dst,
                        binding_type,
                        payloads,
                    } => {
                        let Type::BindingPack { payload_type, .. } = types
                            .get(*binding_type as usize)
                            .ok_or(DecodeError::InvalidTable("binding pack"))?
                            .representation()
                        else {
                            return Err(DecodeError::InvalidTable("binding pack"));
                        };
                        set(&mut t, *dst, *binding_type)?;
                        let fields = callable_capture_fields(types, *payload_type, payloads.len())?;
                        for (&payload, field_type) in payloads.iter().zip(fields) {
                            set(&mut t, payload, field_type)?;
                        }
                    }
                    Instruction::CallIndirect {
                        dst,
                        callable,
                        args,
                        ..
                    } => {
                        if let Some(callable_type) = t[*callable as usize] {
                            let Type::Callable { signature, .. } =
                                types[callable_type as usize].representation()
                            else {
                                return Err(DecodeError::InvalidTable("indirect call"));
                            };
                            if args.len() != signature.params.len() {
                                return Err(DecodeError::InvalidTable("indirect call"));
                            }
                            for (&argument, &argument_type) in args.iter().zip(&signature.params) {
                                set(&mut t, argument, argument_type)?;
                            }
                            if let Some(dst) = dst {
                                set(&mut t, *dst, signature.result)?;
                            } else if !matches!(
                                types
                                    .get(signature.result as usize)
                                    .map(Type::representation),
                                Some(Type::Unit | Type::Never)
                            ) {
                                return Err(DecodeError::InvalidTable("indirect call destination"));
                            }
                        }
                    }
                    Instruction::TailCallIndirect { callable, args, .. } => {
                        if let Some(callable_type) = t[*callable as usize] {
                            let Type::Callable { signature, .. } =
                                types[callable_type as usize].representation()
                            else {
                                return Err(DecodeError::InvalidTable("indirect tail call"));
                            };
                            if args.len() != signature.params.len() {
                                return Err(DecodeError::InvalidTable("indirect tail call"));
                            }
                            for (&argument, &argument_type) in args.iter().zip(&signature.params) {
                                set(&mut t, argument, argument_type)?;
                            }
                        }
                    }
                    Instruction::Handle {
                        dst,
                        handler,
                        body,
                        args,
                    } => {
                        if let Some(handler_type) = t[*handler as usize] {
                            let Type::Handler { handler_def, .. } =
                                types[handler_type as usize].representation()
                            else {
                                return Err(DecodeError::InvalidTable("handle"));
                            };
                            let result = handler_defs
                                .get(*handler_def as usize)
                                .ok_or(DecodeError::InvalidTable("handle"))?
                                .result_type;
                            set(&mut t, *dst, result)?;
                        }
                        if let Some(body_type) = t[*body as usize] {
                            let Type::Callable { signature, .. } =
                                types[body_type as usize].representation()
                            else {
                                return Err(DecodeError::InvalidTable("handle body"));
                            };
                            if args.len() != signature.params.len() {
                                return Err(DecodeError::InvalidTable("handle body"));
                            }
                            for (&argument, &argument_type) in args.iter().zip(&signature.params) {
                                set(&mut t, argument, argument_type)?;
                            }
                            set(&mut t, *dst, signature.result)?;
                        }
                    }
                    Instruction::Perform {
                        dst,
                        protocol,
                        operation,
                        payloads,
                    } => {
                        let operation = protocols
                            .get(*protocol as usize)
                            .and_then(|protocol| protocol.operations.get(*operation as usize))
                            .ok_or(DecodeError::InvalidTable("perform"))?;
                        if payloads.len() != operation.payload_signature.params.len() {
                            return Err(DecodeError::InvalidTable("perform"));
                        }
                        for (&payload, &payload_type) in
                            payloads.iter().zip(&operation.payload_signature.params)
                        {
                            set(&mut t, payload, payload_type)?;
                        }
                        if let Some(dst) = dst {
                            set(&mut t, *dst, operation.result_type)?;
                        }
                    }
                    Instruction::Resume {
                        dst,
                        resumption,
                        value,
                        ..
                    } => {
                        if let Some(resumption_type) = t[*resumption as usize] {
                            let Type::Resumption {
                                input_type,
                                output_type,
                                ..
                            } = types[resumption_type as usize].representation()
                            else {
                                return Err(DecodeError::InvalidTable("resume"));
                            };
                            set(&mut t, *value, *input_type)?;
                            set(&mut t, *dst, *output_type)?;
                        }
                    }
                    Instruction::TailResume {
                        resumption, value, ..
                    } => {
                        if let Some(resumption_type) = t[*resumption as usize] {
                            let Type::Resumption { input_type, .. } =
                                types[resumption_type as usize].representation()
                            else {
                                return Err(DecodeError::InvalidTable("tail resume"));
                            };
                            set(&mut t, *value, *input_type)?;
                        }
                    }
                    Instruction::Cancel { dst, .. } => set(&mut t, *dst, UNIT)?,
                    Instruction::HostCall { dst, import, args } => {
                        let signature = &imports
                            .get(*import as usize)
                            .ok_or(DecodeError::InvalidTable("host call"))?
                            .signature;
                        if args.len() != signature.params.len() {
                            return Err(DecodeError::InvalidTable("host call"));
                        }
                        for (&argument, &argument_type) in args.iter().zip(&signature.params) {
                            set(&mut t, argument, argument_type)?;
                        }
                        if let Some(dst) = dst {
                            set(&mut t, *dst, signature.result)?;
                        }
                    }
                    Instruction::Return { src } => {
                        if let Some(src) = src {
                            set(&mut t, *src, f.return_type)?;
                        } else if f.return_type != UNIT {
                            return Err(DecodeError::InvalidTable("return value"));
                        }
                    }
                    _ => {}
                }
            }
            if old == t {
                break;
            }
        }
        if t.iter().any(Option::is_none) {
            if std::env::var_os("G1_VERIFY_TRACE").is_some() {
                let missing = t
                    .iter()
                    .enumerate()
                    .filter_map(|(register, ty)| ty.is_none().then_some(register))
                    .collect::<Vec<_>>();
                let mentions = ins
                    .iter()
                    .enumerate()
                    .filter(|(_, instruction)| {
                        let debug = format!("{instruction:?}");
                        debug
                            .split(|character: char| !character.is_ascii_digit())
                            .filter_map(|token| token.parse::<usize>().ok())
                            .any(|number| missing.contains(&number))
                    })
                    .collect::<Vec<_>>();
                let projection_context = ins
                    .iter()
                    .enumerate()
                    .filter_map(|(pc, instruction)| match instruction {
                        Instruction::ProjectMove { dst, src, field }
                        | Instruction::ProjectCopy { dst, src, field }
                            if missing.contains(&(*dst as usize)) =>
                        {
                            Some((
                                pc,
                                *dst,
                                *src,
                                *field,
                                t[*src as usize],
                                enum_variants[pc][*src as usize],
                                t[*src as usize]
                                    .and_then(|ty| types.get(ty as usize))
                                    .map(Type::representation),
                            ))
                        }
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                let projection_windows = projection_context
                    .iter()
                    .map(|(pc, _, src, ..)| {
                        let start = pc.saturating_sub(160);
                        let end = pc.saturating_add(32).min(ins.len() - 1);
                        (
                            *src,
                            ins[start..=end]
                                .iter()
                                .enumerate()
                                .map(|(offset, instruction)| {
                                    let instruction_pc = start + offset;
                                    (
                                        instruction_pc,
                                        instruction,
                                        enum_variants[instruction_pc][*src as usize],
                                        enum_variants[instruction_pc]
                                            .iter()
                                            .enumerate()
                                            .filter_map(|(register, variant)| {
                                                variant.map(|variant| (register, variant))
                                            })
                                            .collect::<Vec<_>>(),
                                    )
                                })
                                .collect::<Vec<_>>(),
                        )
                    })
                    .collect::<Vec<_>>();
                eprintln!(
                    "g1-decoder function `{}` uninferred registers: {missing:?}; mentions={mentions:?}; projections={projection_context:?}; projection_windows={projection_windows:?}",
                    f.name
                );
            }
            return Err(DecodeError::InvalidTable("uninferred register type"));
        }
        f.register_types = t.into_iter().map(Option::unwrap).collect()
    }
    Ok(())
}

/// Recover the enum variant selected on each control-flow edge. Register types
/// are deliberately omitted from the wire format, so a projection from an enum
/// whose variants have different field types needs the dominating `EnumTag` /
/// `Switch` fact in order to recover its result type.
fn infer_enum_variant_facts(
    constants: &[Constant],
    register_count: usize,
    code: &[Instruction],
) -> Result<Vec<Vec<Option<u32>>>, DecodeError> {
    #[derive(Clone, PartialEq, Eq)]
    struct Facts {
        initialized: Vec<bool>,
        tag_origins: Vec<Option<Register>>,
        variants: Vec<Option<u32>>,
    }

    if code.is_empty() {
        return Ok(Vec::new());
    }
    let empty = Facts {
        initialized: vec![false; register_count],
        tag_origins: vec![None; register_count],
        variants: vec![None; register_count],
    };
    let mut states = vec![None; code.len()];
    let mut components = vec![None; code.len()];
    states[0] = Some(empty.clone());
    components[0] = Some(0usize);
    let mut work = std::collections::VecDeque::from([0usize]);
    let mut next_component = 1usize;

    loop {
        while let Some(pc) = work.pop_front() {
            let component = components[pc].expect("queued enum fact component");
            let mut state = states[pc].clone().expect("queued enum fact state");
            let instruction = &code[pc];
            let reset = |state: &mut Facts,
                         register: Register,
                         initialized: bool|
             -> Result<usize, DecodeError> {
                let index = register as usize;
                *state
                    .variants
                    .get_mut(index)
                    .ok_or(DecodeError::InvalidTable("register"))? = None;
                *state
                    .tag_origins
                    .get_mut(index)
                    .ok_or(DecodeError::InvalidTable("register"))? = None;
                state.initialized[index] = initialized;
                Ok(index)
            };
            match instruction {
                Instruction::Construct { dst, variant, .. } => {
                    let dst = reset(&mut state, *dst, true)?;
                    state.variants[dst] = *variant;
                }
                Instruction::Move { dst, src } => {
                    let dst = reset(&mut state, *dst, false)?;
                    let src = *src as usize;
                    if src >= register_count {
                        return Err(DecodeError::InvalidTable("register"));
                    }
                    state.initialized[dst] = state.initialized[src];
                    state.variants[dst] = state.variants[src].take();
                    state.tag_origins[dst] = state.tag_origins[src].take();
                    state.initialized[src] = false;
                    for origin in state.tag_origins.iter_mut().flatten() {
                        if *origin as usize == src {
                            *origin = dst as Register;
                        }
                    }
                }
                Instruction::Copy { dst, src } => {
                    let dst = reset(&mut state, *dst, false)?;
                    let src = *src as usize;
                    if src >= register_count {
                        return Err(DecodeError::InvalidTable("register"));
                    }
                    state.initialized[dst] = state.initialized[src];
                    state.variants[dst] = state.variants[src];
                    state.tag_origins[dst] = state.tag_origins[src];
                }
                Instruction::EnumTag { dst, src } => {
                    let dst = reset(&mut state, *dst, true)?;
                    if *src as usize >= register_count {
                        return Err(DecodeError::InvalidTable("register"));
                    }
                    state.tag_origins[dst] = Some(*src);
                }
                Instruction::Drop { register }
                | Instruction::Deconstruct { src: register }
                | Instruction::Return {
                    src: Some(register),
                } => {
                    reset(&mut state, *register, false)?;
                }
                Instruction::DerefStore { src, .. } => {
                    reset(&mut state, *src, false)?;
                }
                Instruction::Const { dst, .. }
                | Instruction::BorrowShared { dst, .. }
                | Instruction::BorrowUnique { dst, .. }
                | Instruction::ReborrowShared { dst, .. }
                | Instruction::ReborrowUnique { dst, .. }
                | Instruction::DerefCopy { dst, .. }
                | Instruction::DerefMove { dst, .. }
                | Instruction::ProjectMove { dst, .. }
                | Instruction::ProjectCopy { dst, .. }
                | Instruction::ProjectBorrowShared { dst, .. }
                | Instruction::ProjectBorrowUnique { dst, .. }
                | Instruction::Primitive { dst, .. }
                | Instruction::MakeCallable { dst, .. }
                | Instruction::MakeHandler { dst, .. }
                | Instruction::MakeHandlerShared { dst, .. }
                | Instruction::MakeBindingPack { dst, .. }
                | Instruction::Handle { dst, .. } => {
                    reset(&mut state, *dst, true)?;
                }
                Instruction::Call { dst: Some(dst), .. }
                | Instruction::CallSelf { dst: Some(dst), .. }
                | Instruction::CallKnownReceiver { dst: Some(dst), .. }
                | Instruction::CallIndirect { dst: Some(dst), .. }
                | Instruction::Perform { dst: Some(dst), .. }
                | Instruction::HostCall { dst: Some(dst), .. }
                | Instruction::Resume { dst, .. }
                | Instruction::Cancel { dst, .. } => {
                    reset(&mut state, *dst, true)?;
                }
                _ => {}
            }

            let mut successors = Vec::new();
            match instruction {
                Instruction::Switch {
                    discr,
                    cases,
                    otherwise,
                } => {
                    let origin = *state
                        .tag_origins
                        .get(*discr as usize)
                        .ok_or(DecodeError::InvalidTable("register"))?;
                    for &(constant, target) in cases {
                        let mut edge = state.clone();
                        if let Some(origin) = origin {
                            let variant = match constants.get(constant as usize) {
                                Some(Constant::U32(variant)) => *variant,
                                _ => return Err(DecodeError::InvalidTable("enum switch")),
                            };
                            edge.variants[origin as usize] = Some(variant);
                        }
                        successors.push((target as usize, edge));
                    }
                    let mut edge = state;
                    if let Some(origin) = origin {
                        edge.variants[origin as usize] = None;
                    }
                    successors.push((*otherwise as usize, edge));
                }
                Instruction::Jump { target } => successors.push((*target as usize, state)),
                Instruction::Return { .. }
                | Instruction::TailCall { .. }
                | Instruction::TailCallSelf { .. }
                | Instruction::TailCallKnownReceiver { .. }
                | Instruction::TailCallIndirect { .. }
                | Instruction::TailResume { .. }
                | Instruction::Perform { dst: None, .. }
                | Instruction::Unreachable
                | Instruction::Abort { .. }
                | Instruction::Leave { .. } => {}
                _ if pc + 1 < code.len() => successors.push((pc + 1, state)),
                _ => {}
            }

            for (target, incoming) in successors {
                if std::env::var_os("G1_VERIFY_TRACE").is_some()
                    && (target == 2111 || target == 2032)
                    && (matches!(
                        code.get(2124),
                        Some(Instruction::ProjectMove {
                            dst: 80,
                            src: 81,
                            field: 0
                        })
                    ) || matches!(
                        code.get(2045),
                        Some(Instruction::ProjectMove {
                            dst: 80,
                            src: 81,
                            field: 0
                        })
                    ))
                {
                    eprintln!(
                        "enum-entry-{target} from={pc} component={component} incoming-r89=({},{:?}) incoming-r92=({},{:?}) existing-component={:?} existing-r89={:?} existing-r92={:?}",
                        incoming.initialized[89],
                        incoming.variants[89],
                        incoming.initialized[92],
                        incoming.variants[92],
                        components[target],
                        states[target]
                            .as_ref()
                            .map(|state| (state.initialized[89], state.variants[89])),
                        states[target]
                            .as_ref()
                            .map(|state| (state.initialized[92], state.variants[92]))
                    );
                }
                let slot = states
                    .get_mut(target)
                    .ok_or(DecodeError::InvalidTable("enum switch target"))?;
                match slot {
                    Some(existing) => {
                        let mut changed = false;
                        for register in 0..register_count {
                            match (
                                existing.initialized[register],
                                incoming.initialized[register],
                            ) {
                                (false, true) => {
                                    existing.initialized[register] = true;
                                    existing.variants[register] = incoming.variants[register];
                                    existing.tag_origins[register] = incoming.tag_origins[register];
                                    changed = true;
                                }
                                (true, true) => {
                                    if existing.variants[register] != incoming.variants[register]
                                        && existing.variants[register].take().is_some()
                                    {
                                        changed = true;
                                    }
                                    if existing.tag_origins[register]
                                        != incoming.tag_origins[register]
                                        && existing.tag_origins[register].take().is_some()
                                    {
                                        changed = true;
                                    }
                                }
                                (false, false) | (true, false) => {}
                            }
                        }
                        if changed {
                            work.push_back(target);
                        }
                    }
                    slot @ None => {
                        *slot = Some(incoming);
                        components[target] = Some(component);
                        work.push_back(target);
                    }
                }
            }
        }
        let Some(root) = states.iter().position(Option::is_none) else {
            break;
        };
        states[root] = Some(empty.clone());
        components[root] = Some(next_component);
        next_component = next_component.saturating_add(1);
        work.push_back(root);
    }

    if std::env::var_os("G1_VERIFY_TRACE").is_some()
        && matches!(
            code.get(1974),
            Some(Instruction::ProjectMove {
                dst: 146,
                src: 142,
                field: 0
            })
        )
    {
        for pc in 1942..=1974 {
            let state = states[pc].as_ref().expect("analyzed enum facts");
            eprintln!(
                "enum-facts pc={pc} component={:?} r137=({},{:?}) r139=({},{:?}) r142=({},{:?}) instruction={:?}",
                components[pc],
                state.initialized[137],
                state.variants[137],
                state.initialized[139],
                state.variants[139],
                state.initialized[142],
                state.variants[142],
                code[pc]
            );
        }
    }
    if std::env::var_os("G1_VERIFY_TRACE").is_some()
        && matches!(
            code.get(2124),
            Some(Instruction::ProjectMove {
                dst: 80,
                src: 81,
                field: 0
            })
        )
    {
        eprintln!(
            "late-cleanup-window={:?}; err-predecessor-window={:?}",
            &code[2110..=2155],
            &code[1690..=1740]
        );
    }

    Ok(states
        .into_iter()
        .map(|state| {
            state.unwrap_or_else(|| Facts {
                initialized: vec![false; register_count],
                tag_origins: vec![None; register_count],
                variants: vec![None; register_count],
            })
        })
        .map(|state| state.variants)
        .collect())
}

fn receiver_capture_type(
    types: &[Type],
    receiver_mode: u32,
    receiver_type: TypeId,
) -> Result<TypeId, DecodeError> {
    match (
        receiver_mode,
        types.get(receiver_type as usize).map(Type::representation),
    ) {
        (0, Some(Type::RefShared { referent })) | (1, Some(Type::RefUnique { referent })) => {
            Ok(*referent)
        }
        (2, Some(_)) => Ok(receiver_type),
        _ => Err(DecodeError::InvalidTable("receiver type")),
    }
}

fn callable_capture_fields(
    types: &[Type],
    capture_type: TypeId,
    count: usize,
) -> Result<Vec<TypeId>, DecodeError> {
    if capture_type == UNIT && count == 0 {
        return Ok(Vec::new());
    }
    let fields = construction_field_types(
        types
            .get(capture_type as usize)
            .ok_or(DecodeError::InvalidTable("capture type"))?,
        None,
    )
    .ok_or(DecodeError::InvalidTable("capture type"))?;
    let fields = fields
        .into_iter()
        .filter(|&field| {
            !matches!(
                types.get(field as usize).map(Type::representation),
                Some(Type::Available { .. })
            )
        })
        .collect::<Vec<_>>();
    (fields.len() == count)
        .then_some(fields)
        .ok_or(DecodeError::InvalidTable("capture count"))
}

fn unique_type(types: &[Type], predicate: impl Fn(&Type) -> bool) -> Option<TypeId> {
    let mut matches = types
        .iter()
        .enumerate()
        .filter(|(_, ty)| predicate(ty.representation()))
        .map(|(id, _)| id as TypeId);
    let first = matches.next()?;
    matches.next().is_none().then_some(first)
}

fn infer_primitive_types(
    types: &[Type],
    op: Primitive,
    dst: Register,
    args: &[Register],
    inferred: &mut [Option<TypeId>],
) -> Result<(), DecodeError> {
    let set = |inferred: &mut [Option<TypeId>], register: Register, ty: TypeId| {
        let slot = inferred
            .get_mut(register as usize)
            .ok_or(DecodeError::InvalidTable("register"))?;
        if slot.is_some_and(|actual| actual != ty) {
            return Err(DecodeError::InvalidTable("primitive signature"));
        }
        *slot = Some(ty);
        Ok(())
    };
    let known = |register: Register, inferred: &[Option<TypeId>]| {
        inferred.get(register as usize).copied().flatten()
    };
    let array = |element: TypeId| {
        unique_type(
            types,
            |ty| matches!(ty, Type::Array { element: actual } if *actual == element),
        )
    };
    let reference = |referent: TypeId, unique: bool| {
        unique_type(types, |ty| match ty {
            Type::RefShared { referent: actual } => !unique && *actual == referent,
            Type::RefUnique { referent: actual } => unique && *actual == referent,
            _ => false,
        })
    };
    let array_reference =
        |element, unique| array(element).and_then(|array| reference(array, unique));
    let set_arg = |index, ty, inferred: &mut [Option<TypeId>]| {
        args.get(index)
            .copied()
            .ok_or(DecodeError::InvalidTable("primitive signature"))
            .and_then(|register| set(inferred, register, ty))
    };
    use Primitive::*;
    match op {
        IntCheckedAdd | IntCheckedSub | IntCheckedMul | IntCheckedDiv | IntCheckedRem
        | IntWrappingAdd | IntWrappingSub | IntWrappingMul | IntBitAnd | IntBitOr | IntBitXor => {
            if let Some(ty) = known(dst, inferred)
                .or_else(|| args.iter().find_map(|register| known(*register, inferred)))
            {
                set(inferred, dst, ty)?;
                for &argument in args {
                    set(inferred, argument, ty)?;
                }
            }
        }
        IntBitNot | IntCheckedNeg | IntWrappingNeg => {
            if let Some(ty) = known(dst, inferred)
                .or_else(|| args.first().and_then(|register| known(*register, inferred)))
            {
                set(inferred, dst, ty)?;
                set_arg(0, ty, inferred)?;
            }
        }
        IntEq | IntNe | IntLt | IntLe | IntGt | IntGe => {
            set(inferred, dst, U32)?;
            if let Some(ty) = args.iter().find_map(|register| known(*register, inferred)) {
                for &argument in args {
                    set(inferred, argument, ty)?;
                }
            }
        }
        IntShl | IntShr => {
            set_arg(1, U32, inferred)?;
            if let Some(ty) = known(dst, inferred)
                .or_else(|| args.first().and_then(|register| known(*register, inferred)))
            {
                set(inferred, dst, ty)?;
                set_arg(0, ty, inferred)?;
            }
        }
        FloatAdd | FloatSub | FloatMul | FloatDiv | FloatRem => {
            if let Some(ty) = known(dst, inferred)
                .or_else(|| args.iter().find_map(|register| known(*register, inferred)))
            {
                set(inferred, dst, ty)?;
                for &argument in args {
                    set(inferred, argument, ty)?;
                }
            }
        }
        FloatEq | FloatNe | FloatLt | FloatLe | FloatGt | FloatGe => {
            set(inferred, dst, U32)?;
            if let Some(ty) = args.iter().find_map(|register| known(*register, inferred)) {
                for &argument in args {
                    set(inferred, argument, ty)?;
                }
            }
        }
        FloatNeg => {
            if let Some(ty) = known(dst, inferred)
                .or_else(|| args.first().and_then(|register| known(*register, inferred)))
            {
                set(inferred, dst, ty)?;
                set_arg(0, ty, inferred)?;
            }
        }
        BytesFromArrayMove => {
            set(inferred, dst, BYTES)?;
            if let Some(array) = array(U8) {
                set_arg(0, array, inferred)?;
            }
        }
        BytesToArray => {
            set_arg(0, BYTES, inferred)?;
            if let Some(array) = array(U8) {
                set(inferred, dst, array)?;
            }
        }
        ArrayNew => {
            set_arg(0, USIZE, inferred)?;
            if let Some(element) = args.get(1).and_then(|register| known(*register, inferred))
                && let Some(array) = array(element)
            {
                set(inferred, dst, array)?;
            }
            if let Some(Type::Array { element }) = known(dst, inferred)
                .and_then(|result| types.get(result as usize))
                .map(Type::representation)
            {
                set_arg(1, *element, inferred)?;
            }
        }
        ArrayLen | ArrayCapacity => set(inferred, dst, USIZE)?,
        ArrayGetCopy | ArrayGetMove => {
            set_arg(1, USIZE, inferred)?;
            if let Some(reference_ty) = args.first().and_then(|register| known(*register, inferred))
                && let Some(referent) =
                    match types.get(reference_ty as usize).map(Type::representation) {
                        Some(Type::RefShared { referent }) if op == ArrayGetCopy => Some(*referent),
                        Some(Type::RefUnique { referent }) if op == ArrayGetMove => Some(*referent),
                        _ => None,
                    }
                && let Some(Type::Array { element }) =
                    types.get(referent as usize).map(Type::representation)
            {
                set(inferred, dst, *element)?;
            }
            if let Some(element) = known(dst, inferred)
                && let Some(reference) = array_reference(element, op == ArrayGetMove)
            {
                set_arg(0, reference, inferred)?;
            }
        }
        ArrayGetBorrowShared | ArrayGetBorrowUnique => {
            set_arg(1, USIZE, inferred)?;
            let unique = op == ArrayGetBorrowUnique;
            if let Some(reference_ty) = args.first().and_then(|register| known(*register, inferred))
                && let Some(referent) =
                    match types.get(reference_ty as usize).map(Type::representation) {
                        Some(Type::RefShared { referent }) if !unique => Some(*referent),
                        Some(Type::RefUnique { referent }) if unique => Some(*referent),
                        _ => None,
                    }
                && let Some(Type::Array { element }) =
                    types.get(referent as usize).map(Type::representation)
                && let Some(result) = reference(*element, unique)
            {
                set(inferred, dst, result)?;
            }
            if let Some(result) = known(dst, inferred)
                && let Some(element) = match types.get(result as usize).map(Type::representation) {
                    Some(Type::RefShared { referent }) if !unique => Some(*referent),
                    Some(Type::RefUnique { referent }) if unique => Some(*referent),
                    _ => None,
                }
                && let Some(reference) = array_reference(element, unique)
            {
                set_arg(0, reference, inferred)?;
            }
        }
        ArraySetMove => {
            set(inferred, dst, UNIT)?;
            set_arg(1, USIZE, inferred)?;
            if let Some(element) = args.get(2).and_then(|register| known(*register, inferred))
                && let Some(reference) = array_reference(element, true)
            {
                set_arg(0, reference, inferred)?;
            }
        }
        ArrayEmpty => {}
        ArrayPushMove => {
            set(inferred, dst, UNIT)?;
            if let Some(element) = args.get(1).and_then(|register| known(*register, inferred))
                && let Some(reference) = array_reference(element, true)
            {
                set_arg(0, reference, inferred)?;
            }
        }
        ArrayPopMove => {
            if let Some(reference_ty) = args.first().and_then(|register| known(*register, inferred))
                && let Some(Type::RefUnique { referent }) =
                    types.get(reference_ty as usize).map(Type::representation)
                && let Some(Type::Array { element }) =
                    types.get(*referent as usize).map(Type::representation)
            {
                set(inferred, dst, *element)?;
            }
            if let Some(element) = known(dst, inferred)
                && let Some(reference) = array_reference(element, true)
            {
                set_arg(0, reference, inferred)?;
            }
        }
        ArrayReserve => {
            set(inferred, dst, UNIT)?;
            set_arg(1, USIZE, inferred)?;
        }
        ArrayFinishDrained => {
            set(inferred, dst, UNIT)?;
        }
        _ => {}
    }
    Ok(())
}
fn const_type(c: &Constant) -> u32 {
    match c {
        Constant::Unit => UNIT,
        Constant::U8(_) => U8,
        Constant::U16(_) => U16,
        Constant::U32(_) => U32,
        Constant::U64(_) => U64,
        Constant::U128(_) => U128,
        Constant::I8(_) => I8,
        Constant::I16(_) => I16,
        Constant::I32(_) => I32,
        Constant::I64(_) => I64,
        Constant::I128(_) => I128,
        Constant::Usize(_) => USIZE,
        Constant::Isize(_) => ISIZE,
        Constant::F32(_) => F32,
        Constant::F64(_) => F64,
        Constant::Char(_) => CHAR,
        Constant::Text(_) => TEXT,
        Constant::Bytes(_) => BYTES,
    }
}
fn words_bytes(w: &[u32]) -> Vec<u8> {
    w.iter().flat_map(|x| x.to_le_bytes()).collect()
}
fn decode_words(b: &[u8]) -> Result<Vec<u32>, DecodeError> {
    if !b.len().is_multiple_of(4) {
        return Err(DecodeError::InvalidTable("words"));
    }
    Ok(b.chunks_exact(4)
        .map(|x| u32::from_le_bytes(x.try_into().unwrap()))
        .collect())
}
fn align8(x: usize) -> usize {
    (x + 7) & !7
}
fn checked_align8(x: usize) -> Option<usize> {
    x.checked_add(7).map(|value| value & !7)
}
fn put_u16(w: &mut Vec<u8>, x: u16) {
    w.extend(x.to_le_bytes())
}
fn put_u32(w: &mut Vec<u8>, x: u32) {
    w.extend(x.to_le_bytes())
}
fn put_u64(w: &mut Vec<u8>, x: u64) {
    w.extend(x.to_le_bytes())
}
struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8], DecodeError> {
        let end = self.at.checked_add(n).ok_or(DecodeError::Truncated)?;
        let x = self.bytes.get(self.at..end).ok_or(DecodeError::Truncated)?;
        self.at = end;
        Ok(x)
    }
    fn u8(&mut self) -> Result<u8, DecodeError> {
        Ok(self.take(1)?[0])
    }
    fn u16(&mut self) -> Result<u16, DecodeError> {
        Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
    }
    fn u32(&mut self) -> Result<u32, DecodeError> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn u64(&mut self) -> Result<u64, DecodeError> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
    fn remaining(&self) -> usize {
        self.bytes.len() - self.at
    }
    fn finish(self) -> Result<(), DecodeError> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(DecodeError::NonCanonical("trailing bytes".into()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn canonical(artifact: Artifact) -> Artifact {
        if artifact.cleanups.is_empty() && !artifact.functions.is_empty() {
            crate::verify::with_generated_cleanup_plans(artifact).unwrap()
        } else {
            artifact
        }
    }

    #[test]
    fn decoder_infers_a_label_result_used_only_by_drop() {
        let mut artifact = Artifact {
            functions: vec![Function {
                flags: 0,
                name: "label_drop".into(),
                params: vec![I64],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, I64],
                code_start: 0,
                code_len: 4,
                label_slot_count: 1,
            }],
            code: vec![
                Instruction::LabelPush {
                    slot: 0,
                    result_register: 2,
                    target: 2,
                },
                Instruction::Leave { slot: 0, value: 1 },
                Instruction::Drop { register: 2 },
                Instruction::Return { src: None },
            ],
            cleanups: vec![
                CleanupPlan {
                    function: 0,
                    first_instruction: 1,
                    end_instruction: 2,
                    registers: vec![1, 2],
                },
                CleanupPlan {
                    function: 0,
                    first_instruction: 2,
                    end_instruction: 3,
                    registers: vec![2],
                },
            ],
            ..Artifact::default()
        };
        artifact.required_features = used_features(&artifact.types, &artifact.code, false, false);
        artifact = crate::verify::with_compiler_seeded_cleanup_plans(artifact).unwrap();

        let decoded = Artifact::decode(&artifact.encode()).unwrap();
        assert_eq!(decoded.functions[0].register_types[2], I64);
    }

    #[test]
    fn decoder_infers_a_projected_field_in_a_disconnected_cleanup_block() {
        let enum_ty = Type::predefined().len() as TypeId;
        let mut artifact = Artifact {
            constants: vec![Constant::I64(7)],
            functions: vec![Function {
                flags: 0,
                name: "known_enum_projection".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, enum_ty, enum_ty, I64],
                code_start: 0,
                code_len: 8,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Return { src: None },
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Construct {
                    dst: 2,
                    ty: enum_ty,
                    variant: Some(0),
                    fields: vec![1],
                },
                Instruction::Copy { dst: 3, src: 2 },
                Instruction::ProjectMove {
                    dst: 4,
                    src: 3,
                    field: 0,
                },
                Instruction::Deconstruct { src: 3 },
                Instruction::Drop { register: 4 },
                Instruction::Return { src: None },
            ],
            ..Artifact::default()
        };
        artifact.types.push(
            Type::Enum {
                name: "EitherWidth".into(),
                variants: vec![
                    EnumVariant {
                        name: "Wide".into(),
                        fields: vec![Field {
                            name: "value".into(),
                            ty: I64,
                        }],
                    tag: None,
},
                    EnumVariant {
                        name: "Narrow".into(),
                        fields: vec![Field {
                            name: "value".into(),
                            ty: U32,
                        }],
                    tag: None,
},
                ],
                copy: true,
            }
            .restricted(true, true),
        );
        artifact.required_features = used_features(&artifact.types, &artifact.code, false, false);
        artifact = crate::verify::with_generated_cleanup_plans(artifact).unwrap();

        let decoded = Artifact::decode(&artifact.encode()).unwrap();
        assert_eq!(decoded.functions[0].register_types[4], I64);
    }

    #[test]
    fn enum_facts_ignore_an_uninitialized_cleanup_join() {
        let constants = [];
        let code = [
            Instruction::Return { src: None },
            Instruction::Jump { target: 5 },
            Instruction::Construct {
                dst: 1,
                ty: 0,
                variant: Some(0),
                fields: vec![],
            },
            Instruction::Copy { dst: 2, src: 1 },
            Instruction::Jump { target: 5 },
            Instruction::ProjectMove {
                dst: 3,
                src: 2,
                field: 0,
            },
        ];

        let facts = infer_enum_variant_facts(&constants, 4, &code).unwrap();
        assert_eq!(facts[5][2], Some(0));
    }

    #[test]
    fn compact_wire_counts_are_bounded_before_capacity_reservation() {
        let contract_section = |payload: Vec<u8>| var_section(&[record(0, 0, payload)]);

        let mut excessive_routes = Vec::new();
        put_u32(&mut excessive_routes, 0);
        put_u32(&mut excessive_routes, u32::MAX);
        let excessive_routes = contract_section(excessive_routes);
        assert!(excessive_routes.len() < 64);
        assert!(matches!(
            decode_reference_return_contracts(&excessive_routes, 1, 1),
            Err(DecodeError::InvalidTable("reference return contract"))
        ));

        let mut excessive_path = Vec::new();
        put_u32(&mut excessive_path, 0);
        put_u32(&mut excessive_path, 1);
        put_u32(&mut excessive_path, u32::MAX);
        put_u32(&mut excessive_path, 1);
        put_u32(&mut excessive_path, 0);
        let excessive_path = contract_section(excessive_path);
        assert!(excessive_path.len() < 64);
        assert!(matches!(
            decode_reference_return_contracts(&excessive_path, 1, 1),
            Err(DecodeError::InvalidTable("reference return path"))
        ));

        assert!(matches!(
            decode_cleanups(&[], u32::MAX, &[], &[], &[]),
            Err(DecodeError::InvalidTable("cleanup count"))
        ));
        assert!(matches!(
            decode_drop_glue(&[], u32::MAX, 0, 0),
            Err(DecodeError::InvalidTable("drop glue"))
        ));
    }

    #[test]
    fn packed_code_shares_variable_operands_and_roundtrips_public_instructions() {
        let instructions = vec![
            Instruction::Construct {
                dst: 0,
                ty: 19,
                variant: None,
                fields: (0..1024).collect(),
            },
            Instruction::Construct {
                dst: 1,
                ty: 19,
                variant: None,
                fields: (0..1024).collect(),
            },
            Instruction::Abort {
                message: Some("packed abort".into()),
            },
        ];
        let public_bytes = instructions.len() * std::mem::size_of::<Instruction>()
            + instructions
                .iter()
                .map(|instruction| match instruction {
                    Instruction::Construct { fields, .. } => {
                        fields.capacity() * std::mem::size_of::<u32>()
                    }
                    Instruction::Abort {
                        message: Some(message),
                    } => message.capacity(),
                    _ => 0,
                })
                .sum::<usize>();
        let packed = PackedCode::from_instructions(&instructions);

        assert_eq!(packed.materialize(), instructions);
        assert_eq!(packed.operands.len(), 1024);
        assert!(packed.storage_bytes() < public_bytes);
    }

    #[test]
    fn operand_table_interns_instruction_and_cleanup_register_lists() {
        let instruction = Instruction::Construct {
            dst: 3,
            ty: 19,
            variant: None,
            fields: vec![1, 2],
        };
        let function = Function {
            name: "intern_operands".into(),
            flags: 0,
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, I64, I64, I64],
            code_start: 0,
            code_len: 4,
            label_slot_count: 0,
        };
        let plans = vec![
            CleanupPlan {
                function: 0,
                first_instruction: 0,
                end_instruction: 1,
                registers: vec![1, 2],
            },
            CleanupPlan {
                function: 0,
                first_instruction: 1,
                end_instruction: 2,
                registers: vec![2],
            },
            CleanupPlan {
                function: 0,
                first_instruction: 2,
                end_instruction: 3,
                registers: vec![2, 3],
            },
            CleanupPlan {
                function: 0,
                first_instruction: 3,
                end_instruction: 4,
                registers: vec![2],
            },
        ];
        let mut code = Vec::new();
        let mut operands = Vec::new();
        let mut operand_lists = BTreeMap::new();
        encode_instruction_with_operand_lists(
            &instruction,
            &BTreeMap::new(),
            &mut code,
            &mut operands,
            &mut operand_lists,
        );
        let (cleanups, spans) = encode_cleanups(
            &plans,
            std::slice::from_ref(&function),
            &mut operands,
            &mut operand_lists,
        )
        .unwrap();

        // [2] first reuses a suffix of [1, 2], and then a prefix of [2, 3].
        assert_eq!(operands, vec![1, 2, 2, 3]);
        assert_eq!(
            decode_instructions(&code, &operands, &[]).unwrap(),
            [instruction]
        );
        assert_eq!(
            decode_cleanups(&cleanups, 4, &operands, &[function], &spans).unwrap(),
            plans
        );
    }

    #[test]
    fn reference_return_contracts_roundtrip_in_their_critical_section() {
        let mut types = Type::predefined();
        let shared = types.len() as TypeId;
        types.push(Type::RefShared { referent: I64 });
        let artifact = crate::verify::with_generated_cleanup_plans(Artifact {
            required_features: CORE_G1 | REFERENCES_G1,
            types,
            reference_return_contracts: vec![ReferenceReturnContract {
                function: 0,
                routes: vec![ReferenceReturnRoute {
                    result_path: vec![],
                    origin: ReferenceReturnOrigin::Parameter {
                        parameter: 0,
                        path: vec![],
                    },
                }],
            }],
            functions: vec![Function {
                name: "identity".into(),
                flags: 0,
                params: vec![shared],
                return_type: shared,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, shared, shared],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Copy { dst: 2, src: 1 },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        })
        .unwrap();
        let bytes = artifact.encode();
        let decoded = Artifact::decode(&bytes).unwrap();
        assert_eq!(
            decoded.reference_return_contracts,
            artifact.reference_return_contracts
        );
        assert_eq!(decoded.encode(), bytes);
    }
    fn artifact() -> Artifact {
        crate::verify::with_generated_cleanup_plans(Artifact {
            constants: vec![Constant::I64(7)],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ],
            ..Artifact::default()
        })
        .unwrap()
    }

    #[test]
    fn canonicalizes_constants_by_exact_wire_payload_and_deduplicates() {
        let mut constants = (0..=256)
            .map(|index| Constant::Text(format!("name-{index:03}")))
            .collect::<Vec<_>>();
        constants.push(Constant::Text("name-001".into()));
        let mut artifact = Artifact {
            constants,
            code: vec![
                Instruction::Const {
                    dst: 0,
                    constant: 1,
                },
                Instruction::Const {
                    dst: 1,
                    constant: 257,
                },
            ],
            ..Artifact::default()
        };

        artifact.canonicalize_constants();

        // String IDs 0 and 256 both begin with a zero byte in little endian,
        // so the latter precedes string ID 1 in the canonical wire ordering.
        assert_eq!(artifact.constants[0], Constant::Text("name-000".into()));
        assert_eq!(artifact.constants[1], Constant::Text("name-256".into()));
        assert_eq!(artifact.constants[2], Constant::Text("name-001".into()));
        assert_eq!(artifact.constants.len(), 257);
        assert_eq!(
            artifact.code,
            vec![
                Instruction::Const {
                    dst: 0,
                    constant: 2,
                },
                Instruction::Const {
                    dst: 1,
                    constant: 2,
                },
            ]
        );

        // The encoder itself is the authoritative check that the resulting
        // pool satisfies the frozen `(tag, payload bytes)` contract.
        artifact.code.clear();
        let bytes = artifact.encode();
        assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    }

    #[test]
    fn golden_header_and_directory() {
        let b = artifact().encode();
        assert_eq!(&b[..8], b"GRBC\r\n\x1a\n");
        assert_eq!(&b[8..16], &[1, 0, 0, 0, 64, 0, 0, 0]);
        assert_eq!(u32::from_le_bytes(b[20..24].try_into().unwrap()), 14);
        assert_eq!(u32::from_le_bytes(b[24..28].try_into().unwrap()), 32);
        assert_eq!(u64::from_le_bytes(b[48..56].try_into().unwrap()), 64);
        assert_eq!(u32::from_le_bytes(b[64..68].try_into().unwrap()), 1);
        assert_eq!(u32::from_le_bytes(b[96..100].try_into().unwrap()), 2)
    }
    #[test]
    fn rejects_unpadded_final_section_without_panicking() {
        let mut bytes = artifact().encode();
        let contract_directory = 64 + (14 - 1) * 32;
        let contract_offset = u64::from_le_bytes(
            bytes[contract_directory + 8..contract_directory + 16]
                .try_into()
                .unwrap(),
        ) as usize;
        assert_eq!(contract_offset + 8, bytes.len());

        bytes.push(0);
        let file_size = bytes.len() as u64;
        bytes[56..64].copy_from_slice(&file_size.to_le_bytes());
        bytes[contract_directory + 16..contract_directory + 24]
            .copy_from_slice(&9u64.to_le_bytes());

        assert_eq!(Artifact::decode(&bytes), Err(DecodeError::InvalidDirectory));
    }
    #[test]
    fn rejects_overflowing_switch_operand_count_without_panicking() {
        let words = [0x021 | (4 << 12), 0, 0, u32::MAX, 0];
        assert_eq!(
            decode_instructions(&words, &[], &[]),
            Err(DecodeError::InvalidTable("operands"))
        );
    }
    #[test]
    fn canonical_roundtrip() {
        let a = artifact();
        let b = a.encode();
        assert_eq!(Artifact::decode(&b).unwrap(), a);
        assert_eq!(Artifact::decode(&b).unwrap().encode(), b)
    }

    #[test]
    fn instantiated_protocol_arguments_roundtrip_and_reject_invalid_type_ids() {
        let protocols = vec![
            Protocol {
                display_name: "Generic".into(),
                type_arguments: vec![I64],
                operations: vec![],
            },
            Protocol {
                display_name: "Generic".into(),
                type_arguments: vec![TEXT],
                operations: vec![],
            },
        ];
        let artifact = Artifact {
            required_features: CORE_G1 | HANDLERS_G1,
            types: Type::predefined(),
            protocols,
            ..Artifact::default()
        };
        let bytes = artifact.encode();
        let decoded = Artifact::decode(&bytes).unwrap();
        assert_eq!(decoded.protocols, artifact.protocols);
        assert_eq!(decoded.encode(), bytes);

        let mut unordered = artifact.clone();
        unordered.protocols.swap(0, 1);
        assert_eq!(
            unordered.encode_impl(),
            Err(DecodeError::NonCanonical(
                "protocol identities must be sorted and unique".into()
            ))
        );

        let mut invalid = artifact;
        invalid.protocols[1].type_arguments[0] = u32::MAX;
        assert_eq!(
            invalid.encode_impl(),
            Err(DecodeError::InvalidTable("protocol type argument"))
        );
    }

    #[test]
    fn deconstruct_has_a_canonical_opcode_and_debug_spelling() {
        let instruction = Instruction::Deconstruct { src: 7 };
        let mut words = Vec::new();
        let mut operands = Vec::new();
        encode_instruction(&instruction, &BTreeMap::new(), &mut words, &mut operands);

        assert_eq!(words, vec![0x1013, 7]);
        assert!(operands.is_empty());
        assert_eq!(
            decode_instructions(&words, &operands, &[]).unwrap(),
            vec![instruction]
        );
        assert_eq!(
            format!("{:?}", Instruction::Deconstruct { src: 7 }),
            "Deconstruct { src: 7 }"
        );
    }

    #[test]
    fn self_call_opcodes_roundtrip_at_their_permanent_assignments() {
        let instructions = [
            (
                Instruction::CallSelf {
                    dst: Some(7),
                    args: vec![2, 3],
                },
                0x02b,
            ),
            (Instruction::TailCallSelf { args: vec![4, 5] }, 0x02c),
        ];
        for (instruction, opcode) in instructions {
            let mut words = Vec::new();
            let mut operands = Vec::new();
            encode_instruction(&instruction, &BTreeMap::new(), &mut words, &mut operands);
            assert_eq!(words[0] & 0xfff, opcode);
            assert_eq!(
                decode_instructions(&words, &operands, &[]).unwrap(),
                vec![instruction]
            );
        }
    }

    #[test]
    fn tail_resume_roundtrips_at_its_permanent_opcode() {
        let instruction = Instruction::TailResume {
            resumption: 7,
            receiver_mode: 2,
            value: 8,
        };
        let mut words = Vec::new();
        let mut operands = Vec::new();
        encode_instruction(&instruction, &BTreeMap::new(), &mut words, &mut operands);

        assert_eq!(words, vec![0x3048, 7, 2, 8]);
        assert!(operands.is_empty());
        assert_eq!(
            decode_instructions(&words, &operands, &[]).unwrap(),
            vec![instruction]
        );
    }

    #[test]
    fn known_receiver_call_opcodes_roundtrip_at_their_permanent_assignments() {
        let instructions = [
            (
                Instruction::CallKnownReceiver {
                    dst: Some(7),
                    function: 11,
                    receiver: 3,
                    args: vec![4, 5],
                },
                0x02d,
            ),
            (
                Instruction::TailCallKnownReceiver {
                    function: 12,
                    receiver: 6,
                    args: vec![8, 9],
                },
                0x02e,
            ),
        ];
        for (instruction, opcode) in instructions {
            let mut words = Vec::new();
            let mut operands = Vec::new();
            encode_instruction(&instruction, &BTreeMap::new(), &mut words, &mut operands);
            assert_eq!(words[0] & 0xfff, opcode);
            assert_eq!(
                decode_instructions(&words, &operands, &[]).unwrap(),
                vec![instruction]
            );
        }
    }

    #[test]
    fn deref_copy_has_frozen_opcode_roundtrips_and_infers_its_referent() {
        let instruction = Instruction::DerefCopy { dst: 7, src: 8 };
        let mut words = Vec::new();
        let mut operands = Vec::new();
        encode_instruction(&instruction, &BTreeMap::new(), &mut words, &mut operands);
        assert_eq!(words, vec![0x2014, 7, 8]);
        assert!(operands.is_empty());
        assert_eq!(
            decode_instructions(&words, &operands, &[]).unwrap(),
            vec![instruction]
        );
        assert_eq!(
            decode_instructions(&[0x1014, 7], &[], &[]),
            Err(DecodeError::InvalidTable("instruction operands"))
        );

        let mut types = Type::predefined();
        let shared_i64 = types.len() as TypeId;
        types.push(Type::RefShared { referent: I64 });
        let artifact = Artifact {
            required_features: CORE_G1 | REFERENCES_G1,
            types,
            cleanups: vec![],
            functions: vec![Function {
                flags: 0,
                name: "read".into(),
                params: vec![shared_i64],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, shared_i64, I64],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::DerefCopy { dst: 2, src: 1 },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        };
        let bytes = artifact.encode();
        assert_eq!(Artifact::decode(&bytes).unwrap(), canonical(artifact));
        assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    }

    #[test]
    fn stored_reference_reborrow_opcodes_roundtrip_at_permanent_assignments() {
        let instructions = [
            Instruction::DerefReborrowShared { dst: 7, src: 8 },
            Instruction::DerefReborrowUnique { dst: 9, src: 10 },
        ];
        let mut words = Vec::new();
        let mut operands = Vec::new();
        for instruction in &instructions {
            encode_instruction(instruction, &BTreeMap::new(), &mut words, &mut operands);
        }
        assert_eq!(words, vec![0x2017, 7, 8, 0x2018, 9, 10]);
        assert!(operands.is_empty());
        assert_eq!(
            decode_instructions(&words, &operands, &[]).unwrap(),
            instructions
        );

        let mut types = Type::predefined();
        let shared_i64 = types.len() as TypeId;
        types.push(Type::RefShared { referent: I64 });
        let unique_i64 = types.len() as TypeId;
        types.push(Type::RefUnique { referent: I64 });
        let shared_stored = types.len() as TypeId;
        types.push(Type::RefShared {
            referent: shared_i64,
        });
        let unique_stored = types.len() as TypeId;
        types.push(Type::RefUnique {
            referent: unique_i64,
        });
        let artifact = Artifact {
            required_features: CORE_G1 | REFERENCES_G1,
            types,
            functions: vec![
                Function {
                    flags: 0,
                    name: "shared-stored-reborrow".into(),
                    params: vec![shared_stored],
                    return_type: shared_i64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, shared_stored, shared_i64],
                    code_start: 0,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "unique-stored-reborrow".into(),
                    params: vec![unique_stored],
                    return_type: unique_i64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, unique_stored, unique_i64],
                    code_start: 2,
                    code_len: 2,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::DerefReborrowShared { dst: 2, src: 1 },
                Instruction::Return { src: Some(2) },
                Instruction::DerefReborrowUnique { dst: 2, src: 1 },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        };
        let bytes = artifact.encode();
        let decoded = Artifact::decode(&bytes).unwrap();
        assert_eq!(decoded.functions[0].register_types[2], shared_i64);
        assert_eq!(decoded.functions[1].register_types[2], unique_i64);
        assert_eq!(decoded.encode(), bytes);
    }

    #[test]
    fn deref_move_store_have_frozen_opcodes_and_infer_exact_types() {
        let instructions = [
            Instruction::DerefMove { dst: 7, src: 8 },
            Instruction::DerefStore { dst: 8, src: 7 },
        ];
        let mut words = Vec::new();
        let mut operands = Vec::new();
        for instruction in &instructions {
            encode_instruction(instruction, &BTreeMap::new(), &mut words, &mut operands);
        }
        assert_eq!(words, vec![0x2015, 7, 8, 0x2016, 8, 7]);
        assert!(operands.is_empty());
        assert_eq!(
            decode_instructions(&words, &operands, &[]).unwrap(),
            instructions
        );

        let mut types = Type::predefined();
        let unique_i64 = types.len() as TypeId;
        types.push(Type::RefUnique { referent: I64 });
        let artifact = Artifact {
            required_features: CORE_G1 | REFERENCES_G1,
            types,
            functions: vec![Function {
                flags: 0,
                name: "replace".into(),
                params: vec![unique_i64, I64],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, unique_i64, I64, I64],
                code_start: 0,
                code_len: 4,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::DerefMove { dst: 3, src: 1 },
                Instruction::DerefStore { dst: 1, src: 2 },
                Instruction::EndBorrow { reference: 1 },
                Instruction::Return { src: Some(3) },
            ],
            ..Artifact::default()
        };
        let bytes = artifact.encode();
        assert_eq!(Artifact::decode(&bytes).unwrap(), canonical(artifact));
    }

    #[test]
    fn shared_handler_has_a_permanent_opcode_and_rejects_hostile_ranges() {
        let instruction = Instruction::MakeHandlerShared {
            dst: 1,
            handler_def: 2,
            functions: vec![3, 4],
            captures: vec![5],
        };
        let mut words = Vec::new();
        let mut operands = Vec::new();
        encode_instruction(&instruction, &BTreeMap::new(), &mut words, &mut operands);

        assert_eq!(words, vec![0x6047, 1, 2, 0, 2, 2, 1]);
        assert_eq!(operands, vec![3, 4, 5]);
        assert_eq!(
            decode_instructions(&words, &operands, &[]).unwrap(),
            vec![instruction]
        );

        let hostile = [0x6047, 1, 2, 0, u32::MAX, 0, 0];
        assert_eq!(
            decode_instructions(&hostile, &[], &[]),
            Err(DecodeError::InvalidTable("operands"))
        );
        let wrong_arity = [0x5047, 1, 2, 0, 0, 0];
        assert_eq!(
            decode_instructions(&wrong_arity, &[], &[]),
            Err(DecodeError::InvalidTable("instruction operands"))
        );
    }
    #[test]
    fn hostile_decoder_corpus_never_panics() {
        fn decode_without_panicking(label: &str, bytes: &[u8]) {
            let result = std::panic::catch_unwind(|| Artifact::decode(bytes));
            assert!(
                result.is_ok(),
                "decoder panicked for {label} ({} bytes)",
                bytes.len()
            );
        }

        let canonical = artifact().encode();

        // Every truncation exercises header, directory, section, record, code,
        // and padding boundaries of a real artifact.
        for end in 0..=canonical.len() {
            decode_without_panicking("canonical truncation", &canonical[..end]);
        }

        // Perturb every byte of a canonical artifact with representative bit
        // patterns, then overwrite aligned fields with troublesome counts,
        // lengths, offsets, opcode operands, and reserved-bit values.
        for offset in 0..canonical.len() {
            for mask in [0x01, 0x80, 0xff] {
                let mut bytes = canonical.clone();
                bytes[offset] ^= mask;
                decode_without_panicking("single-byte mutation", &bytes);
            }
        }
        for offset in (0..canonical.len().saturating_sub(3)).step_by(4) {
            for value in [0, 1, u32::MAX, 0x8000_0000, canonical.len() as u32] {
                let mut bytes = canonical.clone();
                bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
                decode_without_panicking("four-byte field mutation", &bytes);
            }
        }
        for offset in (0..canonical.len().saturating_sub(7)).step_by(8) {
            for value in [
                0,
                1,
                u64::MAX,
                0x8000_0000_0000_0000,
                canonical.len() as u64,
            ] {
                let mut bytes = canonical.clone();
                bytes[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
                decode_without_panicking("eight-byte field mutation", &bytes);
            }
        }

        // A deterministic xorshift corpus covers arbitrary short inputs and
        // canonical-prefix/suffix combinations without a fuzz dependency.
        let mut state = 0x6a09_e667_f3bc_c909u64;
        let mut random = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for case in 0..2_000 {
            let length = match case % 4 {
                0 => case % 96,
                1 => random() as usize % 512,
                2 => random() as usize % 2_048,
                _ => random() as usize % 4_096,
            };
            let mut bytes = Vec::with_capacity(length);
            while bytes.len() < length {
                bytes.extend_from_slice(&random().to_le_bytes());
            }
            bytes.truncate(length);
            if case % 3 == 0 {
                let prefix = bytes
                    .len()
                    .min(canonical.len())
                    .min((random() as usize) % 65);
                bytes[..prefix].copy_from_slice(&canonical[..prefix]);
            }
            decode_without_panicking("fixed-seed arbitrary input", &bytes);
        }
    }

    #[test]
    fn rejects_unrepresentable_register_count_before_allocating() {
        let mut bytes = artifact().encode();
        let functions_directory = 64 + (8 - 1) * 32;
        let functions_offset = u64::from_le_bytes(
            bytes[functions_directory + 8..functions_directory + 16]
                .try_into()
                .unwrap(),
        ) as usize;
        // name, signature, flags, then register count.
        bytes[functions_offset + 12..functions_offset + 16]
            .copy_from_slice(&u32::MAX.to_le_bytes());
        assert_eq!(
            Artifact::decode(&bytes),
            Err(DecodeError::InvalidTable("function registers"))
        );
    }

    #[test]
    fn rejects_repeated_predefined_and_structural_type_encodings() {
        let mut repeated_scalar = artifact();
        repeated_scalar.types.push(Type::Unit);
        assert_eq!(
            Artifact::decode(&repeated_scalar.encode()),
            Err(DecodeError::NonCanonical(
                "predefined scalar type appears more than once".into()
            ))
        );

        let mut repeated_array = artifact();
        repeated_array
            .types
            .extend([Type::Array { element: U64 }, Type::Array { element: U64 }]);
        assert_eq!(
            Artifact::decode(&repeated_array.encode()),
            Err(DecodeError::NonCanonical(
                "duplicate structural type encoding".into()
            ))
        );
    }

    #[test]
    fn allows_distinct_nominal_types_with_the_same_layout() {
        let mut nominal = artifact();
        nominal.types.extend([
            Type::Struct {
                name: "Left".into(),
                fields: vec![Field {
                    name: "value".into(),
                    ty: U64,
                }],
                copy: false,
            },
            Type::Struct {
                name: "Right".into(),
                fields: vec![Field {
                    name: "value".into(),
                    ty: U64,
                }],
                copy: false,
            },
        ]);
        assert_eq!(Artifact::decode(&nominal.encode()).unwrap(), nominal);
    }
    #[test]
    fn rejects_nonzero_format_minor() {
        let mut bytes = artifact().encode();
        bytes[10..12].copy_from_slice(&1u16.to_le_bytes());
        assert_eq!(Artifact::decode(&bytes), Err(DecodeError::InvalidHeader));
    }
    #[test]
    fn all_scalar_constants_roundtrip_exactly() {
        let constants = vec![
            Constant::Unit,
            Constant::U8(u8::MAX),
            Constant::U16(0x1234),
            Constant::U32(0x12345678),
            Constant::U64(0x123456789abcdef0),
            Constant::U128(0x0123456789abcdef_fedcba9876543210),
            Constant::I8(-2),
            Constant::I16(-0x1234),
            Constant::I32(-0x1234567),
            Constant::I64(-0x123456789abcdef),
            Constant::I128(-0x0012_3456_789a_bcde_ffed_cba9_8765_4321),
            Constant::Usize(u64::MAX),
            Constant::Isize(i64::MIN),
            Constant::F32(-0.0),
            Constant::F64(-0.0),
            Constant::Char('\u{1f600}'),
            Constant::Text("grandiose".into()),
            Constant::Bytes(vec![0, 1, 0xff]),
        ];
        let artifact = Artifact {
            constants,
            ..Artifact::default()
        };

        let bytes = artifact.encode();
        let decoded = Artifact::decode(&bytes).unwrap();
        assert_eq!(decoded, canonical(artifact));
        let Constant::F32(zero32) = decoded.constants[13] else {
            panic!()
        };
        let Constant::F64(zero64) = decoded.constants[14] else {
            panic!()
        };
        assert_eq!(zero32.to_bits(), (-0.0_f32).to_bits());
        assert_eq!(zero64.to_bits(), (-0.0_f64).to_bits());
        assert_eq!(decoded.encode(), bytes);
    }

    #[test]
    fn float_constant_codec_canonicalizes_and_rejects_hostile_nan_payloads() {
        let artifact = Artifact {
            constants: vec![
                Constant::F32(f32::from_bits(0xff80_0001)),
                Constant::F64(f64::from_bits(0xfff0_0000_0000_0001)),
            ],
            ..Artifact::default()
        };
        let bytes = artifact.encode();
        let decoded = Artifact::decode(&bytes).unwrap();
        let Constant::F32(nan32) = decoded.constants[0] else {
            panic!()
        };
        let Constant::F64(nan64) = decoded.constants[1] else {
            panic!()
        };
        assert_eq!(nan32.to_bits(), 0x7fc0_0000);
        assert_eq!(nan64.to_bits(), 0x7ff8_0000_0000_0000);

        for (canonical, hostile) in [
            (
                0x7fc0_0000_u32.to_le_bytes().to_vec(),
                0x7fc0_0001_u32.to_le_bytes().to_vec(),
            ),
            (
                0x7ff8_0000_0000_0000_u64.to_le_bytes().to_vec(),
                0xfff8_0000_0000_0001_u64.to_le_bytes().to_vec(),
            ),
        ] {
            let mut hostile_bytes = bytes.clone();
            let offset = hostile_bytes
                .windows(canonical.len())
                .position(|window| window == canonical)
                .expect("canonical NaN payload is present once in the constant table");
            hostile_bytes[offset..offset + hostile.len()].copy_from_slice(&hostile);
            assert_eq!(
                Artifact::decode(&hostile_bytes),
                Err(DecodeError::NonCanonical("NaN".into()))
            );
        }
    }
    #[test]
    fn extended_primitive_ids_roundtrip_with_inferred_result_types() {
        let a = Artifact {
            constants: vec![Constant::Text("grandiose".into())],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: USIZE,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, TEXT, USIZE],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Primitive {
                    dst: 2,
                    op: Primitive::TextByteLen,
                    args: vec![1],
                },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        };
        let bytes = a.encode();
        assert_eq!(Artifact::decode(&bytes).unwrap(), canonical(a));
    }

    #[test]
    fn array_borrow_result_types_infer_from_known_array_references() {
        let mut types = Type::predefined();
        let array = types.len() as TypeId;
        types.push(Type::Array { element: U32 });
        let shared_array = types.len() as TypeId;
        types.push(Type::RefShared { referent: array });
        let unique_array = types.len() as TypeId;
        types.push(Type::RefUnique { referent: array });
        let shared_element = types.len() as TypeId;
        types.push(Type::RefShared { referent: U32 });
        let unique_element = types.len() as TypeId;
        types.push(Type::RefUnique { referent: U32 });
        let artifact = Artifact {
            required_features: CORE_G1 | REFERENCES_G1,
            types,
            functions: vec![
                Function {
                    flags: 0,
                    name: "shared".into(),
                    params: vec![shared_array, USIZE],
                    return_type: shared_element,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, shared_array, USIZE, shared_element],
                    code_start: 0,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "unique".into(),
                    params: vec![unique_array, USIZE],
                    return_type: unique_element,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, unique_array, USIZE, unique_element],
                    code_start: 2,
                    code_len: 2,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Primitive {
                    dst: 3,
                    op: Primitive::ArrayGetBorrowShared,
                    args: vec![1, 2],
                },
                Instruction::Return { src: Some(3) },
                Instruction::Primitive {
                    dst: 3,
                    op: Primitive::ArrayGetBorrowUnique,
                    args: vec![1, 2],
                },
                Instruction::Return { src: Some(3) },
            ],
            ..Artifact::default()
        };
        let bytes = artifact.encode();
        assert_eq!(Artifact::decode(&bytes).unwrap(), canonical(artifact));
    }

    #[test]
    fn numeric_conversion_primitive_ids_roundtrip_at_assigned_values() {
        let cases = [
            ("a", I8, U16, Primitive::IntConvertChecked, 0x0014),
            ("b", I8, U16, Primitive::IntConvertWrapping, 0x0015),
            ("c", F64, F32, Primitive::FloatConvert, 0x002b),
            ("d", I128, F64, Primitive::IntToFloat, 0x002d),
            ("e", F32, I32, Primitive::FloatToIntChecked, 0x002e),
            ("f", F32, U32, Primitive::FloatToBits, 0x002f),
            ("g", U64, F64, Primitive::FloatFromBits, 0x0032),
        ];
        let functions = cases
            .iter()
            .enumerate()
            .map(|(index, (name, parameter, result, _, _))| Function {
                flags: 0,
                name: (*name).into(),
                params: vec![*parameter],
                return_type: *result,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, *parameter, *result],
                code_start: (index * 2) as u32,
                code_len: 2,
                label_slot_count: 0,
            })
            .collect();
        let code = cases
            .iter()
            .flat_map(|(_, _, _, primitive, id)| {
                assert_eq!(*primitive as u32, *id);
                assert_eq!(Primitive::from_u32(*id), Some(*primitive));
                [
                    Instruction::Primitive {
                        dst: 2,
                        op: *primitive,
                        args: vec![1],
                    },
                    Instruction::Return { src: Some(2) },
                ]
            })
            .collect();
        let artifact = Artifact {
            functions,
            code,
            ..Artifact::default()
        };
        let bytes = artifact.encode();
        assert_eq!(Artifact::decode(&bytes).unwrap(), canonical(artifact));
    }

    #[test]
    fn numeric_same_type_primitive_anchors_conversion_temporaries() {
        let artifact = Artifact {
            constants: vec![Constant::U8(3)],
            functions: vec![Function {
                flags: 0,
                name: "conversion-chain".into(),
                params: vec![I64],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, U8, U8, U8, U8, I64],
                code_start: 0,
                code_len: 6,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Primitive {
                    dst: 2,
                    op: Primitive::IntConvertWrapping,
                    args: vec![1],
                },
                Instruction::Move { dst: 3, src: 2 },
                Instruction::Const {
                    dst: 4,
                    constant: 0,
                },
                Instruction::Primitive {
                    dst: 5,
                    op: Primitive::IntCheckedRem,
                    args: vec![3, 4],
                },
                Instruction::Primitive {
                    dst: 6,
                    op: Primitive::IntConvertWrapping,
                    args: vec![5],
                },
                Instruction::Return { src: Some(6) },
            ],
            ..Artifact::default()
        };
        let bytes = artifact.encode();
        assert_eq!(Artifact::decode(&bytes).unwrap(), canonical(artifact));
    }

    #[test]
    fn numeric_primitive_signatures_cover_every_frozen_scalar_width() {
        let types = Type::predefined();
        for integer in [
            U8, U16, U32, U64, U128, I8, I16, I32, I64, I128, USIZE, ISIZE,
        ] {
            assert!(primitive_signature(
                &types,
                Primitive::IntCheckedAdd,
                &[integer, integer],
                integer,
            ));
            assert!(primitive_signature(
                &types,
                Primitive::IntShl,
                &[integer, U32],
                integer,
            ));
            assert!(primitive_signature(
                &types,
                Primitive::IntLt,
                &[integer, integer],
                U32,
            ));
            for target in [
                U8, U16, U32, U64, U128, I8, I16, I32, I64, I128, USIZE, ISIZE,
            ] {
                assert!(primitive_signature(
                    &types,
                    Primitive::IntConvertChecked,
                    &[integer],
                    target,
                ));
                assert!(primitive_signature(
                    &types,
                    Primitive::IntConvertWrapping,
                    &[integer],
                    target,
                ));
            }
            for float in [F32, F64] {
                assert!(primitive_signature(
                    &types,
                    Primitive::IntToFloat,
                    &[integer],
                    float,
                ));
                assert!(primitive_signature(
                    &types,
                    Primitive::FloatToIntChecked,
                    &[float],
                    integer,
                ));
            }
        }
        for float in [F32, F64] {
            assert!(primitive_signature(
                &types,
                Primitive::FloatAdd,
                &[float, float],
                float,
            ));
            for target in [F32, F64] {
                assert!(primitive_signature(
                    &types,
                    Primitive::FloatConvert,
                    &[float],
                    target,
                ));
            }
        }
        assert!(primitive_signature(
            &types,
            Primitive::FloatToBits,
            &[F32],
            U32
        ));
        assert!(primitive_signature(
            &types,
            Primitive::FloatToBits,
            &[F64],
            U64
        ));
        assert!(primitive_signature(
            &types,
            Primitive::FloatFromBits,
            &[U32],
            F32
        ));
        assert!(primitive_signature(
            &types,
            Primitive::FloatFromBits,
            &[U64],
            F64
        ));
        for (op, args, result) in [
            (Primitive::FloatToBits, vec![F32], U64),
            (Primitive::FloatToBits, vec![F64], U32),
            (Primitive::FloatFromBits, vec![U32], F64),
            (Primitive::FloatFromBits, vec![U64], F32),
        ] {
            assert!(!primitive_signature(&types, op, &args, result));
        }
        assert!(!primitive_signature(
            &types,
            Primitive::IntCheckedAdd,
            &[U8, U16],
            U8,
        ));
        assert!(!primitive_signature(
            &types,
            Primitive::FloatAdd,
            &[F32, F64],
            F64,
        ));
        assert!(!primitive_signature(
            &types,
            Primitive::FloatToIntChecked,
            &[F64],
            F32,
        ));
    }
    #[test]
    fn array_and_reference_descriptors_roundtrip_canonically() {
        let mut types = Type::predefined();
        types.push(Type::Array { element: U8 });
        types.push(Type::RefShared { referent: 19 });
        let a = Artifact {
            required_features: CORE_G1 | REFERENCES_G1,
            types,
            cleanups: vec![],
            functions: vec![Function {
                flags: 0,
                name: "observe".into(),
                params: vec![19],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 20],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::BorrowShared { dst: 2, src: 1 },
                Instruction::EndBorrow { reference: 2 },
                Instruction::Return { src: Some(1) },
            ],
            ..Artifact::default()
        };
        let bytes = a.encode();
        assert_eq!(Artifact::decode(&bytes).unwrap(), canonical(a));
        assert_eq!(Artifact::decode(&bytes).unwrap().encode(), bytes);
    }

    #[test]
    fn array_finish_drained_has_permanent_id_and_exact_feature() {
        assert_eq!(Primitive::ArrayFinishDrained as u32, 0x006c);
        assert_eq!(
            Primitive::from_u32(0x006c),
            Some(Primitive::ArrayFinishDrained)
        );
        assert_eq!(
            format!("{:?}", Primitive::ArrayFinishDrained),
            "ArrayFinishDrained"
        );

        let mut types = Type::predefined();
        types[U64 as usize] = Type::U64.restricted(false, false);
        types.push(Type::Array { element: U64 });
        let artifact = Artifact {
            required_features: CORE_G1 | ARRAY_FINISH_DRAINED_G1,
            types,
            cleanups: vec![],
            functions: vec![Function {
                flags: 0,
                name: "finish".into(),
                params: vec![19],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, UNIT],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Primitive {
                    dst: 2,
                    op: Primitive::ArrayFinishDrained,
                    args: vec![1],
                },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        };
        let encoded = artifact.encode();
        assert_eq!(Artifact::decode(&encoded).unwrap(), canonical(artifact));

        let mut missing = encoded.clone();
        missing[32] &= !(ARRAY_FINISH_DRAINED_G1 as u8);
        assert!(matches!(
            Artifact::decode(&missing),
            Err(DecodeError::NonCanonical(message))
                if message == "required feature bits do not exactly describe the artifact"
        ));

        let mut spurious = Artifact::default().encode();
        spurious[32] |= ARRAY_FINISH_DRAINED_G1 as u8;
        assert!(matches!(
            Artifact::decode(&spurious),
            Err(DecodeError::NonCanonical(message))
                if message == "required feature bits do not exactly describe the artifact"
        ));
    }

    #[test]
    fn bytes_utf8_valid_up_to_has_permanent_id_signature_and_exact_feature() {
        assert_eq!(Primitive::BytesUtf8ValidUpTo as u32, 0x0056);
        assert_eq!(
            Primitive::from_u32(0x0056),
            Some(Primitive::BytesUtf8ValidUpTo)
        );
        assert_eq!(
            primitive_result_type(Primitive::BytesUtf8ValidUpTo, &[BYTES]),
            Some(USIZE)
        );

        let artifact = Artifact {
            required_features: CORE_G1 | BYTES_UTF8_VALID_UP_TO_G1,
            functions: vec![Function {
                flags: 0,
                name: "valid_up_to".into(),
                params: vec![BYTES],
                return_type: USIZE,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, BYTES, USIZE],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Primitive {
                    dst: 2,
                    op: Primitive::BytesUtf8ValidUpTo,
                    args: vec![1],
                },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        };
        let encoded = artifact.encode();
        assert_eq!(Artifact::decode(&encoded).unwrap(), canonical(artifact));

        let mut missing = encoded.clone();
        missing[33] &= !((BYTES_UTF8_VALID_UP_TO_G1 >> 8) as u8);
        assert!(matches!(
            Artifact::decode(&missing),
            Err(DecodeError::NonCanonical(message))
                if message == "required feature bits do not exactly describe the artifact"
        ));

        let mut spurious = Artifact::default().encode();
        spurious[33] |= (BYTES_UTF8_VALID_UP_TO_G1 >> 8) as u8;
        assert!(matches!(
            Artifact::decode(&spurious),
            Err(DecodeError::NonCanonical(message))
                if message == "required feature bits do not exactly describe the artifact"
        ));
    }

    #[test]
    fn restricted_use_capabilities_roundtrip_without_changing_layout() {
        let mut a = artifact();
        a.types[I64 as usize] = Type::I64.restricted(false, false);
        a.types.extend([
            Type::Array { element: U8 }.restricted(false, true),
            Type::RefShared { referent: I64 }.restricted(false, true),
            Type::Tuple {
                fields: vec![U8],
                copy: true,
            }
            .restricted(false, true),
        ]);
        a.required_features |= REFERENCES_G1;

        let bytes = a.encode();
        assert_eq!(type_record_flags(&bytes, I64 as usize), 0);
        assert_eq!(type_record_flags(&bytes, 19), ZERO_USE_ALLOWED);
        assert_eq!(type_record_flags(&bytes, 20), ZERO_USE_ALLOWED);
        assert_eq!(type_record_flags(&bytes, 21), ZERO_USE_ALLOWED);
        let decoded = Artifact::decode(&bytes).unwrap();
        assert!(!decoded.types[I64 as usize].claimed_duplicable());
        assert!(!decoded.types[I64 as usize].claimed_zero_use_allowed());
        assert_eq!(decoded.encode(), bytes);
    }

    #[test]
    fn bytes_to_array_primitive_roundtrips() {
        let mut types = Type::predefined();
        types.push(Type::Array { element: U8 });
        let a = Artifact {
            types,
            cleanups: vec![],
            functions: vec![Function {
                flags: 0,
                name: "convert".into(),
                params: vec![BYTES],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, BYTES, 19],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Primitive {
                    dst: 2,
                    op: Primitive::BytesToArray,
                    args: vec![1],
                },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        };
        let bytes = a.encode();
        assert_eq!(Artifact::decode(&bytes).unwrap(), canonical(a));
    }
    #[test]
    fn tuple_struct_and_enum_descriptors_preserve_names_and_layouts() {
        let mut a = artifact();
        a.types.extend([
            Type::Tuple {
                fields: vec![I64, U32],
                copy: true,
            },
            Type::Struct {
                name: "Point".into(),
                fields: vec![
                    Field {
                        name: "x".into(),
                        ty: I64,
                    },
                    Field {
                        name: "y".into(),
                        ty: I64,
                    },
                ],
                copy: true,
            },
            Type::Enum {
                name: "Choice".into(),
                variants: vec![
                    EnumVariant {
                        name: "Signed".into(),
                        fields: vec![Field {
                            name: "value".into(),
                            ty: I64,
                        }],
                    tag: None,
},
                    EnumVariant {
                        name: "Unsigned".into(),
                        fields: vec![Field {
                            name: "value".into(),
                            ty: U64,
                        }],
                    tag: None,
},
                ],
                copy: true,
            },
        ]);
        let bytes = a.encode();
        let decoded = Artifact::decode(&bytes).unwrap();
        assert_eq!(decoded, a);
        assert_eq!(decoded.encode(), bytes);
    }

    #[test]
    fn enum_switch_facts_infer_variant_specific_projection_types() {
        let mut types = Type::predefined();
        let choice = types.len() as TypeId;
        types.push(Type::Enum {
            name: "Choice".into(),
            variants: vec![
                EnumVariant {
                    name: "Empty".into(),
                    fields: vec![Field {
                        name: "value".into(),
                        ty: UNIT,
                    }],
                tag: None,
},
                EnumVariant {
                    name: "Number".into(),
                    fields: vec![Field {
                        name: "value".into(),
                        ty: I64,
                    }],
                tag: None,
},
            ],
            copy: true,
        });
        let artifact = Artifact {
            required_features: CORE_G1,
            types,
            constants: vec![Constant::U32(0), Constant::U32(1)],
            functions: vec![Function {
                flags: 0,
                name: "consume".into(),
                params: vec![choice],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, choice, U32, UNIT, I64],
                code_start: 0,
                code_len: 13,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::EnumTag { dst: 2, src: 1 },
                Instruction::Switch {
                    discr: 2,
                    cases: vec![(0, 2), (1, 7)],
                    otherwise: 12,
                },
                Instruction::Drop { register: 2 },
                Instruction::ProjectMove {
                    dst: 3,
                    src: 1,
                    field: 0,
                },
                Instruction::Deconstruct { src: 1 },
                Instruction::Drop { register: 3 },
                Instruction::Return { src: None },
                Instruction::Drop { register: 2 },
                Instruction::ProjectMove {
                    dst: 4,
                    src: 1,
                    field: 0,
                },
                Instruction::Deconstruct { src: 1 },
                Instruction::Drop { register: 4 },
                Instruction::Return { src: None },
                Instruction::Unreachable,
            ],
            ..Artifact::default()
        };

        let bytes = canonical(artifact.clone()).encode();
        assert_eq!(Artifact::decode(&bytes).unwrap(), canonical(artifact));
    }

    #[test]
    fn enum_tag_type_inference_accepts_a_reference_to_an_enum() {
        let mut types = Type::predefined();
        let choice = types.len() as TypeId;
        types.push(Type::Enum {
            name: "Choice".into(),
            variants: vec![EnumVariant {
                name: "Only".into(),
                fields: vec![],
            tag: None,
}],
            copy: false,
        });
        let borrowed_choice = types.len() as TypeId;
        types.push(Type::RefShared { referent: choice });
        let artifact = Artifact {
            required_features: CORE_G1 | REFERENCES_G1,
            types,
            functions: vec![Function {
                flags: 0,
                name: "borrowed_tag".into(),
                params: vec![borrowed_choice],
                return_type: U32,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, borrowed_choice, U32],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::EnumTag { dst: 2, src: 1 },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        };

        let expected = canonical(artifact);
        let bytes = expected.encode();
        assert_eq!(Artifact::decode(&bytes).unwrap(), expected);
    }

    #[test]
    fn array_pop_type_inference_flows_from_the_unique_array_reference() {
        let mut types = Type::predefined();
        let array = types.len() as TypeId;
        types.push(Type::Array { element: I64 });
        let array_reference = types.len() as TypeId;
        types.push(Type::RefUnique { referent: array });
        let artifact = canonical(Artifact {
            required_features: CORE_G1 | REFERENCES_G1,
            types,
            functions: vec![Function {
                flags: 0,
                name: "pop".into(),
                params: vec![array_reference],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, array_reference, I64],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Primitive {
                    dst: 2,
                    op: Primitive::ArrayPopMove,
                    args: vec![1],
                },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        });

        let bytes = artifact.encode();
        assert_eq!(Artifact::decode(&bytes).unwrap(), artifact);
    }

    fn type_record_flags(bytes: &[u8], type_id: usize) -> u8 {
        let directory = HEADER_LEN + DIRECTORY_ENTRY_LEN;
        let section =
            u64::from_le_bytes(bytes[directory + 8..directory + 16].try_into().unwrap()) as usize;
        let count = u32::from_le_bytes(bytes[section..section + 4].try_into().unwrap()) as usize;
        assert!(type_id < count);
        let offsets = section + 4;
        let records = offsets + (count + 1) * 4;
        let relative = u32::from_le_bytes(
            bytes[offsets + type_id * 4..offsets + type_id * 4 + 4]
                .try_into()
                .unwrap(),
        ) as usize;
        bytes[records + relative + 1]
    }

    fn type_record_flags_mut(bytes: &mut [u8], type_id: usize) -> &mut u8 {
        let directory = HEADER_LEN + DIRECTORY_ENTRY_LEN;
        let section =
            u64::from_le_bytes(bytes[directory + 8..directory + 16].try_into().unwrap()) as usize;
        let count = u32::from_le_bytes(bytes[section..section + 4].try_into().unwrap()) as usize;
        assert!(type_id < count);
        let offsets = section + 4;
        let records = offsets + (count + 1) * 4;
        let relative = u32::from_le_bytes(
            bytes[offsets + type_id * 4..offsets + type_id * 4 + 4]
                .try_into()
                .unwrap(),
        ) as usize;
        &mut bytes[records + relative + 1]
    }

    #[test]
    fn derives_exact_zero_sized_flags_for_owned_layouts() {
        let mut a = artifact();
        a.types.extend([
            Type::Tuple {
                fields: vec![],
                copy: true,
            },
            Type::Struct {
                name: "Empty".into(),
                fields: vec![],
                copy: false,
            },
            Type::Enum {
                name: "Void".into(),
                variants: vec![],
                copy: false,
            },
            Type::Enum {
                name: "Only".into(),
                variants: vec![EnumVariant {
                    name: "Only".into(),
                    fields: vec![],
                tag: None,
}],
                copy: false,
            },
            Type::Enum {
                name: "BoolLike".into(),
                variants: vec![
                    EnumVariant {
                        name: "No".into(),
                        fields: vec![],
                    tag: None,
},
                    EnumVariant {
                        name: "Yes".into(),
                        fields: vec![],
                    tag: None,
},
                ],
                copy: false,
            },
            Type::BindingPack {
                payload_type: 19,
                identity_name: "EmptyBindings".into(),
                copy: true,
            },
        ]);

        let bytes = a.encode();
        assert_eq!(type_record_flags(&bytes, 19), DUPLICABLE | ZERO_SIZED);
        assert_eq!(type_record_flags(&bytes, 20), ZERO_SIZED);
        assert_eq!(type_record_flags(&bytes, 21), ZERO_SIZED);
        assert_eq!(type_record_flags(&bytes, 22), ZERO_SIZED);
        assert_eq!(type_record_flags(&bytes, 23), 0);
        assert_eq!(
            type_record_flags(&bytes, 24),
            DUPLICABLE | ZERO_SIZED | OPAQUE
        );
        let decoded = Artifact::decode(&bytes).unwrap();
        assert_eq!(decoded, a);
        assert_eq!(decoded.encode(), bytes);
    }

    #[test]
    fn rejects_hostile_zero_sized_opaque_and_reserved_flag_mismatches() {
        let mut a = artifact();
        a.types.extend([
            Type::Tuple {
                fields: vec![],
                copy: false,
            },
            Type::Tuple {
                fields: vec![U32],
                copy: false,
            },
            Type::Available {
                identity_name: "proof".into(),
            },
        ]);
        let bytes = a.encode();

        let mut missing = bytes.clone();
        *type_record_flags_mut(&mut missing, 19) &= !ZERO_SIZED;
        assert_eq!(
            Artifact::decode(&missing),
            Err(DecodeError::InvalidTable("ZERO_SIZED flag"))
        );

        let mut forged = bytes.clone();
        *type_record_flags_mut(&mut forged, 20) |= ZERO_SIZED;
        assert_eq!(
            Artifact::decode(&forged),
            Err(DecodeError::InvalidTable("ZERO_SIZED flag"))
        );

        let mut transparent_available = bytes.clone();
        *type_record_flags_mut(&mut transparent_available, 21) &= !OPAQUE;
        assert_eq!(
            Artifact::decode(&transparent_available),
            Err(DecodeError::InvalidTable("available type"))
        );

        let mut reserved = bytes;
        *type_record_flags_mut(&mut reserved, 20) |= 0x20;
        assert_eq!(
            Artifact::decode(&reserved),
            Err(DecodeError::InvalidTable("type flags"))
        );
    }

    #[test]
    fn generation_one_golden_bytes() {
        let b = artifact().encode();
        let hash = b.iter().fold(0xcbf29ce484222325u64, |h, x| {
            (h ^ u64::from(*x)).wrapping_mul(0x100000001b3)
        });
        assert_eq!((b.len(), hash), (1008, 8_653_562_428_044_392_972));
    }
    #[test]
    fn rejects_new_required_feature() {
        let mut b = artifact().encode();
        b[33] |= 0x02;
        assert!(matches!(
            Artifact::decode(&b),
            Err(DecodeError::UnsupportedFeatures { .. })
        ))
    }

    #[test]
    fn imports_and_exports_roundtrip_with_exact_host_feature() {
        let mut artifact = artifact();
        let signature = Signature {
            params: vec![I64],
            result: I64,
            outward_protocols: vec![],
        };
        artifact.required_features = CORE_G1 | HOST_ABI_G1;
        artifact.imports = vec![Import {
            capability: "clock".into(),
            symbol: "monotonic".into(),
            signature,
            may_trap: true,
        }];
        artifact.exports = vec![Export {
            name: "answer".into(),
            function: 0,
            signature: function_signature(&artifact.functions[0]),
        }];
        artifact.functions[0].flags |= EXPORTED;

        let bytes = artifact.encode();
        let decoded = Artifact::decode(&bytes).unwrap();
        assert_eq!(decoded, canonical(artifact));
        assert_eq!(decoded.encode(), bytes);
    }

    #[test]
    fn function_flags_and_drop_glue_roundtrip_with_has_drop() {
        let mut artifact = Artifact::default();
        artifact.required_features |= REFERENCES_G1;
        artifact.types.push(Type::Struct {
            name: "Resource".into(),
            fields: vec![],
            copy: false,
        });
        artifact.types.push(Type::RefUnique { referent: 19 });
        artifact.constants.push(Constant::Unit);
        artifact.functions.push(Function {
            flags: DROP_HOOK,
            name: "drop_resource".into(),
            params: vec![20],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 20, UNIT],
            code_start: 0,
            code_len: 3,
            label_slot_count: 0,
        });
        artifact.code = vec![
            Instruction::Drop { register: 1 },
            Instruction::Const {
                dst: 2,
                constant: 0,
            },
            Instruction::Return { src: Some(2) },
        ];
        artifact.drop_glue.push(DropGlue {
            ty: 19,
            function: 0,
        });

        let bytes = artifact.encode();
        assert_eq!(type_record_flags(&bytes, 19), ZERO_SIZED | HAS_DROP);
        let decoded = Artifact::decode(&bytes).unwrap();
        assert_eq!(decoded.types, artifact.types);
        assert_eq!(decoded.drop_glue, artifact.drop_glue);
        assert_eq!(decoded.encode(), bytes);

        artifact.drop_glue[0].ty = U32;
        assert_eq!(
            artifact.encode_impl(),
            Err(DecodeError::InvalidTable("predefined type flags"))
        );
    }

    #[test]
    fn rejects_unsorted_or_mismatched_function_metadata() {
        let mut artifact = artifact();
        artifact.functions[0].flags = EXPORTED;
        assert_eq!(
            artifact.encode_impl(),
            Err(DecodeError::InvalidTable("EXPORTED flag"))
        );

        artifact.functions[0].flags = DROP_HOOK;
        artifact.drop_glue = vec![
            DropGlue {
                ty: U64,
                function: 0,
            },
            DropGlue {
                ty: U32,
                function: 0,
            },
        ];
        assert!(matches!(
            artifact.encode_impl(),
            Err(DecodeError::NonCanonical(message)) if message.contains("drop glue")
        ));
    }

    #[test]
    fn host_call_roundtrips_at_assigned_opcode() {
        let mut artifact = Artifact {
            required_features: CORE_G1 | HOST_ABI_G1,
            ..Artifact::default()
        };
        artifact.types.push(Type::Array { element: TEXT });
        artifact.imports.push(Import {
            capability: "process.args".into(),
            symbol: "get".into(),
            signature: Signature {
                params: vec![],
                result: 19,
                outward_protocols: vec![],
            },
            may_trap: false,
        });
        artifact.functions.push(Function {
            flags: 0,
            name: "host_args".into(),
            params: vec![],
            return_type: 19,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 19],
            code_start: 0,
            code_len: 2,
            label_slot_count: 0,
        });
        artifact.code = vec![
            Instruction::HostCall {
                dst: Some(1),
                import: 0,
                args: vec![],
            },
            Instruction::Return { src: Some(1) },
        ];

        let bytes = artifact.encode();
        let decoded = Artifact::decode(&bytes).unwrap();
        assert_eq!(decoded, canonical(artifact));
        assert_eq!(decoded.encode(), bytes);
    }

    #[test]
    fn rejects_unsorted_imports_and_exports() {
        let signature = Signature {
            params: vec![],
            result: UNIT,
            outward_protocols: vec![],
        };
        let imports = Artifact {
            required_features: CORE_G1 | HOST_ABI_G1,
            imports: vec![
                Import {
                    capability: "z".into(),
                    symbol: "call".into(),
                    signature: signature.clone(),
                    may_trap: false,
                },
                Import {
                    capability: "a".into(),
                    symbol: "call".into(),
                    signature,
                    may_trap: false,
                },
            ],
            ..Artifact::default()
        };
        assert!(matches!(
            imports.encode_impl(),
            Err(DecodeError::NonCanonical(message)) if message.contains("imports")
        ));

        let mut exports = artifact();
        let signature = function_signature(&exports.functions[0]);
        exports.exports = vec![
            Export {
                name: "z".into(),
                function: 0,
                signature: signature.clone(),
            },
            Export {
                name: "a".into(),
                function: 0,
                signature,
            },
        ];
        exports.functions[0].flags |= EXPORTED;
        assert!(matches!(
            exports.encode_impl(),
            Err(DecodeError::NonCanonical(message)) if message.contains("exports")
        ));
    }

    #[test]
    fn rejects_export_signature_mismatch_and_nonzero_wire_flags() {
        let mut artifact = artifact();
        artifact.exports = vec![Export {
            name: "answer".into(),
            function: 0,
            signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
        }];
        artifact.functions[0].flags |= EXPORTED;
        assert_eq!(
            artifact.encode_impl(),
            Err(DecodeError::InvalidTable("export signature"))
        );

        artifact.exports[0].signature = function_signature(&artifact.functions[0]);
        let mut bytes = artifact.encode();
        let directory = 64 + (12 - 1) * 32;
        let export_offset =
            u64::from_le_bytes(bytes[directory + 8..directory + 16].try_into().unwrap()) as usize;
        bytes[export_offset + 12..export_offset + 16].copy_from_slice(&1u32.to_le_bytes());
        assert_eq!(
            Artifact::decode(&bytes),
            Err(DecodeError::InvalidTable("export signature or flags"))
        );
    }

    #[test]
    fn multishot_feature_bit_and_quantity_roundtrip_exactly() {
        let mut artifact = Artifact::default();
        artifact.types.push(Type::Resumption {
            input_type: I64,
            output_type: UNIT,
            effect_signature: Signature {
                params: vec![I64],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: 2,
            upper_uses: Some(3),
            identity_name: "multi".into(),
            copy: true,
        });
        artifact.required_features = CORE_G1 | MULTISHOT_G1;
        let bytes = artifact.encode();
        assert_eq!(
            u64::from_le_bytes(bytes[32..40].try_into().unwrap()),
            CORE_G1 | MULTISHOT_G1
        );
        assert_eq!(Artifact::decode(&bytes).unwrap(), artifact);
    }

    #[test]
    fn enum_variant_discriminant_respects_explicit_tags() {
        let implicit = EnumVariant {
            name: "A".into(),
            fields: vec![],
            tag: None,
        };
        let explicit = EnumVariant {
            name: "B".into(),
            fields: vec![],
            tag: Some(5),
        };
        assert_eq!(implicit.discriminant(0), 0);
        assert_eq!(implicit.discriminant(2), 2);
        assert_eq!(explicit.discriminant(1), 5);
        assert_eq!(explicit.discriminant(7), 5);
    }

    #[test]
    fn enum_explicit_tags_survive_encode_decode_roundtrip() {
        let enum_ty = Type::predefined().len() as TypeId;
        let artifact = Artifact {
            functions: vec![Function {
                flags: 0,
                name: "tagged_enum".into(),
                params: vec![],
                return_type: enum_ty,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, enum_ty],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Construct {
                    dst: 1,
                    ty: enum_ty,
                    variant: Some(0),
                    fields: vec![],
                },
                Instruction::Return { src: Some(1) },
            ],
            ..Artifact::default()
        };
        let artifact = Artifact {
            types: {
                let mut types = Type::predefined();
                types.push(
                    Type::Enum {
                        name: "E".into(),
                        variants: vec![
                            EnumVariant {
                                name: "A".into(),
                                fields: vec![],
                                tag: Some(1),
                            },
                            EnumVariant {
                                name: "B".into(),
                                fields: vec![],
                                tag: Some(5),
                            },
                            EnumVariant {
                                name: "C".into(),
                                fields: vec![],
                                tag: None,
                            },
                        ],
                        copy: true,
                    }
                    .restricted(true, true),
                );
                types
            },
            ..artifact
        };
        let artifact = canonical(artifact);
        let bytes = artifact.encode();
        let decoded = Artifact::decode(&bytes).unwrap();
        let Type::Enum { variants, .. } = decoded.types[enum_ty as usize].representation() else {
            panic!("expected an enum type");
        };
        assert_eq!(
            variants
                .iter()
                .map(|variant| variant.tag)
                .collect::<Vec<_>>(),
            vec![Some(1), Some(5), None]
        );
        assert_eq!(decoded, artifact);
    }
}
