//! Finite machine-primitive authority bound to a trusted library identity.
//!
//! Source names are never authority.  A request host supplies selectors for a
//! distinguished standard-library package; binding resolves them to exact
//! public declaration identities and freezes a digestible table.

use std::collections::BTreeMap;

use crate::{
    ElaboratedHeader, ElaboratedInterface, PackageInterface, PackageKey, Quantity, ScalarType,
    Type,
    identity::{DefKey, Digest},
    types::EffectRow,
};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PrimitiveRole {
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
    /// Exact generic declaration `__g1_int_wrapping_sub<T>` in distributed
    /// std. Its i64 specialization has wrapping, not checked, overflow.
    IntWrappingSub,
    /// Exact generic declaration `__g1_int_wrapping_mul<T>` in distributed
    /// std. Its i64 specialization has wrapping, not checked, overflow.
    IntWrappingMul,
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
}

impl PrimitiveRole {
    pub const fn selector_name(self) -> &'static str {
        match self {
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
            Self::IntWrappingAdd => "int-wrapping-add",
            Self::IntConvertCheckedToI64 => "int-convert-checked-to-i64",
            Self::IntConvertWrappingToI64 => "int-convert-wrapping-to-i64",
            Self::IntConvertWrappingToU32 => "int-convert-wrapping-to-u32",
            Self::IntConvertWrappingToUsize => "int-convert-wrapping-to-usize",
            Self::IntConvertWrappingToU8 => "int-convert-wrapping-to-u8",
            Self::IntWrappingSub => "int-wrapping-sub",
            Self::IntWrappingMul => "int-wrapping-mul",
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
        }
    }

    pub fn parse_selector_name(value: &str) -> Option<Self> {
        Some(match value {
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
            "int-wrapping-add" => Self::IntWrappingAdd,
            "int-convert-checked-to-i64" => Self::IntConvertCheckedToI64,
            "int-convert-wrapping-to-i64" => Self::IntConvertWrappingToI64,
            "int-convert-wrapping-to-u32" => Self::IntConvertWrappingToU32,
            "int-convert-wrapping-to-usize" => Self::IntConvertWrappingToUsize,
            "int-convert-wrapping-to-u8" => Self::IntConvertWrappingToU8,
            "int-wrapping-sub" => Self::IntWrappingSub,
            "int-wrapping-mul" => Self::IntWrappingMul,
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
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeManifestInput {
    pub standard_library: PackageKey,
    pub selectors: Vec<PrimitiveSelector>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrustedRuntimeManifest {
    pub standard_library: PackageKey,
    pub primitives: BTreeMap<PrimitiveRole, DefKey>,
    pub digest: Digest,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ManifestError {
    DuplicateRole(PrimitiveRole),
    MissingDeclaration {
        module_path: String,
        name: String,
    },
    AmbiguousDeclaration {
        module_path: String,
        name: String,
    },
    IncompatibleSignature {
        role: PrimitiveRole,
        definition: DefKey,
    },
}

impl RuntimeManifestInput {
    pub fn canonicalize(&mut self) -> Result<(), ManifestError> {
        self.selectors.sort();
        for pair in self.selectors.windows(2) {
            if pair[0].role == pair[1].role {
                return Err(ManifestError::DuplicateRole(pair[0].role));
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
            if selectors.insert(selector.role, selector).is_some() {
                return Err(ManifestError::DuplicateRole(selector.role));
            }
        }
        let mut primitives = BTreeMap::new();
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
        Ok(TrustedRuntimeManifest {
            standard_library: self.standard_library.clone(),
            digest: manifest_digest(&self.standard_library, &primitives),
            primitives,
        })
    }
}
fn expected_signature(role: PrimitiveRole) -> crate::CallableSignature {
    match role {
        PrimitiveRole::BranchBool => {
            let result = Type::Generic(0);
            let thunk = Type::Callable {
                lifetime_binders: 0,
                parameters: vec![],
                result: Box::new(result.clone()),
                effects: EffectRow::empty(),
                invocation: Quantity::ONCE,
            };
            crate::CallableSignature {
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
        PrimitiveRole::BytesConcat => crate::CallableSignature {
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
        | PrimitiveRole::IntWrappingAdd
        | PrimitiveRole::IntWrappingSub
        | PrimitiveRole::IntWrappingMul
        | PrimitiveRole::IntBitAnd
        | PrimitiveRole::IntBitOr
        | PrimitiveRole::IntBitXor => crate::CallableSignature {
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
        PrimitiveRole::IntConvertCheckedToI64 => crate::CallableSignature {
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
        PrimitiveRole::IntConvertWrappingToUsize => crate::CallableSignature {
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
        PrimitiveRole::IntBitNot => crate::CallableSignature {
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
    }
}
fn manifest_digest(
    standard_library: &PackageKey,
    primitives: &BTreeMap<PrimitiveRole, DefKey>,
) -> Digest {
    let mut bytes = b"grandiose-stage0-runtime-manifest-v1".to_vec();
    bytes.extend_from_slice(&(standard_library.0.len() as u64).to_le_bytes());
    bytes.extend_from_slice(standard_library.0.as_bytes());
    for (role, definition) in primitives {
        bytes.push(match role {
            PrimitiveRole::BranchBool => 0,
            PrimitiveRole::TextByteLen => 1,
            PrimitiveRole::TextConcat => 2,
            PrimitiveRole::TextEq => 3,
            PrimitiveRole::TextFromUtf8Checked => 4,
            PrimitiveRole::TextAsBytes => 5,
            PrimitiveRole::CharFromU32Checked => 6,
            PrimitiveRole::CharToU32 => 7,
            PrimitiveRole::BytesLen => 8,
            PrimitiveRole::BytesConcat => 9,
            PrimitiveRole::BytesGet => 10,
            PrimitiveRole::BytesSlice => 11,
            PrimitiveRole::BytesFromArrayMove => 12,
            PrimitiveRole::BytesToArray => 13,
            PrimitiveRole::BytesUtf8ValidUpTo => 14,
            PrimitiveRole::U32CheckedAdd => 15,
            PrimitiveRole::U32CheckedSub => 16,
            PrimitiveRole::U32CheckedMul => 17,
            PrimitiveRole::U32CheckedDiv => 18,
            PrimitiveRole::U32CheckedRem => 19,
            PrimitiveRole::U32WrappingAdd => 20,
            PrimitiveRole::U32WrappingSub => 21,
            PrimitiveRole::U32WrappingMul => 22,
            PrimitiveRole::U32WrappingShl => 23,
            PrimitiveRole::U32WrappingShr => 24,
            PrimitiveRole::U32CheckedShl => 25,
            PrimitiveRole::U32CheckedShr => 26,
            PrimitiveRole::U32Eq => 27,
            PrimitiveRole::U32Lt => 28,
            PrimitiveRole::U32Le => 29,
            PrimitiveRole::U32ToUsize => 30,
            PrimitiveRole::UsizeToU32Checked => 31,
            PrimitiveRole::IntCheckedAdd => 32,
            PrimitiveRole::IntWrappingAdd => 33,
            PrimitiveRole::IntConvertCheckedToI64 => 45,
            PrimitiveRole::IntConvertWrappingToI64 => 46,
            PrimitiveRole::IntConvertWrappingToU32 => 48,
            PrimitiveRole::IntConvertWrappingToUsize => 50,
            PrimitiveRole::IntConvertWrappingToU8 => 52,
            PrimitiveRole::IntWrappingSub => 35,
            PrimitiveRole::IntWrappingMul => 36,
            PrimitiveRole::IntEqual => 34,
            PrimitiveRole::IntLess => 38,
            PrimitiveRole::IntGreater => 39,
            PrimitiveRole::IntBitAnd => 37,
            PrimitiveRole::IntBitOr => 40,
            PrimitiveRole::IntBitXor => 41,
            PrimitiveRole::IntBitNot => 42,
            PrimitiveRole::IntShr => 44,
            PrimitiveRole::IntShl => 43,
            PrimitiveRole::IntConvertCheckedToU32 => 47,
            PrimitiveRole::IntConvertCheckedToUsize => 49,
            PrimitiveRole::IntConvertCheckedToU8 => 51,
        });
        bytes.extend_from_slice(&definition.0.as_bytes());
    }
    Digest::of_bytes(&bytes)
}
