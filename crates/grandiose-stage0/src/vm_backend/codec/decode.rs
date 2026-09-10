//! Bounded parsing of untrusted Stage 0 artifact payloads.

#[cfg(test)]
mod const_kind_tests {
    use super::*;
    use crate::ConstKind;

    #[test]
    fn closed_integer_values_round_trip_all_kinds_and_boundaries() {
        use crate::types::integer_const::IntegerConst;
        for kind in (0..=12).filter_map(ConstKind::from_tag) {
            let Some(scalar) = kind.integer_scalar() else { continue };
            for (negative, magnitude) in [(false, 0), (false, 42), (false, u128::MAX), (true, 1u128 << 127)] {
                let Ok(value) = IntegerConst::new(scalar, negative, magnitude, 64) else { continue };
                let argument = VmGenericArgument::ConstInteger(value);
                let mut bytes = vec![];
                super::super::encode_vm_generic_argument(&argument, &mut bytes);
                assert_eq!(Decoder::new(&bytes).vm_generic_argument_at_depth(0).unwrap(), argument);
                for length in 0..bytes.len() {
                    assert!(Decoder::new(&bytes[..length]).vm_generic_argument_at_depth(0).is_err());
                }
                let ty = VmType::ConstInteger(value);
                bytes.clear();
                super::super::encode_type(&ty, &mut bytes);
                assert_eq!(Decoder::new(&bytes).vm_type().unwrap(), ty);
            }
        }
    }

    #[test]
    fn untrusted_integer_values_reject_invalid_kinds_signs_and_ranges() {
        use crate::types::integer_const::IntegerConst;
        use crate::ScalarType;
        let value = IntegerConst::new(ScalarType::U8, false, 0, 64).unwrap();
        let valid = value.canonical_bytes();
        for tag in 0..=u8::MAX {
            if ConstKind::from_tag(tag).and_then(ConstKind::integer_scalar).is_some() { continue }
            let mut bytes = valid;
            bytes[0] = tag;
            assert!(Decoder::new(&bytes).integer_const().is_err());
        }
        for sign in 1..=u8::MAX {
            let mut bytes = valid;
            bytes[1] = sign;
            assert!(Decoder::new(&bytes).integer_const().is_err());
        }
        let mut bytes = valid;
        bytes[3] = 1; // u8 cannot represent 256.
        assert!(Decoder::new(&bytes).integer_const().is_err());
    }

    #[test]
    fn symbolic_integer_codec_requires_canonical_kinded_expressions() {
        use crate::types::integer_const::{IntegerConst, IntegerConstOp as Op};
        for kind in (0..=12).filter_map(ConstKind::from_tag) {
            let Some(scalar) = kind.integer_scalar() else { continue };
            let parameter = IntegerConstExpr::Param { index: 3, scalar };
            let literal = IntegerConstExpr::Literal(IntegerConst::new(scalar, false, 1, 64).unwrap());
            let expression = IntegerConstExpr::binary(Op::Add, Box::new(parameter.clone()), Box::new(literal.clone())).normalized().unwrap();
            let argument = VmGenericArgument::ConstIntegerExpr(expression);
            let mut bytes = vec![];
            super::super::encode_vm_generic_argument(&argument, &mut bytes);
            assert_eq!(Decoder::new(&bytes).vm_generic_argument_at_depth(0).unwrap(), argument);
            for length in 0..bytes.len() {
                assert!(Decoder::new(&bytes[..length]).vm_generic_argument_at_depth(0).is_err());
            }
            for expression in [parameter, literal] {
                bytes.clear();
                super::super::encode_vm_generic_argument(&VmGenericArgument::ConstIntegerExpr(expression), &mut bytes);
                assert!(Decoder::new(&bytes).vm_generic_argument_at_depth(0).is_err());
            }
        }
        assert!(Decoder::new(&[255]).canonical_integer_expr(0).is_err());
        use crate::ScalarType;
        let parameter = IntegerConstExpr::Param { index: 0, scalar: ScalarType::U8 };
        let literal = |scalar, magnitude| IntegerConstExpr::Literal(IntegerConst::new(scalar, false, magnitude, 64).unwrap());
        let sum = IntegerConstExpr::binary(Op::Add, Box::new(parameter.clone()), Box::new(literal(ScalarType::U8, 1))).normalized().unwrap();
        let IntegerConstExpr::Binary { op, left, right } = sum else { panic!("symbolic sum") };
        for malformed in [
            IntegerConstExpr::Binary { op, left: right, right: left },
            IntegerConstExpr::binary(Op::Add, Box::new(parameter.clone()), Box::new(literal(ScalarType::U16, 1))),
            IntegerConstExpr::binary(Op::Div, Box::new(parameter), Box::new(literal(ScalarType::U8, 0))),
            IntegerConstExpr::binary(Op::Add, Box::new(literal(ScalarType::U8, 255)), Box::new(literal(ScalarType::U8, 1))),
        ] {
            let mut bytes = vec![];
            super::super::encode_vm_generic_argument(&VmGenericArgument::ConstIntegerExpr(malformed), &mut bytes);
            assert!(Decoder::new(&bytes).vm_generic_argument_at_depth(0).is_err());
        }
        let mut deep = vec![7; 100];
        deep.push(255);
        assert!(matches!(Decoder::new(&deep).canonical_integer_expr(0), Err(VmArtifactError::DecodeLimit { .. })));
    }

    #[test]
    fn const_kind_metadata_round_trips_without_erasing_width_or_signedness() {
        for kind in (0..=12).filter_map(ConstKind::from_tag) {
            let argument = VmGenericArgument::ConstGeneric { index: 7, kind };
            let mut bytes = vec![];
            super::super::encode_vm_generic_argument(&argument, &mut bytes);
            let mut decoder = Decoder::new(&bytes);
            assert_eq!(decoder.vm_generic_argument_at_depth(0).unwrap(), argument);
            assert_eq!(decoder.remaining(), 0);

            let value = VmType::ConstGeneric { index: 7, kind };
            let mut bytes = vec![];
            super::super::encode_type(&value, &mut bytes);
            let mut decoder = Decoder::new(&bytes);
            assert_eq!(decoder.vm_type().unwrap(), value);
            assert_eq!(decoder.remaining(), 0);
        }
    }

    #[test]
    fn untrusted_const_kind_metadata_rejects_unknown_tags_and_truncation() {
        let argument = VmGenericArgument::ConstGeneric { index: 0, kind: ConstKind::Usize };
        let mut bytes = vec![];
        super::super::encode_vm_generic_argument(&argument, &mut bytes);
        for length in 0..bytes.len() {
            assert!(Decoder::new(&bytes[..length]).vm_generic_argument_at_depth(0).is_err());
        }
        for tag in 13..=u8::MAX {
            *bytes.last_mut().unwrap() = tag;
            assert!(Decoder::new(&bytes).vm_generic_argument_at_depth(0).is_err());
        }
    }
}

#[cfg(test)]
mod body_region_tests {
    use super::*;

    #[test]
    fn body_regions_are_erased_at_emission_and_rejected_on_the_wire() {
        let definition = crate::DefKey(crate::Digest::of_bytes(b"body-region-wire"));
        let lifetime = Lifetime::Inferred(crate::types::BodyRegion { owner: definition, index: 0 });
        let source = crate::GenericArgument::Lifetime(lifetime);
        let expected = VmGenericArgument::Lifetime(Lifetime::Elided);
        assert_eq!(crate::vm_backend::vm_effect_generic_argument(&source).unwrap(), expected);
        assert_eq!(crate::vm_backend::vm_effect_argument(definition, &source).unwrap(), expected);
        for value in [VmGenericArgument::Lifetime(lifetime), expected.clone()] {
            let valid = value == expected;
            assert_eq!(crate::vm_backend::validate_vm_generic_arguments(std::slice::from_ref(&value)).is_ok(), valid);
            let mut bytes = vec![];
            super::super::encode_vm_generic_argument(&value, &mut bytes);
            let decoded = Decoder::new(&bytes).vm_generic_argument_at_depth(0);
            assert_eq!(decoded.is_ok(), valid);
            if valid { assert_eq!(decoded.unwrap(), expected); }
            else {
                for end in 0..bytes.len() {
                    assert!(Decoder::new(&bytes[..end]).vm_generic_argument_at_depth(0).is_err());
                }
            }
        }
    }
}

use super::super::{
    VmArtifactError, VmCapture, VmCaptureEnvironment, VmCaptureMode, VmCleanupLoan, VmCleanupPlace,
    VmCleanupProof, VmCompare, VmContinuationPolicy, VmEffectInstance, VmEffectRow,
    VmEffectRowProjection, VmFrameDrop, VmFunction, VmGenericArgument, VmInstruction,
    VmNativeResident, VmNominalCopyDescriptor, VmPattern, VmPatternField, VmStorageErasureAction,
    VmStorageErasureStorage, VmStorageErasureWitness, VmType,
};
use super::{
    MAX_DECODE_INSTRUCTIONS, MAX_DECODE_REGISTERS, MAX_DECODE_TEXT_BYTES, MAX_DECODE_TYPE_DEPTH,
    decode_const_kind, decode_integer_scalar, vm_effect_instance_key, vm_effect_row_projection_key,
};
use crate::{
    MemoryPrimitive,
    identity::{DefKey, Digest},
    mir::{is_canonical_f32_bits, is_canonical_f64_bits},
    runtime_manifest::PrimitiveRole,
    types::{EffectTail, Lifetime, PointerMutability, Safety, IntegerConstExpr},
};

pub(super) struct Decoder<'a> {
    input: &'a [u8],
    index: usize,
}
impl<'a> Decoder<'a> {
    pub(super) fn new(input: &'a [u8]) -> Self {
        Self { input, index: 0 }
    }
    pub(super) fn remaining(&self) -> usize {
        self.input.len().saturating_sub(self.index)
    }
    pub(super) fn bytes(&mut self, length: usize) -> Result<&'a [u8], VmArtifactError> {
        let end = self
            .index
            .checked_add(length)
            .filter(|end| *end <= self.input.len())
            .ok_or(VmArtifactError::MalformedEncoding {
                message: "truncated artifact",
            })?;
        let value = &self.input[self.index..end];
        self.index = end;
        Ok(value)
    }
    pub(super) fn array(&mut self) -> Result<[u8; 32], VmArtifactError> {
        self.bytes(32)?
            .try_into()
            .map_err(|_| VmArtifactError::MalformedEncoding {
                message: "truncated digest",
            })
    }
    pub(super) fn optional_digest(&mut self) -> Result<Option<Digest>, VmArtifactError> {
        match self.byte()? {
            0 => Ok(None),
            1 => Ok(Some(Digest::from_bytes(self.array()?))),
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "invalid optional manifest digest tag",
            }),
        }
    }
    fn byte(&mut self) -> Result<u8, VmArtifactError> {
        Ok(self.bytes(1)?[0])
    }
    fn boolean(&mut self) -> Result<bool, VmArtifactError> {
        match self.byte()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "invalid boolean tag",
            }),
        }
    }
    pub(super) fn u32(&mut self) -> Result<u32, VmArtifactError> {
        Ok(u32::from_le_bytes(self.bytes(4)?.try_into().unwrap()))
    }
    fn u16(&mut self) -> Result<u16, VmArtifactError> {
        Ok(u16::from_le_bytes(self.bytes(2)?.try_into().unwrap()))
    }
    pub(super) fn u64(&mut self) -> Result<u64, VmArtifactError> {
        Ok(u64::from_le_bytes(self.bytes(8)?.try_into().unwrap()))
    }
    fn u128(&mut self) -> Result<u128, VmArtifactError> {
        Ok(u128::from_le_bytes(self.bytes(16)?.try_into().unwrap()))
    }
    fn integer_const(&mut self) -> Result<crate::types::integer_const::IntegerConst, VmArtifactError> {
        let kind = decode_const_kind(self.byte()?)?;
        let scalar = kind.integer_scalar().ok_or(VmArtifactError::MalformedEncoding {
            message: "non-integer const value kind",
        })?;
        let negative = self.boolean()?;
        let magnitude = self.u128()?;
        if negative && magnitude == 0 {
            return Err(VmArtifactError::MalformedEncoding { message: "noncanonical negative zero const value" });
        }
        // The Stage 0 VM ABI has 64-bit indexing; this is not host usize.
        crate::types::integer_const::IntegerConst::new(scalar, negative, magnitude, 64)
            .map_err(|_| VmArtifactError::MalformedEncoding { message: "integer const value is out of range" })
    }
    fn i8(&mut self) -> Result<i8, VmArtifactError> {
        Ok(i8::from_le_bytes(self.bytes(1)?.try_into().unwrap()))
    }
    fn i16(&mut self) -> Result<i16, VmArtifactError> {
        Ok(i16::from_le_bytes(self.bytes(2)?.try_into().unwrap()))
    }
    fn i32(&mut self) -> Result<i32, VmArtifactError> {
        Ok(i32::from_le_bytes(self.bytes(4)?.try_into().unwrap()))
    }
    fn i64(&mut self) -> Result<i64, VmArtifactError> {
        Ok(i64::from_le_bytes(self.bytes(8)?.try_into().unwrap()))
    }
    fn i128(&mut self) -> Result<i128, VmArtifactError> {
        Ok(i128::from_le_bytes(self.bytes(16)?.try_into().unwrap()))
    }
    pub(super) fn count(
        &mut self,
        kind: &'static str,
        limit: u64,
    ) -> Result<usize, VmArtifactError> {
        let count = self.u64()?;
        if count > limit || count > usize::MAX as u64 {
            return Err(VmArtifactError::DecodeLimit { kind, limit });
        }
        Ok(count as usize)
    }
    fn vm_type(&mut self) -> Result<VmType, VmArtifactError> {
        self.vm_type_at_depth(0)
    }
    pub(super) fn capture_environment(
        &mut self,
    ) -> Result<Option<VmCaptureEnvironment>, VmArtifactError> {
        match self.byte()? {
            0 => Ok(None),
            1 => {
                let owner = self.def_key()?;
                let callable = self.u32()?;
                let instance = self.optional_digest()?;
                let destructor = self.optional_digest()?.map(DefKey);
                let count = self.count("callable environment captures", MAX_DECODE_REGISTERS)?;
                let mut captures = Vec::with_capacity(count);
                for _ in 0..count {
                    let mode = match self.byte()? {
                        0 => VmCaptureMode::SharedBorrow,
                        1 => VmCaptureMode::UniqueBorrow,
                        2 => VmCaptureMode::Copy,
                        3 => VmCaptureMode::Move,
                        _ => {
                            return Err(VmArtifactError::MalformedEncoding {
                                message: "invalid callable capture mode",
                            });
                        }
                    };
                    captures.push(VmCapture {
                        mode,
                        ty: self.vm_type()?,
                    });
                }
                Ok(Some(VmCaptureEnvironment {
                    owner,
                    callable,
                    instance,
                    captures,
                    destructor,
                }))
            }
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "invalid optional callable environment tag",
            }),
        }
    }
    fn vm_type_at_depth(&mut self, depth: u64) -> Result<VmType, VmArtifactError> {
        if depth > MAX_DECODE_TYPE_DEPTH {
            return Err(VmArtifactError::DecodeLimit {
                kind: "callable type nesting",
                limit: MAX_DECODE_TYPE_DEPTH,
            });
        }
        match self.byte()? {
            0 => Ok(VmType::Unit),
            1 => Ok(VmType::I64),
            16 => Ok(VmType::Usize),
            17 => Ok(VmType::U32),
            19 => Ok(VmType::U8),
            20 => Ok(VmType::U16),
            21 => Ok(VmType::I16),
            22 => Ok(VmType::I32),
            23 => Ok(VmType::I8),
            24 => Ok(VmType::U64),
            25 => Ok(VmType::Isize),
            26 => Ok(VmType::U128),
            27 => Ok(VmType::I128),
            28 => Ok(VmType::F32),
            2 => Ok(VmType::F64),
            3 => Ok(VmType::Bool),
            4 => Ok(VmType::Char),
            5 => Ok(VmType::Text),
            18 => Ok(VmType::Bytes),
            29 => Ok(VmType::StaticData {
                element: Box::new(self.vm_type_at_depth(depth + 1)?),
                tag: self.u128()?,
                alignment: self.u32()?,
            }),
            tag @ (6 | 30) => {
                let shared_receiver = self.boolean()?;
                let unique_receiver = self.boolean()?;
                let count = self.count("callable parameters", MAX_DECODE_REGISTERS)?;
                let mut parameters = Vec::with_capacity(count);
                for _ in 0..count {
                    parameters.push(self.vm_type_at_depth(depth + 1)?);
                }
                Ok(VmType::Callable {
                    shared_receiver,
                    unique_receiver,
                    safety: if tag == 6 {
                        Safety::Safe
                    } else {
                        Safety::Unsafe
                    },
                    parameters,
                    result: Box::new(self.vm_type_at_depth(depth + 1)?),
                    effects: Box::new(self.vm_effect_row_at_depth(depth + 1)?),
                })
            }
            31 => {
                let mutability = if self.boolean()? {
                    PointerMutability::Mut
                } else {
                    PointerMutability::Const
                };
                Ok(VmType::RawPointer {
                    mutability,
                    pointee: Box::new(self.vm_type_at_depth(depth + 1)?),
                })
            }
            7 => {
                let count = self.count("tuple fields", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(self.vm_type_at_depth(depth + 1)?);
                }
                Ok(VmType::Tuple(fields))
            }
            8 => {
                let definition = self.def_key()?;
                let count = self.count("nominal type arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.vm_generic_argument_at_depth(depth + 1)?);
                }
                Ok(VmType::Nominal {
                    definition,
                    arguments,
                })
            }
            9 => Ok(VmType::Generic(self.u32()?)),
            10 => Ok(VmType::Array(Box::new(self.vm_type_at_depth(depth + 1)?))),
            32 => Ok(VmType::FixedArray {
                element: Box::new(self.vm_type_at_depth(depth + 1)?), length: self.u64()?,
            }),
            11 => Ok(VmType::Reference {
                unique: match self.byte()? {
                    0 => false,
                    1 => true,
                    _ => {
                        return Err(VmArtifactError::MalformedEncoding {
                            message: "invalid reference mutability",
                        });
                    }
                },
                referent: Box::new(self.vm_type_at_depth(depth + 1)?),
            }),
            12 => Ok(VmType::ConstInteger(self.integer_const()?)),
            13 => Ok(VmType::ConstIntegerExpr(
                self.canonical_integer_expr(depth + 1)?,
            )),
            14 => {
                let lower = self.u64()?;
                let upper = self.quantity_upper()?;
                if upper.is_some_and(|upper| lower > upper) {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid quantity interval",
                    });
                }
                Ok(VmType::ConstQuantity { lower, upper })
            }
            15 => Ok(VmType::ConstGeneric {
                index: self.u32()?,
                kind: decode_const_kind(self.byte()?)?,
            }),
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "unknown VM register type",
            }),
        }
    }
    fn quantity_upper(&mut self) -> Result<Option<u64>, VmArtifactError> {
        match self.byte()? {
            0 => Ok(Some(self.u64()?)),
            1 => Ok(None),
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "invalid quantity upper-bound tag",
            }),
        }
    }
    fn vm_structural_integer_expr(&mut self, depth: u64) -> Result<IntegerConstExpr, VmArtifactError> {
        use crate::types::integer_const::IntegerConstOp as Op;
        if depth > MAX_DECODE_TYPE_DEPTH {
            return Err(VmArtifactError::DecodeLimit { kind: "structural const nesting", limit: MAX_DECODE_TYPE_DEPTH });
        }
        let tag = self.byte()?;
        Ok(match tag {
            0 => IntegerConstExpr::Literal(self.integer_const()?),
            1 => {
                let scalar = decode_const_kind(self.byte()?)?.integer_scalar().ok_or(VmArtifactError::MalformedEncoding {
                    message: "non-integer structural const parameter",
                })?;
                IntegerConstExpr::Param { index: self.u32()?, scalar }
            }
            2..=6 => IntegerConstExpr::Binary {
                op: match tag { 2 => Op::Add, 3 => Op::Sub, 4 => Op::Mul, 5 => Op::Div, _ => Op::Rem },
                left: Box::new(self.vm_structural_integer_expr(depth + 1)?),
                right: Box::new(self.vm_structural_integer_expr(depth + 1)?),
            },
            7 => IntegerConstExpr::Neg(Box::new(self.vm_structural_integer_expr(depth + 1)?)),
            _ => return Err(VmArtifactError::MalformedEncoding { message: "invalid structural integer expression tag" }),
        })
    }
    fn canonical_integer_expr(&mut self, depth: u64) -> Result<IntegerConstExpr, VmArtifactError> {
        let value = self.vm_structural_integer_expr(depth)?;
        super::super::validate_vm_structural_integer_expr(&value)?;
        Ok(value)
    }
    fn vm_generic_arguments(&mut self) -> Result<Vec<VmGenericArgument>, VmArtifactError> {
        self.vm_generic_arguments_at_depth(0)
    }
    fn vm_generic_arguments_at_depth(
        &mut self,
        depth: u64,
    ) -> Result<Vec<VmGenericArgument>, VmArtifactError> {
        let count = self.count("effect protocol arguments", MAX_DECODE_REGISTERS)?;
        let mut values = Vec::with_capacity(count);
        for _ in 0..count {
            values.push(self.vm_generic_argument_at_depth(depth + 1)?);
        }
        Ok(values)
    }
    fn vm_generic_argument_at_depth(
        &mut self,
        depth: u64,
    ) -> Result<VmGenericArgument, VmArtifactError> {
        if depth > MAX_DECODE_TYPE_DEPTH {
            return Err(VmArtifactError::DecodeLimit {
                kind: "effect argument nesting",
                limit: MAX_DECODE_TYPE_DEPTH,
            });
        }
        match self.byte()? {
            0 => Ok(VmGenericArgument::Type(self.vm_type_at_depth(depth + 1)?)),
            1 => Ok(VmGenericArgument::EffectRow(
                self.vm_effect_row_at_depth(depth + 1)?,
            )),
            2 => Ok(VmGenericArgument::Lifetime(match self.byte()? {
                0 => Lifetime::Static,
                1 => Lifetime::Generic(self.u32()?),
                2 => Lifetime::Bound {
                    depth: self.u32()?,
                    index: self.u32()?,
                },
                3 => Lifetime::Elided,
                _ => {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid lifetime argument tag",
                    });
                }
            })),
            3 => Ok(VmGenericArgument::ConstInteger(self.integer_const()?)),
            4 => {
                let lower = self.u64()?;
                let upper = self.quantity_upper()?;
                if upper.is_some_and(|upper| lower > upper) {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid quantity interval",
                    });
                }
                Ok(VmGenericArgument::ConstQuantity { lower, upper })
            }
            5 => {
                let index = self.u32()?;
                let kind = decode_const_kind(self.byte()?)?;
                Ok(VmGenericArgument::ConstGeneric { index, kind })
            }
            6 => Ok(VmGenericArgument::ConstIntegerExpr(
                self.canonical_integer_expr(depth + 1)?,
            )),
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "unknown VM effect argument tag",
            }),
        }
    }
    #[inline(never)]
    fn vm_effect_row_at_depth(&mut self, depth: u64) -> Result<VmEffectRow, VmArtifactError> {
        if depth > MAX_DECODE_TYPE_DEPTH {
            return Err(VmArtifactError::DecodeLimit {
                kind: "effect row nesting",
                limit: MAX_DECODE_TYPE_DEPTH,
            });
        }
        let effect_count = self.count("effect row instances", MAX_DECODE_REGISTERS)?;
        let mut effects = Vec::with_capacity(effect_count);
        for _ in 0..effect_count {
            effects.push(VmEffectInstance {
                definition: self.def_key()?,
                arguments: self.vm_generic_arguments_at_depth(depth + 1)?,
            });
        }
        let projection_count = self.count("effect row projections", MAX_DECODE_REGISTERS)?;
        let mut projections = Vec::with_capacity(projection_count);
        for _ in 0..projection_count {
            let subject = self.vm_type_at_depth(depth + 1)?;
            let trait_definition = self.def_key()?;
            let trait_arguments = self.vm_generic_arguments_at_depth(depth + 1)?;
            let name = self.text()?;
            let item_arguments = self.vm_generic_arguments_at_depth(depth + 1)?;
            projections.push(VmEffectRowProjection {
                subject,
                trait_definition,
                trait_arguments,
                name,
                item_arguments,
            });
        }
        let tail_count = self.count("effect row operands", MAX_DECODE_REGISTERS)?;
        let mut tails = std::collections::BTreeSet::new();
        for _ in 0..tail_count {
            let tail = match self.byte()? {
            0 => EffectTail::Infer(crate::types::EffectVar(self.u32()?)),
            1 => EffectTail::Generic(self.u32()?),
            _ => {
                return Err(VmArtifactError::MalformedEncoding {
                    message: "invalid effect row tail tag",
                });
            }
            };
            if tails.last().is_some_and(|previous| previous >= &tail) {
                return Err(VmArtifactError::MalformedEncoding { message: "effect row operands are not a canonical set" });
            }
            tails.insert(tail);
        }
        let row = VmEffectRow {
            effects,
            projections,
            tails,
        };
        if row
            .effects
            .windows(2)
            .any(|pair| vm_effect_instance_key(&pair[0]) >= vm_effect_instance_key(&pair[1]))
            || row.projections.windows(2).any(|pair| {
                vm_effect_row_projection_key(&pair[0]) >= vm_effect_row_projection_key(&pair[1])
            })
        {
            return Err(VmArtifactError::NonCanonicalEncoding);
        }
        Ok(row)
    }
    fn pattern(&mut self) -> Result<VmPattern, VmArtifactError> {
        self.pattern_at_depth(0)
    }
    fn pattern_at_depth(&mut self, depth: u64) -> Result<VmPattern, VmArtifactError> {
        if depth > MAX_DECODE_TYPE_DEPTH {
            return Err(VmArtifactError::DecodeLimit {
                kind: "pattern nesting",
                limit: MAX_DECODE_TYPE_DEPTH,
            });
        }
        match self.byte()? {
            0 => Ok(VmPattern::Any),
            1 => Ok(VmPattern::Literal(self.text()?)),
            2 => {
                let count = self.count("tuple pattern fields", MAX_DECODE_REGISTERS)?;
                let mut values = Vec::with_capacity(count);
                for _ in 0..count {
                    values.push(self.pattern_at_depth(depth + 1)?);
                }
                Ok(VmPattern::Tuple(values))
            }
            5 => {
                let rest = if self.boolean()? {
                    Some(crate::pattern::ArrayPatternRest { prefix: self.u32()?, omitted: self.u32()? })
                } else { None };
                let element = self.vm_type_at_depth(depth + 1)?;
                let count = self.count("array pattern fields", MAX_DECODE_REGISTERS)?;
                let mut elements = Vec::with_capacity(count);
                for _ in 0..count {
                    elements.push(self.pattern_at_depth(depth + 1)?);
                }
                Ok(VmPattern::Array { element, elements, rest })
            }
            tag @ (3 | 4) => {
                let definition = self.def_key()?;
                let variant = (tag == 4).then(|| self.u32()).transpose()?;
                let field_count = self.u32()?;
                let layout_count = self.count("nominal pattern layout", MAX_DECODE_REGISTERS)?;
                let mut field_types = Vec::with_capacity(layout_count);
                for _ in 0..layout_count {
                    field_types.push(self.vm_type_at_depth(depth + 1)?);
                }
                let count = self.count("nominal pattern fields", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(VmPatternField {
                        index: self.u32()?,
                        ty: self.vm_type_at_depth(depth + 1)?,
                        pattern: self.pattern_at_depth(depth + 1)?,
                    });
                }
                match variant {
                    Some(variant) => Ok(VmPattern::Enum {
                        definition,
                        variant,
                        field_types,
                        field_count,
                        fields,
                    }),
                    None => Ok(VmPattern::Record {
                        definition,
                        field_types,
                        field_count,
                        fields,
                    }),
                }
            }
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "unknown structural pattern tag",
            }),
        }
    }
    fn compare(&mut self) -> Result<VmCompare, VmArtifactError> {
        match self.byte()? {
            0 => Ok(VmCompare::Equal),
            1 => Ok(VmCompare::NotEqual),
            2 => Ok(VmCompare::Less),
            3 => Ok(VmCompare::LessEqual),
            4 => Ok(VmCompare::Greater),
            5 => Ok(VmCompare::GreaterEqual),
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "unknown comparison operator",
            }),
        }
    }
    pub(super) fn def_key(&mut self) -> Result<DefKey, VmArtifactError> {
        Ok(DefKey(Digest::from_bytes(self.array()?)))
    }
    fn register_pair(&mut self) -> Result<(u32, u32), VmArtifactError> {
        Ok((self.u32()?, self.u32()?))
    }
    fn register_triple(&mut self) -> Result<(u32, u32, u32), VmArtifactError> {
        Ok((self.u32()?, self.u32()?, self.u32()?))
    }
    pub(super) fn text(&mut self) -> Result<String, VmArtifactError> {
        let length = self.u64()?;
        if length > MAX_DECODE_TEXT_BYTES || length > usize::MAX as u64 {
            return Err(VmArtifactError::DecodeLimit {
                kind: "text literal bytes",
                limit: MAX_DECODE_TEXT_BYTES,
            });
        }
        String::from_utf8(self.bytes(length as usize)?.to_vec()).map_err(|_| {
            VmArtifactError::MalformedEncoding {
                message: "text literal is not valid UTF-8",
            }
        })
    }
    fn cleanup_proof(&mut self) -> Result<VmCleanupProof, VmArtifactError> {
        let moved_count = self.count("cleanup moved places", MAX_DECODE_REGISTERS)?;
        let mut moved_places = Vec::with_capacity(moved_count);
        for _ in 0..moved_count {
            let path = self.u32()?;
            let binding = self.u32()?;
            let root = self.text()?;
            let field_count = self.count("cleanup moved place fields", MAX_DECODE_REGISTERS)?;
            let mut fields = Vec::with_capacity(field_count);
            for _ in 0..field_count {
                fields.push(self.u32()?);
            }
            moved_places.push(VmCleanupPlace {
                path,
                binding,
                root,
                fields,
            });
        }
        let loan_count = self.count("cleanup active loans", MAX_DECODE_REGISTERS)?;
        let mut active_loans = Vec::with_capacity(loan_count);
        for _ in 0..loan_count {
            let owner = match self.byte()? {
                0 => None,
                1 => Some(self.text()?),
                _ => {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid cleanup loan owner tag",
                    });
                }
            };
            let binding = self.u32()?;
            let root = self.text()?;
            let field_count = self.count("cleanup loan fields", MAX_DECODE_REGISTERS)?;
            let mut fields = Vec::with_capacity(field_count);
            for _ in 0..field_count {
                fields.push(self.u32()?);
            }
            let unique = match self.byte()? {
                0 => false,
                1 => true,
                _ => {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid cleanup loan mutability",
                    });
                }
            };
            active_loans.push(VmCleanupLoan {
                owner,
                binding,
                root,
                fields,
                unique,
            });
        }
        Ok(VmCleanupProof {
            moved_places,
            active_loans,
            storage_erasure: self.storage_erasure_witness()?,
        })
    }
    fn storage_erasure_witness(&mut self) -> Result<VmStorageErasureWitness, VmArtifactError> {
        match self.byte()? {
            0 => Ok(VmStorageErasureWitness::Missing),
            1 => {
                let count = self.count("source-storage erasure storages", MAX_DECODE_REGISTERS)?;
                let mut storages = Vec::with_capacity(count);
                for _ in 0..count {
                    let storage = self.u32()?;
                    let binding = self.u32()?;
                    let value_register = self.u32()?;
                    let initialized = match self.byte()? {
                        0 => false,
                        1 => true,
                        _ => {
                            return Err(VmArtifactError::MalformedEncoding {
                                message: "invalid source-storage initialized tag",
                            });
                        }
                    };
                    let drop_flag = match self.byte()? {
                        0 => None,
                        1 => Some(self.u32()?),
                        _ => {
                            return Err(VmArtifactError::MalformedEncoding {
                                message: "invalid source-storage drop-flag tag",
                            });
                        }
                    };
                    storages.push(VmStorageErasureStorage {
                        storage,
                        binding,
                        value_register,
                        initialized,
                        drop_flag,
                    });
                }
                let count = self.count("source-storage erasure actions", MAX_DECODE_REGISTERS)?;
                let mut actions = Vec::with_capacity(count);
                for _ in 0..count {
                    actions.push(match self.byte()? {
                        0 => VmStorageErasureAction::EndBorrow {
                            storage: self.u32()?,
                        },
                        1 => VmStorageErasureAction::Protect {
                            storage: self.u32()?,
                            register: self.u32()?,
                        },
                        2 => VmStorageErasureAction::Destroy {
                            storage: self.u32()?,
                        },
                        3 => VmStorageErasureAction::SetDropFlag {
                            drop_flag: self.u32()?,
                            initialized: match self.byte()? {
                                0 => false,
                                1 => true,
                                _ => {
                                    return Err(VmArtifactError::MalformedEncoding {
                                        message: "invalid source-storage drop-flag state",
                                    });
                                }
                            },
                        },
                        4 => VmStorageErasureAction::StorageDead {
                            storage: self.u32()?,
                        },
                        _ => {
                            return Err(VmArtifactError::MalformedEncoding {
                                message: "unknown source-storage erasure action",
                            });
                        }
                    });
                }
                let count =
                    self.count("source-storage protected registers", MAX_DECODE_REGISTERS)?;
                let mut protected_registers = Vec::with_capacity(count);
                for _ in 0..count {
                    protected_registers.push(self.u32()?);
                }
                Ok(VmStorageErasureWitness::Verified {
                    storages,
                    actions,
                    protected_registers,
                })
            }
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "invalid source-storage erasure witness tag",
            }),
        }
    }
    pub(super) fn function(&mut self) -> Result<VmFunction, VmArtifactError> {
        let definition = self.def_key()?;
        let safety = if self.boolean()? {
            Safety::Unsafe
        } else {
            Safety::Safe
        };
        let unsafe_execution = self.boolean()?;
        let captures = self.u32()?;
        let parameters = self.u32()?;
        let register_count = self.count("registers", MAX_DECODE_REGISTERS)?;
        let mut registers = Vec::with_capacity(register_count);
        for _ in 0..register_count {
            registers.push(self.vm_type()?);
        }
        let descriptor_count = self.count("nominal copy descriptors", MAX_DECODE_REGISTERS)?;
        let mut nominal_copy_descriptors = Vec::with_capacity(descriptor_count);
        for _ in 0..descriptor_count {
            let definition = self.def_key()?;
            let source_contract = Digest::from_bytes(self.array()?);
            let is_enum = self.boolean()?;
            let argument_count =
                self.count("nominal copy descriptor arguments", MAX_DECODE_REGISTERS)?;
            let mut arguments = Vec::with_capacity(argument_count);
            for _ in 0..argument_count {
                arguments.push(self.vm_generic_argument_at_depth(0)?);
            }
            let variant_count =
                self.count("nominal copy descriptor variants", MAX_DECODE_REGISTERS)?;
            let mut variants = Vec::with_capacity(variant_count);
            for _ in 0..variant_count {
                let field_count =
                    self.count("nominal copy descriptor fields", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(field_count);
                for _ in 0..field_count {
                    fields.push(self.vm_type()?);
                }
                variants.push(fields);
            }
            nominal_copy_descriptors.push(VmNominalCopyDescriptor {
                is_enum,
                definition,
                source_contract,
                arguments,
                variants,
            });
        }
        let instruction_count = self.count("instructions", MAX_DECODE_INSTRUCTIONS)?;
        let mut instructions = Vec::with_capacity(instruction_count);
        for _ in 0..instruction_count {
            instructions.push(self.instruction()?);
        }
        Ok(VmFunction {
            safety,
            unsafe_execution,
            nominal_copy_descriptors,
            definition,
            captures,
            parameters,
            registers,
            instructions,
        })
    }
    fn instruction(&mut self) -> Result<VmInstruction, VmArtifactError> {
        match self.byte()? {
            197 => Ok(VmInstruction::DerefIsInitialized {
                dst: self.u32()?,
                reference: self.u32()?,
            }),
            opcode @ (195 | 196) => {
                let dst = self.u32()?;
                let base = self.u32()?;
                let count = self.count("storage field projections", MAX_DECODE_TYPE_DEPTH)?;
                let mut fields = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(self.u32()?);
                }
                Ok(if opcode == 195 {
                    VmInstruction::TakeProjection { dst, base, fields }
                } else {
                    VmInstruction::IsInitialized { dst, base, fields }
                })
            }
            0 => Ok(VmInstruction::ConstI64 {
                dst: self.u32()?,
                value: self.i64()?,
            }),
            157 => Ok(VmInstruction::ConstU8 {
                dst: self.u32()?,
                value: self.byte()?,
            }),
            158 => Ok(VmInstruction::ConstU16 {
                dst: self.u32()?,
                value: self.u16()?,
            }),
            151 => Ok(VmInstruction::ConstU32 {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            152 => Ok(VmInstruction::ConstU64 {
                dst: self.u32()?,
                value: self.u64()?,
            }),
            159 => Ok(VmInstruction::ConstUsize {
                dst: self.u32()?,
                value: self.u64()?,
            }),
            160 => Ok(VmInstruction::ConstU128 {
                dst: self.u32()?,
                value: self.u128()?,
            }),
            161 => Ok(VmInstruction::ConstI8 {
                dst: self.u32()?,
                value: self.i8()?,
            }),
            162 => Ok(VmInstruction::ConstI16 {
                dst: self.u32()?,
                value: self.i16()?,
            }),
            163 => Ok(VmInstruction::ConstI32 {
                dst: self.u32()?,
                value: self.i32()?,
            }),
            164 => Ok(VmInstruction::ConstIsize {
                dst: self.u32()?,
                value: self.i64()?,
            }),
            165 => Ok(VmInstruction::ConstI128 {
                dst: self.u32()?,
                value: self.i128()?,
            }),
            1 => {
                let (dst, src) = self.register_pair()?;
                Ok(VmInstruction::Copy { dst, src })
            }
            2 => {
                let (dst, src) = self.register_pair()?;
                Ok(VmInstruction::Move { dst, src })
            }
            167 => Ok(VmInstruction::StorageLive {
                binding: self.u32()?,
                local: self.u32()?,
            }),
            168 => Ok(VmInstruction::StorageDead {
                binding: self.u32()?,
                local: self.u32()?,
            }),
            169 => {
                let flag = self.u32()?;
                let value = match self.byte()? {
                    0 => false,
                    1 => true,
                    _ => {
                        return Err(VmArtifactError::MalformedEncoding {
                            message: "invalid source-storage drop flag value",
                        });
                    }
                };
                Ok(VmInstruction::SetDropFlag { flag, value })
            }
            170 => Ok(VmInstruction::DestroyIf {
                local: self.u32()?,
                flag: self.u32()?,
            }),
            38 => {
                let (dst, src) = self.register_pair()?;
                Ok(VmInstruction::Store { dst, src })
            }
            52 => {
                let dst = self.u32()?;
                let src = self.u32()?;
                let unique = match self.byte()? {
                    0 => false,
                    1 => true,
                    _ => {
                        return Err(VmArtifactError::MalformedEncoding {
                            message: "invalid borrow mutability",
                        });
                    }
                };
                let reborrow = match self.byte()? {
                    0 => false,
                    1 => true,
                    _ => {
                        return Err(VmArtifactError::MalformedEncoding {
                            message: "invalid borrow reborrow mode",
                        });
                    }
                };
                let count = self.count("borrow field projections", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(self.u32()?);
                }
                Ok(VmInstruction::Borrow {
                    dst,
                    src,
                    fields,
                    unique,
                    reborrow,
                })
            }
            53 => Ok(VmInstruction::DerefCopy {
                dst: self.u32()?,
                reference: self.u32()?,
            }),
            54 => Ok(VmInstruction::DerefStore {
                reference: self.u32()?,
                src: self.u32()?,
            }),
            174 => Ok(VmInstruction::DerefMove {
                dst: self.u32()?,
                reference: self.u32()?,
            }),
            39 => Ok(VmInstruction::UpdateRecord {
                dst: self.u32()?,
                base: self.u32()?,
                index: self.u32()?,
                field_count: self.u32()?,
                value: self.u32()?,
                field_type: self.vm_type()?,
            }),
            40 => Ok(VmInstruction::PatternTest {
                dst: self.u32()?,
                subject: self.u32()?,
                pattern: self.pattern()?,
            }),
            opcode @ (41 | 208) => {
                let dst = self.u32()?;
                let effect = self.def_key()?;
                let effect_arguments = self.vm_generic_arguments()?;
                let operation = self.u32()?;
                let count = self.count("effect operation arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                let instruction = VmInstruction::Perform {
                    dst,
                    effect,
                    effect_arguments,
                    operation,
                    arguments,
                };
                Ok(if opcode == 208 {
                    instruction.with_owned_effect_payloads()
                } else {
                    instruction
                })
            }
            42 => Ok(VmInstruction::ProjectTuple {
                dst: self.u32()?,
                base: self.u32()?,
                index: self.u32()?,
                field_count: self.u32()?,
                field_type: self.vm_type()?,
            }),
            57 => Ok(VmInstruction::ProjectArray {
                dst: self.u32()?,
                base: self.u32()?,
                index: self.u32()?,
                field_count: self.u32()?,
                element_type: self.vm_type()?,
            }),
            43 => Ok(VmInstruction::Trap),
            opcode @ (44 | 209) => {
                let effect = self.def_key()?;
                let effect_arguments = self.vm_generic_arguments()?;
                let operation = self.u32()?;
                let payload_count =
                    self.count("handler payload destinations", MAX_DECODE_REGISTERS)?;
                let mut payload_destinations = Vec::with_capacity(payload_count);
                for _ in 0..payload_count {
                    payload_destinations.push(self.u32()?);
                }
                let instruction = VmInstruction::InstallHandler {
                    effect,
                    effect_arguments,
                    operation,
                    payload_destinations,
                    resume_type: self.vm_type()?,
                    continuation: match self.byte()? {
                        0 => VmContinuationPolicy::Consume,
                        1 => VmContinuationPolicy::Replay { uses: self.u32()? },
                        2 => VmContinuationPolicy::Terminal,
                        3 => VmContinuationPolicy::Optional,
                        _ => {
                            return Err(VmArtifactError::MalformedEncoding {
                                message: "invalid handler continuation policy",
                            });
                        }
                    },
                    target: self.u32()?,
                };
                if opcode == 209 {
                    let count = self.count("replay-owned roots", MAX_DECODE_REGISTERS)?;
                    let mut roots = Vec::with_capacity(count);
                    for _ in 0..count {
                        roots.push(self.u32()?);
                    }
                    let mut instruction = instruction.with_owned_effect_payloads();
                    if let VmInstruction::InstallHandlerOwned { continuation_owned, .. } =
                        &mut instruction
                    {
                        *continuation_owned = roots;
                    }
                    Ok(instruction)
                } else {
                    Ok(instruction)
                }
            }
            210 => {
                let count = self.count("claimed effect payloads", MAX_DECODE_REGISTERS)?;
                let mut payloads = Vec::with_capacity(count);
                for _ in 0..count {
                    payloads.push(self.u32()?);
                }
                Ok(VmInstruction::ClaimEffectPayloads { payloads })
            }
            45 => Ok(VmInstruction::UninstallHandler),
            198 => Ok(VmInstruction::CompleteHandler { value: self.u32()? }),
            199 => Ok(VmInstruction::DestroyCallable {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            200 => {
                let count = self.count("frame cleanup actions", MAX_DECODE_REGISTERS)?;
                let mut actions = Vec::with_capacity(count);
                for _ in 0..count {
                    actions.push(VmFrameDrop {
                        owner: self.u32()?,
                        destructor: self.def_key()?,
                    });
                }
                Ok(VmInstruction::DeclareFrameCleanup { actions })
            }
            46 => Ok(VmInstruction::Resume { value: self.u32()? }),
            51 => Ok(VmInstruction::ResumeReturn {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            47 => Ok(VmInstruction::Forward),
            69 => Ok(VmInstruction::Cancel),
            70 => Ok(VmInstruction::CaptureResumption { dst: self.u32()? }),
            50 => Ok(VmInstruction::ResumeSnapshot {
                snapshot: self.u32()?,
                value: self.u32()?,
            }),
            55 => {
                let brand_owner = self.def_key()?;
                let brand_label = self.u32()?;
                let handler_depth = self.u32()?;
                let target = self.u32()?;
                let count = self.count("leave arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                let destination_count = self.count("leave destinations", MAX_DECODE_REGISTERS)?;
                if destination_count != count {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "leave arguments and destinations differ in length",
                    });
                }
                let mut destinations = Vec::with_capacity(destination_count);
                for _ in 0..destination_count {
                    destinations.push(self.u32()?);
                }
                Ok(VmInstruction::Leave {
                    brand_owner,
                    brand_label,
                    handler_depth,
                    target,
                    arguments,
                    destinations,
                    cleanup: self.cleanup_proof()?,
                })
            }
            opcode @ (56 | 207) => {
                let dst = self.u32()?;
                let capability = self.text()?;
                let symbol = self.text()?;
                let source_contract = Digest::from_bytes(self.array()?);
                let parameter_count = self.count("host call parameters", MAX_DECODE_REGISTERS)?;
                let mut parameters = Vec::with_capacity(parameter_count);
                for _ in 0..parameter_count {
                    parameters.push(self.vm_type()?);
                }
                let result = self.vm_type()?;
                let resident_count =
                    self.count("native resident operations", MAX_DECODE_REGISTERS)?;
                let mut resident_operations = Vec::with_capacity(resident_count);
                for _ in 0..resident_count {
                    resident_operations.push(VmNativeResident {
                        ty: self.vm_type()?,
                        source_type: Digest::from_bytes(self.array()?),
                        destructor: match self.byte()? {
                            0 => None,
                            1 => Some(self.def_key()?),
                            _ => {
                                return Err(VmArtifactError::MalformedEncoding {
                                    message: "invalid native destructor option",
                                });
                            }
                        },
                    });
                }
                let count = self.count("host call arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                let instruction = VmInstruction::HostCall {
                    dst,
                    capability,
                    symbol,
                    source_contract,
                    parameters,
                    result,
                    resident_operations,
                    arguments,
                };
                Ok(if opcode == 207 {
                    instruction.with_consumed_arguments()
                } else {
                    instruction
                })
            }
            3 => self.i64_arithmetic(|dst, left, right| VmInstruction::AddI64 { dst, left, right }),
            104 => self.i64_arithmetic(|dst, left, right| VmInstruction::WrappingAddI64 {
                dst,
                left,
                right,
            }),
            106 => self.i64_arithmetic(|dst, left, right| VmInstruction::WrappingSubI64 {
                dst,
                left,
                right,
            }),
            107 => self.i64_arithmetic(|dst, left, right| VmInstruction::WrappingMulI64 {
                dst,
                left,
                right,
            }),
            105 => self.i64_arithmetic(|dst, left, right| VmInstruction::IntEqualI64 {
                dst,
                left,
                right,
            }),
            109 => self.i64_arithmetic(|dst, left, right| VmInstruction::IntLessI64 {
                dst,
                left,
                right,
            }),
            110 => self.i64_arithmetic(|dst, left, right| VmInstruction::IntGreaterI64 {
                dst,
                left,
                right,
            }),
            108 => self.i64_arithmetic(|dst, left, right| VmInstruction::BitAndI64 {
                dst,
                left,
                right,
            }),
            153 => self.u32_runtime_binary(|dst, left, right| VmInstruction::BitAndU32 {
                dst,
                left,
                right,
            }),
            154 => self.u32_runtime_binary(|dst, left, right| VmInstruction::BitAndU64 {
                dst,
                left,
                right,
            }),
            155 => {
                let (dst, left, right) = self.register_triple()?;
                Ok(VmInstruction::CompareU32 {
                    dst,
                    left,
                    right,
                    op: self.compare()?,
                })
            }
            156 => {
                let (dst, left, right) = self.register_triple()?;
                Ok(VmInstruction::CompareU64 {
                    dst,
                    left,
                    right,
                    op: self.compare()?,
                })
            }
            112 => self.i64_arithmetic(|dst, left, right| VmInstruction::BitXorI64 {
                dst,
                left,
                right,
            }),
            115 => self.i64_arithmetic(|dst, left, right| VmInstruction::IntShrI64 {
                dst,
                left,
                right,
            }),
            111 => {
                self.i64_arithmetic(|dst, left, right| VmInstruction::BitOrI64 { dst, left, right })
            }
            113 => Ok(VmInstruction::BitNotI64 {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            114 => Ok(VmInstruction::ShlI64 {
                dst: self.u32()?,
                value: self.u32()?,
                count: self.u32()?,
            }),
            4 => self.i64_arithmetic(|dst, left, right| VmInstruction::SubI64 { dst, left, right }),
            5 => self.i64_arithmetic(|dst, left, right| VmInstruction::MulI64 { dst, left, right }),
            opcode @ (6 | 205) => {
                let dst = self.u32()?;
                let callee = self.def_key()?;
                let count = self.count("call arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                let instruction = VmInstruction::Call {
                    dst,
                    callee,
                    arguments,
                };
                Ok(if opcode == 205 {
                    instruction.with_consumed_arguments()
                } else {
                    instruction
                })
            }
            211 => {
                let callee = self.def_key()?;
                let count = self.count("tail transfer arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count { arguments.push(self.u32()?); }
                Ok(VmInstruction::TailCallOwned { callee, arguments })
            }
            212 => Ok(VmInstruction::StoreOwned { dst: self.u32()?, src: self.u32()? }),
            7 => {
                let dst = self.u32()?;
                let bits = self.u64()?;
                if !is_canonical_f64_bits(bits) {
                    return Err(VmArtifactError::NonCanonicalFloat { bits });
                }
                Ok(VmInstruction::ConstF64 { dst, bits })
            }
            171 => {
                let dst = self.u32()?;
                let bits = self.u32()?;
                if !is_canonical_f32_bits(bits) {
                    return Err(VmArtifactError::NonCanonicalFloat {
                        bits: u64::from(bits),
                    });
                }
                Ok(VmInstruction::ConstF32 { dst, bits })
            }
            172 => {
                let result = self.vm_type_at_depth(0)?;
                let returns = match self.byte()? {
                    0 => false,
                    1 => true,
                    _ => {
                        return Err(VmArtifactError::MalformedEncoding {
                            message: "invalid function result control tag",
                        });
                    }
                };
                Ok(VmInstruction::DeclareResult { result, returns })
            }
            138 => {
                let dst = self.u32()?;
                let selector = self.text()?;
                let Some(crate::PrimitiveRole::Float(primitive)) =
                    crate::PrimitiveRole::parse_selector_name(&selector)
                else {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid floating runtime opcode selector",
                    });
                };
                let count = self.count("floating runtime arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                Ok(VmInstruction::FloatIntrinsic {
                    dst,
                    primitive,
                    arguments,
                })
            }
            194 => {
                let dst = self.u32()?;
                let primitive = *MemoryPrimitive::ALL.get(self.byte()? as usize).ok_or(
                    VmArtifactError::MalformedEncoding {
                        message: "invalid memory operation",
                    },
                )?;
                let count = self.count("memory type arguments", 2)?;
                let mut types = Vec::with_capacity(count);
                for _ in 0..count {
                    types.push(self.vm_type()?);
                }
                let count = self.count("memory value arguments", 4)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                Ok(VmInstruction::MemoryIntrinsic {
                    dst,
                    primitive,
                    types,
                    arguments,
                })
            }
            166 => {
                let dst = self.u32()?;
                let selector = self.text()?;
                let Some(primitive) = PrimitiveRole::parse_selector_name(&selector) else {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid integer runtime opcode selector",
                    });
                };
                let scalar = decode_integer_scalar(self.byte()?)?;
                let count = self.count("integer runtime arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                Ok(VmInstruction::IntIntrinsic {
                    dst,
                    primitive,
                    scalar,
                    arguments,
                })
            }
            8 => self.i64_arithmetic(|dst, left, right| VmInstruction::DivI64 { dst, left, right }),
            9 => self.i64_arithmetic(|dst, left, right| VmInstruction::RemI64 { dst, left, right }),
            10 => {
                self.i64_arithmetic(|dst, left, right| VmInstruction::AddF64 { dst, left, right })
            }
            11 => {
                self.i64_arithmetic(|dst, left, right| VmInstruction::SubF64 { dst, left, right })
            }
            12 => {
                self.i64_arithmetic(|dst, left, right| VmInstruction::MulF64 { dst, left, right })
            }
            13 => {
                self.i64_arithmetic(|dst, left, right| VmInstruction::DivF64 { dst, left, right })
            }
            14 => {
                self.i64_arithmetic(|dst, left, right| VmInstruction::RemF64 { dst, left, right })
            }
            15 => Ok(VmInstruction::Return { value: self.u32()? }),
            16 => {
                let dst = self.u32()?;
                let value = match self.byte()? {
                    0 => false,
                    1 => true,
                    _ => {
                        return Err(VmArtifactError::MalformedEncoding {
                            message: "invalid boolean literal",
                        });
                    }
                };
                Ok(VmInstruction::ConstBool { dst, value })
            }
            17 => self.compare_instruction(false),
            18 => self.compare_instruction(true),
            19 => Ok(VmInstruction::NotBool {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            20 => Ok(VmInstruction::ConstChar {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            21 => self.bool_equality(|dst, left, right| VmInstruction::EqBool { dst, left, right }),
            22 => self.bool_equality(|dst, left, right| VmInstruction::NeBool { dst, left, right }),
            23 => {
                let (dst, left, right) = self.register_triple()?;
                Ok(VmInstruction::CompareChar {
                    dst,
                    left,
                    right,
                    op: self.compare()?,
                })
            }
            24 => Ok(VmInstruction::ConstText {
                dst: self.u32()?,
                value: self.text()?,
            }),
            175 => Ok(VmInstruction::ConstStaticData {
                dst: self.u32()?,
                tag: self.u128()?,
                alignment: self.u32()?,
                bytes: {
                    let length = usize::try_from(self.u64()?).map_err(|_| {
                        VmArtifactError::MalformedEncoding {
                            message: "static-data length does not fit usize",
                        }
                    })?;
                    self.bytes(length)?.to_vec()
                },
            }),
            176 => Ok(VmInstruction::StaticLen {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            64 => Ok(VmInstruction::TextByteLen {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            65 => Ok(VmInstruction::TextConcat {
                dst: self.u32()?,
                left: self.u32()?,
                right: self.u32()?,
            }),
            66 => Ok(VmInstruction::TextEq {
                dst: self.u32()?,
                left: self.u32()?,
                right: self.u32()?,
            }),
            67 => Ok(VmInstruction::TextFromUtf8Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            68 => Ok(VmInstruction::TextAsBytes {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            48 => Ok(VmInstruction::CharFromU32Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            49 => Ok(VmInstruction::CharToU32 {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            204 => Ok(VmInstruction::StoreUsize {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            201 => Ok(VmInstruction::ArrayLen {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            202 => Ok(VmInstruction::ArrayElementIsInitialized {
                dst: self.u32()?,
                value: self.u32()?,
                index: self.u32()?,
            }),
            203 => Ok(VmInstruction::TakeArrayElement {
                dst: self.u32()?,
                value: self.u32()?,
                index: self.u32()?,
            }),
            80 => Ok(VmInstruction::BytesLen {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            81 => Ok(VmInstruction::BytesConcat {
                dst: self.u32()?,
                left: self.u32()?,
                right: self.u32()?,
            }),
            82 => Ok(VmInstruction::BytesGet {
                dst: self.u32()?,
                bytes: self.u32()?,
                index: self.u32()?,
            }),
            83 => Ok(VmInstruction::BytesSlice {
                dst: self.u32()?,
                bytes: self.u32()?,
                start: self.u32()?,
                end: self.u32()?,
            }),
            84 => Ok(VmInstruction::BytesFromArrayMove {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            85 => Ok(VmInstruction::BytesToArray {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            86 => Ok(VmInstruction::BytesUtf8ValidUpTo {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            173 => Ok(VmInstruction::Blake3 {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            143 => Ok(VmInstruction::ArrayGetBorrowShared {
                dst: self.u32()?,
                value: self.u32()?,
                index: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            145 => Ok(VmInstruction::ArrayEmpty {
                dst: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            146 => Ok(VmInstruction::ArrayPushMove {
                value: self.u32()?,
                item: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            87 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32CheckedAdd {
                dst,
                left,
                right,
            }),
            88 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32CheckedSub {
                dst,
                left,
                right,
            }),
            89 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32CheckedMul {
                dst,
                left,
                right,
            }),
            90 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32CheckedDiv {
                dst,
                left,
                right,
            }),
            91 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32CheckedRem {
                dst,
                left,
                right,
            }),
            92 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32WrappingAdd {
                dst,
                left,
                right,
            }),
            93 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32WrappingSub {
                dst,
                left,
                right,
            }),
            94 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32WrappingMul {
                dst,
                left,
                right,
            }),
            95 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32WrappingShl {
                dst,
                left,
                right,
            }),
            96 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32WrappingShr {
                dst,
                left,
                right,
            }),
            97 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32CheckedShl {
                dst,
                left,
                right,
            }),
            98 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32CheckedShr {
                dst,
                left,
                right,
            }),
            99 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32Eq {
                dst,
                left,
                right,
            }),
            100 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32Lt {
                dst,
                left,
                right,
            }),
            101 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32Le {
                dst,
                left,
                right,
            }),
            102 => Ok(VmInstruction::U32ToUsize {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            103 => Ok(VmInstruction::UsizeToU32Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            116 => Ok(VmInstruction::I64ToU32Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            117 => Ok(VmInstruction::I64ToU32Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            118 => Ok(VmInstruction::I64ToUsizeChecked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            119 => Ok(VmInstruction::I64ToUsizeWrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            120 => Ok(VmInstruction::I64ToU8Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            121 => Ok(VmInstruction::I64ToU8Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            122 => Ok(VmInstruction::I64ToU16Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            123 => Ok(VmInstruction::I64ToU16Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            124 => Ok(VmInstruction::I64ToI16Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            125 => Ok(VmInstruction::I64ToI16Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            126 => Ok(VmInstruction::I64ToI32Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            127 => Ok(VmInstruction::I64ToI32Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            128 => Ok(VmInstruction::I64ToI8Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            129 => Ok(VmInstruction::I64ToI8Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            130 => Ok(VmInstruction::I64ToU64Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            131 => Ok(VmInstruction::I64ToU64Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            132 => Ok(VmInstruction::I64ToIsizeChecked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            133 => Ok(VmInstruction::I64ToIsizeWrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            134 => Ok(VmInstruction::I64ToU128Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            135 => Ok(VmInstruction::I64ToU128Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            136 => Ok(VmInstruction::I64ToI128Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            137 => Ok(VmInstruction::I64ToI128Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            25 => self.bool_equality(|dst, left, right| VmInstruction::EqText { dst, left, right }),
            26 => self.bool_equality(|dst, left, right| VmInstruction::NeText { dst, left, right }),
            27 => self.i64_arithmetic(|dst, left, right| VmInstruction::ConcatText {
                dst,
                left,
                right,
            }),
            28 => Ok(VmInstruction::ConstUnit { dst: self.u32()? }),
            29 => {
                let dst = self.u32()?;
                let callee = self.def_key()?;
                let count = self.count("callable captures", MAX_DECODE_REGISTERS)?;
                let mut captures = Vec::with_capacity(count);
                for _ in 0..count {
                    captures.push(self.u32()?);
                }
                Ok(VmInstruction::MakeCallable {
                    dst,
                    callee,
                    captures,
                    environment: self.capture_environment()?,
                })
            }
            71 => Ok(VmInstruction::MakeLabel {
                dst: self.u32()?,
                brand_owner: self.def_key()?,
                brand_label: self.u32()?,
                target: self.u32()?,
                destination: self.u32()?,
            }),
            opcode @ (30 | 206) => {
                let dst = self.u32()?;
                let callee = self.u32()?;
                let count = self.count("indirect-call arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                let instruction = VmInstruction::CallIndirect {
                    dst,
                    callee,
                    arguments,
                };
                Ok(if opcode == 206 {
                    instruction.with_consumed_arguments()
                } else {
                    instruction
                })
            }
            31 => Ok(VmInstruction::Jump {
                target: self.u32()?,
            }),
            32 => Ok(VmInstruction::BranchBool {
                condition: self.u32()?,
                then_target: self.u32()?,
                else_target: self.u32()?,
            }),
            opcode @ (33 | 213) => {
                let dst = self.u32()?;
                let count = self.count("tuple fields", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(self.u32()?);
                }
                let value = VmInstruction::MakeTuple { dst, fields };
                Ok(if opcode == 213 { value.with_owned_aggregate() } else { value })
            }
            opcode @ (34 | 215) => {
                let dst = self.u32()?;
                let definition = self.def_key()?;
                let count = self.count("record fields", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(count);
                let mut field_types = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(self.u32()?);
                    field_types.push(self.vm_type()?);
                }
                let value = VmInstruction::MakeRecord {
                    dst,
                    definition,
                    fields,
                    field_types,
                };
                Ok(if opcode == 215 { value.with_owned_aggregate() } else { value })
            }
            35 => Ok(VmInstruction::ProjectRecord {
                dst: self.u32()?,
                base: self.u32()?,
                index: self.u32()?,
                field_count: self.u32()?,
                field_type: self.vm_type()?,
            }),
            opcode @ (36 | 216) => {
                let dst = self.u32()?;
                let definition = self.def_key()?;
                let variant = self.u32()?;
                let count = self.count("enum fields", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(count);
                let mut field_types = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(self.u32()?);
                    field_types.push(self.vm_type()?);
                }
                let value = VmInstruction::MakeEnum {
                    dst,
                    definition,
                    variant,
                    fields,
                    field_types,
                };
                Ok(if opcode == 216 { value.with_owned_aggregate() } else { value })
            }
            opcode @ (37 | 214) => {
                let dst = self.u32()?;
                let element_type = self.vm_type()?;
                let count = self.count("array fields", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(self.u32()?);
                }
                let value = VmInstruction::MakeArray {
                    dst,
                    fields,
                    element_type,
                };
                Ok(if opcode == 214 { value.with_owned_aggregate() } else { value })
            }
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "unknown VM instruction opcode",
            }),
        }
    }
    fn i64_arithmetic(
        &mut self,
        make: impl FnOnce(u32, u32, u32) -> VmInstruction,
    ) -> Result<VmInstruction, VmArtifactError> {
        let (dst, left, right) = self.register_triple()?;
        Ok(make(dst, left, right))
    }
    fn u32_runtime_binary(
        &mut self,
        make: impl FnOnce(u32, u32, u32) -> VmInstruction,
    ) -> Result<VmInstruction, VmArtifactError> {
        let (dst, left, right) = self.register_triple()?;
        Ok(make(dst, left, right))
    }
    fn bool_equality(
        &mut self,
        make: impl FnOnce(u32, u32, u32) -> VmInstruction,
    ) -> Result<VmInstruction, VmArtifactError> {
        let (dst, left, right) = self.register_triple()?;
        Ok(make(dst, left, right))
    }
    fn compare_instruction(&mut self, float: bool) -> Result<VmInstruction, VmArtifactError> {
        let (dst, left, right) = self.register_triple()?;
        let op = self.compare()?;
        Ok(if float {
            VmInstruction::CompareF64 {
                dst,
                left,
                right,
                op,
            }
        } else {
            VmInstruction::CompareI64 {
                dst,
                left,
                right,
                op,
            }
        })
    }
}

#[cfg(test)]
mod row_operand_tests {
    use super::*;

    #[test]
    fn row_union_wire_operands_are_bounded_unique_and_sorted() {
        let row = VmEffectRow { effects: vec![], projections: vec![],
            tails: [EffectTail::Generic(2), EffectTail::Generic(7)].into_iter().collect() };
        let mut bytes = vec![];
        super::super::encode_vm_effect_row(&row, &mut bytes);
        assert_eq!(Decoder::new(&bytes).vm_effect_row_at_depth(0).unwrap(), row);
        // Empty member/projection counts precede the operand count, then
        // each operand has a one-byte kind and four-byte binder index.
        for invalid_index in [1u32, 2] {
            let mut invalid = bytes.clone();
            invalid[30..34].copy_from_slice(&invalid_index.to_le_bytes());
            assert!(matches!(Decoder::new(&invalid).vm_effect_row_at_depth(0),
                Err(VmArtifactError::MalformedEncoding { message: "effect row operands are not a canonical set" })));
        }
        let mut excessive = bytes.clone();
        excessive[16..24].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(matches!(Decoder::new(&excessive).vm_effect_row_at_depth(0), Err(VmArtifactError::DecodeLimit { .. })));
        bytes.pop();
        assert!(Decoder::new(&bytes).vm_effect_row_at_depth(0).is_err());
    }
}
