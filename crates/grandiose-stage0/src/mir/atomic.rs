//! Source-free atomic ABI selection for the Ownership MIR adapter.
//! Operands have already been evaluated. Core IDs are provenance only.
use super::*;

pub(crate) trait AtomicLocals: std::ops::Deref<Target = [MirLocalDecl]> {
    fn allocate(&mut self, local: MirLocalDecl) -> MirLocal;
}
impl AtomicLocals for Vec<MirLocalDecl> {
    fn allocate(&mut self, local: MirLocalDecl) -> MirLocal {
        let id = MirLocal(u32::try_from(self.len()).expect("local arena exceeds u32"));
        self.push(local); id
    }
}
pub(crate) struct AtomicEmitter<'a, L: AtomicLocals> {
    pub locals: &'a mut L,
    pub instructions: &'a mut Vec<MirInstruction>,
    pub nominal_copy_descriptors: &'a mut Vec<MirNominalCopyDescriptor>,
    pub building_nominal_copy_descriptors: &'a mut Vec<(DefKey, Vec<GenericArgument>)>,
    pub diagnostics: &'a mut Vec<MirDiagnostic>,
    pub signatures: Option<&'a ElaboratedInterface>,
    pub runtime_primitives: Option<&'a BTreeMap<DefKey, PrimitiveRole>>,
}
impl<L: AtomicLocals> AtomicEmitter<'_, L> {
    pub(crate) fn intrinsic(&mut self, id: CoreId, dst: MirLocal, operator: String, arguments: Vec<MirLocal>) -> Option<()> {
        let ty = self.locals[dst.0 as usize].ty.clone();
        match arguments.len() {
            1 if true => {
                let value = arguments[0];
                match (operator.as_str(), &ty) {
                    (
                        "+",
                        Type::Scalar(crate::types::ScalarType::I64 | crate::types::ScalarType::F32 | crate::types::ScalarType::F64),
                    ) => {
                        self.instructions
                            .push(MirInstruction::Copy { dst, src: value });
                    }
                    ("-", Type::Scalar(crate::types::ScalarType::I64)) => {
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::I64), id);
                        self.instructions.push(MirInstruction::ConstI64 {
                            dst: zero,
                            value: 0,
                        });
                        self.instructions.push(MirInstruction::SubI64 {
                            dst,
                            left: zero,
                            right: value,
                        });
                    }
                    ("-", Type::Scalar(scalar @ (crate::types::ScalarType::F32 | crate::types::ScalarType::F64))) => {
                        // Negation is not subtraction from +0: that loses
                        // the sign of zero. Use the existing width-specific
                        // IEEE operation for both floating representations.
                        self.instructions.push(MirInstruction::FloatIntrinsic {
                            dst,
                            primitive: crate::runtime_manifest::FloatPrimitive::Neg {
                                width: if *scalar == crate::types::ScalarType::F32 {
                                    crate::runtime_manifest::FloatWidth::F32
                                } else {
                                    crate::runtime_manifest::FloatWidth::F64
                                },
                            },
                            arguments: vec![value],
                        });
                    }
                    ("!", Type::Scalar(crate::types::ScalarType::Bool)) => {
                        self.instructions
                            .push(MirInstruction::NotBool { dst, value });
                    }
                    _ => {
                        self.error("G6005", "prefix operator has no MIR instruction");
                        return None;
                    }
                }
            }
            2 if true
                && matches!(operator.as_str(), "+" | "-" | "*" | "/" | "%") =>
            {
                let left = arguments[0];
                let right = arguments[1];
                let instruction = match (&ty, operator.as_str()) {
                    (Type::Scalar(crate::types::ScalarType::I64), "+") => {
                        MirInstruction::AddI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), "-") => {
                        MirInstruction::SubI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), "*") => {
                        MirInstruction::MulI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), "/") => {
                        MirInstruction::DivI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), "%") => {
                        MirInstruction::RemI64 { dst, left, right }
                    }
                    // Ordinary source arithmetic over u32 has the same
                    // checked semantics as the manifest-bound u32 leaves.
                    // Lower directly to the existing verified instruction
                    // family so bootstrap counters do not require a host
                    // primitive or an i64 detour.
                    (Type::Scalar(crate::types::ScalarType::U32), "+") => {
                        MirInstruction::U32CheckedAdd { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::U32), "-") => {
                        MirInstruction::U32CheckedSub { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::U32), "*") => {
                        MirInstruction::U32CheckedMul { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::U32), "/") => {
                        MirInstruction::U32CheckedDiv { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::U32), "%") => {
                        MirInstruction::U32CheckedRem { dst, left, right }
                    }
                    // `usize` indices use the manifest-bound generic
                    // integer encoder.  Unlike the legacy i64 instruction
                    // family, this keeps pointer-width payload typing in the
                    // canonical artifact and traps deterministically on
                    // overflow through IntCheckedAdd.
                    (Type::Scalar(crate::types::ScalarType::Usize), "+") => {
                        MirInstruction::IntIntrinsic {
                            dst,
                            primitive: PrimitiveRole::IntCheckedAdd,
                            scalar: crate::types::ScalarType::Usize,
                            arguments: vec![left, right],
                        }
                    }
                    // `str_slice` establishes `right <= left` before this
                    // subtraction. The existing generic wrapping primitive
                    // therefore has the same value semantics here while the
                    // public range API reports invalid bounds first.
                    (Type::Scalar(crate::types::ScalarType::Usize), "-") => {
                        MirInstruction::IntIntrinsic {
                            dst,
                            primitive: PrimitiveRole::IntWrappingSub,
                            scalar: crate::types::ScalarType::Usize,
                            arguments: vec![left, right],
                        }
                    }
                    (Type::Scalar(crate::types::ScalarType::Usize), "*") => {
                        MirInstruction::IntIntrinsic {
                            dst,
                            primitive: PrimitiveRole::IntWrappingMul,
                            scalar: crate::types::ScalarType::Usize,
                            arguments: vec![left, right],
                        }
                    }
                    (Type::Scalar(crate::types::ScalarType::Usize), "/") => {
                        // Keep pointer-width division in the generic integer
                        // ABI, just like `usize` addition. The VM validates
                        // the scalar specialization and reports division by
                        // zero or overflow deterministically.
                        MirInstruction::IntIntrinsic {
                            dst,
                            primitive: PrimitiveRole::IntCheckedDiv,
                            scalar: crate::types::ScalarType::Usize,
                            arguments: vec![left, right],
                        }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "+") => {
                        MirInstruction::AddF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Text), "+") => {
                        MirInstruction::ConcatText { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "-") => {
                        MirInstruction::SubF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "*") => {
                        MirInstruction::MulF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "/") => {
                        MirInstruction::DivF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "%") => {
                        MirInstruction::RemF64 { dst, left, right }
                    }
                    _ => {
                        self.error(
                            "G6005",
                            &format!(
                                "operator `{operator}` on `{ty:?}` has no MIR arithmetic instruction"
                            ),
                        );
                        return None;
                    }
                };
                self.instructions.push(instruction);
            }
            2 if true
                && matches!(operator.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=") =>
            {
                let operand_ty = self.locals[arguments[0].0 as usize].ty.clone();
                let left = arguments[0];
                let right = arguments[1];
                let instruction = match (&operand_ty, operator.as_str()) {
                    (Type::Scalar(crate::types::ScalarType::I64), "==") => {
                        MirInstruction::EqI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), "!=") => {
                        MirInstruction::NeI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::U32), "!=") => {
                        MirInstruction::NeU32 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::U64), "!=") => {
                        MirInstruction::NeU64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::U64), "==") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntEqual,
                            scalar: crate::types::ScalarType::U64,
                            arguments: vec![left, right],
                        });
                        MirInstruction::NeU32 { dst, left: predicate, right: zero }
                    }
                    (Type::Scalar(crate::types::ScalarType::U8), "==") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntEqual,
                            scalar: crate::types::ScalarType::U8,
                            arguments: vec![left, right],
                        });
                        MirInstruction::NeU32 { dst, left: predicate, right: zero }
                    }
                    (Type::Scalar(crate::types::ScalarType::Usize), "==") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntEqual,
                            scalar: crate::types::ScalarType::Usize,
                            arguments: vec![left, right],
                        });
                        MirInstruction::NeU32 { dst, left: predicate, right: zero }
                    }
                    (Type::Scalar(crate::types::ScalarType::Usize), "<") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntLess,
                            scalar: crate::types::ScalarType::Usize,
                            arguments: vec![left, right],
                        });
                        MirInstruction::NeU32 { dst, left: predicate, right: zero }
                    }
                    (Type::Scalar(crate::types::ScalarType::Usize), "!=") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let equal = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntEqual,
                            scalar: crate::types::ScalarType::Usize,
                            arguments: vec![left, right],
                        });
                        self.instructions.push(MirInstruction::NeU32 { dst: equal, left: predicate, right: zero });
                        MirInstruction::NotBool { dst, value: equal }
                    }
                    (Type::Scalar(crate::types::ScalarType::Usize), "<=") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let greater = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntLess,
                            scalar: crate::types::ScalarType::Usize,
                            arguments: vec![right, left],
                        });
                        self.instructions.push(MirInstruction::NeU32 { dst: greater, left: predicate, right: zero });
                        MirInstruction::NotBool { dst, value: greater }
                    }
                    (Type::Scalar(crate::types::ScalarType::Usize), ">") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntLess,
                            scalar: crate::types::ScalarType::Usize,
                            arguments: vec![right, left],
                        });
                        MirInstruction::NeU32 { dst, left: predicate, right: zero }
                    }
                    (Type::Scalar(crate::types::ScalarType::Usize), ">=") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let less = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntLess,
                            scalar: crate::types::ScalarType::Usize,
                            arguments: vec![left, right],
                        });
                        self.instructions.push(MirInstruction::NeU32 { dst: less, left: predicate, right: zero });
                        MirInstruction::NotBool { dst, value: less }
                    }
                    (Type::Scalar(crate::types::ScalarType::U8), "!=") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let equal = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntEqual,
                            scalar: crate::types::ScalarType::U8,
                            arguments: vec![left, right],
                        });
                        self.instructions.push(MirInstruction::NeU32 { dst: equal, left: predicate, right: zero });
                        MirInstruction::NotBool { dst, value: equal }
                    }
                    (Type::Scalar(crate::types::ScalarType::U8), "<") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntLess,
                            scalar: crate::types::ScalarType::U8,
                            arguments: vec![left, right],
                        });
                        MirInstruction::NeU32 { dst, left: predicate, right: zero }
                    }
                    (Type::Scalar(crate::types::ScalarType::U8), "<=") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let greater = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntLess,
                            scalar: crate::types::ScalarType::U8,
                            arguments: vec![right, left],
                        });
                        self.instructions.push(MirInstruction::NeU32 { dst: greater, left: predicate, right: zero });
                        MirInstruction::NotBool { dst, value: greater }
                    }
                    (Type::Scalar(crate::types::ScalarType::U8), ">") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntLess,
                            scalar: crate::types::ScalarType::U8,
                            arguments: vec![right, left],
                        });
                        MirInstruction::NeU32 { dst, left: predicate, right: zero }
                    }
                    (Type::Scalar(crate::types::ScalarType::U8), ">=") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let less = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntLess,
                            scalar: crate::types::ScalarType::U8,
                            arguments: vec![left, right],
                        });
                        self.instructions.push(MirInstruction::NeU32 { dst: less, left: predicate, right: zero });
                        MirInstruction::NotBool { dst, value: less }
                    }
                    (Type::Scalar(crate::types::ScalarType::U64), "<") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntLess,
                            scalar: crate::types::ScalarType::U64,
                            arguments: vec![left, right],
                        });
                        MirInstruction::NeU32 { dst, left: predicate, right: zero }
                    }
                    (Type::Scalar(crate::types::ScalarType::U64), "<=") => {
                        let raw_greater = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let greater = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: raw_greater,
                            primitive: PrimitiveRole::IntLess,
                            scalar: crate::types::ScalarType::U64,
                            arguments: vec![right, left],
                        });
                        self.instructions.push(MirInstruction::NeU32 {
                            dst: greater,
                            left: raw_greater,
                            right: zero,
                        });
                        MirInstruction::NotBool { dst, value: greater }
                    }
                    (Type::Scalar(crate::types::ScalarType::U64), ">") => {
                        let predicate = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive: PrimitiveRole::IntLess,
                            scalar: crate::types::ScalarType::U64,
                            arguments: vec![right, left],
                        });
                        MirInstruction::NeU32 { dst, left: predicate, right: zero }
                    }
                    (Type::Scalar(crate::types::ScalarType::U64), ">=") => {
                        let raw_less = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::U32), id);
                        let less = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), id);
                        self.instructions.push(MirInstruction::ConstU32 { dst: zero, value: 0 });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: raw_less,
                            primitive: PrimitiveRole::IntLess,
                            scalar: crate::types::ScalarType::U64,
                            arguments: vec![left, right],
                        });
                        self.instructions.push(MirInstruction::NeU32 {
                            dst: less,
                            left: raw_less,
                            right: zero,
                        });
                        MirInstruction::NotBool { dst, value: less }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), "<") => {
                        MirInstruction::LtI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), "<=") => {
                        MirInstruction::LeI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), ">") => {
                        MirInstruction::GtI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), ">=") => {
                        MirInstruction::GeI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::U32), "==") => {
                        MirInstruction::U32Eq { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::U32), "<") => {
                        MirInstruction::U32Lt { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::U32), "<=") => {
                        MirInstruction::U32Le { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::U32), ">") => {
                        let less_equal =
                            self.alloc(Type::Scalar(crate::types::ScalarType::Bool), id);
                        self.instructions.push(MirInstruction::U32Le {
                            dst: less_equal,
                            left,
                            right,
                        });
                        MirInstruction::NotBool {
                            dst,
                            value: less_equal,
                        }
                    }
                    (Type::Scalar(crate::types::ScalarType::U32), ">=") => {
                        let less = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), id);
                        self.instructions.push(MirInstruction::U32Lt {
                            dst: less,
                            left,
                            right,
                        });
                        MirInstruction::NotBool { dst, value: less }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "==") => {
                        MirInstruction::EqF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "!=") => {
                        MirInstruction::NeF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "<") => {
                        MirInstruction::LtF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "<=") => {
                        MirInstruction::LeF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), ">") => {
                        MirInstruction::GtF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), ">=") => {
                        MirInstruction::GeF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Bool), "==") => {
                        MirInstruction::EqBool { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Bool), "!=") => {
                        MirInstruction::NeBool { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Text), "==") => {
                        MirInstruction::EqText { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Text), "!=") => {
                        MirInstruction::NeText { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Char), "==") => {
                        MirInstruction::EqChar { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Char), "!=") => {
                        MirInstruction::NeChar { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Char), "<") => {
                        MirInstruction::LtChar { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Char), "<=") => {
                        MirInstruction::LeChar { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Char), ">") => {
                        MirInstruction::GtChar { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Char), ">=") => {
                        MirInstruction::GeChar { dst, left, right }
                    }
                    // The VM's verified generic-integer family already
                    // covers every integer width.  Keep source comparisons
                    // on the same path when a scalar does not have a legacy
                    // dedicated MIR opcode (for example u16 and i128), so
                    // the source-defined Ord implementations are not
                    // artificially limited by lowering coverage.
                    (ty, operator) if integer_scalar_type(ty).is_some() => {
                        let scalar = integer_scalar_type(ty)
                            .expect("the guarded integer scalar is present");
                        let primitive = match operator {
                            "==" | "!=" => PrimitiveRole::IntEqual,
                            "<" | ">=" => PrimitiveRole::IntLess,
                            ">" | "<=" => PrimitiveRole::IntGreater,
                            _ => unreachable!("comparison operator was filtered above"),
                        };
                        let (left, right) = match operator {
                            "<=" | ">=" => (right, left),
                            _ => (left, right),
                        };
                        let predicate = self.alloc(
                            Type::Scalar(crate::types::ScalarType::U32),
                            id,
                        );
                        let zero = self.alloc(
                            Type::Scalar(crate::types::ScalarType::U32),
                            id,
                        );
                        self.instructions.push(MirInstruction::ConstU32 {
                            dst: zero,
                            value: 0,
                        });
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst: predicate,
                            primitive,
                            scalar,
                            arguments: vec![left, right],
                        });
                        if operator == "!=" {
                            let equal = self.alloc(
                                Type::Scalar(crate::types::ScalarType::Bool),
                                id,
                            );
                            self.instructions.push(MirInstruction::NeU32 {
                                dst: equal,
                                left: predicate,
                                right: zero,
                            });
                            MirInstruction::NotBool { dst, value: equal }
                        } else {
                            MirInstruction::NeU32 {
                                dst,
                                left: predicate,
                                right: zero,
                            }
                        }
                    }
                    _ => {
                        self.error("G6005", "comparison type has no MIR instruction");
                        return None;
                    }
                };
                self.instructions.push(instruction);
            }
            _ => { self.error("G6005", "intrinsic arity or operator is invalid"); return None; }
        }
        Some(())
    }

    pub(crate) fn call(&mut self, id: CoreId, dst: MirLocal, callee: DefKey,
        generic_arguments: Vec<GenericArgument>, host_import: Option<crate::signature::HostImport>,
        arguments: Vec<MirLocal>) -> Option<()> {
        match self
            .runtime_primitives
            .and_then(|primitives| primitives.get(&callee))
            .copied()
        {
            Some(PrimitiveRole::TextByteLen) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "TextByteLen primitive must have one Text operand",
                    );
                    return None;
                };
                if !generic_arguments.is_empty()
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Text)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Usize)
                {
                    self.error(
                    "G6005",
                    "TextByteLen primitive ABI does not match manifest contract",
                );
                    return None;
                }
                self.instructions
                    .push(MirInstruction::TextByteLen { dst, value: *value });
            }
            Some(PrimitiveRole::StaticLen) => {
                let [value] = arguments.as_slice() else {
                    self.error("G6005", "StaticLen requires one static-data operand");
                    return None;
                };
                let data = Type::StaticData {
                    element: Box::new(Type::Scalar(crate::types::ScalarType::U8)),
                    tag: 0x4752_414e_4449_4f53_455f_5354_4154_4943,
                    alignment: 1,
                };
                if !generic_arguments.is_empty()
                    || self.locals[value.0 as usize].ty != data
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Usize)
                {
                    self.error("G6005", "StaticLen primitive ABI does not match manifest contract");
                    return None;
                }
                self.instructions.push(MirInstruction::StaticLen { dst, value: *value });
            }
            Some(PrimitiveRole::TextConcat) => {
                let [left, right] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "TextConcat primitive must have two Text operands",
                    );
                    return None;
                };
                if !generic_arguments.is_empty()
                    || self.locals[left.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Text)
                    || self.locals[right.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Text)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Text)
                {
                    self.error(
                        "G6005",
                        "TextConcat primitive ABI does not match manifest contract",
                    );
                    return None;
                }
                self.instructions.push(MirInstruction::TextConcat {
                    dst,
                    left: *left,
                    right: *right,
                });
            }
            Some(PrimitiveRole::TextEq) => {
                let [left, right] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "TextEq primitive must have two Text operands",
                    );
                    return None;
                };
                if !generic_arguments.is_empty()
                    || self.locals[left.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Text)
                    || self.locals[right.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Text)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U32)
                {
                    self.error(
                        "G6005",
                        "TextEq primitive ABI does not match manifest contract",
                    );
                    return None;
                }
                self.instructions.push(MirInstruction::TextEq {
                    dst,
                    left: *left,
                    right: *right,
                });
            }
            Some(PrimitiveRole::TextFromUtf8Checked) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "TextFromUtf8Checked primitive must have one Bytes operand",
                    );
                    return None;
                };
                if !generic_arguments.is_empty()
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Bytes)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Text)
                {
                    self.error("G6005", "TextFromUtf8Checked primitive ABI does not match manifest contract");
                    return None;
                }
                self.instructions.push(MirInstruction::TextFromUtf8Checked {
                    dst,
                    value: *value,
                });
            }
            Some(PrimitiveRole::TextAsBytes) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "TextAsBytes primitive must have one Text operand",
                    );
                    return None;
                };
                if !generic_arguments.is_empty()
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Text)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Bytes)
                {
                    self.error(
                    "G6005",
                    "TextAsBytes primitive ABI does not match manifest contract",
                );
                    return None;
                }
                self.instructions
                    .push(MirInstruction::TextAsBytes { dst, value: *value });
            }
            Some(PrimitiveRole::CharFromU32Checked) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "CharFromU32Checked primitive must have one u32 operand",
                    );
                    return None;
                };
                if !generic_arguments.is_empty()
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U32)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Char)
                {
                    self.error("G6005", "CharFromU32Checked primitive ABI does not match manifest contract");
                    return None;
                }
                self.instructions.push(MirInstruction::CharFromU32Checked {
                    dst,
                    value: *value,
                });
            }
            Some(PrimitiveRole::CharToU32) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "CharToU32 primitive must have one Char operand",
                    );
                    return None;
                };
                if !generic_arguments.is_empty()
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Char)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U32)
                {
                    self.error(
                        "G6005",
                        "CharToU32 primitive ABI does not match manifest contract",
                    );
                    return None;
                }
                self.instructions
                    .push(MirInstruction::CharToU32 { dst, value: *value });
            }
            Some(PrimitiveRole::Blake3) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "BLAKE3 primitive must have one Bytes operand",
                    );
                    return None;
                };
                if !generic_arguments.is_empty()
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Bytes)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Bytes)
                {
                    self.error(
                        "G6005",
                        "BLAKE3 primitive ABI does not match manifest contract",
                    );
                    return None;
                }
                self.instructions.push(MirInstruction::Blake3 {
                    dst,
                    value: *value,
                });
            }
            Some(PrimitiveRole::BytesLen | PrimitiveRole::BytesUtf8ValidUpTo) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "Bytes length primitive must have one Bytes operand",
                    );
                    return None;
                };
                if !generic_arguments.is_empty()
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Bytes)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Usize)
                {
                    self.error(
                        "G6005",
                        "Bytes primitive ABI does not match manifest contract",
                    );
                    return None;
                }
                self.instructions.push(
                    if matches!(
                        self.runtime_primitives
                            .and_then(|primitives| primitives.get(&callee)),
                        Some(PrimitiveRole::BytesLen)
                    ) {
                        MirInstruction::BytesLen { dst, value: *value }
                    } else {
                        MirInstruction::BytesUtf8ValidUpTo { dst, value: *value }
                    },
                );
            }
            Some(PrimitiveRole::BytesConcat) => {
                let [left, right] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "BytesConcat primitive must have two Bytes operands",
                    );
                    return None;
                };
                if !generic_arguments.is_empty()
                    || self.locals[left.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Bytes)
                    || self.locals[right.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Bytes)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Bytes)
                {
                    self.error("G6005", "BytesConcat primitive ABI does not match manifest contract");
                    return None;
                }
                self.instructions.push(MirInstruction::BytesConcat {
                    dst,
                    left: *left,
                    right: *right,
                });
            }
            Some(PrimitiveRole::BytesGet) => {
                let [bytes, index] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "BytesGet primitive must have Bytes and usize operands",
                    );
                    return None;
                };
                if !generic_arguments.is_empty()
                    || self.locals[bytes.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Bytes)
                    || self.locals[index.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Usize)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U8)
                {
                    self.error(
                        "G6005",
                        "BytesGet primitive ABI does not match manifest contract",
                    );
                    return None;
                }
                self.instructions.push(MirInstruction::BytesGet {
                    dst,
                    bytes: *bytes,
                    index: *index,
                });
            }
            Some(PrimitiveRole::BytesSlice) => {
                let [bytes, start, end] = arguments.as_slice() else {
                    self.error("G6005", "BytesSlice primitive must have Bytes and two usize operands");
                    return None;
                };
                if !generic_arguments.is_empty()
                    || self.locals[bytes.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Bytes)
                    || self.locals[start.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Usize)
                    || self.locals[end.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Usize)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Bytes)
                {
                    self.error(
                        "G6005",
                        "BytesSlice primitive ABI does not match manifest contract",
                    );
                    return None;
                }
                self.instructions.push(MirInstruction::BytesSlice {
                    dst,
                    bytes: *bytes,
                    start: *start,
                    end: *end,
                });
            }
            Some(PrimitiveRole::BytesFromArrayMove) => {
                let [value] = arguments.as_slice() else {
                    self.error("G6005", "BytesFromArrayMove primitive must have one Array<u8> operand");
                    return None;
                };
                if !generic_arguments.is_empty()
                    || self.locals[value.0 as usize].ty
                        != Type::Array(Box::new(Type::Scalar(
                            crate::types::ScalarType::U8,
                        )))
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Bytes)
                {
                    self.error("G6005", "BytesFromArrayMove primitive ABI does not match manifest contract");
                    return None;
                }
                self.instructions.push(MirInstruction::BytesFromArrayMove {
                    dst,
                    value: *value,
                });
            }
            Some(PrimitiveRole::BytesToArray) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "BytesToArray primitive must have one Bytes operand",
                    );
                    return None;
                };
                if !generic_arguments.is_empty()
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Bytes)
                    || self.locals[dst.0 as usize].ty
                        != Type::Array(Box::new(Type::Scalar(
                            crate::types::ScalarType::U8,
                        )))
                {
                    self.error("G6005", "BytesToArray primitive ABI does not match manifest contract");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::BytesToArray { dst, value: *value });
            }
            Some(role)
                if is_generic_integer_runtime_role(role)
                    && generic_arguments.as_slice()
                        != [GenericArgument::Type(Type::Scalar(
                            crate::types::ScalarType::I64,
                        ))] =>
            {
                let [GenericArgument::Type(source)] = generic_arguments.as_slice()
                else {
                    self.error(
                        "G6005",
                        "generic integer primitive requires one type argument",
                    );
                    return None;
                };
                let expected_result =
                    generic_integer_runtime_result(role, source.clone())
                        .expect("integer role was classified before lowering");
                if self.locals[dst.0 as usize].ty != expected_result {
                    self.error(
                        "G6005",
                        "generic integer primitive result does not match its manifest ABI",
                    );
                    return None;
                }
                let expected_arity = if matches!(
                    role,
                    PrimitiveRole::IntBitNot
                        | PrimitiveRole::IntWrappingNeg
                        | PrimitiveRole::IntConvertCheckedToI64
                        | PrimitiveRole::IntConvertWrappingToI64
                        | PrimitiveRole::IntConvertCheckedToU32
                        | PrimitiveRole::IntConvertWrappingToU32
                        | PrimitiveRole::IntConvertCheckedToUsize
                        | PrimitiveRole::IntConvertWrappingToUsize
                        | PrimitiveRole::IntConvertCheckedToU8
                        | PrimitiveRole::IntConvertWrappingToU8
                        | PrimitiveRole::IntConvertCheckedToU16
                        | PrimitiveRole::IntConvertWrappingToU16
                        | PrimitiveRole::IntConvertCheckedToI16
                        | PrimitiveRole::IntConvertWrappingToI16
                        | PrimitiveRole::IntConvertCheckedToI32
                        | PrimitiveRole::IntConvertWrappingToI32
                        | PrimitiveRole::IntConvertCheckedToI8
                        | PrimitiveRole::IntConvertWrappingToI8
                        | PrimitiveRole::IntConvertCheckedToU64
                        | PrimitiveRole::IntConvertWrappingToU64
                        | PrimitiveRole::IntConvertCheckedToIsize
                        | PrimitiveRole::IntConvertWrappingToIsize
                        | PrimitiveRole::IntConvertCheckedToU128
                        | PrimitiveRole::IntConvertWrappingToU128
                        | PrimitiveRole::IntConvertCheckedToI128
                        | PrimitiveRole::IntConvertWrappingToI128
                ) {
                    1
                } else {
                    2
                };
                if arguments.len() != expected_arity
                    || self.locals[arguments[0].0 as usize].ty != *source
                    || (expected_arity == 2
                        && self.locals[arguments[1].0 as usize].ty
                            != if matches!(
                                role,
                                PrimitiveRole::IntShl | PrimitiveRole::IntShr
                            ) {
                                Type::Scalar(crate::types::ScalarType::U32)
                            } else {
                                source.clone()
                            })
                {
                    self.error(
                        "G6005",
                        "generic integer primitive operands do not match its manifest ABI",
                    );
                    return None;
                }
                match source {
                    Type::Scalar(scalar) => {
                        self.instructions.push(MirInstruction::IntIntrinsic {
                            dst,
                            primitive: role,
                            scalar: *scalar,
                            arguments: arguments.clone(),
                        });
                    }
                    Type::Generic(_) => {
                        self.instructions.push(
                            MirInstruction::IntGenericIntrinsic {
                                dst,
                                primitive: role,
                                arguments: arguments.clone(),
                            },
                        );
                    }
                    _ => {
                        self.error(
                            "G6005",
                            "generic integer primitive requires a runtime integer scalar",
                        );
                        return None;
                    }
                }
            }
            Some(
                role @ (PrimitiveRole::U32CheckedAdd
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
                | PrimitiveRole::U32CheckedShr
                | PrimitiveRole::U32Eq
                | PrimitiveRole::U32Lt
                | PrimitiveRole::U32Le),
            ) => {
                let [left, right] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "u32 runtime primitive must have two u32 operands",
                    );
                    return None;
                };
                let result = if matches!(
                    role,
                    PrimitiveRole::U32Eq
                        | PrimitiveRole::U32Lt
                        | PrimitiveRole::U32Le
                ) {
                    crate::types::ScalarType::Bool
                } else {
                    crate::types::ScalarType::U32
                };
                if !generic_arguments.is_empty()
                    || self.locals[left.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U32)
                    || self.locals[right.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U32)
                    || self.locals[dst.0 as usize].ty != Type::Scalar(result)
                {
                    self.error("G6005", "u32 runtime primitive ABI does not match manifest contract");
                    return None;
                }
                self.instructions.push(match role {
                    PrimitiveRole::U32CheckedAdd => MirInstruction::U32CheckedAdd {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::U32CheckedSub => MirInstruction::U32CheckedSub {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::U32CheckedMul => MirInstruction::U32CheckedMul {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::U32CheckedDiv => MirInstruction::U32CheckedDiv {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::U32CheckedRem => MirInstruction::U32CheckedRem {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::U32WrappingAdd => {
                        MirInstruction::U32WrappingAdd {
                            dst,
                            left: *left,
                            right: *right,
                        }
                    }
                    PrimitiveRole::U32WrappingSub => {
                        MirInstruction::U32WrappingSub {
                            dst,
                            left: *left,
                            right: *right,
                        }
                    }
                    PrimitiveRole::U32WrappingMul => {
                        MirInstruction::U32WrappingMul {
                            dst,
                            left: *left,
                            right: *right,
                        }
                    }
                    PrimitiveRole::U32WrappingShl => {
                        MirInstruction::U32WrappingShl {
                            dst,
                            left: *left,
                            right: *right,
                        }
                    }
                    PrimitiveRole::U32WrappingShr => {
                        MirInstruction::U32WrappingShr {
                            dst,
                            left: *left,
                            right: *right,
                        }
                    }
                    PrimitiveRole::U32CheckedShl => MirInstruction::U32CheckedShl {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::U32CheckedShr => MirInstruction::U32CheckedShr {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::U32Eq => MirInstruction::U32Eq {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::U32Lt => MirInstruction::U32Lt {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::U32Le => MirInstruction::U32Le {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    _ => {
                        unreachable!("role was constrained by the enclosing match")
                    }
                });
            }
            Some(
                role @ (PrimitiveRole::U32ToUsize
                | PrimitiveRole::UsizeToU32Checked),
            ) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "integer conversion primitive must have one operand",
                    );
                    return None;
                };
                let (input, output) = if matches!(role, PrimitiveRole::U32ToUsize) {
                    (
                        crate::types::ScalarType::U32,
                        crate::types::ScalarType::Usize,
                    )
                } else {
                    (
                        crate::types::ScalarType::Usize,
                        crate::types::ScalarType::U32,
                    )
                };
                if !generic_arguments.is_empty()
                    || self.locals[value.0 as usize].ty != Type::Scalar(input)
                    || self.locals[dst.0 as usize].ty != Type::Scalar(output)
                {
                    self.error("G6005", "integer conversion primitive ABI does not match manifest contract");
                    return None;
                }
                self.instructions.push(
                    if matches!(role, PrimitiveRole::U32ToUsize) {
                        MirInstruction::U32ToUsize { dst, value: *value }
                    } else {
                        MirInstruction::UsizeToU32Checked { dst, value: *value }
                    },
                );
            }
            Some(PrimitiveRole::BranchBool) => {
                // BranchBool remains a source-level callable until
                // its control-flow lowering is introduced. It must
                // not silently select the Text primitive path.
                self.instructions.push(MirInstruction::Call {
                    dst,
                    callee,
                    generic_arguments,
                    trait_instance: None,
                    arguments,
                });
            }
            Some(PrimitiveRole::Abort) => {
                if !generic_arguments.is_empty()
                    || !arguments.is_empty()
                    || !matches!(self.locals[dst.0 as usize].ty, Type::Never)
                {
                    self.error(
                        "G6005",
                        "Abort primitive ABI does not match manifest contract",
                    );
                    return None;
                }
                self.instructions.push(MirInstruction::Abort);
            }
            Some(PrimitiveRole::IntConvertWrappingToU32) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic wrapping i64-to-u32 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U32)
                {
                    self.error(
                        "G6005",
                        "generic wrapping i64-to-u32 conversion is only VM-specialized for frozen i64",
                    );
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToU32Wrapping { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertWrappingToUsize) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic wrapping integer-to-usize conversion requires one operand",
                    );
                    return None;
                };
                let scalar = match generic_arguments.as_slice() {
                    [GenericArgument::Type(Type::Scalar(scalar))]
                        if integer_scalar_type(&Type::Scalar(*scalar)).is_some() =>
                    {
                        *scalar
                    }
                    _ => {
                        self.error(
                            "G6005",
                            "generic wrapping integer-to-usize conversion requires one frozen integer scalar argument",
                        );
                        return None;
                    }
                };
                if self.locals[value.0 as usize].ty != Type::Scalar(scalar)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Usize)
                {
                    self.error(
                        "G6005",
                        "generic wrapping integer-to-usize conversion does not match its frozen scalar contract",
                    );
                    return None;
                }
                if scalar == crate::types::ScalarType::I64 {
                    self.instructions.push(MirInstruction::I64ToUsizeWrapping {
                        dst,
                        value: *value,
                    });
                } else {
                    self.instructions.push(MirInstruction::IntIntrinsic {
                        dst,
                        primitive: PrimitiveRole::IntConvertWrappingToUsize,
                        scalar,
                        arguments: vec![*value],
                    });
                }
            }
            Some(PrimitiveRole::IntConvertWrappingToU8) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic wrapping i64-to-u8 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U8)
                {
                    self.error(
                        "G6005",
                        "generic wrapping i64-to-u8 conversion is only VM-specialized for frozen i64",
                    );
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToU8Wrapping { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertWrappingToU16) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic wrapping i64-to-u16 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U16)
                {
                    self.error(
                        "G6005",
                        "generic wrapping i64-to-u16 conversion is only VM-specialized for frozen i64",
                    );
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToU16Wrapping { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertWrappingToI16) => {
                let [value] = arguments.as_slice() else {
                    self.error("G6005", "generic wrapping i64-to-i16 conversion requires one operand");
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I16)
                {
                    self.error("G6005", "generic wrapping i64-to-i16 conversion is only VM-specialized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToI16Wrapping { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertWrappingToI32) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic wrapping i64-to-i32 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I32)
                {
                    self.error(
                        "G6005",
                        "generic wrapping i64-to-i32 conversion is only VM-specialized for frozen i64",
                    );
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToI32Wrapping { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertWrappingToI8) => {
                let [value] = arguments.as_slice() else {
                    self.error("G6005", "generic wrapping i64-to-i8 conversion requires one operand");
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I8)
                {
                    self.error("G6005", "generic wrapping i64-to-i8 conversion is only VM-specialized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToI8Wrapping { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertWrappingToU64) => {
                let [value] = arguments.as_slice() else {
                    self.error("G6005", "generic wrapping i64-to-u64 conversion requires one operand");
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U64)
                {
                    self.error("G6005", "generic wrapping i64-to-u64 conversion is only VM-specialized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToU64Wrapping { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertWrappingToU128) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic wrapping u128 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U128)
                {
                    self.error("G6005", "generic wrapping u128 conversion is only VM-specialized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToU128Wrapping { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertWrappingToI128) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic wrapping i128 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I128)
                {
                    self.error("G6005", "generic wrapping i128 conversion is only VM-specialized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToI128Wrapping { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertWrappingToIsize) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic wrapping isize conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Isize)
                {
                    self.error("G6005", "generic wrapping isize conversion is only VM-specialized for frozen i64");
                    return None;
                }
                self.instructions.push(MirInstruction::I64ToIsizeWrapping {
                    dst,
                    value: *value,
                });
            }
            Some(role @ PrimitiveRole::IntBitNot) => {
                let [value] = arguments.as_slice() else {
                    self.error("G6005", "generic int bit-not requires one operand");
                    return None;
                };
                let scalar = match generic_arguments.as_slice() {
                    [GenericArgument::Type(Type::Scalar(scalar))]
                        if integer_scalar_type(&Type::Scalar(*scalar)).is_some() =>
                    {
                        *scalar
                    }
                    _ => {
                        self.error(
                            "G6005",
                            "generic int bit-not requires one frozen integer scalar argument",
                        );
                        return None;
                    }
                };
                let expected = Type::Scalar(scalar);
                if self.locals[value.0 as usize].ty != expected
                    || self.locals[dst.0 as usize].ty != expected
                {
                    self.error(
                        "G6005",
                        "generic int bit-not operand does not match its frozen scalar contract",
                    );
                    return None;
                }
                if scalar == crate::types::ScalarType::I64 {
                    self.instructions
                        .push(MirInstruction::BitNotI64 { dst, value: *value });
                } else {
                    self.instructions.push(MirInstruction::IntIntrinsic {
                        dst,
                        primitive: role,
                        scalar,
                        arguments: vec![*value],
                    });
                }
            }
            Some(PrimitiveRole::IntWrappingNeg) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic int wrapping-neg requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                {
                    self.error(
                        "G6005",
                        "generic int wrapping-neg is only VM-specialized for frozen i64",
                    );
                    return None;
                }
                let zero =
                    self.alloc(Type::Scalar(crate::types::ScalarType::I64), id);
                self.instructions.push(MirInstruction::ConstI64 {
                    dst: zero,
                    value: 0,
                });
                self.instructions.push(MirInstruction::WrappingSubI64 {
                    dst,
                    left: zero,
                    right: *value,
                });
            }
            Some(role @ PrimitiveRole::IntShr) => {
                let [left, right] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic int shift primitive requires two operands",
                    );
                    return None;
                };
                let scalar = match generic_arguments.as_slice() {
                    [GenericArgument::Type(Type::Scalar(scalar))]
                        if integer_scalar_type(&Type::Scalar(*scalar)).is_some() =>
                    {
                        *scalar
                    }
                    _ => {
                        self.error(
                            "G6005",
                            "generic int shift requires one frozen integer scalar argument",
                        );
                        return None;
                    }
                };
                let expected = Type::Scalar(scalar);
                if self.locals[left.0 as usize].ty != expected
                    || self.locals[right.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U32)
                    || self.locals[dst.0 as usize].ty != expected
                {
                    self.error(
                        "G6005",
                        "generic int shift operands do not match its frozen scalar contract",
                    );
                    return None;
                }
                if scalar == crate::types::ScalarType::I64 {
                    self.instructions.push(MirInstruction::IntShrI64 {
                        dst,
                        left: *left,
                        right: *right,
                    });
                } else {
                    self.instructions.push(MirInstruction::IntIntrinsic {
                        dst,
                        primitive: role,
                        scalar,
                        arguments: vec![*left, *right],
                    });
                }
            }
            Some(role @ PrimitiveRole::IntShl) => {
                let [value, count] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic int shift-left requires a value and count",
                    );
                    return None;
                };
                let scalar = match generic_arguments.as_slice() {
                    [GenericArgument::Type(Type::Scalar(scalar))]
                        if integer_scalar_type(&Type::Scalar(*scalar)).is_some() =>
                    {
                        *scalar
                    }
                    _ => {
                        self.error(
                            "G6005",
                            "generic int shift requires one frozen integer scalar argument",
                        );
                        return None;
                    }
                };
                let expected = Type::Scalar(scalar);
                if self.locals[value.0 as usize].ty != expected
                    || self.locals[count.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U32)
                    || self.locals[dst.0 as usize].ty != expected
                {
                    self.error(
                        "G6005",
                        "generic int shift operands do not match its frozen scalar contract",
                    );
                    return None;
                }
                if scalar == crate::types::ScalarType::I64 {
                    self.instructions.push(MirInstruction::ShlI64 {
                        dst,
                        value: *value,
                        count: *count,
                    });
                } else {
                    self.instructions.push(MirInstruction::IntIntrinsic {
                        dst,
                        primitive: role,
                        scalar,
                        arguments: vec![*value, *count],
                    });
                }
            }
            Some(
                role @ (PrimitiveRole::IntCheckedAdd
                | PrimitiveRole::IntCheckedDiv
                | PrimitiveRole::IntWrappingAdd
                | PrimitiveRole::IntWrappingSub
                | PrimitiveRole::IntWrappingMul
                | PrimitiveRole::IntEqual
                | PrimitiveRole::IntLess
                | PrimitiveRole::IntGreater
                | PrimitiveRole::IntBitAnd
                | PrimitiveRole::IntBitXor
                | PrimitiveRole::IntBitOr),
            ) => {
                let [left, right] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic int primitive requires two operands",
                    );
                    return None;
                };
                let scalar = match generic_arguments.as_slice() {
                    [GenericArgument::Type(Type::Scalar(scalar))]
                        if integer_scalar_type(&Type::Scalar(*scalar)).is_some() =>
                    {
                        *scalar
                    }
                    _ => {
                        self.error(
                            "G6005",
                            "generic int primitive requires one frozen integer scalar argument",
                        );
                        return None;
                    }
                };
                let expected = Type::Scalar(scalar);
                let result = if matches!(
                        role,
                        PrimitiveRole::IntEqual
                            | PrimitiveRole::IntLess
                            | PrimitiveRole::IntGreater
                    ) {
                    Type::Scalar(crate::types::ScalarType::U32)
                } else {
                    expected.clone()
                };
                if self.locals[left.0 as usize].ty != expected
                    || self.locals[right.0 as usize].ty != expected
                    || self.locals[dst.0 as usize].ty != result
                {
                    self.error(
                        "G6005",
                        "generic int primitive operands do not match its frozen scalar contract",
                    );
                    return None;
                }
                if scalar != crate::types::ScalarType::I64 {
                    self.instructions.push(MirInstruction::IntIntrinsic {
                        dst,
                        primitive: role,
                        scalar,
                        arguments: vec![*left, *right],
                    });
                } else {
                self.instructions.push(match role {
                    PrimitiveRole::IntCheckedAdd => MirInstruction::AddI64 {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::IntCheckedDiv => MirInstruction::DivI64 {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::IntWrappingAdd => {
                        MirInstruction::WrappingAddI64 {
                            dst,
                            left: *left,
                            right: *right,
                        }
                    }
                    PrimitiveRole::IntWrappingSub => {
                        MirInstruction::WrappingSubI64 {
                            dst,
                            left: *left,
                            right: *right,
                        }
                    }
                    PrimitiveRole::IntWrappingMul => {
                        MirInstruction::WrappingMulI64 {
                            dst,
                            left: *left,
                            right: *right,
                        }
                    }
                    PrimitiveRole::IntEqual => MirInstruction::IntEqualI64 {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::IntLess => MirInstruction::IntLessI64 {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::IntGreater => MirInstruction::IntGreaterI64 {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::IntBitAnd => MirInstruction::BitAndI64 {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::IntBitXor => MirInstruction::BitXorI64 {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    PrimitiveRole::IntBitOr => MirInstruction::BitOrI64 {
                        dst,
                        left: *left,
                        right: *right,
                    },
                    _ => unreachable!("int primitive role was narrowed above"),
                });
                }
            }
            Some(PrimitiveRole::IntConvertCheckedToI64) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic checked i64 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                {
                    self.error("G6005", "generic checked i64 conversion is only authorized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::Copy { dst, src: *value });
            }
            Some(PrimitiveRole::IntConvertWrappingToI64) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic wrapping i64 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                {
                    self.error("G6005", "generic wrapping i64 conversion is only authorized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::Copy { dst, src: *value });
            }
            Some(PrimitiveRole::IntConvertCheckedToU32) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic checked u32 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U32)
                {
                    self.error("G6005", "generic checked u32 conversion is only authorized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToU32Checked { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertCheckedToUsize) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic checked usize conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Usize)
                {
                    self.error("G6005", "generic checked usize conversion is only authorized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToUsizeChecked { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertCheckedToU8) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic checked u8 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U8)
                {
                    self.error(
                        "G6005",
                        "generic checked u8 conversion is only authorized for frozen i64",
                    );
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToU8Checked { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertCheckedToU16) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic checked u16 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U16)
                {
                    self.error(
                        "G6005",
                        "generic checked u16 conversion is only authorized for frozen i64",
                    );
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToU16Checked { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertCheckedToI16) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic checked i16 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I16)
                {
                    self.error("G6005", "generic checked i16 conversion is only authorized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToI16Checked { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertCheckedToI32) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic checked i32 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I32)
                {
                    self.error(
                        "G6005",
                        "generic checked i32 conversion is only authorized for frozen i64",
                    );
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToI32Checked { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertCheckedToI8) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic checked i8 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I8)
                {
                    self.error("G6005", "generic checked i8 conversion is only authorized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToI8Checked { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertCheckedToU64) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic checked u64 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U64)
                {
                    self.error("G6005", "generic checked u64 conversion is only authorized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToU64Checked { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertCheckedToIsize) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic checked isize conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::Isize)
                {
                    self.error("G6005", "generic checked isize conversion is only authorized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToIsizeChecked { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertCheckedToU128) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic checked u128 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::U128)
                {
                    self.error("G6005", "generic checked u128 conversion is only authorized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToU128Checked { dst, value: *value });
            }
            Some(PrimitiveRole::IntConvertCheckedToI128) => {
                let [value] = arguments.as_slice() else {
                    self.error(
                        "G6005",
                        "generic checked i128 conversion requires one operand",
                    );
                    return None;
                };
                if generic_arguments.as_slice()
                    != [GenericArgument::Type(Type::Scalar(
                        crate::types::ScalarType::I64,
                    ))]
                    || self.locals[value.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I64)
                    || self.locals[dst.0 as usize].ty
                        != Type::Scalar(crate::types::ScalarType::I128)
                {
                    self.error("G6005", "generic checked i128 conversion is only authorized for frozen i64");
                    return None;
                }
                self.instructions
                    .push(MirInstruction::I64ToI128Checked { dst, value: *value });
            }
            Some(role @ (PrimitiveRole::ArrayGetBorrowShared | PrimitiveRole::ArrayEmpty | PrimitiveRole::ArrayPushMove)) => {
                let element_types = generic_arguments
                    .iter()
                    .filter_map(|argument| match argument {
                        GenericArgument::Type(element_type) => {
                            Some(element_type.clone())
                        }
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                let [element_type] = element_types.as_slice() else {
                    self.error(
                        "G6005",
                        "Array primitive requires exactly one frozen element type argument",
                    );
                    return None;
                };
                let array = Type::Array(Box::new(element_type.clone()));
                // A shared array read may be satisfied by a unique borrow.
                // The latter is reborrowed as shared for the duration of the
                // primitive operation, just like an ordinary `&mut T` can be
                // read through `&T` source APIs.
                let shared_array = |ty: &Type| {
                    matches!(ty, Type::Reference {
                    mutability: crate::types::Mutability::Shared,
                    referent,
                    ..
                } if referent.as_ref() == &array)
                    || matches!(ty, Type::Reference {
                    mutability: crate::types::Mutability::Unique,
                    referent,
                    ..
                } if referent.as_ref() == &array)
                };
                let unique_array = |ty: &Type| {
                    matches!(ty, Type::Reference {
                    mutability: crate::types::Mutability::Unique,
                    referent,
                    ..
                } if referent.as_ref() == &array)
                };
                let usize = Type::Scalar(crate::types::ScalarType::Usize);
                let unit = Type::Unit;
                let result = &self.locals[dst.0 as usize].ty;
                match role {
                    PrimitiveRole::ArrayGetBorrowShared => {
                        let [value, index] = arguments.as_slice() else {
                            self.error("G6005", "Array borrow primitive requires borrowed Array and index operands");
                            return None;
                        };
                        if !shared_array(&self.locals[value.0 as usize].ty)
                            || self.locals[index.0 as usize].ty != usize
                        {
                            self.error("G6005", "Array borrow primitive ABI does not match manifest contract");
                            return None;
                        }
                        self.instructions.push(MirInstruction::ArrayGetBorrowShared {
                            dst,
                            value: *value,
                            index: *index,
                            element_type: element_type.clone(),
                        });
                    }
                    PrimitiveRole::ArrayEmpty => {
                        if !arguments.is_empty() || *result != array {
                            self.error("G6005", "ArrayEmpty primitive ABI does not match manifest contract");
                            return None;
                        }
                        self.instructions.push(MirInstruction::ArrayEmpty {
                            dst,
                            element_type: element_type.clone(),
                        });
                    }
                    PrimitiveRole::ArrayPushMove => {
                        let [value, item] = arguments.as_slice() else {
                            self.error("G6005", "ArrayPushMove requires uniquely borrowed Array and item operands");
                            return None;
                        };
                        if !unique_array(&self.locals[value.0 as usize].ty)
                            || self.locals[item.0 as usize].ty != *element_type
                            || *result != unit
                        {
                            self.error("G6005", "ArrayPushMove primitive ABI does not match manifest contract");
                            return None;
                        }
                        self.instructions.push(MirInstruction::ArrayPushMove {
                            value: *value,
                            item: *item,
                            element_type: element_type.clone(),
                        });
                        self.instructions.push(MirInstruction::ConstUnit { dst });
                    }
                    _ => unreachable!("Array role was narrowed above"),
                }
            }
            Some(PrimitiveRole::Memory(primitive)) => {
                let types = generic_arguments.iter().filter_map(|argument| {
                    match argument { GenericArgument::Type(ty) => Some(ty.clone()), _ => None }
                }).collect::<Vec<_>>();
                if primitive.instantiated_signature(&types).is_none() {
                    self.error("G6005", "memory primitive has the wrong type arity");
                    return None;
                }
                for ty in &types { self.register_nominal_copy_descriptors(ty); }
                self.instructions.push(MirInstruction::MemoryIntrinsic { dst, primitive, types, arguments });
            }
            Some(PrimitiveRole::Float(primitive)) => {
                if !generic_arguments.is_empty() {
                    self.error(
                        "G6005",
                        "floating runtime primitive may not carry generic arguments",
                    );
                    return None;
                }
                self.instructions.push(MirInstruction::FloatIntrinsic {
                    dst,
                    primitive,
                    arguments,
                });
            }
            None => match host_import {
                Some(import) => {
                    let Some(crate::ElaboratedHeader::Callable(signature)) = self.signatures
                        .and_then(|signatures| signatures.definitions.get(&callee)) else {
                        self.error("G6005", "host call lacks its frozen source declaration contract");
                        return None;
                    };
                    let source_contract = crate::signature::host_contract_fingerprint(callee, signature);
                    let parameters = arguments.iter()
                        .map(|argument| self.locals[argument.0 as usize].ty.clone()).collect::<Vec<_>>();
                    let result = self.locals[dst.0 as usize].ty.clone();
                    let roots = parameters.iter().chain(std::iter::once(&result)).cloned().collect::<Vec<_>>();
                    let native_nominals = match native_contract_nominals(&roots, self.signatures.expect("host declaration checked above")) {
                        Ok(nominals) => nominals,
                        Err(message) => { self.error("G6005", &message); return None; }
                    };
                    for ty in roots.iter().chain(&native_nominals) {
                        self.register_nominal_copy_descriptors(ty);
                    }
                    self.instructions.push(MirInstruction::HostCall {
                        dst, capability: import.capability, symbol: import.symbol,
                        source_contract, parameters, result, resident_operations: vec![], arguments,
                    });
                }
                None => self.instructions.push(MirInstruction::Call {
                    dst,
                    callee,
                    generic_arguments,
                    trait_instance: None,
                    arguments,
                }),
            },
        }
        Some(())
    }
    fn alloc(&mut self, ty: Type, source: CoreId) -> MirLocal {
        self.register_nominal_copy_descriptors(&ty);
        self.locals.allocate(MirLocalDecl { ty, source })
    }
    /// Freeze every declaration-owned nominal layout reachable from a runtime
    /// type before MIR erases the elaborated interface. Failure to instantiate
    /// a layout intentionally leaves no descriptor, making later `Copy`
    /// validation fail closed for that nominal identity.
    pub(crate) fn register_nominal_copy_descriptors(&mut self, ty: &Type) {
        match ty {
            Type::Tuple(elements) => {
                for element in elements {
                    self.register_nominal_copy_descriptors(element);
                }
            }
            Type::Array(element) => self.register_nominal_copy_descriptors(element),
            // References are independently duplicable/affine according to
            // their mutability; the referent is not inline storage.
            Type::Reference { .. } | Type::RawPointer { .. } => {}
            Type::Callable {
                parameters,
                result,
                effects,
                ..
            } => {
                for parameter in parameters {
                    self.register_nominal_copy_descriptors(parameter);
                }
                self.register_nominal_copy_descriptors(result);
                for effect in &effects.effects {
                    for argument in &effect.arguments {
                        if let GenericArgument::Type(argument) = argument {
                            self.register_nominal_copy_descriptors(argument);
                        }
                    }
                }
            }
            Type::Nominal {
                definition,
                arguments,
            } => {
                let key = (*definition, arguments.clone());
                if self.nominal_copy_descriptors.iter().any(|descriptor| {
                    descriptor.definition == *definition && descriptor.arguments == *arguments
                }) || self.building_nominal_copy_descriptors.contains(&key)
                {
                    return;
                }
                let Some(signatures) = self.signatures else {
                    return;
                };
                let variants = match signatures.definitions.get(definition) {
                    Some(ElaboratedHeader::Nominal {
                        layout: ElaboratedNominalLayout::Struct(_),
                        ..
                    }) => signatures
                        .instantiate_struct_fields_generic(*definition, arguments)
                        .ok()
                        .map(|fields| vec![fields.into_iter().map(|field| field.ty).collect()]),
                    Some(ElaboratedHeader::Nominal {
                        layout: ElaboratedNominalLayout::Enum(variants),
                        ..
                    }) => variants
                        .iter()
                        .enumerate()
                        .map(|(index, _)| {
                            signatures
                                .instantiate_enum_fields_generic(
                                    *definition,
                                    arguments,
                                    index as u32,
                                )
                                .ok()
                                .map(|fields| {
                                    fields.into_iter().map(|field| field.ty).collect::<Vec<_>>()
                                })
                        })
                        .collect::<Option<Vec<_>>>(),
                    _ => None,
                }
                // The older general layout query exposes only type-valued
                // substitutions. Copy descriptors must also cover nominals
                // whose identity is parameterized by lifetimes, effects, or
                // structural constants, so fall back to the frozen raw
                // layout with the complete generic-argument substitution.
                .or_else(|| {
                    signatures.definitions.get(definition).and_then(|header| {
                        let ElaboratedHeader::Nominal { layout, .. } = header else {
                            return None;
                        };
                        instantiate_nominal_copy_layout(layout, arguments)
                    })
                });
                let Some(variants) = variants else {
                    return;
                };
                let Some(source_contract) = signatures.definitions.get(definition)
                    .and_then(|header| crate::signature::nominal_contract_fingerprint(*definition, header)) else {
                    return;
                };
                self.building_nominal_copy_descriptors.push(key);
                for variant in &variants {
                    for field in variant {
                        self.register_nominal_copy_descriptors(field);
                    }
                }
                self.building_nominal_copy_descriptors.pop();
                self.nominal_copy_descriptors
                    .push(MirNominalCopyDescriptor {
                        definition: *definition,
                        source_contract,
                        is_enum: matches!(signatures.definitions.get(definition),
                            Some(ElaboratedHeader::Nominal { layout: ElaboratedNominalLayout::Enum(_), .. })),
                        arguments: arguments.clone(),
                        variants,
                    });
            }
            _ => {}
        }
    }

    fn error(&mut self, code: &'static str, message: &str) {
        self.diagnostics.push(MirDiagnostic { code, message: message.into() });
    }
}
