use super::{Body, I, LlvmError, VmCompare, VmType, layout};
use crate::{
    PrimitiveRole as P,
    runtime_manifest::{FloatBinaryOp, FloatCompareOp, FloatPrimitive, FloatWidth},
};

fn signed(ty: &VmType) -> bool {
    matches!(
        ty,
        VmType::I8 | VmType::I16 | VmType::I32 | VmType::I64 | VmType::I128 | VmType::Isize
    )
}
fn width(ty: &VmType) -> Option<u32> {
    Some(match ty {
        VmType::U8 | VmType::I8 | VmType::Bool => 8,
        VmType::U16 | VmType::I16 => 16,
        VmType::U32 | VmType::I32 | VmType::Char => 32,
        VmType::U64 | VmType::I64 | VmType::Usize | VmType::Isize => 64,
        VmType::U128 | VmType::I128 => 128,
        _ => return None,
    })
}

impl Body<'_, '_> {
    pub(super) fn scalar(&mut self, instruction: &I) -> Result<bool, LlvmError> {
        macro_rules! constant {
            ($dst:expr, $value:expr) => {
                self.store_scalar(*$dst, &$value.to_string())?
            };
        }
        match instruction {
            I::ConstI8 { dst, value } => constant!(dst, value),
            I::ConstU8 { dst, value } => constant!(dst, value),
            I::ConstI16 { dst, value } => constant!(dst, value),
            I::ConstU16 { dst, value } => constant!(dst, value),
            I::ConstI32 { dst, value } => constant!(dst, value),
            I::ConstU32 { dst, value } => constant!(dst, value),
            I::ConstI64 { dst, value } => constant!(dst, value),
            I::ConstU64 { dst, value } => constant!(dst, value),
            I::ConstI128 { dst, value } => constant!(dst, value),
            I::ConstU128 { dst, value } => constant!(dst, value),
            I::ConstIsize { dst, value } => constant!(dst, value),
            I::ConstUsize { dst, value } => constant!(dst, value),
            I::ConstChar { dst, value } => constant!(dst, value),
            I::ConstBool { dst, value } => {
                self.store_scalar(*dst, if *value { "1" } else { "0" })?
            }
            I::ConstF32 { dst, bits } => {
                let value = self.value(format!("bitcast i32 {bits} to float"));
                self.store_scalar(*dst, &value)?;
            }
            I::ConstF64 { dst, bits } => {
                let value = self.value(format!("bitcast i64 {bits} to double"));
                self.store_scalar(*dst, &value)?;
            }
            I::AddI64 { dst, left, right } | I::U32CheckedAdd { dst, left, right } => {
                self.binary(*dst, *left, *right, "add", true)?
            }
            I::SubI64 { dst, left, right } | I::U32CheckedSub { dst, left, right } => {
                self.binary(*dst, *left, *right, "sub", true)?
            }
            I::MulI64 { dst, left, right } | I::U32CheckedMul { dst, left, right } => {
                self.binary(*dst, *left, *right, "mul", true)?
            }
            I::WrappingAddI64 { dst, left, right } | I::U32WrappingAdd { dst, left, right } => {
                self.binary(*dst, *left, *right, "add", false)?
            }
            I::WrappingSubI64 { dst, left, right } | I::U32WrappingSub { dst, left, right } => {
                self.binary(*dst, *left, *right, "sub", false)?
            }
            I::WrappingMulI64 { dst, left, right } | I::U32WrappingMul { dst, left, right } => {
                self.binary(*dst, *left, *right, "mul", false)?
            }
            I::BitAndI64 { dst, left, right }
            | I::BitAndU32 { dst, left, right }
            | I::BitAndU64 { dst, left, right } => {
                self.binary(*dst, *left, *right, "and", false)?
            }
            I::BitOrI64 { dst, left, right } => self.binary(*dst, *left, *right, "or", false)?,
            I::BitXorI64 { dst, left, right } => self.binary(*dst, *left, *right, "xor", false)?,
            I::DivI64 { dst, left, right } | I::U32CheckedDiv { dst, left, right } => {
                self.divide(*dst, *left, *right, false, 2)?
            }
            I::RemI64 { dst, left, right } | I::U32CheckedRem { dst, left, right } => {
                self.divide(*dst, *left, *right, true, 2)?
            }
            I::IntEqualI64 { dst, left, right }
            | I::U32Eq { dst, left, right }
            | I::EqBool { dst, left, right } => {
                self.compare(*dst, *left, *right, VmCompare::Equal)?
            }
            I::NeBool { dst, left, right } => {
                self.compare(*dst, *left, *right, VmCompare::NotEqual)?
            }
            I::IntLessI64 { dst, left, right } | I::U32Lt { dst, left, right } => {
                self.compare(*dst, *left, *right, VmCompare::Less)?
            }
            I::IntGreaterI64 { dst, left, right } => {
                self.compare(*dst, *left, *right, VmCompare::Greater)?
            }
            I::U32Le { dst, left, right } => {
                self.compare(*dst, *left, *right, VmCompare::LessEqual)?
            }
            I::CompareI64 {
                dst,
                left,
                right,
                op,
            }
            | I::CompareU32 {
                dst,
                left,
                right,
                op,
            }
            | I::CompareU64 {
                dst,
                left,
                right,
                op,
            }
            | I::CompareChar {
                dst,
                left,
                right,
                op,
            } => self.compare(*dst, *left, *right, *op)?,
            I::NotBool { dst, value } => {
                let value = self.load(*value)?;
                let result = self.value(format!("xor i8 {value}, 1"));
                self.store_scalar(*dst, &result)?;
            }
            I::BitNotI64 { dst, value } => self.unary(*dst, *value, false)?,
            I::ShlI64 { dst, value, count } => self.shift(*dst, *value, *count, true, false)?,
            I::IntShrI64 { dst, left, right } => self.shift(*dst, *left, *right, false, false)?,
            I::U32CheckedShl { dst, left, right } => {
                self.shift(*dst, *left, *right, true, false)?
            }
            I::U32CheckedShr { dst, left, right } => {
                self.shift(*dst, *left, *right, false, false)?
            }
            I::U32WrappingShl { dst, left, right } => {
                self.shift(*dst, *left, *right, true, true)?
            }
            I::U32WrappingShr { dst, left, right } => {
                self.shift(*dst, *left, *right, false, true)?
            }
            I::U32ToUsize { dst, value } | I::CharToU32 { dst, value } => {
                self.convert(*dst, *value, false)?
            }
            I::UsizeToU32Checked { dst, value }
            | I::I64ToU32Checked { dst, value }
            | I::I64ToUsizeChecked { dst, value }
            | I::I64ToU8Checked { dst, value }
            | I::I64ToU16Checked { dst, value }
            | I::I64ToI8Checked { dst, value }
            | I::I64ToI16Checked { dst, value }
            | I::I64ToI32Checked { dst, value }
            | I::I64ToU64Checked { dst, value }
            | I::I64ToIsizeChecked { dst, value }
            | I::I64ToU128Checked { dst, value }
            | I::I64ToI128Checked { dst, value } => self.convert(*dst, *value, true)?,
            I::I64ToU32Wrapping { dst, value }
            | I::I64ToUsizeWrapping { dst, value }
            | I::I64ToU8Wrapping { dst, value }
            | I::I64ToU16Wrapping { dst, value }
            | I::I64ToI8Wrapping { dst, value }
            | I::I64ToI16Wrapping { dst, value }
            | I::I64ToI32Wrapping { dst, value }
            | I::I64ToU64Wrapping { dst, value }
            | I::I64ToIsizeWrapping { dst, value }
            | I::I64ToU128Wrapping { dst, value }
            | I::I64ToI128Wrapping { dst, value } => self.convert(*dst, *value, false)?,
            I::IntIntrinsic {
                dst,
                primitive,
                arguments,
                ..
            } => self.integer(*dst, *primitive, arguments)?,
            I::AddF64 { dst, left, right } => self.float_binary(*dst, *left, *right, "fadd")?,
            I::SubF64 { dst, left, right } => self.float_binary(*dst, *left, *right, "fsub")?,
            I::MulF64 { dst, left, right } => self.float_binary(*dst, *left, *right, "fmul")?,
            I::DivF64 { dst, left, right } => self.float_binary(*dst, *left, *right, "fdiv")?,
            I::RemF64 { dst, left, right } => self.float_binary(*dst, *left, *right, "frem")?,
            I::CompareF64 {
                dst,
                left,
                right,
                op,
            } => self.float_compare(*dst, *left, *right, *op)?,
            I::FloatIntrinsic {
                dst,
                primitive,
                arguments,
            } => match primitive {
                FloatPrimitive::Binary { operation, .. } => self.float_binary(
                    *dst,
                    arguments[0],
                    arguments[1],
                    match operation {
                        FloatBinaryOp::Add => "fadd",
                        FloatBinaryOp::Sub => "fsub",
                        FloatBinaryOp::Mul => "fmul",
                        FloatBinaryOp::Div => "fdiv",
                        FloatBinaryOp::Rem => "frem",
                    },
                )?,
                FloatPrimitive::Compare { operation, .. } => self.float_compare(
                    *dst,
                    arguments[0],
                    arguments[1],
                    match operation {
                        FloatCompareOp::Eq => VmCompare::Equal,
                        FloatCompareOp::Ne => VmCompare::NotEqual,
                        FloatCompareOp::Lt => VmCompare::Less,
                        FloatCompareOp::Le => VmCompare::LessEqual,
                        FloatCompareOp::Gt => VmCompare::Greater,
                        FloatCompareOp::Ge => VmCompare::GreaterEqual,
                    },
                )?,
                FloatPrimitive::ToBits { width } => {
                    let value = self.load(arguments[0])?;
                    let (from, to) = match width {
                        FloatWidth::F32 => ("float", "i32"),
                        FloatWidth::F64 => ("double", "i64"),
                    };
                    let value = self.value(format!("bitcast {from} {value} to {to}"));
                    self.store_scalar(*dst, &value)?;
                }
                FloatPrimitive::FromBits { width } => {
                    let value = self.load(arguments[0])?;
                    let (from, to) = match width {
                        FloatWidth::F32 => ("i32", "float"),
                        FloatWidth::F64 => ("i64", "double"),
                    };
                    let value = self.value(format!("bitcast {from} {value} to {to}"));
                    self.canonical_float(*dst, &value)?;
                }
                FloatPrimitive::Neg { .. } => {
                    let value = self.load(arguments[0])?;
                    let ty = layout::scalar_ir(&self.function.registers[*dst as usize]).unwrap();
                    let value = self.value(format!("fneg {ty} {value}"));
                    self.canonical_float(*dst, &value)?;
                }
                _ => {
                    return Err(
                        self.unsupported("native float conversion contract is not implemented")
                    );
                }
            },
            _ => return Ok(false),
        }
        Ok(true)
    }

    fn binary(
        &mut self,
        dst: u32,
        left: u32,
        right: u32,
        operation: &str,
        checked: bool,
    ) -> Result<(), LlvmError> {
        let ty = layout::scalar_ir(&self.function.registers[left as usize]).unwrap();
        let left_value = self.load(left)?;
        let right_value = self.load(right)?;
        let value = if checked {
            let name = format!(
                "llvm.{}{}.with.overflow.{ty}",
                if signed(&self.function.registers[left as usize]) {
                    "s"
                } else {
                    "u"
                },
                operation
            );
            self.declarations
                .insert(format!("declare {{ {ty}, i1 }} @{name}({ty}, {ty})"));
            let pair = self.value(format!(
                "call {{ {ty}, i1 }} @{name}({ty} {left_value}, {ty} {right_value})"
            ));
            let overflow = self.value(format!("extractvalue {{ {ty}, i1 }} {pair}, 1"));
            let valid = self.value(format!("xor i1 {overflow}, true"));
            self.guard(&valid, 1);
            self.value(format!("extractvalue {{ {ty}, i1 }} {pair}, 0"))
        } else {
            self.value(format!("{operation} {ty} {left_value}, {right_value}"))
        };
        self.store_scalar(dst, &value)
    }

    fn divide(
        &mut self,
        dst: u32,
        left: u32,
        right: u32,
        remainder: bool,
        zero_fault: u32,
    ) -> Result<(), LlvmError> {
        let ty = self.function.registers[left as usize].clone();
        let ir = layout::scalar_ir(&ty).unwrap();
        let left_value = self.load(left)?;
        let right_value = self.load(right)?;
        let nonzero = self.value(format!("icmp ne {ir} {right_value}, 0"));
        self.guard(&nonzero, zero_fault);
        if signed(&ty) {
            let minimum = if width(&ty) == Some(128) {
                i128::MIN
            } else {
                -(1i128 << (width(&ty).unwrap() - 1))
            };
            let min = self.value(format!("icmp eq {ir} {left_value}, {minimum}"));
            let neg_one = self.value(format!("icmp eq {ir} {right_value}, -1"));
            let overflow = self.value(format!("and i1 {min}, {neg_one}"));
            let valid = self.value(format!("xor i1 {overflow}, true"));
            self.guard(&valid, 1);
        }
        let value = self.value(format!(
            "{}{} {ir} {left_value}, {right_value}",
            if signed(&ty) { "s" } else { "u" },
            if remainder { "rem" } else { "div" }
        ));
        self.store_scalar(dst, &value)
    }

    fn compare(
        &mut self,
        dst: u32,
        left: u32,
        right: u32,
        operation: VmCompare,
    ) -> Result<(), LlvmError> {
        let ty = &self.function.registers[left as usize];
        let ir = layout::scalar_ir(ty).unwrap();
        let sign = if signed(ty) { "s" } else { "u" };
        let predicate = match operation {
            VmCompare::Equal => "eq".into(),
            VmCompare::NotEqual => "ne".into(),
            VmCompare::Less => format!("{sign}lt"),
            VmCompare::LessEqual => format!("{sign}le"),
            VmCompare::Greater => format!("{sign}gt"),
            VmCompare::GreaterEqual => format!("{sign}ge"),
        };
        let left = self.load(left)?;
        let right = self.load(right)?;
        let value = self.value(format!("icmp {predicate} {ir} {left}, {right}"));
        let target = layout::scalar_ir(&self.function.registers[dst as usize]).unwrap();
        let value = self.value(format!("zext i1 {value} to {target}"));
        self.store_scalar(dst, &value)
    }

    fn unary(&mut self, dst: u32, source: u32, negate: bool) -> Result<(), LlvmError> {
        let ir = layout::scalar_ir(&self.function.registers[source as usize]).unwrap();
        let value = self.load(source)?;
        let value = self.value(if negate {
            format!("sub {ir} 0, {value}")
        } else {
            format!("xor {ir} {value}, -1")
        });
        self.store_scalar(dst, &value)
    }

    fn shift(
        &mut self,
        dst: u32,
        source: u32,
        count: u32,
        left: bool,
        wrapping: bool,
    ) -> Result<(), LlvmError> {
        let ty = self.function.registers[source as usize].clone();
        let bits = width(&ty).unwrap();
        let ir = layout::scalar_ir(&ty).unwrap();
        let value = self.load(source)?;
        let mut amount = self.load(count)?;
        if wrapping {
            amount = self.value(format!("and i32 {amount}, {}", bits - 1));
        } else {
            let valid = self.value(format!("icmp ult i32 {amount}, {bits}"));
            self.guard(&valid, 1);
        }
        if bits != 32 {
            amount = self.value(format!(
                "{} i32 {amount} to {ir}",
                if bits > 32 { "zext" } else { "trunc" }
            ));
        }
        let op = if left {
            "shl"
        } else if signed(&ty) {
            "ashr"
        } else {
            "lshr"
        };
        let value = self.value(format!("{op} {ir} {value}, {amount}"));
        self.store_scalar(dst, &value)
    }

    fn convert(&mut self, dst: u32, source: u32, checked: bool) -> Result<(), LlvmError> {
        let from = self.function.registers[source as usize].clone();
        let to = self.function.registers[dst as usize].clone();
        let from_bits = width(&from)
            .ok_or_else(|| self.unsupported("native conversion source is not an integer"))?;
        let to_bits = width(&to)
            .ok_or_else(|| self.unsupported("native conversion result is not an integer"))?;
        let from_ir = layout::scalar_ir(&from).unwrap();
        let to_ir = layout::scalar_ir(&to).unwrap();
        let value = self.load(source)?;
        if checked {
            if signed(&from) && !signed(&to) {
                let valid = self.value(format!("icmp sge {from_ir} {value}, 0"));
                self.guard(&valid, 1);
            }
            if to_bits < from_bits || (to_bits == from_bits && !signed(&from) && signed(&to)) {
                if signed(&to) && signed(&from) {
                    let minimum = -(1i128 << (to_bits - 1));
                    let valid = self.value(format!("icmp sge {from_ir} {value}, {minimum}"));
                    self.guard(&valid, 1);
                }
                let maximum = if signed(&to) {
                    (1u128 << (to_bits - 1)) - 1
                } else if to_bits == 128 {
                    u128::MAX
                } else {
                    (1u128 << to_bits) - 1
                };
                let valid = self.value(format!(
                    "icmp {}le {from_ir} {value}, {maximum}",
                    if signed(&from) && signed(&to) {
                        "s"
                    } else {
                        "u"
                    }
                ));
                self.guard(&valid, 1);
            }
        }
        let result = if from_bits == to_bits {
            value
        } else {
            self.value(format!(
                "{} {from_ir} {value} to {to_ir}",
                if from_bits > to_bits {
                    "trunc"
                } else if signed(&from) {
                    "sext"
                } else {
                    "zext"
                }
            ))
        };
        self.store_scalar(dst, &result)
    }

    fn integer(&mut self, dst: u32, primitive: P, arguments: &[u32]) -> Result<(), LlvmError> {
        match primitive {
            P::IntCheckedAdd => self.binary(dst, arguments[0], arguments[1], "add", true),
            P::IntCheckedDiv => self.divide(dst, arguments[0], arguments[1], false, 1),
            P::IntWrappingAdd => self.binary(dst, arguments[0], arguments[1], "add", false),
            P::IntWrappingSub => self.binary(dst, arguments[0], arguments[1], "sub", false),
            P::IntWrappingMul => self.binary(dst, arguments[0], arguments[1], "mul", false),
            P::IntBitAnd => self.binary(dst, arguments[0], arguments[1], "and", false),
            P::IntBitOr => self.binary(dst, arguments[0], arguments[1], "or", false),
            P::IntBitXor => self.binary(dst, arguments[0], arguments[1], "xor", false),
            P::IntBitNot => self.unary(dst, arguments[0], false),
            P::IntWrappingNeg => self.unary(dst, arguments[0], true),
            P::IntShl => self.shift(dst, arguments[0], arguments[1], true, false),
            P::IntShr => self.shift(dst, arguments[0], arguments[1], false, false),
            P::IntEqual => self.compare(dst, arguments[0], arguments[1], VmCompare::Equal),
            P::IntLess => self.compare(dst, arguments[0], arguments[1], VmCompare::Less),
            P::IntGreater => self.compare(dst, arguments[0], arguments[1], VmCompare::Greater),
            P::IntConvertCheckedToI64
            | P::IntConvertCheckedToU32
            | P::IntConvertCheckedToUsize
            | P::IntConvertCheckedToU8
            | P::IntConvertCheckedToU16
            | P::IntConvertCheckedToI8
            | P::IntConvertCheckedToI16
            | P::IntConvertCheckedToI32
            | P::IntConvertCheckedToU64
            | P::IntConvertCheckedToIsize
            | P::IntConvertCheckedToU128
            | P::IntConvertCheckedToI128 => self.convert(dst, arguments[0], true),
            P::IntConvertWrappingToI64
            | P::IntConvertWrappingToU32
            | P::IntConvertWrappingToUsize
            | P::IntConvertWrappingToU8
            | P::IntConvertWrappingToU16
            | P::IntConvertWrappingToI8
            | P::IntConvertWrappingToI16
            | P::IntConvertWrappingToI32
            | P::IntConvertWrappingToU64
            | P::IntConvertWrappingToIsize
            | P::IntConvertWrappingToU128
            | P::IntConvertWrappingToI128 => self.convert(dst, arguments[0], false),
            _ => Err(self.unsupported("native integer primitive contract is not implemented")),
        }
    }

    fn float_binary(&mut self, dst: u32, left: u32, right: u32, op: &str) -> Result<(), LlvmError> {
        let ty = layout::scalar_ir(&self.function.registers[dst as usize]).unwrap();
        let suffix = if ty == "float" { "f32" } else { "f64" };
        let left = self.load(left)?;
        let right = self.load(right)?;
        let name = format!("llvm.experimental.constrained.{op}.{suffix}");
        self.declarations.insert(format!(
            "declare {ty} @{name}({ty}, {ty}, metadata, metadata)"
        ));
        let value = self.value(format!("call {ty} @{name}({ty} {left}, {ty} {right}, metadata !\"round.tonearest\", metadata !\"fpexcept.ignore\")"));
        self.canonical_float(dst, &value)
    }
    fn canonical_float(&mut self, dst: u32, value: &str) -> Result<(), LlvmError> {
        let ty = layout::scalar_ir(&self.function.registers[dst as usize]).unwrap();
        let (int, bits) = if ty == "float" {
            ("i32", 0x7fc00000u64)
        } else {
            ("i64", 0x7ff8000000000000u64)
        };
        let unordered = self.value(format!("fcmp uno {ty} {value}, {value}"));
        let canonical = self.value(format!("bitcast {int} {bits} to {ty}"));
        let result = self.value(format!(
            "select i1 {unordered}, {ty} {canonical}, {ty} {value}"
        ));
        self.store_scalar(dst, &result)
    }
    fn float_compare(
        &mut self,
        dst: u32,
        left: u32,
        right: u32,
        operation: VmCompare,
    ) -> Result<(), LlvmError> {
        let ty = layout::scalar_ir(&self.function.registers[left as usize]).unwrap();
        let predicate = match operation {
            VmCompare::Equal => "oeq",
            VmCompare::NotEqual => "une",
            VmCompare::Less => "olt",
            VmCompare::LessEqual => "ole",
            VmCompare::Greater => "ogt",
            VmCompare::GreaterEqual => "oge",
        };
        let left = self.load(left)?;
        let right = self.load(right)?;
        let value = self.value(format!("fcmp {predicate} {ty} {left}, {right}"));
        let to = layout::scalar_ir(&self.function.registers[dst as usize]).unwrap();
        let value = self.value(format!("zext i1 {value} to {to}"));
        self.store_scalar(dst, &value)
    }
}
