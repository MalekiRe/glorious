//! Checked structural integer evaluation shared by const-generic domains.
//!
//! Target-sized values use the supplied target width, never the compiler
//! host's `usize`. This is a normalization kernel, not permission to evaluate
//! arbitrary source functions during compilation.

use super::{ConstKind, GenericArgument, ScalarType};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IntegerConstError {
    NonIntegerKind,
    InvalidTargetWidth,
    KindMismatch,
    Overflow,
    DivisionByZero,
    NegativeArrayLength,
    ResourceLimit,
    InvalidLiteral,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum IntegerConstOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

/// Canonical mathematical value, retaining its exact declared integer kind.
/// Sign/magnitude can represent both `i128::MIN` and `u128::MAX` without
/// lossy casts. Private fields exclude out-of-range values and negative zero.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct IntegerConst {
    scalar: ScalarType,
    negative: bool,
    magnitude: u128,
}

fn domain(scalar: ScalarType, pointer_bits: u32) -> Result<(u32, bool), IntegerConstError> {
    if !matches!(pointer_bits, 32 | 64) {
        return Err(IntegerConstError::InvalidTargetWidth);
    }
    use ScalarType::*;
    Ok(match scalar {
        U8 => (8, false),
        U16 => (16, false),
        U32 => (32, false),
        U64 => (64, false),
        U128 => (128, false),
        I8 => (8, true),
        I16 => (16, true),
        I32 => (32, true),
        I64 => (64, true),
        I128 => (128, true),
        Usize => (pointer_bits, false),
        Isize => (pointer_bits, true),
        _ => return Err(IntegerConstError::NonIntegerKind),
    })
}

impl IntegerConst {
    pub fn kind(self) -> ConstKind {
        match self.scalar {
            ScalarType::U8 => ConstKind::U8,
            ScalarType::U16 => ConstKind::U16,
            ScalarType::U32 => ConstKind::U32,
            ScalarType::U64 => ConstKind::U64,
            ScalarType::U128 => ConstKind::U128,
            ScalarType::Usize => ConstKind::Usize,
            ScalarType::I8 => ConstKind::I8,
            ScalarType::I16 => ConstKind::I16,
            ScalarType::I32 => ConstKind::I32,
            ScalarType::I64 => ConstKind::I64,
            ScalarType::I128 => ConstKind::I128,
            ScalarType::Isize => ConstKind::Isize,
            _ => unreachable!("IntegerConst constructors admit only integer scalars"),
        }
    }

    /// Extract only an actual u32-domain constant, never a same-magnitude
    /// value from another const kind.
    pub fn as_u32(self) -> Option<u32> {
        (self.scalar == ScalarType::U32).then_some(self.magnitude as u32)
    }

    /// One framed identity for every integer kind and mathematical value.
    /// There is no alternate u32-only encoding within this schema.
    pub fn canonical_bytes(self) -> [u8; 18] {
        let mut bytes = [0; 18];
        bytes[0] = self.kind().tag();
        bytes[1] = u8::from(self.negative);
        bytes[2..].copy_from_slice(&self.magnitude.to_le_bytes());
        bytes
    }

    /// Elaborate an unsigned literal token at its selected integer width.
    /// `negative` is supplied by the enclosing immediate unary negation, so
    /// signed minima never require an out-of-range positive intermediate.
    /// This does not apply a numeric default or accept a sign/suffix in the
    /// token. The bootstrap lexer admits one separator after a radix prefix;
    /// retain that spelling here as well as separators between digits.
    pub fn from_literal(
        scalar: ScalarType,
        token: &str,
        negative: bool,
        pointer_bits: u32,
    ) -> Result<Self, IntegerConstError> {
        domain(scalar, pointer_bits)?;
        let (radix, digits) = if let Some(digits) = token.strip_prefix("0b") {
            (2u128, digits.strip_prefix('_').unwrap_or(digits))
        } else if let Some(digits) = token.strip_prefix("0o") {
            (8, digits.strip_prefix('_').unwrap_or(digits))
        } else if let Some(digits) = token.strip_prefix("0x") {
            (16, digits.strip_prefix('_').unwrap_or(digits))
        } else {
            (10, token)
        };
        let mut magnitude = 0u128;
        let mut previous_digit = false;
        let mut overflow = false;
        for byte in digits.bytes() {
            if byte == b'_' {
                if !previous_digit {
                    return Err(IntegerConstError::InvalidLiteral);
                }
                previous_digit = false;
                continue;
            }
            let digit = match byte {
                b'0'..=b'9' => byte - b'0',
                b'a'..=b'f' => byte - b'a' + 10,
                b'A'..=b'F' => byte - b'A' + 10,
                _ => return Err(IntegerConstError::InvalidLiteral),
            } as u128;
            if digit >= radix {
                return Err(IntegerConstError::InvalidLiteral);
            }
            previous_digit = true;
            if !overflow {
                match magnitude.checked_mul(radix).and_then(|value| value.checked_add(digit)) {
                    Some(value) => magnitude = value,
                    None => overflow = true,
                }
            }
        }
        if !previous_digit {
            return Err(IntegerConstError::InvalidLiteral);
        }
        if overflow {
            return Err(IntegerConstError::Overflow);
        }
        Self::new(scalar, negative, magnitude, pointer_bits)
    }

    pub fn new(
        scalar: ScalarType,
        negative: bool,
        magnitude: u128,
        pointer_bits: u32,
    ) -> Result<Self, IntegerConstError> {
        let (bits, signed) = domain(scalar, pointer_bits)?;
        let negative = negative && magnitude != 0;
        let maximum = if signed {
            (1u128 << (bits - 1)) - u128::from(!negative)
        } else if bits == 128 {
            u128::MAX
        } else {
            (1u128 << bits) - 1
        };
        if (negative && !signed) || magnitude > maximum {
            return Err(IntegerConstError::Overflow);
        }
        Ok(Self {
            scalar,
            negative,
            magnitude,
        })
    }

    pub fn scalar(self) -> ScalarType {
        self.scalar
    }
    pub fn is_negative(self) -> bool {
        self.negative
    }
    pub fn magnitude(self) -> u128 {
        self.magnitude
    }

    fn validate(self, pointer_bits: u32) -> Result<(), IntegerConstError> {
        Self::new(self.scalar, self.negative, self.magnitude, pointer_bits).map(|_| ())
    }

    fn signed(self) -> i128 {
        if self.negative {
            if self.magnitude == 1u128 << 127 {
                i128::MIN
            } else {
                -(self.magnitude as i128)
            }
        } else {
            self.magnitude as i128
        }
    }

    pub fn checked_neg(self, pointer_bits: u32) -> Result<Self, IntegerConstError> {
        self.validate(pointer_bits)?;
        Self::new(self.scalar, !self.negative, self.magnitude, pointer_bits)
    }

    pub fn checked(
        self,
        op: IntegerConstOp,
        right: Self,
        pointer_bits: u32,
    ) -> Result<Self, IntegerConstError> {
        self.validate(pointer_bits)?;
        right.validate(pointer_bits)?;
        if self.scalar != right.scalar {
            return Err(IntegerConstError::KindMismatch);
        }
        if matches!(op, IntegerConstOp::Div | IntegerConstOp::Rem) && right.magnitude == 0 {
            return Err(IntegerConstError::DivisionByZero);
        }
        let (_, signed) = domain(self.scalar, pointer_bits)?;
        let (negative, magnitude) = if signed {
            let (left, right) = (self.signed(), right.signed());
            let result = match op {
                IntegerConstOp::Add => left.checked_add(right),
                IntegerConstOp::Sub => left.checked_sub(right),
                IntegerConstOp::Mul => left.checked_mul(right),
                IntegerConstOp::Div => left.checked_div(right),
                IntegerConstOp::Rem => left.checked_rem(right),
            }
            .ok_or(IntegerConstError::Overflow)?;
            // MIN / -1 and MIN % -1 are overflow at the declared width,
            // even when evaluating a narrower kind in the wider host domain.
            if matches!(op, IntegerConstOp::Div | IntegerConstOp::Rem) && right == -1 {
                Self::new(self.scalar, false, left.unsigned_abs(), pointer_bits)?;
            }
            (result < 0, result.unsigned_abs())
        } else {
            let (left, right) = (self.magnitude, right.magnitude);
            let result = match op {
                IntegerConstOp::Add => left.checked_add(right),
                IntegerConstOp::Sub => left.checked_sub(right),
                IntegerConstOp::Mul => left.checked_mul(right),
                IntegerConstOp::Div => left.checked_div(right),
                IntegerConstOp::Rem => left.checked_rem(right),
            }
            .ok_or(IntegerConstError::Overflow)?;
            (false, result)
        };
        Self::new(self.scalar, negative, magnitude, pointer_bits)
    }

    /// A length is a nonnegative integer representable by the target's index
    /// size. Element layout multiplication is a separate checked operation.
    pub fn array_length(self, pointer_bits: u32) -> Result<u64, IntegerConstError> {
        self.validate(pointer_bits)?;
        if self.negative {
            return Err(IntegerConstError::NegativeArrayLength);
        }
        Self::new(ScalarType::Usize, false, self.magnitude, pointer_bits)?;
        u64::try_from(self.magnitude).map_err(|_| IntegerConstError::Overflow)
    }
}

impl From<u32> for IntegerConst {
    fn from(value: u32) -> Self {
        Self { scalar: ScalarType::U32, negative: false, magnitude: value.into() }
    }
}

impl std::fmt::Display for IntegerConst {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.negative { formatter.write_str("-")?; }
        write!(formatter, "{}", self.magnitude)
    }
}

/// Structural terms cannot invoke functions or erase the kind of a binder.
/// Normalization folds only closed arithmetic; it does not cancel symbolic
/// subexpressions whose eventual evaluation may overflow.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum IntegerConstExpr {
    Literal(IntegerConst),
    Param {
        index: u32,
        scalar: ScalarType,
    },
    Neg(Box<Self>),
    Binary {
        op: IntegerConstOp,
        left: Box<Self>,
        right: Box<Self>,
    },
}

impl IntegerConstExpr {
    pub fn binary(op: IntegerConstOp, left: Box<Self>, right: Box<Self>) -> Self {
        Self::Binary { op, left, right }
    }
    /// Stage 0's target is the 64-bit VM. Normalization is explicitly bounded
    /// and retains the original declared scalar kind throughout arithmetic.
    pub fn normalized(&self) -> Result<Self, IntegerConstError> {
        self.normalize(64, &mut 1024)
    }

    pub fn scalar(&self) -> Result<ScalarType, IntegerConstError> {
        self.normalize_inner(64, &mut 1024, 0, None).map(|(_, scalar)| scalar)
    }

    pub(crate) fn from_argument(argument: &GenericArgument) -> Result<Self, IntegerConstError> {
        Ok(match argument {
            GenericArgument::ConstInteger(value) => Self::Literal(*value),
            GenericArgument::ConstIntegerExpr(value) => value.clone(),
            GenericArgument::ConstGeneric { index, kind } => Self::Param {
                index: *index,
                scalar: kind.integer_scalar().ok_or(IntegerConstError::NonIntegerKind)?,
            },
            _ => return Err(IntegerConstError::KindMismatch),
        })
    }

    /// Mixed-kind generic slots keep their original indices. A type/row/
    /// lifetime argument is rejected if an integer term actually references
    /// it; no placeholder value or synthetic const binder is introduced.
    pub fn substitute_arguments(&self, arguments: &[GenericArgument]) -> Result<Self, IntegerConstError> {
        self.substitute_with(&|index| arguments.get(index as usize).map(Self::from_argument).transpose(), 64, &mut 1024)
    }

    pub(crate) fn substitute_with(
        &self,
        lookup: &dyn Fn(u32) -> Result<Option<Self>, IntegerConstError>,
        pointer_bits: u32,
        budget: &mut u32,
    ) -> Result<Self, IntegerConstError> {
        self.normalize_inner(pointer_bits, budget, 0, Some(lookup)).map(|(term, _)| term)
    }

    pub(crate) fn encode(&self, output: &mut Vec<u8>) {
        match self {
            Self::Literal(value) => {
                output.push(0);
                output.extend_from_slice(&value.canonical_bytes());
            }
            Self::Param { index, scalar } => {
                output.push(1);
                output.push(ConstKind::from_integer_scalar(*scalar).map(|kind| kind.tag()).unwrap_or(255));
                output.extend_from_slice(&index.to_le_bytes());
            }
            Self::Neg(value) => { output.push(7); value.encode(output); }
            Self::Binary { op, left, right } => {
                output.push(match op {
                    IntegerConstOp::Add => 2, IntegerConstOp::Sub => 3,
                    IntegerConstOp::Mul => 4, IntegerConstOp::Div => 5, IntegerConstOp::Rem => 6,
                });
                left.encode(output);
                right.encode(output);
            }
        }
    }

    pub fn normalize(
        &self,
        pointer_bits: u32,
        budget: &mut u32,
    ) -> Result<Self, IntegerConstError> {
        self.normalize_inner(pointer_bits, budget, 0, None)
            .map(|(term, _)| term)
    }

    /// Simultaneous substitution: binders inside an argument belong to the
    /// argument's scope and are not recursively substituted by the same map.
    pub fn substitute(
        &self,
        arguments: &[Self],
        pointer_bits: u32,
        budget: &mut u32,
    ) -> Result<Self, IntegerConstError> {
        self.substitute_with(&|index| Ok(arguments.get(index as usize).cloned()), pointer_bits, budget)
    }

    fn normalize_inner(
        &self,
        pointer_bits: u32,
        budget: &mut u32,
        depth: u32,
        arguments: Option<&dyn Fn(u32) -> Result<Option<Self>, IntegerConstError>>,
    ) -> Result<(Self, ScalarType), IntegerConstError> {
        // A node budget alone does not protect the Rust stack against one
        // deeply nested untrusted term. Both limits are explicit failures.
        if depth >= 128 || *budget == 0 {
            return Err(IntegerConstError::ResourceLimit);
        }
        *budget -= 1;
        match self {
            Self::Literal(value) => {
                value.validate(pointer_bits)?;
                Ok((Self::Literal(*value), value.scalar))
            }
            Self::Param { index, scalar } => {
                domain(*scalar, pointer_bits)?;
                if let Some(argument) = arguments.map(|lookup| lookup(*index)).transpose()?.flatten() {
                    let (term, kind) =
                        argument.normalize_inner(pointer_bits, budget, depth + 1, None)?;
                    if kind != *scalar {
                        return Err(IntegerConstError::KindMismatch);
                    }
                    Ok((term, kind))
                } else {
                    Ok((self.clone(), *scalar))
                }
            }
            Self::Neg(value) => {
                let (value, scalar) =
                    value.normalize_inner(pointer_bits, budget, depth + 1, arguments)?;
                let value = match value {
                    Self::Literal(value) => Self::Literal(value.checked_neg(pointer_bits)?),
                    value => Self::Neg(Box::new(value)),
                };
                Ok((value, scalar))
            }
            Self::Binary { op, left, right } => {
                let (mut left, scalar) =
                    left.normalize_inner(pointer_bits, budget, depth + 1, arguments)?;
                let (mut right, right_scalar) =
                    right.normalize_inner(pointer_bits, budget, depth + 1, arguments)?;
                if scalar != right_scalar {
                    return Err(IntegerConstError::KindMismatch);
                }
                if matches!(op, IntegerConstOp::Div | IntegerConstOp::Rem)
                    && matches!(&right, Self::Literal(value) if value.magnitude == 0)
                {
                    return Err(IntegerConstError::DivisionByZero);
                }
                if let (Self::Literal(left), Self::Literal(right)) = (&left, &right) {
                    return Ok((
                        Self::Literal(left.checked(*op, *right, pointer_bits)?),
                        scalar,
                    ));
                }
                if matches!(op, IntegerConstOp::Add | IntegerConstOp::Mul) && right < left {
                    std::mem::swap(&mut left, &mut right);
                }
                Ok((
                    Self::Binary {
                        op: *op,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    scalar,
                ))
            }
        }
    }
}
