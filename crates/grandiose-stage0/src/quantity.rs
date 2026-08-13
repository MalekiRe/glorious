//! Quantitative-use interval algebra.
//!
//! This is the one arithmetic used by ordinary values, callable invocation,
//! captured environments, resumptions, and cancellation. It deliberately does
//! not treat destruction as use: zero-use permission is a separate property
//! of a type/evidence relation.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Quantity {
    pub lower: u64,
    /// `None` denotes infinity.
    pub upper: Option<u64>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum QuantityError {
    Overflow,
    EmptyInterval,
}

impl Quantity {
    pub const ZERO: Self = Self {
        lower: 0,
        upper: Some(0),
    };
    pub const ONCE: Self = Self {
        lower: 1,
        upper: Some(1),
    };
    pub const AFFINE: Self = Self {
        lower: 0,
        upper: Some(1),
    };
    pub const UNRESTRICTED: Self = Self {
        lower: 0,
        upper: None,
    };

    pub fn new(lower: u64, upper: Option<u64>) -> Result<Self, QuantityError> {
        if upper.is_some_and(|upper| lower > upper) {
            return Err(QuantityError::EmptyInterval);
        }
        Ok(Self { lower, upper })
    }

    /// Whether `actual` is permitted by this principal interval.
    pub fn contains(self, actual: Self) -> bool {
        self.lower <= actual.lower && upper_leq(actual.upper, self.upper)
    }

    /// Sequencing adds uses on a normal path.
    pub fn sequence(self, other: Self) -> Result<Self, QuantityError> {
        Self::new(
            self.lower
                .checked_add(other.lower)
                .ok_or(QuantityError::Overflow)?,
            upper_add(self.upper, other.upper)?,
        )
    }

    /// Exclusive control-flow joins form an interval hull.
    pub fn branch_hull(self, other: Self) -> Self {
        Self {
            lower: self.lower.min(other.lower),
            upper: upper_max(self.upper, other.upper),
        }
    }

    /// Nested execution/replay multiplies every captured use.
    pub fn multiply(self, other: Self) -> Result<Self, QuantityError> {
        Self::new(
            self.lower
                .checked_mul(other.lower)
                .ok_or(QuantityError::Overflow)?,
            upper_multiply(self.upper, other.upper)?,
        )
    }

    pub fn requires_positive_use(self) -> bool {
        self.lower > 0
    }
}

fn upper_leq(left: Option<u64>, right: Option<u64>) -> bool {
    match (left, right) {
        (_, None) => true,
        (None, Some(_)) => false,
        (Some(left), Some(right)) => left <= right,
    }
}

fn upper_add(left: Option<u64>, right: Option<u64>) -> Result<Option<u64>, QuantityError> {
    match (left, right) {
        (Some(left), Some(right)) => left
            .checked_add(right)
            .map(Some)
            .ok_or(QuantityError::Overflow),
        _ => Ok(None),
    }
}

fn upper_max(left: Option<u64>, right: Option<u64>) -> Option<u64> {
    match (left, right) {
        (Some(left), Some(right)) => Some(left.max(right)),
        _ => None,
    }
}

fn upper_multiply(left: Option<u64>, right: Option<u64>) -> Result<Option<u64>, QuantityError> {
    match (left, right) {
        (Some(left), Some(right)) => left
            .checked_mul(right)
            .map(Some)
            .ok_or(QuantityError::Overflow),
        // Zero repetitions bound even an unrestricted capture to zero.
        (Some(0), _) | (_, Some(0)) => Ok(Some(0)),
        _ => Ok(None),
    }
}
