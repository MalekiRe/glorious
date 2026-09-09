//! Resumption provenance follows resident values, including structural fields.
//!
//! This is the verifier's single resumption value domain. A possible token is
//! not permission to invoke it: only an exact, live `Token` supplies a handler
//! identity. Products retain that distinction per field. Opaque memory access,
//! incompatible joins and expired frames retain possible authority without
//! manufacturing an exact identity.

use std::collections::BTreeMap;
use std::sync::Arc;

const MAX_DEPTH: usize = 32;
const MAX_NODES: usize = 4096;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) enum ResumptionValue {
    #[default]
    None,
    Unknown,
    Token(u32),
    Product(Arc<BTreeMap<u32, ResumptionValue>>),
}

impl ResumptionValue {
    pub(super) fn contains(&self) -> bool {
        !matches!(self, Self::None)
    }

    pub(super) fn frame(&self) -> Option<u32> {
        if let Self::Token(frame) = self { Some(*frame) } else { None }
    }

    pub(super) fn opaque(&self) -> Self {
        if self.contains() { Self::Unknown } else { Self::None }
    }

    pub(super) fn product(values: impl IntoIterator<Item = Self>) -> Self {
        Self::fields(values.into_iter().enumerate().filter_map(|(index, value)|
            value.contains().then_some((index as u32, value))).collect())
    }

    fn fields(fields: BTreeMap<u32, Self>) -> Self {
        if fields.is_empty() { return Self::None; }
        let mut nodes = MAX_NODES;
        if !fields.values().all(|value| value.within_budget(MAX_DEPTH - 1, &mut nodes)) {
            return Self::Unknown;
        }
        Self::Product(Arc::new(fields))
    }

    fn within_budget(&self, depth: usize, nodes: &mut usize) -> bool {
        if *nodes == 0 { return false; }
        *nodes -= 1;
        match self {
            Self::Product(fields) => depth > 0
                && fields.values().all(|value| value.within_budget(depth - 1, nodes)),
            _ => true,
        }
    }

    pub(super) fn project(&self, path: &[u32]) -> Self {
        let Some((first, rest)) = path.split_first() else { return self.clone(); };
        match self {
            Self::Product(fields) => fields.get(first).map_or(Self::None, |value| value.project(rest)),
            Self::None => Self::None,
            _ => Self::Unknown,
        }
    }

    pub(super) fn replace(&mut self, path: &[u32], value: Self) {
        if path.len() > MAX_DEPTH {
            *self = if self.contains() || value.contains() { Self::Unknown } else { Self::None };
            return;
        }
        let Some((first, rest)) = path.split_first() else { *self = value; return; };
        match self {
            Self::None | Self::Product(_) => {
                let mut fields = match std::mem::take(self) {
                    Self::Product(fields) => Arc::unwrap_or_clone(fields),
                    _ => BTreeMap::new(),
                };
                let mut field = fields.remove(first).unwrap_or_default();
                field.replace(rest, value);
                if field.contains() { fields.insert(*first, field); }
                *self = Self::fields(fields);
            }
            // Without a represented product layout, a write cannot prove
            // that other possible control-bearing fields disappeared.
            _ => *self = Self::Unknown,
        }
    }

    pub(super) fn take(&mut self, path: &[u32]) -> Self {
        let result = self.project(path);
        self.replace(path, Self::None);
        result
    }

    pub(super) fn expire(&mut self, frame: u32) {
        match self {
            Self::Token(actual) if *actual == frame => *self = Self::Unknown,
            Self::Product(fields) => for value in Arc::make_mut(fields).values_mut() { value.expire(frame); },
            _ => {},
        }
    }

    pub(super) fn join(&self, other: &Self) -> Self {
        if self == other { return self.clone(); }
        match (self, other) {
            (Self::Product(left), Self::Product(right)) => {
                let keys = left.keys().chain(right.keys());
                Self::fields(keys.map(|key| (*key,
                    left.get(key).unwrap_or(&Self::None).join(right.get(key).unwrap_or(&Self::None)))).collect())
            }
            (Self::Product(fields), Self::None) | (Self::None, Self::Product(fields)) =>
                Self::fields(fields.iter().map(|(key, value)| (*key, value.join(&Self::None))).collect()),
            _ => Self::Unknown,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ResumptionValue as Value;

    #[test]
    fn resumption_products_preserve_exact_fields_and_owned_projection() {
        let mut value = Value::product([Value::None,
            Value::product([Value::Token(3), Value::Token(7)])]);
        assert_eq!(value.project(&[0]), Value::None);
        assert_eq!(value.project(&[1, 1]).frame(), Some(7));
        assert_eq!(value.take(&[1, 0]).frame(), Some(3));
        assert_eq!(value.project(&[1, 0]), Value::None);
        assert_eq!(value.project(&[1, 1]).frame(), Some(7));
        value.replace(&[1, 1], Value::None);
        assert_eq!(value, Value::None);
    }

    #[test]
    fn resumption_product_joins_and_expiry_never_invent_authority() {
        let left = Value::product([Value::Token(3), Value::Token(7)]);
        let right = Value::product([Value::Token(4), Value::Token(7)]);
        let mut joined = left.join(&right);
        assert_eq!(joined.project(&[0]), Value::Unknown);
        assert_eq!(joined.project(&[1]).frame(), Some(7));
        joined.expire(7);
        assert_eq!(joined.project(&[1]), Value::Unknown);
        assert!(joined.contains());
        assert_eq!(joined.frame(), None);
        assert_eq!(left.join(&Value::None).project(&[0]), Value::Unknown);
        assert_eq!(left.opaque().project(&[1]), Value::Unknown);
    }

    #[test]
    fn resumption_product_growth_loses_proof_not_possible_contents() {
        let mut value = Value::Token(1);
        for _ in 0..=super::MAX_DEPTH { value = Value::product([value]); }
        assert_eq!(value, Value::Unknown);
        assert_eq!(Value::product((0..=super::MAX_NODES).map(|_| Value::Token(1))), Value::Unknown);
        let mut unknown = Value::None;
        unknown.replace(&vec![0; super::MAX_DEPTH + 1], Value::Token(2));
        assert_eq!(unknown, Value::Unknown);
    }
}
