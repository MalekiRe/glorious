//! Resumption provenance follows resident values, including structural fields.
//!
//! This is the verifier's single resumption value domain. A possible token is
//! not permission to invoke it: only an exact, live `Token` supplies a handler
//! identity. Products retain that distinction per field. Opaque memory access,
//! incompatible joins retain possible authority without manufacturing an exact
//! identity. Proven frame expiry retains non-invocable control contents so
//! releasing a dead handle cannot be confused with canceling a live branch.

use std::collections::BTreeMap;
use std::sync::Arc;

const MAX_DEPTH: usize = 32;
const MAX_NODES: usize = 4096;

/// A capability supplied by the caller, in the current function's input
/// namespace. It is neither a local handler id nor an unknown live token.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct InputPath {
    pub(super) input: u32,
    pub(super) fields: Vec<u32>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) enum ResumptionValue {
    #[default]
    None,
    Unknown,
    /// Possible control bytes whose exact owner was proved to have ended.
    /// They remain forbidden to escape or invoke, but own no live branch.
    Expired,
    Token(u32),
    Input(InputPath),
    /// A single-use invocation view; even an ordinary callable view may not
    /// become an owned value, escape its activation, or be source-copied.
    Prepared(Arc<ResumptionValue>),
    Product(Arc<BTreeMap<u32, ResumptionValue>>),
}

impl ResumptionValue {
    /// Source copying does not retain an owned continuation capability.
    /// A shared reference copies only its handle, not the control resident
    /// behind it. Structural values preserve that distinction per field.
    pub(super) fn permits_source_copy(&self, ty: &super::VmType, layouts: &[super::VmNominalCopyDescriptor]) -> bool {
        fn visit(value: &ResumptionValue, ty: &super::VmType,
            layouts: &[super::VmNominalCopyDescriptor], depth: usize, nodes: &mut usize,
        ) -> bool {
            use super::VmType;
            if matches!(value, ResumptionValue::Prepared(_)) { return false; }
            if !value.contains() { return true; }
            if depth >= MAX_DEPTH || *nodes == 0 { return false; }
            *nodes -= 1;
            match ty {
                VmType::Reference { unique, .. } => !*unique,
                VmType::Tuple(fields) => fields.iter().enumerate().all(|(index, ty)|
                    visit(&value.project(&[index as u32]), ty, layouts, depth + 1, nodes)),
                VmType::FixedArray { element, length } if *length <= MAX_NODES as u64 =>
                    (0..*length).all(|index| visit(&value.project(&[index as u32]), element, layouts, depth + 1, nodes)),
                VmType::Nominal { definition, arguments } => layouts.iter().find(|layout|
                    layout.definition == *definition && layout.arguments == *arguments).is_some_and(|layout|
                    layout.variants.iter().all(|fields| visit(value, &VmType::Tuple(fields.clone()), layouts, depth + 1, nodes))),
                VmType::Callable { .. } | VmType::Generic(_) | VmType::Array(_) | VmType::FixedArray { .. } => false,
                _ => true,
            }
        }
        let mut nodes = MAX_NODES;
        visit(self, ty, layouts, 0, &mut nodes)
    }

    pub(super) fn contains(&self) -> bool {
        !matches!(self, Self::None)
    }

    pub(super) fn frame(&self) -> Option<u32> {
        if let Self::Token(frame) = self { Some(*frame) } else { None }
    }

    pub(super) fn opaque(&self) -> Self {
        if self.contains() { Self::Unknown } else { Self::None }
    }

    pub(super) fn has_local_or_unknown(&self) -> bool {
        match self {
            Self::None | Self::Input(_) => false,
            Self::Token(_) | Self::Unknown | Self::Expired | Self::Prepared(_) => true,
            Self::Product(fields) => fields.values().any(Self::has_local_or_unknown),
        }
    }

    pub(super) fn instantiate(&self, inputs: &[Self]) -> Self {
        match self {
            Self::Input(path) => inputs.get(path.input as usize)
                .map_or(Self::Unknown, |value| value.project(&path.fields)),
            Self::Product(fields) => Self::fields(fields.iter().map(|(field, value)|
                (*field, value.instantiate(inputs))).collect()),
            value => value.clone(),
        }
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
            Self::Prepared(value) => depth > 0 && value.within_budget(depth - 1, nodes),
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
            Self::Prepared(value) => Arc::make_mut(value).expire(frame),
            Self::Token(actual) if *actual == frame => *self = Self::Expired,
            Self::Product(fields) => for value in Arc::make_mut(fields).values_mut() { value.expire(frame); },
            _ => {},
        }
    }

    pub(super) fn join(&self, other: &Self) -> Self {
        if self == other { return self.clone(); }
        match (self, other) {
            (Self::Expired, Self::None) | (Self::None, Self::Expired) => Self::Expired,
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

    /// An absent register contributes no ordinary callable alternative.
    /// Retain any existing taint even when readability is absent; only the
    /// positively empty, uninitialized side is the resident join's bottom.
    pub(super) fn join_resident(&self, present: bool, other: &Self, other_present: bool) -> Self {
        if !present && matches!(self, Self::None) { return other.clone(); }
        if !other_present && matches!(other, Self::None) { return self.clone(); }
        self.join(other)
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
        assert_eq!(joined.project(&[1]), Value::Expired);
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

    #[test]
    fn caller_input_paths_are_not_local_handler_brands() {
        let mut input = Value::Input(super::InputPath { input: 0, fields: vec![1] });
        input.expire(0);
        assert!(!input.has_local_or_unknown());
        assert_eq!(input.frame(), None);
        let mut supplied = Value::product([Value::None, Value::Token(7)]);
        assert_eq!(input.instantiate(&[supplied.clone()]), Value::Token(7));
        supplied.expire(7);
        assert_eq!(input.instantiate(&[supplied]), Value::Expired);
        assert_eq!(input.instantiate(&[]), Value::Unknown);
        assert_eq!(input.join(&Value::Token(0)), Value::Unknown);
    }

    #[test]
    fn expired_contents_can_be_released_but_never_regain_live_authority() {
        let mut value = Value::Token(7);
        value.expire(7);
        assert_eq!(value, Value::Expired);
        assert!(value.contains());
        assert!(value.has_local_or_unknown());
        assert_eq!(value.frame(), None);
        assert_eq!(value.join(&Value::None), Value::Expired);
        assert_eq!(value.join(&Value::Token(7)), Value::Unknown);
        assert_eq!(value.opaque(), Value::Unknown);
        // A later installation at the same executable location cannot turn
        // the old bytes into that new dynamic frame's token.
        value.expire(7);
        assert_eq!(value.frame(), None);
    }

    #[test]
    fn absent_residents_do_not_invent_nonresumption_value_alternatives() {
        let value = Value::product([Value::None, Value::Token(7)]);
        assert_eq!(value.join_resident(true, &Value::None, false), value);
        assert_eq!(Value::None.join_resident(false, &value, true), value);
        assert_eq!(Value::Token(7).join_resident(true, &Value::None, true), Value::Unknown);
        assert_eq!(Value::Unknown.join_resident(false, &value, true), Value::Unknown);
    }
}
