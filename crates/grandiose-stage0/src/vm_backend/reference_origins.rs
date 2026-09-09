//! The verifier's finite may-set of source-storage roots.
//!
//! Almost every register has either no reference origin or exactly one. Keep
//! those cases inline; only actual CFG unions need a shared ordered set. A
//! verifier snapshot clones the uncommon multi-origin allocation by reference,
//! and a later mutation detaches it. This changes representation, not the
//! lattice: empty is still the empty set, never an unknown or independent fact.

use std::{
    collections::{BTreeSet, btree_set},
    sync::Arc,
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) enum ReferenceOriginSet {
    #[default]
    Empty,
    One(u32),
    /// Canonical invariant: at least two roots, in ascending order.
    Many(Arc<BTreeSet<u32>>),
}

impl ReferenceOriginSet {
    pub(super) fn contains(&self, root: &u32) -> bool {
        match self {
            Self::Empty => false,
            Self::One(value) => value == root,
            Self::Many(values) => values.contains(root),
        }
    }

    pub(super) fn clear(&mut self) {
        *self = Self::Empty;
    }

    /// Monotonic may-join, returning exactly whether any new root was added.
    pub(super) fn union_with(&mut self, other: &Self) -> bool {
        match (&mut *self, other) {
            (_, Self::Empty) => false,
            (Self::Empty, _) => {
                *self = other.clone();
                true
            }
            (Self::One(left), Self::One(right)) if left == right => false,
            (Self::One(left), Self::One(right)) => {
                *self = Self::Many(Arc::new(BTreeSet::from([*left, *right])));
                true
            }
            (Self::One(left), Self::Many(right)) => {
                let mut joined = right.clone();
                if !right.contains(left) {
                    Arc::make_mut(&mut joined).insert(*left);
                }
                *self = Self::Many(joined);
                true
            }
            (Self::Many(left), Self::One(right)) => {
                if left.contains(right) {
                    return false;
                }
                Arc::make_mut(left).insert(*right);
                true
            }
            (Self::Many(left), Self::Many(right)) => {
                if Arc::ptr_eq(left, right) || right.is_subset(left) {
                    return false;
                }
                Arc::make_mut(left).extend(right.iter().copied());
                true
            }
        }
    }
}

pub(super) enum ReferenceOriginIter<'a> {
    Inline(Option<&'a u32>),
    Many(btree_set::Iter<'a, u32>),
}

impl<'a> Iterator for ReferenceOriginIter<'a> {
    type Item = &'a u32;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Inline(value) => value.take(),
            Self::Many(values) => values.next(),
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let count = match self {
            Self::Inline(value) => usize::from(value.is_some()),
            Self::Many(values) => values.len(),
        };
        (count, Some(count))
    }
}
impl ExactSizeIterator for ReferenceOriginIter<'_> {}

impl<'a> IntoIterator for &'a ReferenceOriginSet {
    type Item = &'a u32;
    type IntoIter = ReferenceOriginIter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        match self {
            ReferenceOriginSet::Empty => ReferenceOriginIter::Inline(None),
            ReferenceOriginSet::One(value) => ReferenceOriginIter::Inline(Some(value)),
            ReferenceOriginSet::Many(values) => ReferenceOriginIter::Many(values.iter()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(mask: u8) -> ReferenceOriginSet {
        let mut result = ReferenceOriginSet::Empty;
        for value in 0..6 {
            if mask & (1 << value) != 0 {
                result.union_with(&ReferenceOriginSet::One(value));
            }
        }
        result
    }

    fn roots(value: &ReferenceOriginSet) -> BTreeSet<u32> {
        value.into_iter().copied().collect()
    }

    #[test]
    fn compact_origins_have_exact_ordered_set_lattice() {
        for left in 0..64 {
            for right in 0..64 {
                let mut actual = set(left);
                let saved = actual.clone();
                let other = set(right);
                let expected = roots(&actual)
                    .union(&roots(&other))
                    .copied()
                    .collect::<BTreeSet<_>>();
                let changed = actual.union_with(&other);
                assert_eq!(roots(&actual), expected);
                assert_eq!(changed, left | right != left);
                assert_eq!(
                    saved,
                    set(left),
                    "joining a snapshot must not mutate its origin"
                );
                assert!(
                    !actual.union_with(&other),
                    "a repeated may-join is idempotent"
                );
                for value in 0..6 {
                    assert_eq!(actual.contains(&value), expected.contains(&value));
                }
            }
        }
    }

    #[test]
    fn clearing_one_snapshot_retains_the_other_origin_set() {
        let saved = set(0b101101);
        let mut changed = saved.clone();
        changed.clear();
        assert_eq!(changed, ReferenceOriginSet::Empty);
        assert_eq!(roots(&saved), BTreeSet::from([0, 2, 3, 5]));
        assert_eq!((&saved).into_iter().len(), 4);
        assert!(std::mem::size_of::<ReferenceOriginSet>() < std::mem::size_of::<BTreeSet<u32>>());
    }
}
