//! Lexical control dependencies, independent of invocation or reachability.
//!
//! A direct transfer and a first-class label value retain the same generative
//! destination. A label discharges that dependency only in its own body; a
//! declaration elsewhere in the arena cannot discharge a sibling's reference.
//! Closure bodies participate because this product describes code dependence,
//! not execution at closure formation. It is not an alias/control-flow proof.

use super::{CoreExpr, CoreId, CoreKind, LabelBrand, core_children};
use std::collections::{BTreeSet, VecDeque};

#[derive(Clone, Debug, Eq, PartialEq)]
struct Rule {
    children: Vec<CoreId>,
    reference: Option<LabelBrand>,
    binder: Option<LabelBrand>,
    closure: Option<CoreId>,
}

impl Rule {
    fn project(expression: &CoreExpr) -> Self {
        Self {
            children: core_children(&expression.kind),
            reference: match expression.kind {
                CoreKind::Transfer { brand, .. } | CoreKind::LabelValue { brand } => Some(brand),
                _ => None,
            },
            binder: match expression.kind {
                CoreKind::Label { brand, .. } => Some(brand),
                _ => None,
            },
            closure: match expression.kind {
                CoreKind::Closure { body, .. } => Some(body),
                _ => None,
            },
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum InvalidInput {
    Missing(CoreId),
    Cycle,
    UnboundLabel(CoreId),
}

#[derive(Clone, Debug)]
pub(crate) struct LabelDependencies {
    rules: Vec<Option<Rule>>,
    free: Vec<Option<BTreeSet<LabelBrand>>>,
}

impl LabelDependencies {
    pub(crate) fn derive(expressions: &[CoreExpr]) -> Result<Self, InvalidInput> {
        Self::solve(
            expressions,
            (0..expressions.len()).map(|index| CoreId(index as u32)),
        )
    }

    /// Elaboration can query a completed subgraph before the surrounding body
    /// has been frozen. Unqueried nodes are absent, never known independent.
    pub(super) fn for_root(expressions: &[CoreExpr], root: CoreId) -> Result<Self, InvalidInput> {
        Self::solve(expressions, [root])
    }

    fn solve(
        expressions: &[CoreExpr],
        roots: impl IntoIterator<Item = CoreId>,
    ) -> Result<Self, InvalidInput> {
        let mut rules = vec![None; expressions.len()];
        let mut pending = roots.into_iter().collect::<Vec<_>>();
        while let Some(id) = pending.pop() {
            let Some(expression) = expressions.get(id.0 as usize) else {
                return Err(InvalidInput::Missing(id));
            };
            if rules[id.0 as usize].is_some() {
                continue;
            }
            let rule = Rule::project(expression);
            pending.extend(rule.children.iter().copied());
            rules[id.0 as usize] = Some(rule);
        }
        let mut parents = vec![vec![]; expressions.len()];
        let mut remaining = vec![0; expressions.len()];
        let mut ready = VecDeque::new();
        for (index, rule) in rules.iter().enumerate() {
            let Some(rule) = rule else {
                continue;
            };
            remaining[index] = rule.children.len();
            if rule.children.is_empty() {
                ready.push_back(index);
            }
            for child in &rule.children {
                parents[child.0 as usize].push(index);
            }
        }
        let mut free: Vec<Option<BTreeSet<LabelBrand>>> = vec![None; expressions.len()];
        while let Some(index) = ready.pop_front() {
            let rule = rules[index].as_ref().expect("projected dependency rule");
            let mut labels = BTreeSet::new();
            for child in &rule.children {
                labels.extend(
                    free[child.0 as usize]
                        .as_ref()
                        .expect("solved dependency child"),
                );
            }
            labels.extend(rule.reference);
            if let Some(binder) = rule.binder {
                labels.remove(&binder);
            }
            free[index] = Some(labels);
            for parent in &parents[index] {
                remaining[*parent] -= 1;
                if remaining[*parent] == 0 {
                    ready.push_back(*parent);
                }
            }
        }
        if rules
            .iter()
            .zip(&free)
            .any(|(rule, free)| rule.is_some() && free.is_none())
        {
            return Err(InvalidInput::Cycle);
        }
        Ok(Self { rules, free })
    }

    pub(crate) fn matches(&self, expressions: &[CoreExpr]) -> bool {
        self.rules.len() == expressions.len()
            && self
                .rules
                .iter()
                .zip(expressions)
                .all(|(rule, expression)| {
                    rule.as_ref()
                        .is_none_or(|rule| *rule == Rule::project(expression))
                })
    }

    pub(crate) fn free(&self, root: CoreId) -> Option<&BTreeSet<LabelBrand>> {
        self.free.get(root.0 as usize)?.as_ref()
    }

    pub(crate) fn independent(&self, root: CoreId) -> bool {
        self.free(root).is_some_and(BTreeSet::is_empty)
    }

    /// Pending code dependencies are admitted only while their destination is
    /// lexically in scope at formation. This is not permission to let the
    /// resulting value escape or to materialize an independent closure frame.
    /// A later structural transformation must discharge every pending entry.
    pub(crate) fn pending_closures(
        &self,
        root: CoreId,
    ) -> Result<std::collections::BTreeMap<CoreId, BTreeSet<LabelBrand>>, InvalidInput> {
        let mut pending = vec![(root, BTreeSet::new())];
        let mut seen = BTreeSet::new();
        let mut obligations = std::collections::BTreeMap::new();
        while let Some((id, mut active)) = pending.pop() {
            if !seen.insert((id, active.clone())) { continue; }
            let rule = self.rules.get(id.0 as usize).and_then(Option::as_ref)
                .ok_or(InvalidInput::Missing(id))?;
            if rule.reference.is_some_and(|brand| !active.contains(&brand)) {
                return Err(InvalidInput::UnboundLabel(id));
            }
            if let Some(body) = rule.closure {
                let labels = self.free(body).ok_or(InvalidInput::Missing(body))?;
                if !labels.is_subset(&active) { return Err(InvalidInput::UnboundLabel(id)); }
                if !labels.is_empty() { obligations.insert(id, labels.clone()); }
            }
            active.extend(rule.binder);
            pending.extend(rule.children.iter().map(|child| (*child, active.clone())));
        }
        Ok(obligations)
    }

    pub(crate) fn reference(&self, id: CoreId) -> Option<LabelBrand> {
        self.rules.get(id.0 as usize)?.as_ref()?.reference
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{DefKey, Digest, FileKey, Span, Type};

    fn brand(index: u32) -> LabelBrand {
        LabelBrand {
            owner: DefKey(Digest::of_bytes(b"label dependency rules")),
            label: index,
        }
    }
    fn node(kind: CoreKind) -> CoreExpr {
        CoreExpr {
            kind,
            ty: Type::Unit,
            span: Span {
                file: FileKey(Digest::of_bytes(b"label dependency rules")),
                start: 0,
                end: 0,
            },
        }
    }

    #[test]
    fn values_and_transfers_retain_the_same_exact_destination() {
        let expressions = vec![
            node(CoreKind::Tuple(vec![])),
            node(CoreKind::Transfer {
                brand: brand(0),
                value: CoreId(0),
            }),
            node(CoreKind::LabelValue { brand: brand(1) }),
            node(CoreKind::Block(vec![CoreId(1), CoreId(2)])),
            node(CoreKind::Label {
                brand: brand(0),
                body: CoreId(3),
            }),
            node(CoreKind::Label {
                brand: brand(1),
                body: CoreId(4),
            }),
        ];
        let facts = LabelDependencies::derive(&expressions).unwrap();
        assert_eq!(
            facts.free(CoreId(3)),
            Some(&BTreeSet::from([brand(0), brand(1)]))
        );
        assert_eq!(facts.free(CoreId(4)), Some(&BTreeSet::from([brand(1)])));
        assert!(facts.independent(CoreId(5)));
        assert!(!facts.independent(CoreId(99)));
    }

    #[test]
    fn a_sibling_declaration_does_not_discharge_a_dependency() {
        let expressions = vec![
            node(CoreKind::Tuple(vec![])),
            node(CoreKind::Label {
                brand: brand(0),
                body: CoreId(0),
            }),
            node(CoreKind::LabelValue { brand: brand(0) }),
            node(CoreKind::Block(vec![CoreId(1), CoreId(2)])),
        ];
        let facts = LabelDependencies::derive(&expressions).unwrap();
        assert_eq!(facts.free(CoreId(3)), Some(&BTreeSet::from([brand(0)])));
        assert!(facts.independent(CoreId(1)));
    }

    #[test]
    fn missing_cyclic_and_stale_inputs_cannot_prove_independence() {
        let mut expressions = vec![
            node(CoreKind::LabelValue { brand: brand(0) }),
            node(CoreKind::Label {
                brand: brand(0),
                body: CoreId(0),
            }),
        ];
        let facts = LabelDependencies::derive(&expressions).unwrap();
        expressions[0].kind = CoreKind::LabelValue { brand: brand(1) };
        assert!(!facts.matches(&expressions));
        expressions[1].kind = CoreKind::Block(vec![CoreId(99)]);
        assert!(matches!(
            LabelDependencies::derive(&expressions),
            Err(InvalidInput::Missing(CoreId(99)))
        ));
        expressions[1].kind = CoreKind::Block(vec![CoreId(1)]);
        assert!(matches!(
            LabelDependencies::derive(&expressions),
            Err(InvalidInput::Cycle)
        ));
        let partial = LabelDependencies::for_root(&expressions, CoreId(0)).unwrap();
        assert!(!partial.independent(CoreId(1)));
    }

    #[test]
    fn deeply_shared_graphs_use_one_nonrecursive_worklist() {
        let mut expressions = vec![node(CoreKind::LabelValue { brand: brand(0) })];
        for index in 1..10_000 {
            expressions.push(node(CoreKind::Block(vec![
                CoreId(index - 1),
                CoreId(index - 1),
            ])));
        }
        let facts = LabelDependencies::derive(&expressions).unwrap();
        assert_eq!(facts.free(CoreId(9_999)), Some(&BTreeSet::from([brand(0)])));
    }
}
