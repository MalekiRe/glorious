//! Typed, revision-owned dependency facts for incremental compilation.
//!
//! This is intentionally a ledger, not an ambient global invalidation map.
//! A request stages its complete set of semantic products and publishes it
//! only after the service publication boundary has accepted the request.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Mutex,
};

use crate::{DefKey, Digest, FileKey, InstanceKey, ModuleKey, PackageKey, RevisionId};

/// A stable semantic product identity.  The variants model actual compiler
/// boundaries rather than strings invented by individual passes.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DependencyNode {
    Input(FileKey),
    Interface(ModuleKey),
    Fixity(ModuleKey),
    Body(DefKey),
    Core(DefKey),
    Instance(InstanceKey),
    Mir(DefKey),
    Artifact(PackageKey),
}

/// The result of validating a product against its immediate parent revision.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DependencyStatus {
    /// No parent fact was retained, so reuse was not attempted.
    Cold,
    /// The product and all of its recorded inputs are semantically unchanged.
    Green { parent: RevisionId },
    /// A changed direct or transitive input made this product unavailable for
    /// reuse. `first_changed` is the first canonical explanation edge.
    Red {
        parent: RevisionId,
        first_changed: DependencyNode,
    },
    /// The staged graph contains a dependency cycle. Cycles are never green:
    /// callers must recompute through a query family that has an explicit
    /// SCC/fixed-point policy rather than reuse this fact as ordinary cache
    /// evidence.
    Cycle {
        parent: RevisionId,
        member: DependencyNode,
    },
    /// A product refers to a dependency which this transaction did not stage.
    /// This is incomplete producer evidence, never a reusable cache result.
    Incomplete { missing: DependencyNode },
}

/// Tooling-safe explanation for one published semantic product.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DependencyTrace {
    pub revision: RevisionId,
    pub node: DependencyNode,
    pub fingerprint: Digest,
    pub dependencies: Vec<DependencyNode>,
    pub status: DependencyStatus,
}

#[derive(Clone, Debug)]
struct DependencyFact {
    fingerprint: Digest,
    dependencies: Vec<DependencyNode>,
}

#[derive(Clone, Debug, Default)]
struct RevisionLedger {
    traces: BTreeMap<DependencyNode, DependencyTrace>,
}

/// Database-lifetime owner for all revision dependency products.
#[derive(Debug, Default)]
pub struct DependencyLedger {
    revisions: Mutex<BTreeMap<RevisionId, RevisionLedger>>,
}

impl DependencyLedger {
    pub(crate) fn transaction(
        &self,
        revision: RevisionId,
        parent: Option<RevisionId>,
    ) -> DependencyTransaction<'_> {
        DependencyTransaction {
            ledger: self,
            revision,
            parent,
            facts: BTreeMap::new(),
        }
    }

    pub fn trace(&self, revision: RevisionId, node: &DependencyNode) -> Option<DependencyTrace> {
        self.revisions
            .lock()
            .expect("dependency ledger mutex poisoned")
            .get(&revision)
            .and_then(|ledger| ledger.traces.get(node))
            .cloned()
    }

    pub fn traces(&self, revision: RevisionId) -> Vec<DependencyTrace> {
        self.revisions
            .lock()
            .expect("dependency ledger mutex poisoned")
            .get(&revision)
            .map(|ledger| ledger.traces.values().cloned().collect())
            .unwrap_or_default()
    }

    pub(crate) fn remove_revision(&self, revision: RevisionId) {
        self.revisions
            .lock()
            .expect("dependency ledger mutex poisoned")
            .remove(&revision);
    }
}

/// Request-local staged dependency facts. Dropping without `commit` leaves
/// no revision-visible cache or invalidation state behind.
#[derive(Debug)]
pub(crate) struct DependencyTransaction<'a> {
    ledger: &'a DependencyLedger,
    revision: RevisionId,
    parent: Option<RevisionId>,
    facts: BTreeMap<DependencyNode, DependencyFact>,
}

impl DependencyTransaction<'_> {
    pub(crate) fn record(
        &mut self,
        node: DependencyNode,
        fingerprint: Digest,
        mut dependencies: Vec<DependencyNode>,
    ) {
        dependencies.sort();
        dependencies.dedup();
        self.facts.insert(
            node,
            DependencyFact {
                fingerprint,
                dependencies,
            },
        );
    }

    pub(crate) fn commit(self) {
        let mut revisions = self
            .ledger
            .revisions
            .lock()
            .expect("dependency ledger mutex poisoned");
        let parent = self.parent.and_then(|id| revisions.get(&id));
        let mut statuses = BTreeMap::<DependencyNode, DependencyStatus>::new();
        let mut traces = BTreeMap::new();
        for node in self.facts.keys() {
            let status = validate(
                node,
                &self.facts,
                parent,
                self.parent,
                &mut statuses,
                &mut BTreeSet::new(),
            );
            let fact = self.facts.get(node).expect("fact key came from facts");
            traces.insert(
                node.clone(),
                DependencyTrace {
                    revision: self.revision,
                    node: node.clone(),
                    fingerprint: fact.fingerprint,
                    dependencies: fact.dependencies.clone(),
                    status,
                },
            );
        }
        revisions.insert(self.revision, RevisionLedger { traces });
    }
}

fn validate(
    node: &DependencyNode,
    facts: &BTreeMap<DependencyNode, DependencyFact>,
    parent: Option<&RevisionLedger>,
    parent_id: Option<RevisionId>,
    statuses: &mut BTreeMap<DependencyNode, DependencyStatus>,
    visiting: &mut BTreeSet<DependencyNode>,
) -> DependencyStatus {
    if let Some(status) = statuses.get(node) {
        return status.clone();
    }
    let Some(fact) = facts.get(node) else {
        return DependencyStatus::Incomplete {
            missing: node.clone(),
        };
    };
    let Some(parent_id) = parent_id else {
        if let Some(missing) = fact
            .dependencies
            .iter()
            .find(|dependency| !facts.contains_key(*dependency))
        {
            return DependencyStatus::Incomplete {
                missing: missing.clone(),
            };
        }
        return DependencyStatus::Cold;
    };
    let Some(parent_fact) = parent.and_then(|ledger| ledger.traces.get(node)) else {
        return DependencyStatus::Cold;
    };
    // Dependency edges are normally produced by the acyclic phase pipeline,
    // but the ledger is an internal trust boundary: a malformed or future
    // cyclic query graph must never turn validation into unbounded recursion.
    // Treat the back edge as a deterministic red dependency. The enclosing
    // node records the first canonical cycle member as its invalidation cause.
    if !visiting.insert(node.clone()) {
        return DependencyStatus::Cycle {
            parent: parent_id,
            member: node.clone(),
        };
    }
    // This is red/green *value* validation. A dependency may have changed
    // and forced this product to be checked, while the newly computed
    // product remains byte-for-byte semantically equal. In that case it is
    // green and downstream products can reuse it. That distinction is what
    // keeps a private body edit from invalidating an unchanged public
    // interface (or an unrelated fixity table).
    let mut cycle_member = None;
    let mut incomplete = None;
    let first_changed = fact.dependencies.iter().find_map(|dependency| {
        let dependency_status = validate(
            dependency,
            facts,
            parent,
            Some(parent_id),
            statuses,
            visiting,
        );
        match dependency_status {
            DependencyStatus::Green { .. } => None,
            DependencyStatus::Red { first_changed, .. } => Some(first_changed),
            DependencyStatus::Cycle { member, .. } => {
                cycle_member.get_or_insert(member.clone());
                Some(member)
            }
            DependencyStatus::Incomplete { missing } => {
                incomplete.get_or_insert(missing.clone());
                Some(missing)
            }
            DependencyStatus::Cold => Some(dependency.clone()),
        }
    });
    let status = if let Some(missing) = incomplete {
        DependencyStatus::Incomplete { missing }
    } else if let Some(member) = cycle_member {
        DependencyStatus::Cycle {
            parent: parent_id,
            member,
        }
    } else if parent_fact.fingerprint == fact.fingerprint
        && parent_fact.dependencies == fact.dependencies
    {
        DependencyStatus::Green { parent: parent_id }
    } else if let Some(changed) = first_changed {
        DependencyStatus::Red {
            parent: parent_id,
            first_changed: changed,
        }
    } else {
        DependencyStatus::Red {
            parent: parent_id,
            first_changed: node.clone(),
        }
    };
    visiting.remove(node);
    statuses.insert(node.clone(), status.clone());
    status
}

#[cfg(test)]
mod tests {
    use super::*;

    fn revision(ordinal: u64) -> RevisionId {
        RevisionId {
            database: 7,
            ordinal,
        }
    }

    fn file(value: u8) -> FileKey {
        FileKey(Digest::of_bytes(&[value]))
    }

    #[test]
    fn validates_green_and_reports_transitive_first_change() {
        let ledger = DependencyLedger::default();
        let source = DependencyNode::Input(file(1));
        let interface = DependencyNode::Interface(ModuleKey {
            package: PackageKey("test".into()),
            path: "crate".into(),
        });
        let core = DependencyNode::Core(DefKey(Digest::of_bytes(b"main")));
        let artifact = DependencyNode::Artifact(PackageKey("test".into()));
        let mut first = ledger.transaction(revision(0), None);
        first.record(source.clone(), Digest::of_bytes(b"source-a"), vec![]);
        first.record(
            interface.clone(),
            Digest::of_bytes(b"interface"),
            vec![source.clone()],
        );
        first.record(
            core.clone(),
            Digest::of_bytes(b"core-a"),
            vec![source.clone(), interface],
        );
        first.record(
            artifact.clone(),
            Digest::of_bytes(b"artifact-a"),
            vec![core.clone()],
        );
        first.commit();

        let mut second = ledger.transaction(revision(1), Some(revision(0)));
        second.record(source.clone(), Digest::of_bytes(b"source-b"), vec![]);
        second.record(
            DependencyNode::Interface(ModuleKey {
                package: PackageKey("test".into()),
                path: "crate".into(),
            }),
            Digest::of_bytes(b"interface"),
            vec![source.clone()],
        );
        second.record(
            core.clone(),
            Digest::of_bytes(b"core-b"),
            vec![
                source.clone(),
                DependencyNode::Interface(ModuleKey {
                    package: PackageKey("test".into()),
                    path: "crate".into(),
                }),
            ],
        );
        second.record(
            artifact.clone(),
            Digest::of_bytes(b"artifact-b"),
            vec![core],
        );
        second.commit();
        assert!(matches!(
            ledger.trace(revision(1), &artifact).unwrap().status,
            DependencyStatus::Red { first_changed, .. } if first_changed == source
        ));
    }

    #[test]
    fn cyclic_facts_are_deterministically_red_instead_of_recursing() {
        let ledger = DependencyLedger::default();
        let left = DependencyNode::Core(DefKey(Digest::of_bytes(b"left")));
        let right = DependencyNode::Mir(DefKey(Digest::of_bytes(b"right")));

        let mut first = ledger.transaction(revision(0), None);
        first.record(left.clone(), Digest::of_bytes(b"left"), vec![right.clone()]);
        first.record(
            right.clone(),
            Digest::of_bytes(b"right"),
            vec![left.clone()],
        );
        first.commit();

        let mut second = ledger.transaction(revision(1), Some(revision(0)));
        second.record(left.clone(), Digest::of_bytes(b"left"), vec![right.clone()]);
        second.record(
            right.clone(),
            Digest::of_bytes(b"right"),
            vec![left.clone()],
        );
        second.commit();

        assert!(matches!(
            ledger.trace(revision(1), &left).unwrap().status,
            DependencyStatus::Cycle { member, .. } if member == left
        ));
        assert!(matches!(
            ledger.trace(revision(1), &right).unwrap().status,
            DependencyStatus::Cycle { .. }
        ));
    }

    #[test]
    fn omitted_staged_dependency_fails_closed_without_a_panic() {
        let ledger = DependencyLedger::default();
        let core = DependencyNode::Core(DefKey(Digest::of_bytes(b"main")));
        let missing = DependencyNode::Body(DefKey(Digest::of_bytes(b"main")));

        let mut first = ledger.transaction(revision(0), None);
        first.record(
            core.clone(),
            Digest::of_bytes(b"core"),
            vec![missing.clone()],
        );
        first.commit();

        let mut second = ledger.transaction(revision(1), Some(revision(0)));
        second.record(
            core.clone(),
            Digest::of_bytes(b"core"),
            vec![missing.clone()],
        );
        second.commit();

        assert!(matches!(
            ledger.trace(revision(1), &core).unwrap().status,
            DependencyStatus::Incomplete { missing: found } if found == missing
        ));
    }
}
