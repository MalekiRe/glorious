//! Typed, revision-owned dependency facts for incremental compilation.
//!
//! This is intentionally a ledger, not an ambient global invalidation map.
//! A request stages its complete set of semantic products and publishes it
//! only after the service publication boundary has accepted the request.

use std::{collections::BTreeMap, sync::Mutex};

use crate::{DefKey, Digest, FileKey, ModuleKey, PackageKey, RevisionId};

/// A stable semantic product identity.  The variants model actual compiler
/// boundaries rather than strings invented by individual passes.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DependencyNode {
    Input(FileKey),
    Interface(ModuleKey),
    Fixity(ModuleKey),
    Core(DefKey),
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
            let status = validate(node, &self.facts, parent, self.parent, &mut statuses);
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
) -> DependencyStatus {
    if let Some(status) = statuses.get(node) {
        return status.clone();
    }
    let Some(parent_id) = parent_id else {
        return DependencyStatus::Cold;
    };
    let Some(parent_fact) = parent.and_then(|ledger| ledger.traces.get(node)) else {
        return DependencyStatus::Cold;
    };
    let fact = facts
        .get(node)
        .expect("validation only visits staged facts");
    // This is red/green *value* validation. A dependency may have changed
    // and forced this product to be checked, while the newly computed
    // product remains byte-for-byte semantically equal. In that case it is
    // green and downstream products can reuse it. That distinction is what
    // keeps a private body edit from invalidating an unchanged public
    // interface (or an unrelated fixity table).
    let first_changed = fact.dependencies.iter().find_map(|dependency| {
        let dependency_status = validate(dependency, facts, parent, Some(parent_id), statuses);
        match dependency_status {
            DependencyStatus::Green { .. } => None,
            DependencyStatus::Red { first_changed, .. } => Some(first_changed),
            DependencyStatus::Cold => Some(dependency.clone()),
        }
    });
    let status = if parent_fact.fingerprint == fact.fingerprint
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
}
