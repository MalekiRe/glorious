//! Typed query contract for the stage-zero semantic database.
//!
//! Query execution is intentionally separate from request assembly. A query
//! can only read a `DatabaseSnapshot`, which makes any missing input dependency
//! visible in its key or declared dependency list rather than hiding it behind
//! process state.

use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    sync::{Arc, Mutex},
};

use crate::{
    identity::{Digest, RevisionId},
    operation::{Budget, BudgetError, CancellationToken},
    revision::{DatabaseSnapshot, RevisionCache},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum QueryCompleteness {
    Complete,
    Recovered,
}

#[derive(Clone, Debug)]
pub struct QueryValue<T> {
    pub value: T,
    pub fingerprint: Digest,
    pub completeness: QueryCompleteness,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Dependency {
    pub revision: RevisionId,
    pub query: &'static str,
    pub fingerprint: Digest,
}

/// The in-progress owner of one query evaluation. It records exact typed
/// dependencies in demand order. Publication sorts/deduplicates those records
/// so inspection and invalidation explanations are deterministic even when
/// query execution later gains parallel scheduling.
#[derive(Debug)]
pub struct QueryFrame {
    revision: RevisionId,
    dependencies: Vec<Dependency>,
}

impl QueryFrame {
    pub fn new(snapshot: &DatabaseSnapshot) -> Self {
        Self {
            revision: snapshot.id(),
            dependencies: vec![],
        }
    }

    pub fn depend(&mut self, query: &'static str, fingerprint: Digest) {
        self.dependencies.push(Dependency {
            revision: self.revision,
            query,
            fingerprint,
        });
    }

    pub fn finish(mut self) -> Vec<Dependency> {
        self.dependencies.sort_by(|left, right| {
            (left.revision, left.query, left.fingerprint).cmp(&(
                right.revision,
                right.query,
                right.fingerprint,
            ))
        });
        self.dependencies.dedup();
        self.dependencies
    }
}

#[derive(Clone, Debug)]
pub struct MemoEntry<V> {
    pub result: QueryValue<V>,
    pub dependencies: Vec<Dependency>,
}

/// A deterministic explanation for work performed after a revision change.
/// Query-family owners decide whether a parent memo entry remains valid; the
/// engine records that decision instead of making cache warmth invisible to
/// inspection clients.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum QueryRecomputeReason {
    Cold,
    ParentMemoMissing { parent: RevisionId },
    ParentReuseRejected { parent: RevisionId },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum QueryExecutionKind {
    Memoized { revision: RevisionId },
    ReusedFromParent { parent: RevisionId },
    Recomputed { reason: QueryRecomputeReason },
}

/// Typed, revision-qualified in-memory memoization. Query-family owners keep
/// one of these tables; no stringly typed global cache can mix values from two
/// families or two snapshots.
#[derive(Debug)]
pub struct MemoTable<K, V> {
    entries: Mutex<HashMap<(RevisionId, K), MemoEntry<V>>>,
}

impl<K, V> Default for MemoTable<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> MemoTable<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    pub fn new() -> Self {
        Self {
            entries: Mutex::new(HashMap::new()),
        }
    }

    pub fn get(&self, snapshot: &DatabaseSnapshot, key: &K) -> Option<MemoEntry<V>> {
        self.get_at(snapshot.id(), key)
    }

    fn get_at(&self, revision: RevisionId, key: &K) -> Option<MemoEntry<V>> {
        self.entries
            .lock()
            .expect("query memo mutex poisoned")
            .get(&(revision, key.clone()))
            .cloned()
    }

    /// Forget every product for a collected revision. The compiler database
    /// invokes this only at its retirement safe point, after no snapshot can
    /// still observe the removed immutable world.
    pub fn discard_revision(&self, revision: RevisionId) -> u64 {
        let mut entries = self.entries.lock().expect("query memo mutex poisoned");
        let before = entries.len();
        entries.retain(|(entry_revision, _), _| *entry_revision != revision);
        u64::try_from(before - entries.len()).expect("query memo entry count exceeds u64")
    }

    /// Inspection accounting for bounded-retention hosts and tests. It never
    /// exposes keys or values from a revision that has been retired.
    pub fn retained_entry_count(&self) -> u64 {
        u64::try_from(
            self.entries
                .lock()
                .expect("query memo mutex poisoned")
                .len(),
        )
        .expect("query memo entry count exceeds u64")
    }

    /// A caller publishes only a complete or explicitly recovered value. A
    /// cancellation/failure cannot manufacture an entry because it has no
    /// `QueryValue` to pass to this method.
    pub fn publish(
        &self,
        snapshot: &DatabaseSnapshot,
        key: K,
        result: QueryValue<V>,
        frame: QueryFrame,
    ) {
        assert_eq!(
            snapshot.id(),
            frame.revision,
            "query frame crossed revisions"
        );
        self.entries
            .lock()
            .expect("query memo mutex poisoned")
            .insert(
                (snapshot.id(), key),
                MemoEntry {
                    result,
                    dependencies: frame.finish(),
                },
            );
    }

    /// Re-publish a query-family-validated parent result under a child
    /// revision. Dependencies retain their exact producer/fingerprint but are
    /// rewritten to the child revision because validation has established that
    /// these are the child world's observed facts too.
    fn publish_reused(&self, snapshot: &DatabaseSnapshot, key: K, parent: MemoEntry<V>) {
        let dependencies = parent
            .dependencies
            .into_iter()
            .map(|dependency| Dependency {
                revision: snapshot.id(),
                query: dependency.query,
                fingerprint: dependency.fingerprint,
            })
            .collect();
        self.entries
            .lock()
            .expect("query memo mutex poisoned")
            .insert(
                (snapshot.id(), key),
                MemoEntry {
                    result: parent.result,
                    dependencies,
                },
            );
    }
}

#[derive(Clone, Debug)]
pub enum QueryFailure<E> {
    Rejected(E),
    Cancelled,
    ResourceLimit { name: &'static str, limit: u64 },
    Invariant(&'static str),
    Cycle { query: &'static str },
}

/// The only authority granted to a running query. Nested queries record their
/// observed products here; cancellation and budget checks stay at structural
/// boundaries instead of being ambient process state.
pub struct QueryContext<'a> {
    snapshot: &'a DatabaseSnapshot,
    cancellation: &'a CancellationToken,
    budget: &'a Arc<Budget>,
    frame: QueryFrame,
}

impl<'a> QueryContext<'a> {
    fn new(
        snapshot: &'a DatabaseSnapshot,
        cancellation: &'a CancellationToken,
        budget: &'a Arc<Budget>,
    ) -> Self {
        Self {
            snapshot,
            cancellation,
            budget,
            frame: QueryFrame::new(snapshot),
        }
    }
    pub fn snapshot(&self) -> &DatabaseSnapshot {
        self.snapshot
    }
    pub fn check<E>(&self) -> Result<(), QueryFailure<E>> {
        self.cancellation
            .check()
            .map_err(|_| QueryFailure::Cancelled)
    }
    pub fn charge<E>(&self, amount: u64) -> Result<(), QueryFailure<E>> {
        self.budget
            .charge(amount)
            .map_err(
                |BudgetError { name, ceiling, .. }| QueryFailure::ResourceLimit {
                    name,
                    limit: ceiling,
                },
            )
    }
    pub fn depend(&mut self, query: &'static str, fingerprint: Digest) {
        self.frame.depend(query, fingerprint);
    }
    /// Execute a typed child query under this query's immutable snapshot and
    /// request controls.  The child result is recorded automatically, so phase
    /// code cannot accidentally use a nested semantic product without
    /// explaining that dependency to invalidation and inspection clients.
    pub fn query<Q: Query>(
        &mut self,
        engine: &QueryEngine<Q>,
        key: Q::Key,
    ) -> Result<QueryValue<Q::Value>, QueryFailure<Q::Error>> {
        let result = engine.execute(self.snapshot, key, self.cancellation, self.budget)?;
        self.frame.depend(Q::NAME, result.fingerprint);
        Ok(result)
    }
    fn finish(self) -> QueryFrame {
        self.frame
    }
}

/// Every query family owns one typed key/value contract, cycle policy, and
/// deterministic public name. The engine implementation will memoize these
/// typed values and journal dependencies; phase code must never maintain a
/// second hand-written invalidation graph.
pub trait Query {
    type Key: Clone + Debug + Eq + Hash + Send + Sync + 'static;
    type Value: Clone + Debug + Send + Sync + 'static;
    type Error: Clone + Debug + Send + Sync + 'static;

    const NAME: &'static str;

    /// Validate a cached parent result for one child revision. The default is
    /// fail-closed: only a query family that understands all of its inputs may
    /// carry a result across revisions.
    fn can_reuse(
        &self,
        _key: &Self::Key,
        _parent: &MemoEntry<Self::Value>,
        _from: &DatabaseSnapshot,
        _to: &DatabaseSnapshot,
    ) -> bool {
        false
    }

    fn execute(
        &self,
        context: &mut QueryContext<'_>,
        key: Self::Key,
    ) -> Result<QueryValue<Self::Value>, QueryFailure<Self::Error>>;
}

/// Per-query-family executor. It gives every typed query revision-qualified
/// memoization, cycle rejection, cancellation, bounded work, and transactional
/// publication without permitting phase-global cache state.
#[derive(Debug)]
pub struct QueryEngine<Q: Query> {
    query: Q,
    memo: MemoTable<Q::Key, Q::Value>,
    running: Mutex<HashSet<(RevisionId, Q::Key)>>,
    execution: Mutex<HashMap<(RevisionId, Q::Key), QueryExecutionKind>>,
}

impl<Q: Query> QueryEngine<Q> {
    pub fn new(query: Q) -> Self {
        Self {
            query,
            memo: MemoTable::new(),
            running: Mutex::new(HashSet::new()),
            execution: Mutex::new(HashMap::new()),
        }
    }
    pub fn execute(
        &self,
        snapshot: &DatabaseSnapshot,
        key: Q::Key,
        cancellation: &CancellationToken,
        budget: &Arc<Budget>,
    ) -> Result<QueryValue<Q::Value>, QueryFailure<Q::Error>> {
        // A cached result is still a request publication. Obsolete editor
        // work must not observe it merely because another request populated a
        // memo first.
        cancellation.check().map_err(|_| QueryFailure::Cancelled)?;
        if let Some(entry) = self.memo.get(snapshot, &key) {
            self.record_execution(
                snapshot,
                &key,
                QueryExecutionKind::Memoized {
                    revision: snapshot.id(),
                },
            );
            return Ok(entry.result);
        }
        cancellation.check().map_err(|_| QueryFailure::Cancelled)?;
        let recompute_reason = if let Some(parent_snapshot) = snapshot.parent_snapshot() {
            let parent = parent_snapshot.id();
            match self.memo.get_at(parent, &key) {
                Some(entry)
                    if self
                        .query
                        .can_reuse(&key, &entry, &parent_snapshot, snapshot) =>
                {
                    cancellation.check().map_err(|_| QueryFailure::Cancelled)?;
                    self.memo
                        .publish_reused(snapshot, key.clone(), entry.clone());
                    self.record_execution(
                        snapshot,
                        &key,
                        QueryExecutionKind::ReusedFromParent { parent },
                    );
                    return Ok(entry.result);
                }
                Some(_) => QueryRecomputeReason::ParentReuseRejected { parent },
                None => QueryRecomputeReason::ParentMemoMissing { parent },
            }
        } else if let Some(parent) = snapshot.parent() {
            QueryRecomputeReason::ParentMemoMissing { parent }
        } else {
            QueryRecomputeReason::Cold
        };
        {
            let mut running = self.running.lock().expect("query running mutex poisoned");
            if !running.insert((snapshot.id(), key.clone())) {
                return Err(QueryFailure::Cycle { query: Q::NAME });
            }
        }
        let mut context = QueryContext::new(snapshot, cancellation, budget);
        let result = context
            .charge(1)
            .and_then(|_| self.query.execute(&mut context, key.clone()));
        self.running
            .lock()
            .expect("query running mutex poisoned")
            .remove(&(snapshot.id(), key.clone()));
        let result = result?;
        cancellation.check().map_err(|_| QueryFailure::Cancelled)?;
        self.memo
            .publish(snapshot, key.clone(), result.clone(), context.finish());
        self.record_execution(
            snapshot,
            &key,
            QueryExecutionKind::Recomputed {
                reason: recompute_reason,
            },
        );
        Ok(result)
    }
    pub fn memo(&self) -> &MemoTable<Q::Key, Q::Value> {
        &self.memo
    }
    /// Remove both materialized products and their inspection history for a
    /// collected revision. An executing query always holds a snapshot pin, so
    /// the database safe point cannot call this while the same revision is in
    /// `running`.
    pub fn discard_revision(&self, revision: RevisionId) {
        self.memo.discard_revision(revision);
        self.execution
            .lock()
            .expect("query execution mutex poisoned")
            .retain(|(entry_revision, _), _| *entry_revision != revision);
    }
    /// Number of revision-qualified execution explanations still retained by
    /// this engine. This is deliberately separate from memo counts: a host
    /// can audit that retirement releases both value and provenance state.
    pub fn retained_execution_count(&self) -> u64 {
        u64::try_from(
            self.execution
                .lock()
                .expect("query execution mutex poisoned")
                .len(),
        )
        .expect("query execution entry count exceeds u64")
    }
    /// Explain whether this revision/key was memoized, validated from its
    /// parent, or recomputed. Missing data means no successful publication has
    /// occurred for the requested key, never an implicit cache hit.
    pub fn execution_kind(
        &self,
        snapshot: &DatabaseSnapshot,
        key: &Q::Key,
    ) -> Option<QueryExecutionKind> {
        self.execution
            .lock()
            .expect("query execution mutex poisoned")
            .get(&(snapshot.id(), key.clone()))
            .cloned()
    }
    pub fn why_recomputed(
        &self,
        snapshot: &DatabaseSnapshot,
        key: &Q::Key,
    ) -> Option<QueryRecomputeReason> {
        match self.execution_kind(snapshot, key) {
            Some(QueryExecutionKind::Recomputed { reason }) => Some(reason),
            Some(
                QueryExecutionKind::Memoized { .. } | QueryExecutionKind::ReusedFromParent { .. },
            )
            | None => None,
        }
    }
    fn record_execution(
        &self,
        snapshot: &DatabaseSnapshot,
        key: &Q::Key,
        kind: QueryExecutionKind,
    ) {
        self.execution
            .lock()
            .expect("query execution mutex poisoned")
            .insert((snapshot.id(), key.clone()), kind);
    }
}

impl<Q> RevisionCache for QueryEngine<Q>
where
    Q: Query + Send + Sync,
{
    fn discard_revision(&self, revision: RevisionId) {
        Self::discard_revision(self, revision);
    }
}
