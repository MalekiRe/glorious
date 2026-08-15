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

/// Whether a query family may intentionally produce or consume a recovered
/// semantic product. Recovery is an explicit typed policy rather than a
/// property a parent may erase while constructing its own result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum QueryRecoveryPolicy {
    Reject,
    Allow,
}

impl QueryRecoveryPolicy {
    fn allows_recovery(self) -> bool {
        matches!(self, Self::Allow)
    }
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

/// The in-progress affine owner of one query evaluation. It records exact typed
/// dependencies in demand order. A frame has one terminal transition: it is
/// either consumed by a [`QueryPublicationGuard`] or explicitly aborted. An
/// abandoned frame rolls its staging back on drop, so an error, cancellation,
/// or unwind cannot leave query-local dependency state available for a later
/// publication.
#[derive(Debug)]
pub struct QueryFrame {
    revision: RevisionId,
    state: QueryFrameState,
}

#[derive(Debug)]
enum QueryFrameState {
    Open {
        dependencies: Vec<Dependency>,
        recovered_dependency: bool,
    },
    /// A frame is only marked committed after its canonical dependency journal
    /// has been transferred to the publication guard.
    Committed,
    /// Abort is idempotent, which makes destruction safe on every failure path.
    Aborted,
}

impl QueryFrame {
    pub fn new(snapshot: &DatabaseSnapshot) -> Self {
        Self {
            revision: snapshot.id(),
            state: QueryFrameState::Open {
                dependencies: vec![],
                recovered_dependency: false,
            },
        }
    }

    pub fn depend(&mut self, query: &'static str, fingerprint: Digest) {
        if let QueryFrameState::Open { dependencies, .. } = &mut self.state {
            dependencies.push(Dependency {
                revision: self.revision,
                query,
                fingerprint,
            });
        } else {
            panic!("cannot record a dependency after a query frame has closed");
        }
    }

    fn depend_on_recovered_product(&mut self) {
        if let QueryFrameState::Open {
            recovered_dependency,
            ..
        } = &mut self.state
        {
            *recovered_dependency = true;
        } else {
            panic!("cannot record recovery after a query frame has closed");
        }
    }

    fn contains_recovered_dependency(&self) -> bool {
        match &self.state {
            QueryFrameState::Open {
                recovered_dependency,
                ..
            } => *recovered_dependency,
            QueryFrameState::Committed | QueryFrameState::Aborted => false,
        }
    }

    /// Explicitly abandon the frame's provisional journal. This is normally
    /// performed by `Drop`, but keeping it explicit is useful at a boundary
    /// that wants to release potentially large staged dependency sets early.
    pub fn abort(&mut self) {
        let previous = std::mem::replace(&mut self.state, QueryFrameState::Aborted);
        drop(previous);
    }

    fn commit(mut self) -> Vec<Dependency> {
        let state = std::mem::replace(&mut self.state, QueryFrameState::Committed);
        let QueryFrameState::Open {
            mut dependencies, ..
        } = state
        else {
            panic!("query frame must be open when it is committed");
        };
        canonicalize_dependencies(&mut dependencies);
        dependencies
    }

    /// Finish a standalone frame. Query execution uses
    /// [`QueryPublicationGuard`] instead, so its dependency journal and value
    /// become visible atomically in one terminal operation.
    pub fn finish(self) -> Vec<Dependency> {
        self.commit()
    }
}

impl Drop for QueryFrame {
    fn drop(&mut self) {
        if matches!(&self.state, QueryFrameState::Open { .. }) {
            self.abort();
        }
    }
}

fn canonicalize_dependencies(dependencies: &mut Vec<Dependency>) {
    dependencies.sort_by(|left, right| {
        (left.revision, left.query, left.fingerprint).cmp(&(
            right.revision,
            right.query,
            right.fingerprint,
        ))
    });
    dependencies.dedup();
}

#[derive(Clone, Debug)]
pub struct MemoEntry<V> {
    pub result: QueryValue<V>,
    pub dependencies: Vec<Dependency>,
}

/// Inspection-safe accounting for the immutable products retained by one
/// query family.  Counts deliberately describe ownership classes instead of
/// keys, values, source text, or dependency identities: a host can audit cache
/// pressure without gaining authority to inspect another request's products.
///
/// A memoized product owns one canonical dependency journal.  Execution
/// explanations are tracked separately because they are provenance-only state
/// and must be reclaimed with the product at the same revision safe point.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct QueryRetentionStats {
    /// Complete or explicitly recovered immutable query values.
    pub retained_products: u64,
    /// Exact canonical dependency edges retained by those products.
    pub retained_dependency_edges: u64,
    /// Revision-qualified memo/reuse/recompute explanations.
    pub retained_execution_explanations: u64,
}

impl QueryRetentionStats {
    fn products<K, V>(entries: &HashMap<(RevisionId, K), MemoEntry<V>>) -> Self
    where
        K: Eq + Hash,
    {
        let mut stats = Self::default();
        for entry in entries.values() {
            stats.record_product(entry);
        }
        stats
    }

    fn record_product<V>(&mut self, entry: &MemoEntry<V>) {
        self.retained_products = self
            .retained_products
            .checked_add(1)
            .expect("query memo entry count overflow");
        self.retained_dependency_edges = self
            .retained_dependency_edges
            .checked_add(
                u64::try_from(entry.dependencies.len())
                    .expect("query dependency edge count exceeds u64"),
            )
            .expect("query dependency edge count overflow");
    }

    fn add_execution_explanations(mut self, count: usize) -> Self {
        self.retained_execution_explanations =
            u64::try_from(count).expect("query execution entry count exceeds u64");
        self
    }
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

/// The sole publication capability for a completed query frame. It owns the
/// typed key and the provisional frame until `commit` atomically transfers the
/// canonical dependency journal with the value. Dropping it aborts the frame.
#[must_use = "a query publication guard must be committed or will abort on drop"]
pub struct QueryPublicationGuard<'a, K, V> {
    memo: &'a MemoTable<K, V>,
    snapshot: &'a DatabaseSnapshot,
    key: Option<K>,
    frame: Option<QueryFrame>,
}

impl<K, V> QueryPublicationGuard<'_, K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    /// Atomically make a value and this frame's canonical dependency journal
    /// visible. The consuming transition makes double-publication impossible.
    pub fn commit(mut self, result: QueryValue<V>) {
        let key = self
            .key
            .take()
            .expect("query publication guard must own a key until commit");
        let frame = self
            .frame
            .take()
            .expect("query publication guard must own an open frame until commit");
        assert_eq!(
            self.snapshot.id(),
            frame.revision,
            "query frame crossed revisions"
        );
        let dependencies = frame.commit();
        self.memo
            .entries
            .lock()
            .expect("query memo mutex poisoned")
            .insert(
                (self.snapshot.id(), key),
                MemoEntry {
                    result,
                    dependencies,
                },
            );
    }
}

impl<K, V> Drop for QueryPublicationGuard<'_, K, V> {
    fn drop(&mut self) {
        if let Some(mut frame) = self.frame.take() {
            frame.abort();
        }
    }
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

    fn discard_revision_with_stats(&self, revision: RevisionId) -> QueryRetentionStats {
        let mut entries = self.entries.lock().expect("query memo mutex poisoned");
        let mut discarded = QueryRetentionStats::default();
        entries.retain(|(entry_revision, _), entry| {
            if *entry_revision == revision {
                discarded.record_product(entry);
                false
            } else {
                true
            }
        });
        discarded
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

    /// Return all retention classes owned by this memo table.  This is useful
    /// for a cache family that owns products but no execution provenance.
    pub fn retention_stats(&self) -> QueryRetentionStats {
        let entries = self.entries.lock().expect("query memo mutex poisoned");
        QueryRetentionStats::products(&entries)
    }

    /// Revision-qualified retention accounting that exposes neither memo keys
    /// nor values.  Collected and never-published revisions report zero.
    pub fn retention_stats_for_revision(&self, revision: RevisionId) -> QueryRetentionStats {
        let entries = self.entries.lock().expect("query memo mutex poisoned");
        let mut stats = QueryRetentionStats::default();
        for ((entry_revision, _), entry) in entries.iter() {
            if *entry_revision == revision {
                stats.record_product(entry);
            }
        }
        stats
    }

    /// Begin the sole publication path for a completed frame. Until its guard
    /// is committed, the key and dependency journal remain private staging.
    pub fn begin_publication<'a>(
        &'a self,
        snapshot: &'a DatabaseSnapshot,
        key: K,
        frame: QueryFrame,
    ) -> QueryPublicationGuard<'a, K, V> {
        assert_eq!(
            snapshot.id(),
            frame.revision,
            "query frame crossed revisions"
        );
        QueryPublicationGuard {
            memo: self,
            snapshot,
            key: Some(key),
            frame: Some(frame),
        }
    }

    /// Convenience for callers that already have a complete product. Engine
    /// execution prefers `begin_publication` so cancellation is checked while
    /// the guard still owns all provisional state.
    pub fn publish(
        &self,
        snapshot: &DatabaseSnapshot,
        key: K,
        result: QueryValue<V>,
        frame: QueryFrame,
    ) {
        self.begin_publication(snapshot, key, frame).commit(result);
    }

    /// Re-publish a query-family-validated parent result under a child
    /// revision. Dependencies retain their exact producer/fingerprint but are
    /// rewritten to the child revision because validation has established that
    /// these are the child world's observed facts too.
    fn publish_reused(&self, snapshot: &DatabaseSnapshot, key: K, parent: MemoEntry<V>) {
        let mut dependencies = parent
            .dependencies
            .into_iter()
            .map(|dependency| Dependency {
                revision: snapshot.id(),
                query: dependency.query,
                fingerprint: dependency.fingerprint,
            })
            .collect::<Vec<_>>();
        // Parent entries are already canonical, but validate reuse through the
        // same deterministic publication boundary rather than relying on that
        // implementation detail forever.
        canonicalize_dependencies(&mut dependencies);
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
    ResourceLimit {
        name: &'static str,
        limit: u64,
    },
    Invariant(&'static str),
    Cycle {
        query: &'static str,
    },
    /// A complete-only query attempted to observe a provisional result, or a
    /// query attempted to publish recovery without declaring that policy.
    RecoveredProduct {
        query: &'static str,
    },
}

/// The only authority granted to a running query. Nested queries record their
/// observed products here; cancellation and budget checks stay at structural
/// boundaries instead of being ambient process state.
pub struct QueryContext<'a> {
    snapshot: &'a DatabaseSnapshot,
    cancellation: &'a CancellationToken,
    budget: &'a Arc<Budget>,
    recovery_policy: QueryRecoveryPolicy,
    frame: QueryFrame,
}

impl<'a> QueryContext<'a> {
    fn new(
        snapshot: &'a DatabaseSnapshot,
        cancellation: &'a CancellationToken,
        budget: &'a Arc<Budget>,
        recovery_policy: QueryRecoveryPolicy,
    ) -> Self {
        Self {
            snapshot,
            cancellation,
            budget,
            recovery_policy,
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
        if result.completeness == QueryCompleteness::Recovered {
            if !self.recovery_policy.allows_recovery() {
                return Err(QueryFailure::RecoveredProduct { query: Q::NAME });
            }
            self.frame.depend_on_recovered_product();
        }
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

    /// Recovery-capable queries are tooling-facing by default. A release or
    /// complete-only query must opt in before it can consume a recovered child
    /// or publish a recovered result of its own.
    const RECOVERY_POLICY: QueryRecoveryPolicy = QueryRecoveryPolicy::Reject;

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

/// Removes the execution marker even when a query panics. Panics remain
/// invariant failures for the caller, but they must not poison this key into a
/// permanent synthetic cycle for every later request.
struct RunningQueryGuard<'a, K: Eq + Hash> {
    running: &'a Mutex<HashSet<(RevisionId, K)>>,
    entry: Option<(RevisionId, K)>,
}

impl<K> Drop for RunningQueryGuard<'_, K>
where
    K: Eq + Hash,
{
    fn drop(&mut self) {
        if let Some(entry) = self.entry.take() {
            self.running
                .lock()
                .expect("query running mutex poisoned")
                .remove(&entry);
        }
    }
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
            if entry.result.completeness == QueryCompleteness::Recovered
                && !Q::RECOVERY_POLICY.allows_recovery()
            {
                return Err(QueryFailure::RecoveredProduct { query: Q::NAME });
            }
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
                    if entry.result.completeness == QueryCompleteness::Recovered
                        && !Q::RECOVERY_POLICY.allows_recovery()
                    {
                        return Err(QueryFailure::RecoveredProduct { query: Q::NAME });
                    }
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
        let running = {
            let mut running = self.running.lock().expect("query running mutex poisoned");
            if !running.insert((snapshot.id(), key.clone())) {
                return Err(QueryFailure::Cycle { query: Q::NAME });
            }
            RunningQueryGuard {
                running: &self.running,
                entry: Some((snapshot.id(), key.clone())),
            }
        };
        let mut context = QueryContext::new(snapshot, cancellation, budget, Q::RECOVERY_POLICY);
        let result = context
            .charge(1)
            .and_then(|_| self.query.execute(&mut context, key.clone()));
        let mut result = result?;
        let frame = context.finish();
        if frame.contains_recovered_dependency() {
            result.completeness = QueryCompleteness::Recovered;
        }
        if result.completeness == QueryCompleteness::Recovered
            && !Q::RECOVERY_POLICY.allows_recovery()
        {
            return Err(QueryFailure::RecoveredProduct { query: Q::NAME });
        }
        // From here until commit the guard affinely owns the key and complete
        // dependency journal. A late cancellation takes the error path below,
        // drops the guard, and cannot expose either as a memo entry.
        let publication = self.memo.begin_publication(snapshot, key.clone(), frame);
        cancellation.check().map_err(|_| QueryFailure::Cancelled)?;
        publication.commit(result.clone());
        // A re-entrant demand may only observe a completed memo entry. Keep
        // the cycle marker live through the atomic publication boundary.
        drop(running);
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
    /// collected revision. The returned counts make the release observable to
    /// bounded-retention hosts without exposing the discarded products. An
    /// executing query always holds a snapshot pin, so the database safe point
    /// cannot call this while the same revision is in `running`.
    pub fn discard_revision(&self, revision: RevisionId) -> QueryRetentionStats {
        let mut discarded = self.memo.discard_revision_with_stats(revision);
        let mut execution = self
            .execution
            .lock()
            .expect("query execution mutex poisoned");
        let before = execution.len();
        execution.retain(|(entry_revision, _), _| *entry_revision != revision);
        discarded.retained_execution_explanations = u64::try_from(before - execution.len())
            .expect("query execution entry count exceeds u64");
        discarded
    }

    /// Inspection-safe counts for every retention class owned by this query
    /// family. This reports products, their dependency journals, and cache
    /// provenance together because retirement must reclaim all three.
    pub fn retention_stats(&self) -> QueryRetentionStats {
        let memo = self.memo.retention_stats();
        let execution = self
            .execution
            .lock()
            .expect("query execution mutex poisoned")
            .len();
        memo.add_execution_explanations(execution)
    }

    /// Inspect the retained footprint of one revision within this family.
    /// The result contains counts only and is therefore safe for tooling to
    /// request even when it cannot open the revision itself.
    pub fn retention_stats_for_revision(&self, revision: RevisionId) -> QueryRetentionStats {
        let memo = self.memo.retention_stats_for_revision(revision);
        let execution = self
            .execution
            .lock()
            .expect("query execution mutex poisoned")
            .keys()
            .filter(|(entry_revision, _)| *entry_revision == revision)
            .count();
        memo.add_execution_explanations(execution)
    }
    /// Number of revision-qualified execution explanations still retained by
    /// this engine. This is deliberately separate from memo counts: a host
    /// can audit that retirement releases both value and provenance state.
    pub fn retained_execution_count(&self) -> u64 {
        self.retention_stats().retained_execution_explanations
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
