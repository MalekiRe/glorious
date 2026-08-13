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
    revision::DatabaseSnapshot,
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
        self.entries
            .lock()
            .expect("query memo mutex poisoned")
            .get(&(snapshot.id(), key.clone()))
            .cloned()
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
}

impl<Q: Query> QueryEngine<Q> {
    pub fn new(query: Q) -> Self {
        Self {
            query,
            memo: MemoTable::new(),
            running: Mutex::new(HashSet::new()),
        }
    }
    pub fn execute(
        &self,
        snapshot: &DatabaseSnapshot,
        key: Q::Key,
        cancellation: &CancellationToken,
        budget: &Arc<Budget>,
    ) -> Result<QueryValue<Q::Value>, QueryFailure<Q::Error>> {
        if let Some(entry) = self.memo.get(snapshot, &key) {
            return Ok(entry.result);
        }
        cancellation.check().map_err(|_| QueryFailure::Cancelled)?;
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
            .publish(snapshot, key, result.clone(), context.finish());
        Ok(result)
    }
    pub fn memo(&self) -> &MemoTable<Q::Key, Q::Value> {
        &self.memo
    }
}
