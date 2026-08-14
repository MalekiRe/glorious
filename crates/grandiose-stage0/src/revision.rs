use std::{
    collections::{BTreeSet, HashMap},
    sync::{
        Arc, Mutex, Weak,
        atomic::{AtomicBool, Ordering},
    },
};

use crate::{
    dependency::DependencyLedger,
    identity::{Digest, RevisionId, fresh_database_id},
    interface::{InterfaceCache, InterfaceCacheStats},
    operation::{Budget, BudgetError, BudgetLease, CancellationToken},
    request::{CompilationRequest, InputError, NormalizedInputWorld},
};

#[derive(Debug)]
pub enum RevisionError {
    Input(InputError),
    UnknownRevision(RevisionId),
    StaleRevision(RevisionId),
    RetiredRevision(RevisionId),
}

/// Deterministic result of one safe-point retirement sweep. Retired worlds are
/// retained while any `DatabaseSnapshot` or request session still pins them.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RetentionReport {
    pub collected: u64,
    pub retained_pinned: u64,
}

/// Stable, inspection-safe identity for one database-owned immutable world.
/// It deliberately contains no pointers or local arena IDs; callers can keep
/// this after the underlying revision is retired without gaining authority to
/// reopen or mutate that world.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RevisionMetadata {
    pub revision: RevisionId,
    pub parent: Option<RevisionId>,
    pub input_fingerprint: Digest,
}

impl From<InputError> for RevisionError {
    fn from(error: InputError) -> Self {
        Self::Input(error)
    }
}

#[derive(Debug)]
struct RevisionRecord {
    id: RevisionId,
    world: Arc<NormalizedInputWorld>,
    parent: Option<RevisionId>,
    /// A child may inspect its immediate parent while validating a red/green
    /// query result. This is weak so revision ancestry never prevents the
    /// normal safe-point collector from reclaiming retired worlds.
    parent_record: Option<Weak<RevisionRecord>>,
}

#[derive(Debug)]
struct DatabaseState {
    next_ordinal: u64,
    revisions: HashMap<RevisionId, Arc<RevisionRecord>>,
    equivalent_worlds: HashMap<Digest, Weak<RevisionRecord>>,
    retired: BTreeSet<RevisionId>,
}

/// The only owner of database-lifetime compiler state. The current slice owns
/// revisions; typed query memoization, interners, validated interfaces, and
/// cache metadata are added here rather than as phase globals.
#[derive(Debug)]
pub struct CompilerDatabase {
    id: u64,
    state: Mutex<DatabaseState>,
    /// Validated immutable interface products may span revisions, but only
    /// through content/schema-qualified cache keys.
    interface_cache: InterfaceCache,
    dependency_ledger: DependencyLedger,
}

impl Default for CompilerDatabase {
    fn default() -> Self {
        Self::new()
    }
}

impl CompilerDatabase {
    pub fn new() -> Self {
        Self {
            id: fresh_database_id(),
            state: Mutex::new(DatabaseState {
                next_ordinal: 0,
                revisions: HashMap::new(),
                equivalent_worlds: HashMap::new(),
                retired: BTreeSet::new(),
            }),
            interface_cache: InterfaceCache::default(),
            dependency_ledger: DependencyLedger::default(),
        }
    }

    pub fn import(
        &self,
        request: CompilationRequest,
        parent: Option<RevisionId>,
    ) -> Result<RevisionId, RevisionError> {
        let world = Arc::new(request.normalize()?);
        let mut state = self.state.lock().expect("compiler database mutex poisoned");
        let parent_record = parent
            .map(|parent| self.require_active_revision(&state, parent))
            .transpose()?;
        if let Some(existing) = state
            .equivalent_worlds
            .get(&world.fingerprint)
            .and_then(Weak::upgrade)
        {
            return Ok(existing.id);
        }
        let id = RevisionId {
            database: self.id,
            ordinal: state.next_ordinal,
        };
        state.next_ordinal += 1;
        let record = Arc::new(RevisionRecord {
            id,
            world: world.clone(),
            parent,
            parent_record: parent_record.as_ref().map(Arc::downgrade),
        });
        state
            .equivalent_worlds
            .insert(world.fingerprint, Arc::downgrade(&record));
        state.revisions.insert(id, record);
        Ok(id)
    }

    pub fn open(&self, revision: RevisionId) -> Result<DatabaseSnapshot, RevisionError> {
        let state = self.state.lock().expect("compiler database mutex poisoned");
        Ok(DatabaseSnapshot {
            record: self.require_active_revision(&state, revision)?,
        })
    }

    /// Admit one new request against exactly one currently active immutable
    /// revision. Once constructed, the session keeps that world alive even if
    /// a host later retires the revision in favour of a newer editor/build
    /// input world.
    pub fn open_session(&self, revision: RevisionId) -> Result<RequestSession, RevisionError> {
        self.open_session_with_controls(
            revision,
            CancellationToken::new(),
            Budget::root("request", u64::MAX),
        )
    }

    /// Admit a request with host-owned operational controls. Cancellation and
    /// resource budgets affect whether this request is attempted, never the
    /// identity of its immutable semantic world.
    pub fn open_session_with_controls(
        &self,
        revision: RevisionId,
        cancellation: CancellationToken,
        budget: Arc<Budget>,
    ) -> Result<RequestSession, RevisionError> {
        Ok(RequestSession::new(
            self.open(revision)?,
            cancellation,
            budget,
        ))
    }

    /// Check that a session was admitted by this database and that its pinned
    /// record remains one of this database's live records. Retired records are
    /// intentionally accepted here: retirement blocks *new* sessions, never
    /// invalidates an already admitted request.
    pub(crate) fn validate_session(&self, session: &RequestSession) -> Result<(), RevisionError> {
        let snapshot = session.snapshot();
        if snapshot.id().database != self.id {
            return Err(RevisionError::StaleRevision(snapshot.id()));
        }
        let state = self.state.lock().expect("compiler database mutex poisoned");
        let record = self.require_revision(&state, snapshot.id())?;
        if Arc::ptr_eq(&record, &snapshot.record) {
            Ok(())
        } else {
            // Revision ordinals are never reused, so this can only occur if a
            // future boundary constructs a stale handle incorrectly. Fail
            // closed rather than accepting a same-shaped foreign record.
            Err(RevisionError::UnknownRevision(snapshot.id()))
        }
    }

    pub(crate) fn interface_cache(&self) -> &InterfaceCache {
        &self.interface_cache
    }

    pub(crate) fn dependency_ledger(&self) -> &DependencyLedger {
        &self.dependency_ledger
    }

    /// Explain whether a typed compiler product stayed green or which input
    /// first invalidated it in a published revision.
    pub fn dependency_trace(
        &self,
        revision: RevisionId,
        node: &crate::DependencyNode,
    ) -> Option<crate::DependencyTrace> {
        self.dependency_ledger.trace(revision, node)
    }

    pub fn dependency_traces(&self, revision: RevisionId) -> Vec<crate::DependencyTrace> {
        self.dependency_ledger.traces(revision)
    }

    /// Inspection-only accounting for validated frozen interface reuse.  A
    /// hit never means a whole revision was reused; it records exactly one
    /// source/module interface whose bytes and schema identity matched.
    pub fn interface_cache_stats(&self) -> InterfaceCacheStats {
        self.interface_cache.stats()
    }

    /// Stop admitting new sessions for a revision. Existing snapshots retain
    /// the complete immutable world; `collect_retired` only releases it after
    /// those pins disappear.
    pub fn retire_revision(&self, revision: RevisionId) -> Result<(), RevisionError> {
        let mut state = self.state.lock().expect("compiler database mutex poisoned");
        let record = self.require_revision(&state, revision)?;
        state.retired.insert(revision);
        if state
            .equivalent_worlds
            .get(&record.world.fingerprint)
            .and_then(Weak::upgrade)
            .is_some_and(|current| current.id == revision)
        {
            state.equivalent_worlds.remove(&record.world.fingerprint);
        }
        Ok(())
    }

    /// Release every retired revision that has no live snapshot pin. This is
    /// intentionally a safe-point operation: it cannot invalidate a world an
    /// in-flight request has already opened.
    pub fn collect_retired(&self) -> RetentionReport {
        let mut state = self.state.lock().expect("compiler database mutex poisoned");
        let retired = state.retired.iter().copied().collect::<Vec<_>>();
        let mut report = RetentionReport::default();
        for revision in retired {
            let Some(record) = state.revisions.get(&revision) else {
                state.retired.remove(&revision);
                continue;
            };
            // Measure the map-owned Arc directly. Cloning it first would make
            // the collector itself an artificial pin and prevent collection.
            if Arc::strong_count(record) != 1 {
                report.retained_pinned += 1;
                continue;
            }
            let fingerprint = record.world.fingerprint;
            if state
                .equivalent_worlds
                .get(&fingerprint)
                .and_then(Weak::upgrade)
                .is_some_and(|current| current.id == revision)
            {
                state.equivalent_worlds.remove(&fingerprint);
            }
            state.revisions.remove(&revision);
            self.dependency_ledger.remove_revision(revision);
            state.retired.remove(&revision);
            report.collected += 1;
        }
        report
    }

    fn require_revision(
        &self,
        state: &DatabaseState,
        revision: RevisionId,
    ) -> Result<Arc<RevisionRecord>, RevisionError> {
        if revision.database != self.id {
            return Err(RevisionError::StaleRevision(revision));
        }
        state
            .revisions
            .get(&revision)
            .cloned()
            .ok_or(RevisionError::UnknownRevision(revision))
    }

    fn require_active_revision(
        &self,
        state: &DatabaseState,
        revision: RevisionId,
    ) -> Result<Arc<RevisionRecord>, RevisionError> {
        let record = self.require_revision(state, revision)?;
        if state.retired.contains(&revision) {
            Err(RevisionError::RetiredRevision(revision))
        } else {
            Ok(record)
        }
    }
}

/// Immutable, request-scoped revision view. Holding the snapshot pins its
/// world, so a later import can never affect an in-flight semantic query.
#[derive(Clone, Debug)]
pub struct DatabaseSnapshot {
    record: Arc<RevisionRecord>,
}

impl DatabaseSnapshot {
    pub fn id(&self) -> RevisionId {
        self.record.id
    }

    pub fn world(&self) -> &NormalizedInputWorld {
        &self.record.world
    }

    pub fn parent(&self) -> Option<RevisionId> {
        self.record.parent
    }

    pub fn metadata(&self) -> RevisionMetadata {
        RevisionMetadata {
            revision: self.id(),
            parent: self.parent(),
            input_fingerprint: self.world().fingerprint,
        }
    }

    /// Return the immediate immutable parent when it remains retained. A
    /// collected parent is intentionally indistinguishable from a missing
    /// reusable memo entry: a query must fail closed and recompute rather than
    /// make retention an implicit correctness requirement.
    pub fn parent_snapshot(&self) -> Option<Self> {
        self.record
            .parent_record
            .as_ref()
            .and_then(Weak::upgrade)
            .map(|record| Self { record })
    }
}

/// Request-local owner for cancellation, budgets, diagnostics, and atomic
/// publication. The remaining fields become concrete as those services land;
/// the affine API already prevents a caller from switching revisions midway.
#[derive(Debug)]
pub struct RequestSession {
    snapshot: DatabaseSnapshot,
    cancellation: CancellationToken,
    budget: Arc<Budget>,
    /// A request session owns one cancellation/budget/publication lifetime.
    /// It may be inspected while live, but exactly one compiler execution may
    /// claim it; retries must admit a fresh session against an explicit
    /// immutable revision rather than replaying an already-closed transaction.
    execution_claimed: AtomicBool,
}

impl RequestSession {
    fn new(
        snapshot: DatabaseSnapshot,
        cancellation: CancellationToken,
        budget: Arc<Budget>,
    ) -> Self {
        Self {
            snapshot,
            cancellation,
            budget,
            execution_claimed: AtomicBool::new(false),
        }
    }

    pub fn snapshot(&self) -> &DatabaseSnapshot {
        &self.snapshot
    }

    pub fn revision(&self) -> RevisionId {
        self.snapshot.id()
    }

    pub fn metadata(&self) -> RevisionMetadata {
        self.snapshot.metadata()
    }

    pub fn cancellation(&self) -> &CancellationToken {
        &self.cancellation
    }

    pub fn budget(&self) -> &Arc<Budget> {
        &self.budget
    }

    /// Atomically claim this affine session's sole execution slot. A failed,
    /// cancelled, or resource-limited execution remains consumed: its staged
    /// request products have been abandoned and cannot be replayed under a
    /// possibly changed operational context.
    pub(crate) fn claim_execution(&self) -> bool {
        !self.execution_claimed.swap(true, Ordering::AcqRel)
    }

    pub(crate) fn checkpoint(&self, cost: u64) -> Result<BudgetLease, RequestControlError> {
        self.cancellation
            .check()
            .map_err(|_| RequestControlError::Cancelled)?;
        self.budget
            .lease(cost)
            .map_err(RequestControlError::Resource)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RequestControlError {
    Cancelled,
    Resource(BudgetError),
}
