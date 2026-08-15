use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    sync::{
        Arc, Mutex, Weak,
        atomic::{AtomicBool, Ordering},
    },
};

use crate::{
    dependency::DependencyLedger,
    identity::{Digest, PackageKey, RevisionId, fresh_database_id},
    interface::{InterfaceCache, InterfaceCacheStats},
    operation::{Budget, BudgetError, CancellationToken},
    request::{CompilationRequest, InputError, NormalizedInputWorld},
};

/// A database-owned cache that holds products keyed by a revision.  Cache
/// owners register weakly with the database so retirement can release stale
/// products at the same safe point as their immutable input world.  The
/// callback runs only after the revision record has been removed and no
/// snapshot can still observe that revision.
pub trait RevisionCache: Send + Sync {
    fn discard_revision(&self, revision: RevisionId);
}

/// Weak registrations intentionally do not keep optional query families
/// alive.  A host that drops a query engine should not leave a database-owned
/// retention root behind merely because it once used the engine.
#[derive(Default)]
struct RevisionCacheRegistry {
    caches: Mutex<Vec<Weak<dyn RevisionCache>>>,
}

impl std::fmt::Debug for RevisionCacheRegistry {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let registered = self
            .caches
            .lock()
            .expect("revision cache registry mutex poisoned")
            .len();
        formatter
            .debug_struct("RevisionCacheRegistry")
            .field("registered", &registered)
            .finish()
    }
}

impl RevisionCacheRegistry {
    fn register<C: RevisionCache + 'static>(&self, cache: &Arc<C>) {
        let cache: Arc<dyn RevisionCache> = cache.clone();
        let weak = Arc::downgrade(&cache);
        let mut caches = self
            .caches
            .lock()
            .expect("revision cache registry mutex poisoned");
        caches.retain(|registered| registered.strong_count() != 0);
        if !caches.iter().any(|registered| registered.ptr_eq(&weak)) {
            caches.push(weak);
        }
    }

    fn discard_revision(&self, revision: RevisionId) {
        // Do not invoke cache code while holding the registry lock. A query
        // family may have its own locks and may itself release its final Arc
        // during eviction.
        let caches = {
            let mut registered = self
                .caches
                .lock()
                .expect("revision cache registry mutex poisoned");
            let live = registered
                .iter()
                .filter_map(Weak::upgrade)
                .collect::<Vec<_>>();
            registered.retain(|cache| cache.strong_count() != 0);
            live
        };
        for cache in caches {
            cache.discard_revision(revision);
        }
    }
}

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

/// Inspection-safe retention accounting for database-owned immutable worlds.
///
/// These are ownership counts rather than allocator-byte estimates: shared
/// `Arc` capacity cannot be attributed reliably, while revision pins are the
/// bounded lifetimes a host must be able to diagnose without seeing private
/// source, interface, or query-cache data.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RetentionStats {
    /// Worlds currently retained by the database, whether active or retired.
    pub retained_revisions: u64,
    /// Retained worlds that no longer admit new snapshots or requests.
    pub retired_revisions: u64,
    /// Retained worlds with one or more outstanding snapshot/request pins.
    pub pinned_revisions: u64,
    /// Exact outstanding pins beyond the database revision-map references.
    pub snapshot_pins: u64,
}

/// Inspection-safe lifecycle state for a single retained revision.  The
/// database-local revision key makes pin reports stable without exposing an
/// `Arc`, pointer, source blob, or query product to the caller.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RevisionRetentionMetadata {
    pub revision: RevisionId,
    pub retired: bool,
    pub snapshot_pins: u64,
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

/// The request-visible lifecycle of one demanded package.  These states own
/// only request-local publication authority; package source bytes, frozen
/// interfaces, and database services remain borrowed through the immutable
/// request snapshot.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageSessionStatus {
    /// A package session owns mutable body/interface staging.
    Open,
    /// Its local products are complete, but the enclosing request has not
    /// crossed its single publication boundary yet.
    Staged,
    /// The request published successfully, so the staged package participates
    /// in its immutable outcome.
    Committed,
    /// The package's mutable staging was abandoned.  It cannot be reopened
    /// under this request, which prevents a failed transaction from being
    /// retried with partially retained state.
    RolledBack,
}

/// Inspection-safe state for an entry in a request-owned package registry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageSessionMetadata {
    pub package: PackageKey,
    pub status: PackageSessionStatus,
}

/// Failure to admit or publish package-local work through a request session.
/// These are lifecycle failures rather than source diagnostics: all package
/// identities are validated against the already-pinned immutable world.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PackageSessionError {
    PackageNotInRequest(PackageKey),
    PackageAlreadyActive(PackageKey),
    PackageNotOpen(PackageKey),
    RequestRolledBack,
    UnstagedPackages(Vec<PackageKey>),
}

#[derive(Debug)]
struct PackageSessionRegistry {
    /// The request may open only packages named by its immutable input world.
    /// This guards against a mutable service worklist becoming a backdoor for
    /// ambient packages or source blobs.
    permitted: BTreeSet<PackageKey>,
    states: Mutex<BTreeMap<PackageKey, PackageSessionStatus>>,
}

impl PackageSessionRegistry {
    fn for_snapshot(snapshot: &DatabaseSnapshot) -> Self {
        let mut permitted = snapshot
            .world()
            .sources
            .iter()
            .map(|source| source.package.clone())
            .collect::<BTreeSet<_>>();
        permitted.insert(snapshot.world().root_package.clone());
        Self {
            permitted,
            states: Mutex::new(BTreeMap::new()),
        }
    }

    fn open(&self, package: &PackageKey) -> Result<(), PackageSessionError> {
        if !self.permitted.contains(package) {
            return Err(PackageSessionError::PackageNotInRequest(package.clone()));
        }
        let mut states = self
            .states
            .lock()
            .expect("package session registry mutex poisoned");
        if states
            .values()
            .any(|status| *status == PackageSessionStatus::RolledBack)
        {
            return Err(PackageSessionError::RequestRolledBack);
        }
        if states.contains_key(package) {
            return Err(PackageSessionError::PackageAlreadyActive(package.clone()));
        }
        states.insert(package.clone(), PackageSessionStatus::Open);
        Ok(())
    }

    fn stage(&self, package: &PackageKey) -> Result<(), PackageSessionError> {
        let mut states = self
            .states
            .lock()
            .expect("package session registry mutex poisoned");
        match states.get_mut(package) {
            Some(status @ PackageSessionStatus::Open) => {
                *status = PackageSessionStatus::Staged;
                Ok(())
            }
            _ => Err(PackageSessionError::PackageNotOpen(package.clone())),
        }
    }

    fn commit_all(&self) -> Result<(), PackageSessionError> {
        let mut states = self
            .states
            .lock()
            .expect("package session registry mutex poisoned");
        let unstaged = states
            .iter()
            .filter_map(|(package, status)| {
                (*status != PackageSessionStatus::Staged).then(|| package.clone())
            })
            .collect::<Vec<_>>();
        if !unstaged.is_empty() {
            return Err(PackageSessionError::UnstagedPackages(unstaged));
        }
        // Validate before changing any entry: publication is all-or-nothing
        // across the request's demanded package set.
        for status in states.values_mut() {
            *status = PackageSessionStatus::Committed;
        }
        Ok(())
    }

    fn rollback(&self, package: &PackageKey) {
        let mut states = self
            .states
            .lock()
            .expect("package session registry mutex poisoned");
        if let Some(status @ (PackageSessionStatus::Open | PackageSessionStatus::Staged)) =
            states.get_mut(package)
        {
            *status = PackageSessionStatus::RolledBack;
        }
    }

    fn rollback_all(&self) {
        let mut states = self
            .states
            .lock()
            .expect("package session registry mutex poisoned");
        for status in states.values_mut() {
            if matches!(
                status,
                PackageSessionStatus::Open | PackageSessionStatus::Staged
            ) {
                *status = PackageSessionStatus::RolledBack;
            }
        }
    }

    fn metadata(&self) -> Vec<PackageSessionMetadata> {
        self.states
            .lock()
            .expect("package session registry mutex poisoned")
            .iter()
            .map(|(package, status)| PackageSessionMetadata {
                package: package.clone(),
                status: *status,
            })
            .collect()
    }
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
    revision_caches: RevisionCacheRegistry,
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
            revision_caches: RevisionCacheRegistry::default(),
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

    /// Register a revision-qualified cache for safe-point reclamation. The
    /// database retains only a weak registration; callers keep normal
    /// ownership of their cache engine. Re-registering the same allocation is
    /// idempotent.
    pub fn register_revision_cache<C: RevisionCache + 'static>(&self, cache: &Arc<C>) {
        self.revision_caches.register(cache);
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

    /// Return bounded retention accounting without exposing cache keys,
    /// source bytes, or allocator implementation details. A nonzero pin count
    /// on a retired revision is an observable leaked-pin candidate; it is not
    /// a semantic dependency and does not grant access to the retired world.
    pub fn retention_stats(&self) -> RetentionStats {
        let state = self.state.lock().expect("compiler database mutex poisoned");
        let mut stats = RetentionStats {
            retained_revisions: u64::try_from(state.revisions.len())
                .expect("revision count exceeds u64"),
            retired_revisions: u64::try_from(state.retired.len())
                .expect("retired revision count exceeds u64"),
            ..RetentionStats::default()
        };
        for record in state.revisions.values() {
            // The revisions map owns one strong reference. Every additional
            // one is a live immutable view held by a snapshot, request
            // session, or temporary query/inspection operation.
            let pins = u64::try_from(Arc::strong_count(record).saturating_sub(1))
                .expect("snapshot pin count exceeds u64");
            stats.snapshot_pins = stats
                .snapshot_pins
                .checked_add(pins)
                .expect("total snapshot pin count overflow");
            if pins != 0 {
                stats.pinned_revisions = stats
                    .pinned_revisions
                    .checked_add(1)
                    .expect("pinned revision count overflow");
            }
        }
        stats
    }

    /// Inspect one retained revision's lifecycle state. Retired revisions
    /// remain reportable while pinned; after collection the normal stale/absent
    /// revision error preserves the fail-closed ownership boundary.
    pub fn revision_retention(
        &self,
        revision: RevisionId,
    ) -> Result<RevisionRetentionMetadata, RevisionError> {
        let state = self.state.lock().expect("compiler database mutex poisoned");
        if revision.database != self.id {
            return Err(RevisionError::StaleRevision(revision));
        }
        // Inspect the database-owned Arc in place. Calling `require_revision`
        // here would clone it first and turn this inspection operation into a
        // spurious extra pin in the very count it reports.
        let record = state
            .revisions
            .get(&revision)
            .ok_or(RevisionError::UnknownRevision(revision))?;
        Ok(RevisionRetentionMetadata {
            revision,
            retired: state.retired.contains(&revision),
            snapshot_pins: u64::try_from(Arc::strong_count(record).saturating_sub(1))
                .expect("snapshot pin count exceeds u64"),
        })
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
        let mut collected = vec![];
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
            state.retired.remove(&revision);
            collected.push(revision);
            report.collected += 1;
        }
        drop(state);
        // Reclamation crosses component boundaries only after the database
        // map no longer admits the revision. This preserves the fail-closed
        // stale-handle boundary even if a cache's eviction code is reentrant.
        for revision in collected {
            self.dependency_ledger.remove_revision(revision);
            self.revision_caches.discard_revision(revision);
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
    /// Request-owned registry of package-local mutable lifetimes.  It tracks
    /// authority and publication state only; all semantic inputs continue to
    /// come from `snapshot` and are never copied into a package session.
    package_sessions: PackageSessionRegistry,
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
            package_sessions: PackageSessionRegistry::for_snapshot(&snapshot),
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

    /// Issue the root-owned budget for one mutable package session.  A
    /// package budget is not an independent allowance: every charge also
    /// charges the request parent, which keeps sibling packages beneath the
    /// request cap without ambient accounting.
    pub(crate) fn package_budget(&self) -> Arc<Budget> {
        self.budget.child("package", self.budget.ceiling())
    }

    /// Issue the root-owned budget for final artifact construction.  It is
    /// deliberately separate from package work so cancellation or failure can
    /// drop the emission staging and its accounting owner together.
    pub(crate) fn emission_budget(&self) -> Arc<Budget> {
        self.budget.child("emission", self.budget.ceiling())
    }

    /// Return the package-session lifecycle observed by this request.  This
    /// is an inspection API: it grants neither mutable package authority nor
    /// access to source inputs beyond the request's immutable snapshot.
    pub fn package_sessions(&self) -> Vec<PackageSessionMetadata> {
        self.package_sessions.metadata()
    }

    /// Admit the one mutable staging owner for `package`.  Service code holds
    /// the returned lease while it performs package work; dropping an
    /// un-staged lease rolls that package back automatically.
    pub(crate) fn open_package_session(
        &self,
        package: PackageKey,
    ) -> Result<PackageSessionLease<'_>, PackageSessionError> {
        self.package_sessions.open(&package)?;
        Ok(PackageSessionLease {
            registry: &self.package_sessions,
            package,
            staged: false,
        })
    }

    /// Atomically commit every staged package after the request's final
    /// cancellation check has succeeded.  This is deliberately separate from
    /// package staging so an error in any later phase can still abandon all
    /// request-local products together.
    pub(crate) fn commit_package_sessions(&self) -> Result<(), PackageSessionError> {
        self.package_sessions.commit_all()
    }

    /// Abandon every mutable package product in the request.  The registry
    /// retains only terminal lifecycle metadata; it never retains the staged
    /// bodies, interfaces, or source bytes themselves.
    pub(crate) fn rollback_package_sessions(&self) {
        self.package_sessions.rollback_all();
    }

    /// Atomically claim this affine session's sole execution slot. A failed,
    /// cancelled, or resource-limited execution remains consumed: its staged
    /// request products have been abandoned and cannot be replayed under a
    /// possibly changed operational context.
    pub(crate) fn claim_execution(&self) -> bool {
        !self.execution_claimed.swap(true, Ordering::AcqRel)
    }

    /// Poll cancellation and consume deterministic request work. Unlike a
    /// temporary allocation reservation, compiler work is not released when a
    /// phase returns: otherwise a long request could repeatedly pass a
    /// zero-cost checkpoint while exceeding its advertised resource ceiling.
    pub(crate) fn checkpoint(&self, cost: u64) -> Result<(), RequestControlError> {
        self.checkpoint_in(&self.budget, cost)
    }

    /// Poll the request control plane while charging a phase-owned child
    /// budget.  `Budget::charge` propagates to all parents, so this cannot
    /// bypass the request ceiling even though service phases own distinct
    /// child budgets.
    pub(crate) fn checkpoint_in(
        &self,
        budget: &Arc<Budget>,
        cost: u64,
    ) -> Result<(), RequestControlError> {
        self.cancellation
            .check()
            .map_err(|_| RequestControlError::Cancelled)?;
        budget.charge(cost).map_err(RequestControlError::Resource)
    }
}

/// Affine authority to stage one package through its owning request.  This is
/// intentionally crate-private: a public host can inspect request state, but
/// only the compiler service may mutate package-local semantic staging.
#[derive(Debug)]
pub(crate) struct PackageSessionLease<'request> {
    registry: &'request PackageSessionRegistry,
    package: PackageKey,
    staged: bool,
}

impl PackageSessionLease<'_> {
    pub(crate) fn stage(mut self) -> Result<(), PackageSessionError> {
        self.registry.stage(&self.package)?;
        self.staged = true;
        Ok(())
    }
}

impl Drop for PackageSessionLease<'_> {
    fn drop(&mut self) {
        if !self.staged {
            self.registry.rollback(&self.package);
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RequestControlError {
    Cancelled,
    Resource(BudgetError),
}
