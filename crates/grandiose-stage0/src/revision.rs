use std::{
    collections::{BTreeSet, HashMap},
    sync::{Arc, Mutex, Weak},
};

use crate::{
    identity::{Digest, RevisionId, fresh_database_id},
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
}

impl RequestSession {
    pub fn new(snapshot: DatabaseSnapshot) -> Self {
        Self { snapshot }
    }

    pub fn snapshot(&self) -> &DatabaseSnapshot {
        &self.snapshot
    }
}
