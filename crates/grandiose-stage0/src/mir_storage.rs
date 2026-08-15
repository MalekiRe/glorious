//! Persistent source-storage lifetime facts at the PlaceFlow-to-MIR boundary.
//!
//! Compact Stage-0 register MIR does not yet serialize source `StorageLive`
//! and `StorageDead` opcodes.  It nevertheless must retain their exact typed
//! contract: no later cleanup or lowering pass may reconstruct a storage
//! lifetime from a local spelling, register number, or source span.  This
//! module carries that contract as one immutable arena and validates the
//! equivalent live/dead sequence for every lexical source scope.

use crate::{
    mir::{MirLocal, MirMovePathId, MirMovePathTables, MirPlaceBindingId},
    placeflow::{PlaceFlow, SourceStorageScopeId},
};
use std::collections::BTreeSet;

/// Body-local MIR identity for a source-storage scope. It deliberately wraps
/// the PlaceFlow identity so it cannot be mixed with label/handler scopes.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MirSourceStorageScopeId(pub u32);

impl MirSourceStorageScopeId {
    pub const ROOT: Self = Self(0);
}

/// Typed source-storage event. These are semantic statements at the MIR
/// boundary even though the current register VM erases them after validation:
/// live makes an addressable source slot available, and dead asserts it has
/// been moved or otherwise disarmed and has no live loan.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MirStorageEventKind {
    Live,
    Dead,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MirStorageEvent {
    pub kind: MirStorageEventKind,
    pub binding: MirPlaceBindingId,
}

/// One immutable scope in the source-storage arena. `events` is exactly the
/// `StorageLive` sequence followed by reverse-initialization `StorageDead`;
/// cleanup elaboration may insert destruction between those two phases but
/// cannot reorder either phase.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirSourceStorageScopeData {
    pub source: SourceStorageScopeId,
    pub parent: Option<MirSourceStorageScopeId>,
    pub bindings: Vec<MirPlaceBindingId>,
    pub events: Vec<MirStorageEvent>,
}

/// Frozen source-storage/lifetime data. The vector position is the dense
/// MIR identity and `binding_scopes` is parallel to the frozen move-binding
/// arena, making scope provenance available to cleanup without a text lookup.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirSourceStorageTables {
    pub scopes: Vec<MirSourceStorageScopeData>,
    pub binding_scopes: Vec<MirSourceStorageScopeId>,
    /// Optional executable local for each source storage binding. `None` is
    /// valid only for a binder whose compact lowering currently carries its
    /// storage solely through a block/handler payload; it must never be
    /// filled by guessing from a spelling.
    pub binding_locals: Vec<Option<MirLocal>>,
}

impl Default for MirSourceStorageTables {
    fn default() -> Self {
        Self {
            scopes: vec![MirSourceStorageScopeData {
                source: SourceStorageScopeId::ROOT,
                parent: None,
                bindings: vec![],
                events: vec![],
            }],
            binding_scopes: vec![],
            binding_locals: vec![],
        }
    }
}

impl MirSourceStorageTables {
    /// Import the analyzer's lexical scope arena without resolving any source
    /// spelling.  A malformed PlaceFlow product is represented faithfully and
    /// rejected by [`Self::validate`] at the normal MIR boundary.
    pub fn from_placeflow(flow: &PlaceFlow) -> Self {
        let scopes = flow
            .storage_scopes
            .iter()
            .map(|scope| {
                let bindings = scope
                    .bindings
                    .iter()
                    .map(|binding| MirPlaceBindingId(binding.0))
                    .collect::<Vec<_>>();
                let events = bindings
                    .iter()
                    .copied()
                    .map(|binding| MirStorageEvent {
                        kind: MirStorageEventKind::Live,
                        binding,
                    })
                    .chain(
                        bindings
                            .iter()
                            .rev()
                            .copied()
                            .map(|binding| MirStorageEvent {
                                kind: MirStorageEventKind::Dead,
                                binding,
                            }),
                    )
                    .collect();
                MirSourceStorageScopeData {
                    source: scope.id,
                    parent: scope.parent.map(|parent| MirSourceStorageScopeId(parent.0)),
                    bindings,
                    events,
                }
            })
            .collect();
        Self {
            scopes,
            binding_scopes: flow
                .binding_scopes
                .iter()
                .map(|scope| MirSourceStorageScopeId(scope.0))
                .collect(),
            binding_locals: vec![None; flow.bindings.len()],
        }
    }

    pub fn validate(&self, paths: &MirMovePathTables) -> Result<(), String> {
        let Some(root) = self.scopes.first() else {
            return Err("MIR source-storage table has no root scope".into());
        };
        if root.source != SourceStorageScopeId::ROOT || root.parent.is_some() {
            return Err("MIR source-storage root is malformed".into());
        }
        if self.binding_scopes.len() != paths.bindings.len() {
            return Err("MIR source-storage bindings do not cover frozen move bindings".into());
        }
        if self.binding_locals.len() != paths.bindings.len() {
            return Err(
                "MIR source-storage local mapping does not cover frozen move bindings".into(),
            );
        }
        let mut observed_bindings = vec![None; paths.bindings.len()];
        for (index, scope) in self.scopes.iter().enumerate() {
            if scope.source.0 as usize != index {
                return Err(format!(
                    "MIR source-storage scope {index} has a non-dense PlaceFlow identity"
                ));
            }
            if index > 0 {
                let Some(parent) = scope.parent else {
                    return Err(format!("MIR source-storage scope {index} has no parent"));
                };
                if parent.0 as usize >= index {
                    return Err(format!(
                        "MIR source-storage scope {index} has a non-ancestral parent"
                    ));
                }
            }
            let mut local = BTreeSet::new();
            for &binding in &scope.bindings {
                let binding_index = binding.0 as usize;
                if binding_index >= paths.bindings.len() {
                    return Err(format!(
                        "MIR source-storage scope {index} names absent binding {}",
                        binding.0
                    ));
                }
                if !local.insert(binding) {
                    return Err(format!(
                        "MIR source-storage scope {index} repeats a binding"
                    ));
                }
                if observed_bindings[binding_index].replace(index).is_some() {
                    return Err("MIR source-storage binding belongs to multiple scopes".into());
                }
                if self.binding_scopes[binding_index] != MirSourceStorageScopeId(index as u32) {
                    return Err(
                        "MIR source-storage binding-to-scope index disagrees with arena".into(),
                    );
                }
            }
            let expected = scope
                .bindings
                .iter()
                .copied()
                .map(|binding| MirStorageEvent {
                    kind: MirStorageEventKind::Live,
                    binding,
                })
                .chain(
                    scope
                        .bindings
                        .iter()
                        .rev()
                        .copied()
                        .map(|binding| MirStorageEvent {
                            kind: MirStorageEventKind::Dead,
                            binding,
                        }),
                )
                .collect::<Vec<_>>();
            if scope.events != expected {
                return Err(format!(
                    "MIR source-storage scope {index} has invalid StorageLive/StorageDead ordering"
                ));
            }
        }
        if observed_bindings.iter().any(Option::is_none) {
            return Err("MIR source-storage arena omits a frozen move binding".into());
        }
        Ok(())
    }

    pub fn validate_local_mapping(
        &self,
        paths: &MirMovePathTables,
        locals: usize,
    ) -> Result<(), String> {
        for (binding, local) in self.binding_locals.iter().enumerate() {
            let Some(local) = local else {
                continue;
            };
            if local.0 as usize >= locals {
                return Err(format!(
                    "MIR source-storage binding {binding} maps to absent local {}",
                    local.0
                ));
            }
            if binding >= paths.bindings.len() {
                return Err("MIR source-storage local map exceeds frozen bindings".into());
            }
        }
        Ok(())
    }

    /// Validate the source-storage half of a cleanup plan. The caller supplies
    /// an explicit source and target scope; this function intentionally never
    /// derives them from control scopes or block layout.
    pub fn validate_cleanup_exit(
        &self,
        paths: &MirMovePathTables,
        source: MirSourceStorageScopeId,
        target: MirSourceStorageScopeId,
        moved_paths: &[MirMovePathId],
    ) -> Result<(), String> {
        let scope = |scope: MirSourceStorageScopeId| {
            self.scopes.get(scope.0 as usize).ok_or_else(|| {
                format!(
                    "MIR cleanup references absent source-storage scope {}",
                    scope.0
                )
            })
        };
        scope(source)?;
        scope(target)?;
        if !self.is_ancestor(target, source) {
            return Err("MIR cleanup target source-storage scope is not an ancestor".into());
        }
        // A same-scope nonlocal transfer has no storage boundary to destroy.
        // Its typed paths are disarmed ownership facts carried through the
        // legacy cleanup proof, not destruction actions; protected-payload
        // validation remains the caller's responsibility. Requiring those
        // paths to lie strictly below the target would reject valid partial
        // moves such as `transfer label pair.right` after `move pair.left`.
        if source == target {
            return Ok(());
        }
        let mut previous: Option<(MirSourceStorageScopeId, MirPlaceBindingId)> = None;
        for &path in moved_paths {
            let path_data = paths.paths.get(path.0 as usize).ok_or_else(|| {
                format!("MIR cleanup references absent typed move path {}", path.0)
            })?;
            let binding_scope = *self
                .binding_scopes
                .get(path_data.binding.0 as usize)
                .ok_or_else(|| "MIR cleanup path binding has no source-storage scope".to_owned())?;
            // A plan may disarm only an owner whose storage expires at this
            // edge: it must be below the target boundary and no deeper than
            // the plan source. This rejects a forged cleanup that reaches
            // into a sibling, descendant, or outer live frame.
            if !self.is_ancestor(target, binding_scope) || !self.is_ancestor(binding_scope, source)
            {
                return Err(
                    "MIR cleanup path lies outside its declared source-storage exit".into(),
                );
            }
            if binding_scope == target {
                return Err("MIR cleanup disarms storage retained by its target scope".into());
            }
            if let Some(previous) = previous
                && self.scope_order_key(binding_scope, path_data.binding)
                    > self.scope_order_key(previous.0, previous.1)
            {
                return Err("MIR cleanup does not destroy source storage in reverse lexical initialization order".into());
            }
            previous = Some((binding_scope, path_data.binding));
        }
        Ok(())
    }

    /// Source owners whose lexical storage lifetime ends on `source ->
    /// target`, in the required destruction order: inner scopes first and
    /// reverse declaration order within a scope.
    pub fn exited_bindings(
        &self,
        source: MirSourceStorageScopeId,
        target: MirSourceStorageScopeId,
    ) -> Result<Vec<MirPlaceBindingId>, String> {
        if self.scopes.get(source.0 as usize).is_none()
            || self.scopes.get(target.0 as usize).is_none()
        {
            return Err("MIR cleanup references absent source-storage scope".into());
        }
        if !self.is_ancestor(target, source) {
            return Err("MIR cleanup target source-storage scope is not an ancestor".into());
        }
        let mut bindings = Vec::new();
        let mut scope = source;
        while scope != target {
            let data = &self.scopes[scope.0 as usize];
            bindings.extend(data.bindings.iter().rev().copied());
            scope = data
                .parent
                .expect("validated non-root source-storage scope has a parent");
        }
        Ok(bindings)
    }

    /// The executable local imported for this binding, if compact lowering
    /// has one.  This is a typed arena lookup, never a spelling lookup.
    pub fn binding_local(&self, binding: MirPlaceBindingId) -> Option<MirLocal> {
        self.binding_locals.get(binding.0 as usize).copied().flatten()
    }

    pub fn scope_is_ancestor(
        &self,
        ancestor: MirSourceStorageScopeId,
        scope: MirSourceStorageScopeId,
    ) -> bool {
        self.is_ancestor(ancestor, scope)
    }

    fn is_ancestor(
        &self,
        ancestor: MirSourceStorageScopeId,
        mut scope: MirSourceStorageScopeId,
    ) -> bool {
        loop {
            if ancestor == scope {
                return true;
            }
            let Some(parent) = self
                .scopes
                .get(scope.0 as usize)
                .and_then(|scope| scope.parent)
            else {
                return false;
            };
            scope = parent;
        }
    }

    // Deeper scope IDs were allocated after their parents. Within one scope,
    // later bindings have the greater initialization position; both must run
    // first during cleanup. The tuple therefore sorts in required cleanup
    // order when compared descending.
    fn scope_order_key(
        &self,
        scope: MirSourceStorageScopeId,
        binding: MirPlaceBindingId,
    ) -> (u32, u32) {
        let position = self.scopes[scope.0 as usize]
            .bindings
            .iter()
            .position(|candidate| *candidate == binding)
            .expect("validated source-storage binding belongs to its scope")
            as u32;
        (scope.0, position)
    }
}
