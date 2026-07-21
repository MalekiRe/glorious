//! Generational storage used by VM values and snapshots.
//!
//! Bytecode-visible values must never rely on a native address for identity.
//! [`Handle`] supplies a stable, serializable identity and detects use after
//! reclamation through its generation component.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt,
    marker::PhantomData,
};

/// A typed reference to an arena entry.
///
/// The index selects a slot and the generation distinguishes successive
/// occupants of that slot.
pub struct Handle<T> {
    index: u32,
    generation: u32,
    marker: PhantomData<fn() -> T>,
}

impl<T> Handle<T> {
    pub const fn from_parts(index: u32, generation: u32) -> Self {
        Self {
            index,
            generation,
            marker: PhantomData,
        }
    }

    pub const fn index(self) -> u32 {
        self.index
    }

    pub const fn generation(self) -> u32 {
        self.generation
    }
}

impl<T> Copy for Handle<T> {}

impl<T> Clone for Handle<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> PartialEq for Handle<T> {
    fn eq(&self, other: &Self) -> bool {
        (self.index, self.generation) == (other.index, other.generation)
    }
}

impl<T> Eq for Handle<T> {}

impl<T> PartialOrd for Handle<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for Handle<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.index, self.generation).cmp(&(other.index, other.generation))
    }
}

impl<T> std::hash::Hash for Handle<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.index.hash(state);
        self.generation.hash(state);
    }
}

impl<T> fmt::Debug for Handle<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}@{}", self.index, self.generation)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ArenaError {
    IndexOutOfBounds {
        index: u32,
    },
    Vacant {
        index: u32,
        generation: u32,
    },
    Stale {
        index: u32,
        requested: u32,
        current: u32,
    },
    GenerationExhausted {
        index: u32,
    },
    CapacityExhausted,
    ProjectionOutOfBounds {
        slot: u32,
        len: u32,
    },
    UninitializedProjection {
        slot: u32,
    },
    OccupiedProjection {
        slot: u32,
    },
}

impl fmt::Display for ArenaError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IndexOutOfBounds { index } => {
                write!(formatter, "arena index {index} is out of bounds")
            }
            Self::Vacant { index, generation } => {
                write!(
                    formatter,
                    "arena handle {index}@{generation} names a vacant slot"
                )
            }
            Self::Stale {
                index,
                requested,
                current,
            } => write!(
                formatter,
                "arena handle {index}@{requested} is stale; current generation is {current}"
            ),
            Self::GenerationExhausted { index } => {
                write!(formatter, "arena slot {index} exhausted its generations")
            }
            Self::CapacityExhausted => formatter.write_str("arena exhausted its u32 index space"),
            Self::ProjectionOutOfBounds { slot, len } => {
                write!(
                    formatter,
                    "place projection {slot} is out of bounds for {len} slots"
                )
            }
            Self::UninitializedProjection { slot } => {
                write!(formatter, "place projection {slot} is uninitialized")
            }
            Self::OccupiedProjection { slot } => {
                write!(formatter, "place projection {slot} is already initialized")
            }
        }
    }
}

impl Error for ArenaError {}

#[derive(Clone, Debug)]
struct Entry<T> {
    generation: u32,
    value: Option<T>,
}

/// A deterministic generational arena.
///
/// Reclaimed indices are reused in ascending order. Removal advances the
/// generation before making a slot reusable, so every old handle immediately
/// becomes stale.
#[derive(Clone, Debug)]
pub struct Arena<T> {
    entries: Vec<Entry<T>>,
    free: BTreeSet<u32>,
    len: usize,
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Arena<T> {
    pub const fn new() -> Self {
        Self {
            entries: Vec::new(),
            free: BTreeSet::new(),
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Enumerate occupied handles in stable index order.
    pub fn handles(&self) -> impl Iterator<Item = Handle<T>> + '_ {
        self.entries
            .iter()
            .enumerate()
            .filter_map(|(index, entry)| {
                entry.value.as_ref()?;
                Some(Handle::from_parts(index as u32, entry.generation))
            })
    }

    pub fn insert(&mut self, value: T) -> Result<Handle<T>, ArenaError> {
        let index = if let Some(index) = self.free.pop_first() {
            index
        } else {
            let index =
                u32::try_from(self.entries.len()).map_err(|_| ArenaError::CapacityExhausted)?;
            self.entries.push(Entry {
                generation: 0,
                value: None,
            });
            index
        };
        let entry = &mut self.entries[index as usize];
        debug_assert!(entry.value.is_none());
        entry.value = Some(value);
        self.len += 1;
        Ok(Handle::from_parts(index, entry.generation))
    }

    pub fn contains(&self, handle: Handle<T>) -> bool {
        self.get(handle).is_ok()
    }

    pub fn get(&self, handle: Handle<T>) -> Result<&T, ArenaError> {
        let entry = self.checked_entry(handle)?;
        entry.value.as_ref().ok_or(ArenaError::Vacant {
            index: handle.index,
            generation: handle.generation,
        })
    }

    pub fn get_mut(&mut self, handle: Handle<T>) -> Result<&mut T, ArenaError> {
        let entry = self.checked_entry_mut(handle)?;
        entry.value.as_mut().ok_or(ArenaError::Vacant {
            index: handle.index,
            generation: handle.generation,
        })
    }

    pub fn remove(&mut self, handle: Handle<T>) -> Result<T, ArenaError> {
        let entry = self.checked_entry_mut(handle)?;
        if entry.value.is_none() {
            return Err(ArenaError::Vacant {
                index: handle.index,
                generation: handle.generation,
            });
        }
        let next = entry
            .generation
            .checked_add(1)
            .ok_or(ArenaError::GenerationExhausted {
                index: handle.index,
            })?;
        let value = entry.value.take().expect("vacancy checked above");
        entry.generation = next;
        self.free.insert(handle.index);
        self.len -= 1;
        Ok(value)
    }

    fn checked_entry(&self, handle: Handle<T>) -> Result<&Entry<T>, ArenaError> {
        let entry =
            self.entries
                .get(handle.index as usize)
                .ok_or(ArenaError::IndexOutOfBounds {
                    index: handle.index,
                })?;
        if entry.generation != handle.generation {
            return Err(ArenaError::Stale {
                index: handle.index,
                requested: handle.generation,
                current: entry.generation,
            });
        }
        Ok(entry)
    }

    fn checked_entry_mut(&mut self, handle: Handle<T>) -> Result<&mut Entry<T>, ArenaError> {
        let entry =
            self.entries
                .get_mut(handle.index as usize)
                .ok_or(ArenaError::IndexOutOfBounds {
                    index: handle.index,
                })?;
        if entry.generation != handle.generation {
            return Err(ArenaError::Stale {
                index: handle.index,
                requested: handle.generation,
                current: entry.generation,
            });
        }
        Ok(entry)
    }
}

/// Arena payload for a VM place with independently movable slots.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlaceSlots<T> {
    slots: Vec<Option<T>>,
}

impl<T> PlaceSlots<T> {
    pub fn new(slots: impl IntoIterator<Item = Option<T>>) -> Self {
        Self {
            slots: slots.into_iter().collect(),
        }
    }

    pub fn initialized(slots: impl IntoIterator<Item = T>) -> Self {
        Self::new(slots.into_iter().map(Some))
    }

    pub fn len(&self) -> usize {
        self.slots.len()
    }

    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }
}

/// A checked projection into a [`PlaceSlots`] allocation.
pub struct PlaceHandle<T> {
    owner: Handle<PlaceSlots<T>>,
    slot: u32,
}

impl<T> Copy for PlaceHandle<T> {}

impl<T> Clone for PlaceHandle<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> PartialEq for PlaceHandle<T> {
    fn eq(&self, other: &Self) -> bool {
        (self.owner, self.slot) == (other.owner, other.slot)
    }
}

impl<T> Eq for PlaceHandle<T> {}

impl<T> PartialOrd for PlaceHandle<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for PlaceHandle<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.owner, self.slot).cmp(&(other.owner, other.slot))
    }
}

impl<T> std::hash::Hash for PlaceHandle<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.owner.hash(state);
        self.slot.hash(state);
    }
}

impl<T> fmt::Debug for PlaceHandle<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}.{}", self.owner, self.slot)
    }
}

impl<T> PlaceHandle<T> {
    pub const fn new(owner: Handle<PlaceSlots<T>>, slot: u32) -> Self {
        Self { owner, slot }
    }

    pub const fn owner(self) -> Handle<PlaceSlots<T>> {
        self.owner
    }

    pub const fn slot(self) -> u32 {
        self.slot
    }
}

impl<T> Arena<PlaceSlots<T>> {
    pub fn project(&self, place: PlaceHandle<T>) -> Result<&T, ArenaError> {
        self.checked_slot(place)?
            .as_ref()
            .ok_or(ArenaError::UninitializedProjection { slot: place.slot })
    }

    pub fn project_mut(&mut self, place: PlaceHandle<T>) -> Result<&mut T, ArenaError> {
        let slot = place.slot;
        self.checked_slot_mut(place)?
            .as_mut()
            .ok_or(ArenaError::UninitializedProjection { slot })
    }

    pub fn take_projection(&mut self, place: PlaceHandle<T>) -> Result<T, ArenaError> {
        let slot = place.slot;
        self.checked_slot_mut(place)?
            .take()
            .ok_or(ArenaError::UninitializedProjection { slot })
    }

    pub fn put_projection(&mut self, place: PlaceHandle<T>, value: T) -> Result<(), ArenaError> {
        let slot = self.checked_slot_mut(place)?;
        if slot.is_some() {
            return Err(ArenaError::OccupiedProjection { slot: place.slot });
        }
        *slot = Some(value);
        Ok(())
    }

    fn checked_slot(&self, place: PlaceHandle<T>) -> Result<&Option<T>, ArenaError> {
        let owner = self.get(place.owner)?;
        owner
            .slots
            .get(place.slot as usize)
            .ok_or_else(|| projection_out_of_bounds(place.slot, owner.slots.len()))
    }

    fn checked_slot_mut(&mut self, place: PlaceHandle<T>) -> Result<&mut Option<T>, ArenaError> {
        let owner = self.get_mut(place.owner)?;
        let len = owner.slots.len();
        owner
            .slots
            .get_mut(place.slot as usize)
            .ok_or_else(|| projection_out_of_bounds(place.slot, len))
    }
}

fn projection_out_of_bounds(slot: u32, len: usize) -> ArenaError {
    ArenaError::ProjectionOutOfBounds {
        slot,
        len: u32::try_from(len).unwrap_or(u32::MAX),
    }
}

/// Result of compacting the reachable portion of an arena.
#[derive(Clone, Debug)]
pub struct CompactedArena<T> {
    pub arena: Arena<T>,
    pub roots: Vec<Handle<T>>,
    pub remap: BTreeMap<Handle<T>, Handle<T>>,
}

impl<T> Arena<T> {
    fn reachable_from<Edges>(
        &self,
        roots: impl IntoIterator<Item = Handle<T>>,
        edges: &Edges,
    ) -> Result<BTreeSet<Handle<T>>, ArenaError>
    where
        Edges: Fn(&T) -> Vec<Handle<T>>,
    {
        let mut pending = roots.into_iter().collect::<BTreeSet<_>>();
        let mut reachable = BTreeSet::new();
        while let Some(handle) = pending.pop_first() {
            if !reachable.insert(handle) {
                continue;
            }
            let value = self.get(handle)?;
            for edge in edges(value) {
                self.get(edge)?;
                if !reachable.contains(&edge) {
                    pending.insert(edge);
                }
            }
        }
        Ok(reachable)
    }

    /// Deterministically reclaim every entry not reachable from `roots`.
    ///
    /// Reachable edges are fully validated before any mutation occurs. Cycles
    /// without a root are reclaimed, and returned values follow ascending old
    /// handle order so destruction can preserve a reproducible schedule.
    pub fn reclaim_unreachable<Edges>(
        &mut self,
        roots: impl IntoIterator<Item = Handle<T>>,
        edges: Edges,
    ) -> Result<Vec<(Handle<T>, T)>, ArenaError>
    where
        Edges: Fn(&T) -> Vec<Handle<T>>,
    {
        let reachable = self.reachable_from(roots, &edges)?;
        let doomed = self
            .handles()
            .filter(|handle| !reachable.contains(handle))
            .collect::<Vec<_>>();
        for handle in &doomed {
            if self.checked_entry(*handle)?.generation == u32::MAX {
                return Err(ArenaError::GenerationExhausted {
                    index: handle.index,
                });
            }
        }
        doomed
            .into_iter()
            .map(|handle| self.remove(handle).map(|value| (handle, value)))
            .collect()
    }

    /// Clone only entries reachable from `roots` into a dense arena.
    ///
    /// `edges` enumerates handles stored in a value. `rewrite` must clone the
    /// value while replacing every such handle using the completed map. Any
    /// stale root or edge aborts before a snapshot is produced.
    pub fn compact_reachable<Edges, Rewrite>(
        &self,
        roots: impl IntoIterator<Item = Handle<T>>,
        edges: Edges,
        rewrite: Rewrite,
    ) -> Result<CompactedArena<T>, ArenaError>
    where
        Edges: Fn(&T) -> Vec<Handle<T>>,
        Rewrite: Fn(&T, &BTreeMap<Handle<T>, Handle<T>>) -> T,
    {
        let roots = roots.into_iter().collect::<Vec<_>>();
        let reachable = self.reachable_from(roots.iter().copied(), &edges)?;

        let remap = reachable
            .iter()
            .enumerate()
            .map(|(index, old)| {
                let index = u32::try_from(index).map_err(|_| ArenaError::CapacityExhausted)?;
                Ok((*old, Handle::from_parts(index, 0)))
            })
            .collect::<Result<BTreeMap<_, _>, ArenaError>>()?;

        let mut arena = Arena::new();
        for old in reachable {
            let expected = remap[&old];
            let actual = arena.insert(rewrite(self.get(old)?, &remap))?;
            debug_assert_eq!(actual, expected);
        }
        let roots = roots.into_iter().map(|root| remap[&root]).collect();
        Ok(CompactedArena {
            arena,
            roots,
            remap,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reclamation_invalidates_old_handles_and_reuses_lowest_slot() {
        let mut arena = Arena::new();
        let first = arena.insert("first").unwrap();
        let second = arena.insert("second").unwrap();
        let third = arena.insert("third").unwrap();
        assert_eq!(arena.remove(second).unwrap(), "second");
        assert_eq!(arena.remove(first).unwrap(), "first");

        let replacement = arena.insert("replacement").unwrap();
        assert_eq!(replacement, Handle::from_parts(0, 1));
        assert_eq!(arena.get(replacement), Ok(&"replacement"));
        assert_eq!(
            arena.get(first),
            Err(ArenaError::Stale {
                index: 0,
                requested: 0,
                current: 1,
            })
        );
        assert_eq!(arena.get(third), Ok(&"third"));
    }

    #[test]
    fn generation_exhaustion_does_not_reclaim_or_lose_the_value() {
        let mut arena = Arena::new();
        arena.entries.push(Entry {
            generation: u32::MAX,
            value: Some("last generation"),
        });
        arena.len = 1;
        let handle = Handle::from_parts(0, u32::MAX);

        assert_eq!(
            arena.remove(handle),
            Err(ArenaError::GenerationExhausted { index: 0 })
        );
        assert_eq!(arena.get(handle), Ok(&"last generation"));
        assert_eq!(arena.len(), 1);
    }

    #[test]
    fn place_projections_check_generation_bounds_and_initialization() {
        let mut arena = Arena::new();
        let owner = arena
            .insert(PlaceSlots::new([Some(10), None, Some(30)]))
            .unwrap();
        let middle = PlaceHandle::new(owner, 1);
        assert_eq!(
            arena.project(middle),
            Err(ArenaError::UninitializedProjection { slot: 1 })
        );
        arena.put_projection(middle, 20).unwrap();
        assert_eq!(arena.take_projection(middle), Ok(20));
        assert_eq!(
            arena.project(PlaceHandle::new(owner, 3)),
            Err(ArenaError::ProjectionOutOfBounds { slot: 3, len: 3 })
        );

        arena.remove(owner).unwrap();
        let replacement = arena.insert(PlaceSlots::initialized([40])).unwrap();
        assert_eq!(replacement.index(), owner.index());
        assert!(matches!(
            arena.project(PlaceHandle::new(owner, 0)),
            Err(ArenaError::Stale { .. })
        ));
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct Node {
        name: &'static str,
        edges: Vec<Handle<Node>>,
    }

    #[test]
    fn snapshots_are_dense_and_remap_handles_without_pointer_identity() {
        let mut arena = Arena::new();
        let leaf = arena
            .insert(Node {
                name: "leaf",
                edges: vec![],
            })
            .unwrap();
        let unreachable = arena
            .insert(Node {
                name: "unreachable",
                edges: vec![],
            })
            .unwrap();
        let root = arena
            .insert(Node {
                name: "root",
                edges: vec![leaf],
            })
            .unwrap();

        let compacted = arena
            .compact_reachable(
                [root],
                |node| node.edges.clone(),
                |node, remap| Node {
                    name: node.name,
                    edges: node.edges.iter().map(|edge| remap[edge]).collect(),
                },
            )
            .unwrap();

        assert_eq!(compacted.arena.len(), 2);
        assert!(!compacted.remap.contains_key(&unreachable));
        let compact_root = compacted.roots[0];
        let compact_leaf = compacted.remap[&leaf];
        assert_eq!(
            compacted.arena.get(compact_root).unwrap().edges,
            [compact_leaf]
        );
        assert_eq!(compacted.arena.get(compact_leaf).unwrap().name, "leaf");
    }

    #[test]
    fn snapshot_rejects_stale_edges() {
        let mut arena = Arena::new();
        let dead = arena
            .insert(Node {
                name: "dead",
                edges: vec![],
            })
            .unwrap();
        arena.remove(dead).unwrap();
        let root = arena
            .insert(Node {
                name: "root",
                edges: vec![dead],
            })
            .unwrap();

        let error = arena
            .compact_reachable([root], |node| node.edges.clone(), |node, _| node.clone())
            .unwrap_err();
        assert!(matches!(error, ArenaError::Stale { .. }));
    }

    #[test]
    fn unreachable_cycles_are_reclaimed_in_handle_order() {
        let mut arena = Arena::new();
        let root = arena
            .insert(Node {
                name: "root",
                edges: vec![],
            })
            .unwrap();
        let first = arena
            .insert(Node {
                name: "cycle-a",
                edges: vec![],
            })
            .unwrap();
        let second = arena
            .insert(Node {
                name: "cycle-b",
                edges: vec![first],
            })
            .unwrap();
        arena.get_mut(first).unwrap().edges.push(second);

        let reclaimed = arena
            .reclaim_unreachable([root], |node| node.edges.clone())
            .unwrap();
        assert_eq!(
            reclaimed
                .iter()
                .map(|(handle, node)| (*handle, node.name))
                .collect::<Vec<_>>(),
            [(first, "cycle-a"), (second, "cycle-b")]
        );
        assert_eq!(arena.handles().collect::<Vec<_>>(), [root]);
    }
}
