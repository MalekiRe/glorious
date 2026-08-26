use std::{
    cell::{Ref, RefCell, RefMut},
    collections::{BTreeMap, BTreeSet, VecDeque},
    fmt,
    marker::PhantomData,
    rc::{Rc, Weak},
    sync::atomic::{AtomicU64, Ordering},
};

pub(crate) trait RuntimeEdges {
    fn edge_identities(&self, edges: &mut Vec<u128>);
    fn clear_edges(&mut self);
}

trait ReclaimNode {
    fn identity(&self) -> u128;
    fn strong_count(&self) -> usize;
    fn edge_identities(&self) -> Vec<u128>;
    fn clear_edges(&self);
}

// Compactions prune dead weak registrations; with the churn seen in the
// self-host workloads (millions of aggregate allocations per input) the
// original 64K interval spent ~3.5% of VM run time inside `retain`. Each
// compaction rescans the growing registry, so a larger interval cuts that
// cost proportionally while keeping the same geometric growth behavior.
// 8x the original: retain now measures well under 1% of run time and the
// registry stays well under a few tens of MB even under heavy churn.
const MIN_RECLAMATION_COMPACTION_INTERVAL: usize = 524_288;

struct ReclamationRegistry {
    nodes: Vec<Weak<dyn ReclaimNode>>,
    registrations_until_compaction: usize,
}

impl ReclamationRegistry {
    fn new() -> Self {
        Self {
            nodes: Vec::new(),
            registrations_until_compaction: MIN_RECLAMATION_COMPACTION_INTERVAL,
        }
    }

    fn register(&mut self, node: Weak<dyn ReclaimNode>) {
        self.nodes.push(node);
        self.registrations_until_compaction -= 1;
        if self.registrations_until_compaction == 0 {
            self.nodes.retain(|node| node.strong_count() != 0);
            // When many objects are genuinely live, scan geometrically rather
            // than once per fixed-size batch. Short-lived allocation churn is
            // still pruned at a bounded interval.
            self.registrations_until_compaction =
                self.nodes.len().max(MIN_RECLAMATION_COMPACTION_INTERVAL);
        }
    }
}

thread_local! {
    static RECLAMATION_SCOPES: RefCell<Vec<ReclamationRegistry>> = const { RefCell::new(Vec::new()) };
}

/// Execution-local registry used only to break unreachable `Rc` cycles at a
/// deterministic VM boundary. It is deliberately tracing-only: ordinary
/// acyclic objects continue to reclaim through normal reference counting.
pub(crate) struct ReclamationScope {
    active: bool,
}

impl ReclamationScope {
    pub(crate) fn begin() -> Self {
        RECLAMATION_SCOPES.with(|scopes| scopes.borrow_mut().push(ReclamationRegistry::new()));
        Self { active: true }
    }

    pub(crate) fn track_values(&self, values: &[Value]) {
        let mut visited = BTreeSet::new();
        for value in values {
            track_value_graph(value, &mut visited);
        }
    }

    pub(crate) fn finish(mut self) {
        self.collect();
    }

    fn collect(&mut self) {
        if !self.active {
            return;
        }
        self.active = false;
        let nodes = RECLAMATION_SCOPES.with(|scopes| {
            scopes
                .borrow_mut()
                .pop()
                .map_or_else(Vec::new, |registry| registry.nodes)
        });
        reclaim_unreachable(nodes);
    }
}

impl Drop for ReclamationScope {
    fn drop(&mut self) {
        self.collect();
    }
}

fn register_node<T: RuntimeEdges + 'static>(identity: &Rc<ObjectIdentity<T>>) {
    let erased: Rc<dyn ReclaimNode> = identity.clone();
    let weak = Rc::downgrade(&erased);
    RECLAMATION_SCOPES.with(|scopes| {
        for registry in scopes.borrow_mut().iter_mut() {
            registry.register(weak.clone());
        }
    });
}

pub(crate) fn reclamation_diagnostic_counts() -> (usize, usize) {
    RECLAMATION_SCOPES.with(|scopes| {
        scopes
            .borrow()
            .iter()
            .flat_map(|registry| &registry.nodes)
            .fold((0, 0), |(tracked, live), node| {
                (tracked + 1, live + usize::from(node.strong_count() != 0))
            })
    })
}

fn reclaim_unreachable(nodes: Vec<Weak<dyn ReclaimNode>>) {
    let mut live = BTreeMap::<u128, Rc<dyn ReclaimNode>>::new();
    for weak in nodes {
        if let Some(node) = weak.upgrade() {
            live.entry(node.identity()).or_insert(node);
        }
    }
    let mut incoming = BTreeMap::<u128, usize>::new();
    let mut edges = BTreeMap::<u128, Vec<u128>>::new();
    for (&identity, node) in &live {
        let outgoing = node.edge_identities();
        for target in outgoing.iter().filter(|target| live.contains_key(target)) {
            *incoming.entry(*target).or_default() += 1;
        }
        edges.insert(identity, outgoing);
    }
    let mut reachable = BTreeSet::new();
    let mut pending = live
        .iter()
        .filter_map(|(&identity, node)| {
            // `live` itself owns one temporary strong handle. Every other
            // non-edge strong handle is an execution-boundary root.
            (node.strong_count() > incoming.get(&identity).copied().unwrap_or(0) + 1)
                .then_some(identity)
        })
        .collect::<VecDeque<_>>();
    while let Some(identity) = pending.pop_front() {
        if !reachable.insert(identity) {
            continue;
        }
        if let Some(outgoing) = edges.get(&identity) {
            pending.extend(
                outgoing
                    .iter()
                    .filter(|target| live.contains_key(target))
                    .copied(),
            );
        }
    }
    for (identity, node) in live
        .iter()
        .filter(|(identity, _)| !reachable.contains(identity))
    {
        debug_assert_eq!(*identity, node.identity());
        node.clear_edges();
    }
}

fn track_value_graph(value: &Value, visited: &mut BTreeSet<u128>) {
    match value {
        Value::Array(object) => {
            if visited.insert(object.identity()) {
                object.track();
                for value in object.borrow().slots.iter().flatten() {
                    track_value_graph(value, visited);
                }
            }
        }
        Value::Aggregate(object) => {
            if visited.insert(object.identity()) {
                object.track();
                for value in object.borrow().fields.iter().flatten() {
                    track_value_graph(value, visited);
                }
            }
        }
        Value::Callable(handle) => track_control_graph(&handle.object, visited),
        Value::Handler(handle) => track_control_graph(&handle.object, visited),
        Value::Resumption(handle) => track_control_graph(&handle.object, visited),
        Value::Reference { target, .. } => match target {
            ReferenceTarget::Array(object)
            | ReferenceTarget::ArrayElement { array: object, .. } => {
                track_value_graph(&Value::Array(object.clone()), visited)
            }
            ReferenceTarget::Aggregate(object)
            | ReferenceTarget::AggregateField {
                aggregate: object, ..
            } => track_value_graph(&Value::Aggregate(object.clone()), visited),
            ReferenceTarget::CallableCapture(capture) => track_capture_graph(capture, visited),
            ReferenceTarget::DropSlot(_)
            | ReferenceTarget::WholePlace(_)
            | ReferenceTarget::StaticDataElement { .. } => {}
        },
        _ => {}
    }
}

fn track_capture_graph(capture: &ArenaObject<Option<Value>>, visited: &mut BTreeSet<u128>) {
    if visited.insert(capture.identity()) {
        capture.track();
        if let Some(value) = capture.borrow().as_ref() {
            track_value_graph(value, visited);
        }
    }
}

fn track_control_graph(control: &ArenaObject<ControlRecord>, visited: &mut BTreeSet<u128>) {
    fn track_frame_graph(frame: &RuntimeFrame, visited: &mut BTreeSet<u128>) {
        for value in frame
            .registers
            .iter()
            .flatten()
            .chain(frame.delimiter.iter())
            .chain(&frame.guards)
        {
            track_value_graph(value, visited);
        }
        for deferred in &frame.deferred_frames {
            track_frame_graph(deferred, visited);
        }
    }

    if !visited.insert(control.identity()) {
        return;
    }
    control.track();
    match &*control.borrow() {
        ControlRecord::Callable(value) => track_capture_graph(&value.capture, visited),
        ControlRecord::Handler(value) => {
            for clause in value.clauses.iter().flatten() {
                track_value_graph(clause, visited);
            }
        }
        ControlRecord::Resumption(value) => {
            if let Some(value) = value {
                for frame in &value.frames {
                    track_frame_graph(frame, visited);
                }
            }
        }
    }
}

use crate::{
    arena::{Arena, ArenaError, Handle, PlaceHandle, PlaceSlots},
    bytecode::{TypeId, U8},
};

type ValueSlots = PlaceSlots<Value>;

/// Shared owner of VM place storage. Values carry only typed generational
/// handles into this store; the backing allocation is not their identity.
#[derive(Clone, Debug)]
pub(crate) struct SlotStore {
    id: u64,
    arena: Rc<RefCell<Arena<ValueSlots>>>,
}

static NEXT_SLOT_STORE_ID: AtomicU64 = AtomicU64::new(1);

fn next_store_id() -> u64 {
    NEXT_SLOT_STORE_ID.fetch_add(1, Ordering::Relaxed)
}

impl Default for SlotStore {
    fn default() -> Self {
        Self {
            id: next_store_id(),
            arena: Rc::new(RefCell::new(Arena::new())),
        }
    }
}

impl SlotStore {
    pub(crate) fn diagnostic_counts(&self) -> (usize, usize) {
        let arena = self.arena.borrow();
        (arena.len(), arena.storage_len())
    }

    pub(crate) fn insert(&self, value: Option<Value>) -> Result<SlotHandle, ArenaError> {
        let owner = self.arena.borrow_mut().insert(PlaceSlots::new([value]))?;
        Ok(SlotHandle {
            store: self.clone(),
            owner,
        })
    }
}

/// Runtime handle for a whole register place or custom-drop slot.
#[derive(Clone)]
pub struct SlotHandle {
    store: SlotStore,
    owner: Handle<ValueSlots>,
}

impl SlotHandle {
    pub(crate) fn identity(&self) -> u128 {
        (u128::from(self.store.id) << 64)
            | (u128::from(self.owner.generation()) << 32)
            | u128::from(self.owner.index())
    }

    pub(crate) fn empty_peer(&self) -> Result<Self, ArenaError> {
        self.store.insert(None)
    }

    pub(crate) fn get(&self) -> Result<Value, ArenaError> {
        self.store
            .arena
            .borrow()
            .project(PlaceHandle::new(self.owner, 0))
            .cloned()
    }

    /// Read a place without materializing an intermediate `Value` clone.
    ///
    /// Operations such as bytecode COPY need to derive their own independent
    /// value, but can do so directly from the stored value rather than first
    /// cloning it and then cloning/deep-copying that temporary again.
    pub(crate) fn with_value<T>(
        &self,
        read: impl FnOnce(&Value) -> T,
    ) -> Result<T, ArenaError> {
        let arena = self.store.arena.borrow();
        let value = arena.project(PlaceHandle::new(self.owner, 0))?;
        Ok(read(value))
    }

    pub(crate) fn take(&self) -> Result<Value, ArenaError> {
        self.store
            .arena
            .borrow_mut()
            .take_projection(PlaceHandle::new(self.owner, 0))
    }

    pub(crate) fn put(&self, value: Value) -> Result<(), ArenaError> {
        self.store
            .arena
            .borrow_mut()
            .put_projection(PlaceHandle::new(self.owner, 0), value)
    }

    pub(crate) fn take_and_reclaim(&self) -> Result<Value, ArenaError> {
        let mut arena = self.store.arena.borrow_mut();
        let value = arena.take_projection(PlaceHandle::new(self.owner, 0))?;
        arena.remove(self.owner)?;
        Ok(value)
    }

    /// Consume this place for a conditional drop. An uninitialized place is
    /// the runtime representation of a disarmed drop flag and is reclaimed
    /// without running destruction. All other arena failures remain errors.
    pub(crate) fn take_and_reclaim_if_initialized(&self) -> Result<Option<Value>, ArenaError> {
        let mut arena = self.store.arena.borrow_mut();
        let value = match arena.take_projection(PlaceHandle::new(self.owner, 0)) {
            Ok(value) => Some(value),
            Err(ArenaError::UninitializedProjection { .. }) => None,
            Err(error) => return Err(error),
        };
        arena.remove(self.owner)?;
        Ok(value)
    }
}

impl std::fmt::Debug for SlotHandle {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("SlotHandle")
            .field("store", &self.store.id)
            .field("owner", &self.owner)
            .finish()
    }
}

impl PartialEq for SlotHandle {
    fn eq(&self, other: &Self) -> bool {
        self.store.id == other.store.id && self.owner == other.owner
    }
}

#[derive(Debug)]
struct ObjectIdentity<T> {
    store_id: u64,
    generation: u32,
    object: RefCell<Option<T>>,
    self_weak: RefCell<Weak<ObjectIdentity<T>>>,
}

impl<T: RuntimeEdges> ReclaimNode for ObjectIdentity<T> {
    fn identity(&self) -> u128 {
        (u128::from(self.store_id) << 64) | (u128::from(self.generation) << 32)
    }

    fn strong_count(&self) -> usize {
        self.self_weak.borrow().strong_count()
    }

    fn edge_identities(&self) -> Vec<u128> {
        let mut edges = Vec::new();
        if let Ok(object) = self.object.try_borrow()
            && let Some(value) = object.as_ref()
        {
            value.edge_identities(&mut edges);
        }
        edges
    }

    fn clear_edges(&self) {
        if let Ok(mut object) = self.object.try_borrow_mut()
            && let Some(value) = object.as_mut()
        {
            value.clear_edges();
        }
    }
}

/// Inline-backed shared handle for runtime heap objects.
///
/// Each object owns a single inline `RefCell<Option<T>>` slot rather than a
/// whole single-entry arena. Clones share one logical lease.
/// [`ArenaObject::try_unwrap`] succeeds only for the last lease, matching the
/// ownership boundary previously supplied by `Rc::try_unwrap`, and then
/// deterministically reclaims the inline slot.
pub struct ArenaObject<T> {
    identity: Rc<ObjectIdentity<T>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ObjectBorrowError {
    Conflict,
    Stale,
    WrongControlKind,
}

impl<T> ArenaObject<T> {
    pub fn new(value: T) -> Self {
        Self {
            identity: Rc::new_cyclic(|weak| ObjectIdentity {
                store_id: next_store_id(),
                generation: 0,
                object: RefCell::new(Some(value)),
                self_weak: RefCell::new(weak.clone()),
            }),
        }
    }

    pub(crate) fn track(&self)
    where
        T: RuntimeEdges + 'static,
    {
        register_node(&self.identity);
    }

    pub fn identity(&self) -> u128 {
        (u128::from(self.identity.store_id) << 64)
            | (u128::from(self.identity.generation) << 32)
    }

    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.identity() == other.identity()
    }

    pub fn borrow(&self) -> Ref<'_, T> {
        Ref::filter_map(self.identity.object.borrow(), |object| object.as_ref())
            .unwrap_or_else(|_| panic!("stale inline object identity {:?}", self.identity()))
    }

    pub fn borrow_mut(&self) -> RefMut<'_, T> {
        RefMut::filter_map(self.identity.object.borrow_mut(), |object| object.as_mut())
            .unwrap_or_else(|_| panic!("stale inline object identity {:?}", self.identity()))
    }

    pub fn try_borrow(&self) -> Result<Ref<'_, T>, ObjectBorrowError> {
        let object = self
            .identity
            .object
            .try_borrow()
            .map_err(|_| ObjectBorrowError::Conflict)?;
        Ref::filter_map(object, |object| object.as_ref())
            .map_err(|_| ObjectBorrowError::Stale)
    }

    pub fn try_borrow_mut(&self) -> Result<RefMut<'_, T>, ObjectBorrowError> {
        let object = self
            .identity
            .object
            .try_borrow_mut()
            .map_err(|_| ObjectBorrowError::Conflict)?;
        RefMut::filter_map(object, |object| object.as_mut())
            .map_err(|_| ObjectBorrowError::Stale)
    }

    pub fn try_unwrap(self) -> Result<T, Self> {
        match Rc::try_unwrap(self.identity) {
            Ok(identity) => Ok(identity
                .object
                .into_inner()
                .expect("unique inline object must be live")),
            Err(identity) => Err(Self { identity }),
        }
    }

    #[cfg(test)]
    fn reclaim_for_test(&self) {
        self.identity
            .object
            .borrow_mut()
            .take()
            .expect("test object must be live");
    }
}

#[allow(private_bounds)]
impl<T: RuntimeEdges + 'static> ArenaObject<T> {
    pub(crate) fn new_tracked(value: T) -> Self {
        let object = Self::new(value);
        object.track();
        object
    }
}

impl<T> Clone for ArenaObject<T> {
    fn clone(&self) -> Self {
        Self {
            identity: self.identity.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for ArenaObject<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ArenaObject")
            .field("identity", &self.identity())
            .field("value", &*self.borrow())
            .finish()
    }
}

impl<T: PartialEq> PartialEq for ArenaObject<T> {
    fn eq(&self, other: &Self) -> bool {
        Self::ptr_eq(self, other) || *self.borrow() == *other.borrow()
    }
}

/// Runtime callable/control discriminator. This is independent of bytecode
/// opcodes and exists solely to give all first-class control objects one
/// representation contract.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ControlKind {
    Callable,
    Handler,
    Resumption,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ControlRecord {
    Callable(CallableValue),
    Handler(HandlerValue),
    Resumption(Option<ResumptionValue>),
}

impl ControlRecord {
    pub const fn kind(&self) -> ControlKind {
        match self {
            Self::Callable(_) => ControlKind::Callable,
            Self::Handler(_) => ControlKind::Handler,
            Self::Resumption(_) => ControlKind::Resumption,
        }
    }
}

#[doc(hidden)]
pub trait ControlPayload: Sized {
    const KIND: ControlKind;
    fn into_record(self) -> ControlRecord;
    fn get(record: &ControlRecord) -> Option<&Self>;
    fn get_mut(record: &mut ControlRecord) -> Option<&mut Self>;
    fn from_record(record: ControlRecord) -> Option<Self>;
}

impl ControlPayload for CallableValue {
    const KIND: ControlKind = ControlKind::Callable;

    fn into_record(self) -> ControlRecord {
        ControlRecord::Callable(self)
    }

    fn get(record: &ControlRecord) -> Option<&Self> {
        let ControlRecord::Callable(value) = record else {
            return None;
        };
        Some(value)
    }

    fn get_mut(record: &mut ControlRecord) -> Option<&mut Self> {
        let ControlRecord::Callable(value) = record else {
            return None;
        };
        Some(value)
    }

    fn from_record(record: ControlRecord) -> Option<Self> {
        let ControlRecord::Callable(value) = record else {
            return None;
        };
        Some(value)
    }
}

impl ControlPayload for HandlerValue {
    const KIND: ControlKind = ControlKind::Handler;

    fn into_record(self) -> ControlRecord {
        ControlRecord::Handler(self)
    }

    fn get(record: &ControlRecord) -> Option<&Self> {
        let ControlRecord::Handler(value) = record else {
            return None;
        };
        Some(value)
    }

    fn get_mut(record: &mut ControlRecord) -> Option<&mut Self> {
        let ControlRecord::Handler(value) = record else {
            return None;
        };
        Some(value)
    }

    fn from_record(record: ControlRecord) -> Option<Self> {
        let ControlRecord::Handler(value) = record else {
            return None;
        };
        Some(value)
    }
}

impl ControlPayload for Option<ResumptionValue> {
    const KIND: ControlKind = ControlKind::Resumption;

    fn into_record(self) -> ControlRecord {
        ControlRecord::Resumption(self)
    }

    fn get(record: &ControlRecord) -> Option<&Self> {
        let ControlRecord::Resumption(value) = record else {
            return None;
        };
        Some(value)
    }

    fn get_mut(record: &mut ControlRecord) -> Option<&mut Self> {
        let ControlRecord::Resumption(value) = record else {
            return None;
        };
        Some(value)
    }

    fn from_record(record: ControlRecord) -> Option<Self> {
        let ControlRecord::Resumption(value) = record else {
            return None;
        };
        Some(value)
    }
}

/// Typed view of the unified tagged control record.
pub struct ControlHandle<T: ControlPayload> {
    object: ArenaObject<ControlRecord>,
    marker: PhantomData<fn() -> T>,
}

impl<T: ControlPayload> ControlHandle<T> {
    pub fn new(value: T) -> Self {
        Self {
            object: ArenaObject::new_tracked(value.into_record()),
            marker: PhantomData,
        }
    }

    pub const fn kind(&self) -> ControlKind {
        T::KIND
    }

    pub fn identity(&self) -> u128 {
        self.object.identity()
    }

    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        ArenaObject::ptr_eq(&this.object, &other.object)
    }

    pub fn borrow(&self) -> Ref<'_, T> {
        Ref::map(self.object.borrow(), |record| {
            T::get(record).expect("typed control handle has the declared kind")
        })
    }

    pub fn borrow_mut(&self) -> RefMut<'_, T> {
        RefMut::map(self.object.borrow_mut(), |record| {
            T::get_mut(record).expect("typed control handle has the declared kind")
        })
    }

    pub fn try_borrow(&self) -> Result<Ref<'_, T>, ObjectBorrowError> {
        Ref::filter_map(self.object.try_borrow()?, T::get)
            .map_err(|_| ObjectBorrowError::WrongControlKind)
    }

    pub fn try_borrow_mut(&self) -> Result<RefMut<'_, T>, ObjectBorrowError> {
        RefMut::filter_map(self.object.try_borrow_mut()?, T::get_mut)
            .map_err(|_| ObjectBorrowError::WrongControlKind)
    }

    pub fn try_unwrap(self) -> Result<T, Self> {
        match self.object.try_unwrap() {
            Ok(record) => Ok(T::from_record(record).expect("typed control handle kind is stable")),
            Err(object) => Err(Self {
                object,
                marker: PhantomData,
            }),
        }
    }

    #[cfg(test)]
    fn reclaim_for_test(&self) {
        self.object.reclaim_for_test();
    }
}

impl ControlHandle<CallableValue> {
    pub fn callable_type(&self) -> TypeId {
        self.borrow().callable_type
    }

    pub fn function(&self) -> u32 {
        self.borrow().function
    }

    pub fn capture(&self) -> ArenaObject<Option<Value>> {
        self.borrow().capture.clone()
    }
}

impl<T: ControlPayload> Clone for ControlHandle<T> {
    fn clone(&self) -> Self {
        Self {
            object: self.object.clone(),
            marker: PhantomData,
        }
    }
}

impl<T: ControlPayload + fmt::Debug> fmt::Debug for ControlHandle<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ControlHandle")
            .field("kind", &self.kind())
            .field("identity", &self.identity())
            .field("value", &*self.borrow())
            .finish()
    }
}

impl<T: ControlPayload + PartialEq> PartialEq for ControlHandle<T> {
    fn eq(&self, other: &Self) -> bool {
        Self::ptr_eq(self, other) || *self.borrow() == *other.borrow()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ArrayValue {
    pub element_type: TypeId,
    /// Compact backing for mutable `Array<u8>` values. Bytecode represents an
    /// octet as `Value::U64`, which makes a compiler byte writer consume tens
    /// of bytes of host memory per emitted byte when it uses `slots`. Keeping
    /// the byte-only case packed is an internal representation detail; any
    /// operation requiring a first-class element reference materializes it.
    pub packed_bytes: Option<Vec<Option<u8>>>,
    pub slots: Vec<Option<Value>>,
    pub logical_capacity: usize,
}

#[derive(Clone, Debug, PartialEq)]
pub struct AggregateValue {
    pub ty: TypeId,
    pub variant: Option<u32>,
    pub fields: Vec<Option<Value>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct CallableValue {
    pub callable_type: TypeId,
    pub function: u32,
    pub capture: ArenaObject<Option<Value>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct HandlerValue {
    pub handler_type: TypeId,
    pub handler_def: u32,
    pub clauses: Vec<Option<Value>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct RuntimeFrame {
    pub function: u32,
    pub pc: u32,
    pub registers: Vec<Option<Value>>,
    pub return_dst: Option<u32>,
    pub delimiter: Option<Value>,
    /// Runtime-owned values whose lifetime must extend through this frame, but
    /// which must not participate in delimiter lookup.
    pub guards: Vec<Value>,
    /// Terminally abandoned frames whose storage is still borrowed by values
    /// passed to this frame. They are destroyed after this frame's own values.
    pub deferred_frames: Vec<RuntimeFrame>,
    pub labels: Vec<RuntimeLabel>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuntimeLabel {
    pub slot: u32,
    pub result_register: u32,
    pub target: u32,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ResumptionValue {
    pub resumption_type: TypeId,
    pub frames: Vec<RuntimeFrame>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ReferenceTarget {
    /// A synthetic owner slot used only while invoking custom drop glue.  The
    /// hook receives a unique reference to this slot; ownership stays with the
    /// destruction machinery until the hook returns.
    DropSlot(SlotHandle),
    /// Storage backing a whole-place borrow of a register value.  The owner
    /// register contains `Value::Place` pointing at the same slot, so the
    /// referent remains stable even when a reference is forwarded to another
    /// frame.  This avoids pointers into a growable VM stack.
    WholePlace(SlotHandle),
    Array(ArenaObject<ArrayValue>),
    ArrayElement {
        array: ArenaObject<ArrayValue>,
        index: usize,
    },
    StaticDataElement {
        data: Rc<StaticDataValue>,
        index: usize,
    },
    Aggregate(ArenaObject<AggregateValue>),
    AggregateField {
        aggregate: ArenaObject<AggregateValue>,
        field: usize,
    },
    CallableCapture(ArenaObject<Option<Value>>),
}

/// A bounded immutable view into one verified artifact data segment. The
/// segment identity is retained separately from its bytes so equal payloads
/// from differently tagged declarations never become interchangeable.
#[derive(Clone, Debug, PartialEq)]
pub struct StaticDataValue {
    pub segment: u32,
    pub tag: u128,
    pub alignment: u32,
    pub bytes: Rc<[u8]>,
    pub offset: usize,
    pub length: usize,
}

/// An owned runtime value. Aggregate slots are optional so execution can
/// represent fields that have been moved out without unsafe memory tricks.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Unit,
    I64(i64),
    I128(i128),
    U64(u64),
    U128(u128),
    F32(f32),
    F64(f64),
    /// Immutable, cheaply copied UTF-8 handle. Primitive concatenation creates
    /// fresh backing, while ordinary bytecode COPY/DEREF_COPY shares it.
    Text(Rc<str>),
    /// Immutable, cheaply copied octet handle. Conversion to Array<u8> is the
    /// explicit mutable deep-copy boundary.
    Bytes(Rc<[u8]>),
    /// Compiler-owned immutable bytes with verifier-established type tag and
    /// range. This is not exposed as a source-level runtime value.
    StaticData(Rc<StaticDataValue>),
    /// Runtime-only indirection installed when a whole register place is
    /// borrowed. It is transparent to bytecode value/type semantics.
    Place(SlotHandle),
    Array(ArenaObject<ArrayValue>),
    Reference {
        referent_type: TypeId,
        unique: bool,
        target: ReferenceTarget,
    },
    Aggregate(ArenaObject<AggregateValue>),
    Callable(ControlHandle<CallableValue>),
    Handler(ControlHandle<HandlerValue>),
    Resumption(ControlHandle<Option<ResumptionValue>>),
}

impl Value {
    pub fn aggregate(ty: TypeId, fields: impl IntoIterator<Item = Value>) -> Self {
        Self::aggregate_with_variant(ty, None, fields)
    }

    pub fn aggregate_with_variant(
        ty: TypeId,
        variant: Option<u32>,
        fields: impl IntoIterator<Item = Value>,
    ) -> Self {
        Self::Aggregate(ArenaObject::new_tracked(AggregateValue {
            ty,
            variant,
            fields: fields.into_iter().map(Some).collect(),
        }))
    }

    pub fn array(element_type: TypeId, values: impl IntoIterator<Item = Value>) -> Self {
        let slots = values.into_iter().map(Some).collect::<Vec<_>>();
        let logical_capacity = slots.len();
        let packed_bytes = (element_type == U8).then(|| {
            slots
                .iter()
                .map(|slot| match slot {
                    Some(Value::U64(value)) => u8::try_from(*value).ok().map(Some),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()
        }).flatten();
        Self::Array(ArenaObject::new_tracked(ArrayValue {
            element_type,
            slots: if packed_bytes.is_some() { Vec::new() } else { slots },
            packed_bytes,
            logical_capacity,
        }))
    }
}

fn value_edge_identities(value: &Value, edges: &mut Vec<u128>) {
    match value {
        Value::Array(object) => edges.push(object.identity()),
        Value::Aggregate(object) => edges.push(object.identity()),
        Value::Callable(handle) => edges.push(handle.object.identity()),
        Value::Handler(handle) => edges.push(handle.object.identity()),
        Value::Resumption(handle) => edges.push(handle.object.identity()),
        Value::Reference { target, .. } => match target {
            ReferenceTarget::Array(object)
            | ReferenceTarget::ArrayElement { array: object, .. } => edges.push(object.identity()),
            ReferenceTarget::Aggregate(object)
            | ReferenceTarget::AggregateField {
                aggregate: object, ..
            } => edges.push(object.identity()),
            ReferenceTarget::CallableCapture(capture) => edges.push(capture.identity()),
            ReferenceTarget::DropSlot(_)
            | ReferenceTarget::WholePlace(_)
            | ReferenceTarget::StaticDataElement { .. } => {}
        },
        _ => {}
    }
}

impl RuntimeEdges for Option<Value> {
    fn edge_identities(&self, edges: &mut Vec<u128>) {
        if let Some(value) = self {
            value_edge_identities(value, edges);
        }
    }

    fn clear_edges(&mut self) {
        *self = None;
    }
}

impl RuntimeEdges for ArrayValue {
    fn edge_identities(&self, edges: &mut Vec<u128>) {
        for value in self.slots.iter().flatten() {
            value_edge_identities(value, edges);
        }
    }

    fn clear_edges(&mut self) {
        if let Some(bytes) = &mut self.packed_bytes {
            bytes.iter_mut().for_each(|slot| *slot = None);
        }
        self.slots.iter_mut().for_each(|slot| *slot = None);
    }
}

impl RuntimeEdges for AggregateValue {
    fn edge_identities(&self, edges: &mut Vec<u128>) {
        for value in self.fields.iter().flatten() {
            value_edge_identities(value, edges);
        }
    }

    fn clear_edges(&mut self) {
        self.fields.iter_mut().for_each(|field| *field = None);
    }
}

impl RuntimeEdges for ControlRecord {
    fn edge_identities(&self, edges: &mut Vec<u128>) {
        fn frame_edge_identities(frame: &RuntimeFrame, edges: &mut Vec<u128>) {
            for value in frame
                .registers
                .iter()
                .flatten()
                .chain(frame.delimiter.iter())
                .chain(&frame.guards)
            {
                value_edge_identities(value, edges);
            }
            for deferred in &frame.deferred_frames {
                frame_edge_identities(deferred, edges);
            }
        }

        match self {
            ControlRecord::Callable(value) => edges.push(value.capture.identity()),
            ControlRecord::Handler(value) => {
                for clause in value.clauses.iter().flatten() {
                    value_edge_identities(clause, edges);
                }
            }
            ControlRecord::Resumption(value) => {
                if let Some(value) = value {
                    for frame in &value.frames {
                        frame_edge_identities(frame, edges);
                    }
                }
            }
        }
    }

    fn clear_edges(&mut self) {
        match self {
            ControlRecord::Callable(value) => *value.capture.borrow_mut() = None,
            ControlRecord::Handler(value) => {
                value.clauses.iter_mut().for_each(|clause| *clause = None)
            }
            ControlRecord::Resumption(value) => *value = None,
        }
    }
}

#[cfg(test)]
mod slot_tests {
    use super::*;

    #[test]
    fn reclamation_registry_prunes_dead_allocation_churn_before_run_end() {
        let scope = ReclamationScope::begin();
        for _ in 0..MIN_RECLAMATION_COMPACTION_INTERVAL {
            drop(Value::aggregate(0, std::iter::empty()));
        }
        assert_eq!(reclamation_diagnostic_counts(), (1, 0));
        scope.finish();
        assert_eq!(reclamation_diagnostic_counts(), (0, 0));
    }

    #[test]
    fn boundary_reclamation_breaks_an_unreachable_callable_capture_cycle() {
        let scope = ReclamationScope::begin();
        let capture = ArenaObject::new_tracked(None);
        let callable = ControlHandle::new(CallableValue {
            callable_type: 0,
            function: 0,
            capture: capture.clone(),
        });
        *capture.borrow_mut() = Some(Value::Callable(callable.clone()));
        let weak_capture = Rc::downgrade(&capture.identity);
        let weak_control = Rc::downgrade(&callable.object.identity);
        drop(callable);
        drop(capture);

        scope.finish();

        assert!(weak_capture.upgrade().is_none());
        assert!(weak_control.upgrade().is_none());
    }

    #[test]
    fn boundary_reclamation_preserves_a_rooted_callable_capture_cycle() {
        let scope = ReclamationScope::begin();
        let capture = ArenaObject::new_tracked(None);
        let callable = ControlHandle::new(CallableValue {
            callable_type: 0,
            function: 0,
            capture: capture.clone(),
        });
        *capture.borrow_mut() = Some(Value::Callable(callable.clone()));
        let weak_capture = Rc::downgrade(&capture.identity);
        let weak_control = Rc::downgrade(&callable.object.identity);

        scope.finish();

        assert!(weak_capture.upgrade().is_some());
        assert!(weak_control.upgrade().is_some());
        assert!(matches!(&*capture.borrow(), Some(Value::Callable(_))));
        *capture.borrow_mut() = None;
        drop(callable);
        drop(capture);
    }

    #[test]
    fn boundary_reclamation_breaks_an_unreachable_resumption_frame_cycle() {
        let scope = ReclamationScope::begin();
        let resumption = ControlHandle::new(None::<ResumptionValue>);
        *resumption.borrow_mut() = Some(ResumptionValue {
            resumption_type: 0,
            frames: vec![RuntimeFrame {
                function: 0,
                pc: 0,
                registers: vec![Some(Value::Resumption(resumption.clone()))],
                return_dst: None,
                delimiter: None,
                guards: vec![],
                deferred_frames: vec![],
                labels: vec![],
            }],
        });
        let weak_control = Rc::downgrade(&resumption.object.identity);
        drop(resumption);

        scope.finish();

        assert!(weak_control.upgrade().is_none());
    }

    #[test]
    fn boundary_reclamation_breaks_a_mixed_recursive_receiver_resumption_cycle() {
        let scope = ReclamationScope::begin();
        let capture = ArenaObject::new_tracked(None);
        let callable = ControlHandle::new(CallableValue {
            callable_type: 0,
            function: 0,
            capture: capture.clone(),
        });
        let resumption = ControlHandle::new(None::<ResumptionValue>);
        *resumption.borrow_mut() = Some(ResumptionValue {
            resumption_type: 0,
            frames: vec![RuntimeFrame {
                function: 0,
                pc: 0,
                registers: vec![Some(Value::Callable(callable.clone()))],
                return_dst: None,
                delimiter: None,
                guards: vec![],
                deferred_frames: vec![],
                labels: vec![],
            }],
        });
        *capture.borrow_mut() = Some(Value::Resumption(resumption.clone()));

        let weak_capture = Rc::downgrade(&capture.identity);
        let weak_callable = Rc::downgrade(&callable.object.identity);
        let weak_resumption = Rc::downgrade(&resumption.object.identity);
        drop(resumption);
        drop(callable);
        drop(capture);

        scope.finish();

        assert!(weak_capture.upgrade().is_none());
        assert!(weak_callable.upgrade().is_none());
        assert!(weak_resumption.upgrade().is_none());
    }

    #[test]
    fn boundary_reclamation_tracks_cycles_inside_deferred_resumption_frames() {
        let capture = ArenaObject::new_tracked(None);
        let callable = ControlHandle::new(CallableValue {
            callable_type: 0,
            function: 0,
            capture: capture.clone(),
        });
        *capture.borrow_mut() = Some(Value::Callable(callable.clone()));
        let resumption = ControlHandle::new(Some(ResumptionValue {
            resumption_type: 0,
            frames: vec![RuntimeFrame {
                function: 0,
                pc: 0,
                registers: vec![],
                return_dst: None,
                delimiter: None,
                guards: vec![],
                deferred_frames: vec![RuntimeFrame {
                    function: 0,
                    pc: 0,
                    registers: vec![Some(Value::Callable(callable.clone()))],
                    return_dst: None,
                    delimiter: None,
                    guards: vec![],
                    deferred_frames: vec![],
                    labels: vec![],
                }],
                labels: vec![],
            }],
        }));
        let weak_capture = Rc::downgrade(&capture.identity);
        let weak_callable = Rc::downgrade(&callable.object.identity);

        let scope = ReclamationScope::begin();
        scope.track_values(&[Value::Resumption(resumption.clone())]);
        drop(resumption);
        drop(callable);
        drop(capture);
        scope.finish();

        assert!(weak_capture.upgrade().is_none());
        assert!(weak_callable.upgrade().is_none());
    }

    #[test]
    fn consuming_a_place_reclaims_it_and_stales_every_alias() {
        let store = SlotStore::default();
        let place = store.insert(Some(Value::I64(9))).unwrap();
        let alias = place.clone();

        assert_eq!(place.take_and_reclaim(), Ok(Value::I64(9)));
        assert!(matches!(alias.get(), Err(ArenaError::Stale { .. })));

        let replacement = store.insert(Some(Value::I64(10))).unwrap();
        assert_ne!(alias, replacement);
        assert_eq!(replacement.get(), Ok(Value::I64(10)));
    }

    #[test]
    fn equal_local_handles_from_distinct_stores_never_alias() {
        let first = SlotStore::default().insert(Some(Value::I64(1))).unwrap();
        let second = SlotStore::default().insert(Some(Value::I64(1))).unwrap();

        assert_ne!(first, second);
        assert_ne!(first.identity(), second.identity());
    }

    #[test]
    fn array_and_aggregate_object_handles_check_staleness_and_store_identity() {
        let array = ArenaObject::new(ArrayValue {
            element_type: 1,
            packed_bytes: None,
            slots: vec![Some(Value::I64(1))],
            logical_capacity: 1,
        });
        let stale_alias = array.clone();
        array.reclaim_for_test();
        assert!(matches!(
            stale_alias.try_borrow(),
            Err(ObjectBorrowError::Stale)
        ));

        let first = ArenaObject::new(AggregateValue {
            ty: 2,
            variant: None,
            fields: vec![],
        });
        let second = ArenaObject::new(AggregateValue {
            ty: 2,
            variant: None,
            fields: vec![],
        });
        assert!(!ArenaObject::ptr_eq(&first, &second));
        assert_ne!(first.identity(), second.identity());
    }

    #[test]
    fn inline_storage_preserves_store_identity_across_reclamation() {
        let array = ArenaObject::new(ArrayValue {
            element_type: 1,
            packed_bytes: None,
            slots: vec![Some(Value::I64(5))],
            logical_capacity: 1,
        });
        let other = ArenaObject::new(ArrayValue {
            element_type: 2,
            packed_bytes: None,
            slots: vec![Some(Value::I64(6))],
            logical_capacity: 1,
        });
        let identity = array.identity();
        // The identity layout mirrors the former single-entry arena handle:
        // the store id occupies the high 64 bits while the inline slot keeps a
        // zero generation+index in the low 32 bits, so stores never collide.
        assert_eq!(identity & u32::MAX as u128, 0);
        assert_eq!(other.identity() & u32::MAX as u128, 0);
        assert_ne!(identity, other.identity());

        let alias = array.clone();
        array.reclaim_for_test();

        // Reclamation staleness every alias but leaves its identity stable.
        assert!(matches!(alias.try_borrow(), Err(ObjectBorrowError::Stale)));
        assert_eq!(alias.identity(), identity);
    }

    #[test]
    fn inline_object_exclusive_borrow_reports_conflict() {
        let aggregate = ArenaObject::new(AggregateValue {
            ty: 2,
            variant: None,
            fields: vec![],
        });
        let guard = aggregate.borrow_mut();
        assert!(matches!(
            aggregate.try_borrow(),
            Err(ObjectBorrowError::Conflict)
        ));
        assert!(matches!(
            aggregate.try_borrow_mut(),
            Err(ObjectBorrowError::Conflict)
        ));
        drop(guard);
        assert_eq!(aggregate.try_borrow().map(|f| f.ty), Ok(2));
    }

    #[test]
    fn callable_capture_lease_defers_reclamation_until_the_last_alias() {
        let capture = ArenaObject::new(Some(Value::I64(7)));
        let shared_alternative = capture.clone();

        let capture = capture
            .try_unwrap()
            .expect_err("a shared handler alternative still owns the capture");
        assert_eq!(*shared_alternative.borrow(), Some(Value::I64(7)));
        drop(shared_alternative);
        assert_eq!(capture.try_unwrap().unwrap(), Some(Value::I64(7)));
    }

    #[test]
    fn stale_callable_capture_access_is_rejected_without_aliasing_reuse() {
        let capture = ArenaObject::new(Some(Value::Unit));
        let stale = capture.clone();
        capture.reclaim_for_test();

        assert!(matches!(stale.try_borrow(), Err(ObjectBorrowError::Stale)));
    }

    #[test]
    fn handler_lease_defers_terminal_reclamation_and_rejects_stale_access() {
        let handler = ControlHandle::new(HandlerValue {
            handler_type: 3,
            handler_def: 4,
            clauses: vec![Some(Value::Unit)],
        });
        let active_clause_guard = handler.clone();

        let handler = handler
            .try_unwrap()
            .expect_err("the active clause still guards the handler");
        assert_eq!(active_clause_guard.borrow().handler_def, 4);
        drop(active_clause_guard);
        assert_eq!(handler.try_unwrap().unwrap().clauses, [Some(Value::Unit)]);

        let handler = ControlHandle::new(HandlerValue {
            handler_type: 3,
            handler_def: 5,
            clauses: vec![],
        });
        let stale = handler.clone();
        handler.reclaim_for_test();
        assert!(matches!(stale.try_borrow(), Err(ObjectBorrowError::Stale)));
    }

    #[test]
    fn equal_handlers_from_distinct_stores_do_not_share_identity() {
        let first = ControlHandle::new(HandlerValue {
            handler_type: 3,
            handler_def: 4,
            clauses: vec![],
        });
        let second = ControlHandle::new(HandlerValue {
            handler_type: 3,
            handler_def: 4,
            clauses: vec![],
        });
        assert!(!ControlHandle::ptr_eq(&first, &second));
        assert_ne!(first.identity(), second.identity());
    }

    #[test]
    fn resumption_lease_requires_unique_terminal_consumption_and_checks_staleness() {
        let resumption = ControlHandle::new(Some(ResumptionValue {
            resumption_type: 6,
            frames: vec![],
        }));
        let borrowed_view = resumption.clone();
        let resumption = resumption
            .try_unwrap()
            .expect_err("a borrowed resumption view is still live");
        assert_eq!(borrowed_view.borrow().as_ref().unwrap().resumption_type, 6);
        drop(borrowed_view);
        assert_eq!(resumption.try_unwrap().unwrap().unwrap().resumption_type, 6);

        let resumption = ControlHandle::new(Some(ResumptionValue {
            resumption_type: 7,
            frames: vec![],
        }));
        let stale = resumption.clone();
        resumption.reclaim_for_test();
        assert!(matches!(stale.try_borrow(), Err(ObjectBorrowError::Stale)));
    }

    #[test]
    fn equal_resumptions_from_distinct_stores_do_not_share_quantity_identity() {
        let first = ControlHandle::new(Some(ResumptionValue {
            resumption_type: 6,
            frames: vec![],
        }));
        let second = ControlHandle::new(Some(ResumptionValue {
            resumption_type: 6,
            frames: vec![],
        }));
        assert!(!ControlHandle::ptr_eq(&first, &second));
        assert_ne!(first.identity(), second.identity());
    }

    #[test]
    fn unified_control_records_report_stable_kinds_for_all_payloads() {
        let callable = ControlHandle::new(CallableValue {
            callable_type: 8,
            function: 9,
            capture: ArenaObject::new(Some(Value::Unit)),
        });
        let handler = ControlHandle::new(HandlerValue {
            handler_type: 10,
            handler_def: 11,
            clauses: vec![],
        });
        let resumption = ControlHandle::new(Some(ResumptionValue {
            resumption_type: 12,
            frames: vec![],
        }));

        assert_eq!(callable.kind(), ControlKind::Callable);
        assert_eq!(handler.kind(), ControlKind::Handler);
        assert_eq!(resumption.kind(), ControlKind::Resumption);
        assert_eq!(callable.borrow().function, 9);
        assert_eq!(handler.borrow().handler_def, 11);
        assert_eq!(resumption.borrow().as_ref().unwrap().resumption_type, 12);
    }

    #[test]
    fn mismatched_typed_control_view_is_rejected() {
        let forged = ControlHandle::<CallableValue> {
            object: ArenaObject::new(ControlRecord::Handler(HandlerValue {
                handler_type: 10,
                handler_def: 11,
                clauses: vec![],
            })),
            marker: PhantomData,
        };
        assert!(matches!(
            forged.try_borrow(),
            Err(ObjectBorrowError::WrongControlKind)
        ));
    }

    #[test]
    fn callable_control_lease_preserves_capture_until_final_owner() {
        let capture = ArenaObject::new(Some(Value::I64(13)));
        let callable = ControlHandle::new(CallableValue {
            callable_type: 8,
            function: 9,
            capture: capture.clone(),
        });
        let borrowed_receiver = callable.clone();

        let callable = callable
            .try_unwrap()
            .expect_err("borrowed receiver still owns the callable record");
        assert!(ArenaObject::ptr_eq(&borrowed_receiver.capture(), &capture));
        drop(borrowed_receiver);
        let payload = callable.try_unwrap().unwrap();
        assert_eq!(payload.function, 9);
        assert!(ArenaObject::ptr_eq(&payload.capture, &capture));
    }
}
