//! Concrete MIR ABI consumed by the existing specialization, cleanup and VM
//! stages. Executable bodies arrive exclusively through Ownership MIR.

use crate::{
    core::{
        CaptureMode, CoreId, CorePattern, EnvironmentBrand, TypedBody,
    },
    identity::{DefKey, Digest},
    instance::InstanceKey,
    mir_storage::{MirSourceStorageScopeId, MirSourceStorageTables},
    placeflow::{PlaceBindingId, PlaceBindingOrigin, PlaceFlow},
    runtime_manifest::{FloatPrimitive, PrimitiveRole},
    signature::{
        ElaboratedEnumVariantPayload, ElaboratedHeader, ElaboratedInterface,
        ElaboratedNominalLayout,
    },
    types::{
        GenericArgument, Mutability, Type,
        is_canonical_generic_argument_identity, is_canonical_type_identity,
        projection_item_arguments_match_kinds,
    },
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
pub(crate) mod atomic;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MirLocal(pub u32);

/// Typed, body-local lexical scope identity.  These are dense arena indices:
/// they describe lowering facts inside one frozen MIR body and are never query
/// or package cache keys.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MirScopeId(pub u32);

/// Typed, body-local identity for one lexical label realization.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MirLabelId(pub u32);

/// Typed, body-local identity for one installed handler frame site.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MirHandlerSiteId(pub u32);

/// Typed, body-local identity for one effect-performance site.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MirPerformSiteId(pub u32);

/// Typed, body-local identity for one continuation capture, resume, forward,
/// or cancellation site.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MirResumptionSiteId(pub u32);

/// Typed, body-local identity for one frozen ownership move path.  Unlike a
/// PlaceFlow `MovePathId`, this may only be used with the MIR body that owns
/// its arena.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MirMovePathId(pub u32);

/// Typed MIR identity for a PlaceFlow lexical binding imported into a frozen
/// function.  `source` retains traceability while preventing a consumer from
/// accidentally using an ID from a different body analysis.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MirPlaceBindingId(pub u32);

/// Stable identity for a cleanup drop flag.  Flags are body-local and are
/// deliberately distinct from locals: a later VM lowering may erase their
/// storage representation, but may not manufacture or retarget one.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MirDropFlagId(pub u32);

impl MirScopeId {
    pub const ROOT: Self = Self(0);
}

const UNASSIGNED_CONTROL_SITE: u32 = u32::MAX;

impl MirLabelId {
    pub const UNASSIGNED: Self = Self(UNASSIGNED_CONTROL_SITE);
}

impl MirHandlerSiteId {
    pub const UNASSIGNED: Self = Self(UNASSIGNED_CONTROL_SITE);
}

impl MirPerformSiteId {
    pub const UNASSIGNED: Self = Self(UNASSIGNED_CONTROL_SITE);
}

impl MirResumptionSiteId {
    pub const UNASSIGNED: Self = Self(UNASSIGNED_CONTROL_SITE);
}

/// Immutable lexical-scope record retained after lowering.  The current
/// Stage-0 lowering has one root scope until cleanup elaboration starts
/// splitting lexical exits, but every block already names its scope so that
/// later passes cannot smuggle a raw stack through an instruction stream.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirScopeData {
    pub parent: Option<MirScopeId>,
    pub entered_label: Option<MirLabelId>,
    pub entered_handler: Option<MirHandlerSiteId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirLabelData {
    pub brand: crate::LabelBrand,
    pub scope: MirScopeId,
    pub destination: MirBlockId,
    pub call_destination: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirHandlerSiteData {
    pub block: MirBlockId,
    pub scope: MirScopeId,
    pub effect: DefKey,
    pub effect_arguments: Vec<crate::GenericArgument>,
    pub operation: u32,
    pub target: MirBlockId,
    pub resume_type: Type,
    pub continuation: MirContinuationPolicy,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirPerformSiteData {
    pub block: MirBlockId,
    pub scope: MirScopeId,
    pub effect: DefKey,
    pub effect_arguments: Vec<crate::GenericArgument>,
    pub operation: u32,
    /// Candidate sites are lexical identities, innermost first.  Stage 0
    /// computes this when freezing the lowerer's linear handler regions.
    pub handler_candidates: Vec<MirHandlerSiteId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MirResumptionSiteKind {
    Capture,
    Resume,
    ResumeReturn,
    ResumeSnapshot,
    Forward,
    Cancel,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirResumptionSiteData {
    pub block: MirBlockId,
    pub scope: MirScopeId,
    pub kind: MirResumptionSiteKind,
    pub originating_handler: Option<MirHandlerSiteId>,
}

/// Frozen local-storage identity imported from PlaceFlow.  `origin` is an
/// exact Typed-Core construction site, never a source spelling lookup.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirPlaceBindingData {
    pub source: PlaceBindingId,
    pub origin: PlaceBindingOrigin,
    pub spelling: String,
}

/// One immutable node in MIR's ownership path arena.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirMovePathData {
    pub parent: Option<MirMovePathId>,
    pub binding: MirPlaceBindingId,
    pub field: Option<u32>,
}

/// Persistent ownership identities for a frozen MIR body.  The compact
/// cleanup facts stay alongside these tables temporarily for VM artifact
/// compatibility, but every MIR cleanup names these typed paths as well.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MirMovePathTables {
    pub bindings: Vec<MirPlaceBindingData>,
    pub paths: Vec<MirMovePathData>,
}

/// Frozen control identity tables for a MIR body.  Instructions and
/// terminators refer to these typed IDs; validation checks the relationship in
/// both directions so no pass can add an executable control edge without its
/// lexical identity record.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirControlTables {
    pub scopes: Vec<MirScopeData>,
    pub labels: Vec<MirLabelData>,
    pub handlers: Vec<MirHandlerSiteData>,
    pub performs: Vec<MirPerformSiteData>,
    pub resumptions: Vec<MirResumptionSiteData>,
    /// Explicit lexical handler prefix retained by a direct nonlocal leave.
    /// Absent entries retain the historical empty prefix; specialized lowering
    /// records this only when a label target stays inside an outer handler.
    pub leave_handler_depths: BTreeMap<MirBlockId, u32>,
    /// Body-wide operation identities share the frozen table boundary with
    /// control identities.  This keeps existing raw `MirFunction` literals
    /// source-compatible while still serializing one stable, body-local arena.
    pub operations: MirOperationArena,
    pub move_paths: MirMovePathTables,
    /// Basic blocks retired by a checked structural edit.  Their numeric IDs
    /// stay reserved so persistent operation and diagnostic identities cannot
    /// be accidentally rebound to a different executable block.
    pub tombstoned_blocks: BTreeSet<MirBlockId>,
    /// Persistent lexical source-storage scopes and their validated
    /// `StorageLive`/`StorageDead` lifecycle events. This is deliberately
    /// distinct from the control scope tree above.
    pub source_storage: MirSourceStorageTables,
    /// Concrete destruction obligations for abandoning this invocation.
    /// Constructed by the same ownership/destruction pass as normal returns;
    /// captures remain owned by their callable environment.
    pub frame_cleanup: Vec<MirFrameDrop>,
    /// Cleanup MIR's complete owner inventory includes unnamed temporaries.
    /// Older hand-built MIR fixtures have only source-binding provenance.
    pub cleanup_owners: Option<Vec<MirLocal>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirFrameDrop {
    pub owner: MirLocal,
    pub destructor: DefKey,
}

/// One lexical frame while the raw CFG is frozen.  These markers are only a
/// construction aid: the finished artifact retains their dense `MirScopeId`
/// tree, while the marker uses the exact typed control-site identity rather
/// than a source spelling or block-number convention.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum MirScopeEntry {
    Label(MirLabelId),
    Handler(MirHandlerSiteId),
}

impl Default for MirControlTables {
    fn default() -> Self {
        Self {
            scopes: vec![MirScopeData {
                parent: None,
                entered_label: None,
                entered_handler: None,
            }],
            labels: vec![],
            handlers: vec![],
            performs: vec![],
            resumptions: vec![],
            leave_handler_depths: BTreeMap::new(),
            operations: MirOperationArena::default(),
            move_paths: MirMovePathTables::default(),
            tombstoned_blocks: BTreeSet::new(),
            source_storage: MirSourceStorageTables::default(),
            frame_cleanup: vec![],
            cleanup_owners: None,
        }
    }
}

/// Append-only, typed storage for locals while a MIR body is being built.
///
/// Body-local basic-block identity. It never crosses a MIR body boundary.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MirBlockId(pub u32);

/// A typed selector for one mutable successor slot in a terminator.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MirEdge {
    Goto,
    Then,
    Else,
    Leave,
}

/// A typed mutable local slot in a terminator.  CFG transformations often
/// preserve the terminator's control shape while changing one incoming phi
/// payload or branch condition; representing those slots explicitly keeps
/// that edit within the checked MIR transaction boundary.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MirTerminatorOperand {
    /// The boolean discriminant of a `SwitchBool` terminator.
    Condition,
    /// The returned value of a `Return` terminator.
    ReturnValue,
    /// One argument carried by a selected successor edge.  The edge selector
    /// prevents callers from accidentally treating a branch payload as a
    /// return value or another successor's phi input.
    EdgeArgument { edge: MirEdge, index: u32 },
}

/// Stable body-local identity for one executable MIR instruction.  Like block
/// identities, operation IDs are never recycled: deleting an instruction
/// leaves a tombstone so diagnostics, analysis worklists, and a later edit
/// cannot accidentally refer to a different operation that happened to take
/// its vector slot.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MirOperationId(pub u32);

/// The live location of one operation in the executable block stream.
///
/// Stage 0 deliberately keeps instructions in their established contiguous
/// block vectors for bytecode emission.  This side arena gives those compact
/// instructions persistent identities without duplicating their payloads.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirOperationData {
    pub block: MirBlockId,
    pub instruction_index: u32,
}

/// Append-only operation identity storage.  An absent entry is an intentional
/// tombstone, not a reusable hole.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MirOperationArena {
    entries: Vec<Option<MirOperationData>>,
}

impl MirOperationArena {
    fn frozen(blocks: &[MirBlock]) -> Self {
        let mut entries = Vec::new();
        for (block_index, block) in blocks.iter().enumerate() {
            for instruction_index in 0..block.instructions.len() {
                entries.push(Some(MirOperationData {
                    block: MirBlockId(block_index as u32),
                    instruction_index: instruction_index as u32,
                }));
            }
        }
        Self { entries }
    }

    pub fn get(&self, id: MirOperationId) -> Option<&MirOperationData> {
        self.entries.get(id.0 as usize)?.as_ref()
    }

    pub fn is_tombstone(&self, id: MirOperationId) -> bool {
        self.entries.get(id.0 as usize).is_some_and(Option::is_none)
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn live_len(&self) -> usize {
        self.entries.iter().flatten().count()
    }

    fn allocate(&mut self, data: MirOperationData) -> MirOperationId {
        let id = MirOperationId(
            u32::try_from(self.entries.len())
                .expect("MIR operation arena exceeded the representable operation identity space"),
        );
        self.entries.push(Some(data));
        id
    }

    fn tombstone(&mut self, id: MirOperationId) -> Option<MirOperationData> {
        self.entries.get_mut(id.0 as usize)?.take()
    }

    fn relocate_block_from(&mut self, block: MirBlockId, from: u32, delta: i32) {
        for data in self.entries.iter_mut().flatten() {
            if data.block == block && data.instruction_index >= from {
                data.instruction_index = if delta.is_negative() {
                    data.instruction_index
                        .checked_sub(delta.unsigned_abs())
                        .expect("MIR operation relocation underflow")
                } else {
                    data.instruction_index
                        .checked_add(delta as u32)
                        .expect("MIR operation relocation overflow")
                };
            }
        }
    }
}

/// Analysis bundles invalidated by a checked MIR edit.  The editor keeps the
/// accumulated mask on the body-edit session; consumers can lazily recompute
/// only the affected facts after `finish`.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct MirAnalysisInvalidation(u8);

impl MirAnalysisInvalidation {
    pub const NONE: Self = Self(0);
    pub const CFG: Self = Self(1);
    pub const USES: Self = Self(2);
    pub const FLOW: Self = Self(4);
    pub const EFFECTS: Self = Self(8);
    pub const VALUES: Self = Self(16);
    pub const COST: Self = Self(32);
    pub const ALL: Self = Self(
        Self::CFG.0 | Self::USES.0 | Self::FLOW.0 | Self::EFFECTS.0 | Self::VALUES.0 | Self::COST.0,
    );

    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    const fn from_bits(bits: u8) -> Self {
        Self(bits)
    }
}

impl std::ops::BitOr for MirAnalysisInvalidation {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::from_bits(self.0 | rhs.0)
    }
}

impl std::ops::BitOrAssign for MirAnalysisInvalidation {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}
/// Pattern decisions in MIR remain source-free and carry exact field types so
/// the verifier need not consult compiler interface tables to validate them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MirPattern {
    Any,
    Literal(String),
    Tuple(Vec<MirPattern>),
    /// Exact-length homogeneous array decision. `element` is frozen so a
    /// forged MIR pattern cannot relabel an array payload on its way to VM.
    Array {
        element: Type,
        elements: Vec<MirPattern>,
        rest: Option<crate::pattern::ArrayPatternRest>,
    },
    Record {
        definition: DefKey,
        /// Complete ordered field-layout proof, inherited from sealed Core.
        field_types: Vec<Type>,
        /// Frozen structural layout proof inherited from Typed Core.  MIR
        /// cannot consult source interface tables, so every selected field
        /// must remain bounded by this arity at the hostile-MIR boundary.
        field_count: u32,
        fields: Vec<MirPatternField>,
    },
    Enum {
        definition: DefKey,
        variant: u32,
        /// Complete ordered payload-layout proof for the selected variant.
        field_types: Vec<Type>,
        /// Payload arity for this exact enum variant.
        field_count: u32,
        fields: Vec<MirPatternField>,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirPatternField {
    pub index: u32,
    pub ty: Type,
    pub pattern: MirPattern,
}

/// The sole NaN payload admitted by frozen MIR and VM artifacts.  IEEE-754
/// deliberately leaves NaN payload propagation largely implementation-defined;
/// retaining arbitrary payloads would therefore let semantically equivalent
/// source programs acquire host-dependent artifact bytes and fingerprints.
pub const CANONICAL_F64_NAN_BITS: u64 = 0x7ff8_0000_0000_0000;
pub const CANONICAL_F32_NAN_BITS: u32 = 0x7fc0_0000;

pub fn canonical_f32_bits(bits: u32) -> u32 {
    if f32::from_bits(bits).is_nan() {
        CANONICAL_F32_NAN_BITS
    } else {
        bits
    }
}

pub fn is_canonical_f32_bits(bits: u32) -> bool {
    canonical_f32_bits(bits) == bits
}

/// Canonicalize the one non-value-equivalent part of an IEEE-754 `f64`
/// representation before it crosses a frozen compiler boundary.
pub fn canonical_f64_bits(bits: u64) -> u64 {
    if f64::from_bits(bits).is_nan() {
        CANONICAL_F64_NAN_BITS
    } else {
        bits
    }
}

/// A frozen float immediate is canonical exactly when it does not encode a
/// payload-distinct NaN spelling.
pub fn is_canonical_f64_bits(bits: u64) -> bool {
    canonical_f64_bits(bits) == bits
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MirInstruction {
    ConstUnit {
        dst: MirLocal,
    },
    ConstI64 {
        dst: MirLocal,
        value: i64,
    },
    ConstU8 {
        dst: MirLocal,
        value: u8,
    },
    ConstU16 {
        dst: MirLocal,
        value: u16,
    },
    ConstU32 {
        dst: MirLocal,
        value: u32,
    },
    ConstU64 {
        dst: MirLocal,
        value: u64,
    },
    ConstUsize {
        dst: MirLocal,
        value: u64,
    },
    ConstU128 {
        dst: MirLocal,
        value: u128,
    },
    ConstI8 {
        dst: MirLocal,
        value: i8,
    },
    ConstI16 {
        dst: MirLocal,
        value: i16,
    },
    ConstI32 {
        dst: MirLocal,
        value: i32,
    },
    ConstIsize {
        dst: MirLocal,
        value: i64,
    },
    ConstI128 {
        dst: MirLocal,
        value: i128,
    },
    /// IEEE-754 values are stored by bit pattern so MIR remains Eq/Hash-safe
    /// and artifact fingerprints never depend on host float formatting.
    ConstF64 {
        dst: MirLocal,
        bits: u64,
    },
    ConstF32 {
        dst: MirLocal,
        bits: u32,
    },
    /// A numeric source literal whose scalar representation is fixed only
    /// when an enclosing generic callable is materialized. This instruction
    /// is internal to generic MIR templates and must be rewritten before VM
    /// verification or emission.
    DeferredLiteral {
        dst: MirLocal,
        text: String,
    },
    /// A finite manifest-authorized IEEE-754 operation.  The primitive
    /// selector is retained as sealed semantic data (not a callable name),
    /// so every f32/f64 conversion and bit cast remains explicit through VM
    /// serialization and independent verification.
    FloatIntrinsic {
        dst: MirLocal,
        primitive: FloatPrimitive,
        arguments: Vec<MirLocal>,
    },
    /// Manifest-bound raw-memory operation, specialized with ordinary source
    /// generics. It owns no collection algorithm or initialized-length policy.
    MemoryIntrinsic {
        dst: MirLocal,
        primitive: crate::MemoryPrimitive,
        types: Vec<Type>,
        arguments: Vec<MirLocal>,
    },
    /// A sealed generic-integer operation whose scalar width is fixed by the
    /// enclosing materialized instance. The primitive role remains an exact
    /// trusted-manifest identity, never a source callable name.
    IntIntrinsic {
        dst: MirLocal,
        primitive: PrimitiveRole,
        scalar: crate::types::ScalarType,
        arguments: Vec<MirLocal>,
    },
    /// Source generic templates retain their integer operation until an
    /// enclosing concrete instance chooses the scalar representation.
    IntGenericIntrinsic {
        dst: MirLocal,
        primitive: PrimitiveRole,
        arguments: Vec<MirLocal>,
    },
    ConstBool {
        dst: MirLocal,
        value: bool,
    },
    ConstChar {
        dst: MirLocal,
        value: u32,
    },
    ConstText {
        dst: MirLocal,
        value: String,
    },
    /// Compiler-emitted, sealed read-only bytes.  This is intentionally not
    /// an array or `Bytes`: the tag and alignment remain part of the artifact
    /// type so embedded data cannot be reinterpreted by ordinary source.
    ConstStaticData {
        dst: MirLocal,
        tag: u128,
        alignment: u32,
        bytes: Vec<u8>,
    },
    StaticLen {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Manifest-bound, capability-free UTF-8 byte-length leaf. The callee's
    /// source identity was checked before lowering; MIR intentionally carries
    /// no name, host symbol, or ambient authority for this operation.
    TextByteLen {
        dst: MirLocal,
        value: MirLocal,
    },
    TextConcat {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    TextEq {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    TextFromUtf8Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    TextAsBytes {
        dst: MirLocal,
        value: MirLocal,
    },
    CharFromU32Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    CharToU32 {
        dst: MirLocal,
        value: MirLocal,
    },
    BytesLen {
        dst: MirLocal,
        value: MirLocal,
    },
    BytesConcat {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    BytesGet {
        dst: MirLocal,
        bytes: MirLocal,
        index: MirLocal,
    },
    BytesSlice {
        dst: MirLocal,
        bytes: MirLocal,
        start: MirLocal,
        end: MirLocal,
    },
    BytesFromArrayMove {
        dst: MirLocal,
        value: MirLocal,
    },
    BytesToArray {
        dst: MirLocal,
        value: MirLocal,
    },
    BytesUtf8ValidUpTo {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Sealed unkeyed BLAKE3 leaf. Its declaration identity was consumed by
    /// runtime-manifest validation before MIR lowering.
    Blake3 {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Read the extent without copying or consuming the array.
    ArrayLen { dst: MirLocal, value: MirLocal },
    /// Assign a compiler-owned, activation-local loop counter.
    StoreUsize { dst: MirLocal, value: MirLocal },
    /// Probe a dynamically indexed move hole.
    ArrayElementIsInitialized { dst: MirLocal, value: MirLocal, index: MirLocal },
    /// Move one element out, leaving a hole in the owning array.
    TakeArrayElement { dst: MirLocal, value: MirLocal, index: MirLocal },
    ArrayGetBorrowShared {
        dst: MirLocal,
        value: MirLocal,
        index: MirLocal,
        element_type: Type,
    },
    ArrayEmpty {
        dst: MirLocal,
        element_type: Type,
    },
    ArrayPushMove {
        value: MirLocal,
        item: MirLocal,
        element_type: Type,
    },
    U32CheckedAdd {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32CheckedSub {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32CheckedMul {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32CheckedDiv {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32CheckedRem {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32WrappingAdd {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32WrappingSub {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32WrappingMul {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32WrappingShl {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32WrappingShr {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32CheckedShl {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32CheckedShr {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32Eq {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32Lt {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32Le {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    U32ToUsize {
        dst: MirLocal,
        value: MirLocal,
    },
    UsizeToU32Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU32Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Exact manifest-bound i64-to-u32 conversion, retaining the low
    /// two's-complement bits rather than checking the range.
    I64ToU32Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToUsizeChecked {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Exact manifest-bound i64-to-usize conversion, retaining the low
    /// two's-complement bits rather than checking the range.
    I64ToUsizeWrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Exact manifest-bound checked i64-to-u8 conversion.
    I64ToU8Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Exact manifest-bound i64-to-u8 conversion, retaining the low
    /// two's-complement bits rather than checking the range.
    I64ToU8Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Exact manifest-bound checked i64-to-u16 conversion.
    I64ToU16Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Exact manifest-bound i64-to-u16 conversion, retaining the low
    /// two's-complement bits rather than checking the range.
    I64ToU16Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToI16Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToI16Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Exact manifest-bound checked i64-to-i32 conversion.
    I64ToI32Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Exact manifest-bound i64-to-i32 conversion retaining low two's-complement bits.
    I64ToI32Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToI8Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToI8Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU64Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU64Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToIsizeChecked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToIsizeWrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU128Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToU128Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToI128Checked {
        dst: MirLocal,
        value: MirLocal,
    },
    I64ToI128Wrapping {
        dst: MirLocal,
        value: MirLocal,
    },
    MakeTuple {
        dst: MirLocal,
        fields: Vec<MirLocal>,
    },
    MakeArray {
        dst: MirLocal,
        fields: Vec<MirLocal>,
        element_type: Type,
    },
    /// A named record preserves its nominal identity while carrying the
    /// canonical field order and types verified by Typed Core. Field types are
    /// embedded so an independently decoded VM artifact can validate every
    /// aggregate operand without consulting compiler-internal interfaces.
    MakeRecord {
        dst: MirLocal,
        definition: DefKey,
        fields: Vec<MirLocal>,
        field_types: Vec<Type>,
    },
    MakeEnum {
        dst: MirLocal,
        definition: DefKey,
        variant: u32,
        fields: Vec<MirLocal>,
        field_types: Vec<Type>,
    },
    ProjectRecord {
        dst: MirLocal,
        base: MirLocal,
        index: u32,
        field_count: u32,
        field_type: Type,
    },
    /// Move an owned projection out of its actual source storage. Unlike an
    /// observational projection, this leaves a typed uninitialized slot in
    /// the containing aggregate, for subsequent structural cleanup.
    TakeProjection {
        dst: MirLocal,
        base: MirLocal,
        fields: Vec<u32>,
    },
    /// Inspect storage initialization without reading the resident value.
    /// This is compiler-owned cleanup machinery, not a source-level test
    /// that permits using a moved value.
    IsInitialized {
        dst: MirLocal,
        base: MirLocal,
        fields: Vec<u32>,
    },
    /// Consume a callable's residual environment through its compiler-selected
    /// bytecode destructor. The invocation signature is not its capture layout.
    DestroyCallable {
        dst: MirLocal,
        value: MirLocal,
    },
    /// An owned-value destruction boundary retained through generic MIR.
    /// Concrete instance materialization expands this into ordinary guarded
    /// calls to compiler-generated glue before executable MIR is emitted.
    Drop {
        local: MirLocal,
    },
    /// Project one statically selected tuple element.  Pattern refinement uses
    /// this alongside nominal projection so tuple binders have the same typed
    /// extraction semantics as record and enum binders.
    ProjectTuple {
        dst: MirLocal,
        base: MirLocal,
        index: u32,
        field_count: u32,
        field_type: Type,
    },
    /// Project an element from an exact-length array pattern.
    ProjectArray {
        dst: MirLocal,
        base: MirLocal,
        index: u32,
        field_count: u32,
        element_type: Type,
    },
    /// Rebuild a nominal record with one statically selected field replaced.
    /// A following `Store` commits it to the root source place.
    UpdateRecord {
        dst: MirLocal,
        base: MirLocal,
        index: u32,
        field_count: u32,
        value: MirLocal,
        field_type: Type,
    },
    /// Evaluate a structural decision against one already-computed subject.
    /// Binder extraction is deliberately a later refinement-environment pass;
    /// this operation only produces the boolean decision result.
    PatternTest {
        dst: MirLocal,
        subject: MirLocal,
        pattern: MirPattern,
    },
    /// An effect transfer selected by source semantic checking. Handler
    /// lowering later rewrites covered sites; an uncovered site reaches the
    /// VM's explicit unhandled-effect boundary.
    Perform {
        site: MirPerformSiteId,
        dst: MirLocal,
        effect: DefKey,
        /// Exact nominal arguments of the protocol instance. `State<i64>`
        /// and `State<Text>` must remain distinct at the handler runtime.
        effect_arguments: Vec<crate::GenericArgument>,
        operation: u32,
        arguments: Vec<MirLocal>,
    },
    /// Install a lexical handler frame. The VM stores the protected
    /// continuation at a matching `Perform` and transfers to `target`; a
    /// `Resume` re-enters that continuation with deep reinstatement.
    InstallHandler {
        site: MirHandlerSiteId,
        effect: DefKey,
        effect_arguments: Vec<crate::GenericArgument>,
        operation: u32,
        payload_destinations: Vec<MirLocal>,
        resume_type: Type,
        continuation: MirContinuationPolicy,
        target: MirBlockId,
    },
    /// Transfer the selected operation packet to its handler payload owners.
    ClaimEffectPayloads { payloads: Vec<MirLocal> },
    UninstallHandler,
    /// End the protected computation of the innermost handler. A pending
    /// callable resumption receives this value before the lexical suffix;
    /// ordinary completion falls through to handler removal and that suffix.
    CompleteHandler { value: MirLocal },
    /// Materialize the identity of the innermost suspended continuation as a
    /// first-class, frame-safe callable snapshot.  The verifier binds this to
    /// an active handler frame; runtime aliases carry the same token rather
    /// than relying on a source binder spelling.
    CaptureResumption {
        site: MirResumptionSiteId,
        dst: MirLocal,
    },
    Resume {
        site: MirResumptionSiteId,
        value: MirLocal,
    },
    /// Resume a replayable continuation and re-enter the handler clause once
    /// that continuation completes, writing its result to `dst`.
    ResumeReturn {
        site: MirResumptionSiteId,
        dst: MirLocal,
        value: MirLocal,
    },
    /// Consume the continuation denoted by an explicit snapshot.  This is
    /// distinct from legacy `Resume`, which consumes the innermost frame and
    /// remains useful for tail-resumption lowering.
    ResumeSnapshot {
        site: MirResumptionSiteId,
        snapshot: MirLocal,
        value: MirLocal,
    },
    /// Decline the innermost suspended handler clause and re-perform its
    /// original operation against the next outer matching frame. The VM keeps
    /// the declined frame in the resumed continuation, which is the deep
    /// forwarding counterpart of `Resume`.
    Forward {
        site: MirResumptionSiteId,
    },
    /// Abandon the innermost suspended continuation. This is legal only for
    /// source continuation contracts that permit zero uses; the VM consumes
    /// the snapshot and continues the handler clause normally.
    Cancel {
        site: MirResumptionSiteId,
    },
    /// Begin the addressable lifetime of one source binding.  The binding is
    /// the frozen PlaceFlow provenance; `local` is its exact executable slot.
    /// Keeping both prevents a later pass from recovering storage from a
    /// spelling or an incidental register number.
    StorageLive {
        binding: MirPlaceBindingId,
        local: MirLocal,
    },
    /// End an addressable lifetime after its value has been moved or
    /// destroyed.  This is an executable counterpart to the source-storage
    /// arena event, not a diagnostic-only witness.
    StorageDead {
        binding: MirPlaceBindingId,
        local: MirLocal,
    },
    /// Materialize a conditional-initialization fact in an ordinary typed
    /// local.  Drop flags are compiler-created `Bool` locals and never have a
    /// source spelling.
    SetDropFlag {
        flag: MirLocal,
        value: bool,
    },
    /// Conditionally zero-destroy a source owner and disarm its slot.  The
    /// MIR validator establishes that the flag is live and associated with
    /// the exact source-storage local before VM lowering may erase this to a
    /// runtime empty-slot transition.
    DestroyIf {
        local: MirLocal,
        flag: MirLocal,
    },
    Copy {
        dst: MirLocal,
        src: MirLocal,
    },
    /// Mutate an existing addressable local after its value operand has been
    /// fully evaluated. Unlike `Copy`, this may overwrite initialized storage
    /// or reinitialize storage emptied by `Move`.
    Store {
        dst: MirLocal,
        src: MirLocal,
    },
    Move {
        dst: MirLocal,
        src: MirLocal,
    },
    /// Create a runtime loan to one root local and its statically selected
    /// field path.  The path is authoritative Typed Core place evidence.
    Borrow {
        dst: MirLocal,
        src: MirLocal,
        fields: Vec<u32>,
        unique: bool,
        /// `true` only for `&*parent` (and its unique form). Borrowing a
        /// local which merely *contains* a reference instead creates a loan
        /// to that carrier slot, preserving the extra reference layer.
        reborrow: bool,
    },
    /// Copy through a live loan without consuming it.
    DerefCopy {
        dst: MirLocal,
        reference: MirLocal,
    },
    /// Move the referent of a unique loan into `dst`. The loan is temporarily
    /// unavailable until a subsequent `DerefStore` restores its referent;
    /// this is how source `move *target` supports `Option::take` without
    /// pretending that an affine value was copied.
    DerefMove {
        dst: MirLocal,
        reference: MirLocal,
    },
    /// Probe the referent while retaining a unique loan's restoration
    /// capability. This also accepts a temporarily moved referent.
    DerefIsInitialized {
        dst: MirLocal,
        reference: MirLocal,
    },
    /// Mutate through a unique live loan without replacing the reference.
    DerefStore {
        reference: MirLocal,
        src: MirLocal,
    },
    NotBool {
        dst: MirLocal,
        value: MirLocal,
    },
    AddI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    /// Distinct from `AddI64`: this exact runtime leaf wraps two's-complement
    /// i64 overflow and is never selected for ordinary checked `+` source.
    WrappingAddI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    /// Distinct from `SubI64`: this exact runtime leaf wraps two's-complement
    /// i64 overflow and is never selected for ordinary checked `-` source.
    WrappingSubI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    /// Distinct from `MulI64`: this exact runtime leaf wraps two's-complement
    /// i64 overflow and is never selected for ordinary checked `*` source.
    WrappingMulI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    /// Exact generic `__g1_int_equal<i64>` runtime leaf. Its public ABI
    /// deliberately returns `u32` rather than the language `Bool` carrier.
    IntEqualI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    /// Exact generic `__g1_int_less<i64>` runtime leaf with its public u32 predicate ABI.
    IntLessI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    /// Exact generic `__g1_int_greater<i64>` runtime leaf with its public u32 predicate ABI.
    IntGreaterI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    /// Exact manifest-bound i64 bitwise-and. This is never ordinary source
    /// arithmetic and remains distinct in the frozen MIR contract.
    BitAndI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    /// Exact manifest-bound unsigned bitwise-and. The width remains part of
    /// the instruction contract so a float bit-pattern helper cannot lose
    /// its u32/u64 identity while crossing into the VM.
    BitAndU32 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    BitAndU64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    /// A generic runtime wrapper body has been type-checked but cannot select
    /// a machine width until its concrete instance is materialized.
    BitAndGeneric {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    /// Exact manifest-bound i64 bitwise-xor. This is never ordinary source
    /// arithmetic and remains distinct in the frozen MIR contract.
    BitXorI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    /// Exact manifest-bound i64 right shift, with a u32 count masked modulo
    /// 64. This stays distinct from checked source arithmetic.
    IntShrI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    /// Exact manifest-bound i64 bitwise-or. This is never ordinary source
    /// arithmetic and remains distinct in the frozen MIR contract.
    BitOrI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    /// Exact manifest-bound i64 bitwise-not. This remains a unary frozen MIR
    /// operation and cannot be reconstructed from the source body.
    BitNotI64 {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Exact manifest-bound i64 left shift with a u32 wrapping count.
    ShlI64 {
        dst: MirLocal,
        value: MirLocal,
        count: MirLocal,
    },
    SubI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    MulI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    DivI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    RemI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    AddF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    ConcatText {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    SubF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    MulF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    DivF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    RemF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    EqI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    NeI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    NeU32 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    NeU64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    LtI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    LeI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    GtI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    GeI64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    EqF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    NeF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    LtF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    LeF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    GtF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    GeF64 {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    EqBool {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    NeBool {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    EqText {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    NeText {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    EqChar {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    NeChar {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    LtChar {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    LeChar {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    GtChar {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    GeChar {
        dst: MirLocal,
        left: MirLocal,
        right: MirLocal,
    },
    /// Closed Runtime ABI: every argument is a prepared, consumed carrier.
    CallOwned { dst: MirLocal, callee: DefKey, arguments: Vec<MirLocal> },
    CallIndirectOwned { dst: MirLocal, callee: MirLocal, arguments: Vec<MirLocal> },
    HostCallOwned {
        dst: MirLocal,
        capability: String,
        symbol: String,
        source_contract: crate::Digest,
        parameters: Vec<Type>,
        result: Type,
        resident_operations: Vec<(Type, Option<DefKey>)>,
        arguments: Vec<MirLocal>,
    },
    Call {
        dst: MirLocal,
        callee: DefKey,
        /// Preserved from Typed Core until the instance materializer replaces
        /// the declaration key with a concrete executable identity.
        generic_arguments: Vec<GenericArgument>,
        trait_instance: Option<MirTraitMethodInstance>,
        arguments: Vec<MirLocal>,
    },
    /// An explicit frozen host boundary. It never refers to a VM function,
    /// so a decoded artifact cannot turn an import into ambient authority.
    HostCall {
        dst: MirLocal,
        capability: String,
        symbol: String,
        source_contract: crate::Digest,
        parameters: Vec<Type>,
        result: Type,
        /// Source-selected destruction operations for native-visible resident
        /// types. Filled after concrete instance discovery, never guessed from
        /// a runtime layout or synthesized by the native linker.
        resident_operations: Vec<(Type, Option<DefKey>)>,
        arguments: Vec<MirLocal>,
    },
    /// A trusted non-fallthrough terminal selected only through the runtime
    /// manifest's exact `Abort` declaration identity.
    Abort,
    /// Materialize a lifted callable together with its ordered environment.
    /// The target's capture parameters occupy the prefix of its parameter
    /// list, before ordinary invocation parameters.
    MakeCallable {
        dst: MirLocal,
        callee: DefKey,
        captures: Vec<MirLocal>,
        /// Closed named-function substitutions are retained until the
        /// instance materializer selects their executable body. Lifted
        /// closures always carry an empty list.
        generic_arguments: Vec<GenericArgument>,
        trait_instance: Option<MirTraitMethodInstance>,
        /// Sealed source-level environment evidence.  Unlike the former
        /// brand-only marker, this preserves the exact ordered capture modes
        /// and types through MIR so neither a forged lowering nor a later VM
        /// producer can replay an environment into a different callable
        /// layout.
        environment: Option<MirCaptureEnvironment>,
    },
    /// Materialize a first-class lexical label capability. The target and
    /// destination are frozen CFG facts; the VM records the dynamic frame
    /// depth at construction so this value can cross generic calls safely.
    MakeLabel {
        label: MirLabelId,
        dst: MirLocal,
        brand: crate::LabelBrand,
        target: MirBlockId,
        destination: MirLocal,
    },
    CallIndirect {
        dst: MirLocal,
        callee: MirLocal,
        arguments: Vec<MirLocal>,
    },
}

/// Source-free callable-environment contract retained by a `MakeCallable`.
/// Names are deliberately absent after Core: the owner-scoped brand plus
/// ordered modes and types are the executable identity of the layout.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirCaptureEnvironment {
    pub brand: EnvironmentBrand,
    pub captures: Vec<MirCapture>,
    pub destructor: Option<DefKey>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirCapture {
    pub mode: CaptureMode,
    pub ty: Type,
}

/// Bind executable capture cleanup to exactly one lifted callable.
pub(crate) fn callable_environment_destructor_definition(callee: DefKey) -> DefKey {
    DefKey(Digest::of_parts([
        b"grandiose-callable-environment-destruction-v1".as_slice(),
        callee.0.as_bytes().as_slice(),
    ]))
}

/// Canonical executable identity of one source-owned anonymous callable.
/// Sharing this derivation prevents a nested brand from naming a sibling.
pub(crate) fn lifted_callable_definition(brand: EnvironmentBrand) -> DefKey {
    let callable = brand.callable.0.to_le_bytes();
    DefKey(Digest::of_parts([
        b"grandiose-stage0-lifted-callable".as_slice(),
        brand.owner.0.as_bytes().as_slice(),
        callable.as_slice(),
    ]))
}

/// Executable identity for a lifted callable cloned into a concrete generic
/// callable instance. The source lift remains identified by its environment
/// brand; the enclosing instance keeps two otherwise identical generic
/// specializations from sharing one body with different concrete layouts.
pub(crate) fn materialized_lifted_callable_definition(
    instance: &InstanceKey,
    source: DefKey,
) -> DefKey {
    DefKey(Digest::of_parts([
        b"grandiose-stage0-lifted-callable-instance-v1".as_slice(),
        instance.fingerprint().as_bytes().as_slice(),
        source.0.as_bytes().as_slice(),
    ]))
}

/// The executable use policy for a handler continuation. Typed Core remains
/// authoritative for exact lower/upper bounds; MIR preserves the distinction
/// the VM must enforce at runtime: affine continuations are consumed, whereas
/// unrestricted continuations retain a replayable snapshot.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MirContinuationPolicy {
    Consume,
    /// An exact finite multi-shot continuation.  The count is frozen from
    /// Typed Core and crosses the VM boundary so bytecode cannot turn an
    /// `[n,n]` source contract into an unbounded replay capability.
    Replay {
        uses: u32,
    },
    /// A bottom-typed operation transfers to its clause without any legal
    /// resumption. The target must cancel the suspended frame before return.
    Terminal,
}

/// Explicit control edge for a MIR basic block. Block parameters are the only
/// phi mechanism; every edge carries an exactly typed argument list.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MirTerminator {
    Goto {
        target: MirBlockId,
        arguments: Vec<MirLocal>,
    },
    /// A branded nonlocal label edge.  The plan is explicit even when this
    /// Stage-0 value runtime has no drop glue: validation and emission must
    /// agree on the exact ownership facts crossed by the edge.
    Leave {
        label: MirLabelId,
        /// The lexical destination identity is retained through MIR even
        /// though a fully specialized VM edge may erase it to a jump.
        brand: crate::LabelBrand,
        target: MirBlockId,
        arguments: Vec<MirLocal>,
        cleanup: MirCleanupPlan,
    },
    SwitchBool {
        condition: MirLocal,
        then_target: MirBlockId,
        then_arguments: Vec<MirLocal>,
        else_target: MirBlockId,
        else_arguments: Vec<MirLocal>,
    },
    Return {
        value: MirLocal,
    },
    Unreachable,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirCleanupPlan {
    /// Exact typed source-storage boundary crossed by this cleanup. These are
    /// distinct from label/handler control scopes and are supplied by
    /// PlaceFlow/lowering, never reverse-engineered from the CFG.
    pub source_storage_scope: MirSourceStorageScopeId,
    pub target_storage_scope: MirSourceStorageScopeId,
    /// Body-local ownership paths which are disarmed by this exit.  These are
    /// authoritative in MIR; `moved_places` is retained only until the VM
    /// artifact has a typed cleanup encoding.
    pub moved_paths: Vec<MirMovePathId>,
    pub moved_places: Vec<crate::MoveFact>,
    pub active_loans: Vec<crate::LoanFact>,
    /// One stable drop flag for every source-storage owner whose scope is
    /// exited. The flag makes conditional initialization explicit even though
    /// the current VM may erase it after checking this witness.
    pub drop_flags: Vec<MirCleanupDropFlag>,
    /// Ordered executable cleanup witness. It is intentionally a typed MIR
    /// object rather than an inference made by VM lowering.
    pub actions: Vec<MirCleanupAction>,
    /// Values intentionally carried across the leave boundary. A protected
    /// source-storage owner is preserved with `Protect`, never dropped.
    pub protected_values: Vec<MirLocal>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MirCleanupDropFlag {
    pub id: MirDropFlagId,
    pub binding: MirPlaceBindingId,
}

/// A single ordered action in a source-storage cleanup witness.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MirCleanupAction {
    /// End every borrow of this owner before changing its lifetime.
    EndBorrow { binding: MirPlaceBindingId },
    /// Conditionally destroy the owner if its flag says it was initialized.
    Drop {
        binding: MirPlaceBindingId,
        flag: MirDropFlagId,
    },
    /// Preserve an owner that is explicitly transferred over the edge.
    Protect {
        binding: MirPlaceBindingId,
        local: MirLocal,
    },
    /// Mark the owner uninitialized after its terminal action.
    ClearDropFlag { flag: MirDropFlagId },
    /// End the addressable source storage lifetime.
    StorageDead { binding: MirPlaceBindingId },
}

impl MirCleanupPlan {
    /// Validate the ownership facts carried across a non-local exit.
    ///
    /// A moved place is a disarmed cleanup slot.  It is therefore not enough
    /// for those paths merely to be sorted: a parent and one of its children
    /// would describe the same storage twice and would run drop glue twice
    /// once the value runtime grows destructors.  Likewise, a live loan may
    /// not overlap a disarmed slot.  PlaceFlow establishes both properties
    /// for source programs; checking them again here keeps forged MIR from
    /// manufacturing an impossible destruction proof.
    pub fn validate(&self) -> Result<(), &'static str> {
        if self.moved_places.iter().any(|place| place.root.is_empty()) {
            return Err("MIR leave cleanup plan has an empty moved-place root");
        }
        if self.active_loans.iter().any(|loan| loan.root.is_empty()) {
            return Err("MIR leave cleanup plan has an empty loan root");
        }
        if self.moved_places.windows(2).any(|pair| pair[0] >= pair[1])
            || self.active_loans.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err("MIR leave cleanup plan is not canonically sorted");
        }
        if self.moved_places.iter().enumerate().any(|(index, place)| {
            self.moved_places[index + 1..].iter().any(|other| {
                place.root == other.root
                    && (place.fields.starts_with(&other.fields)
                        || other.fields.starts_with(&place.fields))
            })
        }) {
            return Err("MIR leave cleanup plan has overlapping moved places");
        }
        if self.moved_places.iter().any(|moved| {
            self.active_loans.iter().any(|loan| {
                moved.root == loan.root
                    && (moved.fields.starts_with(&loan.fields)
                        || loan.fields.starts_with(&moved.fields))
            })
        }) {
            return Err("MIR leave cleanup plan moves a place with a live loan");
        }
        Ok(())
    }

    pub fn validate_with_paths(&self, tables: &MirMovePathTables) -> Result<(), String> {
        if self.moved_paths.len() != self.moved_places.len() {
            return Err("MIR cleanup plan has mismatched typed and legacy move paths".into());
        }
        let mut seen = BTreeSet::new();
        for (index, (&path, fact)) in self.moved_paths.iter().zip(&self.moved_places).enumerate() {
            if !seen.insert(path) {
                return Err("MIR cleanup plan repeats a typed move path".into());
            }
            let data = tables.paths.get(path.0 as usize).ok_or_else(|| {
                format!("MIR cleanup plan references absent move path {}", path.0)
            })?;
            let binding = tables
                .bindings
                .get(data.binding.0 as usize)
                .ok_or_else(|| {
                    format!(
                        "MIR move path {} references absent binding {}",
                        path.0, data.binding.0
                    )
                })?;
            if binding.spelling != fact.root {
                return Err(format!(
                    "MIR cleanup path {index} disagrees with binding spelling"
                ));
            }
            let mut fields = Vec::new();
            let mut cursor = Some(path);
            while let Some(current) = cursor {
                let node = tables.paths.get(current.0 as usize).ok_or_else(|| {
                    format!("MIR cleanup path {index} has stale parent {}", current.0)
                })?;
                if node.binding != data.binding {
                    return Err("MIR move path changes binding across a parent edge".into());
                }
                if let Some(field) = node.field {
                    fields.push(field);
                }
                cursor = node.parent;
            }
            fields.reverse();
            if fields != fact.fields {
                return Err(format!(
                    "MIR cleanup path {index} disagrees with its legacy fields"
                ));
            }
        }
        for loan in &self.active_loans {
            if loan.binding.0 as usize >= tables.bindings.len() {
                return Err(format!(
                    "MIR cleanup loan references absent binding {}",
                    loan.binding.0
                ));
            }
        }
        for &path in &self.moved_paths {
            let moved = &tables.paths[path.0 as usize];
            if self.active_loans.iter().any(|loan| {
                loan.binding.0 == moved.binding.0
                    && path_fields(tables, path).is_some_and(|fields| {
                        fields.starts_with(&loan.fields) || loan.fields.starts_with(&fields)
                    })
            }) {
                return Err("MIR cleanup path overlaps a live typed loan".into());
            }
        }
        Ok(())
    }

    pub fn validate_with_storage(
        &self,
        tables: &MirMovePathTables,
        storage: &MirSourceStorageTables,
    ) -> Result<(), String> {
        self.validate_with_paths(tables)?;
        storage.validate_cleanup_exit(
            tables,
            self.source_storage_scope,
            self.target_storage_scope,
            &self.moved_paths,
        )?;
        self.validate_storage_actions(storage)
    }

    /// Validate the executable lifetime witness.  Every source binding in an
    /// exited lexical frame has exactly one terminal action and a matching
    /// flag transition.  This gives VM lowering a closed, ordered input: it
    /// never has to rediscover storage, drops, or protected values from raw
    /// registers.
    pub fn validate_storage_actions(&self, storage: &MirSourceStorageTables) -> Result<(), String> {
        let expected =
            storage.exited_bindings(self.source_storage_scope, self.target_storage_scope)?;
        if expected.is_empty() {
            if !self.drop_flags.is_empty()
                || !self.actions.is_empty()
                || !self.protected_values.is_empty()
            {
                return Err(
                    "MIR cleanup has a storage witness without exited source storage".into(),
                );
            }
            return Ok(());
        }

        if self
            .protected_values
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
        {
            return Err("MIR cleanup protected values are not canonically sorted".into());
        }
        let expected_set = expected.iter().copied().collect::<BTreeSet<_>>();
        let mut flags = BTreeMap::new();
        for (index, flag) in self.drop_flags.iter().enumerate() {
            if flag.id.0 as usize != index {
                return Err("MIR cleanup drop-flag IDs are not dense and stable".into());
            }
            if !expected_set.contains(&flag.binding)
                || flags.insert(flag.binding, flag.id).is_some()
            {
                return Err(
                    "MIR cleanup drop flags do not account for each exited owner exactly once"
                        .into(),
                );
            }
        }
        if flags.len() != expected.len() {
            return Err("MIR cleanup exit omits a source-storage drop flag".into());
        }

        #[derive(Clone, Copy, Eq, PartialEq)]
        enum Progress {
            Start,
            EndedBorrow,
            Terminal,
            Cleared,
            Dead,
        }
        let mut progress = expected
            .iter()
            .copied()
            .map(|binding| (binding, Progress::Start))
            .collect::<BTreeMap<_, _>>();
        let mut terminal_order = Vec::new();
        for action in &self.actions {
            let binding = match *action {
                MirCleanupAction::EndBorrow { binding }
                | MirCleanupAction::Drop { binding, .. }
                | MirCleanupAction::Protect { binding, .. }
                | MirCleanupAction::StorageDead { binding } => binding,
                MirCleanupAction::ClearDropFlag { flag } => flags
                    .iter()
                    .find_map(|(&binding, &candidate)| (candidate == flag).then_some(binding))
                    .ok_or_else(|| "MIR cleanup clears an unknown drop flag".to_owned())?,
            };
            let state = progress.get_mut(&binding).ok_or_else(|| {
                "MIR cleanup action targets retained or absent source storage".to_owned()
            })?;
            match *action {
                MirCleanupAction::EndBorrow { .. } => {
                    if !matches!(*state, Progress::Start) {
                        return Err(
                            "MIR cleanup ends a borrow after terminal storage cleanup".into()
                        );
                    }
                    *state = Progress::EndedBorrow;
                }
                MirCleanupAction::Drop { flag, .. } => {
                    if !matches!(*state, Progress::Start | Progress::EndedBorrow)
                        || flags[&binding] != flag
                    {
                        return Err(
                            "MIR cleanup drop is out of order or uses the wrong flag".into()
                        );
                    }
                    if storage
                        .binding_local(binding)
                        .is_some_and(|local| self.protected_values.binary_search(&local).is_ok())
                    {
                        return Err("MIR cleanup drops a protected leave value".into());
                    }
                    *state = Progress::Terminal;
                    terminal_order.push(binding);
                }
                MirCleanupAction::Protect { local, .. } => {
                    if !matches!(*state, Progress::Start | Progress::EndedBorrow)
                        || storage.binding_local(binding) != Some(local)
                        || self.protected_values.binary_search(&local).is_err()
                    {
                        return Err(
                            "MIR cleanup protection is not an explicit protected source owner"
                                .into(),
                        );
                    }
                    *state = Progress::Terminal;
                    terminal_order.push(binding);
                }
                MirCleanupAction::ClearDropFlag { flag } => {
                    if *state != Progress::Terminal || flags[&binding] != flag {
                        return Err("MIR cleanup clears a drop flag before terminal cleanup".into());
                    }
                    *state = Progress::Cleared;
                }
                MirCleanupAction::StorageDead { .. } => {
                    if *state != Progress::Cleared {
                        return Err(
                            "MIR cleanup ends source storage before clearing its drop flag".into(),
                        );
                    }
                    *state = Progress::Dead;
                }
            }
        }
        if progress.values().any(|state| *state != Progress::Dead) {
            return Err("MIR cleanup exit omits an ordered source-storage action".into());
        }
        if terminal_order != expected {
            return Err(
                "MIR cleanup does not process source-storage owners in reverse lexical order"
                    .into(),
            );
        }
        Ok(())
    }
}

fn path_fields(tables: &MirMovePathTables, path: MirMovePathId) -> Option<Vec<u32>> {
    let mut fields = Vec::new();
    let mut cursor = Some(path);
    while let Some(current) = cursor {
        let node = tables.paths.get(current.0 as usize)?;
        if let Some(field) = node.field {
            fields.push(field);
        }
        cursor = node.parent;
    }
    fields.reverse();
    Some(fields)
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirBlock {
    /// Lexical scope active throughout this block.  Dynamic handler and label
    /// stacks are reconstructed from this immutable scope tree.
    pub scope: MirScopeId,
    pub parameters: Vec<MirLocal>,
    pub instructions: Vec<MirInstruction>,
    pub terminator: MirTerminator,
}
/// Transactional mutation boundary for an already validated MIR body.
///
/// Lowering constructs raw blocks privately; later transformations use this
/// editor so every successful edit leaves a structurally valid CFG and a
/// rejected edit restores the original immutable graph exactly.
#[derive(Clone, Debug)]
pub struct MirEditor {
    function: MirFunction,
    invalidation: MirAnalysisInvalidation,
}
impl MirEditor {
    pub fn open(function: MirFunction) -> Result<Self, String> {
        let function = function.with_frozen_operation_arena();
        function.validate()?;
        Ok(Self {
            function,
            invalidation: MirAnalysisInvalidation::NONE,
        })
    }
    pub fn append_block(&mut self, block: MirBlock) -> Result<MirBlockId, String> {
        self.transaction(MirAnalysisInvalidation::CFG, |function| {
            let id = MirBlockId(function.blocks.len() as u32);
            let instruction_count = block.instructions.len();
            function.blocks.push(block);
            for instruction_index in 0..instruction_count {
                function.control.operations.allocate(MirOperationData {
                    block: id,
                    instruction_index: instruction_index as u32,
                });
            }
            Ok(id)
        })
    }
    pub fn replace_terminator(
        &mut self,
        block: MirBlockId,
        terminator: MirTerminator,
    ) -> Result<MirAnalysisInvalidation, String> {
        let before = self
            .function
            .blocks
            .get(block.0 as usize)
            .ok_or_else(|| format!("MIR edit targets absent block {}", block.0))?
            .terminator
            .clone();
        let invalidation = terminator_replacement_invalidation(&before, &terminator);
        self.transaction(invalidation, |function| {
            let block_data = function
                .blocks
                .get_mut(block.0 as usize)
                .ok_or_else(|| format!("MIR edit targets absent block {}", block.0))?;
            block_data.terminator = terminator;
            synchronize_terminator_control(function, block)?;
            Ok(())
        })?;
        Ok(invalidation)
    }

    /// Replace one local operand in a terminator without changing its control
    /// shape.  This is deliberately narrower than [`Self::replace_terminator`]
    /// so passes that merely rewrite a phi input or branch discriminant retain
    /// precise invalidation and cannot accidentally retarget an edge.
    pub fn replace_terminator_operand(
        &mut self,
        block: MirBlockId,
        operand: MirTerminatorOperand,
        replacement: MirLocal,
    ) -> Result<MirAnalysisInvalidation, String> {
        let before = self
            .function
            .blocks
            .get(block.0 as usize)
            .ok_or_else(|| format!("MIR edit targets absent block {}", block.0))?
            .terminator
            .clone();
        let mut after = before.clone();
        replace_terminator_operand(&mut after, operand, replacement)?;
        let invalidation = terminator_replacement_invalidation(&before, &after);
        self.transaction(invalidation, |function| {
            let terminator = &mut function
                .blocks
                .get_mut(block.0 as usize)
                .ok_or_else(|| format!("MIR edit targets absent block {}", block.0))?
                .terminator;
            replace_terminator_operand(terminator, operand, replacement)?;
            // This is a no-op for ordinary operand edits today, but retaining
            // the synchronization boundary means any future control-bearing
            // terminator operand cannot bypass frozen label metadata.
            synchronize_terminator_control(function, block)?;
            Ok(())
        })?;
        Ok(invalidation)
    }

    /// Redirect exactly one typed successor edge.  The target's argument
    /// contract and all frozen control identities are checked as one
    /// transaction, so an invalid attempt never leaves a partially rewired
    /// terminator or label table behind.
    pub fn redirect_edge(
        &mut self,
        block: MirBlockId,
        edge: MirEdge,
        target: MirBlockId,
        arguments: Vec<MirLocal>,
    ) -> Result<MirAnalysisInvalidation, String> {
        let invalidation = MirAnalysisInvalidation::ALL;
        self.transaction(invalidation, |function| {
            let terminator = &mut function
                .blocks
                .get_mut(block.0 as usize)
                .ok_or_else(|| format!("MIR edit targets absent block {}", block.0))?
                .terminator;
            redirect_terminator_edge(terminator, edge, target, arguments)?;
            synchronize_terminator_control(function, block)?;
            Ok(())
        })?;
        Ok(invalidation)
    }

    /// Insert a fresh, typed forwarding block on one successor edge.  The
    /// bridge receives the old target's block parameters, then forwards those
    /// same locals to the original destination.  This is the CFG primitive
    /// needed by cleanup insertion and edge-local rewriting: it preserves the
    /// original edge's arguments and all pre-existing block identities.
    pub fn split_edge(
        &mut self,
        block: MirBlockId,
        edge: MirEdge,
    ) -> Result<MirBlockId, String> {
        self.transaction(MirAnalysisInvalidation::ALL, |function| {
            if function.control.tombstoned_blocks.contains(&block) {
                return Err("MIR cannot split an edge from a tombstoned block".into());
            }
            let (target, arguments) = terminator_edge(
                &function
                    .blocks
                    .get(block.0 as usize)
                    .ok_or_else(|| format!("MIR edit targets absent block {}", block.0))?
                    .terminator,
                edge,
            )?;
            if function.control.tombstoned_blocks.contains(&target) {
                return Err("MIR cannot split an edge to a tombstoned block".into());
            }
            let target_block = function
                .blocks
                .get(target.0 as usize)
                .ok_or_else(|| format!("MIR edge targets absent block {}", target.0))?;
            let bridge = MirBlockId(
                u32::try_from(function.blocks.len())
                    .map_err(|_| "MIR block identity space exhausted".to_owned())?,
            );
            let parameters = target_block.parameters.clone();
            function.blocks.push(MirBlock {
                scope: target_block.scope,
                parameters: parameters.clone(),
                instructions: vec![],
                terminator: MirTerminator::Goto {
                    target,
                    arguments: parameters,
                },
            });
            let terminator = &mut function
                .blocks
                .get_mut(block.0 as usize)
                .expect("source block was checked before allocating bridge")
                .terminator;
            redirect_terminator_edge(terminator, edge, bridge, arguments)?;
            // In particular, a `Leave` now targets the bridge. This updates
            // its frozen label destination atomically with the edge, while
            // the bridge retains the original label rejoin as its only exit.
            synchronize_terminator_control(function, block)?;
            Ok(bridge)
        })
    }

    /// Retire every ordinary block that cannot be reached through either a
    /// CFG edge or a frozen dynamic label/handler destination.  Retired block
    /// and operation identities remain reserved as tombstones; blocks that
    /// carry frozen control or source-storage lifecycle facts are rejected
    /// instead of silently dropping those semantic identities.
    pub fn remove_unreachable_blocks(&mut self) -> Result<Vec<MirBlockId>, String> {
        let retired = removable_unreachable_blocks(&self.function)?;
        if retired.is_empty() {
            return Ok(retired);
        }
        self.transaction(MirAnalysisInvalidation::ALL, |function| {
            // Recompute inside the transaction so the validation and the
            // exact tombstone set derive from one immutable body snapshot.
            let retired = removable_unreachable_blocks(function)?;
            for block in &retired {
                for operation in &mut function.control.operations.entries {
                    if operation.as_ref().is_some_and(|data| data.block == *block) {
                        *operation = None;
                    }
                }
                let block_data = function
                    .blocks
                    .get_mut(block.0 as usize)
                    .expect("unreachable block was checked before retirement");
                block_data.parameters.clear();
                block_data.instructions.clear();
                block_data.terminator = MirTerminator::Unreachable;
                function.control.tombstoned_blocks.insert(*block);
            }
            Ok(retired)
        })
    }

    /// Split a block before instruction `at`, preserving every operation ID.
    /// The original block becomes a plain fallthrough to a fresh suffix block;
    /// frozen handler/perform/resumption locations are relocated with their
    /// instructions atomically.
    pub fn split_block(&mut self, block: MirBlockId, at: usize) -> Result<MirBlockId, String> {
        self.transaction(MirAnalysisInvalidation::ALL, |function| {
            let source = function
                .blocks
                .get(block.0 as usize)
                .ok_or_else(|| format!("MIR edit targets absent block {}", block.0))?;
            if function.control.tombstoned_blocks.contains(&block) {
                return Err("MIR cannot split a tombstoned block".into());
            }
            if at > source.instructions.len() {
                return Err(format!(
                    "MIR split index {at} exceeds block {} instruction count {}",
                    block.0,
                    source.instructions.len()
                ));
            }
            let suffix_scope = scope_after_block_prefix(function, block, at)?;
            let suffix = MirBlockId(
                u32::try_from(function.blocks.len())
                    .map_err(|_| "MIR block identity space exhausted".to_owned())?,
            );
            let (instructions, terminator) = {
                let source = function.blocks.get_mut(block.0 as usize).unwrap();
                let instructions = source.instructions.split_off(at);
                let terminator = std::mem::replace(
                    &mut source.terminator,
                    MirTerminator::Goto {
                        target: suffix,
                        arguments: vec![],
                    },
                );
                (instructions, terminator)
            };
            function.blocks.push(MirBlock {
                scope: suffix_scope,
                parameters: vec![],
                instructions,
                terminator,
            });
            // This table is an explicit VM lowering contract, keyed by the
            // block that owns the `Leave` terminator.  Splitting moves that
            // terminator to the suffix, so retaining the old key would make
            // VM lowering reconstruct a different handler prefix.
            if let Some(depth) = function.control.leave_handler_depths.remove(&block) {
                function.control.leave_handler_depths.insert(suffix, depth);
            }
            relocate_operations_after_split(function, block, suffix, at);
            refresh_control_block_sites(function, suffix)?;
            Ok(suffix)
        })
    }

    /// Merge a plain fallthrough successor into its predecessor.  The merged
    /// block ID becomes a tombstone, keeping all existing block handles from
    /// being silently repurposed.
    pub fn merge_blocks(
        &mut self,
        predecessor: MirBlockId,
        successor: MirBlockId,
    ) -> Result<MirAnalysisInvalidation, String> {
        let invalidation = MirAnalysisInvalidation::ALL;
        self.transaction(invalidation, |function| {
            if predecessor == successor {
                return Err("MIR cannot merge a block with itself".into());
            }
            if function.control.tombstoned_blocks.contains(&predecessor)
                || function.control.tombstoned_blocks.contains(&successor)
            {
                return Err("MIR cannot merge a tombstoned block".into());
            }
            let predecessor_block =
                function.blocks.get(predecessor.0 as usize).ok_or_else(|| {
                    format!("MIR merge predecessor block {} is absent", predecessor.0)
                })?;
            let (target, arguments) = match &predecessor_block.terminator {
                MirTerminator::Goto { target, arguments } => (*target, arguments),
                _ => return Err("MIR merge predecessor does not end in a plain goto".into()),
            };
            if target != successor {
                return Err("MIR merge successor is not the predecessor goto target".into());
            }
            let successor_block = function
                .blocks
                .get(successor.0 as usize)
                .ok_or_else(|| format!("MIR merge successor block {} is absent", successor.0))?;
            if predecessor_block.scope != successor_block.scope {
                return Err("MIR merge crosses lexical control scopes".into());
            }
            if successor == function.entry
                || predecessor_count(function, successor) != 1
                || function
                    .control
                    .handlers
                    .iter()
                    .any(|site| site.target == successor)
                || function
                    .control
                    .labels
                    .iter()
                    .any(|label| label.destination == successor)
            {
                return Err("MIR merge successor is an externally visible entry".into());
            }
            if !arguments.is_empty() {
                return Err("MIR merge predecessor goto carries block arguments".into());
            }
            if !successor_block.parameters.is_empty() {
                return Err("MIR merge successor has block parameters".into());
            }
            let instruction_offset = predecessor_block.instructions.len() as u32;
            // A valid table entry can only name the successor's `Leave`
            // terminator. That terminator is about to become the
            // predecessor's terminator, so carry its explicit VM unwind
            // prefix to the surviving block identity before tombstoning the
            // successor.
            let leave_handler_depth = function.control.leave_handler_depths.remove(&successor);
            let (instructions, terminator) = {
                let successor_block = function.blocks.get_mut(successor.0 as usize).unwrap();
                let instructions = std::mem::take(&mut successor_block.instructions);
                let terminator =
                    std::mem::replace(&mut successor_block.terminator, MirTerminator::Unreachable);
                (instructions, terminator)
            };
            let predecessor_block = function.blocks.get_mut(predecessor.0 as usize).unwrap();
            predecessor_block.instructions.extend(instructions);
            predecessor_block.terminator = terminator;
            if let Some(depth) = leave_handler_depth {
                function
                    .control
                    .leave_handler_depths
                    .insert(predecessor, depth);
            }
            for entry in &mut function.control.operations.entries {
                if let Some(data) = entry.as_mut().filter(|data| data.block == successor) {
                    data.block = predecessor;
                    data.instruction_index = data
                        .instruction_index
                        .checked_add(instruction_offset)
                        .ok_or_else(|| {
                            "MIR operation location overflow while merging".to_owned()
                        })?;
                }
            }
            function.control.tombstoned_blocks.insert(successor);
            refresh_control_block_sites(function, predecessor)?;
            Ok(())
        })?;
        Ok(invalidation)
    }
    pub fn replace_instructions(
        &mut self,
        block: MirBlockId,
        instructions: Vec<MirInstruction>,
    ) -> Result<(), String> {
        self.transaction(
            MirAnalysisInvalidation::USES
                | MirAnalysisInvalidation::FLOW
                | MirAnalysisInvalidation::EFFECTS
                | MirAnalysisInvalidation::VALUES
                | MirAnalysisInvalidation::COST,
            |function| {
                let old_operations = function
                    .control
                    .operations
                    .entries
                    .iter()
                    .enumerate()
                    .filter_map(|(index, entry)| {
                        entry
                            .as_ref()
                            .is_some_and(|data| data.block == block)
                            .then_some(MirOperationId(index as u32))
                    })
                    .collect::<Vec<_>>();
                let instruction_count = {
                    let block_data = function
                        .blocks
                        .get_mut(block.0 as usize)
                        .ok_or_else(|| format!("MIR edit targets absent block {}", block.0))?;
                    block_data.instructions = instructions;
                    block_data.instructions.len()
                };
                for operation in old_operations {
                    function.control.operations.tombstone(operation);
                }
                for instruction_index in 0..instruction_count {
                    function.control.operations.allocate(MirOperationData {
                        block,
                        instruction_index: instruction_index as u32,
                    });
                }
                Ok(())
            },
        )
    }
    /// Return the current operation location. Tombstoned and absent IDs are
    /// deliberately indistinguishable to callers that merely need a live
    /// executable instruction; `is_operation_tombstone` preserves that
    /// distinction for diagnostics and editor clients.
    pub fn operation(&self, id: MirOperationId) -> Option<&MirInstruction> {
        let data = self.function.control.operations.get(id)?;
        self.function
            .blocks
            .get(data.block.0 as usize)?
            .instructions
            .get(data.instruction_index as usize)
    }
    pub fn operation_data(&self, id: MirOperationId) -> Option<&MirOperationData> {
        self.function.control.operations.get(id)
    }
    pub fn is_operation_tombstone(&self, id: MirOperationId) -> bool {
        self.function.control.operations.is_tombstone(id)
    }
    pub fn invalidation(&self) -> MirAnalysisInvalidation {
        self.invalidation
    }
    /// Replace one operation without changing its identity.  The returned
    /// mask names exactly the analysis bundles that became stale; a rejected
    /// replacement leaves both the body and accumulated invalidation intact.
    pub fn replace_operation(
        &mut self,
        id: MirOperationId,
        instruction: MirInstruction,
    ) -> Result<MirAnalysisInvalidation, String> {
        let original = self
            .operation(id)
            .cloned()
            .ok_or_else(|| format!("MIR edit targets absent or deleted operation {}", id.0))?;
        let invalidation = operation_replacement_invalidation(&original, &instruction);
        self.transaction(invalidation, |function| {
            let data = function
                .control
                .operations
                .get(id)
                .cloned()
                .ok_or_else(|| format!("MIR edit targets absent or deleted operation {}", id.0))?;
            let operation = function
                .blocks
                .get_mut(data.block.0 as usize)
                .and_then(|block| block.instructions.get_mut(data.instruction_index as usize))
                .ok_or_else(|| format!("MIR operation {} has no live instruction", id.0))?;
            *operation = instruction;
            Ok(())
        })?;
        Ok(invalidation)
    }
    /// Replace one input operand of a live operation without rebuilding that
    /// operation's non-local semantic payload. `input` is zero-based in the
    /// instruction's source-order input list; destinations are deliberately
    /// excluded. The exact replacement remains subject to the normal MIR
    /// type, liveness, control-site, and storage validation transaction.
    pub fn replace_operation_input(
        &mut self,
        id: MirOperationId,
        input: u32,
        replacement: MirLocal,
    ) -> Result<MirAnalysisInvalidation, String> {
        let original = self
            .operation(id)
            .cloned()
            .ok_or_else(|| format!("MIR edit targets absent or deleted operation {}", id.0))?;
        let mut rewritten = original.clone();
        let replaced = *operation_input_mut(&mut rewritten, input)?;
        if self.function.local_type(replaced)? != self.function.local_type(replacement)? {
            return Err("MIR operation input replacement changes the operand type".into());
        }
        *operation_input_mut(&mut rewritten, input)? = replacement;
        let invalidation = operation_replacement_invalidation(&original, &rewritten);
        self.transaction(invalidation, |function| {
            let data = function
                .control
                .operations
                .get(id)
                .cloned()
                .ok_or_else(|| format!("MIR edit targets absent or deleted operation {}", id.0))?;
            let operation = function
                .blocks
                .get_mut(data.block.0 as usize)
                .and_then(|block| block.instructions.get_mut(data.instruction_index as usize))
                .ok_or_else(|| format!("MIR operation {} has no live instruction", id.0))?;
            *operation_input_mut(operation, input)? = replacement;
            Ok(())
        })?;
        Ok(invalidation)
    }
    /// Insert an instruction before a live operation.  The new instruction
    /// receives a fresh ID; existing operation IDs remain stable and their
    /// recorded positions are shifted atomically.
    pub fn insert_before(
        &mut self,
        before: MirOperationId,
        instruction: MirInstruction,
    ) -> Result<MirOperationId, String> {
        self.insert_relative(before, instruction, false)
    }
    /// Insert an instruction after a live operation.  See [`insert_before`]
    /// for identity and invalidation guarantees.
    pub fn insert_after(
        &mut self,
        after: MirOperationId,
        instruction: MirInstruction,
    ) -> Result<MirOperationId, String> {
        self.insert_relative(after, instruction, true)
    }
    fn insert_relative(
        &mut self,
        anchor: MirOperationId,
        instruction: MirInstruction,
        after: bool,
    ) -> Result<MirOperationId, String> {
        let data = self
            .operation_data(anchor)
            .cloned()
            .ok_or_else(|| format!("MIR edit targets absent or deleted operation {}", anchor.0))?;
        let index = data
            .instruction_index
            .checked_add(u32::from(after))
            .ok_or_else(|| "MIR operation insertion index overflow".to_owned())?;
        let invalidation = operation_add_remove_invalidation(&instruction);
        self.transaction(invalidation, |function| {
            let block = function
                .blocks
                .get_mut(data.block.0 as usize)
                .ok_or_else(|| format!("MIR operation {} names absent block", anchor.0))?;
            if index as usize > block.instructions.len() {
                return Err(format!("MIR operation {} has no insertion point", anchor.0));
            }
            block.instructions.insert(index as usize, instruction);
            function
                .control
                .operations
                .relocate_block_from(data.block, index, 1);
            Ok(function.control.operations.allocate(MirOperationData {
                block: data.block,
                instruction_index: index,
            }))
        })
    }
    /// Delete an operation and retain its ID as a tombstone.  Validation is
    /// transactional, so removing a definition that leaves the body invalid
    /// restores both the instruction and its live identity.
    pub fn remove_operation(
        &mut self,
        id: MirOperationId,
    ) -> Result<MirAnalysisInvalidation, String> {
        let data = self
            .operation_data(id)
            .cloned()
            .ok_or_else(|| format!("MIR edit targets absent or deleted operation {}", id.0))?;
        let instruction = self
            .operation(id)
            .cloned()
            .ok_or_else(|| format!("MIR operation {} has no live instruction", id.0))?;
        let invalidation = operation_add_remove_invalidation(&instruction);
        self.transaction(invalidation, |function| {
            let block = function
                .blocks
                .get_mut(data.block.0 as usize)
                .ok_or_else(|| format!("MIR operation {} names absent block", id.0))?;
            if data.instruction_index as usize >= block.instructions.len() {
                return Err(format!("MIR operation {} has no live instruction", id.0));
            }
            block.instructions.remove(data.instruction_index as usize);
            function
                .control
                .operations
                .tombstone(id)
                .ok_or_else(|| format!("MIR edit targets absent or deleted operation {}", id.0))?;
            function.control.operations.relocate_block_from(
                data.block,
                data.instruction_index.saturating_add(1),
                -1,
            );
            Ok(())
        })?;
        Ok(invalidation)
    }
    pub fn finish(self) -> MirFunction {
        self.function
    }
    fn transaction<T>(
        &mut self,
        invalidation: MirAnalysisInvalidation,
        edit: impl FnOnce(&mut MirFunction) -> Result<T, String>,
    ) -> Result<T, String> {
        let original = self.function.clone();
        let value = match edit(&mut self.function) {
            Ok(value) => value,
            Err(error) => {
                self.function = original;
                return Err(error);
            }
        };
        if let Err(error) = self.function.validate() {
            self.function = original;
            return Err(error);
        }
        self.invalidation |= invalidation;
        Ok(value)
    }
}

fn redirect_terminator_edge(
    terminator: &mut MirTerminator,
    edge: MirEdge,
    target: MirBlockId,
    arguments: Vec<MirLocal>,
) -> Result<(), String> {
    match (terminator, edge) {
        (
            MirTerminator::Goto {
                target: slot,
                arguments: slots,
            },
            MirEdge::Goto,
        )
        | (
            MirTerminator::Leave {
                target: slot,
                arguments: slots,
                ..
            },
            MirEdge::Leave,
        ) => {
            *slot = target;
            *slots = arguments;
            Ok(())
        }
        (
            MirTerminator::SwitchBool {
                then_target,
                then_arguments,
                ..
            },
            MirEdge::Then,
        ) => {
            *then_target = target;
            *then_arguments = arguments;
            Ok(())
        }
        (
            MirTerminator::SwitchBool {
                else_target,
                else_arguments,
                ..
            },
            MirEdge::Else,
        ) => {
            *else_target = target;
            *else_arguments = arguments;
            Ok(())
        }
        _ => Err("MIR edge selector does not match the source terminator".into()),
    }
}

fn terminator_edge(
    terminator: &MirTerminator,
    edge: MirEdge,
) -> Result<(MirBlockId, Vec<MirLocal>), String> {
    match (terminator, edge) {
        (MirTerminator::Goto { target, arguments }, MirEdge::Goto)
        | (MirTerminator::Leave {
            target, arguments, ..
        }, MirEdge::Leave) => Ok((*target, arguments.clone())),
        (
            MirTerminator::SwitchBool {
                then_target,
                then_arguments,
                ..
            },
            MirEdge::Then,
        ) => Ok((*then_target, then_arguments.clone())),
        (
            MirTerminator::SwitchBool {
                else_target,
                else_arguments,
                ..
            },
            MirEdge::Else,
        ) => Ok((*else_target, else_arguments.clone())),
        _ => Err("MIR edge selector does not match the source terminator".into()),
    }
}

fn replace_terminator_operand(
    terminator: &mut MirTerminator,
    operand: MirTerminatorOperand,
    replacement: MirLocal,
) -> Result<(), String> {
    match (terminator, operand) {
        (MirTerminator::SwitchBool { condition, .. }, MirTerminatorOperand::Condition) => {
            *condition = replacement;
            Ok(())
        }
        (MirTerminator::Return { value }, MirTerminatorOperand::ReturnValue) => {
            *value = replacement;
            Ok(())
        }
        (
            MirTerminator::Goto { arguments, .. },
            MirTerminatorOperand::EdgeArgument {
                edge: MirEdge::Goto,
                index,
            },
        )
        | (
            MirTerminator::Leave { arguments, .. },
            MirTerminatorOperand::EdgeArgument {
                edge: MirEdge::Leave,
                index,
            },
        ) => {
            let argument = arguments.get_mut(index as usize).ok_or_else(|| {
                format!("MIR edge argument index {index} is outside the selected edge")
            })?;
            *argument = replacement;
            Ok(())
        }
        (
            MirTerminator::SwitchBool { then_arguments, .. },
            MirTerminatorOperand::EdgeArgument {
                edge: MirEdge::Then,
                index,
            },
        ) => {
            let argument = then_arguments.get_mut(index as usize).ok_or_else(|| {
                format!("MIR edge argument index {index} is outside the selected edge")
            })?;
            *argument = replacement;
            Ok(())
        }
        (
            MirTerminator::SwitchBool { else_arguments, .. },
            MirTerminatorOperand::EdgeArgument {
                edge: MirEdge::Else,
                index,
            },
        ) => {
            let argument = else_arguments.get_mut(index as usize).ok_or_else(|| {
                format!("MIR edge argument index {index} is outside the selected edge")
            })?;
            *argument = replacement;
            Ok(())
        }
        (_, MirTerminatorOperand::EdgeArgument { .. }) => {
            Err("MIR edge selector does not match the source terminator".into())
        }
        (_, MirTerminatorOperand::Condition) => {
            Err("MIR condition operand does not match the source terminator".into())
        }
        (_, MirTerminatorOperand::ReturnValue) => {
            Err("MIR return operand does not match the source terminator".into())
        }
    }
}

fn synchronize_terminator_control(
    function: &mut MirFunction,
    block: MirBlockId,
) -> Result<(), String> {
    let terminator = function
        .blocks
        .get(block.0 as usize)
        .ok_or_else(|| format!("MIR edit targets absent block {}", block.0))?
        .terminator
        .clone();
    if let MirTerminator::Leave {
        label,
        brand,
        target,
        ..
    } = terminator
    {
        let entry = function
            .control
            .labels
            .get_mut(label.0 as usize)
            .ok_or_else(|| format!("MIR leave references absent label {}", label.0))?;
        if entry.brand != brand {
            return Err("MIR leave brand disagrees with frozen control table".into());
        }
        entry.destination = target;
    }
    Ok(())
}

fn terminator_replacement_invalidation(
    before: &MirTerminator,
    after: &MirTerminator,
) -> MirAnalysisInvalidation {
    if before == after {
        return MirAnalysisInvalidation::NONE;
    }
    let before_successors = terminator_successors(before);
    let after_successors = terminator_successors(after);
    let mut invalidation = MirAnalysisInvalidation::COST;
    if before_successors != after_successors {
        invalidation |= MirAnalysisInvalidation::CFG
            | MirAnalysisInvalidation::USES
            | MirAnalysisInvalidation::FLOW
            | MirAnalysisInvalidation::EFFECTS
            | MirAnalysisInvalidation::VALUES;
    } else if terminator_references(before) != terminator_references(after) {
        invalidation |= MirAnalysisInvalidation::USES
            | MirAnalysisInvalidation::FLOW
            | MirAnalysisInvalidation::VALUES;
    }
    if matches!(before, MirTerminator::Leave { .. }) || matches!(after, MirTerminator::Leave { .. })
    {
        invalidation |= MirAnalysisInvalidation::EFFECTS | MirAnalysisInvalidation::FLOW;
    }
    invalidation
}

fn terminator_successors(terminator: &MirTerminator) -> Vec<MirBlockId> {
    match terminator {
        MirTerminator::Goto { target, .. } | MirTerminator::Leave { target, .. } => vec![*target],
        MirTerminator::SwitchBool {
            then_target,
            else_target,
            ..
        } => vec![*then_target, *else_target],
        MirTerminator::Return { .. } | MirTerminator::Unreachable => vec![],
    }
}

fn terminator_references(terminator: &MirTerminator) -> Vec<MirLocal> {
    match terminator {
        MirTerminator::Goto { arguments, .. } | MirTerminator::Leave { arguments, .. } => {
            arguments.clone()
        }
        MirTerminator::SwitchBool {
            condition,
            then_arguments,
            else_arguments,
            ..
        } => {
            let mut references = vec![*condition];
            references.extend(then_arguments);
            references.extend(else_arguments);
            references
        }
        MirTerminator::Return { value } => vec![*value],
        MirTerminator::Unreachable => vec![],
    }
}

fn scope_after_block_prefix(
    function: &MirFunction,
    block: MirBlockId,
    at: usize,
) -> Result<MirScopeId, String> {
    let block_data = function
        .blocks
        .get(block.0 as usize)
        .ok_or_else(|| format!("MIR edit targets absent block {}", block.0))?;
    let mut scope = block_data.scope;
    for instruction in &block_data.instructions[..at] {
        match instruction {
            MirInstruction::MakeLabel {
                label: label_id, ..
            } => {
                let label = function
                    .control
                    .labels
                    .get(label_id.0 as usize)
                    .ok_or_else(|| {
                        format!(
                            "MIR split instruction references absent label {}",
                            label_id.0
                        )
                    })?;
                if !scope_enters_label(&function.control, label.scope, scope, *label_id) {
                    return Err("MIR split label disagrees with lexical scope".into());
                }
                scope = label.scope;
            }
            MirInstruction::InstallHandler { site, .. } => {
                let handler = function
                    .control
                    .handlers
                    .get(site.0 as usize)
                    .ok_or_else(|| {
                        format!("MIR split instruction references absent handler {}", site.0)
                    })?;
                if !scope_enters_handler(&function.control, handler.scope, scope, *site) {
                    return Err("MIR split handler disagrees with lexical scope".into());
                }
                scope = handler.scope;
            }
            MirInstruction::UninstallHandler => {
                scope = scope_after_uninstall(&function.control, scope)
                    .ok_or_else(|| "MIR split uninstall escapes lexical scope tree".to_owned())?;
            }
            _ => {}
        }
    }
    Ok(scope)
}

fn relocate_operations_after_split(
    function: &mut MirFunction,
    source: MirBlockId,
    suffix: MirBlockId,
    at: usize,
) {
    for entry in &mut function.control.operations.entries {
        if let Some(data) = entry
            .as_mut()
            .filter(|data| data.block == source && data.instruction_index >= at as u32)
        {
            data.block = suffix;
            data.instruction_index -= at as u32;
        }
    }
}

fn refresh_control_block_sites(
    function: &mut MirFunction,
    block: MirBlockId,
) -> Result<(), String> {
    let instructions = function
        .blocks
        .get(block.0 as usize)
        .ok_or_else(|| format!("MIR control refresh names absent block {}", block.0))?
        .instructions
        .clone();
    for instruction in instructions {
        match instruction {
            MirInstruction::InstallHandler { site, .. } => {
                function
                    .control
                    .handlers
                    .get_mut(site.0 as usize)
                    .ok_or_else(|| format!("MIR handler {} is absent", site.0))?
                    .block = block;
            }
            MirInstruction::Perform { site, .. } => {
                function
                    .control
                    .performs
                    .get_mut(site.0 as usize)
                    .ok_or_else(|| format!("MIR perform {} is absent", site.0))?
                    .block = block;
            }
            MirInstruction::CaptureResumption { site, .. }
            | MirInstruction::Resume { site, .. }
            | MirInstruction::ResumeReturn { site, .. }
            | MirInstruction::ResumeSnapshot { site, .. }
            | MirInstruction::Forward { site }
            | MirInstruction::Cancel { site } => {
                function
                    .control
                    .resumptions
                    .get_mut(site.0 as usize)
                    .ok_or_else(|| format!("MIR resumption {} is absent", site.0))?
                    .block = block;
            }
            _ => {}
        }
    }
    Ok(())
}

fn removable_unreachable_blocks(function: &MirFunction) -> Result<Vec<MirBlockId>, String> {
    let mut reachable = BTreeSet::new();
    let mut pending = VecDeque::from([function.entry]);
    // Label values and installed handlers enter their destinations through
    // dynamic control, not an ordinary terminator edge. Treating those
    // destinations as roots prevents CFG normalization from erasing a valid
    // rejoin or handler clause merely because it has no static predecessor.
    pending.extend(function.control.labels.iter().map(|label| label.destination));
    pending.extend(function.control.handlers.iter().map(|handler| handler.target));
    while let Some(block) = pending.pop_front() {
        if function.control.tombstoned_blocks.contains(&block) || !reachable.insert(block) {
            continue;
        }
        let block_data = function
            .blocks
            .get(block.0 as usize)
            .ok_or_else(|| format!("MIR reachability names absent block {}", block.0))?;
        pending.extend(terminator_successors(&block_data.terminator));
    }
    let retired = function
        .blocks
        .iter()
        .enumerate()
        .map(|(index, _)| MirBlockId(index as u32))
        .filter(|block| {
            !reachable.contains(block) && !function.control.tombstoned_blocks.contains(block)
        })
        .collect::<Vec<_>>();
    if retired.is_empty() {
        return Ok(retired);
    }
    let retired_set = retired.iter().copied().collect::<BTreeSet<_>>();
    if function
        .control
        .labels
        .iter()
        .any(|label| retired_set.contains(&label.destination))
        || function.control.handlers.iter().any(|handler| {
            retired_set.contains(&handler.block) || retired_set.contains(&handler.target)
        })
        || function
            .control
            .performs
            .iter()
            .any(|perform| retired_set.contains(&perform.block))
        || function
            .control
            .resumptions
            .iter()
            .any(|resumption| retired_set.contains(&resumption.block))
        || function
            .control
            .leave_handler_depths
            .keys()
            .any(|block| retired_set.contains(block))
    {
        return Err(
            "MIR cannot retire an unreachable block named by frozen control metadata".into(),
        );
    }
    for block in &retired {
        let block_data = &function.blocks[block.0 as usize];
        if block_data.instructions.iter().any(instruction_has_persistent_identity)
            || matches!(block_data.terminator, MirTerminator::Leave { .. })
        {
            return Err(
                "MIR cannot retire an unreachable block with frozen control or storage lifecycle"
                    .into(),
            );
        }
    }
    Ok(retired)
}

fn instruction_has_persistent_identity(instruction: &MirInstruction) -> bool {
    matches!(
        instruction,
        MirInstruction::MakeLabel { .. }
            | MirInstruction::InstallHandler { .. }
            | MirInstruction::Perform { .. }
            | MirInstruction::CaptureResumption { .. }
            | MirInstruction::Resume { .. }
            | MirInstruction::ResumeReturn { .. }
            | MirInstruction::CompleteHandler { .. }
            | MirInstruction::ResumeSnapshot { .. }
            | MirInstruction::Forward { .. }
            | MirInstruction::Cancel { .. }
            | MirInstruction::StorageLive { .. }
            | MirInstruction::StorageDead { .. }
            | MirInstruction::SetDropFlag { .. }
            | MirInstruction::DestroyIf { .. }
            | MirInstruction::Drop { .. }
    )
}

fn predecessor_count(function: &MirFunction, target: MirBlockId) -> usize {
    function
        .blocks
        .iter()
        .enumerate()
        .filter(|(index, _)| {
            !function
                .control
                .tombstoned_blocks
                .contains(&MirBlockId(*index as u32))
        })
        .flat_map(|(_, block)| terminator_successors(&block.terminator))
        .filter(|successor| *successor == target)
        .count()
}

fn operation_input_slot<'a>(
    input: u32,
    inputs: impl IntoIterator<Item = &'a mut MirLocal>,
) -> Result<&'a mut MirLocal, String> {
    inputs
        .into_iter()
        .nth(input as usize)
        .ok_or_else(|| format!("MIR operation input index {input} is outside the instruction"))
}

fn operation_input_mut(
    instruction: &mut MirInstruction,
    input: u32,
) -> Result<&mut MirLocal, String> {
    match instruction {
        MirInstruction::ConstUnit { .. }
        | MirInstruction::ConstI64 { .. }
        | MirInstruction::ConstU8 { .. }
        | MirInstruction::ConstU16 { .. }
        | MirInstruction::ConstU32 { .. }
        | MirInstruction::ConstU64 { .. }
        | MirInstruction::ConstUsize { .. }
        | MirInstruction::ConstU128 { .. }
        | MirInstruction::ConstI8 { .. }
        | MirInstruction::ConstI16 { .. }
        | MirInstruction::ConstI32 { .. }
        | MirInstruction::ConstIsize { .. }
        | MirInstruction::ConstI128 { .. }
        | MirInstruction::ConstF32 { .. }
        | MirInstruction::ConstF64 { .. }
        | MirInstruction::DeferredLiteral { .. }
        | MirInstruction::ConstBool { .. }
        | MirInstruction::ConstChar { .. }
        | MirInstruction::ConstText { .. }
        | MirInstruction::ConstStaticData { .. }
        | MirInstruction::ArrayEmpty { .. }
        | MirInstruction::InstallHandler { .. }
        | MirInstruction::ClaimEffectPayloads { .. }
        | MirInstruction::UninstallHandler
        | MirInstruction::CaptureResumption { .. }
        | MirInstruction::Forward { .. }
        | MirInstruction::Cancel { .. }
        | MirInstruction::StorageLive { .. }
        | MirInstruction::StorageDead { .. }
        | MirInstruction::SetDropFlag { .. }
        | MirInstruction::Abort
        | MirInstruction::MakeLabel { .. } => Err(format!(
            "MIR operation input index {input} is outside an input-free instruction"
        )),
        MirInstruction::FloatIntrinsic { arguments, .. }
        | MirInstruction::MemoryIntrinsic { arguments, .. }
        | MirInstruction::IntIntrinsic { arguments, .. }
        | MirInstruction::IntGenericIntrinsic { arguments, .. }
        | MirInstruction::Perform { arguments, .. }
        | MirInstruction::CallOwned { arguments, .. }
        | MirInstruction::HostCallOwned { arguments, .. }
        | MirInstruction::Call { arguments, .. }
        | MirInstruction::HostCall { arguments, .. } => operation_input_slot(input, arguments),
        MirInstruction::StoreUsize { value, .. }
        | MirInstruction::ArrayLen { value, .. }
        | MirInstruction::TextByteLen { value, .. }
        | MirInstruction::DestroyCallable { value, .. }
        | MirInstruction::StaticLen { value, .. }
        | MirInstruction::TextFromUtf8Checked { value, .. }
        | MirInstruction::TextAsBytes { value, .. }
        | MirInstruction::CharFromU32Checked { value, .. }
        | MirInstruction::CharToU32 { value, .. }
        | MirInstruction::BytesLen { value, .. }
        | MirInstruction::BytesFromArrayMove { value, .. }
        | MirInstruction::BytesToArray { value, .. }
        | MirInstruction::BytesUtf8ValidUpTo { value, .. }
        | MirInstruction::Blake3 { value, .. }
        | MirInstruction::U32ToUsize { value, .. }
        | MirInstruction::UsizeToU32Checked { value, .. }
        | MirInstruction::I64ToU32Checked { value, .. }
        | MirInstruction::I64ToU32Wrapping { value, .. }
        | MirInstruction::I64ToUsizeChecked { value, .. }
        | MirInstruction::I64ToUsizeWrapping { value, .. }
        | MirInstruction::I64ToU8Checked { value, .. }
        | MirInstruction::I64ToU8Wrapping { value, .. }
        | MirInstruction::I64ToU16Checked { value, .. }
        | MirInstruction::I64ToU16Wrapping { value, .. }
        | MirInstruction::I64ToI16Checked { value, .. }
        | MirInstruction::I64ToI16Wrapping { value, .. }
        | MirInstruction::I64ToI32Checked { value, .. }
        | MirInstruction::I64ToI32Wrapping { value, .. }
        | MirInstruction::I64ToI8Checked { value, .. }
        | MirInstruction::I64ToI8Wrapping { value, .. }
        | MirInstruction::I64ToU64Checked { value, .. }
        | MirInstruction::I64ToU64Wrapping { value, .. }
        | MirInstruction::I64ToIsizeChecked { value, .. }
        | MirInstruction::I64ToIsizeWrapping { value, .. }
        | MirInstruction::I64ToU128Checked { value, .. }
        | MirInstruction::I64ToU128Wrapping { value, .. }
        | MirInstruction::I64ToI128Checked { value, .. }
        | MirInstruction::I64ToI128Wrapping { value, .. }
        | MirInstruction::NotBool { value, .. }
        | MirInstruction::BitNotI64 { value, .. }
        | MirInstruction::DerefIsInitialized {
            reference: value, ..
        }
        | MirInstruction::DerefCopy {
            reference: value, ..
        } | MirInstruction::DerefMove {
            reference: value, ..
        }
        | MirInstruction::Resume { value, .. }
        | MirInstruction::CompleteHandler { value }
        | MirInstruction::ResumeReturn { value, .. }
        | MirInstruction::Copy { src: value, .. }
        | MirInstruction::Store { src: value, .. }
        | MirInstruction::Move { src: value, .. }
        | MirInstruction::Borrow { src: value, .. } => operation_input_slot(input, [value]),
        MirInstruction::TextConcat { left, right, .. }
        | MirInstruction::TextEq { left, right, .. }
        | MirInstruction::BytesConcat { left, right, .. }
        | MirInstruction::U32CheckedAdd { left, right, .. }
        | MirInstruction::U32CheckedSub { left, right, .. }
        | MirInstruction::U32CheckedMul { left, right, .. }
        | MirInstruction::U32CheckedDiv { left, right, .. }
        | MirInstruction::U32CheckedRem { left, right, .. }
        | MirInstruction::U32WrappingAdd { left, right, .. }
        | MirInstruction::U32WrappingSub { left, right, .. }
        | MirInstruction::U32WrappingMul { left, right, .. }
        | MirInstruction::U32WrappingShl { left, right, .. }
        | MirInstruction::U32WrappingShr { left, right, .. }
        | MirInstruction::U32CheckedShl { left, right, .. }
        | MirInstruction::U32CheckedShr { left, right, .. }
        | MirInstruction::U32Eq { left, right, .. }
        | MirInstruction::U32Lt { left, right, .. }
        | MirInstruction::U32Le { left, right, .. }
        | MirInstruction::AddI64 { left, right, .. }
        | MirInstruction::WrappingAddI64 { left, right, .. }
        | MirInstruction::WrappingSubI64 { left, right, .. }
        | MirInstruction::WrappingMulI64 { left, right, .. }
        | MirInstruction::IntEqualI64 { left, right, .. }
        | MirInstruction::IntLessI64 { left, right, .. }
        | MirInstruction::IntGreaterI64 { left, right, .. }
        | MirInstruction::BitAndI64 { left, right, .. }
        | MirInstruction::BitAndU32 { left, right, .. }
        | MirInstruction::BitAndU64 { left, right, .. }
        | MirInstruction::BitAndGeneric { left, right, .. }
        | MirInstruction::BitXorI64 { left, right, .. }
        | MirInstruction::IntShrI64 { left, right, .. }
        | MirInstruction::BitOrI64 { left, right, .. }
        | MirInstruction::SubI64 { left, right, .. }
        | MirInstruction::MulI64 { left, right, .. }
        | MirInstruction::DivI64 { left, right, .. }
        | MirInstruction::RemI64 { left, right, .. }
        | MirInstruction::AddF64 { left, right, .. }
        | MirInstruction::ConcatText { left, right, .. }
        | MirInstruction::SubF64 { left, right, .. }
        | MirInstruction::MulF64 { left, right, .. }
        | MirInstruction::DivF64 { left, right, .. }
        | MirInstruction::RemF64 { left, right, .. }
        | MirInstruction::EqI64 { left, right, .. }
        | MirInstruction::NeI64 { left, right, .. }
        | MirInstruction::NeU32 { left, right, .. }
        | MirInstruction::NeU64 { left, right, .. }
        | MirInstruction::LtI64 { left, right, .. }
        | MirInstruction::LeI64 { left, right, .. }
        | MirInstruction::GtI64 { left, right, .. }
        | MirInstruction::GeI64 { left, right, .. }
        | MirInstruction::EqF64 { left, right, .. }
        | MirInstruction::NeF64 { left, right, .. }
        | MirInstruction::LtF64 { left, right, .. }
        | MirInstruction::LeF64 { left, right, .. }
        | MirInstruction::GtF64 { left, right, .. }
        | MirInstruction::GeF64 { left, right, .. }
        | MirInstruction::EqBool { left, right, .. }
        | MirInstruction::NeBool { left, right, .. }
        | MirInstruction::EqText { left, right, .. }
        | MirInstruction::NeText { left, right, .. }
        | MirInstruction::EqChar { left, right, .. }
        | MirInstruction::NeChar { left, right, .. }
        | MirInstruction::LtChar { left, right, .. }
        | MirInstruction::LeChar { left, right, .. }
        | MirInstruction::GtChar { left, right, .. }
        | MirInstruction::GeChar { left, right, .. } => operation_input_slot(input, [left, right]),
        MirInstruction::TakeArrayElement { value: bytes, index, .. }
        | MirInstruction::ArrayElementIsInitialized { value: bytes, index, .. }
        | MirInstruction::BytesGet { bytes, index, .. } | MirInstruction::ArrayGetBorrowShared {
            value: bytes,
            index,
            ..
        } => operation_input_slot(input, [bytes, index]),
        MirInstruction::BytesSlice {
            bytes, start, end, ..
        } => operation_input_slot(input, [bytes, start, end]),
        MirInstruction::ArrayPushMove { value, item, .. } => {
            operation_input_slot(input, [value, item])
        }
        MirInstruction::MakeTuple { fields, .. }
        | MirInstruction::MakeArray { fields, .. }
        | MirInstruction::MakeRecord { fields, .. }
        | MirInstruction::MakeEnum { fields, .. }
        | MirInstruction::MakeCallable {
            captures: fields, ..
        } => operation_input_slot(input, fields),
        MirInstruction::ProjectRecord { base, .. }
        | MirInstruction::TakeProjection { base, .. }
        | MirInstruction::IsInitialized { base, .. }
        | MirInstruction::ProjectTuple { base, .. }
        | MirInstruction::ProjectArray { base, .. }
        | MirInstruction::PatternTest { subject: base, .. } => operation_input_slot(input, [base]),
        MirInstruction::UpdateRecord { base, value, .. } => operation_input_slot(input, [base, value]),
        MirInstruction::ResumeSnapshot {
            snapshot, value, ..
        } => operation_input_slot(input, [snapshot, value]),
        MirInstruction::DestroyIf { local, flag } => operation_input_slot(input, [local, flag]),
        MirInstruction::Drop { local } => operation_input_slot(input, [local]),
        MirInstruction::DerefStore { reference, src } => operation_input_slot(input, [reference, src]),
        MirInstruction::ShlI64 { value, count, .. } => operation_input_slot(input, [value, count]),
        MirInstruction::CallIndirectOwned { callee, arguments, .. }
        | MirInstruction::CallIndirect {
            callee, arguments, ..
        } => operation_input_slot(input, std::iter::once(callee).chain(arguments.iter_mut())),
    }
}

fn operation_replacement_invalidation(
    before: &MirInstruction,
    after: &MirInstruction,
) -> MirAnalysisInvalidation {
    if before == after {
        return MirAnalysisInvalidation::NONE;
    }
    let mut invalidation = MirAnalysisInvalidation::VALUES | MirAnalysisInvalidation::COST;
    if destination(before) != destination(after) || references(before) != references(after) {
        invalidation |= MirAnalysisInvalidation::USES | MirAnalysisInvalidation::FLOW;
    }
    if operation_is_effectful(before) || operation_is_effectful(after) {
        invalidation |= MirAnalysisInvalidation::EFFECTS;
    }
    invalidation
}

fn operation_add_remove_invalidation(instruction: &MirInstruction) -> MirAnalysisInvalidation {
    let mut invalidation = MirAnalysisInvalidation::COST;
    if destination(instruction).is_some() || !references(instruction).is_empty() {
        invalidation |= MirAnalysisInvalidation::USES
            | MirAnalysisInvalidation::FLOW
            | MirAnalysisInvalidation::VALUES;
    }
    if operation_is_effectful(instruction) {
        invalidation |= MirAnalysisInvalidation::EFFECTS;
    }
    invalidation
}

/// The Effects bundle tracks operations whose ordering, control transfer, or
/// external interaction is semantically observable.  Pure arithmetic and
/// aggregate construction deliberately stay out of this set, letting an
/// editor replacement invalidate only value facts when its operands/outputs
/// have not changed.
fn operation_is_effectful(instruction: &MirInstruction) -> bool {
    matches!(
        instruction,
        MirInstruction::Abort
        | MirInstruction::MemoryIntrinsic { .. }
        | MirInstruction::Store { .. }
        | MirInstruction::DerefStore { .. }
        | MirInstruction::StoreUsize { .. }
        | MirInstruction::TakeArrayElement { .. }
        | MirInstruction::ArrayPushMove { .. }
        | MirInstruction::CallOwned { .. }
        | MirInstruction::CallIndirectOwned { .. }
        | MirInstruction::HostCallOwned { .. }
        | MirInstruction::Call { .. }
        | MirInstruction::CallIndirect { .. }
        | MirInstruction::DestroyCallable { .. }
        | MirInstruction::HostCall { .. }
        | MirInstruction::Perform { .. }
        | MirInstruction::InstallHandler { .. }
        | MirInstruction::UninstallHandler
        | MirInstruction::CaptureResumption { .. }
        | MirInstruction::Resume { .. }
        | MirInstruction::CompleteHandler { .. }
        | MirInstruction::ResumeReturn { .. }
        | MirInstruction::ResumeSnapshot { .. }
        | MirInstruction::Forward { .. }
        | MirInstruction::Cancel { .. }
    )
}
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct MirOptimizationReport {
    pub constant_folds: u32,
    pub eliminated_branches: u32,
    pub eliminated_phis: u32,
}
/// Deterministic sparse constant propagation over validated MIR.
///
/// Arithmetic folds only use checked operations, so overflow and division by
/// zero remain explicit VM traps.  Facts cross only explicitly typed block
/// arguments, and a join retains a fact only when every incoming edge proves
/// the identical value. Transformations commit through `MirEditor`; failed
/// validation restores the unmodified graph.
pub fn optimize(function: MirFunction) -> Result<(MirFunction, MirOptimizationReport), String> {
    // Optimization is speculative: a valid source program must never become
    // uncompilable merely because a simplification invalidates source-storage
    // liveness. Keep the immutable pre-edit MIR so the optimizer can fail
    // closed to an O0 artifact while the editor/validator investigation
    // continues. This is especially important for affine array moves, where
    // preserving an owned remainder across a recursive call is semantically
    // valid but not yet a safe phi-elimination candidate.
    let original = function.clone();
    let mut editor = MirEditor::open(function)?;
    let mut report = MirOptimizationReport::default();
    let entry_constants = block_entry_constants(&editor.function);
    for (index, entry_constants) in entry_constants.into_iter().enumerate() {
        let block = editor.function.blocks[index].clone();
        // A `None` entry has no ordinary CFG proof from the function entry.
        // It may be genuinely unreachable or dynamically entered by a label
        // or handler frame; in either case this sparse pass has no valid
        // incoming fact basis and must leave the block untouched.
        let Some(entry_constants) = entry_constants else {
            continue;
        };
        let (instructions, constants, folds) = fold_block(block.instructions, entry_constants);
        report.constant_folds += folds;
        editor.replace_instructions(MirBlockId(index as u32), instructions)?;
        if let MirTerminator::SwitchBool {
            condition,
            then_target,
            then_arguments,
            else_target,
            else_arguments,
        } = block.terminator
            && let Some(Constant::Bool(value)) = constants.get(&condition)
        {
            editor.replace_terminator(
                MirBlockId(index as u32),
                MirTerminator::Goto {
                    target: if *value { then_target } else { else_target },
                    arguments: if *value {
                        then_arguments
                    } else {
                        else_arguments
                    },
                },
            )?;
            report.eliminated_branches += 1;
        }
    }
    // A block parameter is MIR's phi representation.  After sparse folding
    // has selected every statically known branch, erase a parameter only
    // when every ordinary predecessor transports one identical, already-live
    // local.  Dynamic label and handler entries intentionally remain opaque:
    // their payload is not an ordinary CFG predecessor fact.
    while let Some((block, parameter, replacement, predecessors)) =
        trivial_phi_candidate(&editor.function)
    {
        if simplify_trivial_phi(
            &mut editor,
            block,
            parameter,
            replacement,
            &predecessors,
        )
        .is_ok()
        {
            report.eliminated_phis += 1;
        } else {
            // The candidate is structurally plausible but cannot prove the
            // replacement local live through every edge. Leave it intact;
            // a failed speculative editor transaction has restored the
            // exact original body.
            break;
        }
    }
    // Distinct predecessor registers may still carry one proven literal.
    // Materialize that literal at the target rather than selecting an
    // arbitrary predecessor register; this preserves the typed parallel-edge
    // contract while removing the redundant phi transport itself.
    while let Some((block, parameter, value, predecessors)) =
        constant_phi_candidate(&editor.function)
    {
        if simplify_constant_phi(&mut editor, block, parameter, value, &predecessors).is_ok() {
            report.eliminated_phis += 1;
        } else {
            break;
        }
    }
    let function = editor.finish();
    match function.validate() {
        Ok(()) => Ok((function, report)),
        Err(_) => Ok((original, MirOptimizationReport::default())),
    }
}

fn dynamic_entry_blocks(function: &MirFunction) -> BTreeSet<MirBlockId> {
    function
        .control
        .labels
        .iter()
        .map(|label| label.destination)
        .chain(function.control.handlers.iter().map(|handler| handler.target))
        .collect()
}

/// Return one simplifiable block parameter together with all incoming typed
/// edges. The list is deliberately complete, including unreachable ordinary
/// predecessors, because their argument lists remain part of the validated
/// frozen CFG even when they have no current entry facts.
fn trivial_phi_candidate(
    function: &MirFunction,
) -> Option<(MirBlockId, usize, MirLocal, Vec<(MirBlockId, MirEdge)>)> {
    let dynamic_entries = dynamic_entry_blocks(function);
    for (block_index, block_data) in function.blocks.iter().enumerate() {
        let block = MirBlockId(block_index as u32);
        if block == function.entry
            || function.control.tombstoned_blocks.contains(&block)
            || dynamic_entries.contains(&block)
        {
            continue;
        }
        let predecessors = ordinary_predecessor_edges(function, block);
        if predecessors.is_empty() {
            continue;
        }
        for (parameter_index, &parameter) in block_data.parameters.iter().enumerate() {
            let Some((first_predecessor, first_edge)) = predecessors.first().copied() else {
                continue;
            };
            let replacement = edge_arguments(
                &function.blocks[first_predecessor.0 as usize].terminator,
                first_edge,
            )?
            .get(parameter_index)
            .copied()?;
            if replacement == parameter {
                continue;
            }
            if predecessors.iter().all(|&(predecessor, edge)| {
                edge_arguments(&function.blocks[predecessor.0 as usize].terminator, edge)
                    .and_then(|arguments| arguments.get(parameter_index))
                    == Some(&replacement)
            }) {
                return Some((block, parameter_index, replacement, predecessors));
            }
        }
    }
    None
}

fn constant_phi_candidate(
    function: &MirFunction,
) -> Option<(MirBlockId, usize, Constant, Vec<(MirBlockId, MirEdge)>)> {
    let entries = block_entry_constants(function);
    let dynamic_entries = dynamic_entry_blocks(function);
    for (block_index, block_data) in function.blocks.iter().enumerate() {
        let block = MirBlockId(block_index as u32);
        if block == function.entry
            || function.control.tombstoned_blocks.contains(&block)
            || dynamic_entries.contains(&block)
        {
            continue;
        }
        let predecessors = ordinary_predecessor_edges(function, block);
        if predecessors.is_empty() {
            continue;
        }
        for (parameter_index, &parameter) in block_data.parameters.iter().enumerate() {
            let mut value = None;
            let mut all_agree = true;
            for &(predecessor, edge) in &predecessors {
                let Some(entry) = entries.get(predecessor.0 as usize).cloned().flatten() else {
                    all_agree = false;
                    break;
                };
                let (_, exit, _) = fold_block(
                    function.blocks[predecessor.0 as usize].instructions.clone(),
                    entry,
                );
                let Some(argument) = edge_arguments(
                    &function.blocks[predecessor.0 as usize].terminator,
                    edge,
                )
                .and_then(|arguments| arguments.get(parameter_index))
                else {
                    all_agree = false;
                    break;
                };
                let Some(incoming) = exit.get(argument).cloned() else {
                    all_agree = false;
                    break;
                };
                match &value {
                    Some(previous) if previous != &incoming => {
                        all_agree = false;
                        break;
                    }
                    Some(_) => {}
                    None => value = Some(incoming),
                }
            }
            let Some(value) = value else {
                continue;
            };
            if all_agree && constant_matches_local(function, parameter, &value) {
                return Some((block, parameter_index, value, predecessors));
            }
        }
    }
    None
}

fn constant_matches_local(function: &MirFunction, local: MirLocal, value: &Constant) -> bool {
    let expected = match value {
        Constant::I64(_) => Type::Scalar(crate::types::ScalarType::I64),
        Constant::F32(_) => Type::Scalar(crate::types::ScalarType::F32),
        Constant::F64(_) => Type::Scalar(crate::types::ScalarType::F64),
        Constant::Bool(_) => Type::Scalar(crate::types::ScalarType::Bool),
        Constant::Char(_) => Type::Scalar(crate::types::ScalarType::Char),
        Constant::Text(_) => Type::Scalar(crate::types::ScalarType::Text),
    };
    function.local_type(local).is_ok_and(|actual| actual == &expected)
}

fn ordinary_predecessor_edges(
    function: &MirFunction,
    target: MirBlockId,
) -> Vec<(MirBlockId, MirEdge)> {
    let mut predecessors = Vec::new();
    for (index, block) in function.blocks.iter().enumerate() {
        let source = MirBlockId(index as u32);
        if function.control.tombstoned_blocks.contains(&source) {
            continue;
        }
        match &block.terminator {
            MirTerminator::Goto { target: edge_target, .. } if *edge_target == target => {
                predecessors.push((source, MirEdge::Goto));
            }
            MirTerminator::SwitchBool {
                then_target,
                else_target,
                ..
            } => {
                if *then_target == target {
                    predecessors.push((source, MirEdge::Then));
                }
                if *else_target == target {
                    predecessors.push((source, MirEdge::Else));
                }
            }
            // `Leave` is a branded dynamic transfer. Its target is always a
            // frozen label entry and therefore excluded before this helper is
            // queried; retaining that distinction prevents a direct leave
            // payload from becoming an ordinary phi proof.
            MirTerminator::Leave { .. }
            | MirTerminator::Goto { .. }
            | MirTerminator::Return { .. }
            | MirTerminator::Unreachable => {}
        }
    }
    predecessors
}

fn edge_arguments(terminator: &MirTerminator, edge: MirEdge) -> Option<&[MirLocal]> {
    match (terminator, edge) {
        (MirTerminator::Goto { arguments, .. }, MirEdge::Goto)
        | (MirTerminator::Leave { arguments, .. }, MirEdge::Leave) => Some(arguments),
        (MirTerminator::SwitchBool { then_arguments, .. }, MirEdge::Then) => {
            Some(then_arguments)
        }
        (MirTerminator::SwitchBool { else_arguments, .. }, MirEdge::Else) => {
            Some(else_arguments)
        }
        _ => None,
    }
}

fn edge_arguments_mut(
    terminator: &mut MirTerminator,
    edge: MirEdge,
) -> Result<&mut Vec<MirLocal>, String> {
    match (terminator, edge) {
        (MirTerminator::Goto { arguments, .. }, MirEdge::Goto)
        | (MirTerminator::Leave { arguments, .. }, MirEdge::Leave) => Ok(arguments),
        (MirTerminator::SwitchBool { then_arguments, .. }, MirEdge::Then) => Ok(then_arguments),
        (MirTerminator::SwitchBool { else_arguments, .. }, MirEdge::Else) => Ok(else_arguments),
        _ => Err("MIR phi predecessor edge no longer matches its terminator".into()),
    }
}

fn simplify_trivial_phi(
    editor: &mut MirEditor,
    block: MirBlockId,
    parameter_index: usize,
    replacement: MirLocal,
    predecessors: &[(MirBlockId, MirEdge)],
) -> Result<(), String> {
    editor.transaction(MirAnalysisInvalidation::ALL, |function| {
        let use_region = ordinary_phi_use_region(function, block);
        let parameter = *function
            .blocks
            .get(block.0 as usize)
            .and_then(|block| block.parameters.get(parameter_index))
            .ok_or_else(|| "MIR phi parameter no longer exists".to_owned())?;
        // Block-parameter locals are live through ordinary successor blocks,
        // not lexically confined to their defining block. Rewrite that exact
        // CFG region before retiring the parameter. A separate dynamic
        // label/handler entry deliberately receives no speculative local
        // substitution from an ordinary phi proof.
        for block in use_region {
            let block_data = &mut function.blocks[block.0 as usize];
            for instruction in &mut block_data.instructions {
                replace_instruction_inputs(instruction, parameter, replacement);
            }
            replace_terminator_inputs(&mut block_data.terminator, parameter, replacement);
        }
        function
            .blocks
            .get_mut(block.0 as usize)
            .ok_or_else(|| format!("MIR phi block {} is absent", block.0))?
            .parameters
            .remove(parameter_index);
        for &(predecessor, edge) in predecessors {
            let arguments = edge_arguments_mut(
                &mut function
                    .blocks
                    .get_mut(predecessor.0 as usize)
                    .ok_or_else(|| format!("MIR phi predecessor {} is absent", predecessor.0))?
                    .terminator,
                edge,
            )?;
            if arguments.get(parameter_index) != Some(&replacement) {
                return Err("MIR phi predecessor argument changed during simplification".into());
            }
            arguments.remove(parameter_index);
        }
        Ok(())
    })
}

fn simplify_constant_phi(
    editor: &mut MirEditor,
    block: MirBlockId,
    parameter_index: usize,
    value: Constant,
    predecessors: &[(MirBlockId, MirEdge)],
) -> Result<(), String> {
    editor.transaction(MirAnalysisInvalidation::ALL, |function| {
        let parameter = *function
            .blocks
            .get(block.0 as usize)
            .and_then(|block| block.parameters.get(parameter_index))
            .ok_or_else(|| "MIR constant phi parameter no longer exists".to_owned())?;
        if !constant_matches_local(function, parameter, &value) {
            return Err("MIR constant phi type changed during simplification".into());
        }
        let instruction = constant_instruction(parameter, Some(&value))
            .ok_or_else(|| "MIR constant phi has no materializable value".to_owned())?;
        let block_data = function
            .blocks
            .get_mut(block.0 as usize)
            .ok_or_else(|| format!("MIR constant phi block {} is absent", block.0))?;
        block_data.parameters.remove(parameter_index);
        block_data.instructions.insert(0, instruction);
        function.control.operations.relocate_block_from(block, 0, 1);
        function.control.operations.allocate(MirOperationData {
            block,
            instruction_index: 0,
        });
        for &(predecessor, edge) in predecessors {
            let arguments = edge_arguments_mut(
                &mut function
                    .blocks
                    .get_mut(predecessor.0 as usize)
                    .ok_or_else(|| {
                        format!("MIR constant phi predecessor {} is absent", predecessor.0)
                    })?
                    .terminator,
                edge,
            )?;
            if arguments.get(parameter_index).is_none() {
                return Err("MIR constant phi predecessor lost its argument".into());
            }
            arguments.remove(parameter_index);
        }
        Ok(())
    })
}

fn ordinary_phi_use_region(function: &MirFunction, start: MirBlockId) -> BTreeSet<MirBlockId> {
    let dynamic_entries = dynamic_entry_blocks(function);
    let mut region = BTreeSet::new();
    let mut pending = VecDeque::from([start]);
    while let Some(block) = pending.pop_front() {
        if function.control.tombstoned_blocks.contains(&block) || !region.insert(block) {
            continue;
        }
        let Some(block_data) = function.blocks.get(block.0 as usize) else {
            continue;
        };
        let successors = match &block_data.terminator {
            MirTerminator::Goto { target, .. } => vec![*target],
            MirTerminator::SwitchBool {
                then_target,
                else_target,
                ..
            } => vec![*then_target, *else_target],
            // A `Leave` crosses into a branded dynamic label entry. Its
            // argument carries an independently checked cleanup boundary,
            // so it is not an ordinary phi-use propagation edge.
            MirTerminator::Leave { .. }
            | MirTerminator::Return { .. }
            | MirTerminator::Unreachable => vec![],
        };
        for successor in successors {
            if !dynamic_entries.contains(&successor) {
                pending.push_back(successor);
            }
        }
    }
    region
}

fn replace_instruction_inputs(
    instruction: &mut MirInstruction,
    from: MirLocal,
    to: MirLocal,
) {
    for input in 0.. {
        let Ok(local) = operation_input_mut(instruction, input) else {
            break;
        };
        if *local == from {
            *local = to;
        }
    }
}

fn replace_terminator_inputs(terminator: &mut MirTerminator, from: MirLocal, to: MirLocal) {
    let replace = |local: &mut MirLocal| {
        if *local == from {
            *local = to;
        }
    };
    match terminator {
        MirTerminator::Goto { arguments, .. } | MirTerminator::Leave { arguments, .. } => {
            for argument in arguments {
                replace(argument);
            }
        }
        MirTerminator::SwitchBool {
            condition,
            then_arguments,
            else_arguments,
            ..
        } => {
            replace(condition);
            for argument in then_arguments.iter_mut().chain(else_arguments) {
                replace(argument);
            }
        }
        MirTerminator::Return { value } => replace(value),
        MirTerminator::Unreachable => {}
    }
}
/// Compute the constants available at the entry to every reachable block.
///
/// MIR block parameters are the only phi representation. Consequently an
/// edge contributes a fact solely when its argument is already constant; a
/// merge is the intersection of those incoming facts. This deliberately
/// avoids guessing through mutable storage, calls, effects, or handlers.
fn block_entry_constants(function: &MirFunction) -> Vec<Option<BTreeMap<MirLocal, Constant>>> {
    let mut entries = vec![None; function.blocks.len()];
    let entry = function.entry.0 as usize;
    entries[entry] = Some(BTreeMap::new());
    let mut worklist = VecDeque::from([entry]);
    // A label or handler can supply a payload without traversing any of its
    // ordinary CFG predecessors. Seed that additional predecessor with no
    // constant facts. Otherwise a normal fallthrough value can incorrectly
    // replace a dynamically supplied payload at this join (and downstream).
    for target in dynamic_entry_blocks(function) {
        let target = target.0 as usize;
        if entries[target].is_none() {
            entries[target] = Some(BTreeMap::new());
            worklist.push_back(target);
        }
    }

    while let Some(index) = worklist.pop_front() {
        let Some(entry_facts) = entries[index].clone() else {
            continue;
        };
        let block = &function.blocks[index];
        let (_, exit_facts, _) = fold_block(block.instructions.clone(), entry_facts);
        let mut propagate = |target: MirBlockId, arguments: &[MirLocal]| {
            let target_index = target.0 as usize;
            let incoming = function.blocks[target_index]
                .parameters
                .iter()
                .zip(arguments)
                .filter_map(|(&parameter, &argument)| {
                    exit_facts
                        .get(&argument)
                        .cloned()
                        .map(|value| (parameter, value))
                })
                .collect::<BTreeMap<_, _>>();
            if merge_constant_entry(&mut entries[target_index], incoming) {
                worklist.push_back(target_index);
            }
        };
        match &block.terminator {
            MirTerminator::Goto { target, arguments }
            | MirTerminator::Leave {
                target, arguments, ..
            } => propagate(*target, arguments),
            MirTerminator::SwitchBool {
                condition,
                then_target,
                then_arguments,
                else_target,
                else_arguments,
            } => match exit_facts.get(condition) {
                Some(Constant::Bool(true)) => propagate(*then_target, then_arguments),
                Some(Constant::Bool(false)) => propagate(*else_target, else_arguments),
                _ => {
                    propagate(*then_target, then_arguments);
                    propagate(*else_target, else_arguments);
                }
            },
            MirTerminator::Return { .. } | MirTerminator::Unreachable => {}
        }
    }
    entries
}

fn merge_constant_entry(
    existing: &mut Option<BTreeMap<MirLocal, Constant>>,
    incoming: BTreeMap<MirLocal, Constant>,
) -> bool {
    let Some(existing) = existing else {
        *existing = Some(incoming);
        return true;
    };
    let before = existing.clone();
    existing.retain(|local, value| incoming.get(local) == Some(value));
    *existing != before
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Constant {
    I64(i64),
    F32(u32),
    F64(u64),
    Bool(bool),
    Char(u32),
    Text(String),
}
fn fold_block(
    instructions: Vec<MirInstruction>,
    mut constants: BTreeMap<MirLocal, Constant>,
) -> (Vec<MirInstruction>, BTreeMap<MirLocal, Constant>, u32) {
    let mut output = Vec::with_capacity(instructions.len());
    let mut folds = 0;
    for original in instructions {
        let folded = match original.clone() {
            MirInstruction::Copy { dst, src } => constant_instruction(dst, constants.get(&src)),
            MirInstruction::PatternTest {
                dst,
                subject,
                pattern,
            } => fold_pattern_test(dst, constants.get(&subject), &pattern),
            MirInstruction::NotBool { dst, value } => match constants.get(&value) {
                Some(Constant::Bool(value)) => {
                    Some(MirInstruction::ConstBool { dst, value: !value })
                }
                _ => None,
            },
            MirInstruction::AddI64 { dst, left, right } => {
                fold_i64(dst, &constants, left, right, i64::checked_add)
            }
            MirInstruction::WrappingAddI64 { .. } => None,
            MirInstruction::WrappingSubI64 { .. } => None,
            MirInstruction::WrappingMulI64 { .. } => None,
            MirInstruction::IntEqualI64 { .. }
            | MirInstruction::IntLessI64 { .. }
            | MirInstruction::IntGreaterI64 { .. }
            | MirInstruction::BitAndI64 { .. }
            | MirInstruction::BitAndU32 { .. }
            | MirInstruction::BitAndU64 { .. }
            | MirInstruction::BitAndGeneric { .. }
            | MirInstruction::BitOrI64 { .. }
            | MirInstruction::BitXorI64 { .. }
            | MirInstruction::IntShrI64 { .. }
            | MirInstruction::BitNotI64 { .. } => None,
            MirInstruction::ShlI64 { .. } => None,
            MirInstruction::SubI64 { dst, left, right } => {
                fold_i64(dst, &constants, left, right, i64::checked_sub)
            }
            MirInstruction::MulI64 { dst, left, right } => {
                fold_i64(dst, &constants, left, right, i64::checked_mul)
            }
            MirInstruction::DivI64 { dst, left, right } => {
                fold_i64(dst, &constants, left, right, i64::checked_div)
            }
            MirInstruction::RemI64 { dst, left, right } => {
                fold_i64(dst, &constants, left, right, i64::checked_rem)
            }
            MirInstruction::EqI64 { dst, left, right } => {
                fold_reflexive_predicate(dst, left, right, true).or_else(|| {
                    fold_i64_predicate(dst, &constants, left, right, |left, right| left == right)
                })
            }
            MirInstruction::NeI64 { dst, left, right } => {
                fold_reflexive_predicate(dst, left, right, false).or_else(|| {
                    fold_i64_predicate(dst, &constants, left, right, |left, right| left != right)
                })
            }
            MirInstruction::NeU32 { dst, left, right }
            | MirInstruction::NeU64 { dst, left, right } => {
                fold_reflexive_predicate(dst, left, right, false)
            }
            MirInstruction::LtI64 { dst, left, right } => {
                fold_reflexive_predicate(dst, left, right, false).or_else(|| {
                    fold_i64_predicate(dst, &constants, left, right, |left, right| left < right)
                })
            }
            MirInstruction::LeI64 { dst, left, right } => {
                fold_reflexive_predicate(dst, left, right, true).or_else(|| {
                    fold_i64_predicate(dst, &constants, left, right, |left, right| left <= right)
                })
            }
            MirInstruction::GtI64 { dst, left, right } => {
                fold_reflexive_predicate(dst, left, right, false).or_else(|| {
                    fold_i64_predicate(dst, &constants, left, right, |left, right| left > right)
                })
            }
            MirInstruction::GeI64 { dst, left, right } => {
                fold_reflexive_predicate(dst, left, right, true).or_else(|| {
                    fold_i64_predicate(dst, &constants, left, right, |left, right| left >= right)
                })
            }
            MirInstruction::EqBool { dst, left, right } => {
                fold_reflexive_predicate(dst, left, right, true).or_else(|| {
                    fold_bool_predicate(dst, &constants, left, right, |left, right| left == right)
                })
            }
            MirInstruction::NeBool { dst, left, right } => {
                fold_reflexive_predicate(dst, left, right, false).or_else(|| {
                    fold_bool_predicate(dst, &constants, left, right, |left, right| left != right)
                })
            }
            _ => None,
        };
        let did_fold = folded.is_some();
        let instruction = folded.unwrap_or(original);
        if did_fold {
            folds += 1;
        }
        // Constants describe the current contents of addressable locals, not
        // immutable SSA values. A unique dereference may update any local
        // reachable through its sealed loan path; an ordinary call or
        // resumption may do the same in a different frame. Until this pass
        // tracks that alias set precisely, discard every fact at those
        // boundaries. In particular, do not turn a read of `value` after
        // `overwrite(&mut value)` back into the initializer literal.
        if invalidates_alias_visible_constants(&instruction) {
            constants.clear();
        }
        match instruction {
            MirInstruction::ConstI64 { dst, value } => {
                constants.insert(dst, Constant::I64(value));
            }
            MirInstruction::ConstF64 { dst, bits } => {
                constants.insert(dst, Constant::F64(bits));
            }
            MirInstruction::ConstF32 { dst, bits } => {
                constants.insert(dst, Constant::F32(bits));
            }
            MirInstruction::ConstBool { dst, value } => {
                constants.insert(dst, Constant::Bool(value));
            }
            MirInstruction::ConstChar { dst, value } => {
                constants.insert(dst, Constant::Char(value));
            }
            MirInstruction::ConstText { dst, ref value } => {
                constants.insert(dst, Constant::Text(value.clone()));
            }
            _ => {
                if let Some(dst) = destination(&instruction) {
                    constants.remove(&dst);
                }
            }
        }
        output.push(instruction);
    }
    (output, constants, folds)
}

fn invalidates_alias_visible_constants(instruction: &MirInstruction) -> bool {
    matches!(
        instruction,
        MirInstruction::CompleteHandler { .. }
        | MirInstruction::MemoryIntrinsic { .. }
        | MirInstruction::Store { .. }
        | MirInstruction::DerefStore { .. }
        | MirInstruction::TakeArrayElement { .. }
        | MirInstruction::ArrayPushMove { .. }
        | MirInstruction::CallOwned { .. }
        | MirInstruction::CallIndirectOwned { .. }
        | MirInstruction::HostCallOwned { .. }
        | MirInstruction::Call { .. }
        | MirInstruction::CallIndirect { .. }
        | MirInstruction::HostCall { .. }
        | MirInstruction::Perform { .. }
        | MirInstruction::Resume { .. }
        | MirInstruction::ResumeReturn { .. }
        | MirInstruction::ResumeSnapshot { .. }
    )
}

fn constant_instruction(dst: MirLocal, value: Option<&Constant>) -> Option<MirInstruction> {
    match value {
        Some(Constant::I64(value)) => Some(MirInstruction::ConstI64 { dst, value: *value }),
        Some(Constant::F32(bits)) => Some(MirInstruction::ConstF32 { dst, bits: *bits }),
        Some(Constant::F64(bits)) => Some(MirInstruction::ConstF64 { dst, bits: *bits }),
        Some(Constant::Bool(value)) => Some(MirInstruction::ConstBool { dst, value: *value }),
        Some(Constant::Char(value)) => Some(MirInstruction::ConstChar { dst, value: *value }),
        Some(Constant::Text(value)) => Some(MirInstruction::ConstText {
            dst,
            value: value.clone(),
        }),
        None => None,
    }
}
/// Fold structural decisions only when their result is independent of runtime
/// aggregate identity. Literal matching shares MIR's literal decoders with
/// lowering, so escaped text and character spellings retain exact VM
/// comparison semantics. Enum patterns remain refutable even when all of
/// their fields are wildcards because the variant tag is observable. Record
/// field bounds are intentionally opaque in MIR, so only an empty record
/// pattern is independently proven irrefutable.
fn fold_pattern_test(
    dst: MirLocal,
    subject: Option<&Constant>,
    pattern: &MirPattern,
) -> Option<MirInstruction> {
    let value = if pattern_is_mir_irrefutable(pattern) {
        true
    } else {
        literal_pattern_matches_constant(subject?, pattern)?
    };
    Some(MirInstruction::ConstBool { dst, value })
}

fn pattern_is_mir_irrefutable(pattern: &MirPattern) -> bool {
    match pattern {
        MirPattern::Any => true,
        MirPattern::Literal(_) | MirPattern::Enum { .. } => false,
        MirPattern::Tuple(fields) => fields.iter().all(pattern_is_mir_irrefutable),
        MirPattern::Array { .. } => false,
        MirPattern::Record { fields, .. } => fields.is_empty(),
    }
}

fn literal_pattern_matches_constant(value: &Constant, pattern: &MirPattern) -> Option<bool> {
    let MirPattern::Literal(pattern) = pattern else {
        return None;
    };
    Some(match value {
        Constant::I64(value) => parse_i64_literal(pattern).is_ok_and(|pattern| pattern == *value),
        Constant::F32(bits) => {
            parse_f32_literal(pattern).is_ok_and(|pattern| canonical_f32_bits(pattern.to_bits()) == canonical_f32_bits(*bits))
        }
        // Structural scalar equality preserves signed zero and uses the
        // same canonical-bit policy at optimized and interpreted boundaries.
        Constant::F64(bits) => {
            parse_f64_literal(pattern).is_ok_and(|pattern| canonical_f64_bits(pattern.to_bits()) == canonical_f64_bits(*bits))
        }
        Constant::Bool(value) => {
            matches!((pattern.as_str(), value), ("true", true) | ("false", false))
        }
        Constant::Char(value) => parse_char_literal(pattern).is_ok_and(|pattern| pattern == *value),
        Constant::Text(value) => parse_text_literal(pattern).is_ok_and(|pattern| pattern == *value),
    })
}
/// Integer and boolean comparisons are reflexive at every initialized MIR
/// value.  Floats deliberately do not use this rule because `NaN != NaN`.
fn fold_reflexive_predicate(
    dst: MirLocal,
    left: MirLocal,
    right: MirLocal,
    value: bool,
) -> Option<MirInstruction> {
    (left == right).then_some(MirInstruction::ConstBool { dst, value })
}
fn fold_i64(
    dst: MirLocal,
    constants: &BTreeMap<MirLocal, Constant>,
    left: MirLocal,
    right: MirLocal,
    operation: impl FnOnce(i64, i64) -> Option<i64>,
) -> Option<MirInstruction> {
    let (Some(Constant::I64(left)), Some(Constant::I64(right))) =
        (constants.get(&left), constants.get(&right))
    else {
        return None;
    };
    operation(*left, *right).map(|value| MirInstruction::ConstI64 { dst, value })
}
fn fold_i64_predicate(
    dst: MirLocal,
    constants: &BTreeMap<MirLocal, Constant>,
    left: MirLocal,
    right: MirLocal,
    predicate: impl FnOnce(i64, i64) -> bool,
) -> Option<MirInstruction> {
    let (Some(Constant::I64(left)), Some(Constant::I64(right))) =
        (constants.get(&left), constants.get(&right))
    else {
        return None;
    };
    Some(MirInstruction::ConstBool {
        dst,
        value: predicate(*left, *right),
    })
}
fn fold_bool_predicate(
    dst: MirLocal,
    constants: &BTreeMap<MirLocal, Constant>,
    left: MirLocal,
    right: MirLocal,
    predicate: impl FnOnce(bool, bool) -> bool,
) -> Option<MirInstruction> {
    let (Some(Constant::Bool(left)), Some(Constant::Bool(right))) =
        (constants.get(&left), constants.get(&right))
    else {
        return None;
    };
    Some(MirInstruction::ConstBool {
        dst,
        value: predicate(*left, *right),
    })
}
fn destination(instruction: &MirInstruction) -> Option<MirLocal> {
    match instruction {
        MirInstruction::ConstUnit { dst }
        | MirInstruction::ConstI64 { dst, .. }
        | MirInstruction::ConstU8 { dst, .. }
        | MirInstruction::ConstU16 { dst, .. }
        | MirInstruction::ConstU32 { dst, .. }
        | MirInstruction::ConstU64 { dst, .. }
        | MirInstruction::ConstUsize { dst, .. }
        | MirInstruction::ConstU128 { dst, .. }
        | MirInstruction::ConstI8 { dst, .. }
        | MirInstruction::ConstI16 { dst, .. }
        | MirInstruction::ConstI32 { dst, .. }
        | MirInstruction::ConstIsize { dst, .. }
        | MirInstruction::ConstI128 { dst, .. }
        | MirInstruction::ConstF32 { dst, .. }
        | MirInstruction::ConstF64 { dst, .. }
        | MirInstruction::DeferredLiteral { dst, .. }
        | MirInstruction::FloatIntrinsic { dst, .. }
        | MirInstruction::MemoryIntrinsic { dst, .. }
        | MirInstruction::IntIntrinsic { dst, .. }
        | MirInstruction::IntGenericIntrinsic { dst, .. }
        | MirInstruction::ConstBool { dst, .. }
        | MirInstruction::ConstChar { dst, .. }
        | MirInstruction::ConstText { dst, .. }
        | MirInstruction::ConstStaticData { dst, .. }
        | MirInstruction::MakeTuple { dst, .. }
        | MirInstruction::MakeArray { dst, .. }
        | MirInstruction::MakeRecord { dst, .. }
        | MirInstruction::MakeEnum { dst, .. }
        | MirInstruction::ProjectRecord { dst, .. }
        | MirInstruction::TakeProjection { dst, .. }
        | MirInstruction::IsInitialized { dst, .. }
        | MirInstruction::DestroyCallable { dst, .. }
        | MirInstruction::ProjectTuple { dst, .. }
        | MirInstruction::ProjectArray { dst, .. }
        | MirInstruction::UpdateRecord { dst, .. }
        | MirInstruction::PatternTest { dst, .. }
        | MirInstruction::Perform { dst, .. }
        | MirInstruction::Copy { dst, .. }
        | MirInstruction::Store { dst, .. }
        | MirInstruction::Move { dst, .. }
        | MirInstruction::Borrow { dst, .. }
        | MirInstruction::DerefCopy { dst, .. }
        | MirInstruction::DerefIsInitialized { dst, .. }
        | MirInstruction::DerefMove { dst, .. }
        | MirInstruction::NotBool { dst, .. }
        | MirInstruction::AddI64 { dst, .. }
        | MirInstruction::WrappingAddI64 { dst, .. }
        | MirInstruction::WrappingSubI64 { dst, .. }
        | MirInstruction::WrappingMulI64 { dst, .. }
        | MirInstruction::IntEqualI64 { dst, .. }
        | MirInstruction::IntLessI64 { dst, .. }
        | MirInstruction::IntGreaterI64 { dst, .. }
        | MirInstruction::BitAndI64 { dst, .. }
        | MirInstruction::BitAndU32 { dst, .. }
        | MirInstruction::BitAndU64 { dst, .. }
        | MirInstruction::BitAndGeneric { dst, .. }
        | MirInstruction::BitXorI64 { dst, .. }
        | MirInstruction::IntShrI64 { dst, .. }
        | MirInstruction::BitOrI64 { dst, .. }
        | MirInstruction::BitNotI64 { dst, .. }
        | MirInstruction::ShlI64 { dst, .. }
        | MirInstruction::SubI64 { dst, .. }
        | MirInstruction::MulI64 { dst, .. }
        | MirInstruction::DivI64 { dst, .. }
        | MirInstruction::RemI64 { dst, .. }
        | MirInstruction::AddF64 { dst, .. }
        | MirInstruction::ConcatText { dst, .. }
        | MirInstruction::SubF64 { dst, .. }
        | MirInstruction::MulF64 { dst, .. }
        | MirInstruction::DivF64 { dst, .. }
        | MirInstruction::RemF64 { dst, .. }
        | MirInstruction::EqI64 { dst, .. }
        | MirInstruction::NeI64 { dst, .. }
        | MirInstruction::NeU32 { dst, .. }
        | MirInstruction::NeU64 { dst, .. }
        | MirInstruction::LtI64 { dst, .. }
        | MirInstruction::LeI64 { dst, .. }
        | MirInstruction::GtI64 { dst, .. }
        | MirInstruction::GeI64 { dst, .. }
        | MirInstruction::EqF64 { dst, .. }
        | MirInstruction::NeF64 { dst, .. }
        | MirInstruction::LtF64 { dst, .. }
        | MirInstruction::LeF64 { dst, .. }
        | MirInstruction::GtF64 { dst, .. }
        | MirInstruction::GeF64 { dst, .. }
        | MirInstruction::EqBool { dst, .. }
        | MirInstruction::NeBool { dst, .. }
        | MirInstruction::EqText { dst, .. }
        | MirInstruction::NeText { dst, .. }
        | MirInstruction::EqChar { dst, .. }
        | MirInstruction::NeChar { dst, .. }
        | MirInstruction::LtChar { dst, .. }
        | MirInstruction::LeChar { dst, .. }
        | MirInstruction::GtChar { dst, .. }
        | MirInstruction::GeChar { dst, .. }
        | MirInstruction::CallOwned { dst, .. }
        | MirInstruction::CallIndirectOwned { dst, .. }
        | MirInstruction::HostCallOwned { dst, .. }
        | MirInstruction::Call { dst, .. }
        | MirInstruction::HostCall { dst, .. }
        | MirInstruction::TextByteLen { dst, .. }
        | MirInstruction::TextConcat { dst, .. }
        | MirInstruction::TextEq { dst, .. }
        | MirInstruction::TextFromUtf8Checked { dst, .. }
        | MirInstruction::TextAsBytes { dst, .. }
        | MirInstruction::StaticLen { dst, .. }
        | MirInstruction::CharFromU32Checked { dst, .. }
        | MirInstruction::CharToU32 { dst, .. }
        | MirInstruction::BytesLen { dst, .. }
        | MirInstruction::BytesConcat { dst, .. }
        | MirInstruction::BytesGet { dst, .. }
        | MirInstruction::BytesSlice { dst, .. }
        | MirInstruction::BytesFromArrayMove { dst, .. }
        | MirInstruction::BytesToArray { dst, .. }
        | MirInstruction::BytesUtf8ValidUpTo { dst, .. }
        | MirInstruction::Blake3 { dst, .. }
        | MirInstruction::StoreUsize { dst, .. }
        | MirInstruction::ArrayLen { dst, .. }
        | MirInstruction::ArrayElementIsInitialized { dst, .. }
        | MirInstruction::TakeArrayElement { dst, .. }
        | MirInstruction::ArrayGetBorrowShared { dst, .. }
        | MirInstruction::ArrayEmpty { dst, .. }
        | MirInstruction::U32CheckedAdd { dst, .. }
        | MirInstruction::U32CheckedSub { dst, .. }
        | MirInstruction::U32CheckedMul { dst, .. }
        | MirInstruction::U32CheckedDiv { dst, .. }
        | MirInstruction::U32CheckedRem { dst, .. }
        | MirInstruction::U32WrappingAdd { dst, .. }
        | MirInstruction::U32WrappingSub { dst, .. }
        | MirInstruction::U32WrappingMul { dst, .. }
        | MirInstruction::U32WrappingShl { dst, .. }
        | MirInstruction::U32WrappingShr { dst, .. }
        | MirInstruction::U32CheckedShl { dst, .. }
        | MirInstruction::U32CheckedShr { dst, .. }
        | MirInstruction::U32Eq { dst, .. }
        | MirInstruction::U32Lt { dst, .. }
        | MirInstruction::U32Le { dst, .. }
        | MirInstruction::U32ToUsize { dst, .. }
        | MirInstruction::UsizeToU32Checked { dst, .. }
        | MirInstruction::I64ToU32Checked { dst, .. }
        | MirInstruction::I64ToU32Wrapping { dst, .. }
        | MirInstruction::I64ToUsizeChecked { dst, .. }
        | MirInstruction::I64ToUsizeWrapping { dst, .. }
        | MirInstruction::I64ToU8Checked { dst, .. }
        | MirInstruction::I64ToU8Wrapping { dst, .. }
        | MirInstruction::I64ToU16Checked { dst, .. }
        | MirInstruction::I64ToU16Wrapping { dst, .. }
        | MirInstruction::I64ToI16Checked { dst, .. }
        | MirInstruction::I64ToI16Wrapping { dst, .. }
        | MirInstruction::I64ToI32Checked { dst, .. }
        | MirInstruction::I64ToI32Wrapping { dst, .. }
        | MirInstruction::I64ToI8Checked { dst, .. }
        | MirInstruction::I64ToI8Wrapping { dst, .. }
        | MirInstruction::I64ToU64Checked { dst, .. }
        | MirInstruction::I64ToU64Wrapping { dst, .. }
        | MirInstruction::I64ToIsizeChecked { dst, .. }
        | MirInstruction::I64ToIsizeWrapping { dst, .. }
        | MirInstruction::I64ToU128Checked { dst, .. }
        | MirInstruction::I64ToU128Wrapping { dst, .. }
        | MirInstruction::I64ToI128Checked { dst, .. }
        | MirInstruction::I64ToI128Wrapping { dst, .. }
        | MirInstruction::MakeCallable { dst, .. }
        | MirInstruction::MakeLabel { dst, .. }
        | MirInstruction::CallIndirect { dst, .. }
        | MirInstruction::CaptureResumption { dst, .. }
        | MirInstruction::SetDropFlag { flag: dst, .. } => Some(*dst),
        MirInstruction::Abort
        | MirInstruction::InstallHandler { .. }
        | MirInstruction::ClaimEffectPayloads { .. }
        | MirInstruction::UninstallHandler
        | MirInstruction::Resume { .. }
        | MirInstruction::ResumeReturn { .. }
        | MirInstruction::ResumeSnapshot { .. }
        | MirInstruction::Forward { .. }
        | MirInstruction::Cancel { .. }
        | MirInstruction::DerefStore { .. }
        | MirInstruction::StorageLive { .. }
        | MirInstruction::StorageDead { .. }
        | MirInstruction::DestroyIf { .. } => None,
        MirInstruction::Drop { .. } => None,
        MirInstruction::ArrayPushMove { .. }
        | MirInstruction::CompleteHandler { .. } => None,
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirLocalDecl {
    pub ty: Type,
    pub source: CoreId,
}
/// The instantiated owned layout of one nominal identity. This is frozen with
/// MIR because `Type::Nominal` deliberately carries only identity arguments,
/// not its declaration-owned fields. Consumers recompute copyability from
/// these structural fields; there is no producer-asserted `Copy` bit to forge.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirNominalCopyDescriptor {
    pub definition: DefKey,
    /// Uninstantiated source field contract, including lifetime relationships.
    pub source_contract: crate::Digest,
    /// A one-variant enum still needs a discriminant in the native layout.
    pub is_enum: bool,
    pub arguments: Vec<GenericArgument>,
    /// A struct has one entry. An enum has one entry per variant, in its
    /// declaration order.
    pub variants: Vec<Vec<Type>>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirFunction {
    pub safety: crate::Safety,
    /// This body contains explicit unsafe implementation scopes. Admission
    /// is separate from whether calling its public contract is safe.
    pub unsafe_execution: bool,
    pub definition: DefKey,
    pub nominal_copy_descriptors: Vec<MirNominalCopyDescriptor>,
    /// Captured environment entries occupy the prefix of `parameters`.
    pub captures: u32,
    pub parameters: Vec<MirLocal>,
    pub locals: Vec<MirLocalDecl>,
    pub result: Type,
    pub control: MirControlTables,
    pub entry: MirBlockId,
    pub blocks: Vec<MirBlock>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirProgram {
    pub entry: DefKey,
    pub functions: BTreeMap<DefKey, MirFunction>,
    /// Every generated key is traceable back to its canonical substitution.
    /// Ordinary non-generic functions intentionally have no entry here.
    pub instances: BTreeMap<DefKey, MirInstance>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirInstance {
    pub key: InstanceKey,
    /// VM-callable identity derived from `key`, never merely its declaration.
    pub executable: DefKey,
}
/// Solver-selected trait-method identity retained until executable instance
/// materialization. Evidence preserves the coherent implementation selected
/// by Typed Core instead of re-running trait selection during codegen.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirTraitMethodInstance {
    pub evidence: DefKey,
    pub trait_arguments: Vec<GenericArgument>,
    pub method_arguments: Vec<GenericArgument>,
    pub deferred: Option<crate::core::DeferredTraitMethod>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirDiagnostic {
    pub code: &'static str,
    pub message: String,
}
#[derive(Clone, Debug)]
pub struct MirLowering {
    pub function: Option<MirFunction>,
    /// Anonymous callables lifted while lowering `function`.  These carry
    /// stable derived identities and must travel with their owning function
    /// into the MIR program.
    pub lifted: BTreeMap<DefKey, MirFunction>,
    pub diagnostics: Vec<MirDiagnostic>,
}

impl MirLowering {
    pub(crate) fn freeze(function: MirFunction, flow: &PlaceFlow, bindings: &BTreeMap<PlaceBindingOrigin, MirLocal>) -> MirFunction {
        function
            .with_frozen_move_paths(flow)
            .with_frozen_source_storage_bindings(flow, bindings)
            .with_frozen_control_tables()
    }
    pub fn lower(definition: DefKey, body: &TypedBody, flow: &PlaceFlow) -> Self {
        Self::lower_with_bodies_and_signatures(definition, body, flow, &BTreeMap::new(), None)
    }
    /// Lower one body with access to the immutable Core products of its
    /// package world. The map is an inspection-only interprocedural summary:
    /// direct-handler specialization may expose a callee whose entire body is
    /// one exact performance, but ordinary MIR lowering never mutates or
    /// substitutes another body's arena.
    pub fn lower_with_bodies(
        definition: DefKey,
        body: &TypedBody,
        flow: &PlaceFlow,
        bodies: &BTreeMap<DefKey, TypedBody>,
    ) -> Self {
        Self::lower_with_bodies_and_signatures(definition, body, flow, bodies, None)
    }
    /// Lower against the sealed interface that supplied Typed Core. Nominal
    /// copy descriptors are instantiated here, before MIR drops source-level
    /// declaration access.
    pub fn lower_with_bodies_and_signatures(
        definition: DefKey,
        body: &TypedBody,
        flow: &PlaceFlow,
        bodies: &BTreeMap<DefKey, TypedBody>,
        signatures: Option<&ElaboratedInterface>,
    ) -> Self {
        Self::lower_with_bodies_signatures_and_primitives(
            definition, body, flow, bodies, signatures, None,
        )
    }
    /// Lower against the sealed runtime-primitive identity table. This is a
    /// distinct authority input from source signatures: only a manifest-bound
    /// declaration key may select a VM primitive instruction.
    pub fn lower_with_bodies_signatures_and_primitives(
        definition: DefKey,
        body: &TypedBody,
        flow: &PlaceFlow,
        bodies: &BTreeMap<DefKey, TypedBody>,
        signatures: Option<&ElaboratedInterface>,
        runtime_primitives: Option<&BTreeMap<DefKey, PrimitiveRole>>,
    ) -> Self {
        // Recovered syntax and Core errors are deliberately editor-only
        // products.  Do not let an otherwise empty ownership analysis make a
        // malformed body look executable to MIR consumers.
        if body.recovered {
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: vec![MirDiagnostic {
                    code: "G6000",
                    message: "cannot lower recovered Typed Core".into(),
                }],
            };
        }
        let core_validation = body.validate();
        if let Some(diagnostic) = core_validation.first() {
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: vec![MirDiagnostic {
                    code: "G6000",
                    message: format!(
                        "cannot lower invalid Typed Core ({}): {}",
                        diagnostic.code, diagnostic.message
                    ),
                }],
            };
        }
        if let Some(crate::ElaboratedHeader::Callable(signature)) =
            signatures.and_then(|signatures| signatures.definitions.get(&definition))
            && signature.safety != body.safety
        {
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: vec![MirDiagnostic {
                    code: "G6000",
                    message: "Typed Core callable safety does not match its frozen declaration"
                        .into(),
                }],
            };
        }
        if !flow.diagnostics.is_empty() {
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: vec![MirDiagnostic {
                    code: "G6001",
                    message: "cannot lower Typed Core with invalid PlaceFlow".into(),
                }],
            };
        }
        // All executable bodies cross the ordered evaluation, control and
        // ownership boundaries. A failed contract is a diagnostic, never a
        // request to retry lowering against a different source shape.
        let lowered = (|| -> Result<_, MirDiagnostic> {
            let facts = flow.continuations_for(body).map_err(|error| MirDiagnostic {
                code: error.code, message: error.message,
            })?;
            let evaluation = crate::evaluation_mir::EvaluationMir::lower_with_continuations(definition, body, facts)
                .map_err(|error| MirDiagnostic {
                    code: "G6000", message: format!("invalid Evaluation MIR: {error:?}"),
                })?;
            let control = crate::control_mir::ControlMir::lower(&evaluation)
                .map_err(|error| MirDiagnostic {
                    code: "G6000", message: format!("invalid Control MIR: {error:?}"),
                })?;
            let closure_flows = flow.closure_flows().iter().map(|(brand, child)|
                (lifted_callable_definition(*brand), child.clone())).collect();
            let ownership = crate::ownership_mir::OwnershipMir::lower_with_closure_flows(
                control, flow, &closure_flows, signatures,
            ).map_err(|error| MirDiagnostic {
                code: "G6001", message: format!("invalid Ownership MIR: {}", error.0),
            })?;
            // A bottom body still exposes its declared callable result to
            // callers. Otherwise preserve the normalized Core result type.
            let result = if body.expression(body.root).ty == Type::Never {
                signatures.and_then(|signatures| signatures.definitions.get(&definition))
                    .and_then(|header| match header {
                        crate::ElaboratedHeader::Callable(signature)
                        | crate::ElaboratedHeader::ValueAlias { signature, .. } => Some(signature.result.clone()),
                        _ => None,
                    }).unwrap_or(Type::Never)
            } else {
                body.expression(body.root).ty.clone()
            };
            ownership.emit_legacy_values(result, 0, runtime_primitives, signatures.is_some(), signatures)
                .ok_or_else(|| MirDiagnostic {
                    code: "G6002",
                    message: format!("Ownership MIR body {definition:?} has an unsupported runtime representation"),
                })
        })();
        let _ = bodies; // Retained public API compatibility; never inspect callee Core here.
        match lowered {
            Ok((function, lifted)) => Self { function: Some(function), lifted, diagnostics: vec![] },
            Err(diagnostic) => Self { function: None, lifted: BTreeMap::new(), diagnostics: vec![diagnostic] },
        }
    }
}
impl MirFunction {
    /// Import the immutable PlaceFlow ownership graph at the MIR boundary.
    /// This consumes the exact analysis IDs and never resolves a path from a
    /// source spelling, so nested bindings with the same spelling remain
    /// distinct in the frozen artifact.
    pub fn with_frozen_move_paths(mut self, flow: &PlaceFlow) -> Self {
        let bindings = flow
            .bindings
            .iter()
            .enumerate()
            .map(|(_index, binding)| MirPlaceBindingData {
                source: binding.id,
                origin: binding.origin.clone(),
                spelling: binding.spelling.clone(),
            })
            .collect::<Vec<_>>();
        let paths = flow
            .move_paths
            .iter()
            .enumerate()
            .map(|(_index, path)| MirMovePathData {
                parent: path.parent.map(|parent| MirMovePathId(parent.0)),
                binding: MirPlaceBindingId(path.binding.0),
                field: path.field,
            })
            .collect::<Vec<_>>();
        debug_assert!(
            bindings
                .iter()
                .enumerate()
                .all(|(index, binding)| { binding.source.0 as usize == index })
        );
        debug_assert!(paths.iter().enumerate().all(|(index, path)| {
            path.parent.is_none_or(|parent| (parent.0 as usize) < index)
                && (path.binding.0 as usize) < bindings.len()
        }));
        let cleanup_paths = (|| {
            if flow.final_move_paths.len() != flow.moved_places.len() {
                return None;
            }
            let mut seen = BTreeSet::new();
            flow.final_move_paths
                .iter()
                .zip(&flow.moved_places)
                .map(|(path, fact)| {
                    if !seen.insert(*path) {
                        return None;
                    }
                    let node = flow.move_paths.get(path.0 as usize)?;
                    let binding = flow.bindings.get(node.binding.0 as usize)?;
                    if binding.id != node.binding || binding.spelling != fact.root {
                        return None;
                    }
                    let mut fields = Vec::new();
                    let mut cursor = Some(*path);
                    while let Some(current) = cursor {
                        let node = flow.move_paths.get(current.0 as usize)?;
                        if node.binding != binding.id {
                            return None;
                        }
                        if let Some(field) = node.field {
                            fields.push(field);
                        }
                        cursor = node.parent;
                    }
                    fields.reverse();
                    (fields == fact.fields).then_some(MirMovePathId(path.0))
                })
                .collect::<Option<Vec<_>>>()
        })();
        self.control.move_paths = MirMovePathTables { bindings, paths };
        for block in &mut self.blocks {
            if let MirTerminator::Leave { cleanup, .. } = &mut block.terminator {
                if cleanup.moved_places == flow.moved_places {
                    cleanup.moved_paths = cleanup_paths.clone().unwrap_or_default();
                }
            }
        }
        self
    }

    /// Import source-storage ownership boundaries from the same PlaceFlow
    /// product as move paths.  Consumers therefore obtain a typed lifetime
    /// graph rather than reconstructing lexical scope from local spellings.
    pub fn with_frozen_source_storage(mut self, flow: &PlaceFlow) -> Self {
        self = self.with_frozen_source_storage_bindings(flow, &BTreeMap::new());
        self
    }

    fn with_frozen_source_storage_bindings(mut self, flow: &PlaceFlow, bindings: &BTreeMap<PlaceBindingOrigin, MirLocal>) -> Self {
        let mut storage = MirSourceStorageTables::from_placeflow(flow);
        for (index, binding) in self.control.move_paths.bindings.iter().enumerate() {
            let local = match binding.origin {
                PlaceBindingOrigin::Parameter { index } => {
                    self.parameters.get(index as usize).copied()
                }
                PlaceBindingOrigin::Let { expression } => self
                    .locals
                    .iter()
                    .position(|local| local.source == expression)
                    .map(|index| MirLocal(index as u32)),
                PlaceBindingOrigin::Temporary { .. }
                | PlaceBindingOrigin::HandlerBinder { .. }
                | PlaceBindingOrigin::HandlerResumption { .. }
                | PlaceBindingOrigin::CompletionBinder { .. } => bindings.get(&binding.origin).copied(),
            };
            storage.binding_locals[index] = local;
        }
        // Lowered payload/completion binders map to their real owning slots.
        // Statically eliminated binders and resumptions still receive a Unit
        // lifecycle marker, so the source-storage graph remains total without
        // pretending that such a marker owns an executable payload.
        for local in &mut storage.binding_locals {
            if local.is_some() {
                continue;
            }
            let id = MirLocal(u32::try_from(self.locals.len()).expect("MIR local arena overflow"));
            self.locals.push(MirLocalDecl {
                ty: Type::Unit,
                source: CoreId(u32::MAX),
            });
            *local = Some(id);
        }
        // Every executable source owner receives one compiler-created drop
        // flag.  An ordinary source assignment is not a raw register
        // overwrite: the old owner is first conditionally disarmed, then the
        // replacement initializes the exact same storage and rearms it. This
        // makes assignment after a whole move and replacement of an
        // initialized owner explicit without asking the VM to infer lifetime
        // from a register number.
        let parameter_locals = self.parameters.iter().copied().collect::<BTreeSet<_>>();
        let mut storage_flags = BTreeMap::new();
        for local in storage.binding_locals.iter().flatten().copied() {
            storage_flags.entry(local).or_insert_with(|| {
                let flag = MirLocal(
                    u32::try_from(self.locals.len()).expect("MIR local arena overflow"),
                );
                self.locals.push(MirLocalDecl {
                    ty: Type::Scalar(crate::types::ScalarType::Bool),
                    source: CoreId(u32::MAX),
                });
                flag
            });
        }

        // Materialize the frozen lifecycle contract at the first executable
        // program point. Parameters are initialized by the call ABI; every
        // mapped non-parameter source slot begins dead and receives
        // `StorageLive` before any direct definition can make it readable.
        let lives = storage
            .binding_locals
            .iter()
            .enumerate()
            .filter_map(|(binding, local)| {
                local
                    .filter(|local| !parameter_locals.contains(local))
                    .map(|local| MirInstruction::StorageLive {
                        binding: MirPlaceBindingId(binding as u32),
                        local,
                    })
            })
            .collect::<Vec<_>>();
        let mut initial_flags = storage_flags
            .iter()
            .map(|(local, flag)| MirInstruction::SetDropFlag {
                flag: *flag,
                value: parameter_locals.contains(local),
            })
            .collect::<Vec<_>>();
        initial_flags.extend(lives);
        if !initial_flags.is_empty() {
            let entry = self.entry.0 as usize;
            if let Some(block) = self.blocks.get_mut(entry) {
                block.instructions.splice(0..0, initial_flags);
            }
        }

        for block_index in 0..self.blocks.len() {
            let instructions = std::mem::take(&mut self.blocks[block_index].instructions);
            let mut rewritten = Vec::with_capacity(instructions.len());
            // A block reached through a CFG edge may inherit an initialized
            // source owner. Start conservatively armed, then retain the
            // precise same-block transition for an immediately preceding
            // move. An unnecessary conditional destroy of an uninitialized
            // slot is a checked no-op; omitting a required destroy is not.
            let mut initialized = storage_flags.keys().copied().collect::<BTreeSet<_>>();
            for mut instruction in instructions {
                // The first definition of a lexical binding is source
                // storage too. Keep the evaluator's ordinary Copy/Move in a
                // fresh temporary and funnel the resulting value through the
                // same typed Store transition used by later assignment.
                match instruction {
                    MirInstruction::Copy { dst, src } if storage_flags.contains_key(&dst) => {
                        let temporary = MirLocal(
                            u32::try_from(self.locals.len()).expect("MIR local arena overflow"),
                        );
                        let ty = self.locals[dst.0 as usize].ty.clone();
                        self.locals.push(MirLocalDecl {
                            ty,
                            source: CoreId(u32::MAX),
                        });
                        rewritten.push(MirInstruction::Copy {
                            dst: temporary,
                            src,
                        });
                        instruction = MirInstruction::Store {
                            dst,
                            src: temporary,
                        };
                    }
                    MirInstruction::Move { dst, src } if storage_flags.contains_key(&dst) => {
                        let temporary = MirLocal(
                            u32::try_from(self.locals.len()).expect("MIR local arena overflow"),
                        );
                        let ty = self.locals[dst.0 as usize].ty.clone();
                        self.locals.push(MirLocalDecl {
                            ty,
                            source: CoreId(u32::MAX),
                        });
                        rewritten.push(MirInstruction::Move {
                            dst: temporary,
                            src,
                        });
                        instruction = MirInstruction::Store {
                            dst,
                            src: temporary,
                        };
                    }
                    _ => {}
                }
                if let MirInstruction::Store { dst, .. } = &instruction {
                    let dst = *dst;
                    if let Some(flag) = storage_flags.get(&dst) {
                        if initialized.contains(&dst) {
                            // Destroy while the flag is still armed, then
                            // disarm the old resident before publishing the
                            // replacement value.
                            rewritten.push(MirInstruction::DestroyIf {
                                local: dst,
                                flag: *flag,
                            });
                            rewritten.push(MirInstruction::SetDropFlag {
                                flag: *flag,
                                value: false,
                            });
                        }
                    }
                    rewritten.push(instruction);
                    if let Some(flag) = storage_flags.get(&dst) {
                        rewritten.push(MirInstruction::SetDropFlag {
                            flag: *flag,
                            value: true,
                        });
                    }
                    initialized.insert(dst);
                    continue;
                }

                let destination = destination(&instruction);
                let moved = match instruction {
                    MirInstruction::Move { src, .. } => Some(src),
                    _ => None,
                };
                rewritten.push(instruction);
                if let Some(destination) = destination {
                    if let Some(flag) = storage_flags.get(&destination) {
                        rewritten.push(MirInstruction::SetDropFlag {
                            flag: *flag,
                            value: true,
                        });
                        initialized.insert(destination);
                    }
                }
                if let Some(source) = moved {
                    if let Some(flag) = storage_flags.get(&source) {
                        rewritten.push(MirInstruction::SetDropFlag {
                            flag: *flag,
                            value: false,
                        });
                        initialized.remove(&source);
                    }
                }
            }
            self.blocks[block_index].instructions = rewritten;
        }
        self.elaborate_source_storage_leaves(&storage, &flow.label_storage_exits);
        self.control.source_storage = storage;
        self
    }

    /// Turn the lexical source-storage boundary recorded by PlaceFlow into
    /// the executable cleanup witness carried by every static `Leave`.
    ///
    /// This is deliberately an elaboration at the immutable PlaceFlow-to-MIR
    /// boundary: a label brand is the source authority for the scope exit,
    /// while the frozen storage table supplies the exact owners and locals.
    /// No CFG shape, local spelling, or individual source test is used to
    /// rediscover either fact.
    fn elaborate_source_storage_leaves(
        &mut self,
        storage: &MirSourceStorageTables,
        label_exits: &BTreeMap<crate::LabelBrand, (crate::SourceStorageScopeId, crate::SourceStorageScopeId)>,
    ) {
        for block in &mut self.blocks {
            let MirTerminator::Leave {
                brand,
                arguments,
                cleanup,
                ..
            } = &mut block.terminator
            else {
                continue;
            };
            // Raw MIR is intentionally not elaborated here: only a boundary
            // explicitly supplied by the source ownership analysis may gain
            // an executable cleanup witness.
            let Some(&(source, target)) = label_exits.get(brand) else {
                continue;
            };
            let source = MirSourceStorageScopeId(source.0);
            let target = MirSourceStorageScopeId(target.0);
            let Ok(exited) = storage.exited_bindings(source, target) else {
                continue;
            };
            // Crossing an empty syntactic block does not end an addressable
            // source lifetime. Preserve the existing same-scope ownership
            // facts on that `Leave` (notably a residual partial move of an
            // outer owner) instead of fabricating a storage boundary.
            if exited.is_empty() {
                continue;
            }
            cleanup.source_storage_scope = source;
            cleanup.target_storage_scope = target;
            cleanup.drop_flags = exited
                .iter()
                .enumerate()
                .map(|(index, &binding)| MirCleanupDropFlag {
                    id: MirDropFlagId(index as u32),
                    binding,
                })
                .collect();
            cleanup.protected_values = arguments.clone();
            cleanup.actions.clear();
            for (index, binding) in exited.into_iter().enumerate() {
                let flag = MirDropFlagId(index as u32);
                if cleanup
                    .active_loans
                    .iter()
                    .any(|loan| loan.binding.0 == binding.0)
                {
                    cleanup.actions.push(MirCleanupAction::EndBorrow { binding });
                }
                match storage.binding_local(binding) {
                    Some(local) if arguments.contains(&local) => cleanup
                        .actions
                        .push(MirCleanupAction::Protect { binding, local }),
                    _ => cleanup
                        .actions
                        .push(MirCleanupAction::Drop { binding, flag }),
                }
                cleanup
                    .actions
                    .push(MirCleanupAction::ClearDropFlag { flag });
                cleanup
                    .actions
                    .push(MirCleanupAction::StorageDead { binding });
            }
        }
    }

    /// Freeze the body-local control arena after lowering has finished
    /// constructing its CFG.  Allocation deliberately happens once, at the
    /// MIR artifact boundary: all instruction and terminator references are
    /// rewritten from the builder-only unassigned sentinel to dense typed
    /// identities, while VM lowering continues to select exactly the same
    /// wire instructions as before.
    pub fn with_frozen_control_tables(mut self) -> Self {
        let mut control = MirControlTables {
            leave_handler_depths: self.control.leave_handler_depths.clone(),
            move_paths: self.control.move_paths.clone(),
            tombstoned_blocks: self.control.tombstoned_blocks.clone(),
            source_storage: self.control.source_storage.clone(),
            frame_cleanup: self.control.frame_cleanup.clone(),
            cleanup_owners: self.control.cleanup_owners.clone(),
            ..MirControlTables::default()
        };
        let mut labels = BTreeMap::<crate::LabelBrand, MirLabelId>::new();

        for (block_index, block) in self.blocks.iter_mut().enumerate() {
            let block_id = MirBlockId(block_index as u32);
            for instruction in &mut block.instructions {
                match instruction {
                    MirInstruction::MakeLabel {
                        label,
                        brand,
                        target,
                        ..
                    } => {
                        let id = *labels.entry(*brand).or_insert_with(|| {
                            let id = MirLabelId(control.labels.len() as u32);
                            control.labels.push(MirLabelData {
                                brand: *brand,
                                scope: MirScopeId::ROOT,
                                destination: *target,
                                call_destination: true,
                            });
                            id
                        });
                        *label = id;
                    }
                    MirInstruction::InstallHandler {
                        site,
                        effect,
                        effect_arguments,
                        operation,
                        target,
                        resume_type,
                        continuation,
                        ..
                    } => {
                        let id = MirHandlerSiteId(control.handlers.len() as u32);
                        control.handlers.push(MirHandlerSiteData {
                            block: block_id,
                            scope: MirScopeId::ROOT,
                            effect: *effect,
                            effect_arguments: effect_arguments.clone(),
                            operation: *operation,
                            target: *target,
                            resume_type: resume_type.clone(),
                            continuation: *continuation,
                        });
                        *site = id;
                    }
                    _ => {}
                }
            }
        }

        // `Leave` may be the only executable witness of a label (a label
        // need not be materialized as a first-class value), so allocate its
        // typed identity before deriving the lexical CFG contexts.
        for block in &mut self.blocks {
            if let MirTerminator::Leave {
                label,
                brand,
                target,
                ..
            } = &mut block.terminator
            {
                let id = *labels.entry(*brand).or_insert_with(|| {
                    let id = MirLabelId(control.labels.len() as u32);
                    control.labels.push(MirLabelData {
                        brand: *brand,
                        scope: MirScopeId::ROOT,
                        destination: *target,
                        call_destination: false,
                    });
                    id
                });
                *label = id;
            }
        }

        let contexts = lexical_scope_contexts(&self.blocks, self.entry);
        let handler_bodies = control
            .handlers
            .iter()
            .enumerate()
            .map(|(index, handler)| (handler.target, MirHandlerSiteId(index as u32)))
            .collect::<BTreeMap<_, _>>();
        let mut scope_ids = BTreeMap::<Vec<MirScopeEntry>, MirScopeId>::new();
        scope_ids.insert(vec![], MirScopeId::ROOT);
        for context in contexts.values() {
            intern_lexical_scope_context(context, &mut control.scopes, &mut scope_ids);
        }
        for (block_index, block) in self.blocks.iter_mut().enumerate() {
            let block_id = MirBlockId(block_index as u32);
            let mut context = contexts.get(&block_id).cloned().unwrap_or_default();
            block.scope =
                intern_lexical_scope_context(&context, &mut control.scopes, &mut scope_ids);
            for instruction in &mut block.instructions {
                freeze_control_instruction(
                    instruction,
                    block_id,
                    &mut context,
                    &mut control,
                    &mut scope_ids,
                    handler_bodies.get(&block_id).copied(),
                );
            }
            if let MirTerminator::Leave { label, .. } = &block.terminator {
                let id = *label;
                if let Some(position) = context
                    .iter()
                    .rposition(|entry| *entry == MirScopeEntry::Label(id))
                {
                    control.labels[id.0 as usize].scope = intern_lexical_scope_context(
                        &context[..=position],
                        &mut control.scopes,
                        &mut scope_ids,
                    );
                }
            }
        }
        self.control = control;
        self.with_frozen_operation_arena()
    }

    /// Materialize the parallel operation identity arena once a raw block
    /// stream becomes a frozen MIR body.  Re-freezing an already frozen body
    /// is intentionally a no-op: IDs are semantic editor handles and must not
    /// change merely because a caller crosses another validation boundary.
    pub fn with_frozen_operation_arena(mut self) -> Self {
        if self.control.operations.entries.is_empty()
            && self
                .blocks
                .iter()
                .any(|block| !block.instructions.is_empty())
        {
            self.control.operations = MirOperationArena::frozen(&self.blocks);
        }
        self
    }

    pub fn entry_block(&self) -> &MirBlock {
        &self.blocks[self.entry.0 as usize]
    }
    pub fn validate(&self) -> Result<(), String> {
        self.validate_with_specialized_lifted_targets(&BTreeSet::new())
    }

    /// Validate a function that belongs to a whole-program product. Only
    /// `MirProgram` can admit a non-source lifted target, after deriving it
    /// from a registered concrete instance.
    pub(crate) fn validate_with_specialized_lifted_targets(
        &self,
        specialized_lifted_targets: &BTreeSet<DefKey>,
    ) -> Result<(), String> {
        if self.entry.0 as usize >= self.blocks.len() {
            return Err(format!("MIR entry block {} is absent", self.entry.0));
        }
        if self.control.tombstoned_blocks.contains(&self.entry) {
            return Err("MIR entry block is tombstoned".into());
        }
        for &block_id in &self.control.tombstoned_blocks {
            let block = self
                .blocks
                .get(block_id.0 as usize)
                .ok_or_else(|| format!("MIR tombstoned block {} is absent", block_id.0))?;
            if !block.parameters.is_empty()
                || !block.instructions.is_empty()
                || !matches!(block.terminator, MirTerminator::Unreachable)
            {
                return Err(format!(
                    "MIR tombstoned block {} remains executable",
                    block_id.0
                ));
            }
        }
        validate_nominal_copy_descriptors(&self.nominal_copy_descriptors)
            .map_err(|message| format!("nominal copy descriptors: {message}"))?;
        self.validate_move_path_tables()?;
        self.control
            .source_storage
            .validate(&self.control.move_paths)?;
        self.control
            .source_storage
            .validate_local_mapping(&self.control.move_paths, self.locals.len())?;
        if let Some(owners) = &self.control.cleanup_owners {
            let captures = self.parameters.iter().take(self.captures as usize).collect::<BTreeSet<_>>();
            let mut seen = BTreeSet::new();
            for owner in owners {
                self.local_type(*owner)?;
                if captures.contains(owner) || !seen.insert(*owner) {
                    return Err("cleanup owner inventory duplicates an owner or includes an environment capture".into());
                }
            }
        }
        let owners = crate::ownership::FrameOwnership::for_function(self);
        let mut remaining = owners.exiting(None);
        for action in &self.control.frame_cleanup {
            self.local_type(action.owner)?;
            if !remaining.any(|owner| owner == action.owner) {
                return Err("frame cleanup is not an ordered subset of its owning bindings".into());
            }
        }
        validate_mir_type(&self.result, &mut vec![])
            .map_err(|message| format!("result {:?}: {message}", self.result))?;
        for (index, local) in self.locals.iter().enumerate() {
            validate_mir_type(&local.ty, &mut vec![])
                .map_err(|message| format!("local {index} ({:?}): {message}", local.ty))?;
        }
        for (index, block) in self.blocks.iter().enumerate() {
            self.validate_scope(block.scope)?;
            for &parameter in &block.parameters {
                self.local_type(parameter)?;
            }
            for instruction in &block.instructions {
                for local in references(instruction) {
                    self.local_type(local)?;
                }
                self.validate_instruction(instruction, specialized_lifted_targets)?;
                validate_instruction_semantic_types(instruction)
                    .map_err(|message| format!("block {index} instruction {instruction:?}: {message}"))?;
            }
            self.validate_terminator(index, &block.terminator)?;
        }
        self.validate_operation_arena()?;
        self.validate_label_contracts()?;
        self.validate_control_tables()?;
        self.validate_local_storage_liveness()?;
        Ok(())
    }
    /// Validate the explicit compact-MIR storage state before any VM emission.
    /// Parameters and block parameters enter initialized; every other local
    /// starts dead and becomes readable only after a defining instruction on
    /// every reachable predecessor. This is the register representation of
    /// source `StorageLive` plus initialization, and rejects forged local
    /// reads even when no PlaceFlow sidecar was supplied.
    fn validate_local_storage_liveness(&self) -> Result<(), String> {
        // Locals and storage bindings are validated as dense body-local IDs
        // before this pass.  Bit vectors therefore encode the same must-live
        // sets as BTreeSet while making predecessor intersection, worklist
        // cloning, and membership checks linear over compact dense storage.
        let local_count = self.locals.len();
        let binding_count = self.control.source_storage.binding_locals.len();
        let mut entries = vec![None::<Vec<bool>>; self.blocks.len()];
        let mut storage_entries = vec![None::<Vec<bool>>; self.blocks.len()];
        let mut entry_live = vec![false; local_count];
        for parameter in &self.parameters {
            entry_live[parameter.0 as usize] = true;
        }
        entries[self.entry.0 as usize] = Some(entry_live);
        storage_entries[self.entry.0 as usize] = Some(vec![false; binding_count]);
        let mut binding_by_local = vec![None; local_count];
        for (binding, local) in self.control.source_storage.binding_locals.iter().enumerate() {
            if let Some(local) = local {
                binding_by_local[local.0 as usize] = Some(binding);
            }
        }
        let intersect_liveness = |current: &mut Vec<bool>, incoming: &[bool]| {
            let mut changed = false;
            for (current, incoming) in current.iter_mut().zip(incoming) {
                let next = *current && *incoming;
                changed |= *current != next;
                *current = next;
            }
            changed
        };
        let mut worklist = VecDeque::from([self.entry.0 as usize]);
        while let Some(index) = worklist.pop_front() {
            let Some(mut live) = entries[index].clone() else {
                continue;
            };
            let Some(mut storage_live) = storage_entries[index].clone() else {
                continue;
            };
            let block = &self.blocks[index];
            for parameter in &block.parameters {
                live[parameter.0 as usize] = true;
            }
            let mut unique_loans = BTreeMap::<MirLocal, MirLocal>::new();
            let mut aborts = false;
            for instruction in &block.instructions {
                let destination = destination(instruction);
                let mut inputs = references(instruction);
                // A label instruction names a destination block parameter;
                // that payload local is defined on the nonlocal target, not
                // read while the label capability is installed. Likewise
                // handler payload destinations are definitions supplied by
                // dynamic dispatch, never eager reads at installation.
                match instruction {
                    MirInstruction::MakeLabel { destination, .. } => {
                        inputs.retain(|local| local != destination);
                    }
                    MirInstruction::InstallHandler { .. } => inputs.clear(),
                    MirInstruction::StorageLive { .. } => inputs.clear(),
                    MirInstruction::StorageDead { .. } => inputs.clear(),
                    MirInstruction::SetDropFlag { flag, .. } => {
                        inputs.retain(|local| local != flag);
                    }
                    MirInstruction::DestroyIf { local, .. } => {
                        inputs.retain(|candidate| candidate != local);
                    }
                    MirInstruction::Drop { .. } | MirInstruction::IsInitialized { .. } => inputs.clear(),
                    _ => {}
                }
                for local in inputs {
                    if Some(local) != destination && !live[local.0 as usize] {
                        return Err(format!(
                            "MIR reads dead/uninitialized local {} before source-storage initialization",
                            local.0
                        ));
                    }
                }
                if let MirInstruction::Store { dst, .. } = instruction {
                    let binding = binding_by_local[dst.0 as usize];
                    // Captures are ABI parameters of a lifted callable. A
                    // unique capture is addressable through that sealed
                    // environment parameter, but it is not a new lexical
                    // source owner in the child body and therefore has no
                    // child-local StorageLive binding to manufacture.
                    let Some(binding) = binding else {
                        if self.parameters.contains(dst) {
                            continue;
                        }
                        return Err(
                            "MIR Store targets a local without frozen addressable source storage"
                                .into(),
                        );
                    };
                    // A lifted capture or invocation argument is an
                    // addressable child binding whose storage is initialized
                    // by the callable ABI. It has an exact mapping but no
                    // child-local `StorageLive`; ordinary lexical owners
                    // still require the explicit transition.
                    if !storage_live[binding] && !self.parameters.contains(dst) {
                        return Err("MIR Store targets source storage before StorageLive".into());
                    }
                    if live[dst.0 as usize] {
                        return Err(
                            "MIR Store replaces initialized source storage without prior zero-use destroy"
                                .into(),
                        );
                    }
                    if unique_loans.values().any(|borrowed| borrowed == dst) {
                        return Err(
                            "MIR replaces addressable source storage while a unique loan is live"
                                .into(),
                        );
                    }
                }
                if let MirInstruction::Borrow {
                    dst,
                    src,
                    unique: true,
                    ..
                } = instruction
                {
                    unique_loans.insert(*dst, *src);
                }
                match instruction {
                    MirInstruction::StorageLive { binding, local } => {
                        if storage_live[binding.0 as usize] {
                            return Err(format!(
                                "MIR starts source storage for binding {} more than once on one path",
                                binding.0
                            ));
                        }
                        if live[local.0 as usize] {
                            return Err(format!(
                                "MIR StorageLive local {} is already initialized",
                                local.0
                            ));
                        }
                        storage_live[binding.0 as usize] = true;
                    }
                    MirInstruction::StorageDead { binding, local } => {
                        if !std::mem::replace(&mut storage_live[binding.0 as usize], false) {
                            return Err(format!(
                                "MIR ends source storage for inactive binding {}",
                                binding.0
                            ));
                        }
                        if live[local.0 as usize] {
                            return Err(format!(
                                "MIR StorageDead local {} is still initialized",
                                local.0
                            ));
                        }
                        if unique_loans.values().any(|borrowed| borrowed == local) {
                            return Err(
                                "MIR ends addressable source storage while a unique loan is live"
                                    .into(),
                            );
                        }
                    }
                    MirInstruction::DestroyIf { local, .. } => {
                        live[local.0 as usize] = false;
                    }
                    MirInstruction::CallOwned { arguments, .. }
                    | MirInstruction::CallIndirectOwned { arguments, .. }
                    | MirInstruction::HostCallOwned { arguments, .. } => {
                        let mut outgoing = BTreeSet::new();
                        for argument in arguments {
                            if Some(*argument) == destination || !outgoing.insert(*argument) {
                                return Err("Runtime call aliases a consumed argument carrier".into());
                            }
                            live[argument.0 as usize] = false;
                            unique_loans.remove(argument);
                        }
                    }
                    MirInstruction::Move { src, .. } | MirInstruction::DestroyCallable { value: src, .. } => {
                        live[src.0 as usize] = false;
                    }
                    _ => {}
                }
                if let Some(destination) = destination {
                    live[destination.0 as usize] = true;
                }
                // `Abort` terminates the worker immediately.  The compact
                // MIR form deliberately retains the enclosing block
                // terminator for structural compatibility, but that
                // terminator and any following instructions are unreachable
                // at runtime and must not demand an initialized result of
                // the never-returning primitive.
                if matches!(instruction, MirInstruction::Abort) {
                    aborts = true;
                    break;
                }
            }
            if aborts {
                continue;
            }
            let mut check_edge = |target: MirBlockId,
                                  arguments: &[MirLocal],
                                  initialized: Option<MirLocal>|
             -> Result<(), String> {
                let mut edge_live = live.clone();
                if let Some(local) = initialized { edge_live[local.0 as usize] = true; }
                for local in arguments {
                    if !edge_live[local.0 as usize] {
                        return Err(format!(
                            "MIR edge reads dead/uninitialized local {} before source-storage initialization",
                            local.0
                        ));
                    }
                }
                let target_index = target.0 as usize;
                if target_index >= entries.len() {
                    return Err(format!("MIR edge targets absent block {}", target.0));
                }
                let changed_locals = match &mut entries[target_index] {
                    Some(current) => {
                        intersect_liveness(current, &edge_live)
                    }
                    slot => {
                        *slot = Some(edge_live.clone());
                        true
                    }
                };
                let changed_storage = match &mut storage_entries[target_index] {
                    Some(current) => {
                        intersect_liveness(current, &storage_live)
                    }
                    slot => {
                        *slot = Some(storage_live.clone());
                        true
                    }
                };
                if changed_locals || changed_storage {
                    worklist.push_back(target_index);
                }
                Ok(())
            };
            match &block.terminator {
                MirTerminator::Goto { target, arguments }
                | MirTerminator::Leave {
                    target, arguments, ..
                } => check_edge(*target, arguments, None)?,
                MirTerminator::SwitchBool {
                    condition,
                    then_target,
                    then_arguments,
                    else_target,
                    else_arguments,
                } => {
                    if !live[condition.0 as usize] {
                        return Err(format!(
                            "MIR switch reads dead/uninitialized local {} before source-storage initialization",
                            condition.0
                        ));
                    }
                    let initialized = match block.instructions.last() {
                        Some(MirInstruction::IsInitialized { dst, base, .. }) if dst == condition => Some(*base),
                        _ => None,
                    };
                    check_edge(*then_target, then_arguments, initialized)?;
                    check_edge(*else_target, else_arguments, None)?;
                }
                MirTerminator::Return { value } => {
                    if !live[value.0 as usize] {
                        return Err(format!(
                            "MIR return reads dead/uninitialized local {} before source-storage initialization",
                            value.0
                        ));
                    }
                }
                MirTerminator::Unreachable => {}
            }
        }
        Ok(())
    }
    fn validate_operation_arena(&self) -> Result<(), String> {
        // Unfrozen constructor literals remain supported for hostile-MIR unit
        // tests and the raw lowering boundary.  Any nonempty arena, however,
        // is complete and bidirectionally checked.
        if self.control.operations.entries.is_empty() {
            return Ok(());
        }
        // The arena is an identity table, so scanning it once per instruction
        // turns validation into O(instructions × operations).  Build a stable
        // reverse index first; `or_insert` intentionally retains the first
        // entry for a duplicated location, preserving the existing later
        // "live operation ... has no instruction" error for the second one.
        let mut operations_at = BTreeMap::new();
        for (operation_index, entry) in self.control.operations.entries.iter().enumerate() {
            if let Some(data) = entry {
                operations_at
                    .entry((data.block, data.instruction_index))
                    .or_insert(operation_index);
            }
        }
        let mut seen = vec![false; self.control.operations.entries.len()];
        for (block_index, block) in self.blocks.iter().enumerate() {
            let block_id = MirBlockId(block_index as u32);
            for instruction_index in 0..block.instructions.len() {
                let Some(&operation_index) = operations_at
                    .get(&(block_id, instruction_index as u32))
                else {
                    return Err(format!(
                        "MIR instruction at block {} index {} has no operation identity",
                        block_index, instruction_index
                    ));
                };
                if std::mem::replace(&mut seen[operation_index], true) {
                    return Err("MIR operation identity aliases multiple instructions".into());
                }
            }
        }
        for (index, entry) in self.control.operations.entries.iter().enumerate() {
            let Some(data) = entry else {
                continue;
            };
            if !seen[index] {
                return Err(format!("MIR live operation {index} has no instruction"));
            }
            let Some(block) = self.blocks.get(data.block.0 as usize) else {
                return Err(format!(
                    "MIR operation {index} names absent block {}",
                    data.block.0
                ));
            };
            if data.instruction_index as usize >= block.instructions.len() {
                return Err(format!(
                    "MIR operation {index} names absent instruction {} in block {}",
                    data.instruction_index, data.block.0
                ));
            }
        }
        Ok(())
    }
    fn validate_move_path_tables(&self) -> Result<(), String> {
        let tables = &self.control.move_paths;
        let mut origins = BTreeSet::new();
        for (index, binding) in tables.bindings.iter().enumerate() {
            if binding.source.0 as usize != index {
                return Err(format!(
                    "MIR move binding {index} has a non-dense PlaceFlow source identity"
                ));
            }
            if binding.spelling.is_empty() {
                return Err(format!("MIR move binding {index} has an empty spelling"));
            }
            if !origins.insert(binding.origin.clone()) {
                return Err("MIR move binding table repeats typed-core provenance".into());
            }
        }
        let mut roots = BTreeSet::new();
        let mut children = BTreeSet::new();
        for (index, path) in tables.paths.iter().enumerate() {
            if path.binding.0 as usize >= tables.bindings.len() {
                return Err(format!(
                    "MIR move path {index} references absent binding {}",
                    path.binding.0
                ));
            }
            match (path.parent, path.field) {
                (None, None) => {
                    if !roots.insert(path.binding) {
                        return Err("MIR move-path table repeats a binding root".into());
                    }
                }
                (Some(parent), Some(field)) => {
                    if parent.0 as usize >= index {
                        return Err(format!(
                            "MIR move path {index} has a non-ancestral parent {}",
                            parent.0
                        ));
                    }
                    let parent = tables.paths.get(parent.0 as usize).ok_or_else(|| {
                        format!(
                            "MIR move path {index} references absent parent {}",
                            parent.0
                        )
                    })?;
                    if parent.binding != path.binding {
                        return Err("MIR move path changes binding across a parent edge".into());
                    }
                    if !children.insert((path.parent, path.binding, field)) {
                        return Err("MIR move-path table repeats a projected child".into());
                    }
                }
                (None, Some(_)) => {
                    return Err(format!("MIR move path {index} is a root with a field"));
                }
                (Some(_), None) => {
                    return Err(format!("MIR move path {index} is a child without a field"));
                }
            }
        }
        Ok(())
    }
    fn validate_scope(&self, scope: MirScopeId) -> Result<(), String> {
        if scope.0 as usize >= self.control.scopes.len() {
            return Err(format!("MIR block references absent scope {}", scope.0));
        }
        Ok(())
    }
    fn validate_control_tables(&self) -> Result<(), String> {
        let Some(root) = self.control.scopes.first() else {
            return Err("MIR control table has no root scope".into());
        };
        if root.parent.is_some() {
            return Err("MIR root scope has a parent".into());
        }
        for (index, scope) in self.control.scopes.iter().enumerate().skip(1) {
            let Some(parent) = scope.parent else {
                return Err(format!("MIR non-root scope {index} has no parent"));
            };
            if parent.0 as usize >= index {
                return Err(format!("MIR scope {index} has a non-ancestral parent"));
            }
            if let Some(label) = scope.entered_label {
                self.control
                    .labels
                    .get(label.0 as usize)
                    .ok_or_else(|| format!("MIR scope {index} enters absent label {}", label.0))?;
            }
            if let Some(handler) = scope.entered_handler {
                self.control
                    .handlers
                    .get(handler.0 as usize)
                    .ok_or_else(|| {
                        format!("MIR scope {index} enters absent handler {}", handler.0)
                    })?;
            }
        }
        for (index, perform) in self.control.performs.iter().enumerate() {
            let mut seen = BTreeSet::new();
            for candidate in &perform.handler_candidates {
                if !seen.insert(*candidate) {
                    return Err(format!(
                        "MIR perform site {index} has non-canonical handler candidates"
                    ));
                }
                // IDs follow block allocation, not lexical nesting. The
                // instruction check below verifies exact innermost-first
                // scope order independently of those incidental numbers.
                let handler = self
                    .control
                    .handlers
                    .get(candidate.0 as usize)
                    .ok_or_else(|| {
                        format!(
                            "MIR perform site {index} references absent handler candidate {}",
                            candidate.0
                        )
                    })?;
                if handler.effect != perform.effect
                    || handler.effect_arguments != perform.effect_arguments
                    || handler.operation != perform.operation
                {
                    return Err(format!(
                        "MIR perform site {index} has an incompatible handler candidate {}",
                        candidate.0
                    ));
                }
            }
        }
        for (index, label) in self.control.labels.iter().enumerate() {
            if self.control.tombstoned_blocks.contains(&label.destination) {
                return Err(format!("MIR label {index} targets a tombstoned block"));
            }
        }
        for (index, handler) in self.control.handlers.iter().enumerate() {
            if self.control.tombstoned_blocks.contains(&handler.block)
                || self.control.tombstoned_blocks.contains(&handler.target)
            {
                return Err(format!("MIR handler {index} targets a tombstoned block"));
            }
        }
        for (index, perform) in self.control.performs.iter().enumerate() {
            if self.control.tombstoned_blocks.contains(&perform.block) {
                return Err(format!("MIR perform {index} is in a tombstoned block"));
            }
        }
        for (index, resumption) in self.control.resumptions.iter().enumerate() {
            if self.control.tombstoned_blocks.contains(&resumption.block) {
                return Err(format!("MIR resumption {index} is in a tombstoned block"));
            }
        }
        for (&block, _) in &self.control.leave_handler_depths {
            if self.control.tombstoned_blocks.contains(&block) {
                return Err(format!(
                    "MIR leave-handler depth names tombstoned block {}",
                    block.0
                ));
            }
            let block_data = self.blocks.get(block.0 as usize).ok_or_else(|| {
                format!("MIR leave-handler depth names absent block {}", block.0)
            })?;
            if !matches!(block_data.terminator, MirTerminator::Leave { .. }) {
                return Err(format!(
                    "MIR leave-handler depth names block {} without a leave terminator",
                    block.0
                ));
            }
        }
        for (index, resumption) in self.control.resumptions.iter().enumerate() {
            let Some(handler) = resumption.originating_handler else {
                continue;
            };
            let handler = self
                .control
                .handlers
                .get(handler.0 as usize)
                .ok_or_else(|| {
                    format!(
                        "MIR resumption site {index} references absent originating handler {}",
                        handler.0
                    )
                })?;
            if handler.target != resumption.block {
                return Err(format!(
                    "MIR resumption site {index} is outside its originating handler body"
                ));
            }
        }
        let mut seen_labels = vec![false; self.control.labels.len()];
        let mut seen_handlers = vec![false; self.control.handlers.len()];
        let mut seen_performs = vec![false; self.control.performs.len()];
        let mut seen_resumptions = vec![false; self.control.resumptions.len()];
        for (block_index, block) in self.blocks.iter().enumerate() {
            let block_id = MirBlockId(block_index as u32);
            let mut scope = block.scope;
            for instruction in &block.instructions {
                match instruction {
                    MirInstruction::MakeLabel {
                        label,
                        brand,
                        target,
                        ..
                    } => {
                        let entry = self.control.labels.get(label.0 as usize).ok_or_else(|| {
                            format!("MIR label instruction references absent label {}", label.0)
                        })?;
                        if entry.brand != *brand
                            || entry.destination != *target
                            || !scope_enters_label(&self.control, entry.scope, scope, *label)
                        {
                            return Err(
                                "MIR label instruction disagrees with frozen control table".into(),
                            );
                        }
                        if std::mem::replace(&mut seen_labels[label.0 as usize], true)
                            && !entry.call_destination
                        {
                            return Err("MIR non-call label has multiple materializations".into());
                        }
                        scope = entry.scope;
                    }
                    MirInstruction::InstallHandler {
                        site,
                        effect,
                        effect_arguments,
                        operation,
                        target,
                        resume_type,
                        continuation,
                        ..
                    } => {
                        let entry =
                            self.control.handlers.get(site.0 as usize).ok_or_else(|| {
                                format!(
                                    "MIR handler instruction references absent handler {}",
                                    site.0
                                )
                            })?;
                        if entry.block != block_id
                            || !scope_enters_handler(&self.control, entry.scope, scope, *site)
                            || entry.effect != *effect
                            || entry.effect_arguments != *effect_arguments
                            || entry.operation != *operation
                            || entry.target != *target
                            || entry.resume_type != *resume_type
                            || entry.continuation != *continuation
                        {
                            return Err(
                                "MIR handler instruction disagrees with frozen control table"
                                    .into(),
                            );
                        }
                        if std::mem::replace(&mut seen_handlers[site.0 as usize], true) {
                            return Err("MIR handler site is wired more than once".into());
                        }
                        scope = entry.scope;
                    }
                    MirInstruction::Perform {
                        site,
                        effect,
                        effect_arguments,
                        operation,
                        ..
                    } => {
                        let entry =
                            self.control.performs.get(site.0 as usize).ok_or_else(|| {
                                format!(
                                    "MIR perform instruction references absent perform {}",
                                    site.0
                                )
                            })?;
                        if entry.block != block_id
                            || entry.scope != scope
                            || entry.effect != *effect
                            || entry.effect_arguments != *effect_arguments
                            || entry.operation != *operation
                        {
                            return Err(
                                "MIR perform instruction disagrees with frozen control table"
                                    .into(),
                            );
                        }
                        if entry.handler_candidates
                            != lexical_handler_candidates(
                                &self.control,
                                scope,
                                *effect,
                                effect_arguments,
                                *operation,
                            )
                        {
                            return Err(
                                "MIR perform site disagrees with lexical handler candidates".into(),
                            );
                        }
                        if std::mem::replace(&mut seen_performs[site.0 as usize], true) {
                            return Err("MIR perform site is wired more than once".into());
                        }
                    }
                    MirInstruction::UninstallHandler => {
                        scope = scope_after_uninstall(&self.control, scope).ok_or_else(|| {
                            "MIR uninstall handler escapes the lexical scope tree".to_owned()
                        })?;
                    }
                    instruction @ (MirInstruction::CaptureResumption { site, .. }
                    | MirInstruction::Resume { site, .. }
                    | MirInstruction::ResumeReturn { site, .. }
                    | MirInstruction::ResumeSnapshot { site, .. }
                    | MirInstruction::Forward { site }
                    | MirInstruction::Cancel { site }) => {
                        let entry =
                            self.control
                                .resumptions
                                .get(site.0 as usize)
                                .ok_or_else(|| {
                                    format!(
                                        "MIR resumption instruction references absent site {}",
                                        site.0
                                    )
                                })?;
                        let kind = match instruction {
                            MirInstruction::CaptureResumption { .. } => {
                                MirResumptionSiteKind::Capture
                            }
                            MirInstruction::Resume { .. } => MirResumptionSiteKind::Resume,
                            MirInstruction::ResumeReturn { .. } => {
                                MirResumptionSiteKind::ResumeReturn
                            }
                            MirInstruction::ResumeSnapshot { .. } => {
                                MirResumptionSiteKind::ResumeSnapshot
                            }
                            MirInstruction::Forward { .. } => MirResumptionSiteKind::Forward,
                            MirInstruction::Cancel { .. } => MirResumptionSiteKind::Cancel,
                            _ => unreachable!("resumption match is exhaustive"),
                        };
                        if entry.block != block_id || entry.scope != scope || entry.kind != kind {
                            return Err(
                                "MIR resumption instruction disagrees with frozen control table"
                                    .into(),
                            );
                        }
                        if std::mem::replace(&mut seen_resumptions[site.0 as usize], true) {
                            return Err("MIR resumption site is wired more than once".into());
                        }
                    }
                    _ => {}
                }
            }
            if let MirTerminator::Leave {
                label,
                brand,
                target,
                ..
            } = &block.terminator
            {
                let entry = self
                    .control
                    .labels
                    .get(label.0 as usize)
                    .ok_or_else(|| format!("MIR leave references absent label {}", label.0))?;
                if entry.brand != *brand
                    || entry.destination != *target
                    || !scope_is_ancestor(&self.control, entry.scope, scope)
                {
                    return Err("MIR leave disagrees with frozen control table".into());
                }
                seen_labels[label.0 as usize] = true;
            }
        }
        if seen_labels.iter().any(|seen| !seen)
            || seen_handlers.iter().any(|seen| !seen)
            || seen_performs.iter().any(|seen| !seen)
            || seen_resumptions.iter().any(|seen| !seen)
        {
            return Err("MIR control table contains an unwired site".into());
        }
        Ok(())
    }
    /// A nominal label brand is proof of exactly one lexical destination.
    /// Several source paths may leave the same label, but they must all enter
    /// the same block through that block's one typed parameter layout.  Keep
    /// this check at the frozen MIR boundary as well as the VM boundary: a
    /// hand-built MIR graph must not be able to reuse one brand as a general
    /// purpose nonlocal jump capability.
    fn validate_label_contracts(&self) -> Result<(), String> {
        let mut contracts =
            BTreeMap::<crate::LabelBrand, (MirBlockId, Vec<MirLocal>, Vec<Type>)>::new();
        for block in &self.blocks {
            let MirTerminator::Leave { brand, target, .. } = &block.terminator else {
                continue;
            };
            let destination = self
                .blocks
                .get(target.0 as usize)
                .ok_or_else(|| format!("MIR label target block {} is absent", target.0))?;
            let destinations = destination.parameters.clone();
            let layout = destinations
                .iter()
                .map(|local| self.local_type(*local).cloned())
                .collect::<Result<Vec<_>, _>>()?;
            let contract = (*target, destinations, layout);
            match contracts.get(brand) {
                Some(previous) if previous != &contract => {
                    return Err(
                        "MIR label brand has contradictory destination or payload layout".into(),
                    );
                }
                Some(_) => {}
                None => {
                    contracts.insert(*brand, contract);
                }
            }
        }
        Ok(())
    }
    fn local_type(&self, local: MirLocal) -> Result<&Type, String> {
        self.locals
            .get(local.0 as usize)
            .map(|local| &local.ty)
            .ok_or_else(|| format!("MIR references invalid local {}", local.0))
    }
    fn require_scalar_locals(
        &self,
        locals: &[MirLocal],
        scalar: crate::types::ScalarType,
        instruction: &str,
    ) -> Result<(), String> {
        let expected = Type::Scalar(scalar);
        for local in locals {
            if self.local_type(*local)? != &expected {
                return Err(format!("MIR {instruction} has an inconsistent scalar operand type"));
            }
        }
        Ok(())
    }
    fn validate_fixed_scalar_instruction(&self, instruction: &MirInstruction) -> Result<bool, String> {
        use crate::types::ScalarType;
        match instruction {
            MirInstruction::ConstI64 { dst, .. } => {
                self.require_scalar_locals(&[*dst], ScalarType::I64, "i64 constant")?;
            }
            MirInstruction::ConstBool { dst, .. } => {
                self.require_scalar_locals(&[*dst], ScalarType::Bool, "Bool constant")?;
            }
            MirInstruction::AddI64 { dst, left, right }
            | MirInstruction::WrappingAddI64 { dst, left, right }
            | MirInstruction::WrappingSubI64 { dst, left, right }
            | MirInstruction::WrappingMulI64 { dst, left, right }
            | MirInstruction::BitAndI64 { dst, left, right }
            | MirInstruction::BitXorI64 { dst, left, right }
            | MirInstruction::BitOrI64 { dst, left, right }
            | MirInstruction::SubI64 { dst, left, right }
            | MirInstruction::MulI64 { dst, left, right }
            | MirInstruction::DivI64 { dst, left, right }
            | MirInstruction::RemI64 { dst, left, right } => {
                self.require_scalar_locals(&[*dst, *left, *right], ScalarType::I64, "i64 operation")?;
            }
            MirInstruction::NotBool { dst, value } => {
                self.require_scalar_locals(&[*dst, *value], ScalarType::Bool, "Bool operation")?;
            }
            MirInstruction::EqBool { dst, left, right }
            | MirInstruction::NeBool { dst, left, right } => {
                self.require_scalar_locals(&[*dst, *left, *right], ScalarType::Bool, "Bool comparison")?;
            }
            MirInstruction::AddF64 { dst, left, right }
            | MirInstruction::SubF64 { dst, left, right }
            | MirInstruction::MulF64 { dst, left, right }
            | MirInstruction::DivF64 { dst, left, right }
            | MirInstruction::RemF64 { dst, left, right } => {
                self.require_scalar_locals(&[*dst, *left, *right], ScalarType::F64, "f64 operation")?;
            }
            MirInstruction::EqI64 { dst, left, right }
            | MirInstruction::NeI64 { dst, left, right }
            | MirInstruction::LtI64 { dst, left, right }
            | MirInstruction::LeI64 { dst, left, right }
            | MirInstruction::GtI64 { dst, left, right }
            | MirInstruction::GeI64 { dst, left, right } => {
                self.require_scalar_locals(&[*dst], ScalarType::Bool, "i64 comparison result")?;
                self.require_scalar_locals(&[*left, *right], ScalarType::I64, "i64 comparison")?;
            }
            MirInstruction::EqF64 { dst, left, right }
            | MirInstruction::NeF64 { dst, left, right }
            | MirInstruction::LtF64 { dst, left, right }
            | MirInstruction::LeF64 { dst, left, right }
            | MirInstruction::GtF64 { dst, left, right }
            | MirInstruction::GeF64 { dst, left, right } => {
                self.require_scalar_locals(&[*dst], ScalarType::Bool, "f64 comparison result")?;
                self.require_scalar_locals(&[*left, *right], ScalarType::F64, "f64 comparison")?;
            }
            MirInstruction::ConstU32 { dst, .. } => {
                self.require_scalar_locals(&[*dst], ScalarType::U32, "u32 constant")?;
            }
            MirInstruction::ConstUsize { dst, .. } => {
                self.require_scalar_locals(&[*dst], ScalarType::Usize, "usize constant")?;
            }
            MirInstruction::U32CheckedAdd { dst, left, right }
            | MirInstruction::U32CheckedSub { dst, left, right }
            | MirInstruction::U32CheckedMul { dst, left, right }
            | MirInstruction::U32CheckedDiv { dst, left, right }
            | MirInstruction::U32CheckedRem { dst, left, right }
            | MirInstruction::U32WrappingAdd { dst, left, right }
            | MirInstruction::U32WrappingSub { dst, left, right }
            | MirInstruction::U32WrappingMul { dst, left, right }
            | MirInstruction::U32WrappingShl { dst, left, right }
            | MirInstruction::U32WrappingShr { dst, left, right }
            | MirInstruction::U32CheckedShl { dst, left, right }
            | MirInstruction::U32CheckedShr { dst, left, right }
            | MirInstruction::BitAndU32 { dst, left, right } => {
                self.require_scalar_locals(&[*dst, *left, *right], ScalarType::U32, "u32 operation")?;
            }
            MirInstruction::U32Eq { dst, left, right }
            | MirInstruction::U32Lt { dst, left, right }
            | MirInstruction::U32Le { dst, left, right }
            | MirInstruction::NeU32 { dst, left, right } => {
                self.require_scalar_locals(&[*dst], ScalarType::Bool, "u32 comparison result")?;
                self.require_scalar_locals(&[*left, *right], ScalarType::U32, "u32 comparison")?;
            }
            MirInstruction::U32ToUsize { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Usize, "u32-to-usize result")?;
                self.require_scalar_locals(&[*value], ScalarType::U32, "u32-to-usize input")?;
            }
            MirInstruction::UsizeToU32Checked { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::U32, "usize-to-u32 result")?;
                self.require_scalar_locals(&[*value], ScalarType::Usize, "usize-to-u32 input")?;
            }
            MirInstruction::I64ToU32Checked { dst, value }
            | MirInstruction::I64ToU32Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::U32, "i64-to-u32 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-u32 input")?;
            }
            MirInstruction::I64ToUsizeChecked { dst, value }
            | MirInstruction::I64ToUsizeWrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Usize, "i64-to-usize result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-usize input")?;
            }
            MirInstruction::I64ToU8Checked { dst, value }
            | MirInstruction::I64ToU8Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::U8, "i64-to-u8 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-u8 input")?;
            }
            MirInstruction::I64ToU16Checked { dst, value }
            | MirInstruction::I64ToU16Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::U16, "i64-to-u16 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-u16 input")?;
            }
            MirInstruction::I64ToI16Checked { dst, value }
            | MirInstruction::I64ToI16Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::I16, "i64-to-i16 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-i16 input")?;
            }
            MirInstruction::I64ToI32Checked { dst, value }
            | MirInstruction::I64ToI32Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::I32, "i64-to-i32 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-i32 input")?;
            }
            MirInstruction::I64ToI8Checked { dst, value }
            | MirInstruction::I64ToI8Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::I8, "i64-to-i8 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-i8 input")?;
            }
            MirInstruction::I64ToU64Checked { dst, value }
            | MirInstruction::I64ToU64Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::U64, "i64-to-u64 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-u64 input")?;
            }
            MirInstruction::I64ToIsizeChecked { dst, value }
            | MirInstruction::I64ToIsizeWrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Isize, "i64-to-isize result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-isize input")?;
            }
            MirInstruction::I64ToU128Checked { dst, value }
            | MirInstruction::I64ToU128Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::U128, "i64-to-u128 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-u128 input")?;
            }
            MirInstruction::I64ToI128Checked { dst, value }
            | MirInstruction::I64ToI128Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::I128, "i64-to-i128 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-i128 input")?;
            }
            MirInstruction::DestroyCallable { dst, value } => {
                if self.locals[dst.0 as usize].ty != Type::Unit
                    || !matches!(self.locals[value.0 as usize].ty, Type::Callable { .. })
                {
                    return Err("MIR callable destruction requires a callable and unit result".into());
                }
            }
            MirInstruction::MemoryIntrinsic { dst, primitive, types, arguments } => {
                let Some(mut signature) = primitive.instantiated_signature(types) else {
                    return Err("MIR memory primitive has the wrong type arity".into());
                };
                if signature.safety == crate::Safety::Unsafe && !self.unsafe_execution {
                    return Err("MIR memory primitive requires an unsafe implementation scope".into());
                }
                // Creating a checked reference from raw storage explicitly
                // delegates lifetime validity to the unsafe caller. Retain
                // the selected source lifetime, while still checking the
                // concrete pointee and shared/unique contract exactly.
                if primitive.constructs_reference() {
                    if let (Type::Reference { lifetime: expected, .. }, Type::Reference { lifetime, .. }) =
                        (&mut signature.result, &self.locals[dst.0 as usize].ty) {
                        *expected = *lifetime;
                    }
                }
                if matches!(primitive, crate::MemoryPrimitive::AsRawShared | crate::MemoryPrimitive::AsRawUnique)
                    && let ([parameter], [argument]) = (signature.parameters.as_mut_slice(), arguments.as_slice())
                    && let (Type::Reference { lifetime: expected, .. }, Type::Reference { lifetime, .. }) =
                        (parameter, &self.locals[argument.0 as usize].ty)
                {
                    // Address extraction does not rebind or extend this loan.
                    // Its exact permission/referent remain checked below.
                    *expected = *lifetime;
                }
                if arguments.len() != signature.parameters.len()
                    || self.locals[dst.0 as usize].ty != signature.result
                    || arguments.iter().zip(&signature.parameters)
                        .any(|(argument, expected)| &self.locals[argument.0 as usize].ty != expected)
                {
                    return Err("MIR memory primitive ABI does not match its contract".into());
                }
            }
            MirInstruction::FloatIntrinsic {
                dst,
                primitive,
                arguments,
            } => {
                let (parameters, result) = primitive.scalar_signature();
                if arguments.len() != parameters.len() {
                    return Err("MIR floating runtime primitive has the wrong arity".into());
                }
                self.require_scalar_locals(
                    &[*dst],
                    result,
                    "floating runtime primitive result",
                )?;
                for (argument, parameter) in arguments.iter().zip(parameters) {
                    self.require_scalar_locals(
                        &[*argument],
                        parameter,
                        "floating runtime primitive operand",
                    )?;
                }
            }
            MirInstruction::IntIntrinsic {
                dst,
                primitive,
                scalar,
                arguments,
            } => {
                let Some((parameters, result)) = primitive.integer_scalar_signature(*scalar) else {
                    return Err("MIR integer runtime primitive has an invalid ABI".into());
                };
                if arguments.len() != parameters.len() {
                    return Err("MIR integer runtime primitive has the wrong arity".into());
                }
                self.require_scalar_locals(
                    &[*dst],
                    result,
                    "integer runtime primitive result",
                )?;
                for (argument, parameter) in arguments.iter().zip(parameters) {
                    self.require_scalar_locals(
                        &[*argument],
                        parameter,
                        "integer runtime primitive operand",
                    )?;
                }
            }
            MirInstruction::IntGenericIntrinsic {
                dst,
                primitive,
                arguments,
            } => {
                let Some((parameters, result)) = primitive.integer_scalar_signature(ScalarType::I64) else {
                    return Err("MIR generic integer primitive has an invalid ABI".into());
                };
                if arguments.len() != parameters.len() {
                    return Err("MIR generic integer primitive has the wrong arity".into());
                }
                let Some(first) = arguments.first() else {
                    return Err("MIR generic integer primitive has no scalar operand".into());
                };
                let Type::Generic(generic) = self.local_type(*first)? else {
                    return Err(
                        "MIR generic integer primitive requires a generic scalar operand".into(),
                    );
                };
                let expected_result = if result == ScalarType::I64 {
                    Type::Generic(*generic)
                } else {
                    Type::Scalar(result)
                };
                self.validate_local_type(
                    *dst,
                    &expected_result,
                    "generic integer primitive",
                    "the primitive result type",
                )?;
                for (argument, parameter) in arguments.iter().zip(parameters) {
                    let expected = if parameter == ScalarType::I64 {
                        Type::Generic(*generic)
                    } else {
                        Type::Scalar(parameter)
                    };
                    self.validate_local_type(
                        *argument,
                        &expected,
                        "generic integer primitive",
                        "the primitive operand type",
                    )?;
                }
            }
            MirInstruction::TextByteLen { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Usize, "Text byte length result")?;
                self.require_scalar_locals(&[*value], ScalarType::Text, "Text byte length input")?;
            }
            MirInstruction::StaticLen { dst, value } => {
                let data = Type::StaticData {
                    element: Box::new(Type::Scalar(ScalarType::U8)),
                    tag: 0x4752_414e_4449_4f53_455f_5354_4154_4943,
                    alignment: 1,
                };
                self.validate_local_type(*dst, &Type::Scalar(ScalarType::Usize), "static length", "the result type")?;
                self.validate_local_type(*value, &data, "static length", "the static-data input")?;
            }
            MirInstruction::TextConcat { dst, left, right } => {
                self.require_scalar_locals(&[*dst, *left, *right], ScalarType::Text, "Text concatenation")?;
            }
            MirInstruction::TextEq { dst, left, right } => {
                self.require_scalar_locals(&[*dst], ScalarType::U32, "Text equality result")?;
                self.require_scalar_locals(&[*left, *right], ScalarType::Text, "Text equality inputs")?;
            }
            MirInstruction::TextFromUtf8Checked { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Text, "UTF-8 decode result")?;
                self.require_scalar_locals(&[*value], ScalarType::Bytes, "UTF-8 decode input")?;
            }
            MirInstruction::TextAsBytes { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Bytes, "Text bytes result")?;
                self.require_scalar_locals(&[*value], ScalarType::Text, "Text bytes input")?;
            }
            MirInstruction::CharFromU32Checked { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Char, "char conversion result")?;
                self.require_scalar_locals(&[*value], ScalarType::U32, "char conversion input")?;
            }
            MirInstruction::CharToU32 { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::U32, "char code point result")?;
                self.require_scalar_locals(&[*value], ScalarType::Char, "char code point input")?;
            }
            MirInstruction::StoreUsize { dst, value } => {
                self.require_scalar_locals(&[*dst, *value], ScalarType::Usize, "runtime counter assignment")?;
                if self.parameters.contains(dst) || self.control.source_storage.binding_locals.contains(&Some(*dst)) {
                    return Err("runtime counter assignment cannot target source storage or parameters".into());
                }
            }
            MirInstruction::ArrayLen { dst, value } => {
                if self.local_type(*value)?.array_element().is_none() {
                    return Err("array length requires owned array storage".into());
                }
                self.require_scalar_locals(&[*dst], ScalarType::Usize, "array length")?;
            }
            MirInstruction::ArrayElementIsInitialized { dst, value, index }
            | MirInstruction::TakeArrayElement { dst, value, index } => {
                let Some(element) = self.local_type(*value)?.array_element() else {
                    return Err("dynamic array projection requires owned array storage".into());
                };
                self.require_scalar_locals(&[*index], ScalarType::Usize, "array index")?;
                if matches!(instruction, MirInstruction::TakeArrayElement { .. }) {
                    if dst == value || self.local_type(*dst)? != element {
                        return Err("array move result does not match element type".into());
                    }
                } else {
                    self.require_scalar_locals(&[*dst], ScalarType::Bool, "array initialization probe")?;
                }
            }
            MirInstruction::BytesLen { dst, value }
            | MirInstruction::BytesUtf8ValidUpTo { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Usize, "Bytes length result")?;
                self.require_scalar_locals(&[*value], ScalarType::Bytes, "Bytes length input")?;
            }
            MirInstruction::Blake3 { dst, value } => {
                self.require_scalar_locals(&[*dst, *value], ScalarType::Bytes, "BLAKE3")?;
            }
            MirInstruction::BytesFromArrayMove { dst, value } => {
                self.require_scalar_locals(
                    &[*dst],
                    ScalarType::Bytes,
                    "Bytes-from-array result",
                )?;
                self.validate_local_type(
                    *value,
                    &Type::Array(Box::new(Type::Scalar(ScalarType::U8))),
                    "Bytes-from-array conversion",
                    "an owned Array<u8> input",
                )?;
            }
            MirInstruction::BytesToArray { dst, value } => {
                self.validate_local_type(
                    *dst,
                    &Type::Array(Box::new(Type::Scalar(ScalarType::U8))),
                    "Bytes-to-array conversion",
                    "an Array<u8> result",
                )?;
                self.require_scalar_locals(
                    &[*value],
                    ScalarType::Bytes,
                    "Bytes-to-array input",
                )?;
            }
            MirInstruction::BytesConcat { dst, left, right } => {
                self.require_scalar_locals(&[*dst, *left, *right], ScalarType::Bytes, "Bytes concatenation")?;
            }
            MirInstruction::BytesGet { dst, bytes, index } => {
                self.require_scalar_locals(&[*dst], ScalarType::U8, "Bytes get result")?;
                self.require_scalar_locals(&[*bytes], ScalarType::Bytes, "Bytes get input")?;
                self.require_scalar_locals(&[*index], ScalarType::Usize, "Bytes get index")?;
            }
            MirInstruction::BytesSlice {
                dst,
                bytes,
                start,
                end,
            } => {
                self.require_scalar_locals(&[*dst, *bytes], ScalarType::Bytes, "Bytes slice carrier")?;
                self.require_scalar_locals(&[*start, *end], ScalarType::Usize, "Bytes slice bounds")?;
            }
            _ => return Ok(false),
        }
        Ok(true)
    }
    fn validate_reference(
        &self,
        value: MirLocal,
        mutability: Mutability,
        referent: &Type,
        instruction: &str,
        requirement: &str,
    ) -> Result<(), String> {
        match self.local_type(value)? {
            Type::Reference {
                mutability: actual_mutability,
                referent: actual_referent,
                ..
            } if (*actual_mutability == mutability
                || (mutability == Mutability::Shared && *actual_mutability == Mutability::Unique))
                && actual_referent.as_ref() == referent =>
            {
                Ok(())
            }
            actual => Err(format!(
                "MIR {instruction} requires {requirement}; expected {referent:?}, got {actual:?}"
            )),
        }
    }

    fn validate_array_view(
        &self,
        value: MirLocal,
        element_type: &Type,
        mutability: Mutability,
        instruction: &str,
        requirement: &str,
    ) -> Result<(), String> {
        self.validate_reference(
            value,
            mutability,
            &Type::Array(Box::new(element_type.clone())),
            instruction,
            requirement,
        )
    }

    fn validate_owned_array(
        &self,
        value: MirLocal,
        element_type: &Type,
        instruction: &str,
        requirement: &str,
    ) -> Result<(), String> {
        let expected = Type::Array(Box::new(element_type.clone()));
        if self.local_type(value)? == &expected {
            Ok(())
        } else {
            Err(format!("MIR {instruction} requires {requirement}"))
        }
    }

    fn validate_local_type(
        &self,
        value: MirLocal,
        expected: &Type,
        instruction: &str,
        requirement: &str,
    ) -> Result<(), String> {
        if self.local_type(value)? == expected {
            Ok(())
        } else {
            Err(format!("MIR {instruction} requires {requirement}"))
        }
    }

    fn validate_array_view_instruction(
        &self,
        instruction: &MirInstruction,
    ) -> Result<bool, String> {
        match instruction {
            MirInstruction::ArrayGetBorrowShared {
                dst,
                value,
                index,
                element_type,
            } => {
                self.validate_reference(
                    *dst,
                    Mutability::Shared,
                    element_type,
                    "array borrow get",
                    "a shared element reference result",
                )?;
                self.validate_array_view(
                    *value,
                    element_type,
                    Mutability::Shared,
                    "array borrow get",
                    "a shared Array view",
                )?;
                self.require_scalar_locals(
                    &[*index],
                    crate::types::ScalarType::Usize,
                    "array borrow get index",
                )?;
                Ok(true)
            }
            MirInstruction::ArrayEmpty { dst, element_type } => {
                self.validate_owned_array(*dst, element_type, "array empty", "an Array result")?;
                Ok(true)
            }
            MirInstruction::ArrayPushMove {
                value,
                item,
                element_type,
            } => {
                self.validate_array_view(
                    *value,
                    element_type,
                    Mutability::Unique,
                    "array push",
                    "a unique Array view",
                )?;
                self.validate_local_type(*item, element_type, "array push", "an element item")?;
                Ok(true)
            }
            _ => Ok(false),
        }
    }
    fn validate_instruction(
        &self,
        instruction: &MirInstruction,
        specialized_lifted_targets: &BTreeSet<DefKey>,
    ) -> Result<(), String> {
        if let MirInstruction::CallIndirect { callee, .. } | MirInstruction::CallIndirectOwned { callee, .. } = instruction
            && matches!(
                self.local_type(*callee)?,
                Type::Callable {
                    safety: crate::Safety::Unsafe,
                    ..
                }
            )
            && !self.unsafe_execution
        {
            return Err(
                "MIR unsafe indirect call omitted its unsafe implementation requirement".into(),
            );
        }
        match instruction {
            MirInstruction::IsInitialized { dst, base, fields }
            | MirInstruction::TakeProjection { dst, base, fields } => {
                if dst == base {
                    return Err("MIR storage projection requires a distinct destination".into());
                }
                let taking = matches!(instruction, MirInstruction::TakeProjection { .. });
                if taking && fields.is_empty() {
                    return Err("MIR projection move requires a nonempty field path".into());
                }
                let mut candidates = vec![self.local_type(*base)?.clone()];
                for index in fields {
                    let mut projected = Vec::new();
                    for ty in &candidates {
                        match ty {
                            Type::Tuple(fields) => projected.extend(fields.get(*index as usize).cloned()),
                            Type::Array(element) => projected.push((**element).clone()),
                            Type::FixedArray { element, .. } if ty.fixed_array_length().is_some_and(|n| u64::from(*index) < n) => projected.push((**element).clone()),
                            Type::Nominal { definition, arguments } => {
                                let descriptor = self.nominal_copy_descriptors.iter().find(|descriptor|
                                    descriptor.definition == *definition && descriptor.arguments == *arguments)
                                    .ok_or("MIR storage projection has no frozen nominal layout")?;
                                projected.extend(descriptor.variants.iter().filter_map(|fields|
                                    fields.get(*index as usize).cloned()));
                            }
                            _ => {}
                        }
                    }
                    if projected.is_empty() {
                        return Err("MIR storage projection is outside its frozen layout".into());
                    }
                    candidates = projected;
                }
                let destination = self.local_type(*dst)?;
                if if taking { !candidates.contains(destination) }
                    else { destination != &Type::Scalar(crate::types::ScalarType::Bool) }
                {
                    return Err("MIR storage projection destination type is inconsistent".into());
                }
                return Ok(());
            }
            MirInstruction::DerefIsInitialized { dst, reference } => {
                if self.local_type(*dst)? != &Type::Scalar(crate::types::ScalarType::Bool)
                    || !matches!(self.local_type(*reference)?, Type::Reference { mutability: Mutability::Unique, .. })
                {
                    return Err("MIR referent initialization probe requires a unique reference and Bool destination".into());
                }
                return Ok(());
            }
            MirInstruction::StorageLive { binding, local }
            | MirInstruction::StorageDead { binding, local } => {
                if self.control.source_storage.binding_local(*binding) != Some(*local) {
                    return Err(
                        "MIR storage statement does not use its frozen binding-local mapping"
                            .into(),
                    );
                }
                return Ok(());
            }
            MirInstruction::SetDropFlag { flag, .. } => {
                if self.local_type(*flag)? != &Type::Scalar(crate::types::ScalarType::Bool) {
                    return Err("MIR drop flag local is not Bool".into());
                }
                return Ok(());
            }
            MirInstruction::DestroyIf { local, flag } => {
                if self.local_type(*flag)? != &Type::Scalar(crate::types::ScalarType::Bool) {
                    return Err("MIR conditional destroy flag is not Bool".into());
                }
                // A conditional destroy is a source-storage operation, not a
                // general register-clear instruction.  Its owner must have
                // exact frozen binding provenance.
                if !self
                    .control
                    .source_storage
                    .binding_locals
                    .iter()
                    .flatten()
                    .any(|candidate| candidate == local)
                {
                    return Err("MIR conditional destroy targets non-source storage".into());
                }
                return Ok(());
            }
            _ => {}
        }
        if let MirInstruction::Copy { dst, src } = instruction {
            if !mir_type_is_duplicable(self.local_type(*src)?, &self.nominal_copy_descriptors) {
                return Err(format!(
                    "MIR copy duplicates an affine capability from local {} ({:?}, source {:?}) into {}",
                    src.0, self.local_type(*src)?, self.locals[src.0 as usize].source, dst.0
                ));
            }
            return Ok(());
        }
        if let MirInstruction::ConstF64 { dst, bits } = instruction {
            if self.local_type(*dst)? != &Type::Scalar(crate::types::ScalarType::F64) {
                return Err("MIR f64 constant destination is not f64".into());
            }
            if !is_canonical_f64_bits(*bits) {
                return Err("MIR f64 constant has a non-canonical NaN payload".into());
            }
            return Ok(());
        }
        if let MirInstruction::ConstF32 { dst, bits } = instruction {
            if self.local_type(*dst)? != &Type::Scalar(crate::types::ScalarType::F32) {
                return Err("MIR f32 constant destination is not f32".into());
            }
            if !is_canonical_f32_bits(*bits) {
                return Err("MIR f32 constant has a non-canonical NaN payload".into());
            }
            return Ok(());
        }
        if self.validate_fixed_scalar_instruction(instruction)? {
            return Ok(());
        }
        if self.validate_array_view_instruction(instruction)? {
            return Ok(());
        }
        if let MirInstruction::MakeCallable {
            callee,
            captures,
            environment,
            ..
        } = instruction
        {
            match environment {
                Some(environment) => {
                    let source = lifted_callable_definition(environment.brand);
                    if *callee != source && !specialized_lifted_targets.contains(callee) {
                        return Err(
                            "MIR callable environment brand does not match its lifted target"
                                .into(),
                        );
                    }
                    if captures.len() != environment.captures.len() {
                        return Err(
                            "MIR callable capture registers do not match their sealed layout"
                                .into(),
                        );
                    }
                    for (&local, capture) in captures.iter().zip(&environment.captures) {
                        if self.local_type(local)? != &capture.ty {
                            return Err(
                                "MIR callable capture type does not match its sealed layout".into(),
                            );
                        }
                    }
                }
                None if !captures.is_empty() => {
                    return Err("MIR callable has captures but no sealed environment".into());
                }
                None => {}
            }
            return Ok(());
        }
        if let MirInstruction::MakeLabel {
            dst,
            target,
            destination,
            brand,
            ..
        } = instruction
        {
            if *self.local_type(*dst)? != crate::types::label::new(*brand, self.local_type(*destination)?.clone()) {
                return Err("MIR label value nominal brand or payload disagrees with its destination".into());
            }
            let block = self
                .blocks
                .get(target.0 as usize)
                .ok_or_else(|| "MIR label value target block is absent".to_string())?;
            if self.control.tombstoned_blocks.contains(target) {
                return Err("MIR label value targets a tombstoned block".into());
            }
            if block.parameters.as_slice() != [*destination] {
                return Err("MIR label value target does not accept its exact payload".into());
            }
            return Ok(());
        }
        if let MirInstruction::Borrow {
            dst,
            src,
            fields,
            unique,
            reborrow,
        } = instruction
        {
            let Type::Reference {
                mutability,
                referent: destination_referent,
                ..
            } = self.local_type(*dst)?
            else {
                return Err("MIR borrow destination is not a reference".into());
            };
            let expected_mutability = if *unique {
                Mutability::Unique
            } else {
                Mutability::Shared
            };
            if *mutability != expected_mutability {
                return Err(
                    "MIR borrow destination mutability disagrees with its loan mode".into(),
                );
            }
            match (self.local_type(*src)?, *reborrow) {
                (
                    Type::Reference {
                        mutability: parent_mutability,
                        referent: source_referent,
                        ..
                    },
                    true,
                ) => {
                    if *unique && *parent_mutability != Mutability::Unique {
                        return Err("MIR unique reborrow has a shared parent reference".into());
                    }
                    if fields.is_empty() && destination_referent != source_referent {
                        return Err("MIR whole-reference reborrow changes its referent type".into());
                    }
                }
                (source_type, false)
                    if fields.is_empty() && destination_referent.as_ref() != source_type =>
                {
                    return Err(
                        "MIR whole-place borrow referent does not match its source type".into(),
                    );
                }
                (_, true) => {
                    return Err("MIR reborrow source is not a reference".into());
                }
                _ => {}
            }
            return Ok(());
        }
        if let MirInstruction::MakeArray {
            dst,
            fields,
            element_type,
        } = instruction
        {
            if self.local_type(*dst)?.array_element() != Some(element_type)
                || !self.local_type(*dst)?.array_accepts_count(fields.len()) {
                return Err("MIR array destination does not have its array type".into());
            }
            for field in fields {
                if self.local_type(*field)? != element_type {
                    return Err("MIR array field does not match its element type".into());
                }
            }
            return Ok(());
        }
        if let MirInstruction::Store { dst, src } = instruction {
            if self.local_type(*dst)? != self.local_type(*src)? {
                return Err("MIR store value does not match its destination type".into());
            }
            return Ok(());
        }
        if let MirInstruction::UpdateRecord {
            dst,
            base,
            index,
            field_count,
            value,
            field_type,
        } = instruction
        {
            if index >= field_count {
                return Err("MIR record update field index is outside its field count".into());
            }
            if self.local_type(*dst)? != self.local_type(*base)? {
                return Err("MIR record update destination does not match its base type".into());
            }
            if self.local_type(*value)? != field_type {
                return Err("MIR record update value does not match its field type".into());
            }
            if !matches!(self.local_type(*base)?, Type::Nominal { .. }) {
                return Err("MIR record update base is not nominal".into());
            }
            return Ok(());
        }
        if let MirInstruction::PatternTest {
            dst,
            subject,
            pattern,
        } = instruction
        {
            if self.local_type(*dst)? != &Type::Scalar(crate::types::ScalarType::Bool) {
                return Err("MIR pattern test destination is not Bool".into());
            }
            return validate_pattern(pattern, self.local_type(*subject)?);
        }
        if let MirInstruction::InstallHandler {
            payload_destinations,
            continuation,
            target,
            ..
        } = instruction
        {
            if matches!(continuation, MirContinuationPolicy::Replay { uses } if *uses < 2) {
                return Err("MIR replay handler has fewer than two exact uses".into());
            }
            if target.0 as usize >= self.blocks.len() {
                return Err("MIR handler target block is absent".into());
            }
            if self.control.tombstoned_blocks.contains(target) {
                return Err("MIR handler targets a tombstoned block".into());
            }
            let mut destinations = BTreeSet::new();
            for destination in payload_destinations {
                self.local_type(*destination)?;
                if !destinations.insert(*destination) {
                    return Err("MIR handler repeats a payload destination".into());
                }
            }
            return Ok(());
        }
        if let MirInstruction::ProjectTuple {
            dst,
            base,
            index,
            field_count,
            field_type,
        } = instruction
        {
            let Type::Tuple(fields) = self.local_type(*base)? else {
                return Err("MIR tuple projection base is not a tuple".into());
            };
            if *field_count != fields.len() as u32 || *index >= *field_count {
                return Err("MIR tuple projection is outside its tuple layout".into());
            }
            if self.local_type(*dst)? != field_type
                || fields.get(*index as usize) != Some(field_type)
            {
                return Err("MIR tuple projection type does not match its layout".into());
            }
            return Ok(());
        }
        if let MirInstruction::ProjectArray {
            dst,
            base,
            index,
            field_count,
            element_type,
        } = instruction
        {
            let Some(actual) = self.local_type(*base)?.array_element() else {
                return Err("MIR array projection base is not an array".into());
            };
            if *index >= *field_count || actual != element_type
                || !self.local_type(*base)?.array_accepts_count(*field_count as usize) {
                return Err("MIR array projection has inconsistent structural metadata".into());
            }
            if self.local_type(*dst)? != element_type {
                return Err("MIR array projection result type does not match its element".into());
            }
            return Ok(());
        }
        let (dst, definition, fields, field_types) = match instruction {
            MirInstruction::MakeRecord {
                dst,
                definition,
                fields,
                field_types,
            }
            | MirInstruction::MakeEnum {
                dst,
                definition,
                fields,
                field_types,
                ..
            } => (dst, definition, fields, field_types),
            _ => return Ok(()),
        };
        if fields.len() != field_types.len() {
            return Err("MIR record construction has mismatched field values and types".into());
        }
        match self.local_type(*dst)? {
            Type::Nominal {
                definition: actual, ..
            } if actual == definition => {}
            _ => return Err("MIR record destination does not have its nominal type".into()),
        }
        for (&field, expected) in fields.iter().zip(field_types) {
            if self.local_type(field)? != expected {
                return Err("MIR record field does not match its declared type".into());
            }
        }
        Ok(())
    }
    fn validate_edge(&self, target: MirBlockId, arguments: &[MirLocal]) -> Result<(), String> {
        if self.control.tombstoned_blocks.contains(&target) {
            return Err(format!("MIR edge targets tombstoned block {}", target.0));
        }
        let target = self
            .blocks
            .get(target.0 as usize)
            .ok_or_else(|| format!("MIR edge targets absent block {}", target.0))?;
        if arguments.len() != target.parameters.len() {
            return Err(format!(
                "MIR edge has {} arguments for {} block parameters",
                arguments.len(),
                target.parameters.len()
            ));
        }
        for (&argument, &parameter) in arguments.iter().zip(&target.parameters) {
            if self.local_type(argument)? != self.local_type(parameter)? {
                return Err("MIR edge argument type does not match block parameter".into());
            }
        }
        Ok(())
    }
    fn validate_terminator(&self, index: usize, terminator: &MirTerminator) -> Result<(), String> {
        match terminator {
            MirTerminator::Goto { target, arguments } => self.validate_edge(*target, arguments),
            MirTerminator::Leave {
                target,
                arguments,
                cleanup,
                ..
            } => {
                cleanup.validate()?;
                cleanup.validate_with_storage(
                    &self.control.move_paths,
                    &self.control.source_storage,
                )?;
                self.validate_leave_cleanup_payloads(index, arguments, cleanup)?;
                self.validate_edge(*target, arguments)
            }
            MirTerminator::SwitchBool {
                condition,
                then_target,
                then_arguments,
                else_target,
                else_arguments,
            } => {
                if self.local_type(*condition)? != &Type::Scalar(crate::types::ScalarType::Bool) {
                    return Err(format!("MIR switch block {index} condition is not Bool"));
                }
                self.validate_edge(*then_target, then_arguments)?;
                self.validate_edge(*else_target, else_arguments)
            }
            MirTerminator::Return { value } => {
                if self.local_type(*value)? != &self.result {
                    return Err(format!(
                        "MIR return in block {index} does not match function result"
                    ));
                }
                Ok(())
            }
            MirTerminator::Unreachable => Ok(()),
        }
    }
    fn validate_leave_cleanup_payloads(
        &self,
        _block: usize,
        arguments: &[MirLocal],
        cleanup: &MirCleanupPlan,
    ) -> Result<(), String> {
        if !self
            .control
            .source_storage
            .exited_bindings(cleanup.source_storage_scope, cleanup.target_storage_scope)?
            .is_empty()
            && cleanup.protected_values != arguments
        {
            return Err("MIR cleanup protected values do not exactly match leave payloads".into());
        }
        // A cleanup path must never consume the value protected by the leave
        // edge. Parameter-origin bindings are the only compact-MIR mapping
        // available before full source-storage lowering, and are exact rather
        // than spelling-based.
        for path in &cleanup.moved_paths {
            let path = &self.control.move_paths.paths[path.0 as usize];
            let binding = &self.control.move_paths.bindings[path.binding.0 as usize];
            if let PlaceBindingOrigin::Parameter { index } = binding.origin
                && self
                    .parameters
                    .get(index as usize)
                    .is_some_and(|local| arguments.contains(local))
            {
                return Err("MIR cleanup disarms a protected leave payload".into());
            }
        }

        Ok(())
    }
}

fn lexical_scope_contexts(
    blocks: &[MirBlock],
    entry: MirBlockId,
) -> BTreeMap<MirBlockId, Vec<MirScopeEntry>> {
    let mut contexts = BTreeMap::new();
    let mut pending = VecDeque::new();
    if (entry.0 as usize) < blocks.len() {
        contexts.insert(entry, vec![]);
        pending.push_back(entry);
    }
    while let Some(block_id) = pending.pop_front() {
        let Some(block) = blocks.get(block_id.0 as usize) else {
            continue;
        };
        let mut context = contexts.get(&block_id).cloned().unwrap_or_default();
        for instruction in &block.instructions {
            match instruction {
                MirInstruction::MakeLabel { label, target, .. } => {
                    // A first-class invocation re-enters at `target` after
                    // leaving the label's own lexical scope. Preserve the
                    // handler prefix that existed *before* this capability
                    // was minted, so a target nested in an enclosing facade
                    // can later uninstall that facade normally.
                    merge_lexical_context(&mut contexts, &mut pending, *target, &context);
                    context.push(MirScopeEntry::Label(*label));
                }
                MirInstruction::InstallHandler { site, target, .. } => {
                    context.push(MirScopeEntry::Handler(*site));
                    merge_lexical_context(&mut contexts, &mut pending, *target, &context);
                }
                MirInstruction::UninstallHandler => {
                    if let Some(index) = context
                        .iter()
                        .rposition(|entry| matches!(entry, MirScopeEntry::Handler(_)))
                    {
                        context.truncate(index);
                    }
                }
                _ => {}
            }
        }
        match &block.terminator {
            MirTerminator::Goto { target, .. } => {
                merge_lexical_context(&mut contexts, &mut pending, *target, &context)
            }
            MirTerminator::SwitchBool {
                then_target,
                else_target,
                ..
            } => {
                merge_lexical_context(&mut contexts, &mut pending, *then_target, &context);
                merge_lexical_context(&mut contexts, &mut pending, *else_target, &context);
            }
            MirTerminator::Leave { label, target, .. } => {
                let exit = context
                    .iter()
                    .rposition(|entry| *entry == MirScopeEntry::Label(*label))
                    .map(|index| context[..index].to_vec())
                    // Direct branded leaves need not materialize a
                    // first-class label value. Their explicit cleanups have
                    // already left the lexical target prefix in `context`.
                    .unwrap_or_else(|| context.clone());
                merge_lexical_context(&mut contexts, &mut pending, *target, &exit);
            }
            MirTerminator::Return { .. } | MirTerminator::Unreachable => {}
        }
    }
    contexts
}

fn merge_lexical_context(
    contexts: &mut BTreeMap<MirBlockId, Vec<MirScopeEntry>>,
    pending: &mut VecDeque<MirBlockId>,
    block: MirBlockId,
    incoming: &[MirScopeEntry],
) {
    let Some(existing) = contexts.get_mut(&block) else {
        contexts.insert(block, incoming.to_vec());
        pending.push_back(block);
        return;
    };
    let common = existing
        .iter()
        .zip(incoming)
        .take_while(|(left, right)| left == right)
        .count();
    if common < existing.len() {
        existing.truncate(common);
        pending.push_back(block);
    }
}

fn intern_lexical_scope_context(
    context: &[MirScopeEntry],
    scopes: &mut Vec<MirScopeData>,
    ids: &mut BTreeMap<Vec<MirScopeEntry>, MirScopeId>,
) -> MirScopeId {
    if let Some(id) = ids.get(context) {
        return *id;
    }
    let (last, parent_context) = context
        .split_last()
        .expect("the root scope context is interned before child scopes");
    let parent = intern_lexical_scope_context(parent_context, scopes, ids);
    let id = MirScopeId(scopes.len() as u32);
    scopes.push(MirScopeData {
        parent: Some(parent),
        entered_label: match last {
            MirScopeEntry::Label(label) => Some(*label),
            MirScopeEntry::Handler(_) => None,
        },
        entered_handler: match last {
            MirScopeEntry::Label(_) => None,
            MirScopeEntry::Handler(handler) => Some(*handler),
        },
    });
    ids.insert(context.to_vec(), id);
    id
}

fn lexical_handler_candidates(
    control: &MirControlTables,
    scope: MirScopeId,
    effect: DefKey,
    effect_arguments: &[crate::GenericArgument],
    operation: u32,
) -> Vec<MirHandlerSiteId> {
    let mut candidates = Vec::new();
    let mut current = Some(scope);
    while let Some(scope) = current {
        let Some(data) = control.scopes.get(scope.0 as usize) else {
            break;
        };
        if let Some(site) = data.entered_handler
            && let Some(handler) = control.handlers.get(site.0 as usize)
            && handler.effect == effect
            && handler.effect_arguments == effect_arguments
            && handler.operation == operation
        {
            candidates.push(site);
        }
        current = data.parent;
    }
    candidates
}

fn scope_enters_label(
    control: &MirControlTables,
    child: MirScopeId,
    parent: MirScopeId,
    label: MirLabelId,
) -> bool {
    control
        .scopes
        .get(child.0 as usize)
        .is_some_and(|scope| scope.parent == Some(parent) && scope.entered_label == Some(label))
}

fn scope_enters_handler(
    control: &MirControlTables,
    child: MirScopeId,
    parent: MirScopeId,
    handler: MirHandlerSiteId,
) -> bool {
    control
        .scopes
        .get(child.0 as usize)
        .is_some_and(|scope| scope.parent == Some(parent) && scope.entered_handler == Some(handler))
}

fn scope_after_uninstall(control: &MirControlTables, scope: MirScopeId) -> Option<MirScopeId> {
    let mut current = scope;
    loop {
        let data = control.scopes.get(current.0 as usize)?;
        if data.entered_handler.is_some() {
            return data.parent;
        }
        current = data.parent?;
    }
}

fn scope_is_ancestor(control: &MirControlTables, ancestor: MirScopeId, scope: MirScopeId) -> bool {
    let mut current = Some(scope);
    while let Some(id) = current {
        if id == ancestor {
            return true;
        }
        current = control
            .scopes
            .get(id.0 as usize)
            .and_then(|data| data.parent);
    }
    false
}

fn freeze_control_instruction(
    instruction: &mut MirInstruction,
    block: MirBlockId,
    context: &mut Vec<MirScopeEntry>,
    control: &mut MirControlTables,
    scope_ids: &mut BTreeMap<Vec<MirScopeEntry>, MirScopeId>,
    originating_handler: Option<MirHandlerSiteId>,
) {
    match instruction {
        MirInstruction::MakeLabel { label, .. } => {
            context.push(MirScopeEntry::Label(*label));
            control.labels[label.0 as usize].scope =
                intern_lexical_scope_context(context, &mut control.scopes, scope_ids);
        }
        MirInstruction::InstallHandler { site, .. } => {
            context.push(MirScopeEntry::Handler(*site));
            control.handlers[site.0 as usize].scope =
                intern_lexical_scope_context(context, &mut control.scopes, scope_ids);
        }
        MirInstruction::UninstallHandler => {
            if let Some(index) = context
                .iter()
                .rposition(|entry| matches!(entry, MirScopeEntry::Handler(_)))
            {
                context.truncate(index);
            }
        }
        MirInstruction::Perform {
            site,
            effect,
            effect_arguments,
            operation,
            ..
        } => {
            let scope = intern_lexical_scope_context(context, &mut control.scopes, scope_ids);
            let id = MirPerformSiteId(control.performs.len() as u32);
            control.performs.push(MirPerformSiteData {
                block,
                scope,
                effect: *effect,
                effect_arguments: effect_arguments.clone(),
                operation: *operation,
                handler_candidates: lexical_handler_candidates(
                    control,
                    scope,
                    *effect,
                    effect_arguments,
                    *operation,
                ),
            });
            *site = id;
        }
        MirInstruction::CaptureResumption { site, .. } => freeze_resumption_site(
            site,
            MirResumptionSiteKind::Capture,
            block,
            context,
            control,
            scope_ids,
            originating_handler,
        ),
        MirInstruction::Resume { site, .. } => freeze_resumption_site(
            site,
            MirResumptionSiteKind::Resume,
            block,
            context,
            control,
            scope_ids,
            originating_handler,
        ),
        MirInstruction::ResumeReturn { site, .. } => freeze_resumption_site(
            site,
            MirResumptionSiteKind::ResumeReturn,
            block,
            context,
            control,
            scope_ids,
            originating_handler,
        ),
        MirInstruction::ResumeSnapshot { site, .. } => freeze_resumption_site(
            site,
            MirResumptionSiteKind::ResumeSnapshot,
            block,
            context,
            control,
            scope_ids,
            originating_handler,
        ),
        MirInstruction::Forward { site } => freeze_resumption_site(
            site,
            MirResumptionSiteKind::Forward,
            block,
            context,
            control,
            scope_ids,
            originating_handler,
        ),
        MirInstruction::Cancel { site } => freeze_resumption_site(
            site,
            MirResumptionSiteKind::Cancel,
            block,
            context,
            control,
            scope_ids,
            originating_handler,
        ),
        _ => {}
    }
}

fn freeze_resumption_site(
    site: &mut MirResumptionSiteId,
    kind: MirResumptionSiteKind,
    block: MirBlockId,
    context: &[MirScopeEntry],
    control: &mut MirControlTables,
    scope_ids: &mut BTreeMap<Vec<MirScopeEntry>, MirScopeId>,
    originating_handler: Option<MirHandlerSiteId>,
) {
    let id = MirResumptionSiteId(control.resumptions.len() as u32);
    control.resumptions.push(MirResumptionSiteData {
        block,
        scope: intern_lexical_scope_context(context, &mut control.scopes, scope_ids),
        kind,
        // A resumption belongs to the handler clause CFG entered through its
        // explicit target, not merely to an active protected frame. Nested
        // setup code may execute under several frames before it reaches a
        // clause, so using the nearest lexical frame here would forge a
        // handler-body provenance that the existing verifier rejects.
        originating_handler,
    });
    *site = id;
}

pub(crate) fn validate_nominal_copy_descriptors(
    descriptors: &[MirNominalCopyDescriptor],
) -> Result<(), String> {
    for (index, descriptor) in descriptors.iter().enumerate() {
        if descriptor.definition == crate::refinement::bindings_definition() {
            let ty = Type::Nominal { definition: descriptor.definition, arguments: descriptor.arguments.clone() };
            let fields = crate::refinement::binding_pack_fields(&ty).ok_or("MIR binding pack has no canonical environment layout")?;
            if descriptor.is_enum || descriptor.variants.as_slice() != [fields.to_vec()]
                || Some(descriptor.source_contract) != crate::refinement::binding_pack_contract(&ty) {
                return Err("MIR binding pack layout disagrees with its sealed environment".into());
            }
        }
        if descriptor.variants.is_empty() {
            return Err("MIR nominal copy descriptor has no variants".into());
        }
        if descriptors[..index].iter().any(|previous| {
            previous.definition == descriptor.definition
                && previous.arguments == descriptor.arguments
        }) {
            return Err("MIR nominal copy descriptor is duplicated".into());
        }
        for variant in &descriptor.variants {
            for field in variant {
                validate_mir_type(field, &mut vec![])?;
            }
        }
    }
    Ok(())
}

/// Native contracts need referent layouts even when no value of that type
/// ever occupies a source register. Keep this traversal separate from inline
/// copyability: following pointers must not make pointee ownership inline.
pub(crate) fn native_contract_nominals(
    roots: &[Type],
    signatures: &ElaboratedInterface,
) -> Result<Vec<Type>, String> {
    Ok(native_contract_residents(roots, signatures)?.into_iter()
        .filter(|ty| matches!(ty, Type::Nominal { .. })).collect())
}

pub(crate) fn native_contract_residents(
    roots: &[Type],
    signatures: &ElaboratedInterface,
) -> Result<Vec<Type>, String> {
    let mut pending = roots
        .iter()
        .cloned()
        .map(|ty| (ty, 0usize))
        .collect::<Vec<_>>();
    let mut seen = BTreeSet::new();
    let mut nominals = vec![];
    while let Some((ty, depth)) = pending.pop() {
        if !seen.insert(crate::types::canonical_type_encoding(&ty)) {
            continue;
        }
        // Recursive pointers to the same concrete type terminate via `seen`.
        // Expanding generic recursion must fail finitely instead of building
        // an unbounded contract (e.g. Node<T> -> *Node<(T,)> -> ...).
        if depth > 128 || seen.len() > 4096 {
            return Err("native source contract exceeds its finite layout closure limit".into());
        }
        let mut children = vec![];
        match &ty {
            Type::Nominal {
                definition,
                arguments,
            } => {
                nominals.push(ty.clone());
                children.extend(arguments.iter().filter_map(|argument| match argument {
                    GenericArgument::Type(ty) => Some(ty.clone()),
                    _ => None,
                }));
                if let Some(ElaboratedHeader::Nominal { layout, .. }) =
                    signatures.definitions.get(definition)
                    && let Some(variants) = instantiate_nominal_copy_layout(layout, arguments)
                {
                    children.extend(variants.into_iter().flatten());
                }
            }
            Type::Tuple(fields) => {
                nominals.push(ty.clone());
                children.extend(fields.iter().cloned());
            }
            Type::FixedArray { element, .. } => {
                nominals.push(ty.clone());
                children.push((**element).clone());
            }
            Type::Array(element)
            | Type::StaticData { element, .. }
            | Type::RawPointer {
                pointee: element, ..
            }
            | Type::Reference {
                referent: element, ..
            } => children.push((**element).clone()),
            Type::Callable {
                parameters, result, ..
            } => {
                children.extend(parameters.iter().cloned());
                children.push((**result).clone());
            }
            _ => {}
        }
        pending.extend(children.into_iter().map(|ty| (ty, depth + 1)));
    }
    Ok(nominals)
}

/// Instantiate a declaration-owned layout using the entire nominal argument
/// vector. `ElaboratedInterface`'s executable-field query intentionally
/// focuses on type arguments; copyability also needs empty and scalar-only
/// layouts such as `Tag<n: u32>`, whose identity carries a non-type binder.
pub(crate) fn instantiate_nominal_copy_layout(
    layout: &ElaboratedNominalLayout,
    arguments: &[GenericArgument],
) -> Option<Vec<Vec<Type>>> {
    let instantiate_fields = |fields: &[crate::signature::NominalField]| {
        fields
            .iter()
            .map(|field| substitute_nominal_copy_type(&field.ty, arguments))
            .collect()
    };
    match layout {
        ElaboratedNominalLayout::Struct(fields) | ElaboratedNominalLayout::TupleStruct(fields) => Some(vec![instantiate_fields(fields)]),
        ElaboratedNominalLayout::Enum(variants) => Some(
            variants
                .iter()
                .map(|variant| match &variant.payload {
                    ElaboratedEnumVariantPayload::Unit => vec![],
                    ElaboratedEnumVariantPayload::Tuple(fields) => fields
                        .iter()
                        .map(|field| substitute_nominal_copy_type(field, arguments))
                        .collect(),
                    ElaboratedEnumVariantPayload::Struct(fields) => instantiate_fields(fields),
                })
                .collect(),
        ),
        ElaboratedNominalLayout::Opaque => None,
    }
}

fn substitute_nominal_copy_type(value: &Type, arguments: &[GenericArgument]) -> Type {
    match value {
        Type::Generic(slot) => arguments
            .get(*slot as usize)
            .and_then(|argument| match argument {
                GenericArgument::Type(value) => Some(value.clone()),
                _ => None,
            })
            .unwrap_or_else(|| value.clone()),
        Type::Tuple(fields) => Type::Tuple(
            fields
                .iter()
                .map(|field| substitute_nominal_copy_type(field, arguments))
                .collect(),
        ),
        Type::Array(element) => {
            Type::Array(Box::new(substitute_nominal_copy_type(element, arguments)))
        }
        Type::FixedArray { element, length } => Type::FixedArray {
            element: Box::new(substitute_nominal_copy_type(element, arguments)),
            length: Box::new(crate::service::specialize_generic_argument(length, arguments)),
        },
        Type::RawPointer { mutability, pointee } => Type::RawPointer {
            mutability: *mutability,
            pointee: Box::new(substitute_nominal_copy_type(pointee, arguments)),
        },
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability: *mutability,
            lifetime: match lifetime {
                crate::Lifetime::Generic(index) => arguments.get(*index as usize)
                    .and_then(|argument| match argument { GenericArgument::Lifetime(value) => Some(*value), _ => None })
                    .unwrap_or(*lifetime),
                _ => *lifetime,
            },
            referent: Box::new(substitute_nominal_copy_type(referent, arguments)),
        },
        Type::Nominal {
            definition,
            arguments: nested,
        } => Type::Nominal {
            definition: *definition,
            arguments: nested
                .iter()
                .map(|argument| substitute_nominal_copy_argument(argument, arguments))
                .collect(),
        },
        Type::ConstGeneric { index, kind } => arguments
            .get(*index as usize)
            .and_then(|argument| match (kind, argument) {
                (expected, GenericArgument::ConstInteger(value)) if *expected == value.kind() => {
                    Some(Type::ConstInteger(*value))
                }
                (crate::types::ConstKind::Quantity, GenericArgument::ConstQuantity(value)) => {
                    Some(Type::ConstQuantity(*value))
                }
                (expected, GenericArgument::ConstGeneric { index, kind }) if expected == kind => {
                    Some(Type::ConstGeneric {
                        index: *index,
                        kind: *kind,
                    })
                }
                _ => None,
            })
            .unwrap_or_else(|| value.clone()),
        // Callable and projection forms do not contribute inline nominal
        // storage to this layout. They retain their existing sealed type
        // contracts and are validated independently.
        _ => value.clone(),
    }
}

fn substitute_nominal_copy_argument(
    value: &GenericArgument,
    arguments: &[GenericArgument],
) -> GenericArgument {
    match value {
        GenericArgument::Lifetime(crate::Lifetime::Generic(index)) => arguments.get(*index as usize)
            .filter(|argument| matches!(argument, GenericArgument::Lifetime(_)))
            .cloned().unwrap_or_else(|| value.clone()),
        GenericArgument::Type(value) => {
            GenericArgument::Type(substitute_nominal_copy_type(value, arguments))
        }
        GenericArgument::ConstGeneric { index, kind } => arguments
            .get(*index as usize)
            .filter(|argument| match (kind, argument) {
                (expected, GenericArgument::ConstInteger(value)) => *expected == value.kind(),
                (crate::types::ConstKind::Quantity, GenericArgument::ConstQuantity(_)) => true,
                (expected, GenericArgument::ConstGeneric { kind, .. }) => expected == kind,
                _ => false,
            })
            .cloned()
            .unwrap_or_else(|| value.clone()),
        GenericArgument::ConstIntegerExpr(value) => crate::types::integer_const_argument(value.substitute_arguments(arguments)),
        value => value.clone(),
    }
}

pub(crate) fn mir_type_is_duplicable(ty: &Type, descriptors: &[MirNominalCopyDescriptor]) -> bool {
    fn visit(
        ty: &Type,
        descriptors: &[MirNominalCopyDescriptor],
        active: &mut Vec<(DefKey, Vec<GenericArgument>)>,
    ) -> bool {
        if crate::types::label::payload(ty).is_some() { return true; }
        match ty {
            Type::Reference { mutability, .. } => *mutability != Mutability::Unique,
            Type::Tuple(elements) => elements
                .iter()
                .all(|element| visit(element, descriptors, active)),
            Type::Array(element) | Type::FixedArray { element, .. } => visit(element, descriptors, active),
            Type::Nominal {
                definition,
                arguments,
            } => {
                let key = (*definition, arguments.clone());
                let Some(descriptor) = descriptors.iter().find(|candidate| {
                    candidate.definition == *definition && candidate.arguments == *arguments
                }) else {
                    return false;
                };
                if active.contains(&key) {
                    return false;
                }
                active.push(key.clone());
                let result = descriptor.variants.iter().all(|variant| {
                    variant
                        .iter()
                        .all(|field| visit(field, descriptors, active))
                });
                active.pop();
                result
            }
            // Generic-copy authority is checked by `Lowerer` against the
            // callable's explicit `Use<[0,*]>` bounds before it emits a
            // `Copy`. MIR validation only sees the frozen generic type, so
            // it accepts that already-proved instruction here.
            Type::Generic(_) => true,
            Type::Infer(_) | Type::Error => false,
            Type::Callable { .. } => true,
            _ => true,
        }
    }
    visit(ty, descriptors, &mut Vec::new())
}

/// MIR is still permitted to carry declaration-owned generic parameters until
/// instance materialization, including an associated structural-constant
/// projection whose subject still depends on such a declaration binder. It
/// must never carry body-local inference, recovery poison, or a higher-ranked
/// lifetime whose binder is absent. Concrete instance materialization resolves
/// every delayed projection before the VM boundary. The walk intentionally
/// reaches type and effect arguments embedded in callable, nominal, aggregate,
/// pattern, and handler metadata as well as local types.
pub(crate) fn validate_mir_type(ty: &Type, lifetime_binders: &mut Vec<u32>) -> Result<(), String> {
    if let Type::Projection {
        item_generic_kinds,
        item_arguments,
        ..
    } = ty
        && !projection_item_arguments_match_kinds(item_generic_kinds, item_arguments)
    {
        return Err("MIR associated type projection has invalid item generic arguments".into());
    }
    if !is_canonical_type_identity(ty) {
        return Err("MIR semantic type has a non-canonical identity representation".into());
    }
    match ty {
        Type::Infer(_) => Err("MIR semantic type retains an unresolved inference variable".into()),
        Type::FixedArray { element, length } => {
            validate_mir_type(element, lifetime_binders)?;
            validate_mir_generic_argument(length, lifetime_binders)
        }
        Type::Error => Err("MIR semantic type retains recovered error poison".into()),
        Type::Nominal { arguments, .. } => arguments
            .iter()
            .try_for_each(|argument| validate_mir_generic_argument(argument, lifetime_binders)),
        Type::Projection {
            subject,
            trait_arguments,
            item_generic_kinds: _,
            item_arguments,
            ..
        } => {
            validate_mir_type(subject, lifetime_binders)?;
            trait_arguments.iter().try_for_each(|argument| {
                validate_mir_generic_argument(argument, lifetime_binders)
            })?;
            item_arguments
                .iter()
                .try_for_each(|argument| validate_mir_generic_argument(argument, lifetime_binders))
        }
        Type::Tuple(elements) => elements
            .iter()
            .try_for_each(|element| validate_mir_type(element, lifetime_binders)),
        Type::Array(element) | Type::StaticData { element, .. }
        | Type::RawPointer { pointee: element, .. } => {
            validate_mir_type(element, lifetime_binders)
        }
        Type::Reference {
            lifetime, referent, ..
        } => {
            validate_mir_lifetime(*lifetime, lifetime_binders)?;
            validate_mir_type(referent, lifetime_binders)
        }
        Type::Callable {
            lifetime_binders: count,
            parameters,
            result,
            effects,
            ..
        } => {
            lifetime_binders.push(*count);
            let validation = parameters
                .iter()
                .try_for_each(|parameter| validate_mir_type(parameter, lifetime_binders))
                .and_then(|()| validate_mir_type(result, lifetime_binders))
                .and_then(|()| validate_mir_effect_row(effects, lifetime_binders));
            lifetime_binders.pop();
            validation
        }
        // Bytecode gives `Never` a real zero-sized bottom representation. It
        // is valid in a callable result and in a recursively carried semantic
        // contract; recovered error types remain the fail-closed boundary.
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstInteger(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Generic(_) => Ok(()),
    }
}

fn validate_mir_generic_argument(
    argument: &GenericArgument,
    lifetime_binders: &mut Vec<u32>,
) -> Result<(), String> {
    if !is_canonical_generic_argument_identity(argument) {
        return Err("MIR generic argument has a non-canonical identity representation".into());
    }
    match argument {
        GenericArgument::ConstInfer { .. } => {
            Err("MIR generic argument contains unresolved const inference".into())
        }
        GenericArgument::Type(ty) => validate_mir_type(ty, lifetime_binders),
        GenericArgument::EffectRow(effects) => validate_mir_effect_row(effects, lifetime_binders),
        GenericArgument::Lifetime(lifetime) => validate_mir_lifetime(*lifetime, lifetime_binders),
        GenericArgument::ConstInteger(_)
        | GenericArgument::ConstIntegerExpr(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. } => Ok(()),
        GenericArgument::ConstProjection {
            subject,
            trait_arguments,
            ..
        } => {
            validate_mir_type(subject, lifetime_binders)?;
            trait_arguments
                .iter()
                .try_for_each(|argument| validate_mir_generic_argument(argument, lifetime_binders))
        }
    }
}

fn validate_mir_effect_row(
    effects: &crate::EffectRow,
    lifetime_binders: &mut Vec<u32>,
) -> Result<(), String> {
    if effects.tails.iter().any(|tail| matches!(tail, crate::EffectTail::Infer(_))) {
        return Err("MIR effect row retains an unresolved inference tail".into());
    }
    for effect in &effects.effects {
        for argument in &effect.arguments {
            validate_mir_generic_argument(argument, lifetime_binders)?;
        }
    }
    for projection in &effects.projections {
        validate_mir_type(&projection.subject, lifetime_binders)?;
        for argument in &projection.trait_arguments {
            validate_mir_generic_argument(argument, lifetime_binders)?;
        }
        for argument in &projection.item_arguments {
            validate_mir_generic_argument(argument, lifetime_binders)?;
        }
    }
    Ok(())
}

fn validate_mir_lifetime(
    lifetime: crate::Lifetime,
    lifetime_binders: &[u32],
) -> Result<(), String> {
    if matches!(lifetime, crate::Lifetime::Infer(_)) {
        return Err("MIR retains unresolved lifetime inference".into());
    }
    let crate::Lifetime::Bound { depth, index } = lifetime else {
        return Ok(());
    };
    let Some(count) = lifetime_binders.iter().rev().nth(depth as usize) else {
        return Err("MIR lifetime refers to an absent higher-ranked binder".into());
    };
    if index >= *count {
        return Err("MIR lifetime refers to an out-of-range higher-ranked binder".into());
    }
    Ok(())
}

pub(crate) fn validate_instruction_semantic_types(instruction: &MirInstruction) -> Result<(), String> {
    let mut lifetime_binders = vec![];
    match instruction {
        MirInstruction::DeferredLiteral { .. } => Ok(()),
        MirInstruction::MakeArray { element_type, .. } => {
            validate_mir_type(element_type, &mut lifetime_binders)
        }
        MirInstruction::MakeRecord { field_types, .. }
        | MirInstruction::MakeEnum { field_types, .. } => field_types
            .iter()
            .try_for_each(|ty| validate_mir_type(ty, &mut lifetime_binders)),
        MirInstruction::ProjectRecord { field_type, .. }
        | MirInstruction::ProjectTuple { field_type, .. }
        | MirInstruction::ProjectArray {
            element_type: field_type,
            ..
        }
        | MirInstruction::UpdateRecord { field_type, .. } => {
            validate_mir_type(field_type, &mut lifetime_binders)
        }
        MirInstruction::PatternTest { pattern, .. } => {
            validate_mir_pattern_semantic_types(pattern, &mut lifetime_binders)
        }
        MirInstruction::Perform {
            effect_arguments, ..
        } => effect_arguments.iter().try_for_each(|argument| {
            validate_mir_generic_argument(argument, &mut lifetime_binders)
        }),
        MirInstruction::InstallHandler {
            effect_arguments,
            resume_type,
            ..
        } => {
            effect_arguments.iter().try_for_each(|argument| {
                validate_mir_generic_argument(argument, &mut lifetime_binders)
            })?;
            validate_mir_type(resume_type, &mut lifetime_binders)
        }
        MirInstruction::Call {
            generic_arguments,
            trait_instance,
            ..
        }
        | MirInstruction::MakeCallable {
            generic_arguments,
            trait_instance,
            ..
        } => {
            generic_arguments.iter().try_for_each(|argument| {
                validate_mir_generic_argument(argument, &mut lifetime_binders)
            })?;
            if let Some(instance) = trait_instance {
                instance.trait_arguments.iter().try_for_each(|argument| {
                    validate_mir_generic_argument(argument, &mut lifetime_binders)
                })?;
                instance.method_arguments.iter().try_for_each(|argument| {
                    validate_mir_generic_argument(argument, &mut lifetime_binders)
                })?;
            }
            if let MirInstruction::MakeCallable {
                environment: Some(environment),
                ..
            } = instruction
            {
                environment.captures.iter().try_for_each(|capture| {
                    validate_mir_type(&capture.ty, &mut lifetime_binders)
                })?;
            }
            Ok(())
        }
        MirInstruction::HostCallOwned { capability, symbol, .. }
        | MirInstruction::HostCall {
            capability, symbol, ..
        } if capability.is_empty()
            || symbol.is_empty()
            || capability.contains('*')
            || capability.chars().any(char::is_whitespace) =>
        {
            Err("MIR host import identity is not canonical".into())
        }
        MirInstruction::HostCallOwned { parameters, result, .. }
        | MirInstruction::HostCall {
            parameters, result, ..
        } => {
            parameters
                .iter()
                .try_for_each(|ty| validate_mir_type(ty, &mut lifetime_binders))?;
            validate_mir_type(result, &mut lifetime_binders)
        }
        MirInstruction::MemoryIntrinsic { types, .. } => types.iter()
            .try_for_each(|ty| validate_mir_type(ty, &mut lifetime_binders)),
        MirInstruction::Abort
        | MirInstruction::FloatIntrinsic { .. }
        | MirInstruction::IntIntrinsic { .. }
        | MirInstruction::IntGenericIntrinsic { .. } => Ok(()),
        MirInstruction::TextByteLen { .. } | MirInstruction::StaticLen { .. } => Ok(()),
        MirInstruction::TextConcat { .. }
        | MirInstruction::TextEq { .. }
        | MirInstruction::TextFromUtf8Checked { .. }
        | MirInstruction::TextAsBytes { .. } => Ok(()),
        MirInstruction::CharFromU32Checked { .. } | MirInstruction::CharToU32 { .. } => Ok(()),
        MirInstruction::StoreUsize { .. }
        | MirInstruction::ArrayLen { .. }
        | MirInstruction::ArrayElementIsInitialized { .. }
        | MirInstruction::TakeArrayElement { .. }
        | MirInstruction::BytesLen { .. }
        | MirInstruction::BytesConcat { .. }
        | MirInstruction::BytesGet { .. }
        | MirInstruction::BytesSlice { .. }
        | MirInstruction::BytesFromArrayMove { .. }
        | MirInstruction::BytesToArray { .. }
        | MirInstruction::BytesUtf8ValidUpTo { .. }
        | MirInstruction::Blake3 { .. } => Ok(()),
        MirInstruction::ArrayGetBorrowShared { element_type, .. } | MirInstruction::ArrayEmpty { element_type, .. } | MirInstruction::ArrayPushMove { element_type, .. } => {
            validate_mir_type(element_type, &mut lifetime_binders)
        }
        MirInstruction::U32CheckedAdd { .. }
        | MirInstruction::U32CheckedSub { .. }
        | MirInstruction::U32CheckedMul { .. }
        | MirInstruction::U32CheckedDiv { .. }
        | MirInstruction::U32CheckedRem { .. }
        | MirInstruction::U32WrappingAdd { .. }
        | MirInstruction::U32WrappingSub { .. }
        | MirInstruction::U32WrappingMul { .. }
        | MirInstruction::U32WrappingShl { .. }
        | MirInstruction::U32WrappingShr { .. }
        | MirInstruction::U32CheckedShl { .. }
        | MirInstruction::U32CheckedShr { .. }
        | MirInstruction::U32Eq { .. }
        | MirInstruction::U32Lt { .. }
        | MirInstruction::U32Le { .. }
        | MirInstruction::U32ToUsize { .. }
        | MirInstruction::UsizeToU32Checked { .. }
        | MirInstruction::I64ToU32Checked { .. }
        | MirInstruction::I64ToU32Wrapping { .. }
        | MirInstruction::I64ToUsizeChecked { .. }
        | MirInstruction::I64ToUsizeWrapping { .. }
        | MirInstruction::I64ToU8Checked { .. }
        | MirInstruction::I64ToU8Wrapping { .. }
        | MirInstruction::I64ToU16Checked { .. }
        | MirInstruction::I64ToU16Wrapping { .. }
        | MirInstruction::I64ToI16Checked { .. }
        | MirInstruction::I64ToI16Wrapping { .. }
        | MirInstruction::I64ToI32Checked { .. }
        | MirInstruction::I64ToI32Wrapping { .. } => Ok(()),
        MirInstruction::I64ToI8Checked { .. }
        | MirInstruction::I64ToI8Wrapping { .. }
        | MirInstruction::I64ToU64Checked { .. }
        | MirInstruction::I64ToU64Wrapping { .. }
        | MirInstruction::I64ToIsizeChecked { .. }
        | MirInstruction::I64ToIsizeWrapping { .. }
        | MirInstruction::I64ToU128Checked { .. }
        | MirInstruction::I64ToU128Wrapping { .. }
        | MirInstruction::I64ToI128Checked { .. }
        | MirInstruction::I64ToI128Wrapping { .. } => Ok(()),
        MirInstruction::ConstUnit { .. }
        | MirInstruction::ConstI64 { .. }
        | MirInstruction::ConstU8 { .. }
        | MirInstruction::ConstU16 { .. }
        | MirInstruction::ConstU32 { .. }
        | MirInstruction::ConstU64 { .. }
        | MirInstruction::ConstUsize { .. }
        | MirInstruction::ConstU128 { .. }
        | MirInstruction::ConstI8 { .. }
        | MirInstruction::ConstI16 { .. }
        | MirInstruction::ConstI32 { .. }
        | MirInstruction::ConstIsize { .. }
        | MirInstruction::ConstI128 { .. }
        | MirInstruction::ConstF32 { .. }
        | MirInstruction::ConstF64 { .. }
        | MirInstruction::ConstBool { .. }
        | MirInstruction::ConstChar { .. }
        | MirInstruction::ConstText { .. }
        | MirInstruction::ConstStaticData { .. }
        | MirInstruction::MakeTuple { .. }
        | MirInstruction::UninstallHandler
        | MirInstruction::CaptureResumption { .. }
        | MirInstruction::Resume { .. }
        | MirInstruction::ResumeReturn { .. }
        | MirInstruction::ResumeSnapshot { .. }
        | MirInstruction::Forward { .. }
        | MirInstruction::Cancel { .. }
        | MirInstruction::StorageLive { .. }
        | MirInstruction::StorageDead { .. }
        | MirInstruction::SetDropFlag { .. }
        | MirInstruction::DestroyIf { .. }
        | MirInstruction::ClaimEffectPayloads { .. }
        | MirInstruction::Drop { .. }
        | MirInstruction::DestroyCallable { .. }
        | MirInstruction::Copy { .. }
        | MirInstruction::TakeProjection { .. }
        | MirInstruction::IsInitialized { .. }
        | MirInstruction::Store { .. }
        | MirInstruction::Move { .. }
        | MirInstruction::Borrow { .. }
        | MirInstruction::DerefCopy { .. }
        | MirInstruction::DerefIsInitialized { .. }
        | MirInstruction::DerefMove { .. }
        | MirInstruction::DerefStore { .. }
        | MirInstruction::NotBool { .. }
        | MirInstruction::AddI64 { .. }
        | MirInstruction::WrappingAddI64 { .. }
        | MirInstruction::WrappingSubI64 { .. }
        | MirInstruction::WrappingMulI64 { .. }
        | MirInstruction::IntEqualI64 { .. }
        | MirInstruction::IntLessI64 { .. }
        | MirInstruction::IntGreaterI64 { .. }
        | MirInstruction::BitAndI64 { .. }
        | MirInstruction::BitAndU32 { .. }
        | MirInstruction::BitAndU64 { .. }
        | MirInstruction::BitAndGeneric { .. }
        | MirInstruction::BitXorI64 { .. }
        | MirInstruction::IntShrI64 { .. }
        | MirInstruction::BitOrI64 { .. }
        | MirInstruction::BitNotI64 { .. }
        | MirInstruction::ShlI64 { .. }
        | MirInstruction::SubI64 { .. }
        | MirInstruction::MulI64 { .. }
        | MirInstruction::DivI64 { .. }
        | MirInstruction::RemI64 { .. }
        | MirInstruction::AddF64 { .. }
        | MirInstruction::SubF64 { .. }
        | MirInstruction::MulF64 { .. }
        | MirInstruction::DivF64 { .. }
        | MirInstruction::RemF64 { .. }
        | MirInstruction::EqI64 { .. }
        | MirInstruction::NeI64 { .. }
        | MirInstruction::NeU32 { .. }
        | MirInstruction::NeU64 { .. }
        | MirInstruction::LtI64 { .. }
        | MirInstruction::LeI64 { .. }
        | MirInstruction::GtI64 { .. }
        | MirInstruction::GeI64 { .. }
        | MirInstruction::EqF64 { .. }
        | MirInstruction::NeF64 { .. }
        | MirInstruction::LtF64 { .. }
        | MirInstruction::LeF64 { .. }
        | MirInstruction::GtF64 { .. }
        | MirInstruction::GeF64 { .. }
        | MirInstruction::EqBool { .. }
        | MirInstruction::NeBool { .. }
        | MirInstruction::ConcatText { .. }
        | MirInstruction::EqText { .. }
        | MirInstruction::NeText { .. }
        | MirInstruction::EqChar { .. }
        | MirInstruction::NeChar { .. }
        | MirInstruction::LtChar { .. }
        | MirInstruction::LeChar { .. }
        | MirInstruction::GtChar { .. }
        | MirInstruction::GeChar { .. }
        | MirInstruction::MakeLabel { .. }
        | MirInstruction::CallOwned { .. }
        | MirInstruction::CallIndirectOwned { .. }
        | MirInstruction::CallIndirect { .. }
        | MirInstruction::CompleteHandler { .. } => Ok(()),
    }
}

fn validate_mir_pattern_semantic_types(
    pattern: &MirPattern,
    lifetime_binders: &mut Vec<u32>,
) -> Result<(), String> {
    match pattern {
        MirPattern::Any | MirPattern::Literal(_) => Ok(()),
        MirPattern::Tuple(patterns) => patterns
            .iter()
            .try_for_each(|pattern| validate_mir_pattern_semantic_types(pattern, lifetime_binders)),
        MirPattern::Array { element, elements, .. } => {
            validate_mir_type(element, lifetime_binders)?;
            elements.iter().try_for_each(|pattern| {
                validate_mir_pattern_semantic_types(pattern, lifetime_binders)
            })
        }
        MirPattern::Record {
            field_types,
            fields,
            ..
        }
        | MirPattern::Enum {
            field_types,
            fields,
            ..
        } => {
            for field_type in field_types {
                validate_mir_type(field_type, lifetime_binders)?;
            }
            for field in fields {
                validate_mir_type(&field.ty, lifetime_binders)?;
                validate_mir_pattern_semantic_types(&field.pattern, lifetime_binders)?;
            }
            Ok(())
        }
    }
}

/// Check that handler instructions emitted by one of the specialised lowerers
/// still implement the interface frozen by Typed Core.  The VM deliberately
/// does not need to know about source quantities or effect rows; this is the
/// last boundary where those source-level contracts and concrete handler
/// frames coexist.
///
/// Besides matching frame identities, this makes cancellation an explicit
/// cleanup choice.  A `Cancel` may only occur in the target region of an arm
/// whose frozen resumption was discarded and whose quantity admits zero uses.
/// Resumptive and partial arms must instead expose a `Resume` or `Forward`
/// exit.  Normal execution must uninstall every lexical frame it installs.
impl MirProgram {
    pub fn validate(&self) -> Result<(), String> {
        if !self.functions.contains_key(&self.entry) {
            return Err("MIR program entry is absent".into());
        }
        for (executable, instance) in &self.instances {
            if executable != &instance.executable || !self.functions.contains_key(executable) {
                return Err("MIR instance product has no matching executable body".into());
            }
            if *executable != DefKey(instance.key.fingerprint()) {
                return Err(
                    "MIR instance executable does not match its canonical substitution identity"
                        .into(),
                );
            }
            if self.functions[executable].definition != *executable {
                return Err(
                    "MIR instance body definition does not match its executable identity".into(),
                );
            }
            if materialized_instance_retains_generic_placeholder(&self.functions[executable]) {
                let function = &self.functions[executable];
                let detail = function.locals.iter().enumerate().find(|(_, local)| type_retains_generic_placeholder(&local.ty))
                    .map(|(index, local)| format!("local {index}: {:?}", local.ty))
                    .or_else(|| function.blocks.iter().enumerate().find_map(|(block, body)| body.instructions.iter().find(|instruction| instruction_retains_generic_placeholder(instruction))
                        .map(|instruction| format!("block {block}: {instruction:?}"))))
                    .unwrap_or_else(|| format!("result: {:?}", function.result));
                return Err(format!("MIR instance body retains a generic placeholder in frozen metadata ({:?}; {detail})", instance.key));
            }
        }
        let specialized_lifted_owners = self.specialized_lifted_target_owners()?;
        let mut function_owners = BTreeMap::<DefKey, InstanceKey>::new();
        for instance in self.instances.values() {
            if !instance.key.arguments().is_empty()
                && function_owners
                    .insert(instance.executable, instance.key.clone())
                    .is_some()
            {
                return Err("MIR concrete instances have duplicate executable owners".into());
            }
        }
        for (target, owner) in &specialized_lifted_owners {
            if function_owners.insert(*target, owner.clone()).is_some() {
                return Err("MIR specialized lifted callable collides with an instance body".into());
            }
        }
        for (definition, function) in &self.functions {
            let specialized_lifted_targets = function_owners.get(definition).map_or_else(
                BTreeSet::new,
                |owner| {
                    specialized_lifted_owners
                        .iter()
                        .filter_map(|(target, candidate)| (candidate == owner).then_some(*target))
                        .collect()
                },
            );
            function
                .validate_with_specialized_lifted_targets(&specialized_lifted_targets)
                .map_err(|message| format!("MIR function {definition:?}: {message}"))?;
            for block in &function.blocks {
                for instruction in &block.instructions {
                    if let MirInstruction::Call {
                        generic_arguments, ..
                    }
                    | MirInstruction::MakeCallable {
                        generic_arguments, ..
                    } = instruction
                        && !generic_arguments.is_empty()
                    {
                        return Err(
                            "MIR callable retained an unmaterialized generic substitution".into(),
                        );
                    }
                    if matches!(
                        instruction,
                        MirInstruction::Call {
                            trait_instance: Some(_),
                            ..
                        } | MirInstruction::MakeCallable {
                            trait_instance: Some(_),
                            ..
                        }
                    ) {
                        return Err(
                            "MIR callable retained an unmaterialized trait-method identity".into(),
                        );
                    }
                    if let MirInstruction::CallOwned { callee, .. }
                    | MirInstruction::Call { callee, .. }
                    | MirInstruction::MakeCallable { callee, .. } = instruction
                        && !self.functions.contains_key(callee)
                    {
                        return Err(format!("MIR call targets missing function {callee:?}"));
                    }
                    if let MirInstruction::HostCall { resident_operations, .. } | MirInstruction::HostCallOwned { resident_operations, .. } = instruction {
                        for (ty, destructor) in resident_operations {
                            let Some(destructor) = destructor else { continue; };
                            let target = self.functions.get(destructor).ok_or_else(|| format!("MIR native destruction targets missing function {destructor:?}"))?;
                            if target.parameters.len() != 1 || target.captures != 0 || target.local_type(target.parameters[0])? != ty
                                || target.result != Type::Unit || target.safety != crate::Safety::Safe {
                                return Err("MIR native destruction has an incompatible resident ABI".into());
                            }
                        }
                    }
                    match instruction {
                        MirInstruction::Call { callee, .. } | MirInstruction::CallOwned { callee, .. } if self.functions[callee].safety == crate::Safety::Unsafe && !function.unsafe_execution => {
                            return Err("MIR unsafe call omitted its unsafe implementation requirement".into());
                        }
                        MirInstruction::MakeCallable { dst, callee, .. } => {
                            if !matches!(function.local_type(*dst)?, Type::Callable { safety, .. } if *safety == self.functions[callee].safety) {
                                return Err("MIR callable value erased or changed its target safety contract".into());
                            }
                        }
                        _ => {}
                    }
                    if let MirInstruction::MakeCallable {
                        callee,
                        captures,
                        environment: Some(environment),
                        ..
                    } = instruction
                    {
                        let target = &self.functions[callee];
                        if target.captures != captures.len() as u32 {
                            return Err(
                                "MIR callable target capture count does not match sealed environment"
                                    .into(),
                            );
                        }
                        for (index, capture) in environment.captures.iter().enumerate() {
                            if target.local_type(MirLocal(index as u32))? != &capture.ty {
                                return Err(
                                    "MIR callable target capture type does not match sealed environment"
                                        .into(),
                                );
                            }
                        }
                        if let Some(destructor) = environment.destructor {
                            if destructor != callable_environment_destructor_definition(*callee) {
                                return Err("MIR capture destruction does not belong to its callable".into());
                            }
                            let cleanup = self.functions.get(&destructor)
                                .ok_or("MIR capture destruction target is missing")?;
                            if cleanup.captures != 0 || cleanup.parameters.len() != environment.captures.len()
                                || cleanup.result != Type::Unit || cleanup.safety != crate::Safety::Safe
                                || environment.captures.iter().enumerate().any(|(index, capture)|
                                    cleanup.locals[cleanup.parameters[index].0 as usize].ty != capture.ty)
                            {
                                return Err("MIR capture destruction has an incompatible environment ABI".into());
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Derive the only non-source lifted targets admissible in this program.
    /// A standalone `MirFunction` intentionally has no such authority: its
    /// callable target must exactly match the environment brand. Here, each
    /// exception is rooted in an admitted non-empty concrete instance and is
    /// followed transitively through the specialized lifted bodies it owns.
    pub(crate) fn specialized_lifted_target_owners(
        &self,
    ) -> Result<BTreeMap<DefKey, InstanceKey>, String> {
        let mut owners = BTreeMap::<DefKey, InstanceKey>::new();
        let mut pending = VecDeque::new();
        for instance in self.instances.values() {
            if !instance.key.arguments().is_empty() {
                pending.push_back((instance.executable, instance.key.clone()));
            }
        }

        while let Some((definition, instance)) = pending.pop_front() {
            let function = self.functions.get(&definition).ok_or_else(|| {
                "MIR instance product has no matching executable body".to_owned()
            })?;
            if function.definition != definition {
                return Err("MIR function definition disagrees with its program key".into());
            }
            for block in &function.blocks {
                for instruction in &block.instructions {
                    let MirInstruction::MakeCallable {
                        callee,
                        environment: Some(environment),
                        ..
                    } = instruction
                    else {
                        continue;
                    };
                    let source = lifted_callable_definition(environment.brand);
                    let target = materialized_lifted_callable_definition(&instance, source);
                    if *callee != target {
                        return Err(
                            "MIR generic instance does not target its canonical specialized lifted callable"
                                .into(),
                        );
                    }
                    match owners.get(&target) {
                        Some(owner) if owner != &instance => {
                            return Err(
                                "MIR specialized lifted callable has contradictory instance owners"
                                    .into(),
                            );
                        }
                        Some(_) => {}
                        None => {
                            owners.insert(target, instance.clone());
                            pending.push_back((target, instance.clone()));
                        }
                    }
                }
            }
        }
        Ok(owners)
    }
}

/// An instance key is admitted only after every generic argument is concrete.
/// Its executable body therefore has no binder namespace in which a source
/// generic placeholder could be interpreted. Check all frozen type witnesses,
/// not only local registers: aggregate layouts, patterns, handler frames,
/// host ABI records, and capture environments are independently consumed by
/// MIR/VM verification. Elided regions are local borrow witnesses whose
/// identity is intentionally erased by the VM, so they are not placeholders
/// requiring instance substitution.
fn materialized_instance_retains_generic_placeholder(function: &MirFunction) -> bool {
    type_retains_generic_placeholder(&function.result)
        || function
            .locals
            .iter()
            .any(|local| type_retains_generic_placeholder(&local.ty))
        || function
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .any(instruction_retains_generic_placeholder)
}

fn type_retains_generic_placeholder(value: &Type) -> bool {
    match value {
        Type::FixedArray { element, length } => type_retains_generic_placeholder(element)
            || generic_argument_retains_generic_placeholder(length),
        Type::Generic(_) | Type::ConstGeneric { .. } | Type::Infer(_) | Type::Error => true,
        Type::Nominal { arguments, .. } => arguments
            .iter()
            .any(generic_argument_retains_generic_placeholder),
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            type_retains_generic_placeholder(subject)
                || trait_arguments
                    .iter()
                    .any(generic_argument_retains_generic_placeholder)
                || item_arguments
                    .iter()
                    .any(generic_argument_retains_generic_placeholder)
        }
        Type::Tuple(values) => values.iter().any(type_retains_generic_placeholder),
        Type::Array(value) | Type::StaticData { element: value, .. }
        | Type::RawPointer { pointee: value, .. } => {
            type_retains_generic_placeholder(value)
        }
        Type::Reference {
            lifetime, referent, ..
        } => {
            matches!(lifetime, crate::Lifetime::Generic(_) | crate::Lifetime::Infer(_) | crate::Lifetime::Placeholder(_))
                || type_retains_generic_placeholder(referent)
        }
        Type::Callable {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters.iter().any(type_retains_generic_placeholder)
                || type_retains_generic_placeholder(result)
                || effect_row_retains_generic_placeholder(effects)
        }
        Type::Unit | Type::Never | Type::Scalar(_) | Type::ConstInteger(_) | Type::ConstQuantity(_) => {
            false
        }
    }
}

fn generic_argument_retains_generic_placeholder(value: &GenericArgument) -> bool {
    match value {
        GenericArgument::Type(value) => type_retains_generic_placeholder(value),
        GenericArgument::EffectRow(value) => effect_row_retains_generic_placeholder(value),
        GenericArgument::Lifetime(crate::Lifetime::Generic(_) | crate::Lifetime::Infer(_) | crate::Lifetime::Placeholder(_))
        | GenericArgument::ConstIntegerExpr(_)
        | GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstProjection { .. }
        | GenericArgument::ConstInfer { .. } => true,
        GenericArgument::Lifetime(
            crate::Lifetime::Static | crate::Lifetime::Elided | crate::Lifetime::Bound { .. } | crate::Lifetime::Inferred(_),
        )
        | GenericArgument::ConstInteger(_)
        | GenericArgument::ConstQuantity(_) => false,
    }
}

fn effect_row_retains_generic_placeholder(value: &crate::EffectRow) -> bool {
    !value.tails.is_empty() || value.effects.iter().any(|effect| {
        effect
            .arguments
            .iter()
            .any(generic_argument_retains_generic_placeholder)
    }) || value.projections.iter().any(|projection| {
        type_retains_generic_placeholder(&projection.subject)
            || projection
                .trait_arguments
                .iter()
                .any(generic_argument_retains_generic_placeholder)
            || projection
                .item_arguments
                .iter()
                .any(generic_argument_retains_generic_placeholder)
    })
}

fn instruction_retains_generic_placeholder(instruction: &MirInstruction) -> bool {
    match instruction {
        MirInstruction::MemoryIntrinsic { types, .. } => types.iter().any(type_retains_generic_placeholder),
        MirInstruction::MakeArray { element_type, .. }
        | MirInstruction::ProjectArray { element_type, .. }
        | MirInstruction::ArrayGetBorrowShared { element_type, .. }
        | MirInstruction::ArrayEmpty { element_type, .. }
        | MirInstruction::ArrayPushMove { element_type, .. } => {
            type_retains_generic_placeholder(element_type)
        }
        MirInstruction::MakeRecord { field_types, .. }
        | MirInstruction::MakeEnum { field_types, .. } => {
            field_types.iter().any(type_retains_generic_placeholder)
        }
        MirInstruction::ProjectRecord { field_type, .. }
        | MirInstruction::ProjectTuple { field_type, .. }
        | MirInstruction::UpdateRecord { field_type, .. } => {
            type_retains_generic_placeholder(field_type)
        }
        MirInstruction::PatternTest { pattern, .. } => pattern_retains_generic_placeholder(pattern),
        MirInstruction::Perform {
            effect_arguments, ..
        } => effect_arguments
            .iter()
            .any(generic_argument_retains_generic_placeholder),
        MirInstruction::InstallHandler {
            effect_arguments,
            resume_type,
            ..
        } => {
            type_retains_generic_placeholder(resume_type)
                || effect_arguments
                    .iter()
                    .any(generic_argument_retains_generic_placeholder)
        }
        MirInstruction::Call {
            generic_arguments,
            trait_instance,
            ..
        }
        | MirInstruction::MakeCallable {
            generic_arguments,
            trait_instance,
            ..
        } => {
            !generic_arguments.is_empty()
                || trait_instance.is_some()
                || matches!(instruction, MirInstruction::MakeCallable { environment: Some(environment), .. } if environment.captures.iter().any(|capture| type_retains_generic_placeholder(&capture.ty)))
        }
        MirInstruction::HostCallOwned { parameters, result, .. }
        | MirInstruction::HostCall {
            parameters, result, ..
        } => {
            parameters.iter().any(type_retains_generic_placeholder)
                || type_retains_generic_placeholder(result)
        }
        _ => false,
    }
}

fn pattern_retains_generic_placeholder(pattern: &MirPattern) -> bool {
    match pattern {
        MirPattern::Any | MirPattern::Literal(_) => false,
        MirPattern::Tuple(patterns) => patterns.iter().any(pattern_retains_generic_placeholder),
        MirPattern::Array { element, elements, .. } => {
            type_retains_generic_placeholder(element)
                || elements.iter().any(pattern_retains_generic_placeholder)
        }
        MirPattern::Record {
            field_types,
            fields,
            ..
        }
        | MirPattern::Enum {
            field_types,
            fields,
            ..
        } => {
            field_types.iter().any(type_retains_generic_placeholder)
                || fields.iter().any(|field| {
                    type_retains_generic_placeholder(&field.ty)
                        || pattern_retains_generic_placeholder(&field.pattern)
                })
        }
    }
}
fn references(value: &MirInstruction) -> Vec<MirLocal> {
    match value {
        MirInstruction::ConstUnit { dst }
        | MirInstruction::ConstI64 { dst, .. }
        | MirInstruction::ConstU8 { dst, .. }
        | MirInstruction::ConstU16 { dst, .. }
        | MirInstruction::ConstU32 { dst, .. }
        | MirInstruction::ConstU64 { dst, .. }
        | MirInstruction::ConstUsize { dst, .. }
        | MirInstruction::ConstU128 { dst, .. }
        | MirInstruction::ConstI8 { dst, .. }
        | MirInstruction::ConstI16 { dst, .. }
        | MirInstruction::ConstI32 { dst, .. }
        | MirInstruction::ConstIsize { dst, .. }
        | MirInstruction::ConstI128 { dst, .. }
        | MirInstruction::ConstF32 { dst, .. }
        | MirInstruction::ConstF64 { dst, .. }
        | MirInstruction::DeferredLiteral { dst, .. }
        | MirInstruction::ConstBool { dst, .. }
        | MirInstruction::ConstChar { dst, .. }
        | MirInstruction::ConstText { dst, .. }
        | MirInstruction::ConstStaticData { dst, .. } => vec![*dst],
        MirInstruction::FloatIntrinsic { dst, arguments, .. }
        | MirInstruction::MemoryIntrinsic { dst, arguments, .. }
        | MirInstruction::IntIntrinsic { dst, arguments, .. }
        | MirInstruction::IntGenericIntrinsic { dst, arguments, .. } => std::iter::once(*dst)
            .chain(arguments.iter().copied())
            .collect(),
        MirInstruction::StoreUsize { dst, value }
        | MirInstruction::ArrayLen { dst, value } => vec![*dst, *value],
        MirInstruction::ArrayElementIsInitialized { dst, value, index }
        | MirInstruction::TakeArrayElement { dst, value, index } => vec![*dst, *value, *index],
        MirInstruction::TextByteLen { dst, value } => vec![*dst, *value],
        MirInstruction::StaticLen { dst, value } => vec![*dst, *value],
        MirInstruction::TextConcat { dst, left, right }
        | MirInstruction::TextEq { dst, left, right } => vec![*dst, *left, *right],
        MirInstruction::TextFromUtf8Checked { dst, value }
        | MirInstruction::TextAsBytes { dst, value } => vec![*dst, *value],
        MirInstruction::CharFromU32Checked { dst, value }
        | MirInstruction::CharToU32 { dst, value } => vec![*dst, *value],
        MirInstruction::BytesLen { dst, value }
        | MirInstruction::BytesFromArrayMove { dst, value }
        | MirInstruction::BytesToArray { dst, value }
        | MirInstruction::BytesUtf8ValidUpTo { dst, value }
        | MirInstruction::Blake3 { dst, value } => vec![*dst, *value],
        MirInstruction::BytesConcat { dst, left, right } => vec![*dst, *left, *right],
        MirInstruction::BytesGet { dst, bytes, index } => vec![*dst, *bytes, *index],
        MirInstruction::BytesSlice {
            dst,
            bytes,
            start,
            end,
        } => vec![*dst, *bytes, *start, *end],
        MirInstruction::ArrayGetBorrowShared {
            dst, value, index, ..
        } => vec![*dst, *value, *index],
        MirInstruction::ArrayEmpty { dst, .. } => vec![*dst],
        MirInstruction::ArrayPushMove { value, item, .. } => vec![*value, *item],
        MirInstruction::U32CheckedAdd { dst, left, right }
        | MirInstruction::U32CheckedSub { dst, left, right }
        | MirInstruction::U32CheckedMul { dst, left, right }
        | MirInstruction::U32CheckedDiv { dst, left, right }
        | MirInstruction::U32CheckedRem { dst, left, right }
        | MirInstruction::U32WrappingAdd { dst, left, right }
        | MirInstruction::U32WrappingSub { dst, left, right }
        | MirInstruction::U32WrappingMul { dst, left, right }
        | MirInstruction::U32WrappingShl { dst, left, right }
        | MirInstruction::U32WrappingShr { dst, left, right }
        | MirInstruction::U32CheckedShl { dst, left, right }
        | MirInstruction::U32CheckedShr { dst, left, right }
        | MirInstruction::U32Eq { dst, left, right }
        | MirInstruction::U32Lt { dst, left, right }
        | MirInstruction::U32Le { dst, left, right } => vec![*dst, *left, *right],
        MirInstruction::U32ToUsize { dst, value }
        | MirInstruction::UsizeToU32Checked { dst, value }
        | MirInstruction::I64ToU32Checked { dst, value }
        | MirInstruction::I64ToU32Wrapping { dst, value }
        | MirInstruction::I64ToUsizeChecked { dst, value }
        | MirInstruction::I64ToUsizeWrapping { dst, value }
        | MirInstruction::I64ToU8Checked { dst, value }
        | MirInstruction::I64ToU8Wrapping { dst, value }
        | MirInstruction::I64ToU16Checked { dst, value }
        | MirInstruction::I64ToU16Wrapping { dst, value }
        | MirInstruction::I64ToI16Checked { dst, value }
        | MirInstruction::I64ToI16Wrapping { dst, value }
        | MirInstruction::I64ToI32Checked { dst, value }
        | MirInstruction::I64ToI32Wrapping { dst, value } => vec![*dst, *value],
        MirInstruction::I64ToI8Checked { dst, value }
        | MirInstruction::I64ToI8Wrapping { dst, value }
        | MirInstruction::I64ToU64Checked { dst, value }
        | MirInstruction::I64ToU64Wrapping { dst, value }
        | MirInstruction::I64ToIsizeChecked { dst, value }
        | MirInstruction::I64ToIsizeWrapping { dst, value }
        | MirInstruction::I64ToU128Checked { dst, value }
        | MirInstruction::I64ToU128Wrapping { dst, value }
        | MirInstruction::I64ToI128Checked { dst, value }
        | MirInstruction::I64ToI128Wrapping { dst, value } => vec![*dst, *value],
        MirInstruction::DestroyCallable { dst, value } => vec![*dst, *value],
        MirInstruction::MakeTuple { dst, fields }
        | MirInstruction::MakeArray { dst, fields, .. } => std::iter::once(*dst)
            .chain(fields.iter().copied())
            .collect(),
        MirInstruction::MakeRecord { dst, fields, .. } => std::iter::once(*dst)
            .chain(fields.iter().copied())
            .collect(),
        MirInstruction::MakeEnum { dst, fields, .. } => std::iter::once(*dst)
            .chain(fields.iter().copied())
            .collect(),
        MirInstruction::ProjectRecord { dst, base, .. }
        | MirInstruction::TakeProjection { dst, base, .. }
        | MirInstruction::IsInitialized { dst, base, .. }
        | MirInstruction::ProjectTuple { dst, base, .. }
        | MirInstruction::ProjectArray { dst, base, .. } => vec![*dst, *base],
        MirInstruction::UpdateRecord {
            dst, base, value, ..
        } => vec![*dst, *base, *value],
        MirInstruction::PatternTest { dst, subject, .. } => vec![*dst, *subject],
        MirInstruction::Perform { dst, arguments, .. } => std::iter::once(*dst)
            .chain(arguments.iter().copied())
            .collect(),
        MirInstruction::InstallHandler {
            payload_destinations,
            ..
        } => payload_destinations.clone(),
        MirInstruction::Abort => Vec::new(),
        MirInstruction::ClaimEffectPayloads { payloads } => payloads.clone(),
        MirInstruction::UninstallHandler => Vec::new(),
        MirInstruction::CaptureResumption { dst, .. } => vec![*dst],
        MirInstruction::Resume { value, .. }
        | MirInstruction::CompleteHandler { value } => vec![*value],
        MirInstruction::ResumeReturn { dst, value, .. } => vec![*dst, *value],
        MirInstruction::ResumeSnapshot {
            snapshot, value, ..
        } => vec![*snapshot, *value],
        MirInstruction::Forward { .. } => Vec::new(),
        MirInstruction::Cancel { .. } => Vec::new(),
        MirInstruction::StorageLive { local, .. } | MirInstruction::StorageDead { local, .. } => {
            vec![*local]
        }
        MirInstruction::SetDropFlag { flag, .. } => vec![*flag],
        MirInstruction::DestroyIf { local, flag } => vec![*local, *flag],
        MirInstruction::Drop { local } => vec![*local],
        MirInstruction::Copy { dst, src }
        | MirInstruction::Store { dst, src }
        | MirInstruction::Move { dst, src } => vec![*dst, *src],
        MirInstruction::Borrow { dst, src, .. } => vec![*dst, *src],
        MirInstruction::DerefCopy { dst, reference }
        | MirInstruction::DerefIsInitialized { dst, reference }
        | MirInstruction::DerefMove { dst, reference } => vec![*dst, *reference],
        MirInstruction::DerefStore { reference, src } => vec![*reference, *src],
        MirInstruction::NotBool { dst, value } => vec![*dst, *value],
        MirInstruction::BitNotI64 { dst, value } => vec![*dst, *value],
        MirInstruction::ShlI64 { dst, value, count } => vec![*dst, *value, *count],
        MirInstruction::AddI64 { dst, left, right }
        | MirInstruction::WrappingAddI64 { dst, left, right }
        | MirInstruction::WrappingSubI64 { dst, left, right }
        | MirInstruction::WrappingMulI64 { dst, left, right }
        | MirInstruction::IntEqualI64 { dst, left, right }
        | MirInstruction::IntLessI64 { dst, left, right }
        | MirInstruction::IntGreaterI64 { dst, left, right }
        | MirInstruction::BitAndI64 { dst, left, right }
        | MirInstruction::BitAndU32 { dst, left, right }
        | MirInstruction::BitAndU64 { dst, left, right }
        | MirInstruction::BitAndGeneric { dst, left, right }
        | MirInstruction::BitXorI64 { dst, left, right }
        | MirInstruction::IntShrI64 { dst, left, right }
        | MirInstruction::BitOrI64 { dst, left, right }
        | MirInstruction::SubI64 { dst, left, right }
        | MirInstruction::MulI64 { dst, left, right }
        | MirInstruction::DivI64 { dst, left, right }
        | MirInstruction::RemI64 { dst, left, right }
        | MirInstruction::AddF64 { dst, left, right }
        | MirInstruction::ConcatText { dst, left, right }
        | MirInstruction::SubF64 { dst, left, right }
        | MirInstruction::MulF64 { dst, left, right }
        | MirInstruction::DivF64 { dst, left, right }
        | MirInstruction::RemF64 { dst, left, right }
        | MirInstruction::EqI64 { dst, left, right }
        | MirInstruction::NeI64 { dst, left, right }
        | MirInstruction::NeU32 { dst, left, right }
        | MirInstruction::NeU64 { dst, left, right }
        | MirInstruction::LtI64 { dst, left, right }
        | MirInstruction::LeI64 { dst, left, right }
        | MirInstruction::GtI64 { dst, left, right }
        | MirInstruction::GeI64 { dst, left, right }
        | MirInstruction::EqF64 { dst, left, right }
        | MirInstruction::NeF64 { dst, left, right }
        | MirInstruction::LtF64 { dst, left, right }
        | MirInstruction::LeF64 { dst, left, right }
        | MirInstruction::GtF64 { dst, left, right }
        | MirInstruction::GeF64 { dst, left, right }
        | MirInstruction::EqBool { dst, left, right }
        | MirInstruction::NeBool { dst, left, right }
        | MirInstruction::EqText { dst, left, right }
        | MirInstruction::NeText { dst, left, right }
        | MirInstruction::EqChar { dst, left, right }
        | MirInstruction::NeChar { dst, left, right }
        | MirInstruction::LtChar { dst, left, right }
        | MirInstruction::LeChar { dst, left, right }
        | MirInstruction::GtChar { dst, left, right }
        | MirInstruction::GeChar { dst, left, right } => vec![*dst, *left, *right],
        MirInstruction::CallOwned { dst, arguments, .. }
        | MirInstruction::HostCallOwned { dst, arguments, .. }
        | MirInstruction::Call { dst, arguments, .. } => std::iter::once(*dst)
            .chain(arguments.iter().copied())
            .collect(),
        MirInstruction::HostCall { dst, arguments, .. } => std::iter::once(*dst)
            .chain(arguments.iter().copied())
            .collect(),
        MirInstruction::MakeCallable { dst, captures, .. } => std::iter::once(*dst)
            .chain(captures.iter().copied())
            .collect(),
        MirInstruction::MakeLabel {
            dst, destination, ..
        } => vec![*dst, *destination],
        MirInstruction::CallIndirectOwned { dst, callee, arguments }
        | MirInstruction::CallIndirect {
            dst,
            callee,
            arguments,
        } => std::iter::once(*dst)
            .chain(std::iter::once(*callee))
            .chain(arguments.iter().copied())
            .collect(),
    }
}

pub(crate) fn lower_pattern(value: CorePattern) -> Option<MirPattern> {
    match value {
        CorePattern::Any | CorePattern::Bind { .. } => Some(MirPattern::Any),
        CorePattern::Literal(value) => Some(MirPattern::Literal(value)),
        CorePattern::Tuple(values) => values
            .into_iter()
            .map(lower_pattern)
            .collect::<Option<Vec<_>>>()
            .map(MirPattern::Tuple),
        CorePattern::Array { element, elements, rest } => elements
            .into_iter()
            .map(lower_pattern)
            .collect::<Option<Vec<_>>>()
            .map(|elements| MirPattern::Array { element, elements, rest }),
        CorePattern::Record {
            definition,
            field_types,
            field_count,
            fields,
        } => fields
            .into_iter()
            .map(|field| {
                Some(MirPatternField {
                    index: field.index,
                    ty: field.ty,
                    pattern: lower_pattern(field.pattern)?,
                })
            })
            .collect::<Option<Vec<_>>>()
            .map(|fields| MirPattern::Record {
                definition,
                field_types,
                field_count,
                fields,
            }),
        CorePattern::Enum {
            definition,
            variant,
            field_types,
            field_count,
            fields,
            ..
        } => fields
            .into_iter()
            .map(|field| {
                Some(MirPatternField {
                    index: field.index,
                    ty: field.ty,
                    pattern: lower_pattern(field.pattern)?,
                })
            })
            .collect::<Option<Vec<_>>>()
            .map(|fields| MirPattern::Enum {
                definition,
                variant,
                field_types,
                field_count,
                fields,
            }),
        CorePattern::Error => None,
    }
}

pub(crate) fn validate_pattern(pattern: &MirPattern, subject: &Type) -> Result<(), String> {
    if !matches!(pattern, MirPattern::Any) && let Type::Reference { referent, .. } = subject {
        return validate_pattern(pattern, referent);
    }
    match pattern {
        MirPattern::Any => Ok(()),
        MirPattern::Literal(value)
            if literal_type(value).as_ref() == Some(subject)
                || numeric_literal_matches_subject(value, subject) =>
        {
            Ok(())
        }
        MirPattern::Literal(_) => {
            Err("MIR literal pattern has an incompatible subject type".into())
        }
        MirPattern::Tuple(patterns) => match subject {
            Type::Tuple(types) if patterns.len() == types.len() => patterns
                .iter()
                .zip(types)
                .try_for_each(|(pattern, ty)| validate_pattern(pattern, ty)),
            _ => Err("MIR tuple pattern has an incompatible subject type".into()),
        },
        MirPattern::Array { element, elements, rest } => match subject {
            actual if actual.array_element() == Some(element) && actual.array_accepts_pattern(elements.len(), *rest) => elements
                .iter()
                .try_for_each(|pattern| validate_pattern(pattern, element)),
            _ => Err("MIR array pattern has an incompatible subject type".into()),
        },
        MirPattern::Record {
            definition,
            field_types,
            field_count,
            fields,
        } => match subject {
            Type::Nominal {
                definition: actual, ..
            } if actual == definition => validate_pattern_fields(fields, field_types, *field_count),
            _ => Err("MIR record pattern has an incompatible subject type".into()),
        },
        MirPattern::Enum {
            definition,
            field_types,
            field_count,
            fields,
            ..
        } => match subject {
            Type::Nominal {
                definition: actual, ..
            } if actual == definition => validate_pattern_fields(fields, field_types, *field_count),
            _ => Err("MIR enum pattern has an incompatible subject type".into()),
        },
    }
}

// An unsuffixed source integer is initially represented as i64. Pattern
// payloads are contextually typed, so accept an integer spelling that fits
// the payload scalar instead of rejecting `Variant(1)` for an unsigned or
// wider integer field.
fn numeric_literal_matches_subject(text: &str, subject: &Type) -> bool {
    use crate::types::ScalarType;

    let Type::Scalar(scalar) = subject else {
        return false;
    };
    match scalar {
        ScalarType::U8 => parse_u8_literal(text).is_ok(),
        ScalarType::U16 => parse_u16_literal(text).is_ok(),
        ScalarType::U32 => parse_u32_literal(text).is_ok(),
        ScalarType::U64 | ScalarType::Usize => parse_u64_literal(text).is_ok(),
        ScalarType::U128 => parse_u128_literal(text).is_ok(),
        ScalarType::I8 => parse_i8_literal(text).is_ok(),
        ScalarType::I16 => parse_i16_literal(text).is_ok(),
        ScalarType::I32 => parse_i32_literal(text).is_ok(),
        ScalarType::I64 | ScalarType::Isize => parse_i64_literal(text).is_ok(),
        ScalarType::I128 => parse_i128_literal(text).is_ok(),
        ScalarType::F32 => matches!(crate::source::exact_scalar_literal_kind(text), Some(crate::TokenKind::Integer | crate::TokenKind::Float))
            && parse_f32_literal(text).is_ok(),
        ScalarType::F64 => matches!(crate::source::exact_scalar_literal_kind(text), Some(crate::TokenKind::Integer | crate::TokenKind::Float))
            && parse_f64_literal(text).is_ok(),
        _ => false,
    }
}

fn validate_pattern_fields(
    fields: &[MirPatternField],
    field_types: &[Type],
    field_count: u32,
) -> Result<(), String> {
    if field_types.len() != field_count as usize {
        return Err("MIR pattern layout length disagrees with its frozen arity".into());
    }
    let mut previous = None;
    for field in fields {
        if previous.is_some_and(|previous| previous >= field.index) {
            return Err("MIR pattern fields are not strictly ordered".into());
        }
        if field.index >= field_count {
            return Err("MIR pattern field is outside its structural arity".into());
        }
        if field.ty != field_types[field.index as usize] {
            return Err("MIR pattern field type disagrees with its frozen layout".into());
        }
        previous = Some(field.index);
        validate_pattern(&field.pattern, &field.ty)?;
    }
    Ok(())
}

fn literal_type(text: &str) -> Option<Type> {
    use crate::source::{TokenKind, exact_scalar_literal_kind};

    if matches!(text, "true" | "false") {
        return Some(Type::Scalar(crate::types::ScalarType::Bool));
    }
    match exact_scalar_literal_kind(text)? {
        TokenKind::Integer if parse_i64_literal(text).is_ok() => {
            Some(Type::Scalar(crate::types::ScalarType::I64))
        }
        TokenKind::Float if parse_f64_literal(text).is_ok() => {
            Some(Type::Scalar(crate::types::ScalarType::F64))
        }
        TokenKind::Character if parse_char_literal(text).is_ok() => {
            Some(Type::Scalar(crate::types::ScalarType::Char))
        }
        TokenKind::String if parse_text_literal(text).is_ok() => {
            Some(Type::Scalar(crate::types::ScalarType::Text))
        }
        TokenKind::ByteString if parse_byte_literal(text).is_ok() => {
            Some(Type::Scalar(crate::types::ScalarType::Bytes))
        }
        _ => None,
    }
}

/// Lexing has already validated integer structure.  MIR still performs a
/// checked conversion so an out-of-range source value cannot wrap while it is
/// becoming the stage-zero VM's i64 representation.
/// Resolve a generic numeric source literal after enclosing-instance
/// specialization has fixed its scalar representation.
pub(crate) fn materialize_numeric_literal(
    dst: MirLocal,
    text: &str,
    scalar: crate::ScalarType,
) -> Result<MirInstruction, String> {
    use crate::ScalarType;
    let invalid = || format!("invalid {scalar:?} literal during instance materialization");
    match scalar {
        ScalarType::I64 => parse_i64_literal(text)
            .map(|value| MirInstruction::ConstI64 { dst, value })
            .map_err(|_| invalid()),
        ScalarType::U8 => parse_u8_literal(text)
            .map(|value| MirInstruction::ConstU8 { dst, value })
            .map_err(|_| invalid()),
        ScalarType::U16 => parse_u16_literal(text)
            .map(|value| MirInstruction::ConstU16 { dst, value })
            .map_err(|_| invalid()),
        ScalarType::U32 => parse_u32_literal(text)
            .map(|value| MirInstruction::ConstU32 { dst, value })
            .map_err(|_| invalid()),
        ScalarType::U64 => parse_u64_literal(text)
            .map(|value| MirInstruction::ConstU64 { dst, value })
            .map_err(|_| invalid()),
        ScalarType::Usize => parse_u64_literal(text)
            .map(|value| MirInstruction::ConstUsize { dst, value })
            .map_err(|_| invalid()),
        ScalarType::U128 => parse_u128_literal(text)
            .map(|value| MirInstruction::ConstU128 { dst, value })
            .map_err(|_| invalid()),
        ScalarType::I8 => parse_i8_literal(text)
            .map(|value| MirInstruction::ConstI8 { dst, value })
            .map_err(|_| invalid()),
        ScalarType::I16 => parse_i16_literal(text)
            .map(|value| MirInstruction::ConstI16 { dst, value })
            .map_err(|_| invalid()),
        ScalarType::I32 => parse_i32_literal(text)
            .map(|value| MirInstruction::ConstI32 { dst, value })
            .map_err(|_| invalid()),
        ScalarType::Isize => parse_i64_literal(text)
            .map(|value| MirInstruction::ConstIsize { dst, value })
            .map_err(|_| invalid()),
        ScalarType::I128 => parse_i128_literal(text)
            .map(|value| MirInstruction::ConstI128 { dst, value })
            .map_err(|_| invalid()),
        ScalarType::F64 => parse_f64_literal(text)
            .map(|value| MirInstruction::ConstF64 {
                dst,
                bits: canonical_f64_bits(value.to_bits()),
            })
            .map_err(|_| invalid()),
        ScalarType::F32 => parse_f32_literal(text)
            .map(|value| MirInstruction::ConstF32 {
                dst,
                bits: canonical_f32_bits(value.to_bits()),
            })
            .map_err(|_| invalid()),
        ScalarType::Bool | ScalarType::Char | ScalarType::Text | ScalarType::Bytes => {
            Err(format!("generic numeric literal cannot specialize to {scalar:?}"))
        }
    }
}

fn parse_i64_literal(text: &str) -> Result<i64, ()> {
    normalized_integer_literal(text, crate::ScalarType::I64)?.parse().map_err(|_| ())
}

fn parse_u32_literal(text: &str) -> Result<u32, ()> {
    normalized_integer_literal(text, crate::ScalarType::U32)?.parse().map_err(|_| ())
}

fn parse_u8_literal(text: &str) -> Result<u8, ()> {
    normalized_integer_literal(text, crate::ScalarType::U8)?.parse().map_err(|_| ())
}

fn parse_u16_literal(text: &str) -> Result<u16, ()> {
    normalized_integer_literal(text, crate::ScalarType::U16)?.parse().map_err(|_| ())
}

fn parse_u64_literal(text: &str) -> Result<u64, ()> {
    normalized_integer_literal(text, crate::ScalarType::U64)?.parse().map_err(|_| ())
}

fn parse_u128_literal(text: &str) -> Result<u128, ()> {
    normalized_integer_literal(text, crate::ScalarType::U128)?.parse().map_err(|_| ())
}

fn parse_i8_literal(text: &str) -> Result<i8, ()> {
    normalized_integer_literal(text, crate::ScalarType::I8)?.parse().map_err(|_| ())
}

fn parse_i16_literal(text: &str) -> Result<i16, ()> {
    normalized_integer_literal(text, crate::ScalarType::I16)?.parse().map_err(|_| ())
}

fn parse_i32_literal(text: &str) -> Result<i32, ()> {
    normalized_integer_literal(text, crate::ScalarType::I32)?.parse().map_err(|_| ())
}

fn parse_i128_literal(text: &str) -> Result<i128, ()> {
    normalized_integer_literal(text, crate::ScalarType::I128)?.parse().map_err(|_| ())
}

fn integer_scalar_type(ty: &Type) -> Option<crate::types::ScalarType> {
    let Type::Scalar(scalar) = ty else {
        return None;
    };
    matches!(
        scalar,
        crate::types::ScalarType::U8
            | crate::types::ScalarType::U16
            | crate::types::ScalarType::U32
            | crate::types::ScalarType::U64
            | crate::types::ScalarType::U128
            | crate::types::ScalarType::Usize
            | crate::types::ScalarType::I8
            | crate::types::ScalarType::I16
            | crate::types::ScalarType::I32
            | crate::types::ScalarType::I64
            | crate::types::ScalarType::I128
            | crate::types::ScalarType::Isize
    )
    .then_some(*scalar)
}

fn is_generic_integer_runtime_role(role: PrimitiveRole) -> bool {
    matches!(
        role,
        PrimitiveRole::IntCheckedAdd
            | PrimitiveRole::IntCheckedDiv
            | PrimitiveRole::IntWrappingAdd
            | PrimitiveRole::IntWrappingSub
            | PrimitiveRole::IntWrappingMul
            | PrimitiveRole::IntEqual
            | PrimitiveRole::IntLess
            | PrimitiveRole::IntGreater
            | PrimitiveRole::IntBitAnd
            | PrimitiveRole::IntBitOr
            | PrimitiveRole::IntBitXor
            | PrimitiveRole::IntBitNot
            | PrimitiveRole::IntWrappingNeg
            | PrimitiveRole::IntShl
            | PrimitiveRole::IntShr
            | PrimitiveRole::IntConvertCheckedToI64
            | PrimitiveRole::IntConvertWrappingToI64
            | PrimitiveRole::IntConvertCheckedToU32
            | PrimitiveRole::IntConvertWrappingToU32
            | PrimitiveRole::IntConvertCheckedToUsize
            | PrimitiveRole::IntConvertWrappingToUsize
            | PrimitiveRole::IntConvertCheckedToU8
            | PrimitiveRole::IntConvertWrappingToU8
            | PrimitiveRole::IntConvertCheckedToU16
            | PrimitiveRole::IntConvertWrappingToU16
            | PrimitiveRole::IntConvertCheckedToI16
            | PrimitiveRole::IntConvertWrappingToI16
            | PrimitiveRole::IntConvertCheckedToI32
            | PrimitiveRole::IntConvertWrappingToI32
            | PrimitiveRole::IntConvertCheckedToI8
            | PrimitiveRole::IntConvertWrappingToI8
            | PrimitiveRole::IntConvertCheckedToU64
            | PrimitiveRole::IntConvertWrappingToU64
            | PrimitiveRole::IntConvertCheckedToIsize
            | PrimitiveRole::IntConvertWrappingToIsize
            | PrimitiveRole::IntConvertCheckedToU128
            | PrimitiveRole::IntConvertWrappingToU128
            | PrimitiveRole::IntConvertCheckedToI128
            | PrimitiveRole::IntConvertWrappingToI128
    )
}

fn generic_integer_runtime_result(role: PrimitiveRole, source: Type) -> Option<Type> {
    use crate::types::ScalarType;
    Some(match role {
        PrimitiveRole::IntEqual | PrimitiveRole::IntLess | PrimitiveRole::IntGreater => {
            Type::Scalar(ScalarType::U32)
        }
        PrimitiveRole::IntConvertCheckedToI64 | PrimitiveRole::IntConvertWrappingToI64 => {
            Type::Scalar(ScalarType::I64)
        }
        PrimitiveRole::IntConvertCheckedToU32 | PrimitiveRole::IntConvertWrappingToU32 => {
            Type::Scalar(ScalarType::U32)
        }
        PrimitiveRole::IntConvertCheckedToUsize | PrimitiveRole::IntConvertWrappingToUsize => {
            Type::Scalar(ScalarType::Usize)
        }
        PrimitiveRole::IntConvertCheckedToU8 | PrimitiveRole::IntConvertWrappingToU8 => {
            Type::Scalar(ScalarType::U8)
        }
        PrimitiveRole::IntConvertCheckedToU16 | PrimitiveRole::IntConvertWrappingToU16 => {
            Type::Scalar(ScalarType::U16)
        }
        PrimitiveRole::IntConvertCheckedToI16 | PrimitiveRole::IntConvertWrappingToI16 => {
            Type::Scalar(ScalarType::I16)
        }
        PrimitiveRole::IntConvertCheckedToI32 | PrimitiveRole::IntConvertWrappingToI32 => {
            Type::Scalar(ScalarType::I32)
        }
        PrimitiveRole::IntConvertCheckedToI8 | PrimitiveRole::IntConvertWrappingToI8 => {
            Type::Scalar(ScalarType::I8)
        }
        PrimitiveRole::IntConvertCheckedToU64 | PrimitiveRole::IntConvertWrappingToU64 => {
            Type::Scalar(ScalarType::U64)
        }
        PrimitiveRole::IntConvertCheckedToIsize | PrimitiveRole::IntConvertWrappingToIsize => {
            Type::Scalar(ScalarType::Isize)
        }
        PrimitiveRole::IntConvertCheckedToU128 | PrimitiveRole::IntConvertWrappingToU128 => {
            Type::Scalar(ScalarType::U128)
        }
        PrimitiveRole::IntConvertCheckedToI128 | PrimitiveRole::IntConvertWrappingToI128 => {
            Type::Scalar(ScalarType::I128)
        }
        _ if is_generic_integer_runtime_role(role) => source,
        _ => return None,
    })
}

pub(crate) fn normalized_integer_literal(text: &str, scalar: crate::ScalarType) -> Result<String, ()> {
    let (negative, token) = text.strip_prefix('-').map_or((false, text), |token| (true, token));
    crate::IntegerConst::from_literal(scalar, token, negative, 64)
        .map(|value| value.to_string()).map_err(|_| ())
}

pub(crate) fn parse_f64_literal(text: &str) -> Result<f64, ()> {
    let value = text.replace('_', "").parse::<f64>().map_err(|_| ())?;
    // Source has no spelling for `inf` or `NaN`.  A finite decimal that
    // overflows while becoming an f64 is therefore a rejected literal rather
    // than an accidental alternate spelling for infinity.  IEEE infinities
    // and NaNs remain valid *runtime results* of float arithmetic.
    value.is_finite().then_some(value).ok_or(())
}

pub(crate) fn parse_f32_literal(text: &str) -> Result<f32, ()> {
    let value = text.replace('_', "").parse::<f32>().map_err(|_| ())?;
    value.is_finite().then_some(value).ok_or(())
}

/// Source lexing validates literal escape structure. MIR decodes it again so
/// the emitted artifact contains a scalar value rather than source spelling.
pub(crate) fn parse_char_literal(text: &str) -> Result<u32, ()> {
    let Some(body) = text
        .strip_prefix('\'')
        .and_then(|value| value.strip_suffix('\''))
    else {
        return Err(());
    };
    let mut values = body.chars();
    let value = match values.next() {
        Some('\\') => parse_scalar_escape(&mut values)?,
        Some(value) if value != '\n' => value,
        None => return Err(()),
        Some(_) => return Err(()),
    };
    if values.next().is_some() {
        return Err(());
    }
    Ok(value as u32)
}

pub(crate) fn parse_text_literal(text: &str) -> Result<String, ()> {
    let Some(body) = text
        .strip_prefix('"')
        .and_then(|value| value.strip_suffix('"'))
    else {
        return Err(());
    };
    let mut values = body.chars();
    let mut result = String::new();
    while let Some(value) = values.next() {
        let value = if value == '\\' {
            parse_scalar_escape(&mut values)?
        } else if value == '\n' {
            return Err(());
        } else {
            value
        };
        result.push(value);
    }
    Ok(result)
}

/// Decode a `b"..."` literal exactly as accepted by the lexer. Direct source
/// characters and Unicode escapes contribute their UTF-8 encoding; `\\xNN`
/// contributes one raw octet and may therefore produce non-UTF-8 data.
pub(crate) fn parse_byte_literal(text: &str) -> Result<Vec<u8>, ()> {
    let Some(body) = text
        .strip_prefix("b\"")
        .and_then(|value| value.strip_suffix('"'))
    else {
        return Err(());
    };
    let mut values = body.chars();
    let mut result = Vec::new();
    while let Some(value) = values.next() {
        if value == '\n' {
            return Err(());
        }
        if value != '\\' {
            let mut encoded = [0; 4];
            result.extend_from_slice(value.encode_utf8(&mut encoded).as_bytes());
            continue;
        }
        match values.next() {
            Some('x') => {
                let first = ascii_hex(values.next()).ok_or(())?;
                let second = ascii_hex(values.next()).ok_or(())?;
                result.push(first * 16 + second);
            }
            Some(selector @ ('n' | 'r' | 't' | '0' | '\\' | '\'' | '"')) => {
                let escaped = selector.to_string();
                let mut escaped_chars = escaped.chars();
                let decoded = parse_scalar_escape(&mut escaped_chars)?;
                let mut encoded = [0; 4];
                result.extend_from_slice(decoded.encode_utf8(&mut encoded).as_bytes());
            }
            Some('u') => {
                let mut escaped = String::from("u");
                loop {
                    let next = values.next().ok_or(())?;
                    escaped.push(next);
                    if next == '}' {
                        break;
                    }
                }
                let mut escaped_chars = escaped.chars();
                let decoded = parse_scalar_escape(&mut escaped_chars)?;
                let mut encoded = [0; 4];
                result.extend_from_slice(decoded.encode_utf8(&mut encoded).as_bytes());
            }
            _ => return Err(()),
        }
    }
    Ok(result)
}

/// Decode precisely the scalar escapes admitted by the lossless lexer.  This
/// is intentionally shared by literal lowering and VM pattern matching so a
/// recovered or hostile typed product cannot give the same spelling a second,
/// broader meaning after the source boundary has accepted it.
fn parse_scalar_escape(values: &mut std::str::Chars<'_>) -> Result<char, ()> {
    match values.next() {
        Some('n') => Ok('\n'),
        Some('r') => Ok('\r'),
        Some('t') => Ok('\t'),
        Some('0') => Ok('\0'),
        Some('\\') => Ok('\\'),
        Some('\'') => Ok('\''),
        Some('"') => Ok('"'),
        Some('x') => {
            let first = ascii_hex(values.next()).ok_or(())?;
            let second = ascii_hex(values.next()).ok_or(())?;
            let scalar = first * 16 + second;
            (scalar < 0x80).then_some(scalar as char).ok_or(())
        }
        Some('u') => {
            if values.next() != Some('{') {
                return Err(());
            }
            let mut scalar = 0_u32;
            let mut digits = 0_u8;
            loop {
                match values.next() {
                    Some('}') if digits > 0 => return char::from_u32(scalar).ok_or(()),
                    Some('}') | None => return Err(()),
                    Some(value) if digits < 6 => {
                        let value = ascii_hex(Some(value)).ok_or(())?;
                        scalar = scalar * 16 + u32::from(value);
                        digits += 1;
                    }
                    Some(_) => return Err(()),
                }
            }
        }
        _ => Err(()),
    }
}

fn ascii_hex(value: Option<char>) -> Option<u8> {
    let value = value?;
    match value {
        '0'..='9' => Some(value as u8 - b'0'),
        'a'..='f' => Some(value as u8 - b'a' + 10),
        'A'..='F' => Some(value as u8 - b'A' + 10),
        _ => None,
    }
}

#[cfg(test)]
mod mir_place_arena_tests {
    use super::*;

    #[test]
    fn byte_literals_preserve_raw_octets_and_encode_unicode_as_utf8() {
        assert_eq!(
            parse_byte_literal(r#"b"\x00\xffA\u{e9}""#),
            Ok(vec![0, 0xff, b'A', 0xc3, 0xa9])
        );
        assert!(parse_byte_literal(r#"b"\xg0""#).is_err());
    }

    fn operation_validation_function(entries: Vec<Option<MirOperationData>>) -> MirFunction {
        MirFunction {
            safety: crate::Safety::Safe,
            unsafe_execution: false,
            definition: DefKey(Digest::of_bytes(b"operation-validation")),
            nominal_copy_descriptors: vec![],
            captures: 0,
            parameters: vec![],
            locals: vec![MirLocalDecl {
                ty: Type::Scalar(crate::types::ScalarType::I64),
                source: CoreId(0),
            }],
            result: Type::Unit,
            control: MirControlTables {
                operations: MirOperationArena { entries },
                ..MirControlTables::default()
            },
            entry: MirBlockId(0),
            blocks: vec![MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![MirInstruction::ConstI64 {
                    dst: MirLocal(0),
                    value: 1,
                }],
                terminator: MirTerminator::Unreachable,
            }],
        }
    }

    fn branch_liveness_function(initialize_else_branch: bool) -> MirFunction {
        let local = MirLocal(1);
        let initializer = MirInstruction::ConstI64 {
            dst: local,
            value: 1,
        };
        MirFunction {
            safety: crate::Safety::Safe,
            unsafe_execution: false,
            definition: DefKey(Digest::of_bytes(b"branch-liveness")),
            nominal_copy_descriptors: vec![],
            captures: 0,
            parameters: vec![MirLocal(0)],
            locals: vec![
                MirLocalDecl {
                    ty: Type::Scalar(crate::types::ScalarType::Bool),
                    source: CoreId(0),
                },
                MirLocalDecl {
                    ty: Type::Scalar(crate::types::ScalarType::I64),
                    source: CoreId(1),
                },
            ],
            result: Type::Scalar(crate::types::ScalarType::I64),
            control: MirControlTables::default(),
            entry: MirBlockId(0),
            blocks: vec![
                MirBlock {
                    scope: MirScopeId::ROOT,
                    parameters: vec![],
                    instructions: vec![],
                    terminator: MirTerminator::SwitchBool {
                        condition: MirLocal(0),
                        then_target: MirBlockId(1),
                        then_arguments: vec![],
                        else_target: MirBlockId(2),
                        else_arguments: vec![],
                    },
                },
                MirBlock {
                    scope: MirScopeId::ROOT,
                    parameters: vec![],
                    instructions: vec![initializer.clone()],
                    terminator: MirTerminator::Goto {
                        target: MirBlockId(3),
                        arguments: vec![],
                    },
                },
                MirBlock {
                    scope: MirScopeId::ROOT,
                    parameters: vec![],
                    instructions: initialize_else_branch.then_some(initializer).into_iter().collect(),
                    terminator: MirTerminator::Goto {
                        target: MirBlockId(3),
                        arguments: vec![],
                    },
                },
                MirBlock {
                    scope: MirScopeId::ROOT,
                    parameters: vec![],
                    instructions: vec![],
                    terminator: MirTerminator::Return { value: local },
                },
            ],
        }
    }


    #[test]
    fn operation_arena_validation_rejects_a_second_live_identity_at_one_instruction() {
        let function = operation_validation_function(vec![
            Some(MirOperationData {
                block: MirBlockId(0),
                instruction_index: 0,
            }),
            Some(MirOperationData {
                block: MirBlockId(0),
                instruction_index: 0,
            }),
        ]);

        assert_eq!(
            function.validate_operation_arena(),
            Err("MIR live operation 1 has no instruction".into())
        );
    }

    #[test]
    fn operation_arena_validation_rejects_an_instruction_without_an_identity() {
        let mut function = operation_validation_function(vec![]);
        function.control.operations.entries.push(Some(MirOperationData {
            block: MirBlockId(0),
            instruction_index: 1,
        }));

        assert_eq!(
            function.validate_operation_arena(),
            Err("MIR instruction at block 0 index 0 has no operation identity".into())
        );
    }

    #[test]
    fn liveness_intersection_rejects_a_local_initialized_on_only_one_branch() {
        let error = branch_liveness_function(false)
            .validate_local_storage_liveness()
            .expect_err("join must require initialization on every predecessor");
        assert!(error.contains("MIR return reads dead/uninitialized local 1"));
        branch_liveness_function(true)
            .validate_local_storage_liveness()
            .expect("join accepts a local initialized on every predecessor");
    }
}
