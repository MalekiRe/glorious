//! Deterministic stage-zero VM artifact emission and independent verification.
//!
//! This is a deliberately narrow artifact contract owned by the new compiler,
//! not a wrapper around the legacy compiler. Its candidate/verified split is
//! retained as instructions and types grow toward the repository `.grbc`
//! contract: execution receives only `VerifiedVmArtifact`.

use std::{
    borrow::Borrow,
    collections::{BTreeMap, BTreeSet},
    ops::{Deref, DerefMut},
    sync::Arc,
};

use crate::{
    core::CaptureMode,
    identity::{DefKey, Digest},
    mir::{
        MirCleanupAction, MirContinuationPolicy, MirFunction, MirInstruction, MirLocal, MirPattern,
        MirPatternField, MirProgram, MirTerminator, canonical_f64_bits, is_canonical_f32_bits,
        is_canonical_f64_bits, parse_char_literal, parse_f64_literal, parse_text_literal,
    },
    runtime_manifest::{FloatBinaryOp, FloatCompareOp, FloatPrimitive, FloatWidth, PrimitiveRole},
    source::{TokenKind, exact_scalar_literal_kind},
    types::{
        ConstKind, EffectTail, GenericArgument, Lifetime, PointerMutability, Safety, ScalarType, StructuralU32Expr, Type,
    },
};

use crate::MemoryPrimitive;

mod native_memory;
use native_memory::{NativeMemory, NativeReference, execute_memory_intrinsic};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VmType {
    Unit,
    I64,
    /// A target-independent unsigned byte count. It is not represented as a
    /// host pointer width, so frozen artifacts preserve the standard-library
    /// `usize` ABI across hosts.
    Usize,
    U32,
    U8,
    U16,
    I16,
    I32,
    I8,
    U64,
    Isize,
    U128,
    I128,
    F32,
    F64,
    Bool,
    Char,
    Text,
    Bytes,
    /// Binder-local type variable in a generic VM function. The program
    /// verifier instantiates it at each direct call before execution begins.
    Generic(u32),
    /// A checked structural constant in a nominal layout.  Const kinds are
    /// retained as VM types solely because nominal layout identity is typed;
    /// they never become independently executable values.
    ConstU32(u32),
    ConstU32Expr(StructuralU32Expr),
    ConstQuantity {
        lower: u64,
        upper: Option<u64>,
    },
    ConstGeneric {
        index: u32,
        kind: ConstKind,
    },
    Array(Box<VmType>),
    /// Sealed artifact-backed data. This is deliberately distinct from both
    /// `Bytes` and an ordinary array: it carries the verifier-owned type tag
    /// and alignment needed to prevent reinterpreting embedded assets.
    StaticData {
        element: Box<VmType>,
        tag: u128,
        alignment: u32,
    },
    Tuple(Vec<VmType>),
    Nominal {
        definition: DefKey,
        arguments: Vec<VmType>,
    },
    Callable {
        safety: Safety,
        parameters: Vec<VmType>,
        result: Box<VmType>,
        /// The exact outward effect contract of this callable value.  This is
        /// part of callable identity: `() -> I64` and `() -> I64 ! {io}` are
        /// not interchangeable at an indirect-call or frozen-artifact
        /// boundary.
        effects: Box<VmEffectRow>,
    },
    Reference {
        unique: bool,
        referent: Box<VmType>,
    },
    RawPointer {
        mutability: PointerMutability,
        pointee: Box<VmType>,
    },
}

/// Source-free capture authority carried by a verified callable value.  It is
/// deliberately distinct from the runtime reference representation: this is
/// the sealed compile-time layout contract that an independently decoded VM
/// artifact checks before it can construct the value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VmCaptureMode {
    SharedBorrow,
    UniqueBorrow,
    Copy,
    Move,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmCapture {
    pub mode: VmCaptureMode,
    pub ty: VmType,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmCaptureEnvironment {
    pub owner: DefKey,
    pub callable: u32,
    /// The enclosing generic instance for a materialized lifted callable.
    /// `None` denotes the canonical, source-lifted body.  This witness binds
    /// a descriptor's lexical brand to exactly one executable identity rather
    /// than allowing an ABI-compatible sibling body to be substituted.
    pub instance: Option<Digest>,
    pub captures: Vec<VmCapture>,
}

/// A generic argument in a VM effect protocol identity.
///
/// Effect arguments never become VM values, but they are still observable by
/// handler selection.  Keeping their source kind here prevents a `const`,
/// lifetime, or effect-row argument from being silently conflated with a type
/// argument at the bytecode boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VmGenericArgument {
    Type(VmType),
    EffectRow(VmEffectRow),
    Lifetime(Lifetime),
    ConstU32(u32),
    /// Symbolic arithmetic remains a frozen, canonical const identity until
    /// the declaration binder is instantiated.  Do not replace it with an
    /// error type: handlers select on this full protocol identity.
    ConstU32Expr(StructuralU32Expr),
    ConstQuantity {
        lower: u64,
        upper: Option<u64>,
    },
    ConstGeneric {
        index: u32,
        kind: ConstKind,
    },
}

/// VM-owned structural representation of an effect-row generic argument.
/// The vector order is canonical: named instances and delayed projections are
/// both preserved so bytecode fingerprinting and artifact decoding have no
/// dependency on compiler-side inference state.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct VmEffectRow {
    pub effects: Vec<VmEffectInstance>,
    pub projections: Vec<VmEffectRowProjection>,
    pub tail: Option<EffectTail>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmEffectInstance {
    pub definition: DefKey,
    pub arguments: Vec<VmGenericArgument>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmEffectRowProjection {
    pub subject: VmType,
    pub trait_definition: DefKey,
    /// The enclosing trait head retains its source-slot kinds in frozen VM
    /// metadata. This row is not a value layout, so lifetimes and nested rows
    /// must never be coerced into `VmType` merely to serialize it.
    pub trait_arguments: Vec<VmGenericArgument>,
    pub name: String,
    /// Associated item arguments retain their source kind in bytecode
    /// metadata, even though this row never becomes a VM value.
    pub item_arguments: Vec<VmGenericArgument>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VmCompare {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

/// Runtime policy carried by each handler frame.  `Consume` retains affine
/// one-shot behavior; `Replay` keeps an immutable continuation snapshot for
/// every permitted resumption.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VmContinuationPolicy {
    Consume,
    /// The exact remaining-use budget is part of the executable frame, not
    /// merely an elaborator-side fact.  It is reset on each `Perform` and is
    /// decremented by every replay invocation.
    Replay {
        uses: u32,
    },
    /// A bottom-typed operation transfers to a terminal clause. The runtime
    /// retains the suspended call only until that clause cancels its frame.
    Terminal,
}

impl VmContinuationPolicy {
    fn is_replay(self) -> bool {
        matches!(self, Self::Replay { .. })
    }

    fn replay_uses(self) -> Option<u32> {
        match self {
            Self::Replay { uses } => Some(uses),
            Self::Consume | Self::Terminal => None,
        }
    }
}
/// Canonically encoded structural pattern for the standalone VM verifier.
/// It contains no source binder identity; fields carry their expected runtime
/// types so decoding and verification do not depend on compiler interfaces.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VmPattern {
    Any,
    Literal(String),
    Tuple(Vec<VmPattern>),
    Array {
        element: VmType,
        elements: Vec<VmPattern>,
    },
    Record {
        definition: DefKey,
        /// Complete ordered field layout carried from MIR. This allows the
        /// standalone verifier to reject an otherwise in-range projection
        /// with stale or forged field metadata.
        field_types: Vec<VmType>,
        /// Frozen aggregate arity. This lets the standalone verifier reject
        /// forged field projections without consulting compiler interfaces.
        field_count: u32,
        fields: Vec<VmPatternField>,
    },
    Enum {
        definition: DefKey,
        variant: u32,
        /// Complete ordered payload layout for this exact enum variant.
        field_types: Vec<VmType>,
        /// Frozen payload arity for this exact variant.
        field_count: u32,
        fields: Vec<VmPatternField>,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmPatternField {
    pub index: u32,
    pub ty: VmType,
    pub pattern: VmPattern,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VmInstruction {
    /// Function-owned ABI declaration emitted before its executable body.
    /// `returns` distinguishes an ordinary result contract from a body whose
    /// only reachable exits are terminal control transfers.  `Never` shares
    /// the VM's zero-sized Unit representation, so this control bit is what
    /// preserves non-returning intent across serialization.
    DeclareResult {
        result: VmType,
        returns: bool,
    },
    ConstUnit {
        dst: u32,
    },
    ConstI64 {
        dst: u32,
        value: i64,
    },
    ConstU8 {
        dst: u32,
        value: u8,
    },
    ConstU16 {
        dst: u32,
        value: u16,
    },
    ConstU32 {
        dst: u32,
        value: u32,
    },
    ConstU64 {
        dst: u32,
        value: u64,
    },
    ConstUsize {
        dst: u32,
        value: u64,
    },
    ConstU128 {
        dst: u32,
        value: u128,
    },
    ConstI8 {
        dst: u32,
        value: i8,
    },
    ConstI16 {
        dst: u32,
        value: i16,
    },
    ConstI32 {
        dst: u32,
        value: i32,
    },
    ConstIsize {
        dst: u32,
        value: i64,
    },
    ConstI128 {
        dst: u32,
        value: i128,
    },
    ConstF64 {
        dst: u32,
        bits: u64,
    },
    ConstF32 {
        dst: u32,
        bits: u32,
    },
    /// Sealed float leaf selected by the trusted runtime manifest.  It uses a
    /// selector-shaped payload only as an artifact opcode operand; no source
    /// lookup remains possible after MIR lowering.
    FloatIntrinsic {
        dst: u32,
        primitive: FloatPrimitive,
        arguments: Vec<u32>,
    },
    MemoryIntrinsic {
        dst: u32,
        primitive: MemoryPrimitive,
        types: Vec<VmType>,
        arguments: Vec<u32>,
    },
    /// Manifest-sealed generic integer operation specialized to one concrete
    /// integer representation by the instance materializer.
    IntIntrinsic {
        dst: u32,
        primitive: PrimitiveRole,
        scalar: ScalarType,
        arguments: Vec<u32>,
    },
    ConstBool {
        dst: u32,
        value: bool,
    },
    ConstChar {
        dst: u32,
        value: u32,
    },
    ConstText {
        dst: u32,
        value: String,
    },
    /// Sealed static bytes emitted only by compiler literal lowering.  The
    /// destination's `StaticData<u8>` type supplies the stable tag and
    /// alignment contract verified below.
    ConstStaticData {
        dst: u32,
        tag: u128,
        alignment: u32,
        bytes: Vec<u8>,
    },
    StaticLen {
        dst: u32,
        value: u32,
    },
    StaticSubslice {
        dst: u32,
        value: u32,
        start: u32,
        length: u32,
    },
    StaticGetBorrowShared {
        dst: u32,
        value: u32,
        index: u32,
    },
    StaticAsArrayBorrow { dst: u32, value: u32 },
    /// Opcode 64: trusted `Text -> usize` byte-length primitive. It carries
    /// neither a symbol nor a capability because manifest authority was
    /// consumed while lowering source identity to this sealed instruction.
    TextByteLen {
        dst: u32,
        value: u32,
    },
    TextConcat {
        dst: u32,
        left: u32,
        right: u32,
    },
    TextEq {
        dst: u32,
        left: u32,
        right: u32,
    },
    TextFromUtf8Checked {
        dst: u32,
        value: u32,
    },
    TextAsBytes {
        dst: u32,
        value: u32,
    },
    CharFromU32Checked {
        dst: u32,
        value: u32,
    },
    CharToU32 {
        dst: u32,
        value: u32,
    },
    BytesLen {
        dst: u32,
        value: u32,
    },
    BytesConcat {
        dst: u32,
        left: u32,
        right: u32,
    },
    BytesGet {
        dst: u32,
        bytes: u32,
        index: u32,
    },
    BytesSlice {
        dst: u32,
        bytes: u32,
        start: u32,
        end: u32,
    },
    BytesFromArrayMove {
        dst: u32,
        value: u32,
    },
    BytesToArray {
        dst: u32,
        value: u32,
    },
    BytesUtf8ValidUpTo {
        dst: u32,
        value: u32,
    },
    /// Manifest-bound unkeyed BLAKE3 over immutable bytes.
    Blake3 {
        dst: u32,
        value: u32,
    },
    ArrayNew {
        dst: u32,
        length: u32,
        fill: u32,
        element_type: VmType,
    },
    ArrayLen {
        dst: u32,
        value: u32,
        element_type: VmType,
    },
    ArrayUtf8ValidUpTo {
        dst: u32,
        value: u32,
    },
    ArrayPushUtf8Char { value: u32, character: u32 },
    ArrayInsertUtf8FromSlice {
        dst: u32,
        value: u32,
        index: u32,
        source: u32,
        start: u32,
        length: u32,
    },
    ArrayPopUtf8Char { dst: u32, value: u32 },
    ArrayUtf8CharAt {
        dst: u32,
        value: u32,
        start: u32,
        length: u32,
        index: u32,
    },
    ArrayExtendFromSlice {
        value: u32,
        source: u32,
        start: u32,
        length: u32,
        element_type: VmType,
    },
    ArrayInsertMove {
        value: u32,
        index: u32,
        item: u32,
        element_type: VmType,
    },
    ArrayRemoveMove {
        dst: u32,
        value: u32,
        index: u32,
        element_type: VmType,
    },
    ArrayAppendMove {
        value: u32,
        source: u32,
        element_type: VmType,
    },
    ArrayTruncateDiscard {
        value: u32,
        length: u32,
        element_type: VmType,
    },
    ArrayReverseMove {
        value: u32,
        element_type: VmType,
    },
    ArraySplitOffMove {
        dst: u32,
        value: u32,
        index: u32,
        element_type: VmType,
    },
    ArraySplitBorrowUnique {
        dst: u32,
        value: u32,
        start: u32,
        length: u32,
        index: u32,
        element_type: VmType,
    },
    ArrayInsertFromSlice {
        value: u32,
        index: u32,
        source: u32,
        start: u32,
        length: u32,
        element_type: VmType,
    },
    ArrayGetCopy {
        dst: u32,
        value: u32,
        index: u32,
        element_type: VmType,
    },
    ArrayGetMove {
        dst: u32,
        value: u32,
        index: u32,
        element_type: VmType,
    },
    ArrayGetBorrow {
        dst: u32,
        value: u32,
        index: u32,
        unique: bool,
        element_type: VmType,
    },
    ArraySetMove {
        value: u32,
        index: u32,
        item: u32,
        element_type: VmType,
    },
    ArrayEmpty {
        dst: u32,
        element_type: VmType,
    },
    ArrayPushMove {
        value: u32,
        item: u32,
        element_type: VmType,
    },
    ArrayPopMove {
        dst: u32,
        value: u32,
        element_type: VmType,
    },
    ArrayCapacity {
        dst: u32,
        value: u32,
        element_type: VmType,
    },
    ArrayReserve {
        value: u32,
        additional: u32,
        element_type: VmType,
    },
    ArrayFinishDrained {
        value: u32,
        element_type: VmType,
    },
    U32CheckedAdd {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32CheckedSub {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32CheckedMul {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32CheckedDiv {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32CheckedRem {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32WrappingAdd {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32WrappingSub {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32WrappingMul {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32WrappingShl {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32WrappingShr {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32CheckedShl {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32CheckedShr {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32Eq {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32Lt {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32Le {
        dst: u32,
        left: u32,
        right: u32,
    },
    U32ToUsize {
        dst: u32,
        value: u32,
    },
    UsizeToU32Checked {
        dst: u32,
        value: u32,
    },
    I64ToU32Checked {
        dst: u32,
        value: u32,
    },
    /// Exact manifest-bound i64-to-u32 conversion retaining low two's-complement bits.
    I64ToU32Wrapping {
        dst: u32,
        value: u32,
    },
    I64ToUsizeChecked {
        dst: u32,
        value: u32,
    },
    /// Exact manifest-bound i64-to-usize conversion retaining low two's-complement bits.
    I64ToUsizeWrapping {
        dst: u32,
        value: u32,
    },
    /// Exact manifest-bound checked i64-to-u8 conversion.
    I64ToU8Checked {
        dst: u32,
        value: u32,
    },
    /// Exact manifest-bound i64-to-u8 conversion retaining low two's-complement bits.
    I64ToU8Wrapping {
        dst: u32,
        value: u32,
    },
    /// Exact manifest-bound checked i64-to-u16 conversion.
    I64ToU16Checked {
        dst: u32,
        value: u32,
    },
    /// Exact manifest-bound i64-to-u16 conversion retaining low two's-complement bits.
    I64ToU16Wrapping {
        dst: u32,
        value: u32,
    },
    I64ToI16Checked {
        dst: u32,
        value: u32,
    },
    I64ToI16Wrapping {
        dst: u32,
        value: u32,
    },
    /// Exact manifest-bound checked i64-to-i32 conversion.
    I64ToI32Checked {
        dst: u32,
        value: u32,
    },
    /// Exact manifest-bound i64-to-i32 conversion retaining low two's-complement bits.
    I64ToI32Wrapping {
        dst: u32,
        value: u32,
    },
    I64ToI8Checked {
        dst: u32,
        value: u32,
    },
    I64ToI8Wrapping {
        dst: u32,
        value: u32,
    },
    I64ToU64Checked {
        dst: u32,
        value: u32,
    },
    I64ToU64Wrapping {
        dst: u32,
        value: u32,
    },
    I64ToIsizeChecked {
        dst: u32,
        value: u32,
    },
    I64ToIsizeWrapping {
        dst: u32,
        value: u32,
    },
    I64ToU128Checked {
        dst: u32,
        value: u32,
    },
    I64ToU128Wrapping {
        dst: u32,
        value: u32,
    },
    I64ToI128Checked {
        dst: u32,
        value: u32,
    },
    I64ToI128Wrapping {
        dst: u32,
        value: u32,
    },
    MakeTuple {
        dst: u32,
        fields: Vec<u32>,
    },
    MakeArray {
        dst: u32,
        fields: Vec<u32>,
        element_type: VmType,
    },
    MakeRecord {
        dst: u32,
        definition: DefKey,
        fields: Vec<u32>,
        field_types: Vec<VmType>,
    },
    MakeEnum {
        dst: u32,
        definition: DefKey,
        variant: u32,
        fields: Vec<u32>,
        field_types: Vec<VmType>,
    },
    ProjectRecord {
        dst: u32,
        base: u32,
        index: u32,
        field_count: u32,
        field_type: VmType,
    },
    ProjectTuple {
        dst: u32,
        base: u32,
        index: u32,
        field_count: u32,
        field_type: VmType,
    },
    ProjectArray {
        dst: u32,
        base: u32,
        index: u32,
        field_count: u32,
        element_type: VmType,
    },
    UpdateRecord {
        dst: u32,
        base: u32,
        index: u32,
        field_count: u32,
        value: u32,
        field_type: VmType,
    },
    PatternTest {
        dst: u32,
        subject: u32,
        pattern: VmPattern,
    },
    Perform {
        dst: u32,
        effect: DefKey,
        effect_arguments: Vec<VmGenericArgument>,
        operation: u32,
        arguments: Vec<u32>,
    },
    /// Install one lexical handler frame. The frame is active while its
    /// protected continuation executes; `continuation` specifies whether a
    /// suspended snapshot is consumed or retained for replay.
    InstallHandler {
        effect: DefKey,
        effect_arguments: Vec<VmGenericArgument>,
        operation: u32,
        payload_destinations: Vec<u32>,
        resume_type: VmType,
        continuation: VmContinuationPolicy,
        target: u32,
    },
    /// Leave the current lexical handler after its protected computation has
    /// completed. A suspended handler cannot be removed.
    UninstallHandler,
    /// Consume the innermost suspended continuation and continue its protected
    /// computation. The handler is thereby reactivated (deep semantics).
    Resume {
        value: u32,
    },
    /// Invoke a resumable continuation as a callable operation. The resumed
    /// computation returns to the handler clause and writes its result to
    /// `dst`; a replay frame retains its snapshot while a one-shot frame is
    /// consumed before the protected computation runs.
    ResumeReturn {
        dst: u32,
        value: u32,
    },
    /// Materialize an explicit token for the innermost suspended handler
    /// continuation. The token is callable-typed but frame-branded at runtime.
    CaptureResumption {
        dst: u32,
    },
    /// Resume the exact frame named by an explicit snapshot token.
    ResumeSnapshot {
        snapshot: u32,
        value: u32,
    },
    /// Decline the innermost suspended handler clause. The original effect
    /// transfer is retried at the next matching outer frame; the declined
    /// frame is retained in the continuation for deep reinstatement.
    Forward,
    /// Abandon the innermost suspended continuation without resuming it.
    /// The surrounding source contract must establish that zero resumption
    /// uses are permitted.
    Cancel,
    Copy {
        dst: u32,
        src: u32,
    },
    /// Start an addressable source-storage slot. `binding` is the dense
    /// frozen MIR provenance identity retained for independently decoded
    /// artifacts; it is not a register-derived lookup.
    StorageLive {
        binding: u32,
        local: u32,
    },
    /// End an already-disarmed addressable source-storage slot.
    StorageDead {
        binding: u32,
        local: u32,
    },
    /// Runtime representation of a compiler-created conditional-init flag.
    SetDropFlag {
        flag: u32,
        value: bool,
    },
    /// Conditional zero-destruction. The VM's empty register state is the
    /// executable drop-flag outcome; this opcode makes that transition
    /// independently checkable before artifact execution.
    DestroyIf {
        local: u32,
        flag: u32,
    },
    /// A checked mutable-register store. The verifier accepts this as the
    /// only instruction that may overwrite a live register.
    Store {
        dst: u32,
        src: u32,
    },
    Move {
        dst: u32,
        src: u32,
    },
    Borrow {
        dst: u32,
        src: u32,
        fields: Vec<u32>,
        unique: bool,
        /// Distinguishes a loan to a reference carrier (`&reference`) from a
        /// loan derived through that reference (`&*reference`). This bit is
        /// part of the decoded artifact contract; inferring it from the
        /// runtime value would silently erase one reference layer.
        reborrow: bool,
    },
    DerefCopy {
        dst: u32,
        reference: u32,
    },
    /// Move through a unique reference. The verifier makes the reference
    /// temporarily unreadable until `DerefStore` restores a referent.
    DerefMove {
        dst: u32,
        reference: u32,
    },
    DerefStore {
        reference: u32,
        src: u32,
    },
    NotBool {
        dst: u32,
        value: u32,
    },
    AddI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    /// Exact manifest-bound wrapping i64 addition. This remains distinct from
    /// checked `AddI64` in the frozen bytecode contract.
    WrappingAddI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    /// Exact manifest-bound wrapping i64 subtraction. This remains distinct
    /// from checked `SubI64` in the frozen bytecode contract.
    WrappingSubI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    /// Exact manifest-bound wrapping i64 multiplication. This remains distinct
    /// from checked `MulI64` in the frozen bytecode contract.
    WrappingMulI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    /// Exact generic `__g1_int_equal<i64>` leaf with its frozen u32 ABI.
    IntEqualI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    /// Exact generic `__g1_int_less<i64>` leaf with its frozen u32 ABI.
    IntLessI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    /// Exact generic `__g1_int_greater<i64>` leaf with its frozen u32 ABI.
    IntGreaterI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    /// Exact manifest-bound i64 bitwise-and. This remains distinct from all
    /// source arithmetic in the frozen bytecode contract.
    BitAndI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    BitAndU32 {
        dst: u32,
        left: u32,
        right: u32,
    },
    BitAndU64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    /// Exact manifest-bound i64 bitwise-xor. This remains distinct from all
    /// source arithmetic in the frozen bytecode contract.
    BitXorI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    /// Exact manifest-bound i64 right shift with a checked u32 count. Counts
    /// outside the source width trap rather than being masked modulo 64.
    IntShrI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    /// Exact manifest-bound i64 bitwise-or. This remains distinct from all
    /// source arithmetic in the frozen bytecode contract.
    BitOrI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    /// Exact manifest-bound i64 bitwise-not. This is unary in the frozen
    /// bytecode contract.
    BitNotI64 {
        dst: u32,
        value: u32,
    },
    /// Exact manifest-bound i64 left shift with a checked u32 count. The
    /// shifted value wraps within its width only after the count is valid.
    ShlI64 {
        dst: u32,
        value: u32,
        count: u32,
    },
    SubI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    MulI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    DivI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    RemI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    AddF64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    ConcatText {
        dst: u32,
        left: u32,
        right: u32,
    },
    SubF64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    MulF64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    DivF64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    RemF64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    CompareI64 {
        dst: u32,
        left: u32,
        right: u32,
        op: VmCompare,
    },
    CompareU32 {
        dst: u32,
        left: u32,
        right: u32,
        op: VmCompare,
    },
    CompareU64 {
        dst: u32,
        left: u32,
        right: u32,
        op: VmCompare,
    },
    CompareF64 {
        dst: u32,
        left: u32,
        right: u32,
        op: VmCompare,
    },
    EqBool {
        dst: u32,
        left: u32,
        right: u32,
    },
    NeBool {
        dst: u32,
        left: u32,
        right: u32,
    },
    EqText {
        dst: u32,
        left: u32,
        right: u32,
    },
    NeText {
        dst: u32,
        left: u32,
        right: u32,
    },
    CompareChar {
        dst: u32,
        left: u32,
        right: u32,
        op: VmCompare,
    },
    Call {
        dst: u32,
        callee: DefKey,
        arguments: Vec<u32>,
    },
    /// A host boundary carries its exact capability and ABI symbol in the
    /// artifact. Execution receives no implicit host authority.
    HostCall {
        dst: u32,
        capability: String,
        symbol: String,
        parameters: Vec<VmType>,
        result: VmType,
        arguments: Vec<u32>,
    },
    MakeCallable {
        dst: u32,
        callee: DefKey,
        captures: Vec<u32>,
        /// Exact sealed environment contract emitted by MIR for an anonymous
        /// closure. Named function values retain `None` and must have no
        /// captures. The verifier recomputes `callee` from this brand.
        environment: Option<VmCaptureEnvironment>,
    },
    /// A runtime token for a compiler-minted lexical label. The dynamic
    /// frame/handler depth is attached when this instruction executes.
    MakeLabel {
        dst: u32,
        brand_owner: DefKey,
        brand_label: u32,
        target: u32,
        destination: u32,
    },
    CallIndirect {
        dst: u32,
        callee: u32,
        arguments: Vec<u32>,
    },
    /// A branded nonlocal control edge.  Unlike `Jump`, a leave retains the
    /// exact cleanup proof and its parallel block-argument transfer in the
    /// executable artifact.  The VM may erase the lexical brand only after
    /// the verifier has checked it and the cleanup evidence.
    Leave {
        brand_owner: DefKey,
        brand_label: u32,
        handler_depth: u32,
        target: u32,
        arguments: Vec<u32>,
        destinations: Vec<u32>,
        cleanup: VmCleanupProof,
    },
    Jump {
        target: u32,
    },
    BranchBool {
        condition: u32,
        then_target: u32,
        else_target: u32,
    },
    Return {
        value: u32,
    },
    /// A checked terminal for MIR's impossible control-flow edge. It has no
    /// operands and cannot fall through into an unrelated instruction.
    Trap,
}
/// Canonical, artifact-safe ownership evidence attached to a nonlocal leave.
/// Move paths and lexical bindings are numeric identities frozen by MIR. Text
/// is retained only as diagnostic presentation and is never used to decide
/// ownership overlap in a decoded artifact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmCleanupProof {
    pub moved_places: Vec<VmCleanupPlace>,
    pub active_loans: Vec<VmCleanupLoan>,
    /// Checked summary of the source-storage lifecycle that was compacted
    /// before this nonlocal edge entered the VM artifact.  `Missing` is a
    /// deliberately representable hostile-artifact state; the verifier never
    /// accepts it.  Keeping it explicit rather than inferring it from the
    /// register cleanup facts prevents a newer decoder from accidentally
    /// treating pre-schema artifacts as having completed storage cleanup.
    pub storage_erasure: VmStorageErasureWitness,
}
/// A decoder-verifiable account of source storage erased at a lexical exit.
///
/// This is intentionally VM-shaped: `storage`, `binding`, and register
/// identities are frozen numeric artifacts, not MIR types or source spans.
/// The frontend/MIR bridge can therefore construct it without making the
/// runtime artifact depend on compiler-only storage structures.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VmStorageErasureWitness {
    /// Never valid in a verified artifact.  It exists so malformed and stale
    /// wire payloads can be represented and rejected deterministically.
    Missing,
    Verified {
        /// Source storages in lexical creation order.  Cleanup actions run in
        /// the inverse order and complete each storage's lifecycle exactly.
        storages: Vec<VmStorageErasureStorage>,
        /// Ordered lifetime/drop/storage-release actions compacted from MIR.
        actions: Vec<VmStorageErasureAction>,
        /// The exact, sorted set of registers transferred as protected Leave
        /// payloads.  A storage that owns one must use `Protect` rather than
        /// `Destroy` before its `StorageDead` action.
        protected_registers: Vec<u32>,
    },
}
/// A source-storage identity visible at the VM artifact boundary.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct VmStorageErasureStorage {
    pub storage: u32,
    pub binding: u32,
    pub value_register: u32,
    pub initialized: bool,
    /// The compiler-created drop flag for an initialized storage, if it has
    /// one.  The corresponding cleanup action must disarm it before death.
    pub drop_flag: Option<u32>,
}
/// Canonically ordered source-storage cleanup actions.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum VmStorageErasureAction {
    EndBorrow {
        storage: u32,
    },
    /// Move a protected Leave payload out of source storage.  This disarms
    /// destruction while preserving the payload for parallel transfer.
    Protect {
        storage: u32,
        register: u32,
    },
    Destroy {
        storage: u32,
    },
    SetDropFlag {
        drop_flag: u32,
        initialized: bool,
    },
    StorageDead {
        storage: u32,
    },
}
/// The runtime control payload for a verified `Leave`.  It is deliberately
/// separate from a program counter: a perform can capture a continuation
/// while a nonlocal exit is unwinding handler frames, and deep forwarding or
/// resumption must restore the same transfer rather than reconstructing one
/// from ambient register state.
#[derive(Clone, Debug, Eq, PartialEq)]
struct PendingLeave {
    brand_owner: DefKey,
    brand_label: u32,
    handler_depth: u32,
    target: u32,
    arguments: Vec<u32>,
    destinations: Vec<u32>,
    cleanup: VmCleanupProof,
}
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct VmCleanupPlace {
    pub path: u32,
    pub binding: u32,
    /// Human-readable presentation of the binding; never a semantic key.
    pub root: String,
    pub fields: Vec<u32>,
}
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct VmCleanupLoan {
    pub owner: Option<String>,
    pub binding: u32,
    /// Human-readable presentation of the binding; never a semantic key.
    pub root: String,
    pub fields: Vec<u32>,
    pub unique: bool,
}
impl VmCleanupProof {
    pub fn from_mir(
        plan: &crate::MirCleanupPlan,
        paths: &crate::MirMovePathTables,
        storage: &crate::MirSourceStorageTables,
    ) -> Result<Self, VmArtifactError> {
        plan.validate_with_storage(paths, storage).map_err(|_| {
            VmArtifactError::MalformedEncoding {
                message: "MIR source-storage cleanup is not encodable",
            }
        })?;
        let mut moved_places = plan
            .moved_paths
            .iter()
            .zip(&plan.moved_places)
            .map(|(&path, place)| {
                let data = &paths.paths[path.0 as usize];
                VmCleanupPlace {
                    path: path.0,
                    binding: data.binding.0,
                    root: place.root.clone(),
                    fields: place.fields.clone(),
                }
            })
            .collect::<Vec<_>>();
        moved_places.sort_by_key(|place| place.path);
        let mut active_loans = plan
            .active_loans
            .iter()
            .map(|loan| VmCleanupLoan {
                owner: loan.owner.clone(),
                binding: loan.binding.0,
                root: loan.root.clone(),
                fields: loan.fields.clone(),
                unique: loan.unique,
            })
            .collect::<Vec<_>>();
        active_loans.sort_by(|left, right| {
            (left.binding, &left.fields, &left.owner, left.unique).cmp(&(
                right.binding,
                &right.fields,
                &right.owner,
                right.unique,
            ))
        });
        let exited = storage
            .exited_bindings(plan.source_storage_scope, plan.target_storage_scope)
            .map_err(|_| VmArtifactError::MalformedEncoding {
                message: "MIR source-storage exit is not encodable",
            })?;
        let flags = plan
            .drop_flags
            .iter()
            .map(|flag| (flag.binding.0, flag.id.0))
            .collect::<BTreeMap<_, _>>();
        let mut storages =
            exited
                .iter()
                .map(|binding| {
                    let local = storage.binding_local(*binding).ok_or(
                        VmArtifactError::MalformedEncoding {
                            message: "exited source storage has no VM local mapping",
                        },
                    )?;
                    let drop_flag = flags.get(&binding.0).copied().ok_or(
                        VmArtifactError::MalformedEncoding {
                            message: "exited source storage has no typed drop flag",
                        },
                    )?;
                    Ok(VmStorageErasureStorage {
                        storage: binding.0,
                        binding: binding.0,
                        value_register: local.0,
                        // A source drop flag means this owner is conditionally
                        // initialized. Its explicit terminal action, rather than
                        // a guessed register state, decides Drop versus Protect.
                        initialized: true,
                        drop_flag: Some(drop_flag),
                    })
                })
                .collect::<Result<Vec<_>, VmArtifactError>>()?;
        storages.sort_by_key(|storage| storage.storage);
        let actions = plan
            .actions
            .iter()
            .map(|action| match *action {
                MirCleanupAction::EndBorrow { binding } => {
                    VmStorageErasureAction::EndBorrow { storage: binding.0 }
                }
                MirCleanupAction::Drop { binding, .. } => {
                    VmStorageErasureAction::Destroy { storage: binding.0 }
                }
                MirCleanupAction::Protect { binding, local } => VmStorageErasureAction::Protect {
                    storage: binding.0,
                    register: local.0,
                },
                MirCleanupAction::ClearDropFlag { flag } => VmStorageErasureAction::SetDropFlag {
                    drop_flag: flag.0,
                    initialized: false,
                },
                MirCleanupAction::StorageDead { binding } => {
                    VmStorageErasureAction::StorageDead { storage: binding.0 }
                }
            })
            .collect();
        let protected_registers = plan.protected_values.iter().map(|local| local.0).collect();
        Ok(Self {
            moved_places,
            active_loans,
            storage_erasure: VmStorageErasureWitness::Verified {
                storages,
                actions,
                protected_registers,
            },
        })
    }
    pub fn validate(&self) -> bool {
        if self.moved_places.iter().any(|place| {
            place.path == u32::MAX || place.binding == u32::MAX || place.root.is_empty()
        }) || self
            .active_loans
            .iter()
            .any(|loan| loan.binding == u32::MAX || loan.root.is_empty())
            || !self
                .moved_places
                .windows(2)
                .all(|pair| pair[0].path < pair[1].path)
            || !self.active_loans.windows(2).all(|pair| {
                (
                    pair[0].binding,
                    &pair[0].fields,
                    &pair[0].owner,
                    pair[0].unique,
                ) < (
                    pair[1].binding,
                    &pair[1].fields,
                    &pair[1].owner,
                    pair[1].unique,
                )
            })
        {
            return false;
        }
        if self.moved_places.iter().enumerate().any(|(index, place)| {
            self.moved_places[index + 1..].iter().any(|other| {
                place.binding == other.binding
                    && (place.fields.starts_with(&other.fields)
                        || other.fields.starts_with(&place.fields))
            })
        }) {
            return false;
        }
        !self.moved_places.iter().any(|moved| {
            self.active_loans.iter().any(|loan| {
                moved.binding == loan.binding
                    && (moved.fields.starts_with(&loan.fields)
                        || loan.fields.starts_with(&moved.fields))
            })
        })
    }
}
impl VmStorageErasureWitness {
    /// A valid witness for a Leave which has no source-storage owners to
    /// erase.  It is still an explicit proof: instruction selection fills in
    /// the protected transfer registers before serialization.
    pub fn without_source_storage() -> Self {
        Self::Verified {
            storages: vec![],
            actions: vec![],
            protected_registers: vec![],
        }
    }

    pub fn set_protected_registers(&mut self, registers: &[u32]) {
        let protected_registers = registers
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        match self {
            Self::Missing => {}
            Self::Verified {
                protected_registers: current,
                ..
            } => *current = protected_registers,
        }
    }

    fn validate(&self, leave_arguments: &[u32], register_count: usize) -> bool {
        let Self::Verified {
            storages,
            actions,
            protected_registers,
        } = self
        else {
            return false;
        };
        let leave_registers = leave_arguments.iter().copied().collect::<BTreeSet<_>>();
        if protected_registers
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
            .len()
            != protected_registers.len()
            || protected_registers
                .iter()
                .any(|register| !leave_registers.contains(register))
            || protected_registers
                .iter()
                .any(|register| *register as usize >= register_count)
            || !storages
                .windows(2)
                .all(|pair| pair[0].storage < pair[1].storage)
            || storages.iter().any(|storage| {
                storage.storage == u32::MAX
                    || storage.binding == u32::MAX
                    || storage.storage != storage.binding
                    || storage.value_register as usize >= register_count
                    || storage.drop_flag == Some(u32::MAX)
            })
        {
            return false;
        }
        let storage_by_id = storages
            .iter()
            .map(|storage| (storage.storage, storage))
            .collect::<BTreeMap<_, _>>();
        let drop_flags = storages
            .iter()
            .filter_map(|storage| storage.drop_flag)
            .collect::<BTreeSet<_>>();
        if drop_flags.len()
            != storages
                .iter()
                .filter_map(|storage| storage.drop_flag)
                .count()
        {
            return false;
        }
        if storages
            .iter()
            .map(|storage| storage.binding)
            .collect::<BTreeSet<_>>()
            .len()
            != storages.len()
        {
            return false;
        }
        // A frozen source binding owns one exact addressable local. Allowing
        // two distinct bindings to name one value register would let a
        // compact artifact forge ambiguous destruction/protection ownership.
        if storages
            .iter()
            .map(|storage| storage.value_register)
            .collect::<BTreeSet<_>>()
            .len()
            != storages.len()
        {
            return false;
        }
        if storages.iter().any(|storage| {
            protected_registers
                .binary_search(&storage.value_register)
                .is_ok()
                && !leave_registers.contains(&storage.value_register)
        }) {
            return false;
        }

        // Keep the source action order in the artifact rather than reducing
        // it to a register-cleanup shape. EndBorrow operations may be
        // scheduled before another storage's terminal action, so validate the
        // same per-storage state machine used at the MIR boundary while still
        // requiring terminal actions in reverse lexical-storage order.
        #[derive(Clone, Copy, Eq, PartialEq)]
        enum Progress {
            Start,
            BorrowEnded,
            Terminal,
            FlagCleared,
            Dead,
        }
        let mut progress = storages
            .iter()
            .map(|storage| (storage.storage, Progress::Start))
            .collect::<BTreeMap<_, _>>();
        let flag_storage = storages
            .iter()
            .filter_map(|storage| storage.drop_flag.map(|flag| (flag, storage.storage)))
            .collect::<BTreeMap<_, _>>();
        let mut terminal_order = Vec::new();
        for action in actions {
            let storage = match *action {
                VmStorageErasureAction::EndBorrow { storage }
                | VmStorageErasureAction::Destroy { storage }
                | VmStorageErasureAction::StorageDead { storage }
                | VmStorageErasureAction::Protect { storage, .. } => storage,
                VmStorageErasureAction::SetDropFlag { drop_flag, .. } => {
                    let Some(storage) = flag_storage.get(&drop_flag) else {
                        return false;
                    };
                    *storage
                }
            };
            let Some(state) = progress.get_mut(&storage) else {
                return false;
            };
            match *action {
                VmStorageErasureAction::EndBorrow { .. } => {
                    if !matches!(*state, Progress::Start) {
                        return false;
                    }
                    *state = Progress::BorrowEnded;
                }
                VmStorageErasureAction::Destroy { .. } => {
                    let Some(data) = storage_by_id.get(&storage) else {
                        return false;
                    };
                    if !data.initialized
                        || protected_registers
                            .binary_search(&data.value_register)
                            .is_ok()
                        || !matches!(*state, Progress::Start | Progress::BorrowEnded)
                    {
                        return false;
                    }
                    *state = Progress::Terminal;
                    terminal_order.push(storage);
                }
                VmStorageErasureAction::Protect { register, .. } => {
                    let Some(data) = storage_by_id.get(&storage) else {
                        return false;
                    };
                    if !data.initialized
                        || data.value_register != register
                        || protected_registers.binary_search(&register).is_err()
                        || !matches!(*state, Progress::Start | Progress::BorrowEnded)
                    {
                        return false;
                    }
                    *state = Progress::Terminal;
                    terminal_order.push(storage);
                }
                VmStorageErasureAction::SetDropFlag {
                    drop_flag,
                    initialized,
                } => {
                    if initialized
                        || storage_by_id.get(&storage).and_then(|data| data.drop_flag)
                            != Some(drop_flag)
                        || *state != Progress::Terminal
                    {
                        return false;
                    }
                    *state = Progress::FlagCleared;
                }
                VmStorageErasureAction::StorageDead { .. } => {
                    let Some(data) = storage_by_id.get(&storage) else {
                        return false;
                    };
                    // A conditional owner whose flag is known false has no
                    // resident value to destroy and no flag transition to
                    // emit. Its exact erasure path is directly
                    // `StorageDead` (after any borrow-ending action).
                    if *state != Progress::FlagCleared
                        && (data.initialized
                            || !matches!(*state, Progress::Start | Progress::BorrowEnded))
                    {
                        return false;
                    }
                    *state = Progress::Dead;
                }
            }
        }
        progress.values().all(|state| *state == Progress::Dead)
            && terminal_order
                == storages
                    .iter()
                    .rev()
                    .filter(|storage| storage.initialized)
                    .map(|storage| storage.storage)
                    .collect::<Vec<_>>()
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmNominalCopyDescriptor {
    pub definition: DefKey,
    pub is_enum: bool,
    pub arguments: Vec<VmType>,
    pub variants: Vec<Vec<VmType>>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmFunction {
    pub definition: DefKey,
    pub safety: Safety,
    pub unsafe_execution: bool,
    /// Sealed declaration-owned layouts for every nominal identity whose
    /// value may be copied by this function.
    pub nominal_copy_descriptors: Vec<VmNominalCopyDescriptor>,
    /// Captures occupy the prefix of `parameters` for a lifted closure body.
    pub captures: u32,
    pub parameters: u32,
    pub registers: Vec<VmType>,
    pub instructions: Vec<VmInstruction>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateVmArtifact {
    pub schema: u32,
    pub runtime_manifest: Option<Digest>,
    pub function: VmFunction,
    pub fingerprint: Digest,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateVmProgram {
    pub schema: u32,
    pub runtime_manifest: Option<Digest>,
    /// Exact sorted capability declarations required by reachable HostCall
    /// instructions. This is an artifact boundary, not host process state.
    pub host_capabilities: Vec<String>,
    pub entry: DefKey,
    pub functions: BTreeMap<DefKey, VmFunction>,
    /// The target-side sealed layout for every lifted callable. This registry
    /// is independent of each construction instruction so the verifier can
    /// reject a producer that changes capture authority while retaining the
    /// same target and register types.
    pub callable_environments: BTreeMap<DefKey, VmCaptureEnvironment>,
    pub fingerprint: Digest,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VmArtifactError {
    /// Use the explicit unsafe Rust execution entry point for code containing
    /// programmer-owned unsafe obligations. This is not bytecode admission.
    UnsafeExecutionRequiresUnsafeApi,
    NativeMemory {
        message: &'static str,
    },
    UnsupportedNativeLayout {
        ty: VmType,
    },
    MalformedEncoding {
        message: &'static str,
    },
    NonCanonicalEncoding,
    DecodeLimit {
        kind: &'static str,
        limit: u64,
    },
    UnsupportedType {
        local: u32,
        ty: Box<Type>,
    },
    /// A type nested in an effect identity has no representable VM form. This
    /// is distinct from non-type generic arguments, which the VM preserves.
    UnsupportedEffectArgumentType {
        effect: DefKey,
        ty: Box<Type>,
    },
    UnsupportedControlFlow,
    InvalidRegister {
        register: u32,
    },
    InvalidInstructionTarget {
        target: u32,
    },
    /// Ordinary CFG edges may not enter a handler clause.  A clause is entered
    /// only by `Perform`, which installs its payload and one-shot continuation
    /// state before transferring control.
    HandlerTargetReachedByControlFlow {
        target: u32,
    },
    IncompatibleControlFlow {
        target: u32,
    },
    ReadBeforeWrite {
        register: u32,
    },
    DoubleWrite {
        register: u32,
    },
    UseAfterMove {
        register: u32,
    },
    AffineValueCopy {
        register: u32,
    },
    NoReturn,
    Trap,
    /// Checked text construction rejected a byte sequence that is not UTF-8.
    InvalidUtf8,
    /// Checked character construction rejected a non-Unicode-scalar `u32`.
    InvalidChar {
        value: u32,
    },
    InstructionAfterReturn,
    MissingFunction {
        definition: DefKey,
    },
    CallRequiresProgram,
    HostCallRequiresAuthority {
        capability: String,
        symbol: String,
    },
    /// The embedding host explicitly received a frozen host call but could
    /// not complete it.  This is deliberately distinct from an absent host:
    /// a verified artifact never obtains process authority by itself.
    HostCallFailed {
        capability: String,
        symbol: String,
        message: String,
    },
    CallArity {
        expected: u32,
        found: u32,
    },
    NotCallable {
        register: u32,
    },
    InvalidCallableEnvironment {
        message: &'static str,
    },
    /// A nominal label brand denotes one lexical destination and its exact
    /// typed payload ABI.  A candidate must not repurpose it as an arbitrary
    /// jump capability on another path.
    InvalidLabelContract {
        message: &'static str,
    },
    /// A source-storage binding is a frozen identity, not an annotation on an
    /// arbitrary register. Every executable StorageLive/StorageDead mention
    /// must retain its one-to-one binding/local pairing across the artifact.
    InvalidSourceStorageIdentity {
        binding: u32,
        local: u32,
        message: &'static str,
    },
    /// A boundary that snapshots its payload (for example a callable capture
    /// or retained continuation) cannot carry a unique reference without
    /// losing write-back. Ordinary call/return boundaries use live caller
    /// targets instead.
    UnsupportedEscapingUniqueReference,
    CallDepthLimit {
        limit: u32,
    },
    HandlerDepthLimit {
        limit: u32,
    },
    ContinuationLimit {
        limit: u32,
    },
    InstructionLimit {
        limit: u64,
    },
    /// A single aggregate or handler payload exceeded the configured number
    /// of runtime value elements before it was materialized.
    ValueSizeLimit {
        kind: &'static str,
        limit: u64,
        found: u64,
    },
    /// The sum of materialized runtime value elements exceeded its execution
    /// budget. This prevents an instruction-bounded loop from allocating an
    /// unbounded sequence of individually small aggregates.
    AllocationLimit {
        limit: u64,
    },
    TypeMismatch {
        register: u32,
        expected: VmType,
        found: VmType,
    },
    ResultType {
        expected: VmType,
        found: VmType,
    },
    UnsupportedSchema {
        found: u32,
    },
    FingerprintMismatch,
    /// A frozen float immediate carried a payload-distinct NaN spelling.
    /// Runtime arithmetic may produce NaN, but it is canonicalized before it
    /// becomes an observable VM value.
    NonCanonicalFloat {
        bits: u64,
    },
    DivisionByZero,
    ArithmeticOverflow,
    UnhandledEffect {
        effect: DefKey,
        /// The exact nominal protocol instance that escaped the handler
        /// stack. This is required to distinguish e.g. `State<i64>` from
        /// `State<Text>` at the VM boundary.
        effect_arguments: Vec<VmGenericArgument>,
        operation: u32,
    },
    HandlerStackUnderflow,
    HandlerResumeUnavailable,
    HandlerStateMismatch,
    HandlerStillActive,
}

/// Explicit authority for a verified VM program's frozen host imports.
///
/// The VM itself has no ambient process, filesystem, or diagnostic access.
/// An embedding application must pass this adapter to one of the
/// `run_*_with_host` entry points, and only the exact capability/symbol pairs
/// carried by the verified artifact can reach these methods.
pub trait VmHost {
    fn process_args(&mut self) -> Result<Vec<String>, String>;
    fn read_file(&mut self, path: &str) -> Result<Vec<u8>, String>;
    fn write_file(&mut self, path: &str, bytes: &[u8]) -> Result<(), String>;
    /// Atomically replace one final path through a same-directory staging
    /// file. Hosts that do not explicitly expose this authority fail closed.
    fn write_file_atomically(&mut self, _path: &str, _bytes: &[u8]) -> Result<(), String> {
        Err("atomic file write capability is unavailable".into())
    }
    fn write_diagnostic(&mut self, text: &str) -> Result<(), String>;
}

/// A deliberately opt-in host adapter for command-line embeddings.  It is
/// never installed by ordinary `run_*` methods; callers must construct and
/// pass it at the program boundary.
#[derive(Clone, Debug)]
pub struct SystemVmHost {
    arguments: Vec<String>,
}

impl SystemVmHost {
    pub fn new(arguments: Vec<String>) -> Self {
        Self { arguments }
    }
}

impl VmHost for SystemVmHost {
    fn process_args(&mut self) -> Result<Vec<String>, String> {
        Ok(self.arguments.clone())
    }

    fn read_file(&mut self, path: &str) -> Result<Vec<u8>, String> {
        std::fs::read(path).map_err(|error| error.to_string())
    }

    fn write_file(&mut self, path: &str, bytes: &[u8]) -> Result<(), String> {
        std::fs::write(path, bytes).map_err(|error| error.to_string())
    }

    fn write_file_atomically(&mut self, path: &str, bytes: &[u8]) -> Result<(), String> {
        crate::output::write_atomically(path, bytes).map_err(|error| error.to_string())
    }

    fn write_diagnostic(&mut self, text: &str) -> Result<(), String> {
        eprint!("{text}");
        Ok(())
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct VmExecutionLimits {
    /// Live raw allocation bytes, separate from logical register/element charges.
    pub max_native_bytes: u64,
    pub max_native_allocation_bytes: u64,
    pub max_call_depth: u32,
    pub max_handler_depth: u32,
    /// Maximum suspended handler continuations retained at once.
    pub max_retained_continuations: u32,
    pub max_instructions: u64,
    /// Largest materialized aggregate or handler payload, in value elements.
    pub max_value_elements: u64,
    /// Total materialized runtime value elements for one execution.
    pub max_allocation_elements: u64,
}

/// Authoring-runtime measurements, not compiler semantic counters. Allocation
/// charges are logical VM-budget counts, not a Rust allocator census.
/// The opt-in authoring runner can recycle caller-preserving self-tail calls;
/// ordinary execution retains its existing call-depth behavior.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct VmAuthoringProfile {
    pub work_ticks: u64,
    pub charged_allocation_elements: u64,
    pub peak_call_depth: u32,
    pub recycled_tail_calls: u64,
    pub inspected_tail_argument_elements: u64,
}
impl Default for VmExecutionLimits {
    fn default() -> Self {
        Self {
            max_native_bytes: 1 << 24,
            max_native_allocation_bytes: 1 << 20,
            // The source compiler's cursor-based frontend is deliberately
            // recursive until source-defined loops/tail-call lowering land.
            // Keep a finite hostile-program boundary, but leave enough headroom
            // for the compiler to lex and compile its own complete source tree.
            max_call_depth: 16_384,
            max_handler_depth: 4_096,
            max_retained_continuations: 4_096,
            // Compiler-scale source traversal can legitimately execute more
            // than ten million bounded cursor operations before it emits an
            // artifact. The execution budget remains finite and callers can
            // still choose a tighter explicit limit for untrusted programs.
            max_instructions: 100_000_000,
            max_value_elements: 1 << 20,
            max_allocation_elements: 1 << 24,
        }
    }
}
#[derive(Clone, Debug)]
pub struct VerifiedVmArtifact {
    artifact: CandidateVmArtifact,
}
#[derive(Clone, Debug)]
pub struct VerifiedVmProgram {
    program: CandidateVmProgram,
}
impl CandidateVmArtifact {
    pub fn computed_fingerprint(&self) -> Digest {
        artifact_fingerprint(self.runtime_manifest, &self.function)
    }
}

/// Stable, bounded Stage 0 candidate-artifact envelope. The payload is an
/// implementation-local stepping stone rather than the repository's released
/// G1 `.grbc` container; it exists so cache/process boundaries are decoded and
/// independently verified before the VM can see an execution image.
pub const STAGE0_ARTIFACT_MAGIC: [u8; 8] = *b"G0VM\r\n\x1a\n";
pub const STAGE0_PROGRAM_MAGIC: [u8; 8] = *b"G0VP\r\n\x1a\n";
/// Schema 72 adds opcode 131 for manifest-bound wrapping i64-to-u64 conversion. Schema 71 adds opcode 130 for manifest-bound checked i64-to-u64 conversion. Schema 70 adds opcode 129 for manifest-bound wrapping i64-to-i8 conversion. Schema 69 adds opcode 128 for manifest-bound checked i64-to-i8 conversion. Schema 68 adds opcode 127 for manifest-bound wrapping i64-to-i32 conversion. Schema 67 adds opcode 126 for manifest-bound checked i64-to-i32 conversion. Schema 66 adds opcode 125 for manifest-bound wrapping i64-to-i16 conversion. Schema 65 adds opcode 124 for manifest-bound checked i64-to-i16 conversion. Schema 64 adds opcode 123 for manifest-bound wrapping i64-to-u16 conversion,
/// retaining the low two's-complement bits. Schema 63 adds opcode 122 for
/// manifest-bound checked i64-to-u16 conversion,
/// rejecting negative and out-of-range values deterministically. Schema 62
/// adds opcode 121 for manifest-bound wrapping i64-to-u8 conversion,
/// retaining the low two's-complement bits. Schema 61 adds opcode 120 for
/// manifest-bound checked i64-to-u8 conversion,
/// rejecting negative and out-of-range values deterministically. Schema 60
/// adds opcode 119 for manifest-bound wrapping i64-to-usize
/// conversion, retaining the low two's-complement bits. Schema 59 adds opcode
/// 118 for manifest-bound checked i64-to-usize
/// conversion, rejecting negative values deterministically. Schema 58 adds
/// opcode 117 for manifest-bound wrapping i64-to-u32
/// conversion, retaining the low two's-complement bits. Schema 57 adds opcode
/// 116 for manifest-bound checked i64-to-u32 conversion. Schema 56 adds opcode
/// 114 for manifest-bound i64 left shift with a u32 count. Schema 55 adds
/// opcode 115 for manifest-bound i64 right shift with a u32 count. Schema 54 adds opcode 113 for
/// manifest-bound unary i64 bitwise-not. Schema
/// 53 adds opcode 112 for manifest-bound i64 bitwise-xor. Schema 52
/// adds opcode 111 for manifest-bound i64 bitwise-or. Schema 51
/// adds opcode 107 for manifest-bound wrapping i64 multiplication.
/// Schema 50 adds opcode 106 for manifest-bound wrapping i64 subtraction.
/// Schema 49 adds opcode 108 for manifest-bound i64 bitwise-and. Schema 48
/// adds opcode 110 for the manifest-bound generic i64 greater-than leaf,
/// whose public ABI returns a canonical u32 predicate. Schema 47 adds opcode
/// 109 for the manifest-bound generic i64 less-than leaf, whose public ABI
/// returns a canonical u32 predicate. Schema 46 adds opcode 105 for the
/// Schema 80 resolves the independently introduced runtime families into one
/// canonical layout: floating intrinsics use opcode 138 and generic Array
/// storage uses opcodes 139 through 150.
/// Schema 78 adds manifest-bound generic i64 equality leaf, whose public ABI returns a
/// canonical u32 predicate. Schema 45 adds opcode 104 for manifest-bound
/// wrapping i64 addition. Schema
/// 43 adds the canonical Bytes opcode family 80 through 86. Schema 42 reserves G1 opcodes 48 and 49 for the checked Char/u32
/// conversion family and relocates internal control encodings. Schema 40 adds `u32`/`Bytes` values and opcodes 65 through 68 for the
/// manifest-bound Text family. Schema 39 adds a target-independent `usize`
/// scalar and opcode 64 for the manifest-bound `TextByteLen` leaf. Schema 38 adds recursively validated
/// nominal copy descriptors to each VM
/// function. Earlier encodings lack the declaration-owned evidence required
/// to distinguish a copyable record from one that carries a unique reference.
/// Schema 32 adds sealed callable-environment brands, modes, and capture
/// types to `MakeCallable` and the target-side program registry. Schema 33
/// adds explicit Borrow carrier-versus-reborrow intent. Schema 34 carries
/// exact finite replay budgets in `InstallHandler`; older payloads cannot be
/// decoded safely with these independent boundary proofs. Schema 35 seals
/// structural u32 expressions and all const kinds inside nominal layouts and
/// effect protocol identities. Schema 36 canonically represents IEEE-754 NaN
/// immediates, preventing host/payload-dependent artifact identities. Schema
/// 37 makes canonical outward effect rows part of every callable VM type, so
/// effect-distinct function values cannot collapse across a frozen boundary.
/// Schema 80 also adds the sealed f32/f64 runtime intrinsic opcode and
/// first-class f32 VM layout. Older artifacts cannot be decoded under the
/// merged runtime contract. Schema 81 encodes numeric cleanup path and
/// binding identities, making diagnostic root strings non-semantic. Schema
/// 82 adds canonical source-storage lifecycle/drop-flag/action witnesses to
/// every nonlocal Leave, so compact VM cleanup cannot lose its MIR proof.
/// Schema 86 makes nominal aggregate construction, projection, and update
/// prove their field layouts against the frozen declaration-owned descriptor,
/// preventing an embedded callable from being relabelled with a forged ABI.
/// Schema 88 canonically orders each function's declaration-owned nominal
/// layout descriptor set. The descriptors are selected by identity rather
/// than position, so accepting alternate orders would otherwise give one VM
/// program multiple byte encodings and cache fingerprints.
/// Schema 88 also seals each emitted function's declared result and whether
/// it returns normally. This lets a terminal callee retain its source
/// callable ABI even when it contains no Return instruction.
/// Schema 85 binds every sealed callable environment to either its canonical
/// source lift or an explicit enclosing-instance witness, so a decoded
/// closure descriptor cannot redirect to an ABI-compatible sibling body.
/// Schema 83 makes all generic and frozen integer shifts reject a count at or
/// beyond the operand width instead of silently masking it.
/// Schema 91 adds the sealed `StaticData` type encoding. Its tag and
/// alignment are part of the frozen type identity rather than being erased
/// into the legacy Text/Bytes representations.
/// Schema 92 adds `DerefMove`, allowing a unique borrowed referent to be
/// moved out and restored without treating an affine value as copied.
/// Schema 93 adds sealed `ConstStaticData` literals. Schema 94 preserves source
/// safety contracts and nominal kind, and adds host-memory types/operations.
/// It is for locally compiled source; untrusted-bytecode certification of the
/// new unsafe facilities is deferred. Earlier payloads are not reinterpreted.
/// Schema 95 adds raw-to-checked reference construction, retaining native
/// storage identity across calls, reborrows, and checked dereferences.
pub const STAGE0_VM_SCHEMA: u32 = 96;
/// Static process-boundary decoding caps, enforced before vector allocation.
pub const STAGE0_MAX_DECODE_FUNCTIONS: u64 = 1 << 16;
pub const STAGE0_MAX_DECODE_REGISTERS: u64 = 1 << 20;
pub const STAGE0_MAX_DECODE_INSTRUCTIONS: u64 = 1 << 22;
pub const STAGE0_MAX_DECODE_TEXT_BYTES: u64 = 1 << 26;
const MAX_DECODE_FUNCTIONS: u64 = STAGE0_MAX_DECODE_FUNCTIONS;
const MAX_DECODE_REGISTERS: u64 = STAGE0_MAX_DECODE_REGISTERS;
const MAX_DECODE_INSTRUCTIONS: u64 = STAGE0_MAX_DECODE_INSTRUCTIONS;
const MAX_DECODE_TEXT_BYTES: u64 = STAGE0_MAX_DECODE_TEXT_BYTES;
// Callable ABI rows make each decoded type frame materially larger. Keep the
// hostile-artifact bound below the process stack budget while still allowing
// far deeper type nesting than any Stage 0 source construct needs.
const MAX_DECODE_TYPE_DEPTH: u64 = 96;

pub fn encode_artifact(artifact: &CandidateVmArtifact) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&STAGE0_ARTIFACT_MAGIC);
    bytes.extend_from_slice(&artifact.schema.to_le_bytes());
    bytes.extend_from_slice(&artifact.fingerprint.as_bytes());
    encode_optional_digest(artifact.runtime_manifest, &mut bytes);
    let payload_start = bytes.len() + 8;
    bytes.resize(payload_start, 0);
    encode_function(&artifact.function, &mut bytes);
    let payload_len = (bytes.len() - payload_start) as u64;
    let payload_length_offset = payload_start - 8;
    bytes[payload_length_offset..payload_start].copy_from_slice(&payload_len.to_le_bytes());
    bytes
}

pub fn decode_artifact(bytes: &[u8]) -> Result<CandidateVmArtifact, VmArtifactError> {
    let mut decoder = Decoder::new(bytes);
    if decoder.bytes(8)? != STAGE0_ARTIFACT_MAGIC {
        return Err(VmArtifactError::MalformedEncoding {
            message: "invalid Stage 0 artifact magic",
        });
    }
    let schema = decoder.u32()?;
    if schema != STAGE0_VM_SCHEMA {
        return Err(VmArtifactError::UnsupportedSchema { found: schema });
    }
    let fingerprint = Digest::from_bytes(decoder.array()?);
    let runtime_manifest = decoder.optional_digest()?;
    let payload_len = decoder.u64()?;
    if payload_len != decoder.remaining() as u64 {
        return Err(VmArtifactError::MalformedEncoding {
            message: "artifact payload length does not match input length",
        });
    }
    let function = decoder.function()?;
    if decoder.remaining() != 0 {
        return Err(VmArtifactError::MalformedEncoding {
            message: "trailing bytes after artifact payload",
        });
    }
    let artifact = CandidateVmArtifact {
        schema,
        runtime_manifest,
        function,
        fingerprint,
    };
    if encode_artifact(&artifact) != bytes {
        return Err(VmArtifactError::NonCanonicalEncoding);
    }
    Ok(artifact)
}

pub fn decode_and_verify_artifact(bytes: &[u8]) -> Result<VerifiedVmArtifact, VmArtifactError> {
    verify(decode_artifact(bytes)?)
}

pub fn encode_program(program: &CandidateVmProgram) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&STAGE0_PROGRAM_MAGIC);
    bytes.extend_from_slice(&program.schema.to_le_bytes());
    bytes.extend_from_slice(&program.entry.0.as_bytes());
    bytes.extend_from_slice(&program.fingerprint.as_bytes());
    encode_optional_digest(program.runtime_manifest, &mut bytes);
    bytes.extend_from_slice(&(program.host_capabilities.len() as u64).to_le_bytes());
    for capability in &program.host_capabilities {
        bytes.extend_from_slice(&(capability.len() as u64).to_le_bytes());
        bytes.extend_from_slice(capability.as_bytes());
    }
    bytes.extend_from_slice(&(program.functions.len() as u64).to_le_bytes());
    for function in program.functions.values() {
        encode_function(function, &mut bytes);
    }
    bytes.extend_from_slice(&(program.callable_environments.len() as u64).to_le_bytes());
    for (callee, environment) in &program.callable_environments {
        bytes.extend_from_slice(&callee.0.as_bytes());
        encode_capture_environment(Some(environment), &mut bytes);
    }
    bytes
}

pub fn decode_program(bytes: &[u8]) -> Result<CandidateVmProgram, VmArtifactError> {
    let mut decoder = Decoder::new(bytes);
    if decoder.bytes(8)? != STAGE0_PROGRAM_MAGIC {
        return Err(VmArtifactError::MalformedEncoding {
            message: "invalid Stage 0 program magic",
        });
    }
    let schema = decoder.u32()?;
    if schema != STAGE0_VM_SCHEMA {
        return Err(VmArtifactError::UnsupportedSchema { found: schema });
    }
    let entry = decoder.def_key()?;
    let fingerprint = Digest::from_bytes(decoder.array()?);
    let runtime_manifest = decoder.optional_digest()?;
    let capability_count = decoder.count("host capabilities", MAX_DECODE_REGISTERS)?;
    let mut host_capabilities = Vec::with_capacity(capability_count);
    for _ in 0..capability_count {
        host_capabilities.push(decoder.text()?);
    }
    let count = decoder.count("functions", MAX_DECODE_FUNCTIONS)?;
    let mut functions = BTreeMap::new();
    for _ in 0..count {
        let function = decoder.function()?;
        if functions.insert(function.definition, function).is_some() {
            return Err(VmArtifactError::MalformedEncoding {
                message: "duplicate function definition in program",
            });
        }
    }
    let environment_count = decoder.count("callable environment registry", MAX_DECODE_FUNCTIONS)?;
    let mut callable_environments = BTreeMap::new();
    for _ in 0..environment_count {
        let callee = decoder.def_key()?;
        let Some(environment) = decoder.capture_environment()? else {
            return Err(VmArtifactError::MalformedEncoding {
                message: "callable environment registry contains an absent layout",
            });
        };
        if callable_environments.insert(callee, environment).is_some() {
            return Err(VmArtifactError::MalformedEncoding {
                message: "duplicate callable environment target in program",
            });
        }
    }
    if decoder.remaining() != 0 {
        return Err(VmArtifactError::MalformedEncoding {
            message: "trailing bytes after program payload",
        });
    }
    let program = CandidateVmProgram {
        schema,
        runtime_manifest,
        host_capabilities,
        entry,
        functions,
        callable_environments,
        fingerprint,
    };
    if encode_program(&program) != bytes {
        return Err(VmArtifactError::NonCanonicalEncoding);
    }
    Ok(program)
}

pub fn decode_and_verify_program(bytes: &[u8]) -> Result<VerifiedVmProgram, VmArtifactError> {
    verify_program(decode_program(bytes)?)
}
impl CandidateVmProgram {
    pub fn computed_fingerprint(&self) -> Digest {
        program_fingerprint(
            self.entry,
            self.runtime_manifest,
            &self.host_capabilities,
            &self.functions,
            &self.callable_environments,
        )
    }
}
impl VerifiedVmArtifact {
    /// Execute a locally compiled artifact containing programmer-owned unsafe
    /// obligations. Existing structural checks and resource limits still apply.
    ///
    /// # Safety
    /// For this execution, the caller must uphold the source program's unsafe
    /// preconditions, pointer validity, aliasing, resident ownership, and cleanup.
    /// This API does not validate hostile bytecode or provide memory containment.
    pub unsafe fn run_i64_with_unsafe(&self, limits: VmExecutionLimits) -> Result<i64, VmArtifactError> {
        let mut budget = ExecutionBudget { native_memory: NativeMemory::default(), unsafe_execution: true,
            limits, instructions: 0, allocated_elements: 0 };
        expect_i64(execute(&self.artifact.function, &mut budget)?)
    }

    pub fn fingerprint(&self) -> Digest {
        self.artifact.fingerprint
    }
    pub fn runtime_manifest(&self) -> Option<Digest> {
        self.artifact.runtime_manifest
    }
    fn execute_with_limits(&self, limits: VmExecutionLimits) -> Result<VmValue, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits,
            instructions: 0,
            allocated_elements: 0,
        };
        execute(&self.artifact.function, &mut budget)
    }
    pub fn run_i64(&self) -> Result<i64, VmArtifactError> {
        self.run_i64_with_limits(VmExecutionLimits::default())
    }
    pub fn run_usize(&self) -> Result<u64, VmArtifactError> {
        expect_usize(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_u32(&self) -> Result<u32, VmArtifactError> {
        expect_u32(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_u8(&self) -> Result<u8, VmArtifactError> {
        expect_u8(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_u16(&self) -> Result<u16, VmArtifactError> {
        expect_u16(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_i16(&self) -> Result<i16, VmArtifactError> {
        expect_i16(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_i32(&self) -> Result<i32, VmArtifactError> {
        expect_i32(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_i8(&self) -> Result<i8, VmArtifactError> {
        expect_i8(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_u64(&self) -> Result<u64, VmArtifactError> {
        expect_u64(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_isize(&self) -> Result<i64, VmArtifactError> {
        expect_isize(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_u128(&self) -> Result<u128, VmArtifactError> {
        expect_u128(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_i128(&self) -> Result<i128, VmArtifactError> {
        expect_i128(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_i64_with_limits(&self, limits: VmExecutionLimits) -> Result<i64, VmArtifactError> {
        expect_i64(self.execute_with_limits(limits)?)
    }
    pub fn run_tuple_i64(&self) -> Result<Vec<i64>, VmArtifactError> {
        expect_tuple_i64(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_array_i64(&self) -> Result<Vec<i64>, VmArtifactError> {
        expect_array_i64(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_record_i64(&self) -> Result<Vec<i64>, VmArtifactError> {
        expect_record_i64(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_enum_i64(&self) -> Result<Vec<i64>, VmArtifactError> {
        expect_enum_i64(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_unit(&self) -> Result<(), VmArtifactError> {
        expect_unit(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_f64(&self) -> Result<f64, VmArtifactError> {
        expect_f64(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_f32(&self) -> Result<f32, VmArtifactError> {
        expect_f32(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_bool(&self) -> Result<bool, VmArtifactError> {
        expect_bool(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_char(&self) -> Result<char, VmArtifactError> {
        expect_char(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_text(&self) -> Result<String, VmArtifactError> {
        self.run_text_with_limits(VmExecutionLimits::default())
    }
    pub fn run_text_with_limits(
        &self,
        limits: VmExecutionLimits,
    ) -> Result<String, VmArtifactError> {
        Ok(expect_text(self.execute_with_limits(limits)?)?.to_string())
    }
}
impl VerifiedVmProgram {
    /// Execute locally compiled source with its unsafe implementation obligations.
    /// Permission lasts for this call only; it is not attached to artifact bytes.
    ///
    /// # Safety
    /// The caller must uphold all unsafe source/library invariants for this
    /// execution: valid initialized residents, provenance, alignment, aliasing,
    /// ownership transfer, callbacks, and cleanup on every exit. Existing bytecode
    /// checks do not prove these obligations or contain invalid host-memory access.
    pub unsafe fn run_i64_with_unsafe(&self, limits: VmExecutionLimits) -> Result<i64, VmArtifactError> {
        let mut budget = ExecutionBudget { native_memory: NativeMemory::default(), unsafe_execution: true,
            limits, instructions: 0, allocated_elements: 0 };
        expect_i64(execute_with_arguments(&self.program, self.program.entry, &[], 0, &mut budget)?)
    }

    /// Render one unrestricted locally compiled source execution with optional
    /// explicit host capabilities. This is not a hostile-bytecode admission API.
    ///
    /// # Safety
    /// The caller has the same per-execution source/unsafe obligations as
    /// `run_i64_with_unsafe`, including the supplied host's callback contracts.
    pub unsafe fn run_display_with_unsafe(&self, limits: VmExecutionLimits, mut host: Option<&mut dyn VmHost>)
        -> Result<String, VmArtifactError>
    {
        let mut budget = ExecutionBudget { native_memory: NativeMemory::default(), unsafe_execution: true,
            limits, instructions: 0, allocated_elements: 0 };
        let value = execute_with_arguments_with_host(&self.program, self.program.entry, &[], 0, &mut budget, &mut host)?;
        Ok(format_vm_value(&value))
    }

    pub fn fingerprint(&self) -> Digest {
        self.program.fingerprint
    }
    /// Return the canonical bytes that were independently decoded and
    /// verified before this program became executable. This is the only
    /// process-boundary representation exposed by the verified program API.
    pub fn canonical_bytes(&self) -> Vec<u8> {
        encode_program(&self.program)
    }
    /// Execute the entry point and render its VM value without exposing the
    /// runtime's private ownership representation. This is intended for host
    /// tooling; typed embedding APIs should use the `run_*` methods below.
    pub fn run_display(&self) -> Result<String, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        Ok(format_vm_value(&execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?))
    }

    /// Execute a verified program with an explicit, capability-bound host.
    /// The returned rendering preserves the ordinary embedding boundary: VM
    /// ownership values never escape into the host API.
    pub fn run_display_with_host(
        &self,
        host: &mut dyn VmHost,
    ) -> Result<String, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        let mut host = Some(host);
        Ok(format_vm_value(&execute_with_arguments_with_host(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
            &mut host,
        )?))
    }
    pub fn runtime_manifest(&self) -> Option<Digest> {
        self.program.runtime_manifest
    }

    /// Execute a source-substrate probe with measured, opt-in frame recycling.
    /// This is an authoring capability, not a change to the frozen execution
    /// APIs or an assertion that the G1 runtime supports this profile.
    pub fn run_i64_for_authoring(
        &self,
        limits: VmExecutionLimits,
    ) -> Result<(i64, VmAuthoringProfile), VmArtifactError> {
        let (result, profile) = self.run_value_for_authoring(limits)?;
        Ok((expect_i64(result)?, profile))
    }

    /// Execute a batch while retaining every result for independent comparison.
    /// The batch shares the existing execution budget; it does not receive a
    /// larger limit or a fresh budget for each tuple element.
    pub fn run_tuple_i64_for_authoring(
        &self,
        limits: VmExecutionLimits,
    ) -> Result<(Vec<i64>, VmAuthoringProfile), VmArtifactError> {
        let (result, profile) = self.run_value_for_authoring(limits)?;
        Ok((expect_tuple_i64(result)?, profile))
    }

    fn run_value_for_authoring(
        &self,
        limits: VmExecutionLimits,
    ) -> Result<(VmValue, VmAuthoringProfile), VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits,
            instructions: 0,
            allocated_elements: 0,
        };
        let mut profile = VmAuthoringProfile::default();
        let result = execute_program_profiled(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
            &mut None,
            Some(&mut profile),
        )?;
        profile.work_ticks = budget.instructions;
        profile.charged_allocation_elements = budget.allocated_elements;
        Ok((result, profile))
    }
    pub fn run_i64(&self) -> Result<i64, VmArtifactError> {
        self.run_i64_with_limits(VmExecutionLimits::default())
    }
    pub fn run_usize(&self) -> Result<u64, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_usize(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_u32(&self) -> Result<u32, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_u32(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_u8(&self) -> Result<u8, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_u8(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_u16(&self) -> Result<u16, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_u16(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_i16(&self) -> Result<i16, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_i16(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_i32(&self) -> Result<i32, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_i32(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_i8(&self) -> Result<i8, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_i8(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_u64(&self) -> Result<u64, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_u64(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_isize(&self) -> Result<i64, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_isize(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_u128(&self) -> Result<u128, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_u128(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_i128(&self) -> Result<i128, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_i128(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_tuple_i64(&self) -> Result<Vec<i64>, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_tuple_i64(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_array_i64(&self) -> Result<Vec<i64>, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_array_i64(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_record_i64(&self) -> Result<Vec<i64>, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_record_i64(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_enum_i64(&self) -> Result<Vec<i64>, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_enum_i64(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_unit(&self) -> Result<(), VmArtifactError> {
        self.run_unit_with_limits(VmExecutionLimits::default())
    }
    pub fn run_unit_with_limits(&self, limits: VmExecutionLimits) -> Result<(), VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits,
            instructions: 0,
            allocated_elements: 0,
        };
        expect_unit(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }

    /// Execute a unit-returning verified program with explicit host authority.
    /// This is the entry point used by the self-host compiler application.
    pub fn run_unit_with_host(&self, host: &mut dyn VmHost) -> Result<(), VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        let mut host = Some(host);
        expect_unit(execute_with_arguments_with_host(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
            &mut host,
        )?)
    }
    pub fn run_i64_with_limits(&self, limits: VmExecutionLimits) -> Result<i64, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits,
            instructions: 0,
            allocated_elements: 0,
        };
        expect_i64(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_f64(&self) -> Result<f64, VmArtifactError> {
        self.run_f64_with_limits(VmExecutionLimits::default())
    }
    pub fn run_f64_with_limits(&self, limits: VmExecutionLimits) -> Result<f64, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits,
            instructions: 0,
            allocated_elements: 0,
        };
        expect_f64(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_f32(&self) -> Result<f32, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        expect_f32(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_bool(&self) -> Result<bool, VmArtifactError> {
        self.run_bool_with_limits(VmExecutionLimits::default())
    }
    pub fn run_bool_with_limits(&self, limits: VmExecutionLimits) -> Result<bool, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits,
            instructions: 0,
            allocated_elements: 0,
        };
        expect_bool(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_char(&self) -> Result<char, VmArtifactError> {
        self.run_char_with_limits(VmExecutionLimits::default())
    }
    pub fn run_char_with_limits(&self, limits: VmExecutionLimits) -> Result<char, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits,
            instructions: 0,
            allocated_elements: 0,
        };
        expect_char(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)
    }
    pub fn run_text(&self) -> Result<String, VmArtifactError> {
        self.run_text_with_limits(VmExecutionLimits::default())
    }
    pub fn run_text_with_limits(
        &self,
        limits: VmExecutionLimits,
    ) -> Result<String, VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits,
            instructions: 0,
            allocated_elements: 0,
        };
        Ok(expect_text(execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?)?
        .to_string())
    }
}

pub fn emit(function: &MirFunction) -> Result<CandidateVmArtifact, VmArtifactError> {
    emit_with_specialized_lifted_targets(function, &BTreeSet::new())
}

fn emit_with_specialized_lifted_targets(
    function: &MirFunction,
    specialized_lifted_targets: &BTreeSet<DefKey>,
) -> Result<CandidateVmArtifact, VmArtifactError> {
    if function
        .validate_with_specialized_lifted_targets(specialized_lifted_targets)
        .is_err()
        || function.entry.0 != 0
        || !function.blocks[0].parameters.is_empty()
    {
        return Err(VmArtifactError::UnsupportedControlFlow);
    }
    let mut registers = function
        .locals
        .iter()
        .enumerate()
        .map(|(local, value)| {
            vm_type(&value.ty).map_err(|ty| VmArtifactError::UnsupportedType {
                local: local as u32,
                ty,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut starts = Vec::with_capacity(function.blocks.len());
    // Every emitted body starts with its sealed result/control declaration.
    let mut next = 1u32;
    for block in &function.blocks {
        starts.push(next);
        let control_len = match &block.terminator {
            MirTerminator::Return { .. } => 1,
            MirTerminator::Goto { target, arguments } => {
                edge_length(arguments, &function.blocks[target.0 as usize])
            }
            MirTerminator::Leave { .. } => 1,
            MirTerminator::SwitchBool {
                then_target,
                then_arguments,
                else_target,
                else_arguments,
                ..
            } => {
                1 + edge_length(then_arguments, &function.blocks[then_target.0 as usize])
                    + edge_length(else_arguments, &function.blocks[else_target.0 as usize])
            }
            MirTerminator::Unreachable => 1,
        };
        next = next
            .checked_add(block.instructions.len() as u32 + control_len)
            .ok_or(VmArtifactError::UnsupportedControlFlow)?;
    }
    let mut instructions = Vec::with_capacity(next as usize);
    instructions.push(VmInstruction::DeclareResult {
        result: vm_type(&function.result).map_err(|ty| VmArtifactError::UnsupportedType {
            local: u32::MAX,
            ty,
        })?,
        returns: false,
    });
    for (block_index, block) in function.blocks.iter().enumerate() {
        instructions.extend(
            block
                .instructions
                .iter()
                .map(|instruction| lower_instruction(instruction, &starts))
                .collect::<Result<Vec<_>, _>>()?,
        );
        match &block.terminator {
            MirTerminator::Return { value } => {
                instructions.push(VmInstruction::Return { value: value.0 });
            }
            MirTerminator::Goto { target, arguments } => {
                let target = *starts
                    .get(target.0 as usize)
                    .ok_or(VmArtifactError::UnsupportedControlFlow)?;
                emit_edge(
                    arguments,
                    &function.blocks[target_index(target, &starts)?],
                    target,
                    &mut registers,
                    &mut instructions,
                );
            }
            MirTerminator::Leave {
                brand,
                target,
                arguments,
                cleanup,
                ..
            } => {
                let target = *starts
                    .get(target.0 as usize)
                    .ok_or(VmArtifactError::UnsupportedControlFlow)?;
                let arguments = arguments
                    .iter()
                    .map(|argument| argument.0)
                    .collect::<Vec<_>>();
                instructions.push(VmInstruction::Leave {
                    brand_owner: brand.owner,
                    brand_label: brand.label,
                    handler_depth: function
                        .control
                        .leave_handler_depths
                        .get(&crate::mir::MirBlockId(block_index as u32))
                        .copied()
                        .unwrap_or_else(|| retained_handler_depth(&block.instructions)),
                    target,
                    arguments: arguments.clone(),
                    destinations: function.blocks[target_index(target, &starts)?]
                        .parameters
                        .iter()
                        .map(|parameter| parameter.0)
                        .collect(),
                    cleanup: VmCleanupProof::from_mir(
                        cleanup,
                        &function.control.move_paths,
                        &function.control.source_storage,
                    )?,
                });
            }
            MirTerminator::SwitchBool {
                condition,
                then_target,
                then_arguments,
                else_target,
                else_arguments,
            } => {
                let then_destination = *starts
                    .get(then_target.0 as usize)
                    .ok_or(VmArtifactError::UnsupportedControlFlow)?;
                let else_destination = *starts
                    .get(else_target.0 as usize)
                    .ok_or(VmArtifactError::UnsupportedControlFlow)?;
                let then_edge = instructions.len() as u32 + 1;
                let else_edge = then_edge
                    + edge_length(then_arguments, &function.blocks[then_target.0 as usize]);
                instructions.push(VmInstruction::BranchBool {
                    condition: condition.0,
                    then_target: then_edge,
                    else_target: else_edge,
                });
                emit_edge(
                    then_arguments,
                    &function.blocks[then_target.0 as usize],
                    then_destination,
                    &mut registers,
                    &mut instructions,
                );
                emit_edge(
                    else_arguments,
                    &function.blocks[else_target.0 as usize],
                    else_destination,
                    &mut registers,
                    &mut instructions,
                );
            }
            MirTerminator::Unreachable => instructions.push(VmInstruction::Trap),
        }
    }
    let returns = vm_instructions_may_return(&instructions);
    if let Some(VmInstruction::DeclareResult { returns: declared, .. }) = instructions.first_mut() {
        *declared = returns;
    }
    let mut nominal_copy_descriptors = function
        .nominal_copy_descriptors
        .iter()
        .map(vm_nominal_copy_descriptor)
        .collect::<Result<Vec<_>, _>>()?;
    nominal_copy_descriptors.sort_by_key(vm_nominal_copy_descriptor_key);
    // Lifetimes deliberately do not exist in VM type identity.  A source
    // body can therefore reach the same nominal layout once through an
    // explicit `'static` view and once through an elided view.  Collapse the
    // identical VM descriptors here, at the representation-erasure boundary;
    // retain a hard failure if erasure would make two distinct layouts claim
    // the same identity.
    let mut canonical_descriptors: Vec<VmNominalCopyDescriptor> =
        Vec::with_capacity(nominal_copy_descriptors.len());
    for descriptor in nominal_copy_descriptors {
        if let Some(previous) = canonical_descriptors.last() {
            if previous.definition == descriptor.definition && previous.arguments == descriptor.arguments {
                if *previous != descriptor {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "lifetime-erased nominal copy layouts disagree",
                    });
                }
                continue;
            }
        }
        canonical_descriptors.push(descriptor);
    }
    let function = VmFunction {
        safety: function.safety,
        unsafe_execution: function.unsafe_execution,
        nominal_copy_descriptors: canonical_descriptors,
        definition: function.definition,
        captures: function.captures,
        parameters: function.parameters.len() as u32,
        registers,
        instructions,
    };
    Ok(CandidateVmArtifact {
        schema: STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        fingerprint: artifact_fingerprint(None, &function),
        function,
    })
}
fn retained_handler_depth(instructions: &[MirInstruction]) -> u32 {
    instructions
        .iter()
        .fold(0i64, |depth, instruction| match instruction {
            MirInstruction::InstallHandler { .. } => depth + 1,
            MirInstruction::UninstallHandler => depth - 1,
            _ => depth,
        })
        .max(0) as u32
}

/// Compute the normal-control half of a function's ABI before it crosses the
/// VM boundary. Dynamic `Perform` dispatch can transfer to an ancestor, but
/// it never makes a terminal Trap fall through to a syntactically following
/// Return. Keeping this small reachability proof in the emitter prevents a
/// coerced bottom tail from being advertised as a normal Unit return.
fn vm_instructions_may_return(instructions: &[VmInstruction]) -> bool {
    !reachable_return_values(instructions).is_empty()
}

fn reachable_return_values(instructions: &[VmInstruction]) -> Vec<u32> {
    let mut pending = vec![0u32];
    let mut seen = BTreeSet::new();
    let mut values = BTreeSet::new();
    while let Some(pc) = pending.pop() {
        if !seen.insert(pc) {
            continue;
        }
        let Some(instruction) = instructions.get(pc as usize) else {
            continue;
        };
        match instruction {
            VmInstruction::Return { value } => {
                values.insert(*value);
            }
            VmInstruction::Trap
            | VmInstruction::Resume { .. }
            | VmInstruction::Forward
            | VmInstruction::Cancel => {}
            VmInstruction::Jump { target }
            | VmInstruction::MakeLabel { target, .. }
            | VmInstruction::Leave { target, .. } => pending.push(*target),
            VmInstruction::BranchBool {
                then_target,
                else_target,
                ..
            } => {
                pending.push(*then_target);
                pending.push(*else_target);
            }
            // `ResumeReturn` may resume a callee and then return to its
            // clause. Its local fallthrough is therefore still an ordinary
            // executable continuation for this function.
            _ => pending.push(pc.saturating_add(1)),
        }
    }
    values.into_iter().collect()
}

fn edge_length(arguments: &[MirLocal], target: &crate::mir::MirBlock) -> u32 {
    parallel_edge_transfers(arguments, target)
        .iter()
        .map(|transfer| match transfer {
            EdgeTransfer::Direct { .. } => 1,
            // Save one source, rotate every remaining assignment, then write
            // the saved value into the first destination.
            EdgeTransfer::Cycle(transfers) => transfers.len() + 1,
        })
        .sum::<usize>() as u32
        + 1
}
fn target_index(target: u32, starts: &[u32]) -> Result<usize, VmArtifactError> {
    starts
        .iter()
        .position(|start| *start == target)
        .ok_or(VmArtifactError::UnsupportedControlFlow)
}
/// Materialize a CFG edge with the minimal temporary set required for its
/// parallel assignments. Acyclic moves are ordered destination-first, so a
/// write never destroys an unread source. Each remaining cycle saves exactly
/// one source before rotating its assignments. This preserves the MIR's
/// parallel edge-argument semantics without allocating one register per edge
/// argument.
fn emit_edge(
    arguments: &[MirLocal],
    target: &crate::mir::MirBlock,
    destination: u32,
    registers: &mut Vec<VmType>,
    instructions: &mut Vec<VmInstruction>,
) {
    for transfer in parallel_edge_transfers(arguments, target) {
        match transfer {
            // An edge argument transfers ownership from its predecessor into
            // the target block parameter. The predecessor terminates here, so
            // emitting Copy is both unnecessary and invalid for affine values
            // such as source bundles or diagnostic buffers.
            EdgeTransfer::Direct { dst, src } => instructions.push(VmInstruction::Move {
                dst: dst.0,
                src: src.0,
            }),
            EdgeTransfer::Cycle(transfers) => {
                let (first_destination, first_source) = transfers[0];
                let temporary = registers.len() as u32;
                registers.push(registers[first_source.0 as usize].clone());
                instructions.push(VmInstruction::Move {
                    dst: temporary,
                    src: first_source.0,
                });
                for &(destination, source) in transfers.iter().skip(1) {
                    instructions.push(VmInstruction::Move {
                        dst: destination.0,
                        src: source.0,
                    });
                }
                instructions.push(VmInstruction::Move {
                    dst: first_destination.0,
                    src: temporary,
                });
            }
        }
    }
    instructions.push(VmInstruction::Jump {
        target: destination,
    });
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum EdgeTransfer {
    Direct { dst: MirLocal, src: MirLocal },
    /// Ordered as `destination <- source`. The first source is saved before
    /// the remaining transfers rotate values around the cycle.
    Cycle(Vec<(MirLocal, MirLocal)>),
}

/// Build a deterministic schedule for one MIR parallel edge assignment.
///
/// Target block parameters are distinct by MIR validation. After repeatedly
/// removing a destination that no remaining transfer reads, every remaining
/// component is a bijective directed cycle; duplicated sources necessarily
/// peel into the acyclic portion first. `BTreeMap` makes both categories
/// stable across host iteration order.
fn parallel_edge_transfers(
    arguments: &[MirLocal],
    target: &crate::mir::MirBlock,
) -> Vec<EdgeTransfer> {
    let mut pending = arguments
        .iter()
        .zip(&target.parameters)
        .filter_map(|(&source, &destination)| (source != destination).then_some((destination, source)))
        .collect::<BTreeMap<_, _>>();
    let mut transfers = Vec::new();
    while let Some((&destination, &source)) = pending.iter().find(|(destination, _)| {
        !pending.values().any(|source| source == *destination)
    }) {
        pending.remove(&destination);
        transfers.push(EdgeTransfer::Direct { dst: destination, src: source });
    }
    while let Some(&start) = pending.keys().next() {
        let mut cycle = Vec::new();
        let mut destination = start;
        loop {
            let source = pending
                .remove(&destination)
                .expect("unpeeled parallel edge transfer must form a cycle");
            cycle.push((destination, source));
            destination = source;
            if destination == start {
                break;
            }
        }
        transfers.push(EdgeTransfer::Cycle(cycle));
    }
    transfers
}
pub fn verify(artifact: CandidateVmArtifact) -> Result<VerifiedVmArtifact, VmArtifactError> {
    if artifact.schema != STAGE0_VM_SCHEMA {
        return Err(VmArtifactError::UnsupportedSchema {
            found: artifact.schema,
        });
    }
    if artifact.fingerprint != artifact.computed_fingerprint() {
        return Err(VmArtifactError::FingerprintMismatch);
    }
    // A standalone artifact is executed by `VerifiedVmArtifact` through the
    // zero-argument entrypoint. Parameterized functions belong in a verified
    // program, whose caller supplies and verifies their argument values. Do
    // not let a parameterized function cross this boundary: its initially
    // readable verifier registers would otherwise be absent at runtime.
    if artifact.function.parameters != 0 {
        return Err(VmArtifactError::CallArity {
            expected: artifact.function.parameters,
            found: 0,
        });
    }
    verify_function(&artifact.function)?;
    Ok(VerifiedVmArtifact { artifact })
}
pub fn emit_program(program: &MirProgram) -> Result<CandidateVmProgram, VmArtifactError> {
    if let Err(message) = program.validate() {
        // Keep the exact failed invariant visible to the seed compiler while
        // porting new self-hosted source shapes. The artifact API below still
        // returns stable public categories once this diagnostic has been
        // classified.
        eprintln!("stage0 MIR program validation: {message}");
        return Err(VmArtifactError::MalformedEncoding {
            // The public artifact format intentionally has stable error
            // categories; service retains the detailed lowering diagnostic.
            message: if message.contains("call targets missing function") {
                "MIR program has an unstaged call target"
            } else if message.contains("dead/uninitialized") {
                "MIR program has invalid source-storage liveness"
            } else {
                "MIR program failed structural validation"
            },
        });
    }
    let specialized_lifted_target_owners =
        program.specialized_lifted_target_owners().map_err(|_| {
            VmArtifactError::MissingFunction {
                definition: program.entry,
            }
        })?;
    let specialized_lifted_targets = specialized_lifted_target_owners
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut functions = program
        .functions
        .iter()
        .map(|(definition, function)| {
            Ok((
                *definition,
                emit_with_specialized_lifted_targets(function, &specialized_lifted_targets)?
                    .function,
            ))
        })
        .collect::<Result<BTreeMap<_, _>, VmArtifactError>>()?;
    // A generic lifted body receives a materialized executable key. Preserve
    // the enclosing instance fingerprint alongside its lexical environment
    // so independently decoded bytecode can recompute that key instead of
    // trusting the instruction's `callee` field as an advisory pointer.
    for function in functions.values_mut() {
        for instruction in &mut function.instructions {
            let VmInstruction::MakeCallable {
                callee,
                environment: Some(environment),
                ..
            } = instruction
            else {
                continue;
            };
            environment.instance = specialized_lifted_target_owners
                .get(callee)
                .map(|owner| owner.fingerprint());
        }
    }
    let host_capabilities = reachable_host_capabilities(program.entry, &functions);
    let mut callable_environments = BTreeMap::new();
    for function in functions.values() {
        for instruction in &function.instructions {
            let VmInstruction::MakeCallable {
                callee,
                environment: Some(environment),
                ..
            } = instruction
            else {
                continue;
            };
            if let Some(previous) = callable_environments.insert(*callee, environment.clone())
                && previous != *environment
            {
                return Err(VmArtifactError::InvalidCallableEnvironment {
                    message: "lifted callable has conflicting sealed environments",
                });
            }
        }
    }
    Ok(CandidateVmProgram {
        schema: STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: host_capabilities.clone(),
        entry: program.entry,
        fingerprint: program_fingerprint(
            program.entry,
            None,
            &host_capabilities,
            &functions,
            &callable_environments,
        ),
        functions,
        callable_environments,
    })
}
fn vm_nominal_copy_descriptor(
    descriptor: &crate::mir::MirNominalCopyDescriptor,
) -> Result<VmNominalCopyDescriptor, VmArtifactError> {
    Ok(VmNominalCopyDescriptor {
        is_enum: descriptor.is_enum,
        definition: descriptor.definition,
        arguments: descriptor
            .arguments
            .iter()
            .filter(|argument| !matches!(argument, GenericArgument::Lifetime(_)))
            .map(vm_nominal_argument)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|ty| VmArtifactError::UnsupportedType { local: 0, ty })?,
        variants: descriptor
            .variants
            .iter()
            .map(|variant| {
                variant
                    .iter()
                    .map(vm_type)
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|ty| VmArtifactError::UnsupportedType { local: 0, ty })
            })
            .collect::<Result<Vec<_>, _>>()?,
    })
}
fn vm_type(value: &Type) -> Result<VmType, Box<Type>> {
    match value {
        // Bottom has no inhabitant at runtime. It still needs a structural
        // register type so a terminal `Perform` can cross a caller-installed
        // handler frame before the terminal clause cancels that frame.
        Type::Unit | Type::Never => Ok(VmType::Unit),
        Type::Scalar(ScalarType::I64) => Ok(VmType::I64),
        Type::Scalar(ScalarType::Usize) => Ok(VmType::Usize),
        Type::Scalar(ScalarType::U32) => Ok(VmType::U32),
        Type::Scalar(ScalarType::U8) => Ok(VmType::U8),
        Type::Scalar(ScalarType::U16) => Ok(VmType::U16),
        Type::Scalar(ScalarType::I16) => Ok(VmType::I16),
        Type::Scalar(ScalarType::I32) => Ok(VmType::I32),
        Type::Scalar(ScalarType::I8) => Ok(VmType::I8),
        Type::Scalar(ScalarType::U64) => Ok(VmType::U64),
        Type::Scalar(ScalarType::Isize) => Ok(VmType::Isize),
        Type::Scalar(ScalarType::U128) => Ok(VmType::U128),
        Type::Scalar(ScalarType::I128) => Ok(VmType::I128),
        Type::Scalar(ScalarType::F32) => Ok(VmType::F32),
        Type::Scalar(ScalarType::F64) => Ok(VmType::F64),
        Type::Scalar(ScalarType::Bool) => Ok(VmType::Bool),
        Type::Scalar(ScalarType::Char) => Ok(VmType::Char),
        Type::Scalar(ScalarType::Text) => Ok(VmType::Text),
        Type::Scalar(ScalarType::Bytes) => Ok(VmType::Bytes),
        Type::Generic(index) => Ok(VmType::Generic(*index)),
        Type::ConstU32(value) => Ok(VmType::ConstU32(*value)),
        Type::ConstQuantity(value) => Ok(VmType::ConstQuantity {
            lower: value.lower,
            upper: value.upper,
        }),
        Type::ConstGeneric { index, kind } => Ok(VmType::ConstGeneric {
            index: *index,
            kind: *kind,
        }),
        Type::Array(element) => Ok(VmType::Array(Box::new(vm_type(element)?))),
        Type::StaticData {
            element,
            tag,
            alignment,
        } => Ok(VmType::StaticData {
            element: Box::new(vm_type(element)?),
            tag: *tag,
            alignment: *alignment,
        }),
        Type::Tuple(values) => Ok(VmType::Tuple(
            values.iter().map(vm_type).collect::<Result<Vec<_>, _>>()?,
        )),
        Type::Nominal {
            definition,
            arguments,
        } => Ok(VmType::Nominal {
            definition: *definition,
            arguments: arguments
                .iter()
                // Regions constrain source validity and field substitution,
                // but carry no runtime representation. Keeping them out of
                // the VM nominal layout makes `T<'a>` and `T<'b>` the same
                // value shape without weakening compiler-side lifetime
                // checks.
                .filter(|argument| !matches!(argument, GenericArgument::Lifetime(_)))
                .map(vm_nominal_argument)
                .collect::<Result<Vec<_>, _>>()?,
        }),
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            safety,
            ..
        } => {
            // A callable value owns its HRTB binder. Bytecode deliberately
            // has no region universe, so lower that callable's effect
            // metadata under the same opening used for its lifted body.
            // Retaining the raw row would preserve `Bound` lifetime arguments
            // in a VM effect identity after the source binder ceased to exist.
            let effects = if *lifetime_binders == 0 {
                effects.clone()
            } else {
                crate::core::open_hrtb_callable_body_effect_row(effects.clone(), 0)
            };
            Ok(VmType::Callable {
                safety: *safety,
                parameters: parameters
                    .iter()
                    .map(vm_type)
                    .collect::<Result<Vec<_>, _>>()?,
                result: Box::new(vm_type(result)?),
                effects: Box::new(vm_effect_row(&effects)?),
            })
        }
        Type::RawPointer { mutability, pointee } => Ok(VmType::RawPointer {
            mutability: *mutability,
            pointee: Box::new(vm_type(pointee)?),
        }),
        Type::Reference {
            mutability,
            referent,
            ..
        } => Ok(VmType::Reference {
            unique: matches!(mutability, crate::types::Mutability::Unique),
            referent: Box::new(vm_type(referent)?),
        }),
        value => Err(Box::new(value.clone())),
    }
}

fn vm_scalar_type(value: ScalarType) -> VmType {
    vm_type(&Type::Scalar(value))
        .expect("all runtime float ABI scalars are representable in the VM")
}

fn encode_integer_scalar(value: ScalarType) -> Option<u8> {
    Some(match value {
        ScalarType::U8 => 0,
        ScalarType::U16 => 1,
        ScalarType::U32 => 2,
        ScalarType::U64 => 3,
        ScalarType::U128 => 4,
        ScalarType::Usize => 5,
        ScalarType::I8 => 6,
        ScalarType::I16 => 7,
        ScalarType::I32 => 8,
        ScalarType::I64 => 9,
        ScalarType::I128 => 10,
        ScalarType::Isize => 11,
        _ => return None,
    })
}

fn decode_integer_scalar(value: u8) -> Result<ScalarType, VmArtifactError> {
    Ok(match value {
        0 => ScalarType::U8,
        1 => ScalarType::U16,
        2 => ScalarType::U32,
        3 => ScalarType::U64,
        4 => ScalarType::U128,
        5 => ScalarType::Usize,
        6 => ScalarType::I8,
        7 => ScalarType::I16,
        8 => ScalarType::I32,
        9 => ScalarType::I64,
        10 => ScalarType::I128,
        11 => ScalarType::Isize,
        _ => {
            return Err(VmArtifactError::MalformedEncoding {
                message: "invalid integer runtime scalar",
            });
        }
    })
}

fn integer_scalar_bit_width(scalar: ScalarType) -> u32 {
    match scalar {
        ScalarType::U8 | ScalarType::I8 => 8,
        ScalarType::U16 | ScalarType::I16 => 16,
        ScalarType::U32 | ScalarType::I32 => 32,
        ScalarType::U64 | ScalarType::I64 | ScalarType::Usize | ScalarType::Isize => 64,
        ScalarType::U128 | ScalarType::I128 => 128,
        _ => unreachable!("integer intrinsic scalar was validated before execution"),
    }
}

fn memory_intrinsic_signature(primitive: MemoryPrimitive, types: &[VmType])
    -> Result<(Vec<VmType>, VmType), VmArtifactError>
{
    let signature = primitive.signature();
    let indices = primitive.type_generic_indices();
    if indices.len() != types.len() {
        return Err(VmArtifactError::MalformedEncoding { message: "memory operation has the wrong type arity" });
    }
    types.iter().try_for_each(validate_vm_type)?;
    let bindings = indices.into_iter().zip(types.iter().cloned()).collect();
    let convert = |ty: &Type| vm_type(ty).map(|ty| instantiate_vm_type(&ty, &bindings))
        .map_err(|ty| VmArtifactError::UnsupportedType { local: 0, ty });
    Ok((signature.parameters.iter().map(convert).collect::<Result<_, _>>()?, convert(&signature.result)?))
}

fn require_execution_contract(function: &VmFunction, budget: &ExecutionBudget) -> Result<(), VmArtifactError> {
    if !budget.unsafe_execution && (function.safety == Safety::Unsafe || function.unsafe_execution) {
        return Err(VmArtifactError::UnsafeExecutionRequiresUnsafeApi);
    }
    Ok(())
}

fn integer_intrinsic_signature(
    primitive: PrimitiveRole,
    scalar: ScalarType,
) -> Result<(Vec<ScalarType>, ScalarType), VmArtifactError> {
    if encode_integer_scalar(scalar).is_none() {
        return Err(VmArtifactError::MalformedEncoding {
            message: "integer runtime primitive has a non-integer scalar",
        });
    }
    primitive
        .integer_scalar_signature(scalar)
        .ok_or(VmArtifactError::MalformedEncoding {
            message: "non-integer primitive used by integer runtime opcode",
        })
}

/// Lower a Core effect row into its source-free, canonical VM identity.  The
/// same representation is used for protocol arguments and callable ABI rows;
/// keeping one conversion prevents the two frozen contracts from drifting.
fn vm_effect_row(value: &crate::types::EffectRow) -> Result<VmEffectRow, Box<Type>> {
    let value = value.clone().canonicalized();
    Ok(VmEffectRow {
        effects: value
            .effects
            .iter()
            .map(|instance| {
                Ok::<VmEffectInstance, Box<Type>>(VmEffectInstance {
                    definition: instance.definition,
                    arguments: instance
                        .arguments
                        .iter()
                        .map(vm_effect_generic_argument)
                        .collect::<Result<_, _>>()?,
                })
            })
            .collect::<Result<_, _>>()?,
        projections: value
            .projections
            .iter()
            .map(|projection| {
                Ok::<VmEffectRowProjection, Box<Type>>(VmEffectRowProjection {
                    subject: vm_type(&projection.subject)?,
                    trait_definition: projection.trait_definition,
                    trait_arguments: projection
                        .trait_arguments
                        .iter()
                        .map(vm_effect_generic_argument)
                        .collect::<Result<_, _>>()?,
                    name: projection.name.clone(),
                    item_arguments: projection
                        .item_arguments
                        .iter()
                        .map(vm_effect_generic_argument)
                        .collect::<Result<_, _>>()?,
                })
            })
            .collect::<Result<_, _>>()?,
        tail: value.tail,
    })
}

fn vm_effect_generic_argument(
    value: &crate::GenericArgument,
) -> Result<VmGenericArgument, Box<Type>> {
    use crate::GenericArgument;

    Ok(match value {
        GenericArgument::Type(value) => VmGenericArgument::Type(vm_type(value)?),
        GenericArgument::EffectRow(value) => VmGenericArgument::EffectRow(vm_effect_row(value)?),
        GenericArgument::Lifetime(value) => VmGenericArgument::Lifetime(*value),
        GenericArgument::ConstU32(value) => VmGenericArgument::ConstU32(*value),
        GenericArgument::ConstU32Expr(value) => VmGenericArgument::ConstU32Expr(value.clone()),
        GenericArgument::ConstQuantity(value) => VmGenericArgument::ConstQuantity {
            lower: value.lower,
            upper: value.upper,
        },
        GenericArgument::ConstGeneric { index, kind } => VmGenericArgument::ConstGeneric {
            index: *index,
            kind: *kind,
        },
        GenericArgument::ConstProjection { .. } | GenericArgument::ConstInfer { .. } => {
            return Err(Box::new(Type::Error));
        }
    })
}

/// VM nominal layouts remain type-shaped. Mixed-kind nominal identity is
/// retained in Core/instance products, but a row or lifetime must never be
/// coerced into a layout slot while emitting an executable artifact.
fn vm_nominal_argument(value: &GenericArgument) -> Result<VmType, Box<Type>> {
    match value {
        GenericArgument::Type(value) => vm_type(value),
        GenericArgument::ConstU32(value) => vm_type(&Type::ConstU32(*value)),
        GenericArgument::ConstU32Expr(value) => Ok(VmType::ConstU32Expr(value.clone())),
        GenericArgument::ConstQuantity(value) => vm_type(&Type::ConstQuantity(*value)),
        GenericArgument::ConstGeneric { index, kind } => vm_type(&Type::ConstGeneric {
            index: *index,
            kind: *kind,
        }),
        GenericArgument::ConstProjection { .. } => Err(Box::new(Type::Error)),
        GenericArgument::EffectRow(_)
        | GenericArgument::Lifetime(_)
        | GenericArgument::ConstInfer { .. } => Err(Box::new(Type::Error)),
    }
}

fn vm_effect_argument(
    effect: DefKey,
    value: &crate::GenericArgument,
) -> Result<VmGenericArgument, VmArtifactError> {
    use crate::GenericArgument;

    Ok(match value {
        GenericArgument::Type(value) => VmGenericArgument::Type(
            vm_type(value)
                .map_err(|ty| VmArtifactError::UnsupportedEffectArgumentType { effect, ty })?,
        ),
        GenericArgument::EffectRow(value) => {
            let value = value.clone().canonicalized();
            VmGenericArgument::EffectRow(VmEffectRow {
                effects: value
                    .effects
                    .iter()
                    .map(|instance| {
                        Ok(VmEffectInstance {
                            definition: instance.definition,
                            arguments: instance
                                .arguments
                                .iter()
                                .map(|argument| vm_effect_argument(instance.definition, argument))
                                .collect::<Result<_, _>>()?,
                        })
                    })
                    .collect::<Result<_, _>>()?,
                projections: value
                    .projections
                    .iter()
                    .map(|projection| {
                        Ok(VmEffectRowProjection {
                            subject: vm_type(&projection.subject).map_err(|ty| {
                                VmArtifactError::UnsupportedEffectArgumentType { effect, ty }
                            })?,
                            trait_definition: projection.trait_definition,
                            trait_arguments: projection
                                .trait_arguments
                                .iter()
                                .map(|argument| vm_effect_argument(effect, argument))
                                .collect::<Result<_, _>>()?,
                            name: projection.name.clone(),
                            item_arguments: projection
                                .item_arguments
                                .iter()
                                .map(|argument| vm_effect_argument(effect, argument))
                                .collect::<Result<_, _>>()?,
                        })
                    })
                    .collect::<Result<_, _>>()?,
                tail: value.tail,
            })
        }
        GenericArgument::Lifetime(value) => VmGenericArgument::Lifetime(*value),
        GenericArgument::ConstU32(value) => VmGenericArgument::ConstU32(*value),
        GenericArgument::ConstU32Expr(value) => VmGenericArgument::ConstU32Expr(value.clone()),
        GenericArgument::ConstQuantity(value) => VmGenericArgument::ConstQuantity {
            lower: value.lower,
            upper: value.upper,
        },
        GenericArgument::ConstGeneric { index, kind } => VmGenericArgument::ConstGeneric {
            index: *index,
            kind: *kind,
        },
        GenericArgument::ConstProjection { .. } => {
            return Err(VmArtifactError::UnsupportedEffectArgumentType {
                effect,
                ty: Box::new(Type::Error),
            });
        }
        GenericArgument::ConstInfer { .. } => {
            return Err(VmArtifactError::UnsupportedEffectArgumentType {
                effect,
                ty: Box::new(Type::Error),
            });
        }
    })
}
fn encode_type(value: &VmType, output: &mut Vec<u8>) {
    output.push(match value {
        VmType::Unit => 0,
        VmType::I64 => 1,
        VmType::Usize => 16,
        VmType::U32 => 17,
        VmType::U8 => 19,
        VmType::U16 => 20,
        VmType::I16 => 21,
        VmType::I32 => 22,
        VmType::I8 => 23,
        VmType::U64 => 24,
        VmType::Isize => 25,
        VmType::U128 => 26,
        VmType::I128 => 27,
        VmType::F32 => 28,
        VmType::F64 => 2,
        VmType::Bool => 3,
        VmType::Char => 4,
        VmType::Text => 5,
        VmType::Bytes => 18,
        VmType::Generic(_) => 9,
        VmType::Array(_) => 10,
        VmType::Callable { safety: Safety::Safe, .. } => 6,
        VmType::Callable { safety: Safety::Unsafe, .. } => 30,
        VmType::RawPointer { .. } => 31,
        VmType::Tuple(_) => 7,
        VmType::Nominal { .. } => 8,
        VmType::Reference { .. } => 11,
        VmType::ConstU32(_) => 12,
        VmType::ConstU32Expr(_) => 13,
        VmType::ConstQuantity { .. } => 14,
        VmType::ConstGeneric { .. } => 15,
        VmType::StaticData { .. } => 29,
    });
    match value {
        VmType::Callable {
            parameters,
            result,
            effects,
            ..
        } => {
            output.extend_from_slice(&(parameters.len() as u64).to_le_bytes());
            for parameter in parameters {
                encode_type(parameter, output);
            }
            encode_type(result, output);
            encode_vm_effect_row(effects, output);
        }
        VmType::Tuple(fields) => {
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for field in fields {
                encode_type(field, output);
            }
        }
        VmType::Nominal {
            definition,
            arguments,
        } => {
            output.extend_from_slice(&definition.0.as_bytes());
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                encode_type(argument, output);
            }
        }
        VmType::RawPointer { mutability, pointee } => {
            output.push(u8::from(*mutability == PointerMutability::Mut));
            encode_type(pointee, output);
        }
        VmType::Generic(index) => output.extend_from_slice(&index.to_le_bytes()),
        VmType::ConstU32(value) => output.extend_from_slice(&value.to_le_bytes()),
        VmType::ConstU32Expr(value) => encode_vm_structural_u32_expr(value, output),
        VmType::ConstQuantity { lower, upper } => {
            output.extend_from_slice(&lower.to_le_bytes());
            match upper {
                Some(upper) => {
                    output.push(0);
                    output.extend_from_slice(&upper.to_le_bytes());
                }
                None => output.push(1),
            }
        }
        VmType::ConstGeneric { index, kind } => {
            output.extend_from_slice(&index.to_le_bytes());
            output.push(encode_const_kind(*kind));
        }
        VmType::Reference { unique, referent } => {
            output.push(*unique as u8);
            encode_type(referent, output);
        }
        VmType::StaticData {
            element,
            tag,
            alignment,
        } => {
            encode_type(element, output);
            output.extend_from_slice(&tag.to_le_bytes());
            output.extend_from_slice(&alignment.to_le_bytes());
        }
        VmType::Array(element) => encode_type(element, output),
        _ => {}
    }
}

fn encode_const_kind(kind: ConstKind) -> u8 {
    match kind {
        ConstKind::U32 => 0,
        ConstKind::Quantity => 1,
    }
}

fn decode_const_kind(tag: u8) -> Result<ConstKind, VmArtifactError> {
    match tag {
        0 => Ok(ConstKind::U32),
        1 => Ok(ConstKind::Quantity),
        _ => Err(VmArtifactError::MalformedEncoding {
            message: "invalid const generic kind",
        }),
    }
}

fn encode_vm_structural_u32_expr(value: &StructuralU32Expr, output: &mut Vec<u8>) {
    match value {
        StructuralU32Expr::Literal(value) => {
            output.push(0);
            output.extend_from_slice(&value.to_le_bytes());
        }
        StructuralU32Expr::Param(value) => {
            output.push(1);
            output.extend_from_slice(&value.to_le_bytes());
        }
        StructuralU32Expr::Add(left, right) => {
            output.push(2);
            encode_vm_structural_u32_expr(left, output);
            encode_vm_structural_u32_expr(right, output);
        }
        StructuralU32Expr::Sub(left, right) => {
            output.push(3);
            encode_vm_structural_u32_expr(left, output);
            encode_vm_structural_u32_expr(right, output);
        }
        StructuralU32Expr::Mul(left, right) => {
            output.push(4);
            encode_vm_structural_u32_expr(left, output);
            encode_vm_structural_u32_expr(right, output);
        }
        StructuralU32Expr::Div(left, right) => {
            output.push(5);
            encode_vm_structural_u32_expr(left, output);
            encode_vm_structural_u32_expr(right, output);
        }
        StructuralU32Expr::Rem(left, right) => {
            output.push(6);
            encode_vm_structural_u32_expr(left, output);
            encode_vm_structural_u32_expr(right, output);
        }
    }
}

fn encode_capture_environment(value: Option<&VmCaptureEnvironment>, output: &mut Vec<u8>) {
    match value {
        None => output.push(0),
        Some(value) => {
            output.push(1);
            output.extend_from_slice(&value.owner.0.as_bytes());
            output.extend_from_slice(&value.callable.to_le_bytes());
            encode_optional_digest(value.instance, output);
            output.extend_from_slice(&(value.captures.len() as u64).to_le_bytes());
            for capture in &value.captures {
                output.push(match capture.mode {
                    VmCaptureMode::SharedBorrow => 0,
                    VmCaptureMode::UniqueBorrow => 1,
                    VmCaptureMode::Copy => 2,
                    VmCaptureMode::Move => 3,
                });
                encode_type(&capture.ty, output);
            }
        }
    }
}

fn encode_vm_generic_argument(value: &VmGenericArgument, output: &mut Vec<u8>) {
    match value {
        VmGenericArgument::Type(value) => {
            output.push(0);
            encode_type(value, output);
        }
        VmGenericArgument::EffectRow(value) => {
            output.push(1);
            encode_vm_effect_row(value, output);
        }
        VmGenericArgument::Lifetime(value) => {
            output.push(2);
            match value {
                Lifetime::Static => output.push(0),
                Lifetime::Generic(index) => {
                    output.push(1);
                    output.extend_from_slice(&index.to_le_bytes());
                }
                Lifetime::Bound { depth, index } => {
                    output.push(2);
                    output.extend_from_slice(&depth.to_le_bytes());
                    output.extend_from_slice(&index.to_le_bytes());
                }
                Lifetime::Elided => output.push(3),
            }
        }
        VmGenericArgument::ConstU32(value) => {
            output.push(3);
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmGenericArgument::ConstU32Expr(value) => {
            output.push(6);
            encode_vm_structural_u32_expr(value, output);
        }
        VmGenericArgument::ConstQuantity { lower, upper } => {
            output.push(4);
            output.extend_from_slice(&lower.to_le_bytes());
            match upper {
                Some(upper) => {
                    output.push(0);
                    output.extend_from_slice(&upper.to_le_bytes());
                }
                None => output.push(1),
            }
        }
        VmGenericArgument::ConstGeneric { index, kind } => {
            output.push(5);
            output.extend_from_slice(&index.to_le_bytes());
            output.push(encode_const_kind(*kind));
        }
    }
}

#[inline(never)]
fn encode_vm_effect_row(value: &VmEffectRow, output: &mut Vec<u8>) {
    output.extend_from_slice(&(value.effects.len() as u64).to_le_bytes());
    for effect in &value.effects {
        output.extend_from_slice(&effect.definition.0.as_bytes());
        encode_vm_generic_arguments(&effect.arguments, output);
    }
    output.extend_from_slice(&(value.projections.len() as u64).to_le_bytes());
    for projection in &value.projections {
        encode_type(&projection.subject, output);
        output.extend_from_slice(&projection.trait_definition.0.as_bytes());
        encode_vm_generic_arguments(&projection.trait_arguments, output);
        output.extend_from_slice(&(projection.name.len() as u64).to_le_bytes());
        output.extend_from_slice(projection.name.as_bytes());
        encode_vm_generic_arguments(&projection.item_arguments, output);
    }
    match value.tail {
        Some(EffectTail::Infer(variable)) => {
            output.push(0);
            output.extend_from_slice(&variable.0.to_le_bytes());
        }
        Some(EffectTail::Generic(index)) => {
            output.push(1);
            output.extend_from_slice(&index.to_le_bytes());
        }
        None => output.push(2),
    }
}

fn encode_vm_generic_arguments(values: &[VmGenericArgument], output: &mut Vec<u8>) {
    output.extend_from_slice(&(values.len() as u64).to_le_bytes());
    for value in values {
        encode_vm_generic_argument(value, output);
    }
}

fn vm_effect_instance_key(value: &VmEffectInstance) -> Vec<u8> {
    let mut output = value.definition.0.as_bytes().to_vec();
    encode_vm_generic_arguments(&value.arguments, &mut output);
    output
}

fn vm_effect_row_projection_key(value: &VmEffectRowProjection) -> Vec<u8> {
    let mut output = Vec::new();
    encode_type(&value.subject, &mut output);
    output.extend_from_slice(&value.trait_definition.0.as_bytes());
    encode_vm_generic_arguments(&value.trait_arguments, &mut output);
    output.extend_from_slice(&(value.name.len() as u64).to_le_bytes());
    output.extend_from_slice(value.name.as_bytes());
    encode_vm_generic_arguments(&value.item_arguments, &mut output);
    output
}

fn encode_optional_digest(value: Option<Digest>, output: &mut Vec<u8>) {
    match value {
        None => output.push(0),
        Some(value) => {
            output.push(1);
            output.extend_from_slice(&value.as_bytes());
        }
    }
}
fn artifact_fingerprint(runtime_manifest: Option<Digest>, function: &VmFunction) -> Digest {
    let mut bytes = b"grandiose-stage0-vm-v25".to_vec();
    encode_optional_digest(runtime_manifest, &mut bytes);
    encode_function(function, &mut bytes);
    Digest::of_bytes(&bytes)
}
fn program_fingerprint(
    entry: DefKey,
    runtime_manifest: Option<Digest>,
    host_capabilities: &[String],
    functions: &BTreeMap<DefKey, VmFunction>,
    callable_environments: &BTreeMap<DefKey, VmCaptureEnvironment>,
) -> Digest {
    let mut bytes = b"grandiose-stage0-vm-program-v26".to_vec();
    bytes.extend_from_slice(&entry.0.as_bytes());
    encode_optional_digest(runtime_manifest, &mut bytes);
    bytes.extend_from_slice(&(host_capabilities.len() as u64).to_le_bytes());
    for capability in host_capabilities {
        bytes.extend_from_slice(&(capability.len() as u64).to_le_bytes());
        bytes.extend_from_slice(capability.as_bytes());
    }
    for function in functions.values() {
        encode_function(function, &mut bytes);
    }
    for (callee, environment) in callable_environments {
        bytes.extend_from_slice(&callee.0.as_bytes());
        encode_capture_environment(Some(environment), &mut bytes);
    }
    Digest::of_bytes(&bytes)
}
fn encode_function(function: &VmFunction, output: &mut Vec<u8>) {
    output.extend_from_slice(&function.definition.0.as_bytes());
    output.push(u8::from(function.safety == Safety::Unsafe));
    output.push(u8::from(function.unsafe_execution));
    output.extend_from_slice(&function.captures.to_le_bytes());
    output.extend_from_slice(&function.parameters.to_le_bytes());
    output.extend_from_slice(&(function.registers.len() as u64).to_le_bytes());
    for register in &function.registers {
        encode_type(register, output);
    }
    output.extend_from_slice(&(function.nominal_copy_descriptors.len() as u64).to_le_bytes());
    for descriptor in &function.nominal_copy_descriptors {
        output.extend_from_slice(&descriptor.definition.0.as_bytes());
        output.push(u8::from(descriptor.is_enum));
        output.extend_from_slice(&(descriptor.arguments.len() as u64).to_le_bytes());
        for argument in &descriptor.arguments {
            encode_type(argument, output);
        }
        output.extend_from_slice(&(descriptor.variants.len() as u64).to_le_bytes());
        for variant in &descriptor.variants {
            output.extend_from_slice(&(variant.len() as u64).to_le_bytes());
            for field in variant {
                encode_type(field, output);
            }
        }
    }
    output.extend_from_slice(&(function.instructions.len() as u64).to_le_bytes());
    for instruction in &function.instructions {
        encode_instruction(instruction, output);
    }
}

fn vm_nominal_copy_descriptor_key(descriptor: &VmNominalCopyDescriptor) -> Vec<u8> {
    let mut output = descriptor.definition.0.as_bytes().to_vec();
    output.extend_from_slice(&(descriptor.arguments.len() as u64).to_le_bytes());
    for argument in &descriptor.arguments {
        encode_type(argument, &mut output);
    }
    output
}

struct Decoder<'a> {
    input: &'a [u8],
    index: usize,
}
impl<'a> Decoder<'a> {
    fn new(input: &'a [u8]) -> Self {
        Self { input, index: 0 }
    }
    fn remaining(&self) -> usize {
        self.input.len().saturating_sub(self.index)
    }
    fn bytes(&mut self, length: usize) -> Result<&'a [u8], VmArtifactError> {
        let end = self
            .index
            .checked_add(length)
            .filter(|end| *end <= self.input.len())
            .ok_or(VmArtifactError::MalformedEncoding {
                message: "truncated artifact",
            })?;
        let value = &self.input[self.index..end];
        self.index = end;
        Ok(value)
    }
    fn array(&mut self) -> Result<[u8; 32], VmArtifactError> {
        self.bytes(32)?
            .try_into()
            .map_err(|_| VmArtifactError::MalformedEncoding {
                message: "truncated digest",
            })
    }
    fn optional_digest(&mut self) -> Result<Option<Digest>, VmArtifactError> {
        match self.byte()? {
            0 => Ok(None),
            1 => Ok(Some(Digest::from_bytes(self.array()?))),
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "invalid optional manifest digest tag",
            }),
        }
    }
    fn byte(&mut self) -> Result<u8, VmArtifactError> {
        Ok(self.bytes(1)?[0])
    }
    fn boolean(&mut self) -> Result<bool, VmArtifactError> {
        match self.byte()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(VmArtifactError::MalformedEncoding { message: "invalid boolean tag" }),
        }
    }
    fn u32(&mut self) -> Result<u32, VmArtifactError> {
        Ok(u32::from_le_bytes(self.bytes(4)?.try_into().unwrap()))
    }
    fn u16(&mut self) -> Result<u16, VmArtifactError> {
        Ok(u16::from_le_bytes(self.bytes(2)?.try_into().unwrap()))
    }
    fn u64(&mut self) -> Result<u64, VmArtifactError> {
        Ok(u64::from_le_bytes(self.bytes(8)?.try_into().unwrap()))
    }
    fn u128(&mut self) -> Result<u128, VmArtifactError> {
        Ok(u128::from_le_bytes(self.bytes(16)?.try_into().unwrap()))
    }
    fn i8(&mut self) -> Result<i8, VmArtifactError> {
        Ok(i8::from_le_bytes(self.bytes(1)?.try_into().unwrap()))
    }
    fn i16(&mut self) -> Result<i16, VmArtifactError> {
        Ok(i16::from_le_bytes(self.bytes(2)?.try_into().unwrap()))
    }
    fn i32(&mut self) -> Result<i32, VmArtifactError> {
        Ok(i32::from_le_bytes(self.bytes(4)?.try_into().unwrap()))
    }
    fn i64(&mut self) -> Result<i64, VmArtifactError> {
        Ok(i64::from_le_bytes(self.bytes(8)?.try_into().unwrap()))
    }
    fn i128(&mut self) -> Result<i128, VmArtifactError> {
        Ok(i128::from_le_bytes(self.bytes(16)?.try_into().unwrap()))
    }
    fn count(&mut self, kind: &'static str, limit: u64) -> Result<usize, VmArtifactError> {
        let count = self.u64()?;
        if count > limit || count > usize::MAX as u64 {
            return Err(VmArtifactError::DecodeLimit { kind, limit });
        }
        Ok(count as usize)
    }
    fn vm_type(&mut self) -> Result<VmType, VmArtifactError> {
        self.vm_type_at_depth(0)
    }
    fn capture_environment(&mut self) -> Result<Option<VmCaptureEnvironment>, VmArtifactError> {
        match self.byte()? {
            0 => Ok(None),
            1 => {
                let owner = self.def_key()?;
                let callable = self.u32()?;
                let instance = self.optional_digest()?;
                let count = self.count("callable environment captures", MAX_DECODE_REGISTERS)?;
                let mut captures = Vec::with_capacity(count);
                for _ in 0..count {
                    let mode = match self.byte()? {
                        0 => VmCaptureMode::SharedBorrow,
                        1 => VmCaptureMode::UniqueBorrow,
                        2 => VmCaptureMode::Copy,
                        3 => VmCaptureMode::Move,
                        _ => {
                            return Err(VmArtifactError::MalformedEncoding {
                                message: "invalid callable capture mode",
                            });
                        }
                    };
                    captures.push(VmCapture {
                        mode,
                        ty: self.vm_type()?,
                    });
                }
                Ok(Some(VmCaptureEnvironment {
                    owner,
                    callable,
                    instance,
                    captures,
                }))
            }
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "invalid optional callable environment tag",
            }),
        }
    }
    fn vm_type_at_depth(&mut self, depth: u64) -> Result<VmType, VmArtifactError> {
        if depth > MAX_DECODE_TYPE_DEPTH {
            return Err(VmArtifactError::DecodeLimit {
                kind: "callable type nesting",
                limit: MAX_DECODE_TYPE_DEPTH,
            });
        }
        match self.byte()? {
            0 => Ok(VmType::Unit),
            1 => Ok(VmType::I64),
            16 => Ok(VmType::Usize),
            17 => Ok(VmType::U32),
            19 => Ok(VmType::U8),
            20 => Ok(VmType::U16),
            21 => Ok(VmType::I16),
            22 => Ok(VmType::I32),
            23 => Ok(VmType::I8),
            24 => Ok(VmType::U64),
            25 => Ok(VmType::Isize),
            26 => Ok(VmType::U128),
            27 => Ok(VmType::I128),
            28 => Ok(VmType::F32),
            2 => Ok(VmType::F64),
            3 => Ok(VmType::Bool),
            4 => Ok(VmType::Char),
            5 => Ok(VmType::Text),
            18 => Ok(VmType::Bytes),
            29 => Ok(VmType::StaticData {
                element: Box::new(self.vm_type_at_depth(depth + 1)?),
                tag: self.u128()?,
                alignment: self.u32()?,
            }),
            tag @ (6 | 30) => {
                let count = self.count("callable parameters", MAX_DECODE_REGISTERS)?;
                let mut parameters = Vec::with_capacity(count);
                for _ in 0..count {
                    parameters.push(self.vm_type_at_depth(depth + 1)?);
                }
                Ok(VmType::Callable {
                    safety: if tag == 6 { Safety::Safe } else { Safety::Unsafe },
                    parameters,
                    result: Box::new(self.vm_type_at_depth(depth + 1)?),
                    effects: Box::new(self.vm_effect_row_at_depth(depth + 1)?),
                })
            }
            31 => {
                let mutability = if self.boolean()? { PointerMutability::Mut } else { PointerMutability::Const };
                Ok(VmType::RawPointer { mutability, pointee: Box::new(self.vm_type_at_depth(depth + 1)?) })
            }
            7 => {
                let count = self.count("tuple fields", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(self.vm_type_at_depth(depth + 1)?);
                }
                Ok(VmType::Tuple(fields))
            }
            8 => {
                let definition = self.def_key()?;
                let count = self.count("nominal type arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.vm_type_at_depth(depth + 1)?);
                }
                Ok(VmType::Nominal {
                    definition,
                    arguments,
                })
            }
            9 => Ok(VmType::Generic(self.u32()?)),
            10 => Ok(VmType::Array(Box::new(self.vm_type_at_depth(depth + 1)?))),
            11 => Ok(VmType::Reference {
                unique: match self.byte()? {
                    0 => false,
                    1 => true,
                    _ => {
                        return Err(VmArtifactError::MalformedEncoding {
                            message: "invalid reference mutability",
                        });
                    }
                },
                referent: Box::new(self.vm_type_at_depth(depth + 1)?),
            }),
            12 => Ok(VmType::ConstU32(self.u32()?)),
            13 => Ok(VmType::ConstU32Expr(
                self.vm_structural_u32_expr(depth + 1)?,
            )),
            14 => {
                let lower = self.u64()?;
                let upper = self.quantity_upper()?;
                if upper.is_some_and(|upper| lower > upper) {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid quantity interval",
                    });
                }
                Ok(VmType::ConstQuantity { lower, upper })
            }
            15 => Ok(VmType::ConstGeneric {
                index: self.u32()?,
                kind: decode_const_kind(self.byte()?)?,
            }),
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "unknown VM register type",
            }),
        }
    }
    fn quantity_upper(&mut self) -> Result<Option<u64>, VmArtifactError> {
        match self.byte()? {
            0 => Ok(Some(self.u64()?)),
            1 => Ok(None),
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "invalid quantity upper-bound tag",
            }),
        }
    }
    fn vm_structural_u32_expr(&mut self, depth: u64) -> Result<StructuralU32Expr, VmArtifactError> {
        if depth > MAX_DECODE_TYPE_DEPTH {
            return Err(VmArtifactError::DecodeLimit {
                kind: "structural const nesting",
                limit: MAX_DECODE_TYPE_DEPTH,
            });
        }
        let binary = |decoder: &mut Self,
                      constructor: fn(
            Box<StructuralU32Expr>,
            Box<StructuralU32Expr>,
        ) -> StructuralU32Expr|
         -> Result<StructuralU32Expr, VmArtifactError> {
            Ok(constructor(
                Box::new(decoder.vm_structural_u32_expr(depth + 1)?),
                Box::new(decoder.vm_structural_u32_expr(depth + 1)?),
            ))
        };
        match self.byte()? {
            0 => Ok(StructuralU32Expr::Literal(self.u32()?)),
            1 => Ok(StructuralU32Expr::Param(self.u32()?)),
            2 => binary(self, StructuralU32Expr::Add),
            3 => binary(self, StructuralU32Expr::Sub),
            4 => binary(self, StructuralU32Expr::Mul),
            5 => binary(self, StructuralU32Expr::Div),
            6 => binary(self, StructuralU32Expr::Rem),
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "invalid structural u32 expression tag",
            }),
        }
    }
    fn vm_generic_arguments(&mut self) -> Result<Vec<VmGenericArgument>, VmArtifactError> {
        self.vm_generic_arguments_at_depth(0)
    }
    fn vm_generic_arguments_at_depth(
        &mut self,
        depth: u64,
    ) -> Result<Vec<VmGenericArgument>, VmArtifactError> {
        let count = self.count("effect protocol arguments", MAX_DECODE_REGISTERS)?;
        let mut values = Vec::with_capacity(count);
        for _ in 0..count {
            values.push(self.vm_generic_argument_at_depth(depth + 1)?);
        }
        Ok(values)
    }
    fn vm_generic_argument_at_depth(
        &mut self,
        depth: u64,
    ) -> Result<VmGenericArgument, VmArtifactError> {
        if depth > MAX_DECODE_TYPE_DEPTH {
            return Err(VmArtifactError::DecodeLimit {
                kind: "effect argument nesting",
                limit: MAX_DECODE_TYPE_DEPTH,
            });
        }
        match self.byte()? {
            0 => Ok(VmGenericArgument::Type(self.vm_type_at_depth(depth + 1)?)),
            1 => Ok(VmGenericArgument::EffectRow(
                self.vm_effect_row_at_depth(depth + 1)?,
            )),
            2 => Ok(VmGenericArgument::Lifetime(match self.byte()? {
                0 => Lifetime::Static,
                1 => Lifetime::Generic(self.u32()?),
                2 => Lifetime::Bound {
                    depth: self.u32()?,
                    index: self.u32()?,
                },
                3 => Lifetime::Elided,
                _ => {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid lifetime argument tag",
                    });
                }
            })),
            3 => Ok(VmGenericArgument::ConstU32(self.u32()?)),
            4 => {
                let lower = self.u64()?;
                let upper = self.quantity_upper()?;
                if upper.is_some_and(|upper| lower > upper) {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid quantity interval",
                    });
                }
                Ok(VmGenericArgument::ConstQuantity { lower, upper })
            }
            5 => {
                let index = self.u32()?;
                let kind = decode_const_kind(self.byte()?)?;
                Ok(VmGenericArgument::ConstGeneric { index, kind })
            }
            6 => Ok(VmGenericArgument::ConstU32Expr(
                self.vm_structural_u32_expr(depth + 1)?,
            )),
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "unknown VM effect argument tag",
            }),
        }
    }
    #[inline(never)]
    fn vm_effect_row_at_depth(&mut self, depth: u64) -> Result<VmEffectRow, VmArtifactError> {
        if depth > MAX_DECODE_TYPE_DEPTH {
            return Err(VmArtifactError::DecodeLimit {
                kind: "effect row nesting",
                limit: MAX_DECODE_TYPE_DEPTH,
            });
        }
        let effect_count = self.count("effect row instances", MAX_DECODE_REGISTERS)?;
        let mut effects = Vec::with_capacity(effect_count);
        for _ in 0..effect_count {
            effects.push(VmEffectInstance {
                definition: self.def_key()?,
                arguments: self.vm_generic_arguments_at_depth(depth + 1)?,
            });
        }
        let projection_count = self.count("effect row projections", MAX_DECODE_REGISTERS)?;
        let mut projections = Vec::with_capacity(projection_count);
        for _ in 0..projection_count {
            let subject = self.vm_type_at_depth(depth + 1)?;
            let trait_definition = self.def_key()?;
            let trait_arguments = self.vm_generic_arguments_at_depth(depth + 1)?;
            let name = self.text()?;
            let item_arguments = self.vm_generic_arguments_at_depth(depth + 1)?;
            projections.push(VmEffectRowProjection {
                subject,
                trait_definition,
                trait_arguments,
                name,
                item_arguments,
            });
        }
        let tail = match self.byte()? {
            0 => Some(EffectTail::Infer(crate::types::EffectVar(self.u32()?))),
            1 => Some(EffectTail::Generic(self.u32()?)),
            2 => None,
            _ => {
                return Err(VmArtifactError::MalformedEncoding {
                    message: "invalid effect row tail tag",
                });
            }
        };
        let row = VmEffectRow {
            effects,
            projections,
            tail,
        };
        if row
            .effects
            .windows(2)
            .any(|pair| vm_effect_instance_key(&pair[0]) >= vm_effect_instance_key(&pair[1]))
            || row.projections.windows(2).any(|pair| {
                vm_effect_row_projection_key(&pair[0]) >= vm_effect_row_projection_key(&pair[1])
            })
        {
            return Err(VmArtifactError::NonCanonicalEncoding);
        }
        Ok(row)
    }
    fn pattern(&mut self) -> Result<VmPattern, VmArtifactError> {
        self.pattern_at_depth(0)
    }
    fn pattern_at_depth(&mut self, depth: u64) -> Result<VmPattern, VmArtifactError> {
        if depth > MAX_DECODE_TYPE_DEPTH {
            return Err(VmArtifactError::DecodeLimit {
                kind: "pattern nesting",
                limit: MAX_DECODE_TYPE_DEPTH,
            });
        }
        match self.byte()? {
            0 => Ok(VmPattern::Any),
            1 => Ok(VmPattern::Literal(self.text()?)),
            2 => {
                let count = self.count("tuple pattern fields", MAX_DECODE_REGISTERS)?;
                let mut values = Vec::with_capacity(count);
                for _ in 0..count {
                    values.push(self.pattern_at_depth(depth + 1)?);
                }
                Ok(VmPattern::Tuple(values))
            }
            5 => {
                let element = self.vm_type_at_depth(depth + 1)?;
                let count = self.count("array pattern fields", MAX_DECODE_REGISTERS)?;
                let mut elements = Vec::with_capacity(count);
                for _ in 0..count {
                    elements.push(self.pattern_at_depth(depth + 1)?);
                }
                Ok(VmPattern::Array { element, elements })
            }
            tag @ (3 | 4) => {
                let definition = self.def_key()?;
                let variant = (tag == 4).then(|| self.u32()).transpose()?;
                let field_count = self.u32()?;
                let layout_count = self.count("nominal pattern layout", MAX_DECODE_REGISTERS)?;
                let mut field_types = Vec::with_capacity(layout_count);
                for _ in 0..layout_count {
                    field_types.push(self.vm_type_at_depth(depth + 1)?);
                }
                let count = self.count("nominal pattern fields", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(VmPatternField {
                        index: self.u32()?,
                        ty: self.vm_type_at_depth(depth + 1)?,
                        pattern: self.pattern_at_depth(depth + 1)?,
                    });
                }
                match variant {
                    Some(variant) => Ok(VmPattern::Enum {
                        definition,
                        variant,
                        field_types,
                        field_count,
                        fields,
                    }),
                    None => Ok(VmPattern::Record {
                        definition,
                        field_types,
                        field_count,
                        fields,
                    }),
                }
            }
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "unknown structural pattern tag",
            }),
        }
    }
    fn compare(&mut self) -> Result<VmCompare, VmArtifactError> {
        match self.byte()? {
            0 => Ok(VmCompare::Equal),
            1 => Ok(VmCompare::NotEqual),
            2 => Ok(VmCompare::Less),
            3 => Ok(VmCompare::LessEqual),
            4 => Ok(VmCompare::Greater),
            5 => Ok(VmCompare::GreaterEqual),
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "unknown comparison operator",
            }),
        }
    }
    fn def_key(&mut self) -> Result<DefKey, VmArtifactError> {
        Ok(DefKey(Digest::from_bytes(self.array()?)))
    }
    fn register_pair(&mut self) -> Result<(u32, u32), VmArtifactError> {
        Ok((self.u32()?, self.u32()?))
    }
    fn register_triple(&mut self) -> Result<(u32, u32, u32), VmArtifactError> {
        Ok((self.u32()?, self.u32()?, self.u32()?))
    }
    fn text(&mut self) -> Result<String, VmArtifactError> {
        let length = self.u64()?;
        if length > MAX_DECODE_TEXT_BYTES || length > usize::MAX as u64 {
            return Err(VmArtifactError::DecodeLimit {
                kind: "text literal bytes",
                limit: MAX_DECODE_TEXT_BYTES,
            });
        }
        String::from_utf8(self.bytes(length as usize)?.to_vec()).map_err(|_| {
            VmArtifactError::MalformedEncoding {
                message: "text literal is not valid UTF-8",
            }
        })
    }
    fn cleanup_proof(&mut self) -> Result<VmCleanupProof, VmArtifactError> {
        let moved_count = self.count("cleanup moved places", MAX_DECODE_REGISTERS)?;
        let mut moved_places = Vec::with_capacity(moved_count);
        for _ in 0..moved_count {
            let path = self.u32()?;
            let binding = self.u32()?;
            let root = self.text()?;
            let field_count = self.count("cleanup moved place fields", MAX_DECODE_REGISTERS)?;
            let mut fields = Vec::with_capacity(field_count);
            for _ in 0..field_count {
                fields.push(self.u32()?);
            }
            moved_places.push(VmCleanupPlace {
                path,
                binding,
                root,
                fields,
            });
        }
        let loan_count = self.count("cleanup active loans", MAX_DECODE_REGISTERS)?;
        let mut active_loans = Vec::with_capacity(loan_count);
        for _ in 0..loan_count {
            let owner = match self.byte()? {
                0 => None,
                1 => Some(self.text()?),
                _ => {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid cleanup loan owner tag",
                    });
                }
            };
            let binding = self.u32()?;
            let root = self.text()?;
            let field_count = self.count("cleanup loan fields", MAX_DECODE_REGISTERS)?;
            let mut fields = Vec::with_capacity(field_count);
            for _ in 0..field_count {
                fields.push(self.u32()?);
            }
            let unique = match self.byte()? {
                0 => false,
                1 => true,
                _ => {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid cleanup loan mutability",
                    });
                }
            };
            active_loans.push(VmCleanupLoan {
                owner,
                binding,
                root,
                fields,
                unique,
            });
        }
        Ok(VmCleanupProof {
            moved_places,
            active_loans,
            storage_erasure: self.storage_erasure_witness()?,
        })
    }
    fn storage_erasure_witness(&mut self) -> Result<VmStorageErasureWitness, VmArtifactError> {
        match self.byte()? {
            0 => Ok(VmStorageErasureWitness::Missing),
            1 => {
                let count = self.count("source-storage erasure storages", MAX_DECODE_REGISTERS)?;
                let mut storages = Vec::with_capacity(count);
                for _ in 0..count {
                    let storage = self.u32()?;
                    let binding = self.u32()?;
                    let value_register = self.u32()?;
                    let initialized = match self.byte()? {
                        0 => false,
                        1 => true,
                        _ => {
                            return Err(VmArtifactError::MalformedEncoding {
                                message: "invalid source-storage initialized tag",
                            });
                        }
                    };
                    let drop_flag = match self.byte()? {
                        0 => None,
                        1 => Some(self.u32()?),
                        _ => {
                            return Err(VmArtifactError::MalformedEncoding {
                                message: "invalid source-storage drop-flag tag",
                            });
                        }
                    };
                    storages.push(VmStorageErasureStorage {
                        storage,
                        binding,
                        value_register,
                        initialized,
                        drop_flag,
                    });
                }
                let count = self.count("source-storage erasure actions", MAX_DECODE_REGISTERS)?;
                let mut actions = Vec::with_capacity(count);
                for _ in 0..count {
                    actions.push(match self.byte()? {
                        0 => VmStorageErasureAction::EndBorrow {
                            storage: self.u32()?,
                        },
                        1 => VmStorageErasureAction::Protect {
                            storage: self.u32()?,
                            register: self.u32()?,
                        },
                        2 => VmStorageErasureAction::Destroy {
                            storage: self.u32()?,
                        },
                        3 => VmStorageErasureAction::SetDropFlag {
                            drop_flag: self.u32()?,
                            initialized: match self.byte()? {
                                0 => false,
                                1 => true,
                                _ => {
                                    return Err(VmArtifactError::MalformedEncoding {
                                        message: "invalid source-storage drop-flag state",
                                    });
                                }
                            },
                        },
                        4 => VmStorageErasureAction::StorageDead {
                            storage: self.u32()?,
                        },
                        _ => {
                            return Err(VmArtifactError::MalformedEncoding {
                                message: "unknown source-storage erasure action",
                            });
                        }
                    });
                }
                let count =
                    self.count("source-storage protected registers", MAX_DECODE_REGISTERS)?;
                let mut protected_registers = Vec::with_capacity(count);
                for _ in 0..count {
                    protected_registers.push(self.u32()?);
                }
                Ok(VmStorageErasureWitness::Verified {
                    storages,
                    actions,
                    protected_registers,
                })
            }
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "invalid source-storage erasure witness tag",
            }),
        }
    }
    fn function(&mut self) -> Result<VmFunction, VmArtifactError> {
        let definition = self.def_key()?;
        let safety = if self.boolean()? { Safety::Unsafe } else { Safety::Safe };
        let unsafe_execution = self.boolean()?;
        let captures = self.u32()?;
        let parameters = self.u32()?;
        let register_count = self.count("registers", MAX_DECODE_REGISTERS)?;
        let mut registers = Vec::with_capacity(register_count);
        for _ in 0..register_count {
            registers.push(self.vm_type()?);
        }
        let descriptor_count = self.count("nominal copy descriptors", MAX_DECODE_REGISTERS)?;
        let mut nominal_copy_descriptors = Vec::with_capacity(descriptor_count);
        for _ in 0..descriptor_count {
            let definition = self.def_key()?;
            let is_enum = self.boolean()?;
            let argument_count =
                self.count("nominal copy descriptor arguments", MAX_DECODE_REGISTERS)?;
            let mut arguments = Vec::with_capacity(argument_count);
            for _ in 0..argument_count {
                arguments.push(self.vm_type()?);
            }
            let variant_count =
                self.count("nominal copy descriptor variants", MAX_DECODE_REGISTERS)?;
            let mut variants = Vec::with_capacity(variant_count);
            for _ in 0..variant_count {
                let field_count =
                    self.count("nominal copy descriptor fields", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(field_count);
                for _ in 0..field_count {
                    fields.push(self.vm_type()?);
                }
                variants.push(fields);
            }
            nominal_copy_descriptors.push(VmNominalCopyDescriptor {
                is_enum,
                definition,
                arguments,
                variants,
            });
        }
        let instruction_count = self.count("instructions", MAX_DECODE_INSTRUCTIONS)?;
        let mut instructions = Vec::with_capacity(instruction_count);
        for _ in 0..instruction_count {
            instructions.push(self.instruction()?);
        }
        Ok(VmFunction {
            safety,
            unsafe_execution,
            nominal_copy_descriptors,
            definition,
            captures,
            parameters,
            registers,
            instructions,
        })
    }
    fn instruction(&mut self) -> Result<VmInstruction, VmArtifactError> {
        match self.byte()? {
            0 => Ok(VmInstruction::ConstI64 {
                dst: self.u32()?,
                value: self.i64()?,
            }),
            157 => Ok(VmInstruction::ConstU8 {
                dst: self.u32()?,
                value: self.byte()?,
            }),
            158 => Ok(VmInstruction::ConstU16 {
                dst: self.u32()?,
                value: self.u16()?,
            }),
            151 => Ok(VmInstruction::ConstU32 {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            152 => Ok(VmInstruction::ConstU64 {
                dst: self.u32()?,
                value: self.u64()?,
            }),
            159 => Ok(VmInstruction::ConstUsize {
                dst: self.u32()?,
                value: self.u64()?,
            }),
            160 => Ok(VmInstruction::ConstU128 {
                dst: self.u32()?,
                value: self.u128()?,
            }),
            161 => Ok(VmInstruction::ConstI8 {
                dst: self.u32()?,
                value: self.i8()?,
            }),
            162 => Ok(VmInstruction::ConstI16 {
                dst: self.u32()?,
                value: self.i16()?,
            }),
            163 => Ok(VmInstruction::ConstI32 {
                dst: self.u32()?,
                value: self.i32()?,
            }),
            164 => Ok(VmInstruction::ConstIsize {
                dst: self.u32()?,
                value: self.i64()?,
            }),
            165 => Ok(VmInstruction::ConstI128 {
                dst: self.u32()?,
                value: self.i128()?,
            }),
            1 => {
                let (dst, src) = self.register_pair()?;
                Ok(VmInstruction::Copy { dst, src })
            }
            2 => {
                let (dst, src) = self.register_pair()?;
                Ok(VmInstruction::Move { dst, src })
            }
            167 => Ok(VmInstruction::StorageLive {
                binding: self.u32()?,
                local: self.u32()?,
            }),
            168 => Ok(VmInstruction::StorageDead {
                binding: self.u32()?,
                local: self.u32()?,
            }),
            169 => {
                let flag = self.u32()?;
                let value = match self.byte()? {
                    0 => false,
                    1 => true,
                    _ => {
                        return Err(VmArtifactError::MalformedEncoding {
                            message: "invalid source-storage drop flag value",
                        });
                    }
                };
                Ok(VmInstruction::SetDropFlag { flag, value })
            }
            170 => Ok(VmInstruction::DestroyIf {
                local: self.u32()?,
                flag: self.u32()?,
            }),
            38 => {
                let (dst, src) = self.register_pair()?;
                Ok(VmInstruction::Store { dst, src })
            }
            52 => {
                let dst = self.u32()?;
                let src = self.u32()?;
                let unique = match self.byte()? {
                    0 => false,
                    1 => true,
                    _ => {
                        return Err(VmArtifactError::MalformedEncoding {
                            message: "invalid borrow mutability",
                        });
                    }
                };
                let reborrow = match self.byte()? {
                    0 => false,
                    1 => true,
                    _ => {
                        return Err(VmArtifactError::MalformedEncoding {
                            message: "invalid borrow reborrow mode",
                        });
                    }
                };
                let count = self.count("borrow field projections", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(self.u32()?);
                }
                Ok(VmInstruction::Borrow {
                    dst,
                    src,
                    fields,
                    unique,
                    reborrow,
                })
            }
            53 => Ok(VmInstruction::DerefCopy {
                dst: self.u32()?,
                reference: self.u32()?,
            }),
            54 => Ok(VmInstruction::DerefStore {
                reference: self.u32()?,
                src: self.u32()?,
            }),
            174 => Ok(VmInstruction::DerefMove {
                dst: self.u32()?,
                reference: self.u32()?,
            }),
            39 => Ok(VmInstruction::UpdateRecord {
                dst: self.u32()?,
                base: self.u32()?,
                index: self.u32()?,
                field_count: self.u32()?,
                value: self.u32()?,
                field_type: self.vm_type()?,
            }),
            40 => Ok(VmInstruction::PatternTest {
                dst: self.u32()?,
                subject: self.u32()?,
                pattern: self.pattern()?,
            }),
            41 => {
                let dst = self.u32()?;
                let effect = self.def_key()?;
                let effect_arguments = self.vm_generic_arguments()?;
                let operation = self.u32()?;
                let count = self.count("effect operation arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                Ok(VmInstruction::Perform {
                    dst,
                    effect,
                    effect_arguments,
                    operation,
                    arguments,
                })
            }
            42 => Ok(VmInstruction::ProjectTuple {
                dst: self.u32()?,
                base: self.u32()?,
                index: self.u32()?,
                field_count: self.u32()?,
                field_type: self.vm_type()?,
            }),
            57 => Ok(VmInstruction::ProjectArray {
                dst: self.u32()?,
                base: self.u32()?,
                index: self.u32()?,
                field_count: self.u32()?,
                element_type: self.vm_type()?,
            }),
            43 => Ok(VmInstruction::Trap),
            44 => {
                let effect = self.def_key()?;
                let effect_arguments = self.vm_generic_arguments()?;
                let operation = self.u32()?;
                let payload_count =
                    self.count("handler payload destinations", MAX_DECODE_REGISTERS)?;
                let mut payload_destinations = Vec::with_capacity(payload_count);
                for _ in 0..payload_count {
                    payload_destinations.push(self.u32()?);
                }
                Ok(VmInstruction::InstallHandler {
                    effect,
                    effect_arguments,
                    operation,
                    payload_destinations,
                    resume_type: self.vm_type()?,
                    continuation: match self.byte()? {
                        0 => VmContinuationPolicy::Consume,
                        1 => VmContinuationPolicy::Replay { uses: self.u32()? },
                        2 => VmContinuationPolicy::Terminal,
                        _ => {
                            return Err(VmArtifactError::MalformedEncoding {
                                message: "invalid handler continuation policy",
                            });
                        }
                    },
                    target: self.u32()?,
                })
            }
            45 => Ok(VmInstruction::UninstallHandler),
            46 => Ok(VmInstruction::Resume { value: self.u32()? }),
            51 => Ok(VmInstruction::ResumeReturn {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            47 => Ok(VmInstruction::Forward),
            69 => Ok(VmInstruction::Cancel),
            70 => Ok(VmInstruction::CaptureResumption { dst: self.u32()? }),
            50 => Ok(VmInstruction::ResumeSnapshot {
                snapshot: self.u32()?,
                value: self.u32()?,
            }),
            55 => {
                let brand_owner = self.def_key()?;
                let brand_label = self.u32()?;
                let handler_depth = self.u32()?;
                let target = self.u32()?;
                let count = self.count("leave arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                let destination_count = self.count("leave destinations", MAX_DECODE_REGISTERS)?;
                if destination_count != count {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "leave arguments and destinations differ in length",
                    });
                }
                let mut destinations = Vec::with_capacity(destination_count);
                for _ in 0..destination_count {
                    destinations.push(self.u32()?);
                }
                Ok(VmInstruction::Leave {
                    brand_owner,
                    brand_label,
                    handler_depth,
                    target,
                    arguments,
                    destinations,
                    cleanup: self.cleanup_proof()?,
                })
            }
            56 => {
                let dst = self.u32()?;
                let capability = self.text()?;
                let symbol = self.text()?;
                let parameter_count = self.count("host call parameters", MAX_DECODE_REGISTERS)?;
                let mut parameters = Vec::with_capacity(parameter_count);
                for _ in 0..parameter_count {
                    parameters.push(self.vm_type()?);
                }
                let result = self.vm_type()?;
                let count = self.count("host call arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                Ok(VmInstruction::HostCall {
                    dst,
                    capability,
                    symbol,
                    parameters,
                    result,
                    arguments,
                })
            }
            3 => self.i64_arithmetic(|dst, left, right| VmInstruction::AddI64 { dst, left, right }),
            104 => self.i64_arithmetic(|dst, left, right| VmInstruction::WrappingAddI64 {
                dst,
                left,
                right,
            }),
            106 => self.i64_arithmetic(|dst, left, right| VmInstruction::WrappingSubI64 {
                dst,
                left,
                right,
            }),
            107 => self.i64_arithmetic(|dst, left, right| VmInstruction::WrappingMulI64 {
                dst,
                left,
                right,
            }),
            105 => self.i64_arithmetic(|dst, left, right| VmInstruction::IntEqualI64 {
                dst,
                left,
                right,
            }),
            109 => self.i64_arithmetic(|dst, left, right| VmInstruction::IntLessI64 {
                dst,
                left,
                right,
            }),
            110 => self.i64_arithmetic(|dst, left, right| VmInstruction::IntGreaterI64 {
                dst,
                left,
                right,
            }),
            108 => self.i64_arithmetic(|dst, left, right| VmInstruction::BitAndI64 {
                dst,
                left,
                right,
            }),
            153 => self.u32_runtime_binary(|dst, left, right| VmInstruction::BitAndU32 {
                dst,
                left,
                right,
            }),
            154 => self.u32_runtime_binary(|dst, left, right| VmInstruction::BitAndU64 {
                dst,
                left,
                right,
            }),
            155 => {
                let (dst, left, right) = self.register_triple()?;
                Ok(VmInstruction::CompareU32 {
                    dst,
                    left,
                    right,
                    op: self.compare()?,
                })
            }
            156 => {
                let (dst, left, right) = self.register_triple()?;
                Ok(VmInstruction::CompareU64 {
                    dst,
                    left,
                    right,
                    op: self.compare()?,
                })
            }
            112 => self.i64_arithmetic(|dst, left, right| VmInstruction::BitXorI64 {
                dst,
                left,
                right,
            }),
            115 => self.i64_arithmetic(|dst, left, right| VmInstruction::IntShrI64 {
                dst,
                left,
                right,
            }),
            111 => {
                self.i64_arithmetic(|dst, left, right| VmInstruction::BitOrI64 { dst, left, right })
            }
            113 => Ok(VmInstruction::BitNotI64 {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            114 => Ok(VmInstruction::ShlI64 {
                dst: self.u32()?,
                value: self.u32()?,
                count: self.u32()?,
            }),
            4 => self.i64_arithmetic(|dst, left, right| VmInstruction::SubI64 { dst, left, right }),
            5 => self.i64_arithmetic(|dst, left, right| VmInstruction::MulI64 { dst, left, right }),
            6 => {
                let dst = self.u32()?;
                let callee = self.def_key()?;
                let count = self.count("call arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                Ok(VmInstruction::Call {
                    dst,
                    callee,
                    arguments,
                })
            }
            7 => {
                let dst = self.u32()?;
                let bits = self.u64()?;
                if !is_canonical_f64_bits(bits) {
                    return Err(VmArtifactError::NonCanonicalFloat { bits });
                }
                Ok(VmInstruction::ConstF64 { dst, bits })
            }
            171 => {
                let dst = self.u32()?;
                let bits = self.u32()?;
                if !is_canonical_f32_bits(bits) {
                    return Err(VmArtifactError::NonCanonicalFloat {
                        bits: u64::from(bits),
                    });
                }
                Ok(VmInstruction::ConstF32 { dst, bits })
            }
            172 => {
                let result = self.vm_type_at_depth(0)?;
                let returns = match self.byte()? {
                    0 => false,
                    1 => true,
                    _ => {
                        return Err(VmArtifactError::MalformedEncoding {
                            message: "invalid function result control tag",
                        });
                    }
                };
                Ok(VmInstruction::DeclareResult { result, returns })
            }
            138 => {
                let dst = self.u32()?;
                let selector = self.text()?;
                let Some(crate::PrimitiveRole::Float(primitive)) =
                    crate::PrimitiveRole::parse_selector_name(&selector)
                else {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid floating runtime opcode selector",
                    });
                };
                let count = self.count("floating runtime arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                Ok(VmInstruction::FloatIntrinsic {
                    dst,
                    primitive,
                    arguments,
                })
            }
            194 => {
                let dst = self.u32()?;
                let primitive = *MemoryPrimitive::ALL.get(self.byte()? as usize)
                    .ok_or(VmArtifactError::MalformedEncoding { message: "invalid memory operation" })?;
                let count = self.count("memory type arguments", 2)?;
                let mut types = Vec::with_capacity(count);
                for _ in 0..count { types.push(self.vm_type()?); }
                let count = self.count("memory value arguments", 4)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count { arguments.push(self.u32()?); }
                Ok(VmInstruction::MemoryIntrinsic { dst, primitive, types, arguments })
            }
            166 => {
                let dst = self.u32()?;
                let selector = self.text()?;
                let Some(primitive) = PrimitiveRole::parse_selector_name(&selector) else {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid integer runtime opcode selector",
                    });
                };
                let scalar = decode_integer_scalar(self.byte()?)?;
                let count = self.count("integer runtime arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                Ok(VmInstruction::IntIntrinsic {
                    dst,
                    primitive,
                    scalar,
                    arguments,
                })
            }
            8 => self.i64_arithmetic(|dst, left, right| VmInstruction::DivI64 { dst, left, right }),
            9 => self.i64_arithmetic(|dst, left, right| VmInstruction::RemI64 { dst, left, right }),
            10 => {
                self.i64_arithmetic(|dst, left, right| VmInstruction::AddF64 { dst, left, right })
            }
            11 => {
                self.i64_arithmetic(|dst, left, right| VmInstruction::SubF64 { dst, left, right })
            }
            12 => {
                self.i64_arithmetic(|dst, left, right| VmInstruction::MulF64 { dst, left, right })
            }
            13 => {
                self.i64_arithmetic(|dst, left, right| VmInstruction::DivF64 { dst, left, right })
            }
            14 => {
                self.i64_arithmetic(|dst, left, right| VmInstruction::RemF64 { dst, left, right })
            }
            15 => Ok(VmInstruction::Return { value: self.u32()? }),
            16 => {
                let dst = self.u32()?;
                let value = match self.byte()? {
                    0 => false,
                    1 => true,
                    _ => {
                        return Err(VmArtifactError::MalformedEncoding {
                            message: "invalid boolean literal",
                        });
                    }
                };
                Ok(VmInstruction::ConstBool { dst, value })
            }
            17 => self.compare_instruction(false),
            18 => self.compare_instruction(true),
            19 => Ok(VmInstruction::NotBool {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            20 => Ok(VmInstruction::ConstChar {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            21 => self.bool_equality(|dst, left, right| VmInstruction::EqBool { dst, left, right }),
            22 => self.bool_equality(|dst, left, right| VmInstruction::NeBool { dst, left, right }),
            23 => {
                let (dst, left, right) = self.register_triple()?;
                Ok(VmInstruction::CompareChar {
                    dst,
                    left,
                    right,
                    op: self.compare()?,
                })
            }
            24 => Ok(VmInstruction::ConstText {
                dst: self.u32()?,
                value: self.text()?,
            }),
            175 => Ok(VmInstruction::ConstStaticData {
                dst: self.u32()?,
                tag: self.u128()?,
                alignment: self.u32()?,
                bytes: {
                    let length = usize::try_from(self.u64()?).map_err(|_| {
                        VmArtifactError::MalformedEncoding {
                            message: "static-data length does not fit usize",
                        }
                    })?;
                    self.bytes(length)?.to_vec()
                },
            }),
            176 => Ok(VmInstruction::StaticLen {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            177 => Ok(VmInstruction::StaticSubslice {
                dst: self.u32()?,
                value: self.u32()?,
                start: self.u32()?,
                length: self.u32()?,
            }),
            178 => Ok(VmInstruction::StaticGetBorrowShared {
                dst: self.u32()?,
                value: self.u32()?,
                index: self.u32()?,
            }),
            179 => Ok(VmInstruction::StaticAsArrayBorrow { dst: self.u32()?, value: self.u32()? }),
            180 => Ok(VmInstruction::ArrayUtf8ValidUpTo {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            181 => Ok(VmInstruction::ArrayPushUtf8Char {
                value: self.u32()?,
                character: self.u32()?,
            }),
            187 => Ok(VmInstruction::ArrayInsertUtf8FromSlice {
                dst: self.u32()?,
                value: self.u32()?,
                index: self.u32()?,
                source: self.u32()?,
                start: self.u32()?,
                length: self.u32()?,
            }),
            188 => Ok(VmInstruction::ArrayTruncateDiscard {
                value: self.u32()?,
                length: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            189 => Ok(VmInstruction::ArrayReverseMove {
                value: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            190 => Ok(VmInstruction::ArraySplitOffMove {
                dst: self.u32()?,
                value: self.u32()?,
                index: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            193 => Ok(VmInstruction::ArraySplitBorrowUnique {
                dst: self.u32()?,
                value: self.u32()?,
                start: self.u32()?,
                length: self.u32()?,
                index: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            191 => Ok(VmInstruction::ArrayPopUtf8Char {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            192 => Ok(VmInstruction::ArrayUtf8CharAt {
                dst: self.u32()?,
                value: self.u32()?,
                start: self.u32()?,
                length: self.u32()?,
                index: self.u32()?,
            }),
            182 => Ok(VmInstruction::ArrayExtendFromSlice {
                value: self.u32()?,
                source: self.u32()?,
                start: self.u32()?,
                length: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            183 => Ok(VmInstruction::ArrayInsertMove {
                value: self.u32()?,
                index: self.u32()?,
                item: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            184 => Ok(VmInstruction::ArrayRemoveMove {
                dst: self.u32()?,
                value: self.u32()?,
                index: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            185 => Ok(VmInstruction::ArrayAppendMove {
                value: self.u32()?,
                source: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            186 => Ok(VmInstruction::ArrayInsertFromSlice {
                value: self.u32()?,
                index: self.u32()?,
                source: self.u32()?,
                start: self.u32()?,
                length: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            64 => Ok(VmInstruction::TextByteLen {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            65 => Ok(VmInstruction::TextConcat {
                dst: self.u32()?,
                left: self.u32()?,
                right: self.u32()?,
            }),
            66 => Ok(VmInstruction::TextEq {
                dst: self.u32()?,
                left: self.u32()?,
                right: self.u32()?,
            }),
            67 => Ok(VmInstruction::TextFromUtf8Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            68 => Ok(VmInstruction::TextAsBytes {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            48 => Ok(VmInstruction::CharFromU32Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            49 => Ok(VmInstruction::CharToU32 {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            80 => Ok(VmInstruction::BytesLen {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            81 => Ok(VmInstruction::BytesConcat {
                dst: self.u32()?,
                left: self.u32()?,
                right: self.u32()?,
            }),
            82 => Ok(VmInstruction::BytesGet {
                dst: self.u32()?,
                bytes: self.u32()?,
                index: self.u32()?,
            }),
            83 => Ok(VmInstruction::BytesSlice {
                dst: self.u32()?,
                bytes: self.u32()?,
                start: self.u32()?,
                end: self.u32()?,
            }),
            84 => Ok(VmInstruction::BytesFromArrayMove {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            85 => Ok(VmInstruction::BytesToArray {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            86 => Ok(VmInstruction::BytesUtf8ValidUpTo {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            173 => Ok(VmInstruction::Blake3 {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            139 => Ok(VmInstruction::ArrayNew {
                dst: self.u32()?,
                length: self.u32()?,
                fill: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            140 => Ok(VmInstruction::ArrayLen {
                dst: self.u32()?,
                value: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            141 => Ok(VmInstruction::ArrayGetCopy {
                dst: self.u32()?,
                value: self.u32()?,
                index: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            142 => Ok(VmInstruction::ArrayGetMove {
                dst: self.u32()?,
                value: self.u32()?,
                index: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            143 => Ok(VmInstruction::ArrayGetBorrow {
                dst: self.u32()?,
                value: self.u32()?,
                index: self.u32()?,
                unique: self.byte()? != 0,
                element_type: self.vm_type_at_depth(0)?,
            }),
            144 => Ok(VmInstruction::ArraySetMove {
                value: self.u32()?,
                index: self.u32()?,
                item: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            145 => Ok(VmInstruction::ArrayEmpty {
                dst: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            146 => Ok(VmInstruction::ArrayPushMove {
                value: self.u32()?,
                item: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            147 => Ok(VmInstruction::ArrayPopMove {
                dst: self.u32()?,
                value: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            148 => Ok(VmInstruction::ArrayCapacity {
                dst: self.u32()?,
                value: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            149 => Ok(VmInstruction::ArrayReserve {
                value: self.u32()?,
                additional: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            150 => Ok(VmInstruction::ArrayFinishDrained {
                value: self.u32()?,
                element_type: self.vm_type_at_depth(0)?,
            }),
            87 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32CheckedAdd {
                dst,
                left,
                right,
            }),
            88 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32CheckedSub {
                dst,
                left,
                right,
            }),
            89 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32CheckedMul {
                dst,
                left,
                right,
            }),
            90 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32CheckedDiv {
                dst,
                left,
                right,
            }),
            91 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32CheckedRem {
                dst,
                left,
                right,
            }),
            92 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32WrappingAdd {
                dst,
                left,
                right,
            }),
            93 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32WrappingSub {
                dst,
                left,
                right,
            }),
            94 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32WrappingMul {
                dst,
                left,
                right,
            }),
            95 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32WrappingShl {
                dst,
                left,
                right,
            }),
            96 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32WrappingShr {
                dst,
                left,
                right,
            }),
            97 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32CheckedShl {
                dst,
                left,
                right,
            }),
            98 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32CheckedShr {
                dst,
                left,
                right,
            }),
            99 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32Eq {
                dst,
                left,
                right,
            }),
            100 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32Lt {
                dst,
                left,
                right,
            }),
            101 => self.u32_runtime_binary(|dst, left, right| VmInstruction::U32Le {
                dst,
                left,
                right,
            }),
            102 => Ok(VmInstruction::U32ToUsize {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            103 => Ok(VmInstruction::UsizeToU32Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            116 => Ok(VmInstruction::I64ToU32Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            117 => Ok(VmInstruction::I64ToU32Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            118 => Ok(VmInstruction::I64ToUsizeChecked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            119 => Ok(VmInstruction::I64ToUsizeWrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            120 => Ok(VmInstruction::I64ToU8Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            121 => Ok(VmInstruction::I64ToU8Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            122 => Ok(VmInstruction::I64ToU16Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            123 => Ok(VmInstruction::I64ToU16Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            124 => Ok(VmInstruction::I64ToI16Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            125 => Ok(VmInstruction::I64ToI16Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            126 => Ok(VmInstruction::I64ToI32Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            127 => Ok(VmInstruction::I64ToI32Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            128 => Ok(VmInstruction::I64ToI8Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            129 => Ok(VmInstruction::I64ToI8Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            130 => Ok(VmInstruction::I64ToU64Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            131 => Ok(VmInstruction::I64ToU64Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            132 => Ok(VmInstruction::I64ToIsizeChecked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            133 => Ok(VmInstruction::I64ToIsizeWrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            134 => Ok(VmInstruction::I64ToU128Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            135 => Ok(VmInstruction::I64ToU128Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            136 => Ok(VmInstruction::I64ToI128Checked {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            137 => Ok(VmInstruction::I64ToI128Wrapping {
                dst: self.u32()?,
                value: self.u32()?,
            }),
            25 => self.bool_equality(|dst, left, right| VmInstruction::EqText { dst, left, right }),
            26 => self.bool_equality(|dst, left, right| VmInstruction::NeText { dst, left, right }),
            27 => self.i64_arithmetic(|dst, left, right| VmInstruction::ConcatText {
                dst,
                left,
                right,
            }),
            28 => Ok(VmInstruction::ConstUnit { dst: self.u32()? }),
            29 => {
                let dst = self.u32()?;
                let callee = self.def_key()?;
                let count = self.count("callable captures", MAX_DECODE_REGISTERS)?;
                let mut captures = Vec::with_capacity(count);
                for _ in 0..count {
                    captures.push(self.u32()?);
                }
                Ok(VmInstruction::MakeCallable {
                    dst,
                    callee,
                    captures,
                    environment: self.capture_environment()?,
                })
            }
            71 => Ok(VmInstruction::MakeLabel {
                dst: self.u32()?,
                brand_owner: self.def_key()?,
                brand_label: self.u32()?,
                target: self.u32()?,
                destination: self.u32()?,
            }),
            30 => {
                let dst = self.u32()?;
                let callee = self.u32()?;
                let count = self.count("indirect-call arguments", MAX_DECODE_REGISTERS)?;
                let mut arguments = Vec::with_capacity(count);
                for _ in 0..count {
                    arguments.push(self.u32()?);
                }
                Ok(VmInstruction::CallIndirect {
                    dst,
                    callee,
                    arguments,
                })
            }
            31 => Ok(VmInstruction::Jump {
                target: self.u32()?,
            }),
            32 => Ok(VmInstruction::BranchBool {
                condition: self.u32()?,
                then_target: self.u32()?,
                else_target: self.u32()?,
            }),
            33 => {
                let dst = self.u32()?;
                let count = self.count("tuple fields", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(self.u32()?);
                }
                Ok(VmInstruction::MakeTuple { dst, fields })
            }
            34 => {
                let dst = self.u32()?;
                let definition = self.def_key()?;
                let count = self.count("record fields", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(count);
                let mut field_types = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(self.u32()?);
                    field_types.push(self.vm_type()?);
                }
                Ok(VmInstruction::MakeRecord {
                    dst,
                    definition,
                    fields,
                    field_types,
                })
            }
            35 => Ok(VmInstruction::ProjectRecord {
                dst: self.u32()?,
                base: self.u32()?,
                index: self.u32()?,
                field_count: self.u32()?,
                field_type: self.vm_type()?,
            }),
            36 => {
                let dst = self.u32()?;
                let definition = self.def_key()?;
                let variant = self.u32()?;
                let count = self.count("enum fields", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(count);
                let mut field_types = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(self.u32()?);
                    field_types.push(self.vm_type()?);
                }
                Ok(VmInstruction::MakeEnum {
                    dst,
                    definition,
                    variant,
                    fields,
                    field_types,
                })
            }
            37 => {
                let dst = self.u32()?;
                let element_type = self.vm_type()?;
                let count = self.count("array fields", MAX_DECODE_REGISTERS)?;
                let mut fields = Vec::with_capacity(count);
                for _ in 0..count {
                    fields.push(self.u32()?);
                }
                Ok(VmInstruction::MakeArray {
                    dst,
                    fields,
                    element_type,
                })
            }
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "unknown VM instruction opcode",
            }),
        }
    }
    fn i64_arithmetic(
        &mut self,
        make: impl FnOnce(u32, u32, u32) -> VmInstruction,
    ) -> Result<VmInstruction, VmArtifactError> {
        let (dst, left, right) = self.register_triple()?;
        Ok(make(dst, left, right))
    }
    fn u32_runtime_binary(
        &mut self,
        make: impl FnOnce(u32, u32, u32) -> VmInstruction,
    ) -> Result<VmInstruction, VmArtifactError> {
        let (dst, left, right) = self.register_triple()?;
        Ok(make(dst, left, right))
    }
    fn bool_equality(
        &mut self,
        make: impl FnOnce(u32, u32, u32) -> VmInstruction,
    ) -> Result<VmInstruction, VmArtifactError> {
        let (dst, left, right) = self.register_triple()?;
        Ok(make(dst, left, right))
    }
    fn compare_instruction(&mut self, float: bool) -> Result<VmInstruction, VmArtifactError> {
        let (dst, left, right) = self.register_triple()?;
        let op = self.compare()?;
        Ok(if float {
            VmInstruction::CompareF64 {
                dst,
                left,
                right,
                op,
            }
        } else {
            VmInstruction::CompareI64 {
                dst,
                left,
                right,
                op,
            }
        })
    }
}
pub fn verify_program(program: CandidateVmProgram) -> Result<VerifiedVmProgram, VmArtifactError> {
    if program.schema != STAGE0_VM_SCHEMA {
        return Err(VmArtifactError::UnsupportedSchema {
            found: program.schema,
        });
    }
    if program.fingerprint != program.computed_fingerprint() {
        return Err(VmArtifactError::FingerprintMismatch);
    }
    if !program.functions.contains_key(&program.entry) {
        return Err(VmArtifactError::MissingFunction {
            definition: program.entry,
        });
    }
    // The program map key is the executable identity used by direct calls,
    // capability reachability, and dynamic label restoration. A host that
    // assembles CandidateVmProgram directly must not be able to associate it
    // with a differently branded function body; the decoder already keys
    // wire functions by their embedded definition.
    if program
        .functions
        .iter()
        .any(|(key, function)| *key != function.definition)
    {
        return Err(VmArtifactError::MalformedEncoding {
            message: "program function map key does not match definition",
        });
    }
    // A nominal value may cross any direct call boundary while retaining only
    // its nominal identity in the register type.  Its field layout therefore
    // cannot be a function-local opinion: two functions which declare the
    // same instantiated nominal layout must freeze byte-for-byte identical
    // descriptors, or a caller can construct one layout and a callee can
    // project it as another.
    let mut nominal_layouts = Vec::<&VmNominalCopyDescriptor>::new();
    for function in program.functions.values() {
        for descriptor in &function.nominal_copy_descriptors {
            if let Some(previous) = nominal_layouts.iter().find(|previous| {
                previous.definition == descriptor.definition
                    && previous.arguments == descriptor.arguments
            }) {
                if **previous != *descriptor {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "program nominal layout declarations disagree",
                    });
                }
            } else {
                nominal_layouts.push(descriptor);
            }
        }
    }
    let declared = program
        .host_capabilities
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    if declared.len() != program.host_capabilities.len()
        || program
            .host_capabilities
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
        || declared.iter().any(|capability| {
            capability.is_empty()
                || capability.contains('*')
                || capability.chars().any(char::is_whitespace)
        })
    {
        return Err(VmArtifactError::MalformedEncoding {
            message: "host capability declarations are not canonical",
        });
    }
    let reachable = reachable_host_capabilities(program.entry, &program.functions)
        .into_iter()
        .collect::<BTreeSet<_>>();
    if declared != reachable {
        return Err(VmArtifactError::MalformedEncoding {
            message: "host capability declarations do not match host imports",
        });
    }
    // The environment registry is a canonical target-side declaration set,
    // not an advisory cache.  Require an exact producer union so a decoded
    // artifact cannot carry orphaned callable authority or two conflicting
    // layouts for one lifted target.
    let mut produced_environments = BTreeMap::new();
    for function in program.functions.values() {
        for instruction in &function.instructions {
            let VmInstruction::MakeCallable {
                callee,
                environment: Some(environment),
                ..
            } = instruction
            else {
                continue;
            };
            if let Some(previous) = produced_environments.insert(*callee, environment.clone())
                && previous != *environment
            {
                return Err(VmArtifactError::InvalidCallableEnvironment {
                    message: "lifted callable producers disagree on their sealed environment",
                });
            }
        }
    }
    if program.callable_environments != produced_environments {
        return Err(VmArtifactError::InvalidCallableEnvironment {
            message: "callable environment registry does not exactly match producers",
        });
    }
    for (callee, environment) in &program.callable_environments {
        if callable_environment_target(environment) != *callee {
            return Err(VmArtifactError::InvalidCallableEnvironment {
                message: "callable environment brand does not authenticate target",
            });
        }
        let Some(target) = program.functions.get(callee) else {
            return Err(VmArtifactError::MissingFunction {
                definition: *callee,
            });
        };
        // The source environment brand authenticates the capture layout, but
        // a generic owner may choose a distinct concrete executable identity
        // for the same lifted source callable. The checks below bind that
        // environment to this exact target's ABI.
        if target.captures != environment.captures.len() as u32 {
            return Err(VmArtifactError::InvalidCallableEnvironment {
                message: "callable environment registry count does not match target",
            });
        }
        for (index, capture) in environment.captures.iter().enumerate() {
            if register_type(target, index as u32)? != capture.ty {
                return Err(VmArtifactError::InvalidCallableEnvironment {
                    message: "callable environment registry type does not match target",
                });
            }
        }
    }
    for function in program.functions.values() {
        verify_function(function)?;
    }
    verify_program_effect_operation_abis(&program.functions)?;
    for function in program.functions.values() {
        for instruction in &function.instructions {
            if let VmInstruction::Call {
                dst,
                callee,
                arguments,
            } = instruction
            {
                let Some(target) = program.functions.get(callee) else {
                    return Err(VmArtifactError::MissingFunction {
                        definition: *callee,
                    });
                };
                if target.captures != 0 {
                    return Err(VmArtifactError::CallArity {
                        expected: 0,
                        found: target.captures,
                    });
                }
                if target.parameters != arguments.len() as u32 {
                    return Err(VmArtifactError::CallArity {
                        expected: target.parameters,
                        found: arguments.len() as u32,
                    });
                }
                let mut generic_bindings = BTreeMap::new();
                for (index, argument) in arguments.iter().enumerate() {
                    let expected = register_type(target, index as u32)?;
                    let found = register_type(function, *argument)?;
                    if !unify_call_type(&expected, &found, &mut generic_bindings) {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *argument,
                            expected,
                            found,
                        });
                    }
                }
                let found = register_type(function, *dst)?;
                // A non-returning target has no normal edge on which `dst`
                // becomes observable. Its source callable may have been
                // bottom-coerced at the call site, so only the sealed control
                // declaration (not a synthetic Unit runtime leaf) decides
                // whether the ordinary result equality is required.
                let target_returns = declared_result(target)?
                    .map(|(_, returns)| returns)
                    .unwrap_or(true);
                let declared_return = return_type(target)?;
                // Constructors such as `vec_new<T>()` have no value argument
                // from which to infer `T`: their destination is the only
                // concrete part of the call ABI.  Treat it as an additional
                // unification site, just as ordinary parameters are.  This
                // also rejects an artifact whose arguments and destination
                // demand incompatible specializations of the same binder.
                if target_returns
                    && !unify_call_type(&declared_return, &found, &mut generic_bindings)
                {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: declared_return,
                        found,
                    });
                }
                verify_effect_operation_specialization(target, &generic_bindings)?;
                let expected = instantiate_vm_type(&declared_return, &generic_bindings);
                if target_returns && expected != found {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected,
                        found,
                    });
                }
            }
            if let VmInstruction::MakeCallable {
                dst,
                callee,
                captures,
                environment,
            } = instruction
            {
                let Some(target) = program.functions.get(callee) else {
                    return Err(VmArtifactError::MissingFunction {
                        definition: *callee,
                    });
                };
                if target.captures != captures.len() as u32 {
                    return Err(VmArtifactError::CallArity {
                        expected: target.captures,
                        found: captures.len() as u32,
                    });
                }
                match environment {
                    Some(environment) => {
                        if program.callable_environments.get(callee) != Some(environment) {
                            return Err(VmArtifactError::InvalidCallableEnvironment {
                                message: "callable producer does not match target sealed environment",
                            });
                        }
                        // The environment brand remains source provenance;
                        // a generic source callable may target a separately
                        // materialized executable body. The exact target ABI
                        // is checked immediately below.
                        if environment.captures.len() != captures.len() {
                            return Err(VmArtifactError::InvalidCallableEnvironment {
                                message: "callable environment layout does not match capture count",
                            });
                        }
                        for (index, capture) in environment.captures.iter().enumerate() {
                            let actual = register_type(function, captures[index])?;
                            if actual != capture.ty {
                                return Err(VmArtifactError::InvalidCallableEnvironment {
                                    message: "callable capture register does not match sealed type",
                                });
                            }
                            let target_type = register_type(target, index as u32)?;
                            if target_type != capture.ty {
                                return Err(VmArtifactError::InvalidCallableEnvironment {
                                    message: "callable target capture does not match sealed type",
                                });
                            }
                        }
                    }
                    None if !captures.is_empty() => {
                        return Err(VmArtifactError::InvalidCallableEnvironment {
                            message: "callable has captures but no sealed environment",
                        });
                    }
                    None if program.callable_environments.contains_key(callee) => {
                        return Err(VmArtifactError::InvalidCallableEnvironment {
                            message: "lifted callable producer omitted its sealed environment",
                        });
                    }
                    None => {}
                }
                let VmType::Callable {
                    safety, parameters, result, ..
                } = register_type(function, *dst)?
                else {
                    return Err(VmArtifactError::NotCallable { register: *dst });
                };
                if safety != target.safety {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "callable value safety does not match its target",
                    });
                }
                if target.parameters != target.captures + parameters.len() as u32 {
                    return Err(VmArtifactError::CallArity {
                        expected: target.parameters.saturating_sub(target.captures),
                        found: parameters.len() as u32,
                    });
                }
                // A callable value can capture a concrete instantiation of a
                // generic function. Infer that target-local substitution from
                // its captures and public parameter signature, exactly as a
                // direct call does; comparing raw `Generic(0)` binders would
                // incorrectly reject `identity` used as a first-class value.
                let mut generic_bindings = BTreeMap::new();
                for (index, capture) in captures.iter().enumerate() {
                    let expected = register_type(target, index as u32)?;
                    let found = register_type(function, *capture)?;
                    if !unify_call_type(&expected, &found, &mut generic_bindings) {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *capture,
                            expected,
                            found,
                        });
                    }
                }
                for (index, parameter) in parameters.iter().enumerate() {
                    let expected = register_type(target, target.captures + index as u32)?;
                    if !unify_call_type(&expected, parameter, &mut generic_bindings) {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *dst,
                            expected,
                            found: parameter.clone(),
                        });
                    }
                }
                let target_returns = declared_result(target)?
                    .map(|(_, returns)| returns)
                    .unwrap_or(true);
                let declared_return = return_type(target)?;
                // A first-class zero-argument generic constructor likewise
                // receives its specialization from the callable result.
                if target_returns
                    && !unify_call_type(&declared_return, result.as_ref(), &mut generic_bindings)
                {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: declared_return,
                        found: *result,
                    });
                }
                verify_effect_operation_specialization(target, &generic_bindings)?;
                let expected = instantiate_vm_type(&declared_return, &generic_bindings);
                if target_returns && expected != *result {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected,
                        found: *result,
                    });
                }
            }
        }
    }
    Ok(VerifiedVmProgram { program })
}

/// Direct calls and lifted callable construction infer a target-local generic
/// substitution from their concrete ABI.  Effect operations cross dynamic VM
/// handler frames, however, so their identity and payload/resumption ABI must
/// have been materialized with that very substitution as well.  Without this
/// check, a hostile artifact can call `helper<i64>` whose body still performs
/// `Ask<T>`: signature verification accepts the call while runtime handler
/// lookup compares `Ask<T>` and `Ask<i64>` as distinct identities.
fn verify_effect_operation_specialization(
    function: &VmFunction,
    bindings: &BTreeMap<u32, VmType>,
) -> Result<(), VmArtifactError> {
    for instruction in &function.instructions {
        match instruction {
            VmInstruction::Perform {
                dst,
                effect_arguments,
                arguments,
                ..
            } => {
                let specialized_arguments = effect_arguments
                    .iter()
                    .map(|argument| instantiate_vm_generic_argument(argument, bindings))
                    .collect::<Vec<_>>();
                let result = register_type(function, *dst)?;
                let specialized_result = instantiate_vm_type(&result, bindings);
                let payloads = arguments
                    .iter()
                    .map(|argument| register_type(function, *argument))
                    .collect::<Result<Vec<_>, _>>()?;
                let specialized_payloads = payloads
                    .iter()
                    .map(|payload| instantiate_vm_type(payload, bindings))
                    .collect::<Vec<_>>();
                if *effect_arguments != specialized_arguments
                    || result != specialized_result
                    || payloads != specialized_payloads
                {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "generic effect operation ABI was not specialized for call",
                    });
                }
            }
            VmInstruction::InstallHandler {
                effect_arguments,
                payload_destinations,
                resume_type,
                ..
            } => {
                let specialized_arguments = effect_arguments
                    .iter()
                    .map(|argument| instantiate_vm_generic_argument(argument, bindings))
                    .collect::<Vec<_>>();
                let payloads = payload_destinations
                    .iter()
                    .map(|destination| register_type(function, *destination))
                    .collect::<Result<Vec<_>, _>>()?;
                let specialized_payloads = payloads
                    .iter()
                    .map(|payload| instantiate_vm_type(payload, bindings))
                    .collect::<Vec<_>>();
                let specialized_resume_type = instantiate_vm_type(resume_type, bindings);
                if *effect_arguments != specialized_arguments
                    || payloads != specialized_payloads
                    || *resume_type != specialized_resume_type
                {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "generic effect operation ABI was not specialized for call",
                    });
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// An effect performance may suspend in an ordinary callee and select a
/// handler installed by any caller.  Function-local verification cannot see
/// that dynamic edge, so freeze one operation ABI for every exact effect
/// identity in the whole program.  Otherwise a callee can write a resumed
/// `I64` into a locally declared `Bool` destination (or reinterpret handler
/// payloads) after crossing a call frame.
fn verify_program_effect_operation_abis(
    functions: &BTreeMap<DefKey, VmFunction>,
) -> Result<(), VmArtifactError> {
    let mut operations = Vec::<(DefKey, Vec<VmGenericArgument>, u32, Vec<VmType>, VmType)>::new();
    for function in functions.values() {
        for instruction in &function.instructions {
            let (effect, effect_arguments, operation, payloads, resume_type) = match instruction {
                VmInstruction::Perform {
                    dst,
                    effect,
                    effect_arguments,
                    operation,
                    arguments,
                } => (
                    *effect,
                    effect_arguments.clone(),
                    *operation,
                    arguments
                        .iter()
                        .map(|argument| register_type(function, *argument))
                        .collect::<Result<Vec<_>, _>>()?,
                    register_type(function, *dst)?,
                ),
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments,
                    operation,
                    payload_destinations,
                    resume_type,
                    ..
                } => (
                    *effect,
                    effect_arguments.clone(),
                    *operation,
                    payload_destinations
                        .iter()
                        .map(|destination| register_type(function, *destination))
                        .collect::<Result<Vec<_>, _>>()?,
                    resume_type.clone(),
                ),
                _ => continue,
            };
            if let Some((_, _, _, expected_payloads, expected_resume_type)) = operations
                .iter()
                .find(|(known_effect, known_arguments, known_operation, _, _)| {
                    *known_effect == effect
                        && *known_arguments == effect_arguments
                        && *known_operation == operation
                })
            {
                if *expected_payloads != payloads || *expected_resume_type != resume_type {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "program effect operation ABI declarations disagree",
                    });
                }
            } else {
                operations.push((effect, effect_arguments, operation, payloads, resume_type));
            }
        }
    }
    Ok(())
}

/// Derive the only executable identity a sealed closure environment may
/// construct.  The normal lift is keyed by its source owner/callable brand;
/// a concrete generic enclosing instance derives a second key from that same
/// source lift and its frozen instance fingerprint.  Keeping this derivation
/// at the artifact boundary prevents a serialized descriptor from naming an
/// arbitrary ABI-compatible function body.
fn callable_environment_target(environment: &VmCaptureEnvironment) -> DefKey {
    let callable = environment.callable.to_le_bytes();
    let source = DefKey(Digest::of_parts([
        b"grandiose-stage0-lifted-callable".as_slice(),
        environment.owner.0.as_bytes().as_slice(),
        callable.as_slice(),
    ]));
    match environment.instance {
        None => source,
        Some(instance) => DefKey(Digest::of_parts([
            b"grandiose-stage0-lifted-callable-instance-v1".as_slice(),
            instance.as_bytes().as_slice(),
            source.0.as_bytes().as_slice(),
        ])),
    }
}

/// Conservative executable reachability for artifact declarations. A direct
/// call is an edge; materializing a callable is also an edge because a later
/// `CallIndirect` may invoke it. This never omits a host capability while
/// avoiding declarations from wholly unreachable emitted instances.
fn reachable_host_capabilities(
    entry: DefKey,
    functions: &BTreeMap<DefKey, VmFunction>,
) -> Vec<String> {
    let mut pending = vec![entry];
    let mut seen = BTreeSet::new();
    let mut capabilities = BTreeSet::new();
    while let Some(definition) = pending.pop() {
        if !seen.insert(definition) {
            continue;
        }
        let Some(function) = functions.get(&definition) else {
            continue;
        };
        for instruction in &function.instructions {
            match instruction {
                VmInstruction::HostCall { capability, .. } => {
                    capabilities.insert(capability.clone());
                }
                VmInstruction::Call { callee, .. } | VmInstruction::MakeCallable { callee, .. } => {
                    pending.push(*callee)
                }
                _ => {}
            }
        }
    }
    capabilities.into_iter().collect()
}

/// Match a callee-side type against one caller-side type while collecting the
/// callee's binder-local generic arguments. These binders are scoped to the
/// target function, so identical numeric indices in two functions never
/// accidentally alias.
fn unify_call_type(
    expected: &VmType,
    found: &VmType,
    bindings: &mut BTreeMap<u32, VmType>,
) -> bool {
    match expected {
        VmType::Generic(index) => match bindings.get(index) {
            Some(bound) => bound == found,
            None => {
                bindings.insert(*index, found.clone());
                true
            }
        },
        VmType::Tuple(expected) => match found {
            VmType::Tuple(found) if expected.len() == found.len() => expected
                .iter()
                .zip(found)
                .all(|(expected, found)| unify_call_type(expected, found, bindings)),
            _ => false,
        },
        VmType::Array(expected) => match found {
            VmType::Array(found) => unify_call_type(expected, found, bindings),
            _ => false,
        },
        VmType::StaticData {
            element: expected_element,
            tag: expected_tag,
            alignment: expected_alignment,
        } => match found {
            VmType::StaticData {
                element: found_element,
                tag: found_tag,
                alignment: found_alignment,
            } if expected_tag == found_tag && expected_alignment == found_alignment => {
                unify_call_type(expected_element, found_element, bindings)
            }
            _ => false,
        },
        VmType::Reference {
            unique: expected_unique,
            referent: expected_referent,
        } => match found {
            VmType::Reference {
                unique: found_unique,
                referent: found_referent,
            } if expected_unique == found_unique => {
                unify_call_type(expected_referent, found_referent, bindings)
            }
            _ => false,
        },
        VmType::Nominal {
            definition: expected_definition,
            arguments: expected_arguments,
        } => match found {
            VmType::Nominal {
                definition: found_definition,
                arguments: found_arguments,
            } if expected_definition == found_definition
                && expected_arguments.len() == found_arguments.len() =>
            {
                expected_arguments
                    .iter()
                    .zip(found_arguments)
                    .all(|(expected, found)| unify_call_type(expected, found, bindings))
            }
            _ => false,
        },
        VmType::Callable {
            safety: expected_safety,
            parameters: expected_parameters,
            result: expected_result,
            effects: expected_effects,
        } => match found {
            VmType::Callable {
                safety: found_safety,
                parameters: found_parameters,
                result: found_result,
                effects: found_effects,
            } if expected_safety == found_safety && expected_parameters.len() == found_parameters.len() => {
                expected_parameters
                    .iter()
                    .zip(found_parameters)
                    .all(|(expected, found)| unify_call_type(expected, found, bindings))
                    && unify_call_type(expected_result, found_result, bindings)
                    && unify_vm_effect_row(expected_effects, found_effects, bindings)
            }
            _ => false,
        },
        VmType::RawPointer { mutability, pointee } => match found {
            VmType::RawPointer { mutability: found_mutability, pointee: found_pointee }
                if mutability == found_mutability => unify_call_type(pointee, found_pointee, bindings),
            _ => false,
        },
        _ => expected == found,
    }
}

fn instantiate_vm_type(value: &VmType, bindings: &BTreeMap<u32, VmType>) -> VmType {
    match value {
        VmType::Generic(index) => bindings
            .get(index)
            .cloned()
            .unwrap_or_else(|| value.clone()),
        VmType::Tuple(fields) => VmType::Tuple(
            fields
                .iter()
                .map(|field| instantiate_vm_type(field, bindings))
                .collect(),
        ),
        VmType::Array(element) => VmType::Array(Box::new(instantiate_vm_type(element, bindings))),
        VmType::StaticData {
            element,
            tag,
            alignment,
        } => VmType::StaticData {
            element: Box::new(instantiate_vm_type(element, bindings)),
            tag: *tag,
            alignment: *alignment,
        },
        VmType::Nominal {
            definition,
            arguments,
        } => VmType::Nominal {
            definition: *definition,
            arguments: arguments
                .iter()
                .map(|argument| instantiate_vm_type(argument, bindings))
                .collect(),
        },
        VmType::Callable {
            safety,
            parameters,
            result,
            effects,
        } => VmType::Callable {
            safety: *safety,
            parameters: parameters
                .iter()
                .map(|parameter| instantiate_vm_type(parameter, bindings))
                .collect(),
            result: Box::new(instantiate_vm_type(result, bindings)),
            effects: Box::new(instantiate_vm_effect_row(effects, bindings)),
        },
        VmType::Reference { unique, referent } => VmType::Reference {
            unique: *unique,
            referent: Box::new(instantiate_vm_type(referent, bindings)),
        },
        VmType::RawPointer { mutability, pointee } => VmType::RawPointer {
            mutability: *mutability,
            pointee: Box::new(instantiate_vm_type(pointee, bindings)),
        },
        value => value.clone(),
    }
}

fn unify_vm_effect_row(
    expected: &VmEffectRow,
    found: &VmEffectRow,
    bindings: &mut BTreeMap<u32, VmType>,
) -> bool {
    expected.tail == found.tail
        && expected.effects.len() == found.effects.len()
        && expected.projections.len() == found.projections.len()
        && expected
            .effects
            .iter()
            .zip(&found.effects)
            .all(|(expected, found)| {
                expected.definition == found.definition
                    && expected.arguments.len() == found.arguments.len()
                    && expected
                        .arguments
                        .iter()
                        .zip(&found.arguments)
                        .all(|(expected, found)| {
                            unify_vm_generic_argument(expected, found, bindings)
                        })
            })
        && expected
            .projections
            .iter()
            .zip(&found.projections)
            .all(|(expected, found)| {
                unify_call_type(&expected.subject, &found.subject, bindings)
                    && expected.trait_definition == found.trait_definition
                    && expected.name == found.name
                    && expected.trait_arguments.len() == found.trait_arguments.len()
                    && expected.item_arguments.len() == found.item_arguments.len()
                    && expected
                        .trait_arguments
                        .iter()
                        .zip(&found.trait_arguments)
                        .all(|(expected, found)| {
                            unify_vm_generic_argument(expected, found, bindings)
                        })
                    && expected
                        .item_arguments
                        .iter()
                        .zip(&found.item_arguments)
                        .all(|(expected, found)| {
                            unify_vm_generic_argument(expected, found, bindings)
                        })
            })
}

fn unify_vm_generic_argument(
    expected: &VmGenericArgument,
    found: &VmGenericArgument,
    bindings: &mut BTreeMap<u32, VmType>,
) -> bool {
    match (expected, found) {
        (VmGenericArgument::Type(expected), VmGenericArgument::Type(found)) => {
            unify_call_type(expected, found, bindings)
        }
        (VmGenericArgument::EffectRow(expected), VmGenericArgument::EffectRow(found)) => {
            unify_vm_effect_row(expected, found, bindings)
        }
        _ => expected == found,
    }
}

fn instantiate_vm_effect_row(value: &VmEffectRow, bindings: &BTreeMap<u32, VmType>) -> VmEffectRow {
    VmEffectRow {
        effects: value
            .effects
            .iter()
            .map(|effect| VmEffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .iter()
                    .map(|argument| instantiate_vm_generic_argument(argument, bindings))
                    .collect(),
            })
            .collect(),
        projections: value
            .projections
            .iter()
            .map(|projection| VmEffectRowProjection {
                subject: instantiate_vm_type(&projection.subject, bindings),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .iter()
                    .map(|argument| instantiate_vm_generic_argument(argument, bindings))
                    .collect(),
                name: projection.name.clone(),
                item_arguments: projection
                    .item_arguments
                    .iter()
                    .map(|argument| instantiate_vm_generic_argument(argument, bindings))
                    .collect(),
            })
            .collect(),
        tail: value.tail,
    }
}

fn instantiate_vm_generic_argument(
    value: &VmGenericArgument,
    bindings: &BTreeMap<u32, VmType>,
) -> VmGenericArgument {
    match value {
        VmGenericArgument::Type(value) => {
            VmGenericArgument::Type(instantiate_vm_type(value, bindings))
        }
        VmGenericArgument::EffectRow(value) => {
            VmGenericArgument::EffectRow(instantiate_vm_effect_row(value, bindings))
        }
        value => value.clone(),
    }
}

fn return_type(function: &VmFunction) -> Result<VmType, VmArtifactError> {
    if let Some((declared, returns)) = declared_result(function)? {
        let mut observed_return = false;
        for value in reachable_return_values(&function.instructions) {
            observed_return = true;
            let found = register_type(function, value)?;
            if &found != declared {
                return Err(VmArtifactError::ResultType {
                    expected: declared.clone(),
                    found,
                });
            }
        }
        if !returns && observed_return {
            return Err(VmArtifactError::MalformedEncoding {
                message: "non-returning function contains a Return instruction",
            });
        }
        return Ok(declared.clone());
    }
    let mut result: Option<VmType> = None;
    for instruction in &function.instructions {
        let VmInstruction::Return { value } = instruction else {
            continue;
        };
        let found = register_type(function, *value)?;
        if let Some(expected) = &result {
            if expected != &found {
                return Err(VmArtifactError::ResultType {
                    expected: expected.clone(),
                    found,
                });
            }
        } else {
            result = Some(found);
        }
    }
    result.ok_or(VmArtifactError::NoReturn)
}

/// A declaration is deliberately an instruction so existing in-memory test
/// fixtures can remain concise, while emitted/decoded artifacts retain the
/// exact control ABI in their canonical payload.  It must be the unique first
/// instruction: allowing a jumpable or repeated declaration would make the
/// summary control-flow dependent.
fn declared_result(function: &VmFunction) -> Result<Option<(&VmType, bool)>, VmArtifactError> {
    let Some(first) = function.instructions.first() else {
        return Ok(None);
    };
    let VmInstruction::DeclareResult { result, returns } = first else {
        if function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::DeclareResult { .. }))
        {
            return Err(VmArtifactError::MalformedEncoding {
                message: "function result declaration is not its first instruction",
            });
        }
        return Ok(None);
    };
    validate_vm_type(result)?;
    if function.instructions[1..]
        .iter()
        .any(|instruction| matches!(instruction, VmInstruction::DeclareResult { .. }))
    {
        return Err(VmArtifactError::MalformedEncoding {
            message: "function has multiple result declarations",
        });
    }
    Ok(Some((result, *returns)))
}

fn lower_instruction(
    value: &MirInstruction,
    starts: &[u32],
) -> Result<VmInstruction, VmArtifactError> {
    Ok(match value {
        MirInstruction::ConstUnit { dst } => VmInstruction::ConstUnit { dst: dst.0 },
        MirInstruction::ConstI64 { dst, value } => VmInstruction::ConstI64 {
            dst: dst.0,
            value: *value,
        },
        MirInstruction::ConstU8 { dst, value } => VmInstruction::ConstU8 {
            dst: dst.0,
            value: *value,
        },
        MirInstruction::ConstU16 { dst, value } => VmInstruction::ConstU16 {
            dst: dst.0,
            value: *value,
        },
        MirInstruction::ConstU32 { dst, value } => VmInstruction::ConstU32 {
            dst: dst.0,
            value: *value,
        },
        MirInstruction::ConstU64 { dst, value } => VmInstruction::ConstU64 {
            dst: dst.0,
            value: *value,
        },
        MirInstruction::ConstUsize { dst, value } => VmInstruction::ConstUsize {
            dst: dst.0,
            value: *value,
        },
        MirInstruction::ConstU128 { dst, value } => VmInstruction::ConstU128 {
            dst: dst.0,
            value: *value,
        },
        MirInstruction::ConstI8 { dst, value } => VmInstruction::ConstI8 {
            dst: dst.0,
            value: *value,
        },
        MirInstruction::ConstI16 { dst, value } => VmInstruction::ConstI16 {
            dst: dst.0,
            value: *value,
        },
        MirInstruction::ConstI32 { dst, value } => VmInstruction::ConstI32 {
            dst: dst.0,
            value: *value,
        },
        MirInstruction::ConstIsize { dst, value } => VmInstruction::ConstIsize {
            dst: dst.0,
            value: *value,
        },
        MirInstruction::ConstI128 { dst, value } => VmInstruction::ConstI128 {
            dst: dst.0,
            value: *value,
        },
        MirInstruction::ConstF64 { dst, bits } => VmInstruction::ConstF64 {
            dst: dst.0,
            bits: *bits,
        },
        MirInstruction::ConstF32 { dst, bits } => VmInstruction::ConstF32 {
            dst: dst.0,
            bits: *bits,
        },
        MirInstruction::DeferredLiteral { .. } => {
            return Err(VmArtifactError::MalformedEncoding {
                message: "generic deferred literal reached VM lowering",
            });
        }
        MirInstruction::MemoryIntrinsic { dst, primitive, types, arguments } => VmInstruction::MemoryIntrinsic {
            dst: dst.0,
            primitive: *primitive,
            types: types.iter().map(vm_type).collect::<Result<_, _>>()
                .map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
            arguments: arguments.iter().map(|argument| argument.0).collect(),
        },
        MirInstruction::FloatIntrinsic {
            dst,
            primitive,
            arguments,
        } => VmInstruction::FloatIntrinsic {
            dst: dst.0,
            primitive: *primitive,
            arguments: arguments.iter().map(|argument| argument.0).collect(),
        },
        MirInstruction::IntIntrinsic {
            dst,
            primitive,
            scalar,
            arguments,
        } => VmInstruction::IntIntrinsic {
            dst: dst.0,
            primitive: *primitive,
            scalar: *scalar,
            arguments: arguments.iter().map(|argument| argument.0).collect(),
        },
        MirInstruction::IntGenericIntrinsic { .. } => {
            return Err(VmArtifactError::MalformedEncoding {
                message: "unmaterialized generic integer primitive reached VM lowering",
            });
        }
        MirInstruction::ConstBool { dst, value } => VmInstruction::ConstBool {
            dst: dst.0,
            value: *value,
        },
        MirInstruction::ConstChar { dst, value } => VmInstruction::ConstChar {
            dst: dst.0,
            value: *value,
        },
        MirInstruction::ConstText { dst, value } => VmInstruction::ConstText {
            dst: dst.0,
            value: value.clone(),
        },
        MirInstruction::ConstStaticData {
            dst,
            tag,
            alignment,
            bytes,
        } => VmInstruction::ConstStaticData {
            dst: dst.0,
            tag: *tag,
            alignment: *alignment,
            bytes: bytes.clone(),
        },
        MirInstruction::StaticLen { dst, value } => VmInstruction::StaticLen {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::StaticSubslice {
            dst,
            value,
            start,
            length,
        } => VmInstruction::StaticSubslice {
            dst: dst.0,
            value: value.0,
            start: start.0,
            length: length.0,
        },
        MirInstruction::StaticGetBorrowShared { dst, value, index } => {
            VmInstruction::StaticGetBorrowShared {
                dst: dst.0,
                value: value.0,
                index: index.0,
            }
        }
        MirInstruction::StaticAsArrayBorrow { dst, value } => VmInstruction::StaticAsArrayBorrow { dst: dst.0, value: value.0 },
        MirInstruction::TextByteLen { dst, value } => VmInstruction::TextByteLen {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::TextConcat { dst, left, right } => VmInstruction::TextConcat {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::TextEq { dst, left, right } => VmInstruction::TextEq {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::TextFromUtf8Checked { dst, value } => VmInstruction::TextFromUtf8Checked {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::TextAsBytes { dst, value } => VmInstruction::TextAsBytes {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::CharFromU32Checked { dst, value } => VmInstruction::CharFromU32Checked {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::CharToU32 { dst, value } => VmInstruction::CharToU32 {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::BytesLen { dst, value } => VmInstruction::BytesLen {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::BytesConcat { dst, left, right } => VmInstruction::BytesConcat {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::BytesGet { dst, bytes, index } => VmInstruction::BytesGet {
            dst: dst.0,
            bytes: bytes.0,
            index: index.0,
        },
        MirInstruction::BytesSlice {
            dst,
            bytes,
            start,
            end,
        } => VmInstruction::BytesSlice {
            dst: dst.0,
            bytes: bytes.0,
            start: start.0,
            end: end.0,
        },
        MirInstruction::BytesFromArrayMove { dst, value } => VmInstruction::BytesFromArrayMove {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::BytesToArray { dst, value } => VmInstruction::BytesToArray {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::BytesUtf8ValidUpTo { dst, value } => VmInstruction::BytesUtf8ValidUpTo {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::Blake3 { dst, value } => VmInstruction::Blake3 {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::ArrayNew {
            dst,
            length,
            fill,
            element_type,
        } => VmInstruction::ArrayNew {
            dst: dst.0,
            length: length.0,
            fill: fill.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
        },
        MirInstruction::ArrayLen {
            dst,
            value,
            element_type,
        } => VmInstruction::ArrayLen {
            dst: dst.0,
            value: value.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
        },
        MirInstruction::ArrayUtf8ValidUpTo { dst, value } => VmInstruction::ArrayUtf8ValidUpTo {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::ArrayPushUtf8Char { value, character } => VmInstruction::ArrayPushUtf8Char {
            value: value.0,
            character: character.0,
        },
        MirInstruction::ArrayInsertUtf8FromSlice {
            dst,
            value,
            index,
            source,
            start,
            length,
        } => VmInstruction::ArrayInsertUtf8FromSlice {
            dst: dst.0,
            value: value.0,
            index: index.0,
            source: source.0,
            start: start.0,
            length: length.0,
        },
        MirInstruction::ArrayPopUtf8Char { dst, value } => VmInstruction::ArrayPopUtf8Char {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::ArrayUtf8CharAt { dst, value, start, length, index } => {
            VmInstruction::ArrayUtf8CharAt {
                dst: dst.0,
                value: value.0,
                start: start.0,
                length: length.0,
                index: index.0,
            }
        }
        MirInstruction::ArrayExtendFromSlice {
            value,
            source,
            start,
            length,
            element_type,
        } => VmInstruction::ArrayExtendFromSlice {
            value: value.0,
            source: source.0,
            start: start.0,
            length: length.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: value.0, ty })?,
        },
        MirInstruction::ArrayInsertMove {
            value,
            index,
            item,
            element_type,
        } => VmInstruction::ArrayInsertMove {
            value: value.0,
            index: index.0,
            item: item.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: value.0, ty })?,
        },
        MirInstruction::ArrayRemoveMove {
            dst,
            value,
            index,
            element_type,
        } => VmInstruction::ArrayRemoveMove {
            dst: dst.0,
            value: value.0,
            index: index.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: value.0, ty })?,
        },
        MirInstruction::ArrayAppendMove {
            value,
            source,
            element_type,
        } => VmInstruction::ArrayAppendMove {
            value: value.0,
            source: source.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: value.0, ty })?,
        },
        MirInstruction::ArrayTruncateDiscard {
            value,
            length,
            element_type,
        } => VmInstruction::ArrayTruncateDiscard {
            value: value.0,
            length: length.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: value.0, ty })?,
        },
        MirInstruction::ArrayReverseMove {
            value,
            element_type,
        } => VmInstruction::ArrayReverseMove {
            value: value.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: value.0, ty })?,
        },
        MirInstruction::ArraySplitOffMove {
            dst,
            value,
            index,
            element_type,
        } => VmInstruction::ArraySplitOffMove {
            dst: dst.0,
            value: value.0,
            index: index.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: value.0, ty })?,
        },
        MirInstruction::ArraySplitBorrowUnique {
            dst,
            value,
            start,
            length,
            index,
            element_type,
        } => VmInstruction::ArraySplitBorrowUnique {
            dst: dst.0,
            value: value.0,
            start: start.0,
            length: length.0,
            index: index.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: value.0, ty })?,
        },
        MirInstruction::ArrayInsertFromSlice {
            value,
            index,
            source,
            start,
            length,
            element_type,
        } => VmInstruction::ArrayInsertFromSlice {
            value: value.0,
            index: index.0,
            source: source.0,
            start: start.0,
            length: length.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: value.0, ty })?,
        },
        MirInstruction::ArrayGetCopy {
            dst,
            value,
            index,
            element_type,
        } => VmInstruction::ArrayGetCopy {
            dst: dst.0,
            value: value.0,
            index: index.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
        },
        MirInstruction::ArrayGetMove {
            dst,
            value,
            index,
            element_type,
        } => VmInstruction::ArrayGetMove {
            dst: dst.0,
            value: value.0,
            index: index.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
        },
        MirInstruction::ArrayGetBorrow {
            dst,
            value,
            index,
            unique,
            element_type,
        } => VmInstruction::ArrayGetBorrow {
            dst: dst.0,
            value: value.0,
            index: index.0,
            unique: *unique,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
        },
        MirInstruction::ArraySetMove {
            value,
            index,
            item,
            element_type,
        } => VmInstruction::ArraySetMove {
            value: value.0,
            index: index.0,
            item: item.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: value.0, ty })?,
        },
        MirInstruction::ArrayEmpty { dst, element_type } => VmInstruction::ArrayEmpty {
            dst: dst.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
        },
        MirInstruction::ArrayPushMove {
            value,
            item,
            element_type,
        } => VmInstruction::ArrayPushMove {
            value: value.0,
            item: item.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: value.0, ty })?,
        },
        MirInstruction::ArrayPopMove {
            dst,
            value,
            element_type,
        } => VmInstruction::ArrayPopMove {
            dst: dst.0,
            value: value.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
        },
        MirInstruction::ArrayCapacity {
            dst,
            value,
            element_type,
        } => VmInstruction::ArrayCapacity {
            dst: dst.0,
            value: value.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
        },
        MirInstruction::ArrayReserve {
            value,
            additional,
            element_type,
        } => VmInstruction::ArrayReserve {
            value: value.0,
            additional: additional.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: value.0, ty })?,
        },
        MirInstruction::ArrayFinishDrained {
            value,
            element_type,
        } => VmInstruction::ArrayFinishDrained {
            value: value.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: value.0, ty })?,
        },
        MirInstruction::U32CheckedAdd { dst, left, right } => VmInstruction::U32CheckedAdd {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32CheckedSub { dst, left, right } => VmInstruction::U32CheckedSub {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32CheckedMul { dst, left, right } => VmInstruction::U32CheckedMul {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32CheckedDiv { dst, left, right } => VmInstruction::U32CheckedDiv {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32CheckedRem { dst, left, right } => VmInstruction::U32CheckedRem {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32WrappingAdd { dst, left, right } => VmInstruction::U32WrappingAdd {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32WrappingSub { dst, left, right } => VmInstruction::U32WrappingSub {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32WrappingMul { dst, left, right } => VmInstruction::U32WrappingMul {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32WrappingShl { dst, left, right } => VmInstruction::U32WrappingShl {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32WrappingShr { dst, left, right } => VmInstruction::U32WrappingShr {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32CheckedShl { dst, left, right } => VmInstruction::U32CheckedShl {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32CheckedShr { dst, left, right } => VmInstruction::U32CheckedShr {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32Eq { dst, left, right } => VmInstruction::U32Eq {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32Lt { dst, left, right } => VmInstruction::U32Lt {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32Le { dst, left, right } => VmInstruction::U32Le {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::U32ToUsize { dst, value } => VmInstruction::U32ToUsize {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::UsizeToU32Checked { dst, value } => VmInstruction::UsizeToU32Checked {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToU32Checked { dst, value } => VmInstruction::I64ToU32Checked {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToU32Wrapping { dst, value } => VmInstruction::I64ToU32Wrapping {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToUsizeChecked { dst, value } => VmInstruction::I64ToUsizeChecked {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToUsizeWrapping { dst, value } => VmInstruction::I64ToUsizeWrapping {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToU8Checked { dst, value } => VmInstruction::I64ToU8Checked {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToU8Wrapping { dst, value } => VmInstruction::I64ToU8Wrapping {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToU16Checked { dst, value } => VmInstruction::I64ToU16Checked {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToU16Wrapping { dst, value } => VmInstruction::I64ToU16Wrapping {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToI16Checked { dst, value } => VmInstruction::I64ToI16Checked {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToI16Wrapping { dst, value } => VmInstruction::I64ToI16Wrapping {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToI32Checked { dst, value } => VmInstruction::I64ToI32Checked {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToI32Wrapping { dst, value } => VmInstruction::I64ToI32Wrapping {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToI8Checked { dst, value } => VmInstruction::I64ToI8Checked {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToI8Wrapping { dst, value } => VmInstruction::I64ToI8Wrapping {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToU64Checked { dst, value } => VmInstruction::I64ToU64Checked {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToU64Wrapping { dst, value } => VmInstruction::I64ToU64Wrapping {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToIsizeChecked { dst, value } => VmInstruction::I64ToIsizeChecked {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToIsizeWrapping { dst, value } => VmInstruction::I64ToIsizeWrapping {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToU128Checked { dst, value } => VmInstruction::I64ToU128Checked {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToU128Wrapping { dst, value } => VmInstruction::I64ToU128Wrapping {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToI128Checked { dst, value } => VmInstruction::I64ToI128Checked {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::I64ToI128Wrapping { dst, value } => VmInstruction::I64ToI128Wrapping {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::MakeTuple { dst, fields } => VmInstruction::MakeTuple {
            dst: dst.0,
            fields: fields.iter().map(|field| field.0).collect(),
        },
        MirInstruction::MakeArray {
            dst,
            fields,
            element_type,
        } => VmInstruction::MakeArray {
            dst: dst.0,
            fields: fields.iter().map(|field| field.0).collect(),
            element_type: vm_type(element_type)
                .expect("validated MIR has VM-representable array element type"),
        },
        MirInstruction::MakeRecord {
            dst,
            definition,
            fields,
            field_types,
        } => VmInstruction::MakeRecord {
            dst: dst.0,
            definition: *definition,
            fields: fields.iter().map(|field| field.0).collect(),
            field_types: field_types
                .iter()
                .map(|field| {
                    vm_type(field).expect("validated MIR has VM-representable record fields")
                })
                .collect(),
        },
        MirInstruction::MakeEnum {
            dst,
            definition,
            variant,
            fields,
            field_types,
        } => VmInstruction::MakeEnum {
            dst: dst.0,
            definition: *definition,
            variant: *variant,
            fields: fields.iter().map(|field| field.0).collect(),
            field_types: field_types
                .iter()
                .map(|field| {
                    vm_type(field).expect("validated MIR has VM-representable enum fields")
                })
                .collect(),
        },
        MirInstruction::ProjectRecord {
            dst,
            base,
            index,
            field_count,
            field_type,
        } => VmInstruction::ProjectRecord {
            dst: dst.0,
            base: base.0,
            index: *index,
            field_count: *field_count,
            field_type: vm_type(field_type)
                .expect("validated MIR has VM-representable record projection type"),
        },
        MirInstruction::ProjectTuple {
            dst,
            base,
            index,
            field_count,
            field_type,
        } => VmInstruction::ProjectTuple {
            dst: dst.0,
            base: base.0,
            index: *index,
            field_count: *field_count,
            field_type: vm_type(field_type)
                .expect("validated MIR has VM-representable tuple projection type"),
        },
        MirInstruction::ProjectArray {
            dst,
            base,
            index,
            field_count,
            element_type,
        } => VmInstruction::ProjectArray {
            dst: dst.0,
            base: base.0,
            index: *index,
            field_count: *field_count,
            element_type: vm_type(element_type)
                .expect("validated MIR has VM-representable array projection type"),
        },
        MirInstruction::UpdateRecord {
            dst,
            base,
            index,
            field_count,
            value,
            field_type,
        } => VmInstruction::UpdateRecord {
            dst: dst.0,
            base: base.0,
            index: *index,
            field_count: *field_count,
            value: value.0,
            field_type: vm_type(field_type)
                .expect("validated MIR has VM-representable record update type"),
        },
        MirInstruction::PatternTest {
            dst,
            subject,
            pattern,
        } => VmInstruction::PatternTest {
            dst: dst.0,
            subject: subject.0,
            pattern: lower_pattern(pattern),
        },
        MirInstruction::Perform {
            dst,
            effect,
            effect_arguments,
            operation,
            arguments,
            ..
        } => VmInstruction::Perform {
            dst: dst.0,
            effect: *effect,
            effect_arguments: effect_arguments
                .iter()
                .map(|argument| vm_effect_argument(*effect, argument))
                .collect::<Result<_, _>>()?,
            operation: *operation,
            arguments: arguments.iter().map(|argument| argument.0).collect(),
        },
        MirInstruction::InstallHandler {
            effect,
            effect_arguments,
            operation,
            payload_destinations,
            resume_type,
            continuation,
            target,
            ..
        } => VmInstruction::InstallHandler {
            effect: *effect,
            effect_arguments: effect_arguments
                .iter()
                .map(|argument| vm_effect_argument(*effect, argument))
                .collect::<Result<_, _>>()?,
            operation: *operation,
            payload_destinations: payload_destinations
                .iter()
                .map(|destination| destination.0)
                .collect(),
            resume_type: vm_type(resume_type)
                .expect("validated MIR has VM-representable handler result type"),
            continuation: match continuation {
                MirContinuationPolicy::Consume => VmContinuationPolicy::Consume,
                MirContinuationPolicy::Replay { uses } => {
                    VmContinuationPolicy::Replay { uses: *uses }
                }
                MirContinuationPolicy::Terminal => VmContinuationPolicy::Terminal,
            },
            target: *starts
                .get(target.0 as usize)
                .expect("validated MIR handler target exists"),
        },
        MirInstruction::UninstallHandler => VmInstruction::UninstallHandler,
        MirInstruction::CaptureResumption { dst, .. } => {
            VmInstruction::CaptureResumption { dst: dst.0 }
        }
        MirInstruction::Resume { value, .. } => VmInstruction::Resume { value: value.0 },
        MirInstruction::ResumeReturn { dst, value, .. } => VmInstruction::ResumeReturn {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::ResumeSnapshot {
            snapshot, value, ..
        } => VmInstruction::ResumeSnapshot {
            snapshot: snapshot.0,
            value: value.0,
        },
        MirInstruction::Forward { .. } => VmInstruction::Forward,
        MirInstruction::Cancel { .. } => VmInstruction::Cancel,
        MirInstruction::Copy { dst, src } => VmInstruction::Copy {
            dst: dst.0,
            src: src.0,
        },
        MirInstruction::StorageLive { binding, local } => VmInstruction::StorageLive {
            binding: binding.0,
            local: local.0,
        },
        MirInstruction::StorageDead { binding, local } => VmInstruction::StorageDead {
            binding: binding.0,
            local: local.0,
        },
        MirInstruction::SetDropFlag { flag, value } => VmInstruction::SetDropFlag {
            flag: flag.0,
            value: *value,
        },
        MirInstruction::DestroyIf { local, flag } => VmInstruction::DestroyIf {
            local: local.0,
            flag: flag.0,
        },
        MirInstruction::Store { dst, src } => VmInstruction::Store {
            dst: dst.0,
            src: src.0,
        },
        MirInstruction::Move { dst, src } => VmInstruction::Move {
            dst: dst.0,
            src: src.0,
        },
        MirInstruction::Borrow {
            dst,
            src,
            fields,
            unique,
            reborrow,
        } => VmInstruction::Borrow {
            dst: dst.0,
            src: src.0,
            fields: fields.clone(),
            unique: *unique,
            reborrow: *reborrow,
        },
        MirInstruction::DerefCopy { dst, reference } => VmInstruction::DerefCopy {
            dst: dst.0,
            reference: reference.0,
        },
        MirInstruction::DerefMove { dst, reference } => VmInstruction::DerefMove {
            dst: dst.0,
            reference: reference.0,
        },
        MirInstruction::DerefStore { reference, src } => VmInstruction::DerefStore {
            reference: reference.0,
            src: src.0,
        },
        MirInstruction::NotBool { dst, value } => VmInstruction::NotBool {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::AddI64 { dst, left, right } => VmInstruction::AddI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::WrappingAddI64 { dst, left, right } => VmInstruction::WrappingAddI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::WrappingSubI64 { dst, left, right } => VmInstruction::WrappingSubI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::WrappingMulI64 { dst, left, right } => VmInstruction::WrappingMulI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::IntEqualI64 { dst, left, right } => VmInstruction::IntEqualI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::IntLessI64 { dst, left, right } => VmInstruction::IntLessI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::IntGreaterI64 { dst, left, right } => VmInstruction::IntGreaterI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::BitAndI64 { dst, left, right } => VmInstruction::BitAndI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::BitAndU32 { dst, left, right } => VmInstruction::BitAndU32 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::BitAndU64 { dst, left, right } => VmInstruction::BitAndU64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::BitAndGeneric { .. } => {
            return Err(VmArtifactError::MalformedEncoding {
                message: "unmaterialized generic bitwise-and reached VM lowering",
            });
        }
        MirInstruction::BitXorI64 { dst, left, right } => VmInstruction::BitXorI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::IntShrI64 { dst, left, right } => VmInstruction::IntShrI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::BitOrI64 { dst, left, right } => VmInstruction::BitOrI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::BitNotI64 { dst, value } => VmInstruction::BitNotI64 {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::ShlI64 { dst, value, count } => VmInstruction::ShlI64 {
            dst: dst.0,
            value: value.0,
            count: count.0,
        },
        MirInstruction::SubI64 { dst, left, right } => VmInstruction::SubI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::MulI64 { dst, left, right } => VmInstruction::MulI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::DivI64 { dst, left, right } => VmInstruction::DivI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::RemI64 { dst, left, right } => VmInstruction::RemI64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::AddF64 { dst, left, right } => VmInstruction::AddF64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::ConcatText { dst, left, right } => VmInstruction::ConcatText {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::SubF64 { dst, left, right } => VmInstruction::SubF64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::MulF64 { dst, left, right } => VmInstruction::MulF64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::DivF64 { dst, left, right } => VmInstruction::DivF64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::RemF64 { dst, left, right } => VmInstruction::RemF64 {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::EqI64 { dst, left, right } => {
            compare_i64(dst.0, left.0, right.0, VmCompare::Equal)
        }
        MirInstruction::NeI64 { dst, left, right } => {
            compare_i64(dst.0, left.0, right.0, VmCompare::NotEqual)
        }
        MirInstruction::NeU32 { dst, left, right } => {
            compare_u32(dst.0, left.0, right.0, VmCompare::NotEqual)
        }
        MirInstruction::NeU64 { dst, left, right } => {
            compare_u64(dst.0, left.0, right.0, VmCompare::NotEqual)
        }
        MirInstruction::LtI64 { dst, left, right } => {
            compare_i64(dst.0, left.0, right.0, VmCompare::Less)
        }
        MirInstruction::LeI64 { dst, left, right } => {
            compare_i64(dst.0, left.0, right.0, VmCompare::LessEqual)
        }
        MirInstruction::GtI64 { dst, left, right } => {
            compare_i64(dst.0, left.0, right.0, VmCompare::Greater)
        }
        MirInstruction::GeI64 { dst, left, right } => {
            compare_i64(dst.0, left.0, right.0, VmCompare::GreaterEqual)
        }
        MirInstruction::EqF64 { dst, left, right } => {
            compare_f64(dst.0, left.0, right.0, VmCompare::Equal)
        }
        MirInstruction::NeF64 { dst, left, right } => {
            compare_f64(dst.0, left.0, right.0, VmCompare::NotEqual)
        }
        MirInstruction::LtF64 { dst, left, right } => {
            compare_f64(dst.0, left.0, right.0, VmCompare::Less)
        }
        MirInstruction::LeF64 { dst, left, right } => {
            compare_f64(dst.0, left.0, right.0, VmCompare::LessEqual)
        }
        MirInstruction::GtF64 { dst, left, right } => {
            compare_f64(dst.0, left.0, right.0, VmCompare::Greater)
        }
        MirInstruction::GeF64 { dst, left, right } => {
            compare_f64(dst.0, left.0, right.0, VmCompare::GreaterEqual)
        }
        MirInstruction::EqBool { dst, left, right } => VmInstruction::EqBool {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::NeBool { dst, left, right } => VmInstruction::NeBool {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::EqText { dst, left, right } => VmInstruction::EqText {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::NeText { dst, left, right } => VmInstruction::NeText {
            dst: dst.0,
            left: left.0,
            right: right.0,
        },
        MirInstruction::EqChar { dst, left, right } => {
            compare_char(dst.0, left.0, right.0, VmCompare::Equal)
        }
        MirInstruction::NeChar { dst, left, right } => {
            compare_char(dst.0, left.0, right.0, VmCompare::NotEqual)
        }
        MirInstruction::LtChar { dst, left, right } => {
            compare_char(dst.0, left.0, right.0, VmCompare::Less)
        }
        MirInstruction::LeChar { dst, left, right } => {
            compare_char(dst.0, left.0, right.0, VmCompare::LessEqual)
        }
        MirInstruction::GtChar { dst, left, right } => {
            compare_char(dst.0, left.0, right.0, VmCompare::Greater)
        }
        MirInstruction::GeChar { dst, left, right } => {
            compare_char(dst.0, left.0, right.0, VmCompare::GreaterEqual)
        }
        MirInstruction::Call {
            dst,
            callee,
            arguments,
            ..
        } => VmInstruction::Call {
            dst: dst.0,
            callee: *callee,
            arguments: arguments.iter().map(|argument| argument.0).collect(),
        },
        MirInstruction::HostCall {
            dst,
            capability,
            symbol,
            parameters,
            result,
            arguments,
        } => VmInstruction::HostCall {
            dst: dst.0,
            capability: capability.clone(),
            symbol: symbol.clone(),
            parameters: parameters
                .iter()
                .map(vm_type)
                .collect::<Result<Vec<_>, _>>()
                .map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
            result: vm_type(result)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
            arguments: arguments.iter().map(|argument| argument.0).collect(),
        },
        MirInstruction::Abort => VmInstruction::Trap,
        MirInstruction::MakeCallable {
            dst,
            callee,
            captures,
            environment,
            ..
        } => VmInstruction::MakeCallable {
            dst: dst.0,
            callee: *callee,
            captures: captures.iter().map(|capture| capture.0).collect(),
            environment: environment
                .as_ref()
                .map(|environment| {
                    Ok(VmCaptureEnvironment {
                        owner: environment.brand.owner,
                        callable: environment.brand.callable.0,
                        instance: None,
                        captures: environment
                            .captures
                            .iter()
                            .map(|capture| {
                                Ok(VmCapture {
                                    mode: match capture.mode {
                                        CaptureMode::SharedBorrow => VmCaptureMode::SharedBorrow,
                                        CaptureMode::UniqueBorrow => VmCaptureMode::UniqueBorrow,
                                        CaptureMode::Copy => VmCaptureMode::Copy,
                                        CaptureMode::Move => VmCaptureMode::Move,
                                    },
                                    // The corresponding value register is
                                    // checked independently; this metadata
                                    // type has no one register identity of
                                    // its own.
                                    ty: vm_type(&capture.ty).map_err(|ty| {
                                        VmArtifactError::UnsupportedType {
                                            local: u32::MAX,
                                            ty,
                                        }
                                    })?,
                                })
                            })
                            .collect::<Result<Vec<_>, VmArtifactError>>()?,
                    })
                })
                .transpose()?,
        },
        MirInstruction::MakeLabel {
            dst,
            brand,
            target,
            destination,
            ..
        } => VmInstruction::MakeLabel {
            dst: dst.0,
            brand_owner: brand.owner,
            brand_label: brand.label,
            target: *starts
                .get(target.0 as usize)
                .expect("validated MIR label target exists"),
            destination: destination.0,
        },
        MirInstruction::CallIndirect {
            dst,
            callee,
            arguments,
        } => VmInstruction::CallIndirect {
            dst: dst.0,
            callee: callee.0,
            arguments: arguments.iter().map(|argument| argument.0).collect(),
        },
    })
}
fn lower_pattern(value: &MirPattern) -> VmPattern {
    match value {
        MirPattern::Any => VmPattern::Any,
        MirPattern::Literal(value) => VmPattern::Literal(value.clone()),
        MirPattern::Tuple(values) => VmPattern::Tuple(values.iter().map(lower_pattern).collect()),
        MirPattern::Array { element, elements } => VmPattern::Array {
            element: vm_type(element)
                .expect("validated MIR has VM-representable array pattern element"),
            elements: elements.iter().map(lower_pattern).collect(),
        },
        MirPattern::Record {
            definition,
            field_types,
            field_count,
            fields,
        } => VmPattern::Record {
            definition: *definition,
            field_types: field_types
                .iter()
                .map(|field| {
                    vm_type(field).expect("validated MIR has VM-representable pattern layout")
                })
                .collect(),
            field_count: *field_count,
            fields: lower_pattern_fields(fields),
        },
        MirPattern::Enum {
            definition,
            variant,
            field_types,
            field_count,
            fields,
        } => VmPattern::Enum {
            definition: *definition,
            variant: *variant,
            field_types: field_types
                .iter()
                .map(|field| {
                    vm_type(field).expect("validated MIR has VM-representable pattern layout")
                })
                .collect(),
            field_count: *field_count,
            fields: lower_pattern_fields(fields),
        },
    }
}
fn lower_pattern_fields(fields: &[MirPatternField]) -> Vec<VmPatternField> {
    fields
        .iter()
        .map(|field| VmPatternField {
            index: field.index,
            ty: vm_type(&field.ty).expect("validated MIR has VM-representable pattern field"),
            pattern: lower_pattern(&field.pattern),
        })
        .collect()
}
fn compare_i64(dst: u32, left: u32, right: u32, op: VmCompare) -> VmInstruction {
    VmInstruction::CompareI64 {
        dst,
        left,
        right,
        op,
    }
}
fn compare_u32(dst: u32, left: u32, right: u32, op: VmCompare) -> VmInstruction {
    VmInstruction::CompareU32 {
        dst,
        left,
        right,
        op,
    }
}
fn compare_u64(dst: u32, left: u32, right: u32, op: VmCompare) -> VmInstruction {
    VmInstruction::CompareU64 {
        dst,
        left,
        right,
        op,
    }
}
fn compare_f64(dst: u32, left: u32, right: u32, op: VmCompare) -> VmInstruction {
    VmInstruction::CompareF64 {
        dst,
        left,
        right,
        op,
    }
}
fn compare_char(dst: u32, left: u32, right: u32, op: VmCompare) -> VmInstruction {
    VmInstruction::CompareChar {
        dst,
        left,
        right,
        op,
    }
}
fn verify_pattern(pattern: &VmPattern, subject: &VmType) -> Result<(), VmArtifactError> {
    match pattern {
        VmPattern::Any => Ok(()),
        VmPattern::Literal(value) => {
            if numeric_literal_matches_vm_type(value, subject) {
                return Ok(());
            }
            let expected = literal_vm_type(value).ok_or(VmArtifactError::MalformedEncoding {
                message: "invalid scalar literal pattern",
            })?;
            if expected == *subject {
                Ok(())
            } else {
                Err(VmArtifactError::TypeMismatch {
                    register: 0,
                    expected,
                    found: subject.clone(),
                })
            }
        }
        VmPattern::Tuple(patterns) => match subject {
            VmType::Tuple(types) if patterns.len() == types.len() => patterns
                .iter()
                .zip(types)
                .try_for_each(|(pattern, ty)| verify_pattern(pattern, ty)),
            _ => Err(VmArtifactError::TypeMismatch {
                register: 0,
                expected: VmType::Tuple(Vec::new()),
                found: subject.clone(),
            }),
        },
        VmPattern::Array { element, elements } => match subject {
            VmType::Array(actual) if actual.as_ref() == element => elements
                .iter()
                .try_for_each(|pattern| verify_pattern(pattern, element)),
            _ => Err(VmArtifactError::TypeMismatch {
                register: 0,
                expected: VmType::Array(Box::new(element.clone())),
                found: subject.clone(),
            }),
        },
        VmPattern::Record {
            definition,
            field_types,
            field_count,
            fields,
        }
        | VmPattern::Enum {
            definition,
            field_types,
            field_count,
            fields,
            ..
        } => match subject {
            VmType::Nominal {
                definition: actual, ..
            } if actual == definition => verify_pattern_fields(fields, field_types, *field_count),
            _ => Err(VmArtifactError::TypeMismatch {
                register: 0,
                expected: VmType::Nominal {
                    definition: *definition,
                    arguments: Vec::new(),
                },
                found: subject.clone(),
            }),
        },
    }
}
fn verify_pattern_fields(
    fields: &[VmPatternField],
    field_types: &[VmType],
    field_count: u32,
) -> Result<(), VmArtifactError> {
    if field_types.len() != field_count as usize {
        return Err(VmArtifactError::MalformedEncoding {
            message: "pattern layout length disagrees with its frozen arity",
        });
    }
    let mut previous = None;
    for field in fields {
        if previous.is_some_and(|previous| previous >= field.index) {
            return Err(VmArtifactError::MalformedEncoding {
                message: "pattern fields are not strictly ordered",
            });
        }
        if field.index >= field_count {
            return Err(VmArtifactError::MalformedEncoding {
                message: "pattern field is outside its structural arity",
            });
        }
        if field.ty != field_types[field.index as usize] {
            return Err(VmArtifactError::MalformedEncoding {
                message: "pattern field type disagrees with its frozen layout",
            });
        }
        previous = Some(field.index);
        verify_pattern(&field.pattern, &field.ty)?;
    }
    Ok(())
}
fn literal_vm_type(value: &str) -> Option<VmType> {
    if matches!(value, "true" | "false") {
        return Some(VmType::Bool);
    }
    match exact_scalar_literal_kind(value)? {
        TokenKind::Integer if parse_pattern_i64(value).is_some() => Some(VmType::I64),
        TokenKind::Float if parse_pattern_f64(value).is_some() => Some(VmType::F64),
        TokenKind::Character if parse_pattern_char(value).is_some() => Some(VmType::Char),
        TokenKind::String if parse_pattern_text(value).is_some() => Some(VmType::Text),
        _ => None,
    }
}

// Integer pattern syntax is contextually typed by the enum/record payload.
// The compact VM pattern keeps only its canonical spelling, so recover that
// context during verification rather than forcing every u32/u64 arm to use
// an artificial i64 representation.
fn numeric_literal_matches_vm_type(value: &str, subject: &VmType) -> bool {
    let signed = || parse_pattern_i64(value);
    let unsigned = || parse_pattern_u64(value);
    match subject {
        VmType::I64 => signed().is_some(),
        VmType::I32 => signed().and_then(|value| i32::try_from(value).ok()).is_some(),
        VmType::I16 => signed().and_then(|value| i16::try_from(value).ok()).is_some(),
        VmType::I8 => signed().and_then(|value| i8::try_from(value).ok()).is_some(),
        VmType::Isize => signed().is_some(),
        VmType::I128 => parse_pattern_i128(value).is_some(),
        VmType::U64 | VmType::Usize => unsigned().is_some(),
        VmType::U128 => parse_pattern_u128(value).is_some(),
        VmType::U32 => unsigned().and_then(|value| u32::try_from(value).ok()).is_some(),
        VmType::U16 => unsigned().and_then(|value| u16::try_from(value).ok()).is_some(),
        VmType::U8 => unsigned().and_then(|value| u8::try_from(value).ok()).is_some(),
        _ => false,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct VerifierHandlerFrame {
    /// The installing instruction is a stable function-local frame brand.
    /// Callable shape alone cannot authorize `ResumeSnapshot`: an ordinary
    /// callable with the same signature must never be mistaken for a captured
    /// continuation.
    id: u32,
    effect: DefKey,
    effect_arguments: Vec<VmGenericArgument>,
    operation: u32,
    payload_destinations: Vec<u32>,
    resume_type: VmType,
    continuation: VmContinuationPolicy,
    target: u32,
    /// A verifier join can represent several concrete one-shot suspensions
    /// reaching one shared handler body. Runtime execution has exactly one.
    continuations: Vec<VerifierContinuation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct VerifierContinuation {
    target: u32,
    dst: u32,
    registers: Vec<Option<bool>>,
    /// The continuation resumes the exact source-storage lifetime state at
    /// the performance site.  Register initialization alone cannot recover
    /// this fact: `Some(false)` means either a moved SSA value or a live,
    /// uninitialized addressable slot.
    storage_live: Vec<bool>,
    /// Every source-storage root a reference value may address.  A join of
    /// two references with distinct roots must retain both possibilities:
    /// preserving only the predecessor that happened to arrive first would
    /// permit `StorageDead` to erase the other live loan.
    reference_origins: Vec<BTreeSet<u32>>,
    snapshots: Vec<Option<u32>>,
    labels: Vec<bool>,
    /// Whether a value contains a frame-branded resumption token.  This is
    /// separate from `snapshots`: a token nested in an aggregate cannot be
    /// invoked directly, but it still cannot cross a retained-frame boundary.
    resumptions: Vec<bool>,
    performed: VerifierPerformed,
    /// Frames crossed while looking for the selected outer handler. They are
    /// absent while its clause runs and are restored when the continuation
    /// resumes, which is the operational form of deep forwarding.
    above: Vec<VerifierHandlerFrame>,
    pending_leave: Option<PendingLeave>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct VerifierPerformed {
    effect: DefKey,
    effect_arguments: Vec<VmGenericArgument>,
    operation: u32,
    arguments: Vec<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct VerifierState {
    registers: Vec<Option<bool>>,
    /// Addressable source slots have a lifetime independent from their
    /// resident value.  A live-but-uninitialized slot is a valid target for a
    /// first definition, whereas an emptied SSA register remains unavailable
    /// until a CFG edge supplies a new definition.
    storage_live: Vec<bool>,
    /// Whether a register has ever been declared as addressable source
    /// storage in this function.  Unlike `storage_live`, this fact remains
    /// true after `StorageDead` so an attacker cannot revive a dead slot by
    /// exploiting the otherwise identical empty SSA register state.
    source_storage: Vec<bool>,
    /// Source-storage roots a reference value may address. This is deliberately
    /// separate from its type: a reference remains a live loan after its
    /// owner has been moved, so StorageDead must inspect every possible root
    /// rather than only the owner's resident-value state.
    reference_origins: Vec<BTreeSet<u32>>,
    /// Provenance for first-class continuation values. `Some(frame)` means
    /// this register was produced by `CaptureResumption` for that exact live
    /// frame. The type system still sees a callable; this parallel proof fact
    /// is what prevents capability forgery through an equally typed callable.
    snapshots: Vec<Option<u32>>,
    /// A first-class lexical label shares the callable ABI but can only be
    /// invoked in the frame that minted it. This taint is propagated through
    /// aggregates because a label cannot be frozen into another callable
    /// environment even when nested inside an otherwise ordinary value.
    labels: Vec<bool>,
    /// Aggregate-aware counterpart to `snapshots`.  The exact brand remains
    /// in `snapshots` for `ResumeSnapshot`; this bit prevents a brand from
    /// being smuggled through a tuple, array, record, or shared snapshot.
    resumptions: Vec<bool>,
    handlers: Vec<VerifierHandlerFrame>,
    pending_leave: Option<PendingLeave>,
    /// Number of dynamic clause-return continuations currently being checked.
    /// Their `Return` is consumed by `ResumeReturn`, not by the function.
    resumption_return_depth: u32,
    /// Handler brands that may remain active while the current protected
    /// replay returns to its clause. A nested operation can cancel its own
    /// frame and still leave an outer replay frame to be restored by that
    /// clause-return edge; unrelated frames remain an error.
    resumption_return_handler_ids: Vec<u32>,
}

impl Deref for VerifierState {
    type Target = [Option<bool>];

    fn deref(&self) -> &Self::Target {
        &self.registers
    }
}

impl DerefMut for VerifierState {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.registers
    }
}

/// Check the frozen counterpart of MIR's lexical-label invariant.  A leave
/// need not carry a runtime label object, but its nominal brand is still a
/// capability for one destination only.  In particular, equal register types
/// are insufficient: a forged artifact must not retarget a leave to another
/// block (or write a different set of registers) under an existing brand.
fn verify_label_brand_contracts(function: &VmFunction) -> Result<(), VmArtifactError> {
    let mut contracts = BTreeMap::<(DefKey, u32), (u32, Vec<u32>, Vec<VmType>)>::new();
    for instruction in &function.instructions {
        let (brand_owner, brand_label, target, destinations) = match instruction {
            VmInstruction::Leave {
                brand_owner,
                brand_label,
                target,
                destinations,
                ..
            } => (*brand_owner, *brand_label, *target, destinations.clone()),
            // First-class labels are the dynamic spelling of the same static
            // brand.  They must therefore agree with direct `Leave`s and
            // with every other materialization of that brand; otherwise a
            // hostile artifact could forge an equally typed label that exits
            // to a contradictory destination.
            VmInstruction::MakeLabel {
                brand_owner,
                brand_label,
                target,
                destination,
                ..
            } => (*brand_owner, *brand_label, *target, vec![*destination]),
            _ => continue,
        };
        if target as usize >= function.instructions.len() {
            return Err(VmArtifactError::InvalidInstructionTarget { target });
        }
        let layout = destinations
            .iter()
            .map(|destination| register_type(function, *destination))
            .collect::<Result<Vec<_>, _>>()?;
        let contract = (target, destinations, layout);
        match contracts.get(&(brand_owner, brand_label)) {
            Some(previous) if previous != &contract => {
                return Err(VmArtifactError::InvalidLabelContract {
                    message: "label brand has contradictory destination or payload layout",
                });
            }
            Some(_) => {}
            None => {
                contracts.insert((brand_owner, brand_label), contract);
            }
        }
    }
    Ok(())
}

/// The bytecode keeps source-storage provenance as a dense binding identity
/// beside its executable register slot.  The state-machine verifier below
/// proves each slot is live or dead on every CFG path, but that alone cannot
/// detect an artifact which swaps two simultaneously-live slots at its
/// `StorageDead` instruction. Freeze the association up front so every later
/// lifecycle transition refers to the same source owner.
fn verify_source_storage_identity_contracts(function: &VmFunction) -> Result<(), VmArtifactError> {
    let mut binding_locals = BTreeMap::<u32, u32>::new();
    let mut local_bindings = BTreeMap::<u32, u32>::new();
    for instruction in &function.instructions {
        let (VmInstruction::StorageLive { binding, local }
        | VmInstruction::StorageDead { binding, local }) = instruction
        else {
            continue;
        };
        match binding_locals.insert(*binding, *local) {
            Some(expected) if expected != *local => {
                return Err(VmArtifactError::InvalidSourceStorageIdentity {
                    binding: *binding,
                    local: *local,
                    message: "source-storage binding was paired with multiple locals",
                });
            }
            _ => {}
        }
        match local_bindings.insert(*local, *binding) {
            Some(expected) if expected != *binding => {
                return Err(VmArtifactError::InvalidSourceStorageIdentity {
                    binding: *binding,
                    local: *local,
                    message: "source-storage local was paired with multiple bindings",
                });
            }
            _ => {}
        }
    }
    Ok(())
}

fn verify_function(function: &VmFunction) -> Result<(), VmArtifactError> {
    // `decode_artifact` checks these invariants while reading bytes, but a
    // candidate can also be assembled directly by an embedding host. Keep
    // the verifier boundary equally strict so two spellings of one effect
    // identity cannot receive distinct executable fingerprints.
    for register in &function.registers {
        validate_vm_type(register)?;
    }
    let declared_result = declared_result(function)?;
    validate_vm_nominal_copy_descriptors(&function.nominal_copy_descriptors)?;
    for instruction in &function.instructions {
        match instruction {
            VmInstruction::Perform {
                effect_arguments, ..
            }
            | VmInstruction::InstallHandler {
                effect_arguments, ..
            } => validate_vm_generic_arguments(effect_arguments)?,
            _ => {}
        }
    }
    verify_label_brand_contracts(function)?;
    verify_source_storage_identity_contracts(function)?;
    verify_handler_entry_boundaries(function)?;
    let mut initial = vec![None; function.registers.len()];
    if function.captures > function.parameters {
        return Err(VmArtifactError::CallArity {
            expected: function.parameters,
            found: function.captures,
        });
    }
    if function.parameters as usize > initial.len() {
        return Err(VmArtifactError::InvalidRegister {
            register: function.parameters,
        });
    }
    for state in initial.iter_mut().take(function.parameters as usize) {
        *state = Some(true);
    }
    // The callable ABI initializes its parameter register prefix before the
    // first instruction.  Source-storage freezing may give an addressable
    // capture or argument an exact mapping without emitting a child-local
    // `StorageLive`, so the verifier must carry the corresponding lifetime
    // fact as well as the definite-write fact above.
    let mut initial_storage_live = vec![false; function.registers.len()];
    for state in initial_storage_live
        .iter_mut()
        .take(function.parameters as usize)
    {
        *state = true;
    }
    let mut source_storage = vec![false; function.registers.len()];
    for state in source_storage
        .iter_mut()
        .take(function.parameters as usize)
    {
        *state = true;
    }
    for instruction in &function.instructions {
        let (VmInstruction::StorageLive { local, .. }
        | VmInstruction::StorageDead { local, .. }) = instruction
        else {
            continue;
        };
        let Some(state) = source_storage.get_mut(*local as usize) else {
            return Err(VmArtifactError::InvalidRegister { register: *local });
        };
        *state = true;
    }
    let mut incoming = vec![None; function.instructions.len()];
    if let Some(entry) = incoming.first_mut() {
        *entry = Some(VerifierState {
            registers: initial,
            storage_live: initial_storage_live,
            source_storage,
            reference_origins: vec![BTreeSet::new(); function.registers.len()],
            snapshots: vec![None; function.registers.len()],
            labels: vec![false; function.registers.len()],
            resumptions: vec![false; function.registers.len()],
            handlers: Vec::new(),
            pending_leave: None,
            resumption_return_depth: 0,
            resumption_return_handler_ids: Vec::new(),
        });
    }
    let mut worklist = if function.instructions.is_empty() {
        vec![]
    } else {
        vec![0usize]
    };
    let mut returned: Option<VmType> = None;
    // A verified VM function may be intentionally terminal: `Trap` is the
    // executable representation of the trusted source `!` abort leaf. Such
    // a function has no return edge, but it is still a complete control-flow
    // graph and must not be rejected as a malformed fallthrough.
    let mut trapped = false;
    while let Some(pc) = worklist.pop() {
        let mut states = incoming[pc].clone().expect("scheduled verifier state");
        let mut advances = true;
        let instruction = &function.instructions[pc];
        match instruction {
            VmInstruction::DeclareResult { .. } => {
                // `declared_result` above has already proven this is the
                // unique leading ABI declaration. It is not executable work.
            }
            VmInstruction::ConstUnit { dst } => {
                expect_type(function, *dst, VmType::Unit)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstI64 { dst, .. } => {
                expect_type(function, *dst, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstU8 { dst, .. } => {
                expect_type(function, *dst, VmType::U8)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstU16 { dst, .. } => {
                expect_type(function, *dst, VmType::U16)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstU32 { dst, .. } => {
                expect_type(function, *dst, VmType::U32)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstU64 { dst, .. } => {
                expect_type(function, *dst, VmType::U64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstUsize { dst, .. } => {
                expect_type(function, *dst, VmType::Usize)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstU128 { dst, .. } => {
                expect_type(function, *dst, VmType::U128)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstI8 { dst, .. } => {
                expect_type(function, *dst, VmType::I8)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstI16 { dst, .. } => {
                expect_type(function, *dst, VmType::I16)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstI32 { dst, .. } => {
                expect_type(function, *dst, VmType::I32)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstIsize { dst, .. } => {
                expect_type(function, *dst, VmType::Isize)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstI128 { dst, .. } => {
                expect_type(function, *dst, VmType::I128)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstF64 { dst, bits } => {
                if !is_canonical_f64_bits(*bits) {
                    return Err(VmArtifactError::NonCanonicalFloat { bits: *bits });
                }
                expect_type(function, *dst, VmType::F64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstF32 { dst, bits } => {
                if !is_canonical_f32_bits(*bits) {
                    return Err(VmArtifactError::NonCanonicalFloat {
                        bits: u64::from(*bits),
                    });
                }
                expect_type(function, *dst, VmType::F32)?;
                write(&mut states, *dst)?
            }
            VmInstruction::MemoryIntrinsic { dst, primitive, types, arguments } => {
                let (parameters, result) = memory_intrinsic_signature(*primitive, types)?;
                if arguments.len() != parameters.len() {
                    return Err(VmArtifactError::MalformedEncoding { message: "memory operation has the wrong arity" });
                }
                expect_type(function, *dst, result)?;
                for (&argument, parameter) in arguments.iter().zip(parameters) {
                    expect_type(function, argument, parameter)?;
                    read(&states, argument)?;
                }
                if *primitive == MemoryPrimitive::Write {
                    states[arguments[1] as usize] = Some(false);
                }
                write(&mut states, *dst)?;
            }
            VmInstruction::FloatIntrinsic {
                dst,
                primitive,
                arguments,
            } => {
                let (parameters, result) = primitive.scalar_signature();
                if arguments.len() != parameters.len() {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "floating runtime primitive has the wrong arity",
                    });
                }
                expect_type(function, *dst, vm_scalar_type(result))?;
                for (&argument, parameter) in arguments.iter().zip(parameters) {
                    expect_type(function, argument, vm_scalar_type(parameter))?;
                    read(&states, argument)?;
                }
                write(&mut states, *dst)?
            }
            VmInstruction::IntIntrinsic {
                dst,
                primitive,
                scalar,
                arguments,
            } => {
                let (parameters, result) = integer_intrinsic_signature(*primitive, *scalar)?;
                if arguments.len() != parameters.len() {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "integer runtime primitive has the wrong arity",
                    });
                }
                expect_type(function, *dst, vm_scalar_type(result))?;
                for (&argument, parameter) in arguments.iter().zip(parameters) {
                    expect_type(function, argument, vm_scalar_type(parameter))?;
                    read(&states, argument)?;
                }
                write(&mut states, *dst)?
            }
            VmInstruction::ConstBool { dst, .. } => {
                expect_type(function, *dst, VmType::Bool)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstChar { dst, value } => {
                if char::from_u32(*value).is_none() {
                    return Err(VmArtifactError::InvalidRegister { register: *dst });
                }
                expect_type(function, *dst, VmType::Char)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstText { dst, .. } => {
                expect_type(function, *dst, VmType::Text)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstStaticData {
                dst,
                tag,
                alignment,
                ..
            } => {
                let found = function
                    .registers
                    .get(*dst as usize)
                    .ok_or(VmArtifactError::InvalidRegister { register: *dst })?;
                match found {
                    VmType::StaticData {
                        element,
                        tag: found_tag,
                        alignment: found_alignment,
                    } if element.as_ref() == &VmType::U8
                        && found_tag == tag
                        && found_alignment == alignment => {}
                    _ => {
                        return Err(VmArtifactError::ResultType {
                            expected: VmType::StaticData {
                                element: Box::new(VmType::U8),
                                tag: *tag,
                                alignment: *alignment,
                            },
                            found: found.clone(),
                        });
                    }
                }
                write(&mut states, *dst)?
            }
            VmInstruction::StaticLen { dst, value } => {
                expect_type(function, *dst, VmType::Usize)?;
                let data = function
                    .registers
                    .get(*value as usize)
                    .ok_or(VmArtifactError::InvalidRegister { register: *value })?;
                if !matches!(data, VmType::StaticData { element, tag: 0x4752_414e_4449_4f53_455f_5354_4154_4943, alignment: 1 } if element.as_ref() == &VmType::U8) {
                    return Err(VmArtifactError::ResultType {
                        expected: VmType::StaticData { element: Box::new(VmType::U8), tag: 0x4752_414e_4449_4f53_455f_5354_4154_4943, alignment: 1 },
                        found: data.clone(),
                    });
                }
                read(&states, *value)?;
                write(&mut states, *dst)?
            }
            VmInstruction::StaticSubslice { dst, value, start, length } => {
                let expected = VmType::StaticData { element: Box::new(VmType::U8), tag: 0x4752_414e_4449_4f53_455f_5354_4154_4943, alignment: 1 };
                expect_type(function, *dst, expected.clone())?;
                expect_type(function, *value, expected)?;
                expect_type(function, *start, VmType::Usize)?;
                expect_type(function, *length, VmType::Usize)?;
                read(&states, *value)?;
                read(&states, *start)?;
                read(&states, *length)?;
                write(&mut states, *dst)?
            }
            VmInstruction::StaticGetBorrowShared { dst, value, index } => {
                expect_type(function, *dst, VmType::Reference { unique: false, referent: Box::new(VmType::U8) })?;
                let expected = VmType::StaticData { element: Box::new(VmType::U8), tag: 0x4752_414e_4449_4f53_455f_5354_4154_4943, alignment: 1 };
                expect_type(function, *value, expected)?;
                expect_type(function, *index, VmType::Usize)?;
                read(&states, *value)?;
                read(&states, *index)?;
                write(&mut states, *dst)?
            }
            VmInstruction::StaticAsArrayBorrow { dst, value } => {
                expect_type(function, *dst, VmType::Reference { unique: false, referent: Box::new(VmType::Array(Box::new(VmType::U8))) })?;
                expect_static_u8_type(function, *value)?;
                read(&states, *value)?; write(&mut states, *dst)?
            }
            VmInstruction::TextByteLen { dst, value } => {
                expect_type(function, *dst, VmType::Usize)?;
                expect_type(function, *value, VmType::Text)?;
                read(&states, *value)?;
                write(&mut states, *dst)?
            }
            VmInstruction::TextConcat { dst, left, right } => {
                expect_type(function, *dst, VmType::Text)?;
                for value in [left, right] {
                    expect_type(function, *value, VmType::Text)?;
                    read(&states, *value)?;
                }
                write(&mut states, *dst)?
            }
            VmInstruction::TextEq { dst, left, right } => {
                expect_type(function, *dst, VmType::U32)?;
                for value in [left, right] {
                    expect_type(function, *value, VmType::Text)?;
                    read(&states, *value)?;
                }
                write(&mut states, *dst)?
            }
            VmInstruction::TextFromUtf8Checked { dst, value } => {
                expect_type(function, *dst, VmType::Text)?;
                expect_type(function, *value, VmType::Bytes)?;
                read(&states, *value)?;
                write(&mut states, *dst)?
            }
            VmInstruction::TextAsBytes { dst, value } => {
                expect_type(function, *dst, VmType::Bytes)?;
                expect_type(function, *value, VmType::Text)?;
                read(&states, *value)?;
                write(&mut states, *dst)?
            }
            VmInstruction::CharFromU32Checked { dst, value } => {
                expect_type(function, *dst, VmType::Char)?;
                expect_type(function, *value, VmType::U32)?;
                read(&states, *value)?;
                write(&mut states, *dst)?
            }
            VmInstruction::CharToU32 { dst, value } => {
                expect_type(function, *dst, VmType::U32)?;
                expect_type(function, *value, VmType::Char)?;
                read(&states, *value)?;
                write(&mut states, *dst)?
            }
            VmInstruction::BytesLen { dst, value }
            | VmInstruction::BytesUtf8ValidUpTo { dst, value } => {
                expect_type(function, *dst, VmType::Usize)?;
                expect_type(function, *value, VmType::Bytes)?;
                read(&states, *value)?;
                write(&mut states, *dst)?
            }
            VmInstruction::Blake3 { dst, value } => {
                expect_type(function, *dst, VmType::Bytes)?;
                expect_type(function, *value, VmType::Bytes)?;
                read(&states, *value)?;
                write(&mut states, *dst)?
            }
            VmInstruction::BytesConcat { dst, left, right } => {
                expect_type(function, *dst, VmType::Bytes)?;
                for value in [left, right] {
                    expect_type(function, *value, VmType::Bytes)?;
                    read(&states, *value)?;
                }
                write(&mut states, *dst)?
            }
            VmInstruction::BytesGet { dst, bytes, index } => {
                expect_type(function, *dst, VmType::U8)?;
                expect_type(function, *bytes, VmType::Bytes)?;
                expect_type(function, *index, VmType::Usize)?;
                read(&states, *bytes)?;
                read(&states, *index)?;
                write(&mut states, *dst)?
            }
            VmInstruction::BytesSlice {
                dst,
                bytes,
                start,
                end,
            } => {
                expect_type(function, *dst, VmType::Bytes)?;
                expect_type(function, *bytes, VmType::Bytes)?;
                expect_type(function, *start, VmType::Usize)?;
                expect_type(function, *end, VmType::Usize)?;
                for value in [bytes, start, end] {
                    read(&states, *value)?;
                }
                write(&mut states, *dst)?
            }
            VmInstruction::BytesFromArrayMove { dst, value } => {
                expect_type(function, *dst, VmType::Bytes)?;
                expect_type(function, *value, VmType::Array(Box::new(VmType::U8)))?;
                read(&states, *value)?;
                write(&mut states, *dst)?
            }
            VmInstruction::BytesToArray { dst, value } => {
                expect_type(function, *dst, VmType::Array(Box::new(VmType::U8)))?;
                expect_type(function, *value, VmType::Bytes)?;
                read(&states, *value)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ArrayNew {
                dst,
                length,
                fill,
                element_type,
            } => {
                expect_type(
                    function,
                    *dst,
                    VmType::Array(Box::new(element_type.clone())),
                )?;
                expect_type(function, *length, VmType::Usize)?;
                expect_type(function, *fill, element_type.clone())?;
                read(&states, *length)?;
                read(&states, *fill)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArrayEmpty { dst, element_type } => {
                expect_type(
                    function,
                    *dst,
                    VmType::Array(Box::new(element_type.clone())),
                )?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArrayLen {
                dst,
                value,
                element_type,
            }
            | VmInstruction::ArrayCapacity {
                dst,
                value,
                element_type,
            } => {
                expect_type(function, *dst, VmType::Usize)?;
                expect_type(
                    function,
                    *value,
                    VmType::Reference {
                        unique: false,
                        referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                    },
                )?;
                read(&states, *value)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArrayUtf8ValidUpTo { dst, value } => {
                expect_type(function, *dst, VmType::Usize)?;
                expect_type(
                    function,
                    *value,
                    VmType::Reference {
                        unique: false,
                        referent: Box::new(VmType::Array(Box::new(VmType::U8))),
                    },
                )?;
                read(&states, *value)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArrayPushUtf8Char { value, character } => {
                expect_type(function, *value, VmType::Reference { unique: true, referent: Box::new(VmType::Array(Box::new(VmType::U8))) })?;
                expect_type(function, *character, VmType::Char)?;
                read(&states, *value)?;
                read(&states, *character)?;
                states.registers[*character as usize] = Some(false);
            }
            VmInstruction::ArrayInsertUtf8FromSlice {
                dst,
                value,
                index,
                source,
                start,
                length,
            } => {
                expect_type(function, *dst, VmType::Usize)?;
                expect_type(function, *value, VmType::Reference {
                    unique: true,
                    referent: Box::new(VmType::Array(Box::new(VmType::U8))),
                })?;
                expect_type(function, *index, VmType::Usize)?;
                expect_type(function, *source, VmType::Reference {
                    unique: false,
                    referent: Box::new(VmType::Array(Box::new(VmType::U8))),
                })?;
                expect_type(function, *start, VmType::Usize)?;
                expect_type(function, *length, VmType::Usize)?;
                read(&states, *value)?;
                read(&states, *index)?;
                read(&states, *source)?;
                read(&states, *start)?;
                read(&states, *length)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArrayPopUtf8Char { dst, value } => {
                expect_type(function, *dst, VmType::Tuple(vec![VmType::Char, VmType::Usize]))?;
                expect_type(function, *value, VmType::Reference {
                    unique: true,
                    referent: Box::new(VmType::Array(Box::new(VmType::U8))),
                })?;
                read(&states, *value)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArrayUtf8CharAt { dst, value, start, length, index } => {
                expect_type(function, *dst, VmType::Tuple(vec![VmType::Char, VmType::Usize]))?;
                expect_type(function, *value, VmType::Reference {
                    unique: false,
                    referent: Box::new(VmType::Array(Box::new(VmType::U8))),
                })?;
                for register in [*value, *start, *length, *index] {
                    read(&states, register)?;
                }
                expect_type(function, *start, VmType::Usize)?;
                expect_type(function, *length, VmType::Usize)?;
                expect_type(function, *index, VmType::Usize)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArrayExtendFromSlice {
                value,
                source,
                start,
                length,
                element_type,
            } => {
                expect_type(
                    function,
                    *value,
                    VmType::Reference {
                        unique: true,
                        referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                    },
                )?;
                expect_type(
                    function,
                    *source,
                    VmType::Reference {
                        unique: false,
                        referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                    },
                )?;
                expect_type(function, *start, VmType::Usize)?;
                expect_type(function, *length, VmType::Usize)?;
                read(&states, *value)?;
                read(&states, *source)?;
                read(&states, *start)?;
                read(&states, *length)?;
            }
            VmInstruction::ArrayInsertMove {
                value,
                index,
                item,
                element_type,
            } => {
                expect_type(function, *value, VmType::Reference {
                    unique: true,
                    referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                })?;
                expect_type(function, *index, VmType::Usize)?;
                expect_type(function, *item, element_type.clone())?;
                read(&states, *value)?;
                read(&states, *index)?;
                read(&states, *item)?;
                states.registers[*item as usize] = Some(false);
            }
            VmInstruction::ArrayRemoveMove {
                dst,
                value,
                index,
                element_type,
            } => {
                expect_type(function, *dst, element_type.clone())?;
                expect_type(function, *value, VmType::Reference {
                    unique: true,
                    referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                })?;
                expect_type(function, *index, VmType::Usize)?;
                read(&states, *value)?;
                read(&states, *index)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArrayAppendMove {
                value,
                source,
                element_type,
            } => {
                expect_type(function, *value, VmType::Reference {
                    unique: true,
                    referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                })?;
                expect_type(function, *source, VmType::Array(Box::new(element_type.clone())))?;
                read(&states, *value)?;
                read(&states, *source)?;
                states.registers[*source as usize] = Some(false);
            }
            VmInstruction::ArrayTruncateDiscard {
                value,
                length,
                element_type,
            } => {
                expect_type(function, *value, VmType::Reference {
                    unique: true,
                    referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                })?;
                expect_type(function, *length, VmType::Usize)?;
                read(&states, *value)?;
                read(&states, *length)?;
            }
            VmInstruction::ArrayReverseMove {
                value,
                element_type,
            } => {
                expect_type(function, *value, VmType::Reference {
                    unique: true,
                    referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                })?;
                read(&states, *value)?;
            }
            VmInstruction::ArraySplitOffMove {
                dst,
                value,
                index,
                element_type,
            } => {
                expect_type(function, *dst, VmType::Array(Box::new(element_type.clone())))?;
                expect_type(function, *value, VmType::Reference {
                    unique: true,
                    referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                })?;
                expect_type(function, *index, VmType::Usize)?;
                read(&states, *value)?;
                read(&states, *index)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArraySplitBorrowUnique {
                dst,
                value,
                start,
                length,
                index,
                element_type,
            } => {
                let array = VmType::Reference {
                    unique: true,
                    referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                };
                expect_type(function, *dst, VmType::Tuple(vec![array.clone(), array.clone()]))?;
                expect_type(function, *value, array)?;
                for register in [start, length, index] {
                    expect_type(function, *register, VmType::Usize)?;
                    read(&states, *register)?;
                }
                read(&states, *value)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArrayInsertFromSlice {
                value,
                index,
                source,
                start,
                length,
                element_type,
            } => {
                expect_type(function, *value, VmType::Reference {
                    unique: true,
                    referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                })?;
                expect_type(function, *index, VmType::Usize)?;
                expect_type(function, *source, VmType::Reference {
                    unique: false,
                    referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                })?;
                expect_type(function, *start, VmType::Usize)?;
                expect_type(function, *length, VmType::Usize)?;
                read(&states, *value)?;
                read(&states, *index)?;
                read(&states, *source)?;
                read(&states, *start)?;
                read(&states, *length)?;
            }
            VmInstruction::ArrayGetCopy {
                dst,
                value,
                index,
                element_type,
            } => {
                expect_type(function, *dst, element_type.clone())?;
                expect_type(
                    function,
                    *value,
                    VmType::Reference {
                        unique: false,
                        referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                    },
                )?;
                expect_type(function, *index, VmType::Usize)?;
                read(&states, *value)?;
                read(&states, *index)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArrayGetMove {
                dst,
                value,
                index,
                element_type,
            } => {
                expect_type(function, *dst, element_type.clone())?;
                expect_type(
                    function,
                    *value,
                    VmType::Reference {
                        unique: true,
                        referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                    },
                )?;
                expect_type(function, *index, VmType::Usize)?;
                read(&states, *value)?;
                read(&states, *index)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArrayGetBorrow {
                dst,
                value,
                index,
                unique,
                element_type,
            } => {
                expect_type(
                    function,
                    *dst,
                    VmType::Reference {
                        unique: *unique,
                        referent: Box::new(element_type.clone()),
                    },
                )?;
                expect_type(
                    function,
                    *value,
                    VmType::Reference {
                        unique: *unique,
                        referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                    },
                )?;
                expect_type(function, *index, VmType::Usize)?;
                read(&states, *value)?;
                read(&states, *index)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArraySetMove {
                value,
                index,
                item,
                element_type,
            } => {
                expect_type(
                    function,
                    *value,
                    VmType::Reference {
                        unique: true,
                        referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                    },
                )?;
                expect_type(function, *index, VmType::Usize)?;
                expect_type(function, *item, element_type.clone())?;
                read(&states, *value)?;
                read(&states, *index)?;
                read(&states, *item)?;
                states.registers[*item as usize] = Some(false);
            }
            VmInstruction::ArrayPushMove {
                value,
                item,
                element_type,
            } => {
                expect_type(
                    function,
                    *value,
                    VmType::Reference {
                        unique: true,
                        referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                    },
                )?;
                expect_type(function, *item, element_type.clone())?;
                read(&states, *value)?;
                read(&states, *item)?;
                states.registers[*item as usize] = Some(false);
            }
            VmInstruction::ArrayPopMove {
                dst,
                value,
                element_type,
            } => {
                expect_type(function, *dst, element_type.clone())?;
                expect_type(
                    function,
                    *value,
                    VmType::Reference {
                        unique: true,
                        referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                    },
                )?;
                read(&states, *value)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArrayReserve {
                value,
                additional,
                element_type,
            } => {
                expect_type(
                    function,
                    *value,
                    VmType::Reference {
                        unique: true,
                        referent: Box::new(VmType::Array(Box::new(element_type.clone()))),
                    },
                )?;
                expect_type(function, *additional, VmType::Usize)?;
                read(&states, *value)?;
                read(&states, *additional)?;
            }
            VmInstruction::ArrayFinishDrained {
                value,
                element_type,
            } => {
                expect_type(
                    function,
                    *value,
                    VmType::Array(Box::new(element_type.clone())),
                )?;
                read(&states, *value)?;
                states.registers[*value as usize] = Some(false);
            }
            VmInstruction::U32CheckedAdd { dst, left, right }
            | VmInstruction::U32CheckedSub { dst, left, right }
            | VmInstruction::U32CheckedMul { dst, left, right }
            | VmInstruction::U32CheckedDiv { dst, left, right }
            | VmInstruction::U32CheckedRem { dst, left, right }
            | VmInstruction::U32WrappingAdd { dst, left, right }
            | VmInstruction::U32WrappingSub { dst, left, right }
            | VmInstruction::U32WrappingMul { dst, left, right }
            | VmInstruction::U32WrappingShl { dst, left, right }
            | VmInstruction::U32WrappingShr { dst, left, right }
            | VmInstruction::U32CheckedShl { dst, left, right }
            | VmInstruction::U32CheckedShr { dst, left, right } => {
                expect_type(function, *dst, VmType::U32)?;
                for value in [left, right] {
                    expect_type(function, *value, VmType::U32)?;
                    read(&states, *value)?;
                }
                write(&mut states, *dst)?
            }
            VmInstruction::U32Eq { dst, left, right }
            | VmInstruction::U32Lt { dst, left, right }
            | VmInstruction::U32Le { dst, left, right } => {
                expect_type(function, *dst, VmType::Bool)?;
                for value in [left, right] {
                    expect_type(function, *value, VmType::U32)?;
                    read(&states, *value)?;
                }
                write(&mut states, *dst)?
            }
            VmInstruction::U32ToUsize { dst, value } => {
                expect_type(function, *dst, VmType::Usize)?;
                expect_type(function, *value, VmType::U32)?;
                read(&states, *value)?;
                write(&mut states, *dst)?
            }
            VmInstruction::UsizeToU32Checked { dst, value } => {
                expect_type(function, *dst, VmType::U32)?;
                expect_type(function, *value, VmType::Usize)?;
                read(&states, *value)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToU32Checked { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::U32)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToU32Wrapping { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::U32)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToUsizeChecked { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::Usize)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToUsizeWrapping { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::Usize)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToU8Checked { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::U8)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToU8Wrapping { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::U8)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToU16Checked { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::U16)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToU16Wrapping { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::U16)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToI16Checked { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::I16)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToI16Wrapping { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::I16)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToI32Checked { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::I32)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToI32Wrapping { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::I32)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToI8Checked { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::I8)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToI8Wrapping { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::I8)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToU64Checked { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::U64)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToU64Wrapping { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::U64)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToIsizeChecked { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::Isize)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToIsizeWrapping { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::Isize)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToU128Checked { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::U128)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToU128Wrapping { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::U128)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToI128Checked { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::I128)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::I64ToI128Wrapping { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::I128)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::MakeTuple { dst, fields } => {
                let expected = match register_type(function, *dst)? {
                    VmType::Tuple(fields) => fields,
                    found => {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *dst,
                            expected: VmType::Tuple(Vec::new()),
                            found,
                        });
                    }
                };
                if expected.len() != fields.len() {
                    return Err(VmArtifactError::CallArity {
                        expected: expected.len() as u32,
                        found: fields.len() as u32,
                    });
                }
                for (field, expected) in fields.iter().zip(expected) {
                    read(&states, *field)?;
                    let found = register_type(function, *field)?;
                    if found != expected {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *field,
                            expected,
                            found,
                        });
                    }
                }
                write(&mut states, *dst)?;
                states.labels[*dst as usize] = fields
                    .iter()
                    .any(|field| states.labels[*field as usize]);
                states.resumptions[*dst as usize] = fields
                    .iter()
                    .any(|field| states.resumptions[*field as usize]);
            }
            VmInstruction::MakeArray {
                dst,
                fields,
                element_type,
            } => {
                let expected = VmType::Array(Box::new(element_type.clone()));
                let found = register_type(function, *dst)?;
                if found != expected {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected,
                        found,
                    });
                }
                for field in fields {
                    read(&states, *field)?;
                    let found = register_type(function, *field)?;
                    if found != *element_type {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *field,
                            expected: element_type.clone(),
                            found,
                        });
                    }
                }
                write(&mut states, *dst)?;
                states.labels[*dst as usize] = fields
                    .iter()
                    .any(|field| states.labels[*field as usize]);
                states.resumptions[*dst as usize] = fields
                    .iter()
                    .any(|field| states.resumptions[*field as usize]);
            }
            VmInstruction::MakeRecord {
                dst,
                definition,
                fields,
                field_types,
            } => {
                let destination_type = register_type(function, *dst)?;
                match &destination_type {
                    VmType::Nominal {
                        definition: actual, ..
                    } if *actual == *definition => {}
                    found => {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *dst,
                            expected: VmType::Nominal {
                                definition: *definition,
                                arguments: Vec::new(),
                            },
                            found: found.clone(),
                        });
                    }
                }
                let layout = nominal_record_layout(function, &destination_type)?;
                if field_types != layout {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "record field layout does not match nominal descriptor",
                    });
                }
                if fields.len() != field_types.len() {
                    return Err(VmArtifactError::CallArity {
                        expected: field_types.len() as u32,
                        found: fields.len() as u32,
                    });
                }
                for (field, expected) in fields.iter().zip(field_types) {
                    read(&states, *field)?;
                    let found = register_type(function, *field)?;
                    if found != *expected {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *field,
                            expected: expected.clone(),
                            found,
                        });
                    }
                }
                write(&mut states, *dst)?;
                states.labels[*dst as usize] = fields
                    .iter()
                    .any(|field| states.labels[*field as usize]);
                states.resumptions[*dst as usize] = fields
                    .iter()
                    .any(|field| states.resumptions[*field as usize]);
            }
            VmInstruction::MakeEnum {
                dst,
                definition,
                variant,
                fields,
                field_types,
            } => {
                let destination_type = register_type(function, *dst)?;
                match &destination_type {
                    VmType::Nominal {
                        definition: actual, ..
                    } if *actual == *definition => {}
                    found => {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *dst,
                            expected: VmType::Nominal {
                                definition: *definition,
                                arguments: Vec::new(),
                            },
                            found: found.clone(),
                        });
                    }
                }
                let layout = nominal_variant_layout(function, &destination_type, *variant)?;
                if field_types != layout {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "enum field layout does not match nominal descriptor",
                    });
                }
                if fields.len() != field_types.len() {
                    return Err(VmArtifactError::CallArity {
                        expected: field_types.len() as u32,
                        found: fields.len() as u32,
                    });
                }
                for (field, expected) in fields.iter().zip(field_types) {
                    read(&states, *field)?;
                    let found = register_type(function, *field)?;
                    if found != *expected {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *field,
                            expected: expected.clone(),
                            found,
                        });
                    }
                }
                write(&mut states, *dst)?;
                states.labels[*dst as usize] = fields
                    .iter()
                    .any(|field| states.labels[*field as usize]);
                states.resumptions[*dst as usize] = fields
                    .iter()
                    .any(|field| states.resumptions[*field as usize]);
            }
            VmInstruction::ProjectRecord {
                dst,
                base,
                index,
                field_count,
                field_type,
            } => {
                if index >= field_count {
                    return Err(VmArtifactError::InvalidRegister { register: *index });
                }
                read(&states, *base)?;
                let base_type = register_type(function, *base)?;
                if !matches!(base_type, VmType::Nominal { .. }) {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *base,
                        expected: VmType::Nominal {
                            definition: DefKey(Digest::of_bytes(b"record-base")),
                            arguments: Vec::new(),
                        },
                        found: register_type(function, *base)?,
                    });
                }
                if !nominal_projection_matches_layout(
                    function,
                    &base_type,
                    *index,
                    *field_count,
                    field_type,
                )? {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "nominal projection layout does not match frozen descriptor",
                    });
                }
                let found = register_type(function, *dst)?;
                if found != *field_type {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: field_type.clone(),
                        found,
                    });
                }
                write(&mut states, *dst)?;
                states.labels[*dst as usize] = states.labels[*base as usize];
                states.resumptions[*dst as usize] = states.resumptions[*base as usize];
            }
            VmInstruction::ProjectTuple {
                dst,
                base,
                index,
                field_count,
                field_type,
            } => {
                if *index >= *field_count {
                    return Err(VmArtifactError::InvalidRegister { register: *index });
                }
                read(&states, *base)?;
                let VmType::Tuple(fields) = register_type(function, *base)? else {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *base,
                        expected: VmType::Tuple(Vec::new()),
                        found: register_type(function, *base)?,
                    });
                };
                if fields.len() != *field_count as usize
                    || fields.get(*index as usize) != Some(field_type)
                    || register_type(function, *dst)? != *field_type
                {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: field_type.clone(),
                        found: register_type(function, *dst)?,
                    });
                }
                write(&mut states, *dst)?;
                states.labels[*dst as usize] = states.labels[*base as usize];
                states.resumptions[*dst as usize] = states.resumptions[*base as usize];
            }
            VmInstruction::ProjectArray {
                dst,
                base,
                index,
                field_count,
                element_type,
            } => {
                if *index >= *field_count {
                    return Err(VmArtifactError::InvalidRegister { register: *index });
                }
                read(&states, *base)?;
                let VmType::Array(actual) = register_type(function, *base)? else {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *base,
                        expected: VmType::Array(Box::new(element_type.clone())),
                        found: register_type(function, *base)?,
                    });
                };
                if actual.as_ref() != element_type
                    || register_type(function, *dst)? != *element_type
                {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: element_type.clone(),
                        found: register_type(function, *dst)?,
                    });
                }
                write(&mut states, *dst)?;
                states.labels[*dst as usize] = states.labels[*base as usize];
                states.resumptions[*dst as usize] = states.resumptions[*base as usize];
            }
            VmInstruction::UpdateRecord {
                dst,
                base,
                index,
                field_count,
                value,
                field_type,
            } => {
                if index >= field_count {
                    return Err(VmArtifactError::InvalidRegister { register: *index });
                }
                read(&states, *base)?;
                read(&states, *value)?;
                let base_type = register_type(function, *base)?;
                if !matches!(base_type, VmType::Nominal { .. }) {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *base,
                        expected: VmType::Nominal {
                            definition: DefKey(Digest::of_bytes(b"record-base")),
                            arguments: Vec::new(),
                        },
                        found: base_type,
                    });
                }
                let layout = nominal_record_layout(function, &base_type)?;
                if *field_count as usize != layout.len()
                    || layout.get(*index as usize) != Some(field_type)
                {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "record update layout does not match nominal descriptor",
                    });
                }
                if register_type(function, *dst)? != base_type {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: base_type,
                        found: register_type(function, *dst)?,
                    });
                }
                if register_type(function, *value)? != *field_type {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *value,
                        expected: field_type.clone(),
                        found: register_type(function, *value)?,
                    });
                }
                write(&mut states, *dst)?
            }
            VmInstruction::PatternTest {
                dst,
                subject,
                pattern,
            } => {
                read(&states, *subject)?;
                expect_type(function, *dst, VmType::Bool)?;
                verify_pattern(pattern, &register_type(function, *subject)?)?;
                write(&mut states, *dst)?
            }
            VmInstruction::Perform {
                dst,
                effect,
                effect_arguments,
                operation,
                arguments,
            } => {
                for argument in arguments {
                    read(&states, *argument)?;
                }
                if let Some(index) = states.handlers.iter().rposition(|frame| {
                    frame.continuations.is_empty()
                        && frame.effect == *effect
                        && frame.effect_arguments == *effect_arguments
                        && frame.operation == *operation
                }) {
                    let above = states.handlers.split_off(index + 1);
                    let frame = states.handlers[index].clone();
                    if frame.payload_destinations.len() != arguments.len() {
                        return Err(VmArtifactError::CallArity {
                            expected: frame.payload_destinations.len() as u32,
                            found: arguments.len() as u32,
                        });
                    }
                    if register_type(function, *dst)? != frame.resume_type {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *dst,
                            expected: frame.resume_type,
                            found: register_type(function, *dst)?,
                        });
                    }
                    let saved = states.registers.clone();
                    for (destination, argument) in frame.payload_destinations.iter().zip(arguments)
                    {
                        same_type(function, *destination, *argument)?;
                        write(&mut states, *destination)?;
                    }
                    states.handlers[index].continuations = vec![VerifierContinuation {
                        target: (pc + 1) as u32,
                        dst: *dst,
                        registers: saved,
                        storage_live: states.storage_live.clone(),
                        reference_origins: states.reference_origins.clone(),
                        snapshots: states.snapshots.clone(),
                        labels: states.labels.clone(),
                        resumptions: states.resumptions.clone(),
                        performed: VerifierPerformed {
                            effect: *effect,
                            effect_arguments: effect_arguments.clone(),
                            operation: *operation,
                            arguments: arguments.clone(),
                        },
                        above,
                        pending_leave: states.pending_leave.clone(),
                    }];
                    propagate_state(&mut incoming, &mut worklist, frame.target, &states)?;
                    advances = false;
                } else {
                    // The verifier validates register initialization and keeps
                    // the result type declared by the compiler. Protocol
                    // signature checking and handler evidence are source-level
                    // facts, deliberately not duplicated by the artifact layer.
                    write(&mut states, *dst)?;
                }
            }
            VmInstruction::InstallHandler {
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                resume_type,
                continuation,
                target,
            } => {
                if matches!(continuation, VmContinuationPolicy::Replay { uses } if *uses < 2) {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                validate_vm_type(resume_type)?;
                // Source `!` is represented by the VM's Unit leaf. A
                // terminal frame never resumes its protected computation, so
                // admitting any other result ABI would manufacture a second,
                // uncheckable interpretation of the same operation identity
                // at a caller/callee handler boundary.
                if *continuation == VmContinuationPolicy::Terminal
                    && *resume_type != VmType::Unit
                {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "terminal handler has a non-unit resume type",
                    });
                }
                if function.instructions.get(*target as usize).is_none() {
                    return Err(VmArtifactError::InvalidInstructionTarget { target: *target });
                }
                let mut destinations = BTreeSet::new();
                for destination in payload_destinations {
                    register_type(function, *destination)?;
                    if !destinations.insert(*destination) {
                        return Err(VmArtifactError::InvalidRegister {
                            register: *destination,
                        });
                    }
                }
                states.handlers.push(VerifierHandlerFrame {
                    id: pc as u32,
                    effect: *effect,
                    effect_arguments: effect_arguments.clone(),
                    operation: *operation,
                    payload_destinations: payload_destinations.clone(),
                    resume_type: resume_type.clone(),
                    continuation: *continuation,
                    target: *target,
                    continuations: Vec::new(),
                });
                if *continuation == VmContinuationPolicy::Terminal {
                    // A terminal performance may happen in an ordinary callee
                    // rather than in this function's visible CFG. Model that
                    // exceptional transfer with initialized payload registers
                    // so the terminal target and its mandatory cancellation
                    // are verified even though the normal call edge cannot
                    // return successfully.
                    let mut terminal = states.clone();
                    for destination in payload_destinations {
                        write(&mut terminal, *destination)?;
                    }
                    propagate_state(&mut incoming, &mut worklist, *target, &terminal)?;
                }
            }
            VmInstruction::UninstallHandler => {
                let Some(frame) = states.handlers.pop() else {
                    return Err(VmArtifactError::HandlerStackUnderflow);
                };
                if !frame.continuations.is_empty() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                expire_snapshot_brand(&mut states.snapshots, frame.id);
            }
            VmInstruction::Resume { value } => {
                read(&states, *value)?;
                let Some(frame) = states.handlers.last_mut() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.continuation == VmContinuationPolicy::Terminal
                    || frame.continuations.is_empty()
                {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                if frame.continuation.is_replay() {
                    // Exact multi-shot contracts return to their clause after
                    // every invocation so the bounded counter can be carried
                    // forward. A tail `Resume` would abandon that evidence.
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                let found = register_type(function, *value)?;
                if found != frame.resume_type {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *value,
                        expected: frame.resume_type.clone(),
                        found,
                    });
                }
                let continuations = match frame.continuation {
                    VmContinuationPolicy::Consume => std::mem::take(&mut frame.continuations),
                    VmContinuationPolicy::Replay { .. } => frame.continuations.clone(),
                    VmContinuationPolicy::Terminal => {
                        return Err(VmArtifactError::HandlerResumeUnavailable);
                    }
                };
                let replaying = frame.continuation.is_replay();
                for continuation in continuations {
                    let mut resumed_handlers = states.handlers.clone();
                    if replaying {
                        resumed_handlers
                            .last_mut()
                            .expect("active handler frame exists")
                            .continuations
                            .clear();
                    }
                    resumed_handlers.extend(continuation.above);
                    let mut resumed = VerifierState {
                        registers: continuation.registers,
                        storage_live: continuation.storage_live,
                        source_storage: states.source_storage.clone(),
                        reference_origins: continuation.reference_origins,
                        snapshots: continuation.snapshots,
                        labels: continuation.labels,
                        resumptions: continuation.resumptions,
                        handlers: resumed_handlers,
                        pending_leave: continuation.pending_leave,
                        resumption_return_depth: states.resumption_return_depth,
                        resumption_return_handler_ids: states.resumption_return_handler_ids.clone(),
                    };
                    write(&mut resumed, continuation.dst)?;
                    propagate_state(&mut incoming, &mut worklist, continuation.target, &resumed)?;
                }
                advances = false;
            }
            VmInstruction::ResumeReturn { dst, value } => {
                read(&states, *value)?;
                let Some(frame) = states.handlers.last() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.continuation == VmContinuationPolicy::Terminal
                    || frame.continuations.is_empty()
                {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let continuation = frame
                    .continuations
                    .first()
                    .expect("nonempty replay continuation")
                    .clone();
                let found = register_type(function, *value)?;
                if found != frame.resume_type {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *value,
                        expected: frame.resume_type.clone(),
                        found,
                    });
                }
                // The resumed path returns from the enclosing function after
                // its protected computation completes.  A replay-only root
                // shape can have the same type as the resume argument, but
                // an interprocedural one-shot continuation commonly does
                // not (for example `Unit -> i64`).
                let result = register_type(function, *dst)?;
                let function_result = return_type(function)?;
                if result != frame.resume_type && result != function_result {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: function_result,
                        found: result,
                    });
                }
                let mut resumed_handlers = states.handlers.clone();
                resumed_handlers
                    .last_mut()
                    .expect("active resumable handler exists")
                    .continuations
                    .clear();
                resumed_handlers.extend(continuation.above.clone());
                let resumption_return_handler_ids =
                    resumed_handlers.iter().map(|frame| frame.id).collect();
                let mut resumed = VerifierState {
                    registers: continuation.registers,
                    storage_live: continuation.storage_live,
                    source_storage: states.source_storage.clone(),
                    reference_origins: continuation.reference_origins,
                    snapshots: continuation.snapshots,
                    labels: continuation.labels,
                    resumptions: continuation.resumptions,
                    handlers: resumed_handlers,
                    pending_leave: continuation.pending_leave,
                    resumption_return_depth: states.resumption_return_depth.saturating_add(1),
                    resumption_return_handler_ids,
                };
                write(&mut resumed, continuation.dst)?;
                propagate_state(&mut incoming, &mut worklist, continuation.target, &resumed)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::CaptureResumption { dst } => {
                let Some(frame) = states.handlers.last() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.continuation == VmContinuationPolicy::Terminal
                    || frame.continuations.is_empty()
                {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let found = register_type(function, *dst)?;
                let VmType::Callable { parameters, .. } = &found else {
                    return Err(VmArtifactError::NotCallable { register: *dst });
                };
                let frame_id = frame.id;
                let expected = VmType::Callable {
                    safety: Safety::Safe,
                    parameters: vec![frame.resume_type.clone()],
                    // A resumption returns to its suspended computation, so
                    // its result is frame-specific. Its effect row is the
                    // residual outward row from Core; it remains part of the
                    // callable ABI instead of being erased at this boundary.
                    result: Box::new(match &found {
                        VmType::Callable { result, .. } => (**result).clone(),
                        _ => unreachable!("callable was checked above"),
                    }),
                    effects: match &found {
                        VmType::Callable { effects, .. } => effects.clone(),
                        _ => unreachable!("callable was checked above"),
                    },
                };
                if parameters.as_slice() != [frame.resume_type.clone()] {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected,
                        found,
                    });
                }
                write(&mut states, *dst)?;
                states.snapshots[*dst as usize] = Some(frame_id);
                states.labels[*dst as usize] = false;
                states.resumptions[*dst as usize] = true;
            }
            VmInstruction::ResumeSnapshot { snapshot, value } => {
                read(&states, *snapshot)?;
                read(&states, *value)?;
                let Some(frame_id) = states.snapshots[*snapshot as usize] else {
                    // The callable type is necessary but not sufficient: the
                    // value must originate in this live handler stack.
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                let Some(index) = states
                    .handlers
                    .iter()
                    .rposition(|frame| frame.id == frame_id)
                else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                let frame = &mut states.handlers[index];
                if frame.continuation == VmContinuationPolicy::Terminal
                    || frame.continuations.is_empty()
                {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let VmType::Callable { parameters, .. } = register_type(function, *snapshot)?
                else {
                    return Err(VmArtifactError::NotCallable {
                        register: *snapshot,
                    });
                };
                if parameters.as_slice() != [frame.resume_type.clone()]
                    || register_type(function, *value)? != frame.resume_type
                {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                let continuations = match frame.continuation {
                    VmContinuationPolicy::Consume => std::mem::take(&mut frame.continuations),
                    VmContinuationPolicy::Replay { .. } => frame.continuations.clone(),
                    VmContinuationPolicy::Terminal => {
                        return Err(VmArtifactError::HandlerResumeUnavailable);
                    }
                };
                let replaying = frame.continuation.is_replay();
                // A non-local snapshot transfer abandons frames installed
                // after the captured frame, then reinstates precisely the
                // frames saved with its continuation. This is the verifier
                // counterpart of the VM's deep-handler restoration rule.
                let prefix = states.handlers[..=index].to_vec();
                for continuation in continuations {
                    let mut resumed_handlers = prefix.clone();
                    if replaying {
                        resumed_handlers
                            .last_mut()
                            .expect("captured handler frame exists")
                            .continuations
                            .clear();
                    }
                    resumed_handlers.extend(continuation.above);
                    let mut resumed = VerifierState {
                        registers: continuation.registers,
                        storage_live: continuation.storage_live,
                        source_storage: states.source_storage.clone(),
                        reference_origins: continuation.reference_origins,
                        snapshots: continuation.snapshots,
                        labels: continuation.labels,
                        resumptions: continuation.resumptions,
                        handlers: resumed_handlers,
                        pending_leave: continuation.pending_leave,
                        resumption_return_depth: states.resumption_return_depth,
                        resumption_return_handler_ids: states.resumption_return_handler_ids.clone(),
                    };
                    write(&mut resumed, continuation.dst)?;
                    propagate_state(&mut incoming, &mut worklist, continuation.target, &resumed)?;
                }
                advances = false;
            }
            VmInstruction::Forward => {
                let Some(mut declined) = states.handlers.pop() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if declined.continuations.is_empty() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let continuations = std::mem::take(&mut declined.continuations);
                for continuation in continuations {
                    let Some(index) = states.handlers.iter().rposition(|frame| {
                        frame.continuations.is_empty()
                            && frame.effect == continuation.performed.effect
                            && frame.effect_arguments == continuation.performed.effect_arguments
                            && frame.operation == continuation.performed.operation
                    }) else {
                        return Err(VmArtifactError::UnhandledEffect {
                            effect: continuation.performed.effect,
                            effect_arguments: continuation.performed.effect_arguments,
                            operation: continuation.performed.operation,
                        });
                    };
                    let mut forwarded = states.clone();
                    let mut crossed = forwarded.handlers.split_off(index + 1);
                    let outer = forwarded.handlers[index].clone();
                    if outer.payload_destinations.len() != continuation.performed.arguments.len() {
                        return Err(VmArtifactError::CallArity {
                            expected: outer.payload_destinations.len() as u32,
                            found: continuation.performed.arguments.len() as u32,
                        });
                    }
                    forwarded.registers = continuation.registers.clone();
                    forwarded.storage_live = continuation.storage_live.clone();
                    forwarded.reference_origins = continuation.reference_origins.clone();
                    forwarded.snapshots = continuation.snapshots.clone();
                    forwarded.labels = continuation.labels.clone();
                    forwarded.resumptions = continuation.resumptions.clone();
                    for (destination, argument) in outer
                        .payload_destinations
                        .iter()
                        .zip(&continuation.performed.arguments)
                    {
                        same_type(function, *destination, *argument)?;
                        write(&mut forwarded, *destination)?;
                    }
                    let declined_active = declined.clone();
                    crossed.push(declined_active);
                    crossed.extend(continuation.above.clone());
                    forwarded.handlers[index].continuations = vec![VerifierContinuation {
                        target: continuation.target,
                        dst: continuation.dst,
                        registers: continuation.registers,
                        storage_live: continuation.storage_live,
                        reference_origins: continuation.reference_origins,
                        snapshots: continuation.snapshots,
                        labels: continuation.labels,
                        resumptions: continuation.resumptions,
                        performed: continuation.performed,
                        above: crossed,
                        pending_leave: continuation.pending_leave,
                    }];
                    propagate_state(&mut incoming, &mut worklist, outer.target, &forwarded)?;
                }
                advances = false;
            }
            VmInstruction::Cancel => {
                let Some(frame) = states.handlers.pop() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.continuations.is_empty()
                    && frame.continuation != VmContinuationPolicy::Terminal
                {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                expire_snapshot_brand(&mut states.snapshots, frame.id);
                // A terminal handler result is a non-local completion of the
                // protected computation. In particular, it must not return
                // through a pending `ResumeReturn` clause after a resumed
                // callee performs its later terminal operation.
                if frame.continuation == VmContinuationPolicy::Terminal {
                    states.resumption_return_depth = 0;
                    states.resumption_return_handler_ids.clear();
                }
            }
            VmInstruction::Copy { dst, src } => {
                read(&states, *src)?;
                if !vm_type_is_duplicable(
                    &register_type(function, *src)?,
                    &function.nominal_copy_descriptors,
                ) {
                    return Err(VmArtifactError::AffineValueCopy { register: *src });
                }
                same_type(function, *dst, *src)?;
                write(&mut states, *dst)?;
                states.snapshots[*dst as usize] = states.snapshots[*src as usize];
                states.labels[*dst as usize] = states.labels[*src as usize];
                states.resumptions[*dst as usize] = states.resumptions[*src as usize];
                if matches!(register_type(function, *dst)?, VmType::Reference { .. }) {
                    states.reference_origins[*dst as usize] =
                        states.reference_origins[*src as usize].clone();
                }
            }
            VmInstruction::StorageLive { local, .. } => {
                let index = *local as usize;
                let slot = states
                    .registers
                    .get_mut(index)
                    .ok_or(VmArtifactError::InvalidRegister { register: *local })?;
                if states.storage_live[index] || slot.is_some() {
                    return Err(VmArtifactError::ReadBeforeWrite { register: *local });
                }
                *slot = Some(false);
                states.storage_live[index] = true;
                states.snapshots[*local as usize] = None;
                states.labels[*local as usize] = false;
                states.resumptions[*local as usize] = false;
                states.reference_origins[*local as usize].clear();
            }
            VmInstruction::StorageDead { local, .. } => {
                let index = *local as usize;
                let slot = states
                    .registers
                    .get_mut(index)
                    .ok_or(VmArtifactError::InvalidRegister { register: *local })?;
                if !states.storage_live[index]
                    || *slot != Some(false)
                    || states
                        .reference_origins
                        .iter()
                        .any(|origins| origins.contains(&(*local)))
                {
                    return Err(VmArtifactError::ReadBeforeWrite { register: *local });
                }
                *slot = None;
                states.storage_live[index] = false;
                states.snapshots[*local as usize] = None;
                states.labels[*local as usize] = false;
                states.resumptions[*local as usize] = false;
                states.reference_origins[*local as usize].clear();
            }
            VmInstruction::SetDropFlag { flag, .. } => {
                expect_type(function, *flag, VmType::Bool)?;
                let slot = states
                    .registers
                    .get_mut(*flag as usize)
                    .ok_or(VmArtifactError::InvalidRegister { register: *flag })?;
                // Drop flags are compiler-created state cells. Their explicit
                // transitions are the sole allowed overwrite operation and
                // may occur repeatedly as initialization changes.
                *slot = Some(true);
                states.snapshots[*flag as usize] = None;
                states.labels[*flag as usize] = false;
                states.resumptions[*flag as usize] = false;
            }
            VmInstruction::DestroyIf { local, flag } => {
                read(&states, *flag)?;
                expect_type(function, *flag, VmType::Bool)?;
                let index = *local as usize;
                let slot = states
                    .registers
                    .get_mut(index)
                    .ok_or(VmArtifactError::InvalidRegister { register: *local })?;
                if !states.storage_live[index] || slot.is_none() {
                    return Err(VmArtifactError::ReadBeforeWrite { register: *local });
                }
                *slot = Some(false);
                states.snapshots[*local as usize] = None;
                states.labels[*local as usize] = false;
                states.resumptions[*local as usize] = false;
            }
            VmInstruction::Store { dst, src } => {
                read(&states, *src)?;
                same_type(function, *dst, *src)?;
                let index = *dst as usize;
                if states.source_storage[index] && !states.storage_live[index] {
                    return Err(VmArtifactError::ReadBeforeWrite { register: *dst });
                }
                let state = states
                    .registers
                    .get_mut(index)
                    .ok_or(VmArtifactError::InvalidRegister { register: *dst })?;
                *state = Some(true);
                states.snapshots[*dst as usize] = states.snapshots[*src as usize];
                states.labels[*dst as usize] = states.labels[*src as usize];
                states.resumptions[*dst as usize] = states.resumptions[*src as usize];
                if matches!(register_type(function, *dst)?, VmType::Reference { .. }) {
                    states.reference_origins[*dst as usize] = states.reference_origins[*src as usize].clone();
                } else {
                    states.reference_origins[*dst as usize].clear();
                }
            }
            VmInstruction::Move { dst, src } => {
                read(&states, *src)?;
                same_type(function, *dst, *src)?;
                states[*src as usize] = Some(false);
                states.snapshots[*dst as usize] = states.snapshots[*src as usize];
                states.snapshots[*src as usize] = None;
                states.labels[*dst as usize] = states.labels[*src as usize];
                states.labels[*src as usize] = false;
                states.resumptions[*dst as usize] = states.resumptions[*src as usize];
                states.resumptions[*src as usize] = false;
                write(&mut states, *dst)?;
                if matches!(register_type(function, *dst)?, VmType::Reference { .. }) {
                    states.reference_origins[*dst as usize] = states.reference_origins[*src as usize].clone();
                }
                states.reference_origins[*src as usize].clear();
            }
            VmInstruction::Borrow {
                dst,
                src,
                fields,
                unique,
                reborrow,
            } => {
                read(&states, *src)?;
                let found = register_type(function, *dst)?;
                let VmType::Reference {
                    unique: actual_unique,
                    referent: destination_referent,
                } = found.clone()
                else {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: VmType::Reference {
                            unique: *unique,
                            referent: Box::new(VmType::Unit),
                        },
                        found,
                    });
                };
                if actual_unique != *unique {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: VmType::Reference {
                            unique: *unique,
                            referent: destination_referent,
                        },
                        found,
                    });
                }

                let source_type = register_type(function, *src)?;
                let source_referent = match (&source_type, *reborrow) {
                    (
                        VmType::Reference {
                            unique: parent_unique,
                            referent,
                        },
                        true,
                    ) => {
                        // A bytecode artifact must not manufacture an
                        // exclusive child from a shared parent. The explicit
                        // mode matters: a unique *carrier* loan to `&T` is
                        // valid, whereas a unique reborrow of that `&T` is
                        // not.
                        if *unique && !*parent_unique {
                            return Err(VmArtifactError::TypeMismatch {
                                register: *src,
                                expected: VmType::Reference {
                                    unique: true,
                                    referent: referent.clone(),
                                },
                                found: source_type,
                            });
                        }
                        referent.as_ref()
                    }
                    (_, true) => {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *src,
                            expected: VmType::Reference {
                                unique: false,
                                referent: Box::new(VmType::Unit),
                            },
                            found: source_type,
                        });
                    }
                    (source, false) => source,
                };
                // A whole-place carrier loan and every tuple/array projection
                // have a fully knowable referent at this boundary. Reject a
                // forged destination type rather than allowing a later
                // DerefCopy to observe a value that disagrees with its
                // register contract. Nominal field layouts are sealed by the
                // compiler's frozen layout proof and remain opaque to this
                // standalone VM function representation.
                let projected_referent = vm_projected_referent_type(source_referent, fields)?;
                if let Some(projected_referent) = projected_referent
                    && destination_referent.as_ref() != &projected_referent
                {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: projected_referent,
                        found: *destination_referent,
                    });
                }
                write(&mut states, *dst)?;
                states.labels[*dst as usize] = states.labels[*src as usize];
                states.resumptions[*dst as usize] = states.resumptions[*src as usize];
                states.reference_origins[*dst as usize] = if *reborrow {
                    states.reference_origins[*src as usize].clone()
                } else {
                    BTreeSet::from([*src])
                };
            }
            VmInstruction::DerefCopy { dst, reference } => {
                read(&states, *reference)?;
                let VmType::Reference { referent, .. } = register_type(function, *reference)?
                else {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *reference,
                        expected: VmType::Reference {
                            unique: false,
                            referent: Box::new(VmType::Unit),
                        },
                        found: register_type(function, *reference)?,
                    });
                };
                expect_type(function, *dst, *referent)?;
                write(&mut states, *dst)?;
                states.labels[*dst as usize] = states.labels[*reference as usize];
                states.resumptions[*dst as usize] = states.resumptions[*reference as usize];
                if matches!(register_type(function, *dst)?, VmType::Reference { .. }) {
                    states.reference_origins[*dst as usize] = states.reference_origins[*reference as usize].clone();
                }
            }
            VmInstruction::DerefMove { dst, reference } => {
                read(&states, *reference)?;
                let VmType::Reference {
                    unique: true,
                    referent,
                } = register_type(function, *reference)?
                else {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *reference,
                        expected: VmType::Reference {
                            unique: true,
                            referent: Box::new(VmType::Unit),
                        },
                        found: register_type(function, *reference)?,
                    });
                };
                expect_type(function, *dst, *referent)?;
                write(&mut states, *dst)?;
                states.labels[*dst as usize] = states.labels[*reference as usize];
                states.resumptions[*dst as usize] = states.resumptions[*reference as usize];
                // Hold the unique loan itself while its referent is absent.
                // Every normal read of the reference now fails until the
                // accompanying DerefStore reinitializes it.
                states.registers[*reference as usize] = Some(false);
            }
            VmInstruction::DerefStore { reference, src } => {
                match states.registers.get(*reference as usize).copied() {
                    Some(Some(_)) => {}
                    Some(None) => return Err(VmArtifactError::ReadBeforeWrite { register: *reference }),
                    None => return Err(VmArtifactError::InvalidRegister { register: *reference }),
                }
                read(&states, *src)?;
                // `ResumeSnapshot` authenticates an exact live handler
                // frame, but an indirect store has no frozen provenance slot
                // through which that authority can be recovered.  Reject the
                // write instead of allowing a later DerefCopy to erase the
                // marker and present the resumption as an ordinary callable.
                if states.resumptions[*src as usize] {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let VmType::Reference {
                    unique: true,
                    referent,
                } = register_type(function, *reference)?
                else {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *reference,
                        expected: VmType::Reference {
                            unique: true,
                            referent: Box::new(register_type(function, *src)?),
                        },
                        found: register_type(function, *reference)?,
                    });
                };
                expect_type(function, *src, *referent)?;
                // A reference is the verifier's handle for the addressed
                // content. Keep its lexical-label taint synchronized with a
                // store so a subsequent DerefCopy cannot repackage a label
                // as an ordinary capturable callable. This remains local to
                // the active frame; labels still pass through ordinary calls.
                states.labels[*reference as usize] = states.labels[*src as usize];
                for &origin in &states.reference_origins[*reference as usize] {
                    if states.source_storage[origin as usize]
                        && !states.storage_live[origin as usize]
                    {
                        return Err(VmArtifactError::ReadBeforeWrite { register: origin });
                    }
                }
                states.registers[*reference as usize] = Some(true);
            }
            VmInstruction::NotBool { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::Bool)?;
                expect_type(function, *value, VmType::Bool)?;
                write(&mut states, *dst)?
            }
            VmInstruction::BitNotI64 { dst, value } => {
                read(&states, *value)?;
                expect_type(function, *dst, VmType::I64)?;
                expect_type(function, *value, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ShlI64 { dst, value, count } => {
                read(&states, *value)?;
                read(&states, *count)?;
                expect_type(function, *dst, VmType::I64)?;
                expect_type(function, *value, VmType::I64)?;
                expect_type(function, *count, VmType::U32)?;
                write(&mut states, *dst)?
            }
            VmInstruction::AddI64 { dst, left, right }
            | VmInstruction::WrappingAddI64 { dst, left, right }
            | VmInstruction::BitAndI64 { dst, left, right }
            | VmInstruction::BitXorI64 { dst, left, right }
            | VmInstruction::WrappingSubI64 { dst, left, right }
            | VmInstruction::WrappingMulI64 { dst, left, right }
            | VmInstruction::BitOrI64 { dst, left, right }
            | VmInstruction::SubI64 { dst, left, right }
            | VmInstruction::MulI64 { dst, left, right }
            | VmInstruction::DivI64 { dst, left, right }
            | VmInstruction::RemI64 { dst, left, right } => {
                read(&states, *left)?;
                read(&states, *right)?;
                expect_type(function, *dst, VmType::I64)?;
                expect_type(function, *left, VmType::I64)?;
                expect_type(function, *right, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::BitAndU32 { dst, left, right } => {
                read(&states, *left)?;
                read(&states, *right)?;
                expect_type(function, *dst, VmType::U32)?;
                expect_type(function, *left, VmType::U32)?;
                expect_type(function, *right, VmType::U32)?;
                write(&mut states, *dst)?
            }
            VmInstruction::BitAndU64 { dst, left, right } => {
                read(&states, *left)?;
                read(&states, *right)?;
                expect_type(function, *dst, VmType::U64)?;
                expect_type(function, *left, VmType::U64)?;
                expect_type(function, *right, VmType::U64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::IntShrI64 { dst, left, right } => {
                read(&states, *left)?;
                read(&states, *right)?;
                expect_type(function, *dst, VmType::I64)?;
                expect_type(function, *left, VmType::I64)?;
                expect_type(function, *right, VmType::U32)?;
                write(&mut states, *dst)?
            }
            VmInstruction::AddF64 { dst, left, right }
            | VmInstruction::SubF64 { dst, left, right }
            | VmInstruction::MulF64 { dst, left, right }
            | VmInstruction::DivF64 { dst, left, right }
            | VmInstruction::RemF64 { dst, left, right } => {
                read(&states, *left)?;
                read(&states, *right)?;
                expect_type(function, *dst, VmType::F64)?;
                expect_type(function, *left, VmType::F64)?;
                expect_type(function, *right, VmType::F64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::IntEqualI64 { dst, left, right }
            | VmInstruction::IntLessI64 { dst, left, right }
            | VmInstruction::IntGreaterI64 { dst, left, right } => {
                read(&states, *left)?;
                read(&states, *right)?;
                expect_type(function, *dst, VmType::U32)?;
                expect_type(function, *left, VmType::I64)?;
                expect_type(function, *right, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConcatText { dst, left, right } => {
                read(&states, *left)?;
                read(&states, *right)?;
                expect_type(function, *dst, VmType::Text)?;
                expect_type(function, *left, VmType::Text)?;
                expect_type(function, *right, VmType::Text)?;
                write(&mut states, *dst)?
            }
            VmInstruction::CompareI64 {
                dst, left, right, ..
            } => {
                read(&states, *left)?;
                read(&states, *right)?;
                expect_type(function, *dst, VmType::Bool)?;
                expect_type(function, *left, VmType::I64)?;
                expect_type(function, *right, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::CompareU32 {
                dst, left, right, ..
            } => {
                read(&states, *left)?;
                read(&states, *right)?;
                expect_type(function, *dst, VmType::Bool)?;
                expect_type(function, *left, VmType::U32)?;
                expect_type(function, *right, VmType::U32)?;
                write(&mut states, *dst)?
            }
            VmInstruction::CompareU64 {
                dst, left, right, ..
            } => {
                read(&states, *left)?;
                read(&states, *right)?;
                expect_type(function, *dst, VmType::Bool)?;
                expect_type(function, *left, VmType::U64)?;
                expect_type(function, *right, VmType::U64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::CompareF64 {
                dst, left, right, ..
            } => {
                read(&states, *left)?;
                read(&states, *right)?;
                expect_type(function, *dst, VmType::Bool)?;
                expect_type(function, *left, VmType::F64)?;
                expect_type(function, *right, VmType::F64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::EqBool { dst, left, right }
            | VmInstruction::NeBool { dst, left, right } => {
                read(&states, *left)?;
                read(&states, *right)?;
                expect_type(function, *dst, VmType::Bool)?;
                expect_type(function, *left, VmType::Bool)?;
                expect_type(function, *right, VmType::Bool)?;
                write(&mut states, *dst)?
            }
            VmInstruction::EqText { dst, left, right }
            | VmInstruction::NeText { dst, left, right } => {
                read(&states, *left)?;
                read(&states, *right)?;
                expect_type(function, *dst, VmType::Bool)?;
                expect_type(function, *left, VmType::Text)?;
                expect_type(function, *right, VmType::Text)?;
                write(&mut states, *dst)?
            }
            VmInstruction::CompareChar {
                dst, left, right, ..
            } => {
                read(&states, *left)?;
                read(&states, *right)?;
                expect_type(function, *dst, VmType::Bool)?;
                expect_type(function, *left, VmType::Char)?;
                expect_type(function, *right, VmType::Char)?;
                write(&mut states, *dst)?
            }
            VmInstruction::Call { dst, arguments, .. } => {
                for &argument in arguments {
                    read(&states, argument)?;
                    verify_call_frame_resumption_transfer(&states, argument)?;
                }
                write(&mut states, *dst)?
            }
            VmInstruction::HostCall {
                dst,
                capability,
                symbol,
                parameters,
                result,
                arguments,
            } => {
                if capability.is_empty()
                    || symbol.is_empty()
                    || capability.contains('*')
                    || capability.chars().any(char::is_whitespace)
                    || parameters.len() != arguments.len()
                {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid frozen host import boundary",
                    });
                }
                for (argument, expected) in arguments.iter().zip(parameters) {
                    read(&states, *argument)?;
                    expect_type(function, *argument, expected.clone())?;
                }
                expect_type(function, *dst, result.clone())?;
                write(&mut states, *dst)?
            }
            VmInstruction::MakeCallable { dst, captures, .. } => {
                for &capture in captures {
                    read(&states, capture)?;
                    // A callable environment is retained independently of
                    // this frame. The executor cannot freeze an `&mut`
                    // capture without severing its write-back target, so
                    // reject the artifact at verification instead of
                    // deferring this safety failure until a caller observes
                    // the returned callable.
                    if vm_type_contains_unique_reference(
                        &register_type(function, capture)?,
                        &function.nominal_copy_descriptors,
                    ) {
                        return Err(VmArtifactError::UnsupportedEscapingUniqueReference);
                    }
                    if states.snapshots[capture as usize].is_some() {
                        return Err(VmArtifactError::HandlerResumeUnavailable);
                    }
                    if states.labels[capture as usize] {
                        return Err(VmArtifactError::InvalidLabelContract {
                            message: "callable capture cannot retain a lexical label",
                        });
                    }
                    if states.resumptions[capture as usize] {
                        return Err(VmArtifactError::HandlerResumeUnavailable);
                    }
                }
                if !matches!(register_type(function, *dst)?, VmType::Callable { .. }) {
                    return Err(VmArtifactError::NotCallable { register: *dst });
                }
                write(&mut states, *dst)?;
                states.labels[*dst as usize] = false;
                states.resumptions[*dst as usize] = false;
            }
            VmInstruction::MakeLabel {
                dst,
                target,
                destination,
                ..
            } => {
                let VmType::Callable {
                    safety: Safety::Safe, parameters, result, ..
                } = register_type(function, *dst)?
                else {
                    return Err(VmArtifactError::NotCallable { register: *dst });
                };
                if parameters.as_slice() != [register_type(function, *destination)?]
                    // VM represents source `!` as its zero-sized Unit leaf.
                    || !matches!(result.as_ref(), VmType::Unit)
                {
                    return Err(VmArtifactError::NotCallable { register: *dst });
                }
                if *target as usize >= function.instructions.len() {
                    return Err(VmArtifactError::InvalidRegister { register: *target });
                }
                write(&mut states, *dst)?;
                states.labels[*dst as usize] = true;
                states.resumptions[*dst as usize] = false;
            }
            VmInstruction::CallIndirect {
                dst,
                callee,
                arguments,
            } => {
                read(&states, *callee)?;
                // A captured resumption is callable-shaped but is not an
                // ordinary function value. It may be invoked only through
                // `ResumeSnapshot`, which proves the originating handler
                // frame remains active.
                if states.resumptions[*callee as usize] {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let VmType::Callable {
                    parameters, result, ..
                } = register_type(function, *callee)?
                else {
                    return Err(VmArtifactError::NotCallable { register: *callee });
                };
                if parameters.len() != arguments.len() {
                    return Err(VmArtifactError::CallArity {
                        expected: parameters.len() as u32,
                        found: arguments.len() as u32,
                    });
                }
                for (parameter, argument) in parameters.iter().zip(arguments) {
                    read(&states, *argument)?;
                    verify_call_frame_resumption_transfer(&states, *argument)?;
                    let found = register_type(function, *argument)?;
                    if parameter != &found {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *argument,
                            expected: parameter.clone(),
                            found,
                        });
                    }
                }
                let found = register_type(function, *dst)?;
                if *result != found {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: *result,
                        found,
                    });
                }
                write(&mut states, *dst)?
            }
            VmInstruction::Jump { target } => {
                propagate_state(&mut incoming, &mut worklist, *target, &states)?;
                advances = false;
            }
            VmInstruction::Leave {
                handler_depth,
                target,
                arguments,
                destinations,
                cleanup,
                ..
            } => {
                if !cleanup.validate() {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "leave cleanup proof is not canonical",
                    });
                }
                if !cleanup
                    .storage_erasure
                    .validate(arguments, function.registers.len())
                {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "leave source-storage erasure witness is not canonical",
                    });
                }
                if arguments.len() != destinations.len() {
                    return Err(VmArtifactError::CallArity {
                        expected: destinations.len() as u32,
                        found: arguments.len() as u32,
                    });
                }
                let mut written = BTreeSet::new();
                for (&argument, &destination) in arguments.iter().zip(destinations) {
                    read(&states, argument)?;
                    same_type(function, argument, destination)?;
                    if !written.insert(destination) {
                        return Err(VmArtifactError::InvalidRegister {
                            register: destination,
                        });
                    }
                }
                // A leave is a nonlocal exit: suspended continuations and all
                // frame-branded snapshot capabilities are invalidated before
                // control reaches its lexical destination.
                let handler_depth = *handler_depth as usize;
                if handler_depth > states.handlers.len() {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                states.handlers.truncate(handler_depth);
                states.snapshots.fill(None);
                for &destination in destinations {
                    write(&mut states, destination)?;
                }
                propagate_state(&mut incoming, &mut worklist, *target, &states)?;
                advances = false;
            }
            VmInstruction::BranchBool {
                condition,
                then_target,
                else_target,
            } => {
                read(&states, *condition)?;
                expect_type(function, *condition, VmType::Bool)?;
                propagate_state(&mut incoming, &mut worklist, *then_target, &states)?;
                propagate_state(&mut incoming, &mut worklist, *else_target, &states)?;
                advances = false;
            }
            VmInstruction::Return { value } => {
                read(&states, *value)?;
                // Return leaves this activation (or exposes the value to the
                // embedding host). A captured resumption is instead valid
                // only while its branded handler frame remains live.
                if states.resumptions[*value as usize] {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                if states.resumption_return_depth != 0 {
                    if states
                        .handlers
                        .iter()
                        .any(|frame| !states.resumption_return_handler_ids.contains(&frame.id))
                    {
                        return Err(VmArtifactError::HandlerStillActive);
                    }
                    continue;
                }
                if !states.handlers.is_empty() {
                    return Err(VmArtifactError::HandlerStillActive);
                }
                let found = register_type(function, *value)?;
                if let Some(expected) = &returned {
                    if *expected != found {
                        return Err(VmArtifactError::ResultType {
                            expected: expected.clone(),
                            found,
                        });
                    }
                } else {
                    returned = Some(found);
                }
                advances = false;
            }
            VmInstruction::Trap => {
                trapped = true;
                advances = false;
            }
        }
        if advances {
            propagate_state(&mut incoming, &mut worklist, (pc + 1) as u32, &states)?;
        }
    }
    if returned.is_some() || trapped || matches!(declared_result, Some((_, false))) {
        Ok(())
    } else {
        Err(VmArtifactError::NoReturn)
    }
}

/// A captured resumption is frame-scoped control authority, not an ordinary
/// callable argument. A lexical label, by contrast, deliberately supports
/// generic facade calls: the executor restores its captured caller frame on
/// invocation. Only resumptions are forbidden at ordinary call boundaries.
fn verify_call_frame_resumption_transfer(
    states: &VerifierState,
    register: u32,
) -> Result<(), VmArtifactError> {
    if states.resumptions[register as usize] {
        return Err(VmArtifactError::HandlerResumeUnavailable);
    }
    Ok(())
}

/// Validate the effect-identity metadata that survives into bytecode.
///
/// VM value types intentionally erase source regions and higher-ranked
/// callable binders.  A declaration generic lifetime is still a meaningful
/// protocol identity, but a `for<'a>` placeholder is not: there is no VM
/// binder scope in which a `Lifetime::Bound` term could be interpreted.  Such
/// a term therefore proves that a rigid HRTB universe escaped Core/MIR rather
/// than becoming an executable contract.  Check this recursively through row
/// projections as well as nested named effects; previously the projection
/// arguments were not visited at all, giving forged bytecode a path around
/// the higher-ranked leak boundary.
fn validate_vm_generic_arguments(values: &[VmGenericArgument]) -> Result<(), VmArtifactError> {
    for value in values {
        match value {
            VmGenericArgument::Type(value) => validate_vm_type(value)?,
            VmGenericArgument::ConstU32(_) => {}
            VmGenericArgument::ConstU32Expr(value) => validate_vm_structural_u32_expr(value)?,
            VmGenericArgument::Lifetime(Lifetime::Bound { .. }) => {
                return Err(VmArtifactError::MalformedEncoding {
                    message: "VM effect identity retains an escaped higher-ranked lifetime",
                });
            }
            VmGenericArgument::Lifetime(
                Lifetime::Static | Lifetime::Generic(_) | Lifetime::Elided,
            ) => {}
            VmGenericArgument::ConstQuantity { lower, upper } => {
                if upper.is_some_and(|upper| *lower > upper) {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "invalid quantity interval",
                    });
                }
            }
            VmGenericArgument::ConstGeneric { .. } => {}
            VmGenericArgument::EffectRow(row) => validate_vm_effect_row(row)?,
        }
    }
    Ok(())
}

fn validate_vm_type(value: &VmType) -> Result<(), VmArtifactError> {
    match value {
        VmType::Array(value) => validate_vm_type(value),
        VmType::StaticData {
            element,
            alignment,
            ..
        } => {
            if *alignment == 0 || !alignment.is_power_of_two() {
                return Err(VmArtifactError::MalformedEncoding {
                    message: "static-data type has invalid alignment",
                });
            }
            validate_vm_type(element)
        }
        VmType::Tuple(values) => values.iter().try_for_each(validate_vm_type),
        VmType::Nominal { arguments, .. } => arguments
            .iter()
            .try_for_each(validate_vm_nominal_argument_type),
        VmType::Callable {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters.iter().try_for_each(validate_vm_type)?;
            validate_vm_type(result)?;
            validate_vm_effect_row(effects)
        }
        VmType::Reference { referent, .. } => validate_vm_type(referent),
        VmType::RawPointer { pointee, .. } => validate_vm_type(pointee),
        // Consts are metadata slots inside a nominal identity, not VM value
        // layouts. Reject direct candidate registers/parameters/results and
        // any attempt to smuggle one through a tuple, array, callable, or
        // reference type.
        VmType::ConstU32(_)
        | VmType::ConstU32Expr(_)
        | VmType::ConstQuantity { .. }
        | VmType::ConstGeneric { .. } => Err(VmArtifactError::MalformedEncoding {
            message: "metadata-only structural const used as VM value type",
        }),
        VmType::Unit
        | VmType::I64
        | VmType::Usize
        | VmType::U32
        | VmType::U8
        | VmType::U16
        | VmType::I16
        | VmType::I32
        | VmType::I8
        | VmType::U64
        | VmType::Isize
        | VmType::U128
        | VmType::I128
        | VmType::F32
        | VmType::F64
        | VmType::Bool
        | VmType::Char
        | VmType::Text
        | VmType::Bytes
        | VmType::Generic(_) => Ok(()),
    }
}

fn validate_vm_nominal_argument_type(value: &VmType) -> Result<(), VmArtifactError> {
    match value {
        VmType::ConstU32(_) | VmType::ConstGeneric { .. } => Ok(()),
        VmType::ConstU32Expr(value) => validate_vm_structural_u32_expr(value),
        VmType::ConstQuantity { lower, upper } if upper.is_some_and(|upper| *lower > upper) => {
            Err(VmArtifactError::MalformedEncoding {
                message: "invalid quantity interval",
            })
        }
        VmType::ConstQuantity { .. } => Ok(()),
        value => validate_vm_type(value),
    }
}

fn validate_vm_structural_u32_expr(value: &StructuralU32Expr) -> Result<(), VmArtifactError> {
    match value.clone().normalized() {
        Ok(normalized) if normalized == *value => Ok(()),
        Ok(_) => Err(VmArtifactError::NonCanonicalEncoding),
        Err(_) => Err(VmArtifactError::MalformedEncoding {
            message: "invalid structural u32 expression",
        }),
    }
}

fn validate_vm_effect_row(row: &VmEffectRow) -> Result<(), VmArtifactError> {
    if matches!(row.tail, Some(EffectTail::Infer(_))) {
        return Err(VmArtifactError::MalformedEncoding {
            message: "VM effect row retains inference tail",
        });
    }
    if row
        .effects
        .windows(2)
        .any(|pair| vm_effect_instance_key(&pair[0]) >= vm_effect_instance_key(&pair[1]))
        || row.projections.windows(2).any(|pair| {
            vm_effect_row_projection_key(&pair[0]) >= vm_effect_row_projection_key(&pair[1])
        })
    {
        return Err(VmArtifactError::NonCanonicalEncoding);
    }
    for effect in &row.effects {
        validate_vm_generic_arguments(&effect.arguments)?;
    }
    for projection in &row.projections {
        validate_vm_generic_arguments(&projection.trait_arguments)?;
        validate_vm_generic_arguments(&projection.item_arguments)?;
    }
    Ok(())
}

/// Handler clause entry points are private control-flow boundaries.  Reaching
/// one through an ordinary jump, branch, fallthrough, or dynamic label would
/// let hostile bytecode execute a clause without the `Perform` transition that
/// initializes payload destinations and records the continuation consumed by
/// `Resume`, `Forward`, or `Cancel`.
///
/// This compact VM encodes no separate handler-region table, so the
/// `InstallHandler` instruction is the authoritative declaration of the entry.
/// A target must follow its install site, and only a dynamic perform transfer
/// may enter it.
fn verify_handler_entry_boundaries(function: &VmFunction) -> Result<(), VmArtifactError> {
    let mut targets = BTreeSet::new();
    for (pc, instruction) in function.instructions.iter().enumerate() {
        let VmInstruction::InstallHandler { target, .. } = instruction else {
            continue;
        };
        if *target as usize <= pc || function.instructions.get(*target as usize).is_none() {
            return Err(VmArtifactError::InvalidInstructionTarget { target: *target });
        }
        targets.insert(*target);
    }

    for (pc, instruction) in function.instructions.iter().enumerate() {
        let enters_handler = match instruction {
            VmInstruction::DeclareResult { .. } => false,
            VmInstruction::Jump { target }
            | VmInstruction::Leave { target, .. }
            | VmInstruction::MakeLabel { target, .. } => {
                targets.contains(target)
            }
            VmInstruction::BranchBool {
                then_target,
                else_target,
                ..
            } => targets.contains(then_target) || targets.contains(else_target),
            VmInstruction::Return { .. }
            | VmInstruction::Trap
            | VmInstruction::Resume { .. }
            | VmInstruction::ResumeReturn { .. }
            | VmInstruction::Forward
            | VmInstruction::Cancel => false,
            _ => targets.contains(&((pc + 1) as u32)),
        };
        if enters_handler {
            let target = match instruction {
                VmInstruction::Jump { target }
                | VmInstruction::Leave { target, .. }
                | VmInstruction::MakeLabel { target, .. } => *target,
                VmInstruction::BranchBool {
                    then_target,
                    else_target,
                    ..
                } if targets.contains(then_target) => *then_target,
                VmInstruction::BranchBool { else_target, .. } => *else_target,
                _ => (pc + 1) as u32,
            };
            return Err(VmArtifactError::HandlerTargetReachedByControlFlow { target });
        }
    }
    Ok(())
}
fn propagate_state(
    incoming: &mut [Option<VerifierState>],
    worklist: &mut Vec<usize>,
    target: u32,
    state: &VerifierState,
) -> Result<(), VmArtifactError> {
    let Some(slot) = incoming.get_mut(target as usize) else {
        return Err(VmArtifactError::InvalidInstructionTarget { target });
    };
    match slot {
        None => {
            *slot = Some(state.clone());
            worklist.push(target as usize);
            Ok(())
        }
        Some(existing) => {
            if existing.resumption_return_depth != state.resumption_return_depth
                || existing.resumption_return_handler_ids != state.resumption_return_handler_ids
            {
                return Err(VmArtifactError::HandlerStateMismatch);
            }
            let handler_changed = merge_handler_states(&mut existing.handlers, &state.handlers)
                .ok_or(VmArtifactError::HandlerStateMismatch)?;
            // This is a forward must-analysis: a register is readable at a
            // join only when every predecessor has initialized it and none
            // has moved it.  Requiring identical complete register files
            // rejects valid CFGs merely because separate arms allocate dead
            // temporaries.  Joining their facts also lets a later use of a
            // path-local value produce the ordinary read-before-write error.
            let joined = existing
                .registers
                .iter()
                .zip(&state.registers)
                .map(|(left, right)| match (left, right) {
                    (Some(true), Some(true)) => Some(true),
                    (Some(false), Some(false)) => Some(false),
                    _ => None,
                })
                .collect::<Vec<_>>();
            // Source-storage liveness is also a must fact.  A post-join
            // write may initialize an addressable slot only when that slot
            // remains live on every incoming edge; otherwise bytecode could
            // revive a slot which a sibling arm already erased.
            let storage_live = existing
                .storage_live
                .iter()
                .zip(&state.storage_live)
                .map(|(left, right)| *left && *right)
                .collect::<Vec<_>>();
            // Reference provenance is a may fact.  A merged reference can
            // address any root reached by either predecessor, and a later
            // StorageDead must therefore respect every retained loan.
            let reference_origins = existing
                .reference_origins
                .iter()
                .zip(&state.reference_origins)
                .map(|(left, right)| left.union(right).copied().collect::<BTreeSet<_>>())
                .collect::<Vec<_>>();
            let snapshots = existing
                .snapshots
                .iter()
                .zip(&state.snapshots)
                .map(|(left, right)| if left == right { *left } else { None })
                .collect::<Vec<_>>();
            // Labels and captured resumptions are capability facts, not
            // ordinary register initialization. A join must retain either
            // taint whenever one predecessor carries it; otherwise a
            // continuation minted in just one handler-clause branch can be
            // repackaged as an innocent callable after the merge.
            let labels = existing
                .labels
                .iter()
                .zip(&state.labels)
                .map(|(left, right)| *left || *right)
                .collect::<Vec<_>>();
            let resumptions = existing
                .resumptions
                .iter()
                .zip(&state.resumptions)
                .map(|(left, right)| *left || *right)
                .collect::<Vec<_>>();
            let pending_leave = if existing.pending_leave == state.pending_leave {
                existing.pending_leave.clone()
            } else {
                None
            };
            if existing.registers != joined
                || existing.storage_live != storage_live
                || existing.reference_origins != reference_origins
                || existing.snapshots != snapshots
                || existing.labels != labels
                || existing.resumptions != resumptions
                || existing.pending_leave != pending_leave
                || handler_changed
            {
                existing.registers = joined;
                existing.storage_live = storage_live;
                existing.reference_origins = reference_origins;
                existing.snapshots = snapshots;
                existing.labels = labels;
                existing.resumptions = resumptions;
                existing.pending_leave = pending_leave;
                worklist.push(target as usize);
            }
            Ok(())
        }
    }
}
fn merge_handler_states(
    existing: &mut [VerifierHandlerFrame],
    incoming: &[VerifierHandlerFrame],
) -> Option<bool> {
    if existing.len() != incoming.len() {
        return None;
    }
    let mut changed = false;
    for (left, right) in existing.iter_mut().zip(incoming) {
        if left.id != right.id
            || left.effect != right.effect
            || left.effect_arguments != right.effect_arguments
            || left.operation != right.operation
            || left.payload_destinations != right.payload_destinations
            || left.resume_type != right.resume_type
            || left.target != right.target
        {
            return None;
        }
        for continuation in &right.continuations {
            if !left.continuations.contains(continuation) {
                left.continuations.push(continuation.clone());
                changed = true;
            }
        }
        left.continuations.sort_by_key(|continuation| {
            (
                continuation.target,
                continuation.dst,
                continuation.registers.clone(),
            )
        });
    }
    Some(changed)
}

/// A continuation token is capability-bearing only while its branded handler
/// activation remains live.  Clearing all aliases at the structural exit
/// prevents a stale register from becoming valid if bytecode later revisits
/// the same lexical `InstallHandler` instruction.
fn expire_snapshot_brand(snapshots: &mut [Option<u32>], frame: u32) {
    for snapshot in snapshots {
        if *snapshot == Some(frame) {
            *snapshot = None;
        }
    }
}
fn register_type(function: &VmFunction, register: u32) -> Result<VmType, VmArtifactError> {
    function
        .registers
        .get(register as usize)
        .cloned()
        .ok_or(VmArtifactError::InvalidRegister { register })
}
fn validate_vm_nominal_copy_descriptors(
    descriptors: &[VmNominalCopyDescriptor],
) -> Result<(), VmArtifactError> {
    let mut previous_key: Option<Vec<u8>> = None;
    for (index, descriptor) in descriptors.iter().enumerate() {
        let key = vm_nominal_copy_descriptor_key(descriptor);
        if descriptor.variants.is_empty()
            || (!descriptor.is_enum && descriptor.variants.len() != 1)
            || descriptors[..index].iter().any(|previous| {
                previous.definition == descriptor.definition
                    && previous.arguments == descriptor.arguments
            })
            || previous_key.as_ref().is_some_and(|previous| previous >= &key)
        {
            return Err(VmArtifactError::InvalidCallableEnvironment {
                message: "nominal copy descriptors are not canonical",
            });
        }
        previous_key = Some(key);
        for argument in &descriptor.arguments {
            // These are nominal identity slots, not value registers. A
            // structural const is valid metadata here even though it is
            // rejected as a standalone runtime value type.
            validate_vm_nominal_argument_type(argument)?;
        }
        for variant in &descriptor.variants {
            for field in variant {
                validate_vm_type(field)?;
            }
        }
    }
    Ok(())
}

/// The descriptor is the frozen declaration-owned layout authority for a
/// nominal value.  VM register types retain only nominal identity, so every
/// aggregate operation must recover its fields here instead of trusting the
/// instruction-local `field_type` metadata supplied by a decoded artifact.
fn nominal_layout_descriptor<'a>(
    function: &'a VmFunction,
    nominal: &VmType,
) -> Result<&'a VmNominalCopyDescriptor, VmArtifactError> {
    let VmType::Nominal {
        definition,
        arguments,
    } = nominal
    else {
        return Err(VmArtifactError::MalformedEncoding {
            message: "nominal aggregate operation has a non-nominal base",
        });
    };
    function
        .nominal_copy_descriptors
        .iter()
        .find(|descriptor| {
            descriptor.definition == *definition && descriptor.arguments == *arguments
        })
        .ok_or(VmArtifactError::MalformedEncoding {
            message: "nominal aggregate operation lacks a frozen layout descriptor",
        })
}

fn nominal_record_layout<'a>(
    function: &'a VmFunction,
    nominal: &VmType,
) -> Result<&'a [VmType], VmArtifactError> {
    let descriptor = nominal_layout_descriptor(function, nominal)?;
    if descriptor.is_enum || descriptor.variants.len() != 1 {
        return Err(VmArtifactError::MalformedEncoding {
            message: "record aggregate operation targets an enum descriptor",
        });
    }
    Ok(&descriptor.variants[0])
}

fn nominal_variant_layout<'a>(
    function: &'a VmFunction,
    nominal: &VmType,
    variant: u32,
) -> Result<&'a [VmType], VmArtifactError> {
    let descriptor = nominal_layout_descriptor(function, nominal)?;
    if !descriptor.is_enum {
        return Err(VmArtifactError::MalformedEncoding {
            message: "enum aggregate operation targets a record descriptor",
        });
    }
    descriptor.variants
        .get(variant as usize)
        .map(Vec::as_slice)
        .ok_or(VmArtifactError::MalformedEncoding {
            message: "enum variant is outside frozen nominal layout",
        })
}

/// A source field projection may follow a successful enum-pattern dispatch,
/// so its static nominal type alone does not retain one selected variant.
/// Admit only a field type/arity that appears in the declaration-owned
/// layout. The executor then rechecks the concrete variant value before it
/// exposes the field, preventing a different variant from relabelling a
/// callable while preserving legitimate completion-dispatch lowering.
fn nominal_projection_matches_layout(
    function: &VmFunction,
    nominal: &VmType,
    index: u32,
    field_count: u32,
    field_type: &VmType,
) -> Result<bool, VmArtifactError> {
    Ok(nominal_layout_descriptor(function, nominal)?
        .variants
        .iter()
        .any(|layout| {
            layout.len() == field_count as usize && layout.get(index as usize) == Some(field_type)
        }))
}
/// Recover a projected referent when the VM type itself carries the complete
/// structural layout. Nominal layouts intentionally return `None`: their
/// proof lives in frozen Core/MIR metadata rather than a standalone artifact.
/// A scalar projection is always malformed and cannot be deferred safely.
fn vm_projected_referent_type(
    source: &VmType,
    fields: &[u32],
) -> Result<Option<VmType>, VmArtifactError> {
    let mut current = source;
    for field in fields {
        current = match current {
            VmType::Tuple(elements) => elements
                .get(*field as usize)
                .ok_or(VmArtifactError::InvalidRegister { register: *field })?,
            VmType::Array(element) => element,
            VmType::Nominal { .. } => return Ok(None),
            _ => return Err(VmArtifactError::InvalidRegister { register: *field }),
        };
    }
    Ok(Some(current.clone()))
}

fn vm_type_is_duplicable(ty: &VmType, descriptors: &[VmNominalCopyDescriptor]) -> bool {
    fn visit(
        ty: &VmType,
        descriptors: &[VmNominalCopyDescriptor],
        active: &mut Vec<(DefKey, Vec<VmType>)>,
    ) -> bool {
        match ty {
            VmType::Reference { unique, .. } => !*unique,
            VmType::Tuple(elements) => elements
                .iter()
                .all(|element| visit(element, descriptors, active)),
            VmType::Array(element) => visit(element, descriptors, active),
            VmType::Nominal {
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
                active.push(key);
                let result = descriptor.variants.iter().all(|variant| {
                    variant
                        .iter()
                        .all(|field| visit(field, descriptors, active))
                });
                active.pop();
                result
            }
            // A generic function is verified again after each direct-call
            // instantiation. Until then its binder has no concrete nominal
            // layout to inspect, so leave the copy admissible here and let
            // the specialized function close the proof.
            VmType::Generic(_) => true,
            VmType::Callable { .. } => true,
            _ => true,
        }
    }
    visit(ty, descriptors, &mut Vec::new())
}

/// A retained callable environment is a snapshot boundary.  It may carry a
/// shared reference, but a unique reference anywhere in an explicitly known
/// aggregate would lose its write-back target when frozen.
fn vm_type_contains_unique_reference(ty: &VmType, descriptors: &[VmNominalCopyDescriptor]) -> bool {
    fn visit(
        ty: &VmType,
        descriptors: &[VmNominalCopyDescriptor],
        active: &mut Vec<(DefKey, Vec<VmType>)>,
    ) -> bool {
        match ty {
            // Freezing a shared reference retains a recursively frozen
            // snapshot of its referent. A unique capability nested behind
            // that otherwise benign shared carrier is therefore just as
            // invalid as a directly captured `&mut`.
            VmType::Reference { unique, referent } => *unique || visit(referent, descriptors, active),
            VmType::Tuple(elements) => elements.iter().any(|element| visit(element, descriptors, active)),
            VmType::Array(element) => visit(element, descriptors, active),
            VmType::Nominal {
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
                active.push(key);
                let result = descriptor.variants.iter().any(|variant| {
                    variant
                        .iter()
                        .any(|field| visit(field, descriptors, active))
                });
                active.pop();
                result
            }
            _ => false,
        }
    }
    visit(ty, descriptors, &mut Vec::new())
}
fn expect_type(
    function: &VmFunction,
    register: u32,
    expected: VmType,
) -> Result<(), VmArtifactError> {
    let found = register_type(function, register)?;
    if found == expected {
        Ok(())
    } else {
        Err(VmArtifactError::TypeMismatch {
            register,
            expected,
            found,
        })
    }
}

fn expect_static_u8_type(function: &VmFunction, register: u32) -> Result<(), VmArtifactError> {
    let found = register_type(function, register)?;
    if matches!(
        found,
        VmType::StaticData { ref element, tag: crate::STATIC_UTF8_DATA_TAG | crate::STATIC_RAW_U8_DATA_TAG, alignment: 1 }
            if **element == VmType::U8
    ) {
        Ok(())
    } else {
        Err(VmArtifactError::TypeMismatch {
            register,
            expected: VmType::StaticData {
                element: Box::new(VmType::U8),
                tag: crate::STATIC_UTF8_DATA_TAG,
                alignment: 1,
            },
            found,
        })
    }
}
fn same_type(function: &VmFunction, destination: u32, source: u32) -> Result<(), VmArtifactError> {
    let expected = register_type(function, destination)?;
    let found = register_type(function, source)?;
    if expected == found {
        Ok(())
    } else {
        Err(VmArtifactError::TypeMismatch {
            register: source,
            expected,
            found,
        })
    }
}

fn write(states: &mut VerifierState, register: u32) -> Result<(), VmArtifactError> {
    let index = register as usize;
    let storage_live = *states
        .storage_live
        .get(index)
        .ok_or(VmArtifactError::InvalidRegister { register })?;
    let source_storage = *states
        .source_storage
        .get(index)
        .ok_or(VmArtifactError::InvalidRegister { register })?;
    let state = states
        .registers
        .get_mut(index)
        .ok_or(VmArtifactError::InvalidRegister { register })?;
    states.reference_origins[index].clear();
    match *state {
        None if !source_storage || storage_live => {
            *state = Some(true);
            Ok(())
        }
        None => Err(VmArtifactError::ReadBeforeWrite { register }),
        Some(false) if storage_live => {
            *state = Some(true);
            Ok(())
        }
        _ => Err(VmArtifactError::DoubleWrite { register }),
    }
}
fn read(states: &[Option<bool>], register: u32) -> Result<(), VmArtifactError> {
    match states.get(register as usize).copied() {
        None => Err(VmArtifactError::InvalidRegister { register }),
        Some(None) => Err(VmArtifactError::ReadBeforeWrite { register }),
        Some(Some(false)) => Err(VmArtifactError::UseAfterMove { register }),
        Some(Some(true)) => Ok(()),
    }
}
#[derive(Clone, Debug)]
enum VmValue {
    /// A genuine process pointer. Frame transfers copy the pointer, not its
    /// pointee or provenance. Dereferencing requires an unsafe execution call.
    RawPointer { pointer: *mut u8, signature: VmType },
    Unit,
    I64(i64),
    Usize(u64),
    U32(u32),
    U8(u8),
    U16(u16),
    I16(i16),
    I32(i32),
    I8(i8),
    U64(u64),
    Isize(i64),
    U128(u128),
    I128(i128),
    F32(f32),
    F64(f64),
    Bool(bool),
    Char(char),
    Text(Arc<str>),
    Bytes(Arc<[u8]>),
    StaticData {
        tag: u128,
        alignment: u32,
        bytes: Arc<[u8]>,
        offset: usize,
        length: usize,
    },
    Tuple(Arc<[VmValue]>),
    Array {
        values: Arc<[VmValue]>,
        capacity: usize,
    },
    StaticArray { bytes: Arc<[u8]>, offset: usize, length: usize },
    Record {
        definition: DefKey,
        fields: Arc<[VmValue]>,
        signature: VmType,
    },
    Reference {
        target: ReferenceTarget,
        fields: Arc<[u32]>,
        unique: bool,
        referent: VmType,
    },
    Enum {
        definition: DefKey,
        variant: u32,
        fields: Arc<[VmValue]>,
        signature: VmType,
    },
    Callable {
        callee: DefKey,
        captures: Arc<[VmValue]>,
        signature: VmType,
    },
    /// A dynamic instance of one verified lexical label destination. It is
    /// callable only through the ordinary one-argument `Label<T>` contract;
    /// invocation unwinds to the captured frame rather than returning here.
    Label {
        owner: DefKey,
        label: u32,
        target: u32,
        destination: u32,
        call_depth: usize,
        handler_depth: usize,
        signature: VmType,
    },
    /// A frame-branded callable token. Only `ResumeSnapshot` may consume it;
    /// ordinary indirect calls reject it.
    Resumption {
        frame: u64,
        signature: VmType,
    },
}

#[derive(Clone, Debug)]
enum ReferenceTarget {
    /// A checked language reference into real native storage. Its lifetime and
    /// alias contract was established by an explicit unsafe source operation.
    Native(NativeReference),
    Register(u32),
    /// A unique loan owned by an active caller frame. `caller_depth = 0`
    /// denotes the direct caller; larger values walk further outward. Unlike
    /// a captured snapshot, this target preserves write-back into the live
    /// owning register while a callee holds a reborrow.
    Caller {
        caller_depth: u32,
        register: u32,
    },
    Captured(Arc<VmValue>),
}

#[derive(Clone)]
struct RuntimeHandlerFrame {
    id: u64,
    /// Dynamic call-stack depth of the function that installed this frame.
    /// It remains visible to deeper ordinary calls, but its clause always
    /// executes in this owning frame.
    call_depth: usize,
    effect: DefKey,
    effect_arguments: Vec<VmGenericArgument>,
    operation: u32,
    payload_destinations: Vec<u32>,
    continuation: VmContinuationPolicy,
    target: u32,
    suspended: Option<RuntimeContinuation>,
}

#[derive(Clone)]
struct RuntimeContinuation {
    target: usize,
    dst: u32,
    registers: Vec<Option<VmValue>>,
    performed: RuntimePerformed,
    above: Vec<RuntimeHandlerFrame>,
    pending_leave: Option<PendingLeave>,
    /// A replayable performance starts with the exact source-declared count.
    /// Clause-side replay snapshots carry the decremented remainder back to
    /// the handler, so bytecode cannot replay one capture forever.
    remaining_replays: u32,
    /// Standalone artifacts have one execution frame. Programs additionally
    /// retain the complete caller/callee path, so a performance may cross an
    /// ordinary call and still resume at its original instruction.
    program: Option<RuntimeProgramContinuation>,
}

#[derive(Clone)]
struct RuntimeProgramCaller {
    definition: DefKey,
    registers: Vec<Option<VmValue>>,
    pc: usize,
    return_destination: u32,
}

#[derive(Clone)]
struct RuntimeProgramContinuation {
    definition: DefKey,
    callers: Vec<RuntimeProgramCaller>,
}

/// A clause-side call frame for `ResumeReturn`.  It is intentionally separate
/// from ordinary function calls: resumption return restores the handler
/// environment captured immediately before the transfer, including the
/// retained replay snapshot.
struct RuntimeResumptionReturn {
    pc: usize,
    dst: u32,
    registers: Vec<Option<VmValue>>,
    handlers: Vec<RuntimeHandlerFrame>,
    /// A replayed continuation can cross ordinary calls. Restoring only its
    /// registers and handler frames would resume the saved program counter
    /// in whichever callee happened to return last; retain the full program
    /// location alongside the clause environment.
    program: Option<RuntimeProgramContinuation>,
    /// The protected replay may return with an outer frame still active after
    /// an inner operation has cancelled. Only frames restored for this exact
    /// continuation are permitted to cross the clause-return edge.
    resumed_handler_ids: Vec<u64>,
}

#[derive(Clone)]
struct RuntimePerformed {
    effect: DefKey,
    effect_arguments: Vec<VmGenericArgument>,
    operation: u32,
    payloads: Vec<VmValue>,
}

impl VmValue {
    fn ty(&self) -> VmType {
        match self {
            Self::RawPointer { signature, .. } => signature.clone(),
            Self::Unit => VmType::Unit,
            Self::I64(_) => VmType::I64,
            Self::Usize(_) => VmType::Usize,
            Self::U32(_) => VmType::U32,
            Self::U8(_) => VmType::U8,
            Self::U16(_) => VmType::U16,
            Self::I16(_) => VmType::I16,
            Self::I32(_) => VmType::I32,
            Self::I8(_) => VmType::I8,
            Self::U64(_) => VmType::U64,
            Self::Isize(_) => VmType::Isize,
            Self::U128(_) => VmType::U128,
            Self::I128(_) => VmType::I128,
            Self::F32(_) => VmType::F32,
            Self::F64(_) => VmType::F64,
            Self::Bool(_) => VmType::Bool,
            Self::Char(_) => VmType::Char,
            Self::Text(_) => VmType::Text,
            Self::Bytes(_) => VmType::Bytes,
            Self::StaticData { tag, alignment, .. } => VmType::StaticData {
                element: Box::new(VmType::U8),
                tag: *tag,
                alignment: *alignment,
            },
            Self::Tuple(values) => VmType::Tuple(values.iter().map(VmValue::ty).collect()),
            Self::Array { values, .. } => VmType::Array(Box::new(
                values.first().map(VmValue::ty).unwrap_or(VmType::Unit),
            )),
            Self::StaticArray { .. } => VmType::Array(Box::new(VmType::U8)),
            Self::Record { signature, .. } => signature.clone(),
            Self::Enum { signature, .. } => signature.clone(),
            Self::Callable { signature, .. } => signature.clone(),
            Self::Label { signature, .. } => signature.clone(),
            Self::Resumption { signature, .. } => signature.clone(),
            Self::Reference {
                unique, referent, ..
            } => VmType::Reference {
                unique: *unique,
                referent: Box::new(referent.clone()),
            },
        }
    }
}

fn project_reference(value: &VmValue, fields: &[u32]) -> Result<VmValue, VmArtifactError> {
    let Some((field, rest)) = fields.split_first() else {
        return Ok(value.clone());
    };
    let values: &[VmValue] = match value {
        VmValue::Tuple(values) => values,
        VmValue::Array { values, .. } => values,
        VmValue::StaticArray { bytes, offset, length } => {
            let value = bytes
                .get(*offset..offset.saturating_add(*length))
                .and_then(|bytes| bytes.get(*field as usize))
                .copied()
                .map(VmValue::U8)
                .ok_or(VmArtifactError::InvalidRegister { register: *field })?;
            return project_reference(&value, rest);
        }
        VmValue::Record { fields, .. } | VmValue::Enum { fields, .. } => fields,
        value => {
            return Err(VmArtifactError::ResultType {
                expected: VmType::Tuple(Vec::new()),
                found: value.ty(),
            });
        }
    };
    let value = values
        .get(*field as usize)
        .ok_or(VmArtifactError::InvalidRegister { register: *field })?;
    project_reference(value, rest)
}

// Mutable projections retain uniquely owned backing and detach only shared
// aggregates. Reserve the same logical fields as the previous rebuilding
// implementation before entering each level; physical reuse is not a budget
// discount and no reference/snapshot can observe another owner's mutation.
fn project_reference_mut<'a>(
    value: &'a mut VmValue,
    fields: &[u32],
    budget: &mut ExecutionBudget,
) -> Result<&'a mut VmValue, VmArtifactError> {
    let Some((field, rest)) = fields.split_first() else {
        return Ok(value);
    };
    let values = match value {
        VmValue::Tuple(values) | VmValue::Array { values, .. }
        | VmValue::Record { fields: values, .. } | VmValue::Enum { fields: values, .. } => values,
        VmValue::StaticArray { .. } => return Err(VmArtifactError::UnsupportedEscapingUniqueReference),
        value => return Err(VmArtifactError::ResultType {
            expected: VmType::Tuple(Vec::new()),
            found: value.ty(),
        }),
    };
    budget.reserve_value("reference update fields", values.len())?;
    let slot = Arc::make_mut(values)
        .get_mut(*field as usize)
        .ok_or(VmArtifactError::InvalidRegister { register: *field })?;
    project_reference_mut(slot, rest, budget)
}

// Empty dynamic arrays have no resident from which `VmValue::ty` can infer
// their element type. A Borrow instruction already has an independently
// verified destination layout; retain that layout for empty projected arrays
// instead of manufacturing Array(Unit). Nonempty residents still determine
// their actual type, so an incompatible value is not relabeled as acceptable.
fn borrowed_value_type(value: &VmValue, declared: &VmType) -> VmType {
    match (value, declared) {
        (VmValue::Array { values, .. }, VmType::Array(element)) => VmType::Array(Box::new(
            values.first().map(|value| borrowed_value_type(value, element))
                .unwrap_or_else(|| element.as_ref().clone()),
        )),
        (VmValue::Tuple(values), VmType::Tuple(elements)) if values.len() == elements.len() => {
            VmType::Tuple(values.iter().zip(elements)
                .map(|(value, element)| borrowed_value_type(value, element)).collect())
        }
        _ => value.ty(),
    }
}

fn borrow_value(
    registers: &[Option<VmValue>],
    callers: &[RuntimeProgramCaller],
    source: u32,
    value: &VmValue,
    fields: &[u32],
    unique: bool,
    reborrow: bool,
    declared_referent: &VmType,
) -> Result<VmValue, VmArtifactError> {
    if reborrow {
        let VmValue::Reference {
            target,
            fields: parent_fields,
            unique: parent_unique,
            referent: parent_referent,
        } = value
        else {
            return Err(VmArtifactError::InvalidRegister { register: source });
        };
        if unique && !parent_unique {
            return Err(VmArtifactError::InvalidRegister { register: source });
        }
        let mut path = parent_fields.to_vec();
        path.extend_from_slice(fields);
        if let ReferenceTarget::Native(native) = target {
            let projected = native.project(&path)?;
            let referent = projected.ty().clone();
            if referent != *declared_referent {
                return Err(VmArtifactError::ResultType { expected: declared_referent.clone(), found: referent });
            }
            return Ok(VmValue::Reference { target: ReferenceTarget::Native(projected), fields: Arc::from([]), unique, referent });
        }
        let referent = if fields.is_empty() {
            parent_referent.clone()
        } else {
            borrowed_value_type(
                &project_reference(reference_target(registers, callers, target)?, &path)?,
                declared_referent,
            )
        };
        return Ok(VmValue::Reference {
            target: target.clone(),
            fields: path.into(),
            unique,
            // A reborrow projects from the referent behind the parent
            // reference, never from the `VmValue::Reference` carrier
            // itself.  The latter has no structural fields and used to make
            // a valid `&value.0` fail at runtime.
            referent,
        });
    }
    Ok(VmValue::Reference {
        target: ReferenceTarget::Register(source),
        fields: fields.to_vec().into(),
        unique,
        referent: borrowed_value_type(&project_reference(value, fields)?, declared_referent),
    })
}

fn reference_target<'a>(
    registers: &'a [Option<VmValue>],
    callers: &'a [RuntimeProgramCaller],
    target: &'a ReferenceTarget,
) -> Result<&'a VmValue, VmArtifactError> {
    match target {
        ReferenceTarget::Native(_) => Err(VmArtifactError::NativeMemory { message: "native reference requires a typed memory access" }),
        ReferenceTarget::Register(target) => registers
            .get(*target as usize)
            .and_then(Option::as_ref)
            .ok_or(VmArtifactError::InvalidRegister { register: *target }),
        ReferenceTarget::Caller {
            caller_depth,
            register,
        } => {
            let value = callers
                .len()
                .checked_sub(*caller_depth as usize + 1)
                .and_then(|index| callers.get(index))
                .and_then(|caller| caller.registers.get(*register as usize))
                .and_then(Option::as_ref);
            value.ok_or(VmArtifactError::InvalidRegister {
                register: *register,
            })
        }
        ReferenceTarget::Captured(value) => Ok(value),
    }
}

fn load_reference_target(
    registers: &[Option<VmValue>], callers: &[RuntimeProgramCaller], target: &ReferenceTarget,
    fields: &[u32], budget: &mut ExecutionBudget,
) -> Result<VmValue, VmArtifactError> {
    match target {
        ReferenceTarget::Native(native) => native.read(fields, budget),
        _ => project_reference(reference_target(registers, callers, target)?, fields),
    }
}

fn store_reference_target(
    registers: &mut [Option<VmValue>],
    callers: &mut [RuntimeProgramCaller],
    target: &ReferenceTarget,
    fields: &[u32],
    replacement: VmValue,
    budget: &mut ExecutionBudget,
) -> Result<(), VmArtifactError> {
    if let ReferenceTarget::Native(native) = target {
        return native.write(fields, replacement);
    }
    let value = reference_target_mut(registers, callers, target)?;
    *project_reference_mut(value, fields, budget)? = replacement;
    Ok(())
}

fn reference_target_mut<'a>(
    registers: &'a mut [Option<VmValue>],
    callers: &'a mut [RuntimeProgramCaller],
    target: &ReferenceTarget,
) -> Result<&'a mut VmValue, VmArtifactError> {
    let register = match target {
        ReferenceTarget::Native(_) => return Err(VmArtifactError::NativeMemory { message: "native reference requires a typed memory store" }),
        ReferenceTarget::Register(register) => {
            registers
                .get_mut(*register as usize)
                .ok_or(VmArtifactError::InvalidRegister {
                    register: *register,
                })?
        }
        ReferenceTarget::Caller {
            caller_depth,
            register,
        } => callers
            .len()
            .checked_sub(*caller_depth as usize + 1)
            .and_then(|index| callers.get_mut(index))
            .and_then(|caller| caller.registers.get_mut(*register as usize))
            .ok_or(VmArtifactError::InvalidRegister {
                register: *register,
            })?,
        ReferenceTarget::Captured(_) => {
            return Err(VmArtifactError::UnsupportedEscapingUniqueReference);
        }
    };
    register.as_mut().ok_or(VmArtifactError::InvalidRegister { register: 0 })
}

fn referenced_array(
    registers: &[Option<VmValue>],
    callers: &[RuntimeProgramCaller],
    reference: &VmValue,
) -> Result<Arc<[VmValue]>, VmArtifactError> {
    let VmValue::Reference {
        target,
        fields,
        referent,
        ..
    } = reference
    else {
        return Err(VmArtifactError::InvalidRegister { register: 0 });
    };
    if !matches!(referent, VmType::Array(_)) {
        return Err(VmArtifactError::ResultType {
            expected: VmType::Array(Box::new(VmType::Unit)),
            found: referent.clone(),
        });
    }
    match project_reference(reference_target(registers, callers, target)?, fields)? {
        VmValue::Array { values, .. } => Ok(values),
        found => Err(VmArtifactError::ResultType {
            expected: referent.clone(),
            found: found.ty(),
        }),
    }
}

fn referenced_array_len(registers: &[Option<VmValue>], callers: &[RuntimeProgramCaller], reference: &VmValue) -> Result<usize, VmArtifactError> {
    let VmValue::Reference { target, fields, .. } = reference else { return Err(VmArtifactError::InvalidRegister { register: 0 }); };
    match project_reference(reference_target(registers, callers, target)?, fields)? {
        VmValue::Array { values, .. } => Ok(values.len()),
        VmValue::StaticArray { length, .. } => Ok(length),
        found => Err(VmArtifactError::ResultType { expected: VmType::Array(Box::new(VmType::Unit)), found: found.ty() }),
    }
}

fn referenced_array_mut<'a>(
    registers: &'a mut [Option<VmValue>],
    callers: &'a mut [RuntimeProgramCaller],
    reference: &VmValue,
    budget: &mut ExecutionBudget,
) -> Result<&'a mut [VmValue], VmArtifactError> {
    let VmValue::Reference { target, fields, unique: true, referent } = reference else {
        return Err(VmArtifactError::UnsupportedEscapingUniqueReference);
    };
    if !matches!(referent, VmType::Array(_)) {
        return Err(VmArtifactError::ResultType {
            expected: VmType::Array(Box::new(VmType::Unit)),
            found: referent.clone(),
        });
    }
    let owner = reference_target_mut(registers, callers, target)?;
    match project_reference_mut(owner, fields, budget)? {
        VmValue::Array { values, .. } => Ok(Arc::make_mut(values)),
        found => Err(VmArtifactError::ResultType {
            expected: referent.clone(),
            found: found.ty(),
        }),
    }
}

fn referenced_array_get(registers: &[Option<VmValue>], callers: &[RuntimeProgramCaller], reference: &VmValue, index: usize) -> Result<VmValue, VmArtifactError> {
    let VmValue::Reference { target, fields, .. } = reference else { return Err(VmArtifactError::InvalidRegister { register: 0 }); };
    match project_reference(reference_target(registers, callers, target)?, fields)? {
        VmValue::Array { values, .. } => values.get(index).cloned().ok_or(VmArtifactError::InvalidRegister { register: index as u32 }),
        VmValue::StaticArray { bytes, offset, length } => bytes
            .get(offset..offset.saturating_add(length)).and_then(|bytes| bytes.get(index)).copied()
            .map(VmValue::U8).ok_or(VmArtifactError::InvalidRegister { register: index as u32 }),
        found => Err(VmArtifactError::ResultType { expected: VmType::Array(Box::new(VmType::Unit)), found: found.ty() }),
    }
}

/// Return the prefix before the first malformed or incomplete UTF-8 sequence
/// without materializing an intermediate `Bytes` value. This is the runtime
/// half of std's `String::from_utf8(Vec<u8>)` leaf and works for both ordinary
/// arrays and the read-only static-array facade.
fn referenced_array_utf8_valid_prefix(
    registers: &[Option<VmValue>],
    callers: &[RuntimeProgramCaller],
    reference: &VmValue,
) -> Result<usize, VmArtifactError> {
    let length = referenced_array_len(registers, callers, reference)?;
    let byte = |index| match referenced_array_get(registers, callers, reference, index)? {
        VmValue::U8(value) => Ok(value),
        found => Err(VmArtifactError::ResultType {
            expected: VmType::U8,
            found: found.ty(),
        }),
    };
    let mut index = 0;
    while index < length {
        let first = byte(index)?;
        let (following, second_range) = match first {
            0x00..=0x7f => {
                index += 1;
                continue;
            }
            0xc2..=0xdf => (1, 0x80..=0xbf),
            0xe0 => (2, 0xa0..=0xbf),
            0xed => (2, 0x80..=0x9f),
            0xe1..=0xec | 0xee..=0xef => (2, 0x80..=0xbf),
            0xf0 => (3, 0x90..=0xbf),
            0xf1..=0xf3 => (3, 0x80..=0xbf),
            0xf4 => (3, 0x80..=0x8f),
            _ => return Ok(index),
        };
        let Some(end) = index.checked_add(following + 1).filter(|end| *end <= length) else {
            return Ok(index);
        };
        if !second_range.contains(&byte(index + 1)?) {
            return Ok(index);
        }
        if (index + 2..end).any(|position| !matches!(byte(position), Ok(0x80..=0xbf))) {
            return Ok(index);
        }
        index = end;
    }
    Ok(length)
}

fn replace_referenced_array(
    registers: &mut [Option<VmValue>],
    callers: &mut [RuntimeProgramCaller],
    reference: &VmValue,
    values: Vec<VmValue>,
    budget: &mut ExecutionBudget,
) -> Result<(), VmArtifactError> {
    let capacity = match reference {
        VmValue::Reference { target, fields, .. } => {
            match project_reference(reference_target(registers, callers, target)?, fields)? {
                VmValue::Array { capacity, .. } => capacity,
                _ => values.len(),
            }
        }
        _ => values.len(),
    };
    replace_referenced_array_with_capacity(registers, callers, reference, values, capacity, budget)
}

fn replace_referenced_array_with_capacity(
    registers: &mut [Option<VmValue>],
    callers: &mut [RuntimeProgramCaller],
    reference: &VmValue,
    values: Vec<VmValue>,
    capacity: usize,
    budget: &mut ExecutionBudget,
) -> Result<(), VmArtifactError> {
    let VmValue::Reference {
        target,
        fields,
        unique: true,
        ..
    } = reference
    else {
        return Err(VmArtifactError::UnsupportedEscapingUniqueReference);
    };
    let capacity = capacity.max(values.len());
    store_reference_target(
        registers,
        callers,
        target,
        fields,
        VmValue::Array {
            values: values.into(),
            capacity,
        },
        budget,
    )
}

fn array_element_borrow(
    reference: &VmValue,
    index: u32,
    unique: bool,
    element_type: &VmType,
) -> Result<VmValue, VmArtifactError> {
    let VmValue::Reference {
        target,
        fields,
        unique: parent_unique,
        ..
    } = reference
    else {
        return Err(VmArtifactError::InvalidRegister { register: 0 });
    };
    if unique && !parent_unique {
        return Err(VmArtifactError::UnsupportedEscapingUniqueReference);
    }
    let mut fields = fields.to_vec();
    fields.push(index);
    Ok(VmValue::Reference {
        target: target.clone(),
        fields: fields.into(),
        unique,
        referent: element_type.clone(),
    })
}

fn execute_array_primitive(
    registers: &mut [Option<VmValue>],
    callers: &mut [RuntimeProgramCaller],
    instruction: &VmInstruction,
    budget: &mut ExecutionBudget,
) -> Result<(), VmArtifactError> {
    let index = |register: u32, registers: &[Option<VmValue>]| -> Result<usize, VmArtifactError> {
        Ok(expect_usize(
            registers[register as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register })?,
        )? as usize)
    };
    match instruction {
        VmInstruction::ArrayNew {
            dst, length, fill, ..
        } => {
            let length_value = *length;
            let length = index(length_value, registers)?;
            budget.reserve_value("array elements", length)?;
            let fill = registers[*fill as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *fill })?
                .clone();
            registers[*dst as usize] = Some(VmValue::Array {
                values: vec![fill; length].into(),
                capacity: length,
            });
        }
        VmInstruction::ArrayEmpty { dst, .. } => {
            registers[*dst as usize] = Some(VmValue::Array {
                values: Arc::from([]),
                capacity: 0,
            })
        }
        VmInstruction::ArrayLen { dst, value, .. } => {
            registers[*dst as usize] = Some(VmValue::Usize(
                referenced_array_len(
                    registers,
                    callers,
                    registers[*value as usize]
                        .as_ref()
                        .ok_or(VmArtifactError::InvalidRegister { register: *value })?,
                )? as u64,
            ));
        }
        VmInstruction::ArrayCapacity { dst, value, .. } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?;
            let VmValue::Reference { target, fields, .. } = reference else {
                return Err(VmArtifactError::InvalidRegister { register: *value });
            };
            let capacity = match
                project_reference(reference_target(registers, callers, target)?, fields)?
            {
                VmValue::Array { capacity, .. } => capacity,
                VmValue::StaticArray { length, .. } => length,
                _ => return Err(VmArtifactError::InvalidRegister { register: *value }),
            };
            registers[*dst as usize] = Some(VmValue::Usize(capacity as u64));
        }
        VmInstruction::ArrayGetCopy {
            dst,
            value,
            index: position,
            ..
        } => {
            let reference = registers[*value as usize].as_ref().ok_or(VmArtifactError::InvalidRegister { register: *value })?;
            registers[*dst as usize] = Some(referenced_array_get(registers, callers, reference, index(*position, registers)?)?);
        }
        VmInstruction::ArrayGetMove {
            dst,
            value,
            index: position,
            ..
        } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let length = referenced_array(registers, callers, &reference)?.len();
            let position = index(*position, registers)?;
            if position >= length {
                return Err(VmArtifactError::InvalidRegister { register: position as u32 });
            }
            let moved = referenced_array_mut(registers, callers, &reference, budget)?
                .get_mut(position)
                .ok_or(VmArtifactError::InvalidRegister {
                    register: position as u32,
                })?;
            let moved = std::mem::replace(moved, VmValue::Unit);
            registers[*dst as usize] = Some(moved);
        }
        VmInstruction::ArrayGetBorrow {
            dst,
            value,
            index: position,
            unique,
            element_type,
        } => {
            let position = index(*position, registers)?;
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?;
            let VmValue::Reference { target, fields, .. } = reference else { return Err(VmArtifactError::InvalidRegister { register: *value }); };
            match project_reference(reference_target(registers, callers, target)?, fields)? {
                VmValue::Array { values, .. } => {
                    values.get(position).ok_or(VmArtifactError::InvalidRegister { register: position as u32 })?;
                    registers[*dst as usize] = Some(array_element_borrow(reference, position as u32, *unique, element_type)?);
                }
                VmValue::StaticArray { .. } => {
                    if *unique { return Err(VmArtifactError::UnsupportedEscapingUniqueReference); }
                    let value = referenced_array_get(registers, callers, reference, position)?;
                    registers[*dst as usize] = Some(VmValue::Reference { target: ReferenceTarget::Captured(Arc::new(value)), fields: Arc::from([]), unique: false, referent: element_type.clone() });
                }
                _ => return Err(VmArtifactError::InvalidRegister { register: *value }),
            }
        }
        VmInstruction::ArraySetMove {
            value,
            index: position,
            item,
            ..
        } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let length = referenced_array(registers, callers, &reference)?.len();
            let position = index(*position, registers)?;
            if position >= length {
                return Err(VmArtifactError::InvalidRegister { register: position as u32 });
            }
            let item = registers[*item as usize]
                .take()
                .ok_or(VmArtifactError::InvalidRegister { register: *item })?;
            referenced_array_mut(registers, callers, &reference, budget)?[position] = item;
        }
        VmInstruction::ArrayPushMove { value, item, .. } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let mut values = referenced_array(registers, callers, &reference)?.to_vec();
            budget.reserve_value("array elements", values.len().saturating_add(1))?;
            values.push(
                registers[*item as usize]
                    .take()
                    .ok_or(VmArtifactError::InvalidRegister { register: *item })?,
            );
            replace_referenced_array(registers, callers, &reference, values, budget)?;
        }
        VmInstruction::ArrayPushUtf8Char { value, character } => {
            let reference = registers[*value as usize].as_ref().ok_or(VmArtifactError::InvalidRegister { register: *value })?.clone();
            let character_register = *character;
            let character = expect_char(registers[character_register as usize].as_ref().ok_or(VmArtifactError::InvalidRegister { register: character_register })?)?;
            let mut values = referenced_array(registers, callers, &reference)?.to_vec();
            let mut encoded = [0; 4];
            values.extend(character.encode_utf8(&mut encoded).bytes().map(VmValue::U8));
            registers[character_register as usize] = None;
            replace_referenced_array(registers, callers, &reference, values, budget)?;
        }
        VmInstruction::ArrayInsertUtf8FromSlice { dst, value, index: position, source, start, length } => {
            let destination_reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let position = index(*position, registers)?;
            let source_reference = registers[*source as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *source })?;
            let start = index(*start, registers)?;
            let length_register = *length;
            let length = index(length_register, registers)?;
            let end = start.checked_add(length).ok_or(VmArtifactError::InvalidRegister {
                register: length_register,
            })?;
            if end > referenced_array_len(registers, callers, source_reference)? {
                return Err(VmArtifactError::InvalidRegister { register: *source });
            }
            let copied = (start..end)
                .map(|index| referenced_array_get(registers, callers, source_reference, index))
                .collect::<Result<Vec<_>, _>>()?;
            let destination_length = referenced_array_len(registers, callers, &destination_reference)?;
            let boundary = if position > destination_length {
                false
            } else if position == 0 || position == destination_length {
                true
            } else {
                let byte = expect_u8(&referenced_array_get(
                    registers,
                    callers,
                    &destination_reference,
                    position,
                )?)?;
                byte < 128 || byte >= 192
            };
            if boundary {
                let mut values = referenced_array(registers, callers, &destination_reference)?.to_vec();
                budget.reserve_value("array elements", values.len().saturating_add(copied.len()))?;
                values.splice(position..position, copied);
                replace_referenced_array(registers, callers, &destination_reference, values, budget)?;
            }
            registers[*dst as usize] = Some(VmValue::Usize(u64::from(boundary)));
        }
        VmInstruction::ArrayPopUtf8Char { dst, value } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let mut values = referenced_array(registers, callers, &reference)?.to_vec();
            let (character, present) = if values.is_empty() {
                ('\0', false)
            } else {
                let bytes = values.iter().map(expect_u8).collect::<Result<Vec<_>, _>>()?;
                let text = std::str::from_utf8(&bytes)
                    .map_err(|_| VmArtifactError::InvalidRegister { register: *value })?;
                let character = text.chars().next_back().expect("nonempty UTF-8 text");
                values.truncate(values.len().saturating_sub(character.len_utf8()));
                (character, true)
            };
            if present {
                replace_referenced_array(registers, callers, &reference, values, budget)?;
            }
            registers[*dst as usize] = Some(VmValue::Tuple(
                Arc::from([VmValue::Char(character), VmValue::Usize(u64::from(present))]),
            ));
        }
        VmInstruction::ArrayUtf8CharAt { dst, value, start, length, index: position } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?;
            let start = index(*start, registers)?;
            let length_register = *length;
            let length = index(length_register, registers)?;
            let end = start.checked_add(length).ok_or(VmArtifactError::InvalidRegister {
                register: length_register,
            })?;
            if end > referenced_array_len(registers, callers, reference)? {
                return Err(VmArtifactError::InvalidRegister { register: *value });
            }
            let position_register = *position;
            let position = index(position_register, registers)?;
            let (character, width) = if position >= length {
                ('\0', 0)
            } else {
                let bytes = (start..end)
                    .map(|index| referenced_array_get(registers, callers, reference, index))
                    .collect::<Result<Vec<_>, _>>()?
                    .iter()
                    .map(expect_u8)
                    .collect::<Result<Vec<_>, _>>()?;
                let text = std::str::from_utf8(&bytes)
                    .map_err(|_| VmArtifactError::InvalidRegister { register: *value })?;
                let suffix = text.get(position..).ok_or(VmArtifactError::InvalidRegister {
                    register: position_register,
                })?;
                let character = suffix.chars().next().ok_or(VmArtifactError::InvalidRegister {
                    register: position_register,
                })?;
                (character, character.len_utf8())
            };
            registers[*dst as usize] = Some(VmValue::Tuple(
                Arc::from([VmValue::Char(character), VmValue::Usize(width as u64)]),
            ));
        }
        VmInstruction::ArrayExtendFromSlice { value, source, start, length, .. } => {
            // Snapshot the source before replacing the destination. This also
            // gives deterministic behavior if a trusted caller supplies two
            // views of the same backing allocation.
            let source_reference = registers[*source as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *source })?
                .clone();
            let start = index(*start, registers)?;
            let length_register = *length;
            let length = index(length_register, registers)?;
            let end = start.checked_add(length).ok_or(VmArtifactError::InvalidRegister {
                register: length as u32,
            })?;
            if end > referenced_array_len(registers, callers, &source_reference)? {
                return Err(VmArtifactError::InvalidRegister { register: *source });
            }
            let copied = (start..end)
                .map(|index| referenced_array_get(registers, callers, &source_reference, index))
                .collect::<Result<Vec<_>, _>>()?;
            let destination_reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let mut values = referenced_array(registers, callers, &destination_reference)?.to_vec();
            budget.reserve_value("array elements", values.len().saturating_add(copied.len()))?;
            values.extend(copied);
            replace_referenced_array(registers, callers, &destination_reference, values, budget)?;
        }
        VmInstruction::ArrayInsertMove { value, index: position, item, .. } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let position = index(*position, registers)?;
            let mut values = referenced_array(registers, callers, &reference)?.to_vec();
            if position > values.len() {
                return Err(VmArtifactError::InvalidRegister { register: *value });
            }
            budget.reserve_value("array elements", values.len().saturating_add(1))?;
            let item = registers[*item as usize]
                .take()
                .ok_or(VmArtifactError::InvalidRegister { register: *item })?;
            values.insert(position, item);
            replace_referenced_array(registers, callers, &reference, values, budget)?;
        }
        VmInstruction::ArrayRemoveMove { dst, value, index: position, .. } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let position = index(*position, registers)?;
            let mut values = referenced_array(registers, callers, &reference)?.to_vec();
            if position >= values.len() {
                return Err(VmArtifactError::InvalidRegister { register: *value });
            }
            let removed = values.remove(position);
            replace_referenced_array(registers, callers, &reference, values, budget)?;
            registers[*dst as usize] = Some(removed);
        }
        VmInstruction::ArrayAppendMove { value, source, .. } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let source_register = *source;
            let source_value = registers[source_register as usize]
                .take()
                .ok_or(VmArtifactError::InvalidRegister { register: source_register })?;
            let VmValue::Array { values: source, .. } = source_value else {
                return Err(VmArtifactError::InvalidRegister { register: source_register });
            };
            let mut values = referenced_array(registers, callers, &reference)?.to_vec();
            budget.reserve_value("array elements", values.len().saturating_add(source.len()))?;
            values.extend(source.iter().cloned());
            replace_referenced_array(registers, callers, &reference, values, budget)?;
        }
        VmInstruction::ArrayTruncateDiscard { value, length, .. } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let length = index(*length, registers)?;
            let mut values = referenced_array(registers, callers, &reference)?.to_vec();
            values.truncate(length);
            replace_referenced_array(registers, callers, &reference, values, budget)?;
        }
        VmInstruction::ArrayReverseMove { value, .. } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            referenced_array_mut(registers, callers, &reference, budget)?.reverse();
        }
        VmInstruction::ArraySplitOffMove { dst, value, index: position, .. } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let position = index(*position, registers)?;
            let mut values = referenced_array(registers, callers, &reference)?.to_vec();
            if position > values.len() {
                return Err(VmArtifactError::InvalidRegister { register: *value });
            }
            let suffix = values.split_off(position);
            let capacity = suffix.len();
            replace_referenced_array(registers, callers, &reference, values, budget)?;
            registers[*dst as usize] = Some(VmValue::Array {
                values: suffix.into(),
                capacity,
            });
        }
        VmInstruction::ArraySplitBorrowUnique {
            dst,
            value,
            start,
            length,
            index: split,
            ..
        } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let VmValue::Reference {
                target,
                fields,
                unique: true,
                referent,
            } = reference
            else {
                return Err(VmArtifactError::InvalidRegister { register: *value });
            };
            let start = index(*start, registers)?;
            let length_register = *length;
            let length = index(length_register, registers)?;
            let split = index(*split, registers)?;
            let end = start.checked_add(length).ok_or(VmArtifactError::InvalidRegister {
                register: length_register,
            })?;
            if split > length || end > referenced_array_len(registers, callers, &VmValue::Reference {
                target: target.clone(), fields: fields.clone(), unique: true, referent: referent.clone(),
            })? {
                return Err(VmArtifactError::InvalidRegister { register: *value });
            }
            // The compiler verifies the private array-window leaf identity and
            // `SliceMut` keeps its own start/length fields. The two reference
            // carriers intentionally share one allocation, but source code
            // cannot forge or widen either private view.
            let make_window = || VmValue::Reference {
                target: target.clone(),
                fields: fields.clone(),
                unique: true,
                referent: referent.clone(),
            };
            registers[*dst as usize] = Some(VmValue::Tuple(
                vec![make_window(), make_window()].into(),
            ));
        }
        VmInstruction::ArrayInsertFromSlice { value, index: position, source, start, length, .. } => {
            let source_reference = registers[*source as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *source })?
                .clone();
            let position = index(*position, registers)?;
            let start = index(*start, registers)?;
            let length_register = *length;
            let length = index(length_register, registers)?;
            let end = start.checked_add(length).ok_or(VmArtifactError::InvalidRegister {
                register: length_register,
            })?;
            if end > referenced_array_len(registers, callers, &source_reference)? {
                return Err(VmArtifactError::InvalidRegister { register: *source });
            }
            let copied = (start..end)
                .map(|index| referenced_array_get(registers, callers, &source_reference, index))
                .collect::<Result<Vec<_>, _>>()?;
            let destination_reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let mut values = referenced_array(registers, callers, &destination_reference)?.to_vec();
            if position > values.len() {
                return Err(VmArtifactError::InvalidRegister { register: *value });
            }
            budget.reserve_value("array elements", values.len().saturating_add(copied.len()))?;
            values.splice(position..position, copied);
            replace_referenced_array(registers, callers, &destination_reference, values, budget)?;
        }
        VmInstruction::ArrayPopMove { dst, value, .. } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let mut values = referenced_array(registers, callers, &reference)?.to_vec();
            let moved = values
                .pop()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?;
            replace_referenced_array(registers, callers, &reference, values, budget)?;
            registers[*dst as usize] = Some(moved);
        }
        VmInstruction::ArrayReserve {
            value, additional, ..
        } => {
            let reference = registers[*value as usize]
                .as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?
                .clone();
            let wanted = referenced_array(registers, callers, &reference)?
                .len()
                .saturating_add(index(*additional, registers)?);
            budget.reserve_value("array reserve", wanted)?;
            let VmValue::Reference { target, fields, .. } = &reference else {
                return Err(VmArtifactError::InvalidRegister { register: *value });
            };
            let (values, capacity) =
                match project_reference(reference_target(registers, callers, target)?, fields)? {
                    VmValue::Array { values, capacity } => (values.to_vec(), capacity),
                    _ => return Err(VmArtifactError::InvalidRegister { register: *value }),
                };
            if wanted > capacity {
                replace_referenced_array_with_capacity(
                    registers, callers, &reference, values, wanted, budget,
                )?;
            }
        }
        VmInstruction::ArrayFinishDrained { value, .. } => {
            let values = registers[*value as usize]
                .take()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?;
            if !matches!(values, VmValue::Array { .. }) {
                return Err(VmArtifactError::ResultType {
                    expected: VmType::Array(Box::new(VmType::Unit)),
                    found: values.ty(),
                });
            }
        }
        _ => unreachable!("non-array instruction passed to array primitive executor"),
    }
    Ok(())
}

/// Freeze a value for a boundary whose payload is retained independently of
/// its current frame (callable captures and continuations). Shared references
/// become immutable snapshots; unique references remain rejected because
/// snapshotting would silently sever their write-back alias. Ordinary
/// call/return boundaries use `transfer_call_frame_value` instead.
fn freeze_frame_value(
    value: &VmValue,
    registers: &[Option<VmValue>],
    callers: &[RuntimeProgramCaller],
) -> Result<VmValue, VmArtifactError> {
    match value {
        VmValue::Reference { target: ReferenceTarget::Native(_), .. } => Ok(value.clone()),
        VmValue::Reference { unique: true, .. } => {
            Err(VmArtifactError::UnsupportedEscapingUniqueReference)
        }
        VmValue::Reference {
            target,
            fields,
            unique: false,
            referent,
        } => {
            // Nested references are expressed in their owner's frame. A
            // borrowed aggregate can contain loans to any retained caller;
            // freezing it must resolve those loans in that caller's context.
            let (owner_registers, owner_callers) = match target {
                ReferenceTarget::Caller { caller_depth, register } => {
                    let index = callers.len().checked_sub(*caller_depth as usize + 1)
                        .ok_or(VmArtifactError::InvalidRegister { register: *register })?;
                    (callers[index].registers.as_slice(), &callers[..index])
                }
                ReferenceTarget::Register(_) => (registers, callers),
                ReferenceTarget::Captured(_) | ReferenceTarget::Native(_) => (&[][..], &[][..]),
            };
            let projected = project_reference(reference_target(registers, callers, target)?, fields)?;
            Ok(VmValue::Reference {
                target: ReferenceTarget::Captured(Arc::new(freeze_frame_value(
                    &projected, owner_registers, owner_callers,
                )?)),
                fields: Arc::from([]),
                unique: false,
                referent: referent.clone(),
            })
        }
        VmValue::Tuple(values) => Ok(VmValue::Tuple(
            values
                .iter()
                .map(|value| freeze_frame_value(value, registers, callers))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
        )),
        VmValue::Array { values, capacity } => Ok(VmValue::Array {
            values: values
                .iter()
                .map(|value| freeze_frame_value(value, registers, callers))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
            capacity: *capacity,
        }),
        VmValue::Record {
            definition,
            fields,
            signature,
        } => Ok(VmValue::Record {
            definition: *definition,
            fields: fields
                .iter()
                .map(|value| freeze_frame_value(value, registers, callers))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
            signature: signature.clone(),
        }),
        VmValue::Enum {
            definition,
            variant,
            fields,
            signature,
        } => Ok(VmValue::Enum {
            definition: *definition,
            variant: *variant,
            fields: fields
                .iter()
                .map(|value| freeze_frame_value(value, registers, callers))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
            signature: signature.clone(),
        }),
        VmValue::Label { .. } => Err(VmArtifactError::InvalidLabelContract {
            message: "callable capture cannot retain a lexical label",
        }),
        VmValue::Resumption { .. } => Err(VmArtifactError::HandlerResumeUnavailable),
        value => Ok(value.clone()),
    }
}

#[derive(Clone, Copy)]
enum UniqueReferenceTransfer {
    IntoCallee,
    ToCaller,
}

/// Translate reference targets embedded in a value read through a caller
/// reference into the current callee's coordinate system. A caller-local
/// target at depth `n` remains one caller farther away for every nested call;
/// preserving that arithmetic recursively is what lets destructors safely
/// observe aggregates containing mutable references.
fn rebase_caller_references(value: VmValue, caller_depth: u32) -> Result<VmValue, VmArtifactError> {
    match value {
        VmValue::Reference {
            target,
            fields,
            unique,
            referent,
        } => {
            let target = match target {
                ReferenceTarget::Native(native) => ReferenceTarget::Native(native),
                ReferenceTarget::Register(register) => ReferenceTarget::Caller {
                    caller_depth,
                    register,
                },
                ReferenceTarget::Caller {
                    caller_depth: nested,
                    register,
                } => ReferenceTarget::Caller {
                    caller_depth: caller_depth
                        .checked_add(nested)
                        .and_then(|depth| depth.checked_add(1))
                        .ok_or(VmArtifactError::UnsupportedEscapingUniqueReference)?,
                    register,
                },
                ReferenceTarget::Captured(value) => ReferenceTarget::Captured(value),
            };
            Ok(VmValue::Reference {
                target,
                fields,
                unique,
                referent,
            })
        }
        VmValue::Tuple(values) => Ok(VmValue::Tuple(
            values
                .iter()
                .cloned()
                .map(|value| rebase_caller_references(value, caller_depth))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
        )),
        VmValue::Array { values, capacity } => Ok(VmValue::Array {
            values: values
                .iter()
                .cloned()
                .map(|value| rebase_caller_references(value, caller_depth))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
            capacity,
        }),
        VmValue::Record {
            definition,
            fields,
            signature,
        } => Ok(VmValue::Record {
            definition,
            fields: fields
                .iter()
                .cloned()
                .map(|value| rebase_caller_references(value, caller_depth))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
            signature,
        }),
        VmValue::Enum {
            definition,
            variant,
            fields,
            signature,
        } => Ok(VmValue::Enum {
            definition,
            variant,
            fields: fields
                .iter()
                .cloned()
                .map(|value| rebase_caller_references(value, caller_depth))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
            signature,
        }),
        value => Ok(value),
    }
}

/// Move a value across an ordinary call boundary. Both shared and unique
/// incoming loans keep their surviving caller owner, with rebased coordinates.
/// Already-frozen captures are frame-neutral and keep their immutable backing.
/// Only a shared reference returned from a callee-local register needs a new
/// snapshot before that frame disappears. Unique local returns remain rejected.
/// Independently retained callable captures still use `freeze_frame_value`.
fn transfer_call_frame_value(
    value: &VmValue,
    registers: &[Option<VmValue>],
    callers: &[RuntimeProgramCaller],
    transfer: UniqueReferenceTransfer,
) -> Result<VmValue, VmArtifactError> {
    match value {
        VmValue::Reference {
            unique: false,
            target: ReferenceTarget::Register(_),
            ..
        } if matches!(transfer, UniqueReferenceTransfer::ToCaller) => {
            freeze_frame_value(value, registers, callers)
        }
        VmValue::Reference {
            unique,
            target,
            fields,
            referent,
        } => {
            let target = match (transfer, target) {
                (_, ReferenceTarget::Native(native)) => ReferenceTarget::Native(native.clone()),
                (UniqueReferenceTransfer::IntoCallee, ReferenceTarget::Register(register)) => {
                    ReferenceTarget::Caller {
                        caller_depth: 0,
                        register: *register,
                    }
                }
                (
                    UniqueReferenceTransfer::IntoCallee,
                    ReferenceTarget::Caller {
                        caller_depth,
                        register,
                    },
                ) => ReferenceTarget::Caller {
                    caller_depth: caller_depth
                        .checked_add(1)
                        .ok_or(VmArtifactError::UnsupportedEscapingUniqueReference)?,
                    register: *register,
                },
                (
                    UniqueReferenceTransfer::ToCaller,
                    ReferenceTarget::Caller {
                        caller_depth: 0,
                        register,
                    },
                ) => ReferenceTarget::Register(*register),
                (
                    UniqueReferenceTransfer::ToCaller,
                    ReferenceTarget::Caller {
                        caller_depth,
                        register,
                    },
                ) => ReferenceTarget::Caller {
                    caller_depth: caller_depth - 1,
                    register: *register,
                },
                // Captured/static shared storage already has a frame-neutral
                // identity. Unlike a lexical register it needs no rebasing
                // at an ordinary call boundary.
                (_, ReferenceTarget::Captured(value)) if !*unique => {
                    ReferenceTarget::Captured(value.clone())
                }
                (_, ReferenceTarget::Captured(_))
                | (UniqueReferenceTransfer::ToCaller, ReferenceTarget::Register(_)) => {
                    return Err(VmArtifactError::UnsupportedEscapingUniqueReference);
                }
            };
            Ok(VmValue::Reference {
                target,
                fields: fields.clone(),
                unique: *unique,
                referent: referent.clone(),
            })
        }
        VmValue::Tuple(values) => Ok(VmValue::Tuple(
            values
                .iter()
                .map(|value| transfer_call_frame_value(value, registers, callers, transfer))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
        )),
        VmValue::Array { values, capacity } => Ok(VmValue::Array {
            values: values
                .iter()
                .map(|value| transfer_call_frame_value(value, registers, callers, transfer))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
            capacity: *capacity,
        }),
        VmValue::Record {
            definition,
            fields,
            signature,
        } => Ok(VmValue::Record {
            definition: *definition,
            fields: fields
                .iter()
                .map(|value| transfer_call_frame_value(value, registers, callers, transfer))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
            signature: signature.clone(),
        }),
        VmValue::Enum {
            definition,
            variant,
            fields,
            signature,
        } => Ok(VmValue::Enum {
            definition: *definition,
            variant: *variant,
            fields: fields
                .iter()
                .map(|value| transfer_call_frame_value(value, registers, callers, transfer))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
            signature: signature.clone(),
        }),
        value => Ok(value.clone()),
    }
}

// Effect clauses run in their installing frame, not necessarily the frame
// that performed the operation. Keep the suspended payload in its original
// coordinates; translate only the values exposed to the selected clause.
fn transfer_to_ancestor_frame(
    mut value: VmValue,
    registers: &[Option<VmValue>],
    callers: &[RuntimeProgramCaller],
    owner_depth: usize,
    budget: &mut ExecutionBudget,
) -> Result<VmValue, VmArtifactError> {
    if owner_depth > callers.len() {
        return Err(VmArtifactError::HandlerStateMismatch);
    }
    for depth in (owner_depth + 1..=callers.len()).rev() {
        budget.tick()?;
        let owner_registers = if depth == callers.len() {
            registers
        } else {
            callers[depth].registers.as_slice()
        };
        value = transfer_call_frame_value(
            &value, owner_registers, &callers[..depth], UniqueReferenceTransfer::ToCaller,
        )?;
    }
    Ok(value)
}

// A resumption may be invoked through helpers in the clause. Translate back
// through the installing frame, then into the original suspended call chain;
// source and destination can be siblings, not just adjacent frames.
fn transfer_to_resumed_frame(
    value: VmValue,
    registers: &[Option<VmValue>],
    callers: &[RuntimeProgramCaller],
    handler_depth: usize,
    destination_depth: usize,
    budget: &mut ExecutionBudget,
) -> Result<VmValue, VmArtifactError> {
    if destination_depth < handler_depth {
        return Err(VmArtifactError::HandlerStateMismatch);
    }
    let mut value = transfer_to_ancestor_frame(value, registers, callers, handler_depth, budget)?;
    for _ in handler_depth..destination_depth {
        budget.tick()?;
        value = transfer_call_frame_value(&value, &[], &[], UniqueReferenceTransfer::IntoCallee)?;
    }
    Ok(value)
}

fn format_vm_value(value: &VmValue) -> String {
    match value {
        VmValue::RawPointer { .. } => "<raw pointer>".into(),
        VmValue::Unit => "()".into(),
        VmValue::I64(value) => value.to_string(),
        VmValue::Usize(value) => value.to_string(),
        VmValue::U32(value) => value.to_string(),
        VmValue::U8(value) => value.to_string(),
        VmValue::U16(value) => value.to_string(),
        VmValue::I16(value) => value.to_string(),
        VmValue::I32(value) => value.to_string(),
        VmValue::I8(value) => value.to_string(),
        VmValue::U64(value) => value.to_string(),
        VmValue::Isize(value) => value.to_string(),
        VmValue::U128(value) => value.to_string(),
        VmValue::I128(value) => value.to_string(),
        VmValue::F32(value) => value.to_string(),
        VmValue::F64(value) => value.to_string(),
        VmValue::Bool(value) => value.to_string(),
        VmValue::Char(value) => format!("{value:?}"),
        VmValue::Text(value) => format!("{value:?}"),
        VmValue::Bytes(value) => format!("{value:?}"),
        VmValue::StaticData { tag, alignment, bytes, offset, length } => {
            let end = offset.saturating_add(*length).min(bytes.len());
            format!("static<{tag:#x}, align {alignment}>({:?})", &bytes[*offset..end])
        }
        VmValue::Tuple(values) => format!(
            "({})",
            values
                .iter()
                .map(format_vm_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        VmValue::Array { values, .. } => format!(
            "[{}]",
            values
                .iter()
                .map(format_vm_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        VmValue::StaticArray { bytes, offset, length } => {
            let end = offset.saturating_add(*length).min(bytes.len());
            format!("{:?}", &bytes[*offset..end])
        }
        VmValue::Record {
            definition, fields, ..
        } => format!(
            "record@{definition:?}({})",
            fields
                .iter()
                .map(format_vm_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        VmValue::Enum {
            definition,
            variant,
            fields,
            ..
        } => format!(
            "enum@{definition:?}#{variant}({})",
            fields
                .iter()
                .map(format_vm_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        VmValue::Callable {
            callee, captures, ..
        } => format!("callable@{callee:?}[captures={}]", captures.len()),
        VmValue::Label { owner, label, .. } => format!("label@{owner:?}#{label}"),
        VmValue::Resumption { frame, .. } => format!("resumption@{frame}"),
        VmValue::Reference { target, fields, .. } => {
            let target = match target {
                ReferenceTarget::Register(target) => format!("register@{target}"),
                ReferenceTarget::Caller {
                    caller_depth,
                    register,
                } => format!("caller-{caller_depth}@{register}"),
                ReferenceTarget::Captured(_) => "captured".into(),
                ReferenceTarget::Native(_) => "native".into(),
            };
            format!("reference@{target}[fields={}]", fields.len())
        }
    }
}
fn expect_unit(value: impl Borrow<VmValue>) -> Result<(), VmArtifactError> {
    match value.borrow() {
        VmValue::Unit => Ok(()),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Unit,
            found: value.ty(),
        }),
    }
}
fn expect_i64(value: impl Borrow<VmValue>) -> Result<i64, VmArtifactError> {
    match value.borrow() {
        VmValue::I64(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::I64,
            found: value.ty(),
        }),
    }
}
fn expect_usize(value: impl Borrow<VmValue>) -> Result<u64, VmArtifactError> {
    match value.borrow() {
        VmValue::Usize(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Usize,
            found: value.ty(),
        }),
    }
}
fn expect_u32(value: impl Borrow<VmValue>) -> Result<u32, VmArtifactError> {
    match value.borrow() {
        VmValue::U32(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::U32,
            found: value.ty(),
        }),
    }
}
fn expect_u8(value: impl Borrow<VmValue>) -> Result<u8, VmArtifactError> {
    match value.borrow() {
        VmValue::U8(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::U8,
            found: value.ty(),
        }),
    }
}
fn expect_u16(value: impl Borrow<VmValue>) -> Result<u16, VmArtifactError> {
    match value.borrow() {
        VmValue::U16(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::U16,
            found: value.ty(),
        }),
    }
}
fn expect_i16(value: impl Borrow<VmValue>) -> Result<i16, VmArtifactError> {
    match value.borrow() {
        VmValue::I16(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::I16,
            found: value.ty(),
        }),
    }
}
fn expect_i32(value: impl Borrow<VmValue>) -> Result<i32, VmArtifactError> {
    match value.borrow() {
        VmValue::I32(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::I32,
            found: value.ty(),
        }),
    }
}
fn expect_i8(value: impl Borrow<VmValue>) -> Result<i8, VmArtifactError> {
    match value.borrow() {
        VmValue::I8(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::I8,
            found: value.ty(),
        }),
    }
}
fn expect_u64(value: impl Borrow<VmValue>) -> Result<u64, VmArtifactError> {
    match value.borrow() {
        VmValue::U64(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::U64,
            found: value.ty(),
        }),
    }
}
fn expect_isize(value: impl Borrow<VmValue>) -> Result<i64, VmArtifactError> {
    match value.borrow() {
        VmValue::Isize(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Isize,
            found: value.ty(),
        }),
    }
}
fn expect_u128(value: impl Borrow<VmValue>) -> Result<u128, VmArtifactError> {
    match value.borrow() {
        VmValue::U128(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::U128,
            found: value.ty(),
        }),
    }
}
fn expect_i128(value: impl Borrow<VmValue>) -> Result<i128, VmArtifactError> {
    match value.borrow() {
        VmValue::I128(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::I128,
            found: value.ty(),
        }),
    }
}
fn expect_bytes(value: impl Borrow<VmValue>) -> Result<Arc<[u8]>, VmArtifactError> {
    match value.borrow() {
        VmValue::Bytes(value) => Ok(value.clone()),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Bytes,
            found: value.ty(),
        }),
    }
}
fn expect_tuple_i64(value: impl Borrow<VmValue>) -> Result<Vec<i64>, VmArtifactError> {
    match value.borrow() {
        VmValue::Tuple(values) => values.iter().map(expect_i64).collect(),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Tuple(Vec::new()),
            found: value.ty(),
        }),
    }
}
fn expect_array_i64(value: impl Borrow<VmValue>) -> Result<Vec<i64>, VmArtifactError> {
    match value.borrow() {
        VmValue::Array { values, .. } => values.iter().map(expect_i64).collect(),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Array(Box::new(VmType::I64)),
            found: value.ty(),
        }),
    }
}
fn expect_record_i64(value: impl Borrow<VmValue>) -> Result<Vec<i64>, VmArtifactError> {
    match value.borrow() {
        VmValue::Record {
            definition, fields, ..
        } => {
            let _ = definition;
            fields.iter().map(expect_i64).collect()
        }
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Nominal {
                definition: DefKey(Digest::of_bytes(b"expected-record")),
                arguments: Vec::new(),
            },
            found: value.ty(),
        }),
    }
}
fn expect_enum_i64(value: impl Borrow<VmValue>) -> Result<Vec<i64>, VmArtifactError> {
    match value.borrow() {
        VmValue::Enum {
            definition,
            variant,
            fields,
            ..
        } => {
            let _ = (definition, variant);
            fields.iter().map(expect_i64).collect()
        }
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Nominal {
                definition: DefKey(Digest::of_bytes(b"expected-enum")),
                arguments: Vec::new(),
            },
            found: value.ty(),
        }),
    }
}
fn expect_f64(value: impl Borrow<VmValue>) -> Result<f64, VmArtifactError> {
    match value.borrow() {
        VmValue::F64(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::F64,
            found: value.ty(),
        }),
    }
}
fn expect_f32(value: impl Borrow<VmValue>) -> Result<f32, VmArtifactError> {
    match value.borrow() {
        VmValue::F32(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::F32,
            found: value.ty(),
        }),
    }
}

/// Keep the VM's observable IEEE-754 representation independent of the host
/// NaN payload selected by an arithmetic instruction.  The numerical
/// comparison rules remain ordinary IEEE rules; only the non-semantic payload
/// encoding is collapsed.
fn canonical_vm_f64(value: f64) -> f64 {
    f64::from_bits(canonical_f64_bits(value.to_bits()))
}

fn canonical_vm_f32(value: f32) -> f32 {
    if value.is_nan() {
        f32::from_bits(0x7fc0_0000)
    } else {
        value
    }
}

fn float_argument<'a>(
    arguments: &[u32],
    index: usize,
    registers: &'a [Option<VmValue>],
) -> Result<&'a VmValue, VmArtifactError> {
    let register = *arguments
        .get(index)
        .ok_or(VmArtifactError::MalformedEncoding {
            message: "floating runtime primitive has the wrong arity",
        })?;
    registers
        .get(register as usize)
        .and_then(Option::as_ref)
        .ok_or(VmArtifactError::ReadBeforeWrite { register })
}

fn execute_float_intrinsic(
    primitive: FloatPrimitive,
    arguments: &[u32],
    registers: &[Option<VmValue>],
) -> Result<VmValue, VmArtifactError> {
    let (parameters, _) = primitive.scalar_signature();
    if arguments.len() != parameters.len() {
        return Err(VmArtifactError::MalformedEncoding {
            message: "floating runtime primitive has the wrong arity",
        });
    }
    match primitive {
        FloatPrimitive::Binary { width, operation } => match width {
            FloatWidth::F32 => {
                let left = expect_f32(float_argument(arguments, 0, registers)?)?;
                let right = expect_f32(float_argument(arguments, 1, registers)?)?;
                let value = match operation {
                    FloatBinaryOp::Add => left + right,
                    FloatBinaryOp::Sub => left - right,
                    FloatBinaryOp::Mul => left * right,
                    FloatBinaryOp::Div => left / right,
                    FloatBinaryOp::Rem => left % right,
                };
                Ok(VmValue::F32(canonical_vm_f32(value)))
            }
            FloatWidth::F64 => {
                let left = expect_f64(float_argument(arguments, 0, registers)?)?;
                let right = expect_f64(float_argument(arguments, 1, registers)?)?;
                let value = match operation {
                    FloatBinaryOp::Add => left + right,
                    FloatBinaryOp::Sub => left - right,
                    FloatBinaryOp::Mul => left * right,
                    FloatBinaryOp::Div => left / right,
                    FloatBinaryOp::Rem => left % right,
                };
                Ok(VmValue::F64(canonical_vm_f64(value)))
            }
        },
        FloatPrimitive::Neg { width } => match width {
            FloatWidth::F32 => Ok(VmValue::F32(canonical_vm_f32(-expect_f32(
                float_argument(arguments, 0, registers)?,
            )?))),
            FloatWidth::F64 => Ok(VmValue::F64(canonical_vm_f64(-expect_f64(
                float_argument(arguments, 0, registers)?,
            )?))),
        },
        FloatPrimitive::Compare { width, operation } => {
            let result = match width {
                FloatWidth::F32 => compare_f32_values(
                    expect_f32(float_argument(arguments, 0, registers)?)?,
                    expect_f32(float_argument(arguments, 1, registers)?)?,
                    operation,
                ),
                FloatWidth::F64 => compare_f64_values(
                    expect_f64(float_argument(arguments, 0, registers)?)?,
                    expect_f64(float_argument(arguments, 1, registers)?)?,
                    float_compare(operation),
                ),
            };
            Ok(VmValue::U32(u32::from(result)))
        }
        FloatPrimitive::Convert { from, to, checked } => {
            let value = float_argument(arguments, 0, registers)?;
            if matches!(to, ScalarType::F32 | ScalarType::F64) {
                return Ok(match to {
                    ScalarType::F32 => VmValue::F32(canonical_vm_f32(scalar_to_f32(value, from)?)),
                    ScalarType::F64 => VmValue::F64(canonical_vm_f64(scalar_to_f64(value, from)?)),
                    _ => unreachable!(),
                });
            }
            debug_assert!(checked);
            scalar_from_checked_float(scalar_to_f64(value, from)?, to)
        }
        FloatPrimitive::ToBits { width } => match width {
            FloatWidth::F32 => Ok(VmValue::U32(
                expect_f32(float_argument(arguments, 0, registers)?)?.to_bits(),
            )),
            FloatWidth::F64 => Ok(VmValue::U64(
                expect_f64(float_argument(arguments, 0, registers)?)?.to_bits(),
            )),
        },
        FloatPrimitive::FromBits { width } => match width {
            FloatWidth::F32 => Ok(VmValue::F32(canonical_vm_f32(f32::from_bits(expect_u32(
                float_argument(arguments, 0, registers)?,
            )?)))),
            FloatWidth::F64 => Ok(VmValue::F64(canonical_vm_f64(f64::from_bits(expect_u64(
                float_argument(arguments, 0, registers)?,
            )?)))),
        },
    }
}

fn integer_argument<'a>(
    arguments: &[u32],
    index: usize,
    registers: &'a [Option<VmValue>],
) -> Result<&'a VmValue, VmArtifactError> {
    let register = *arguments
        .get(index)
        .ok_or(VmArtifactError::MalformedEncoding {
            message: "integer runtime primitive has the wrong arity",
        })?;
    registers
        .get(register as usize)
        .and_then(Option::as_ref)
        .ok_or(VmArtifactError::ReadBeforeWrite { register })
}

macro_rules! execute_integer_binary {
    ($primitive:expr, $arguments:expr, $registers:expr, $expect:ident, $variant:ident) => {{
        let left = $expect(integer_argument($arguments, 0, $registers)?)?;
        let right = $expect(integer_argument($arguments, 1, $registers)?)?;
        let value = match $primitive {
            PrimitiveRole::IntCheckedAdd => left
                .checked_add(right)
                .ok_or(VmArtifactError::ArithmeticOverflow)?,
            PrimitiveRole::IntCheckedDiv => left
                .checked_div(right)
                .ok_or(VmArtifactError::ArithmeticOverflow)?,
            PrimitiveRole::IntWrappingAdd => left.wrapping_add(right),
            PrimitiveRole::IntWrappingSub => left.wrapping_sub(right),
            PrimitiveRole::IntWrappingMul => left.wrapping_mul(right),
            PrimitiveRole::IntBitAnd => left & right,
            PrimitiveRole::IntBitOr => left | right,
            PrimitiveRole::IntBitXor => left ^ right,
            _ => unreachable!("integer binary operation was validated"),
        };
        Ok(VmValue::$variant(value))
    }};
}

macro_rules! execute_integer_compare {
    ($primitive:expr, $arguments:expr, $registers:expr, $expect:ident) => {{
        let left = $expect(integer_argument($arguments, 0, $registers)?)?;
        let right = $expect(integer_argument($arguments, 1, $registers)?)?;
        let value = match $primitive {
            PrimitiveRole::IntEqual => left == right,
            PrimitiveRole::IntLess => left < right,
            PrimitiveRole::IntGreater => left > right,
            _ => unreachable!("integer comparison was validated"),
        };
        Ok(VmValue::U32(u32::from(value)))
    }};
}

macro_rules! execute_integer_unary {
    ($primitive:expr, $arguments:expr, $registers:expr, $expect:ident, $variant:ident) => {{
        let value = $expect(integer_argument($arguments, 0, $registers)?)?;
        let value = match $primitive {
            PrimitiveRole::IntBitNot => !value,
            PrimitiveRole::IntWrappingNeg => value.wrapping_neg(),
            _ => unreachable!("integer unary operation was validated"),
        };
        Ok(VmValue::$variant(value))
    }};
}

macro_rules! execute_integer_shift {
    ($primitive:expr, $arguments:expr, $registers:expr, $expect:ident, $variant:ident) => {{
        let value = $expect(integer_argument($arguments, 0, $registers)?)?;
        let count = expect_u32(integer_argument($arguments, 1, $registers)?)?;
        let value = match $primitive {
            PrimitiveRole::IntShl => value.wrapping_shl(count),
            PrimitiveRole::IntShr => value.wrapping_shr(count),
            _ => unreachable!("integer shift operation was validated"),
        };
        Ok(VmValue::$variant(value))
    }};
}

macro_rules! execute_integer_for_scalar {
    ($primitive:expr, $arguments:expr, $registers:expr, $expect:ident, $variant:ident) => {{
        match $primitive {
            PrimitiveRole::IntCheckedAdd
            | PrimitiveRole::IntCheckedDiv
            | PrimitiveRole::IntWrappingAdd
            | PrimitiveRole::IntWrappingSub
            | PrimitiveRole::IntWrappingMul
            | PrimitiveRole::IntBitAnd
            | PrimitiveRole::IntBitOr
            | PrimitiveRole::IntBitXor => {
                execute_integer_binary!($primitive, $arguments, $registers, $expect, $variant)
            }
            PrimitiveRole::IntEqual | PrimitiveRole::IntLess | PrimitiveRole::IntGreater => {
                execute_integer_compare!($primitive, $arguments, $registers, $expect)
            }
            PrimitiveRole::IntBitNot | PrimitiveRole::IntWrappingNeg => {
                execute_integer_unary!($primitive, $arguments, $registers, $expect, $variant)
            }
            PrimitiveRole::IntShl | PrimitiveRole::IntShr => {
                execute_integer_shift!($primitive, $arguments, $registers, $expect, $variant)
            }
            _ => unreachable!("integer intrinsic role was validated"),
        }
    }};
}

fn execute_integer_intrinsic(
    primitive: PrimitiveRole,
    scalar: ScalarType,
    arguments: &[u32],
    registers: &[Option<VmValue>],
) -> Result<VmValue, VmArtifactError> {
    let (parameters, _) = integer_intrinsic_signature(primitive, scalar)?;
    if arguments.len() != parameters.len() {
        return Err(VmArtifactError::MalformedEncoding {
            message: "integer runtime primitive has the wrong arity",
        });
    }
    if matches!(primitive, PrimitiveRole::IntShl | PrimitiveRole::IntShr) {
        let count = expect_u32(integer_argument(arguments, 1, registers)?)?;
        if count >= integer_scalar_bit_width(scalar) {
            return Err(VmArtifactError::ArithmeticOverflow);
        }
    }
    if matches!(
        primitive,
        PrimitiveRole::IntConvertCheckedToI64
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
    ) {
        let value = integer_argument(arguments, 0, registers)?;
        return integer_convert(primitive, scalar, value);
    }
    match scalar {
        ScalarType::U8 => {
            execute_integer_for_scalar!(primitive, arguments, registers, expect_u8, U8)
        }
        ScalarType::U16 => {
            execute_integer_for_scalar!(primitive, arguments, registers, expect_u16, U16)
        }
        ScalarType::U32 => {
            execute_integer_for_scalar!(primitive, arguments, registers, expect_u32, U32)
        }
        ScalarType::U64 => {
            execute_integer_for_scalar!(primitive, arguments, registers, expect_u64, U64)
        }
        ScalarType::U128 => {
            execute_integer_for_scalar!(primitive, arguments, registers, expect_u128, U128)
        }
        ScalarType::Usize => {
            execute_integer_for_scalar!(primitive, arguments, registers, expect_usize, Usize)
        }
        ScalarType::I8 => {
            execute_integer_for_scalar!(primitive, arguments, registers, expect_i8, I8)
        }
        ScalarType::I16 => {
            execute_integer_for_scalar!(primitive, arguments, registers, expect_i16, I16)
        }
        ScalarType::I32 => {
            execute_integer_for_scalar!(primitive, arguments, registers, expect_i32, I32)
        }
        ScalarType::I64 => {
            execute_integer_for_scalar!(primitive, arguments, registers, expect_i64, I64)
        }
        ScalarType::I128 => {
            execute_integer_for_scalar!(primitive, arguments, registers, expect_i128, I128)
        }
        ScalarType::Isize => {
            execute_integer_for_scalar!(primitive, arguments, registers, expect_isize, Isize)
        }
        _ => Err(VmArtifactError::MalformedEncoding {
            message: "integer runtime primitive has a non-integer scalar",
        }),
    }
}

fn integer_width(scalar: ScalarType) -> Option<u32> {
    Some(match scalar {
        ScalarType::U8 | ScalarType::I8 => 8,
        ScalarType::U16 | ScalarType::I16 => 16,
        ScalarType::U32 | ScalarType::I32 => 32,
        ScalarType::U64 | ScalarType::I64 | ScalarType::Usize | ScalarType::Isize => 64,
        ScalarType::U128 | ScalarType::I128 => 128,
        _ => return None,
    })
}

fn integer_is_signed(scalar: ScalarType) -> bool {
    matches!(
        scalar,
        ScalarType::I8
            | ScalarType::I16
            | ScalarType::I32
            | ScalarType::I64
            | ScalarType::I128
            | ScalarType::Isize
    )
}

fn integer_mask(scalar: ScalarType) -> Option<u128> {
    let width = integer_width(scalar)?;
    Some(if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    })
}

fn integer_bits(scalar: ScalarType, value: &VmValue) -> Result<u128, VmArtifactError> {
    Ok(match scalar {
        ScalarType::U8 => u128::from(expect_u8(value)?),
        ScalarType::U16 => u128::from(expect_u16(value)?),
        ScalarType::U32 => u128::from(expect_u32(value)?),
        ScalarType::U64 => u128::from(expect_u64(value)?),
        ScalarType::U128 => expect_u128(value)?,
        ScalarType::Usize => u128::from(expect_usize(value)?),
        ScalarType::I8 => expect_i8(value)? as u128,
        ScalarType::I16 => expect_i16(value)? as u128,
        ScalarType::I32 => expect_i32(value)? as u128,
        ScalarType::I64 => expect_i64(value)? as u128,
        ScalarType::I128 => expect_i128(value)? as u128,
        ScalarType::Isize => expect_isize(value)? as u128,
        _ => {
            return Err(VmArtifactError::MalformedEncoding {
                message: "integer runtime primitive has a non-integer argument",
            });
        }
    })
}

fn integer_signed(scalar: ScalarType, value: &VmValue) -> Result<i128, VmArtifactError> {
    Ok(match scalar {
        ScalarType::I8 => i128::from(expect_i8(value)?),
        ScalarType::I16 => i128::from(expect_i16(value)?),
        ScalarType::I32 => i128::from(expect_i32(value)?),
        ScalarType::I64 => i128::from(expect_i64(value)?),
        ScalarType::I128 => expect_i128(value)?,
        ScalarType::Isize => i128::from(expect_isize(value)?),
        _ => {
            return Err(VmArtifactError::MalformedEncoding {
                message: "integer runtime primitive expected a signed argument",
            });
        }
    })
}

fn integer_from_bits(scalar: ScalarType, bits: u128) -> Result<VmValue, VmArtifactError> {
    let bits = bits
        & integer_mask(scalar).ok_or(VmArtifactError::MalformedEncoding {
            message: "integer runtime primitive has a non-integer result",
        })?;
    Ok(match scalar {
        ScalarType::U8 => VmValue::U8(bits as u8),
        ScalarType::U16 => VmValue::U16(bits as u16),
        ScalarType::U32 => VmValue::U32(bits as u32),
        ScalarType::U64 => VmValue::U64(bits as u64),
        ScalarType::U128 => VmValue::U128(bits),
        ScalarType::Usize => VmValue::Usize(bits as u64),
        ScalarType::I8 => VmValue::I8(bits as i8),
        ScalarType::I16 => VmValue::I16(bits as i16),
        ScalarType::I32 => VmValue::I32(bits as i32),
        ScalarType::I64 => VmValue::I64(bits as i64),
        ScalarType::I128 => VmValue::I128(bits as i128),
        ScalarType::Isize => VmValue::Isize(bits as i64),
        _ => {
            return Err(VmArtifactError::MalformedEncoding {
                message: "integer runtime primitive has a non-integer result",
            });
        }
    })
}

fn integer_conversion_fits(
    source: ScalarType,
    target: ScalarType,
    value: &VmValue,
) -> Result<bool, VmArtifactError> {
    let target_width = integer_width(target).ok_or(VmArtifactError::MalformedEncoding {
        message: "integer conversion target is not an integer",
    })?;
    if integer_is_signed(source) {
        let value = integer_signed(source, value)?;
        if integer_is_signed(target) {
            let (minimum, maximum) = if target_width == 128 {
                (i128::MIN, i128::MAX)
            } else {
                (
                    -(1i128 << (target_width - 1)),
                    (1i128 << (target_width - 1)) - 1,
                )
            };
            Ok((minimum..=maximum).contains(&value))
        } else {
            Ok(value >= 0 && (value as u128) <= integer_mask(target).unwrap())
        }
    } else {
        let value = integer_bits(source, value)?;
        if integer_is_signed(target) {
            let maximum = if target_width == 128 {
                i128::MAX as u128
            } else {
                (1u128 << (target_width - 1)) - 1
            };
            Ok(value <= maximum)
        } else {
            Ok(value <= integer_mask(target).unwrap())
        }
    }
}

fn integer_convert(
    primitive: PrimitiveRole,
    source: ScalarType,
    value: &VmValue,
) -> Result<VmValue, VmArtifactError> {
    let (_, target) = integer_intrinsic_signature(primitive, source)?;
    let checked = matches!(
        primitive,
        PrimitiveRole::IntConvertCheckedToI64
            | PrimitiveRole::IntConvertCheckedToU32
            | PrimitiveRole::IntConvertCheckedToUsize
            | PrimitiveRole::IntConvertCheckedToU8
            | PrimitiveRole::IntConvertCheckedToU16
            | PrimitiveRole::IntConvertCheckedToI16
            | PrimitiveRole::IntConvertCheckedToI32
            | PrimitiveRole::IntConvertCheckedToI8
            | PrimitiveRole::IntConvertCheckedToU64
            | PrimitiveRole::IntConvertCheckedToIsize
            | PrimitiveRole::IntConvertCheckedToU128
            | PrimitiveRole::IntConvertCheckedToI128
    );
    if checked && !integer_conversion_fits(source, target, value)? {
        return Err(VmArtifactError::ArithmeticOverflow);
    }
    integer_from_bits(target, integer_bits(source, value)?)
}

fn float_compare(operation: FloatCompareOp) -> VmCompare {
    match operation {
        FloatCompareOp::Eq => VmCompare::Equal,
        FloatCompareOp::Ne => VmCompare::NotEqual,
        FloatCompareOp::Lt => VmCompare::Less,
        FloatCompareOp::Le => VmCompare::LessEqual,
        FloatCompareOp::Gt => VmCompare::Greater,
        FloatCompareOp::Ge => VmCompare::GreaterEqual,
    }
}

fn compare_f32_values(left: f32, right: f32, operation: FloatCompareOp) -> bool {
    match operation {
        FloatCompareOp::Eq => left == right,
        FloatCompareOp::Ne => left != right,
        FloatCompareOp::Lt => left < right,
        FloatCompareOp::Le => left <= right,
        FloatCompareOp::Gt => left > right,
        FloatCompareOp::Ge => left >= right,
    }
}

// Convert directly at the requested precision. Routing wide integers through
// f64 before f32 can double-round at a halfway point.
fn scalar_to_f32(value: &VmValue, scalar: ScalarType) -> Result<f32, VmArtifactError> {
    Ok(match scalar {
        ScalarType::F32 => expect_f32(value)?,
        ScalarType::F64 => expect_f64(value)? as f32,
        ScalarType::U8 => expect_u8(value)? as f32,
        ScalarType::U16 => expect_u16(value)? as f32,
        ScalarType::U32 => expect_u32(value)? as f32,
        ScalarType::U64 => expect_u64(value)? as f32,
        ScalarType::U128 => expect_u128(value)? as f32,
        ScalarType::Usize => expect_usize(value)? as f32,
        ScalarType::I8 => expect_i8(value)? as f32,
        ScalarType::I16 => expect_i16(value)? as f32,
        ScalarType::I32 => expect_i32(value)? as f32,
        ScalarType::I64 => expect_i64(value)? as f32,
        ScalarType::I128 => expect_i128(value)? as f32,
        ScalarType::Isize => expect_isize(value)? as f32,
        _ => {
            return Err(VmArtifactError::MalformedEncoding {
                message: "non-numeric floating conversion",
            });
        }
    })
}

fn scalar_to_f64(value: &VmValue, scalar: ScalarType) -> Result<f64, VmArtifactError> {
    Ok(match scalar {
        ScalarType::F32 => expect_f32(value)? as f64,
        ScalarType::F64 => expect_f64(value)?,
        ScalarType::U8 => expect_u8(value)? as f64,
        ScalarType::U16 => expect_u16(value)? as f64,
        ScalarType::U32 => expect_u32(value)? as f64,
        ScalarType::U64 => expect_u64(value)? as f64,
        ScalarType::U128 => expect_u128(value)? as f64,
        ScalarType::Usize => expect_usize(value)? as f64,
        ScalarType::I8 => expect_i8(value)? as f64,
        ScalarType::I16 => expect_i16(value)? as f64,
        ScalarType::I32 => expect_i32(value)? as f64,
        ScalarType::I64 => expect_i64(value)? as f64,
        ScalarType::I128 => expect_i128(value)? as f64,
        ScalarType::Isize => expect_isize(value)? as f64,
        _ => {
            return Err(VmArtifactError::MalformedEncoding {
                message: "non-numeric floating conversion",
            });
        }
    })
}

fn scalar_from_checked_float(value: f64, target: ScalarType) -> Result<VmValue, VmArtifactError> {
    let (lower, upper) = match target {
        ScalarType::U8 => (0.0, 256.0),
        ScalarType::U16 => (0.0, 65536.0),
        ScalarType::U32 => (0.0, 4_294_967_296.0),
        ScalarType::U64 | ScalarType::Usize => (0.0, 18_446_744_073_709_551_616.0),
        ScalarType::U128 => (0.0, 340_282_366_920_938_463_463_374_607_431_768_211_456.0),
        ScalarType::I8 => (-128.0, 128.0),
        ScalarType::I16 => (-32768.0, 32768.0),
        ScalarType::I32 => (-2_147_483_648.0, 2_147_483_648.0),
        ScalarType::I64 | ScalarType::Isize => {
            (-9_223_372_036_854_775_808.0, 9_223_372_036_854_775_808.0)
        }
        ScalarType::I128 => (
            -170_141_183_460_469_231_731_687_303_715_884_105_728.0,
            170_141_183_460_469_231_731_687_303_715_884_105_728.0,
        ),
        _ => {
            return Err(VmArtifactError::MalformedEncoding {
                message: "invalid checked float conversion target",
            });
        }
    };
    if !value.is_finite() || value < lower || value >= upper {
        return Err(VmArtifactError::Trap);
    }
    Ok(match target {
        ScalarType::U8 => VmValue::U8(value as u8),
        ScalarType::U16 => VmValue::U16(value as u16),
        ScalarType::U32 => VmValue::U32(value as u32),
        ScalarType::U64 => VmValue::U64(value as u64),
        ScalarType::U128 => VmValue::U128(value as u128),
        ScalarType::Usize => VmValue::Usize(value as u64),
        ScalarType::I8 => VmValue::I8(value as i8),
        ScalarType::I16 => VmValue::I16(value as i16),
        ScalarType::I32 => VmValue::I32(value as i32),
        ScalarType::I64 => VmValue::I64(value as i64),
        ScalarType::I128 => VmValue::I128(value as i128),
        ScalarType::Isize => VmValue::Isize(value as i64),
        _ => unreachable!(),
    })
}

fn expect_bool(value: impl Borrow<VmValue>) -> Result<bool, VmArtifactError> {
    match value.borrow() {
        VmValue::Bool(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Bool,
            found: value.ty(),
        }),
    }
}
fn expect_char(value: impl Borrow<VmValue>) -> Result<char, VmArtifactError> {
    match value.borrow() {
        VmValue::Char(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Char,
            found: value.ty(),
        }),
    }
}
fn expect_text(value: impl Borrow<VmValue>) -> Result<Arc<str>, VmArtifactError> {
    match value.borrow() {
        VmValue::Text(value) => Ok(value.clone()),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Text,
            found: value.ty(),
        }),
    }
}
fn expect_static_utf8(
    value: impl Borrow<VmValue>,
) -> Result<(Arc<[u8]>, usize, usize), VmArtifactError> {
    match value.borrow() {
        VmValue::StaticData {
            tag: crate::STATIC_UTF8_DATA_TAG | crate::STATIC_RAW_U8_DATA_TAG,
            alignment: 1,
            bytes,
            offset,
            length,
        } => Ok((bytes.clone(), *offset, *length)),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::StaticData {
                element: Box::new(VmType::U8),
                tag: 0x4752_414e_4449_4f53_455f_5354_4154_4943,
                alignment: 1,
            },
            found: value.ty(),
        }),
    }
}
fn compare_i64_values(left: i64, right: i64, op: VmCompare) -> bool {
    match op {
        VmCompare::Equal => left == right,
        VmCompare::NotEqual => left != right,
        VmCompare::Less => left < right,
        VmCompare::LessEqual => left <= right,
        VmCompare::Greater => left > right,
        VmCompare::GreaterEqual => left >= right,
    }
}
fn compare_u32_values(left: u32, right: u32, op: VmCompare) -> bool {
    match op {
        VmCompare::Equal => left == right,
        VmCompare::NotEqual => left != right,
        VmCompare::Less => left < right,
        VmCompare::LessEqual => left <= right,
        VmCompare::Greater => left > right,
        VmCompare::GreaterEqual => left >= right,
    }
}
fn compare_u64_values(left: u64, right: u64, op: VmCompare) -> bool {
    match op {
        VmCompare::Equal => left == right,
        VmCompare::NotEqual => left != right,
        VmCompare::Less => left < right,
        VmCompare::LessEqual => left <= right,
        VmCompare::Greater => left > right,
        VmCompare::GreaterEqual => left >= right,
    }
}
fn compare_f64_values(left: f64, right: f64, op: VmCompare) -> bool {
    match op {
        VmCompare::Equal => left == right,
        VmCompare::NotEqual => left != right,
        VmCompare::Less => left < right,
        VmCompare::LessEqual => left <= right,
        VmCompare::Greater => left > right,
        VmCompare::GreaterEqual => left >= right,
    }
}
fn compare_char_values(left: char, right: char, op: VmCompare) -> bool {
    match op {
        VmCompare::Equal => left == right,
        VmCompare::NotEqual => left != right,
        VmCompare::Less => left < right,
        VmCompare::LessEqual => left <= right,
        VmCompare::Greater => left > right,
        VmCompare::GreaterEqual => left >= right,
    }
}
fn matches_pattern(value: &VmValue, pattern: &VmPattern) -> bool {
    match pattern {
        VmPattern::Any => true,
        VmPattern::Literal(literal) => literal_matches(value, literal),
        VmPattern::Tuple(patterns) => match value {
            VmValue::Tuple(values) if values.len() == patterns.len() => values
                .iter()
                .zip(patterns)
                .all(|(value, pattern)| matches_pattern(value, pattern)),
            _ => false,
        },
        VmPattern::Array { element, elements } => match value {
            VmValue::Array { values, .. }
                if values.len() == elements.len()
                    && values
                        .iter()
                        .all(|value| value_matches_vm_type(value, element)) =>
            {
                values
                    .iter()
                    .zip(elements)
                    .all(|(value, pattern)| matches_pattern(value, pattern))
            }
            _ => false,
        },
        VmPattern::Record {
            definition,
            field_types,
            field_count,
            fields,
        } => match value {
            VmValue::Record {
                definition: actual,
                fields: values,
                ..
            } if actual == definition
                && values.len() == *field_count as usize
                && aggregate_matches_layout(values, field_types) =>
            {
                matches_pattern_fields(values, fields)
            }
            _ => false,
        },
        VmPattern::Enum {
            definition,
            variant,
            field_types,
            field_count,
            fields,
        } => match value {
            VmValue::Enum {
                definition: actual,
                variant: actual_variant,
                fields: values,
                ..
            } if actual == definition
                && actual_variant == variant
                && values.len() == *field_count as usize
                && aggregate_matches_layout(values, field_types) =>
            {
                matches_pattern_fields(values, fields)
            }
            _ => false,
        },
    }
}
fn matches_pattern_fields(values: &[VmValue], fields: &[VmPatternField]) -> bool {
    fields.iter().all(|field| {
        values.get(field.index as usize).is_some_and(|value| {
            value_matches_vm_type(value, &field.ty) && matches_pattern(value, &field.pattern)
        })
    })
}

/// Runtime rechecks the frozen layout against the constructed aggregate. This
/// means an artifact cannot change a selected field's metadata while leaving
/// its pattern as `Any` and gain a silently different match behavior.
fn aggregate_matches_layout(values: &[VmValue], field_types: &[VmType]) -> bool {
    values.len() == field_types.len()
        && values
            .iter()
            .zip(field_types)
            .all(|(value, ty)| value_matches_vm_type(value, ty))
}

/// A VM generic is a declaration-local wildcard at runtime; every other
/// structural component must agree exactly with the value's concrete shape.
fn value_matches_vm_type(value: &VmValue, expected: &VmType) -> bool {
    match expected {
        VmType::Generic(_) => true,
        // Structural constants inhabit nominal identity only; no standalone
        // runtime value may claim one of these metadata-only layouts.
        VmType::ConstU32(_)
        | VmType::ConstU32Expr(_)
        | VmType::ConstQuantity { .. }
        | VmType::ConstGeneric { .. } => false,
        VmType::Unit => matches!(value, VmValue::Unit),
        VmType::I64 => matches!(value, VmValue::I64(_)),
        VmType::Usize => matches!(value, VmValue::Usize(_)),
        VmType::U32 => matches!(value, VmValue::U32(_)),
        VmType::U8 => matches!(value, VmValue::U8(_)),
        VmType::U16 => matches!(value, VmValue::U16(_)),
        VmType::I16 => matches!(value, VmValue::I16(_)),
        VmType::I32 => matches!(value, VmValue::I32(_)),
        VmType::I8 => matches!(value, VmValue::I8(_)),
        VmType::U64 => matches!(value, VmValue::U64(_)),
        VmType::Isize => matches!(value, VmValue::Isize(_)),
        VmType::U128 => matches!(value, VmValue::U128(_)),
        VmType::I128 => matches!(value, VmValue::I128(_)),
        VmType::F32 => matches!(value, VmValue::F32(_)),
        VmType::F64 => matches!(value, VmValue::F64(_)),
        VmType::Bool => matches!(value, VmValue::Bool(_)),
        VmType::Char => matches!(value, VmValue::Char(_)),
        VmType::Text => matches!(value, VmValue::Text(_)),
        VmType::Bytes => matches!(value, VmValue::Bytes(_)),
        VmType::StaticData {
            element,
            tag,
            alignment,
        } => matches!(value, VmValue::StaticData {
            tag: value_tag,
            alignment: value_alignment,
            ..
        } if element.as_ref() == &VmType::U8 && tag == value_tag && alignment == value_alignment),
        VmType::Tuple(expected) => {
            matches!(value, VmValue::Tuple(values) if values.len() == expected.len() && values.iter().zip(expected).all(|(value, ty)| value_matches_vm_type(value, ty)))
        }
        VmType::Array(expected) => {
            matches!(value, VmValue::Array { values, .. } if values.iter().all(|value| value_matches_vm_type(value, expected)))
        }
        VmType::Nominal {
            definition,
            arguments,
        } => {
            matches!(value, VmValue::Record { definition: actual, signature: VmType::Nominal { definition: signature_definition, arguments: actual_arguments }, .. } | VmValue::Enum { definition: actual, signature: VmType::Nominal { definition: signature_definition, arguments: actual_arguments }, .. } if actual == definition && signature_definition == definition && actual_arguments.len() == arguments.len() && actual_arguments.iter().zip(arguments).all(|(actual, expected)| vm_type_matches(actual, expected)))
        }
        VmType::Callable {
            safety,
            parameters,
            result,
            effects,
        } => {
            matches!(value, VmValue::Callable { signature: VmType::Callable { safety: actual_safety, parameters: actual_parameters, result: actual_result, effects: actual_effects }, .. } if actual_safety == safety && actual_parameters.len() == parameters.len() && actual_parameters.iter().zip(parameters).all(|(actual, expected)| vm_type_matches(actual, expected)) && vm_type_matches(actual_result, result) && vm_effect_row_matches(actual_effects, effects))
        }
        VmType::RawPointer { .. } => matches!(value, VmValue::RawPointer { signature, .. } if vm_type_matches(signature, expected)),
        VmType::Reference { unique, referent } => {
            matches!(value, VmValue::Reference { unique: actual_unique, referent: actual_referent, .. } if actual_unique == unique && vm_type_matches(actual_referent, referent))
        }
    }
}

fn vm_type_matches(actual: &VmType, expected: &VmType) -> bool {
    match expected {
        VmType::Generic(_) => true,
        VmType::Array(expected) => {
            matches!(actual, VmType::Array(actual) if vm_type_matches(actual, expected))
        }
        VmType::StaticData {
            element: expected_element,
            tag: expected_tag,
            alignment: expected_alignment,
        } => matches!(actual, VmType::StaticData {
            element: actual_element,
            tag: actual_tag,
            alignment: actual_alignment,
        } if actual_tag == expected_tag
            && actual_alignment == expected_alignment
            && vm_type_matches(actual_element, expected_element)),
        VmType::Tuple(expected) => {
            matches!(actual, VmType::Tuple(actual) if actual.len() == expected.len() && actual.iter().zip(expected).all(|(actual, expected)| vm_type_matches(actual, expected)))
        }
        VmType::Nominal {
            definition,
            arguments,
        } => {
            matches!(actual, VmType::Nominal { definition: actual_definition, arguments: actual_arguments } if actual_definition == definition && actual_arguments.len() == arguments.len() && actual_arguments.iter().zip(arguments).all(|(actual, expected)| vm_type_matches(actual, expected)))
        }
        VmType::Callable {
            safety,
            parameters,
            result,
            effects,
        } => {
            matches!(actual, VmType::Callable { safety: actual_safety, parameters: actual_parameters, result: actual_result, effects: actual_effects } if actual_safety == safety && actual_parameters.len() == parameters.len() && actual_parameters.iter().zip(parameters).all(|(actual, expected)| vm_type_matches(actual, expected)) && vm_type_matches(actual_result, result) && vm_effect_row_matches(actual_effects, effects))
        }
        VmType::RawPointer { mutability, pointee } => matches!(actual,
            VmType::RawPointer { mutability: actual_mutability, pointee: actual_pointee }
                if actual_mutability == mutability && vm_type_matches(actual_pointee, pointee)),
        VmType::Reference { unique, referent } => {
            matches!(actual, VmType::Reference { unique: actual_unique, referent: actual_referent } if actual_unique == unique && vm_type_matches(actual_referent, referent))
        }
        _ => actual == expected,
    }
}

fn vm_effect_row_matches(actual: &VmEffectRow, expected: &VmEffectRow) -> bool {
    actual.tail == expected.tail
        && actual.effects.len() == expected.effects.len()
        && actual.projections.len() == expected.projections.len()
        && actual
            .effects
            .iter()
            .zip(&expected.effects)
            .all(|(actual, expected)| {
                actual.definition == expected.definition
                    && actual.arguments.len() == expected.arguments.len()
                    && actual
                        .arguments
                        .iter()
                        .zip(&expected.arguments)
                        .all(|(actual, expected)| vm_generic_argument_matches(actual, expected))
            })
        && actual
            .projections
            .iter()
            .zip(&expected.projections)
            .all(|(actual, expected)| {
                vm_type_matches(&actual.subject, &expected.subject)
                    && actual.trait_definition == expected.trait_definition
                    && actual.name == expected.name
                    && actual.trait_arguments.len() == expected.trait_arguments.len()
                    && actual.item_arguments.len() == expected.item_arguments.len()
                    && actual
                        .trait_arguments
                        .iter()
                        .zip(&expected.trait_arguments)
                        .all(|(actual, expected)| vm_generic_argument_matches(actual, expected))
                    && actual
                        .item_arguments
                        .iter()
                        .zip(&expected.item_arguments)
                        .all(|(actual, expected)| vm_generic_argument_matches(actual, expected))
            })
}

fn vm_generic_argument_matches(actual: &VmGenericArgument, expected: &VmGenericArgument) -> bool {
    match (actual, expected) {
        (VmGenericArgument::Type(actual), VmGenericArgument::Type(expected)) => {
            vm_type_matches(actual, expected)
        }
        (VmGenericArgument::EffectRow(actual), VmGenericArgument::EffectRow(expected)) => {
            vm_effect_row_matches(actual, expected)
        }
        _ => actual == expected,
    }
}
fn literal_matches(value: &VmValue, literal: &str) -> bool {
    match value {
        VmValue::Bool(value) => matches!((literal, value), ("true", true) | ("false", false)),
        VmValue::I64(value) => parse_pattern_i64(literal).is_some_and(|literal| literal == *value),
        VmValue::U8(value) => parse_pattern_u64(literal).is_some_and(|literal| literal == u64::from(*value)),
        VmValue::U16(value) => parse_pattern_u64(literal).is_some_and(|literal| literal == u64::from(*value)),
        VmValue::U32(value) => parse_pattern_u64(literal).is_some_and(|literal| literal == u64::from(*value)),
        VmValue::U64(value) | VmValue::Usize(value) => parse_pattern_u64(literal).is_some_and(|literal| literal == *value),
        VmValue::U128(value) => parse_pattern_u128(literal).is_some_and(|literal| literal == *value),
        VmValue::I8(value) => parse_pattern_i64(literal).is_some_and(|literal| literal == i64::from(*value)),
        VmValue::I16(value) => parse_pattern_i64(literal).is_some_and(|literal| literal == i64::from(*value)),
        VmValue::I32(value) => parse_pattern_i64(literal).is_some_and(|literal| literal == i64::from(*value)),
        VmValue::Isize(value) => parse_pattern_i64(literal).is_some_and(|literal| literal == *value),
        VmValue::I128(value) => parse_pattern_i128(literal).is_some_and(|literal| literal == *value),
        VmValue::F64(value) => parse_pattern_f64(literal).is_some_and(|literal| literal == *value),
        VmValue::F32(value) => {
            parse_pattern_f64(literal).is_some_and(|literal| literal as f32 == *value)
        }
        VmValue::Char(value) => {
            parse_pattern_char(literal).is_some_and(|literal| literal == *value)
        }
        VmValue::Text(value) => {
            parse_pattern_text(literal).is_some_and(|literal| literal == value.as_ref())
        }
        _ => false,
    }
}
fn parse_pattern_i64(text: &str) -> Option<i64> {
    let digits = text.replace('_', "");
    let (radix, digits) = if let Some(value) = digits.strip_prefix("0b") {
        (2, value)
    } else if let Some(value) = digits.strip_prefix("0o") {
        (8, value)
    } else if let Some(value) = digits.strip_prefix("0x") {
        (16, value)
    } else {
        (10, digits.as_str())
    };
    i64::from_str_radix(digits, radix).ok()
}
fn parse_pattern_u64(text: &str) -> Option<u64> {
    let digits = text.replace('_', "");
    let (radix, digits) = if let Some(value) = digits.strip_prefix("0b") {
        (2, value)
    } else if let Some(value) = digits.strip_prefix("0o") {
        (8, value)
    } else if let Some(value) = digits.strip_prefix("0x") {
        (16, value)
    } else {
        (10, digits.as_str())
    };
    u64::from_str_radix(digits, radix).ok()
}
fn parse_pattern_u128(text: &str) -> Option<u128> {
    let digits = text.replace('_', "");
    let (radix, digits) = if let Some(value) = digits.strip_prefix("0b") {
        (2, value)
    } else if let Some(value) = digits.strip_prefix("0o") {
        (8, value)
    } else if let Some(value) = digits.strip_prefix("0x") {
        (16, value)
    } else {
        (10, digits.as_str())
    };
    u128::from_str_radix(digits, radix).ok()
}
fn parse_pattern_i128(text: &str) -> Option<i128> {
    let digits = text.replace('_', "");
    let (radix, digits) = if let Some(value) = digits.strip_prefix("0b") {
        (2, value)
    } else if let Some(value) = digits.strip_prefix("0o") {
        (8, value)
    } else if let Some(value) = digits.strip_prefix("0x") {
        (16, value)
    } else {
        (10, digits.as_str())
    };
    i128::from_str_radix(digits, radix).ok()
}
fn parse_pattern_f64(text: &str) -> Option<f64> {
    parse_f64_literal(text).ok()
}
fn parse_pattern_char(text: &str) -> Option<char> {
    char::from_u32(parse_char_literal(text).ok()?)
}
fn valid_utf8_prefix(bytes: &[u8]) -> usize {
    for end in (0..=bytes.len()).rev() {
        if std::str::from_utf8(&bytes[..end]).is_ok() {
            return end;
        }
    }
    0
}

fn u32_checked_binary(
    registers: &mut [Option<VmValue>],
    dst: u32,
    left: u32,
    right: u32,
    operation: impl FnOnce(u32, u32) -> Option<u32>,
) -> Result<(), VmArtifactError> {
    let left = expect_u32(
        registers[left as usize]
            .as_ref()
            .expect("verified register"),
    )?;
    let right = expect_u32(
        registers[right as usize]
            .as_ref()
            .expect("verified register"),
    )?;
    let value = operation(left, right).ok_or(VmArtifactError::ArithmeticOverflow)?;
    registers[dst as usize] = Some(VmValue::U32(value));
    Ok(())
}

fn u32_wrapping_binary(
    registers: &mut [Option<VmValue>],
    dst: u32,
    left: u32,
    right: u32,
    operation: impl FnOnce(u32, u32) -> u32,
) -> Result<(), VmArtifactError> {
    let left = expect_u32(
        registers[left as usize]
            .as_ref()
            .expect("verified register"),
    )?;
    let right = expect_u32(
        registers[right as usize]
            .as_ref()
            .expect("verified register"),
    )?;
    registers[dst as usize] = Some(VmValue::U32(operation(left, right)));
    Ok(())
}

fn u32_checked_division(
    registers: &mut [Option<VmValue>],
    dst: u32,
    left: u32,
    right: u32,
    remainder: bool,
) -> Result<(), VmArtifactError> {
    let left = expect_u32(
        registers[left as usize]
            .as_ref()
            .expect("verified register"),
    )?;
    let right = expect_u32(
        registers[right as usize]
            .as_ref()
            .expect("verified register"),
    )?;
    if right == 0 {
        return Err(VmArtifactError::DivisionByZero);
    }
    let value = if remainder {
        left % right
    } else {
        left / right
    };
    registers[dst as usize] = Some(VmValue::U32(value));
    Ok(())
}

fn u32_compare(
    registers: &mut [Option<VmValue>],
    dst: u32,
    left: u32,
    right: u32,
    operation: impl FnOnce(u32, u32) -> bool,
) -> Result<(), VmArtifactError> {
    let left = expect_u32(
        registers[left as usize]
            .as_ref()
            .expect("verified register"),
    )?;
    let right = expect_u32(
        registers[right as usize]
            .as_ref()
            .expect("verified register"),
    )?;
    registers[dst as usize] = Some(VmValue::Bool(operation(left, right)));
    Ok(())
}
fn parse_pattern_text(text: &str) -> Option<String> {
    parse_text_literal(text).ok()
}
/// Execute a standalone artifact under the same step and call-entry budget as
/// a program. Standalone artifacts cannot contain calls, but a zero call-depth
/// ceiling still rejects their root invocation deterministically.
fn execute(
    function: &VmFunction,
    budget: &mut ExecutionBudget,
) -> Result<VmValue, VmArtifactError> {
    require_execution_contract(function, budget)?;
    if budget.limits.max_call_depth == 0 {
        return Err(VmArtifactError::CallDepthLimit {
            limit: budget.limits.max_call_depth,
        });
    }
    budget.reserve_allocation(function.registers.len())?;
    let mut registers = vec![None; function.registers.len()];
    let mut handlers = Vec::<RuntimeHandlerFrame>::new();
    let mut resumption_returns = Vec::<RuntimeResumptionReturn>::new();
    let mut next_handler_id = 0u64;
    let mut pc = 0usize;
    while let Some(instruction) = function.instructions.get(pc).cloned() {
        budget.tick()?;
        match instruction {
            VmInstruction::DeclareResult { .. } => {}
            VmInstruction::ConstUnit { dst } => registers[dst as usize] = Some(VmValue::Unit),
            VmInstruction::MemoryIntrinsic { dst, primitive, types, arguments } => {
                registers[dst as usize] = Some(execute_memory_intrinsic(primitive, &types, &arguments, function, &mut registers, budget)?);
            }
            VmInstruction::ConstI64 { dst, value } => {
                registers[dst as usize] = Some(VmValue::I64(value))
            }
            VmInstruction::ConstU8 { dst, value } => {
                registers[dst as usize] = Some(VmValue::U8(value))
            }
            VmInstruction::ConstU16 { dst, value } => {
                registers[dst as usize] = Some(VmValue::U16(value))
            }
            VmInstruction::ConstU32 { dst, value } => {
                registers[dst as usize] = Some(VmValue::U32(value))
            }
            VmInstruction::ConstU64 { dst, value } => {
                registers[dst as usize] = Some(VmValue::U64(value))
            }
            VmInstruction::ConstUsize { dst, value } => {
                registers[dst as usize] = Some(VmValue::Usize(value))
            }
            VmInstruction::ConstU128 { dst, value } => {
                registers[dst as usize] = Some(VmValue::U128(value))
            }
            VmInstruction::ConstI8 { dst, value } => {
                registers[dst as usize] = Some(VmValue::I8(value))
            }
            VmInstruction::ConstI16 { dst, value } => {
                registers[dst as usize] = Some(VmValue::I16(value))
            }
            VmInstruction::ConstI32 { dst, value } => {
                registers[dst as usize] = Some(VmValue::I32(value))
            }
            VmInstruction::ConstIsize { dst, value } => {
                registers[dst as usize] = Some(VmValue::Isize(value))
            }
            VmInstruction::ConstI128 { dst, value } => {
                registers[dst as usize] = Some(VmValue::I128(value))
            }
            VmInstruction::ConstF64 { dst, bits } => {
                registers[dst as usize] = Some(VmValue::F64(canonical_vm_f64(f64::from_bits(bits))))
            }
            VmInstruction::ConstF32 { dst, bits } => {
                registers[dst as usize] = Some(VmValue::F32(canonical_vm_f32(f32::from_bits(bits))))
            }
            VmInstruction::FloatIntrinsic {
                dst,
                primitive,
                arguments,
            } => {
                registers[dst as usize] =
                    Some(execute_float_intrinsic(primitive, &arguments, &registers)?)
            }
            VmInstruction::IntIntrinsic {
                dst,
                primitive,
                scalar,
                arguments,
            } => {
                registers[dst as usize] = Some(execute_integer_intrinsic(
                    primitive, scalar, &arguments, &registers,
                )?)
            }
            VmInstruction::ConstBool { dst, value } => {
                registers[dst as usize] = Some(VmValue::Bool(value))
            }
            VmInstruction::ConstChar { dst, value } => {
                registers[dst as usize] =
                    Some(VmValue::Char(char::from_u32(value).expect("verified char")))
            }
            VmInstruction::ConstText { dst, value } => {
                budget.reserve_value("text bytes", value.len())?;
                registers[dst as usize] = Some(VmValue::Text(Arc::from(value)));
            }
            VmInstruction::ConstStaticData {
                dst,
                tag,
                alignment,
                bytes,
            } => {
                budget.reserve_value("static-data bytes", bytes.len())?;
                let length = bytes.len();
                registers[dst as usize] = Some(VmValue::StaticData {
                    tag,
                    alignment,
                    bytes: Arc::from(bytes),
                    offset: 0,
                    length,
                });
            }
            VmInstruction::StaticLen { dst, value } => {
                let (_, _, length) = expect_static_utf8(
                    registers[value as usize].as_ref().expect("verified register"),
                )?;
                registers[dst as usize] = Some(VmValue::Usize(length as u64));
            }
            VmInstruction::StaticSubslice { dst, value, start, length } => {
                let (bytes, offset, available) = expect_static_utf8(
                    registers[value as usize].as_ref().expect("verified register"),
                )?;
                let start = expect_usize(registers[start as usize].as_ref().expect("verified register"))? as usize;
                let length = expect_usize(registers[length as usize].as_ref().expect("verified register"))? as usize;
                let end = start.checked_add(length).filter(|end| *end <= available)
                    .ok_or(VmArtifactError::InvalidRegister { register: start as u32 })?;
                registers[dst as usize] = Some(VmValue::StaticData {
                    tag: 0x4752_414e_4449_4f53_455f_5354_4154_4943,
                    alignment: 1,
                    bytes,
                    offset: offset + start,
                    length: end - start,
                });
            }
            VmInstruction::StaticGetBorrowShared { dst, value, index } => {
                let (bytes, offset, length) = expect_static_utf8(
                    registers[value as usize].as_ref().expect("verified register"),
                )?;
                let index = expect_usize(registers[index as usize].as_ref().expect("verified register"))? as usize;
                let byte = *bytes.get(offset.checked_add(index).filter(|_| index < length).ok_or(
                    VmArtifactError::InvalidRegister { register: index as u32 },
                )?).ok_or(VmArtifactError::InvalidRegister { register: index as u32 })?;
                registers[dst as usize] = Some(VmValue::Reference {
                    target: ReferenceTarget::Captured(Arc::new(VmValue::U8(byte))),
                    fields: Arc::from([]),
                    unique: false,
                    referent: VmType::U8,
                });
            }
            VmInstruction::StaticAsArrayBorrow { dst, value } => {
                let (bytes, offset, length) = expect_static_utf8(registers[value as usize].as_ref().expect("verified register"))?;
                registers[dst as usize] = Some(VmValue::Reference { target: ReferenceTarget::Captured(Arc::new(VmValue::StaticArray { bytes, offset, length })), fields: Arc::from([]), unique: false, referent: VmType::Array(Box::new(VmType::U8)) });
            }
            VmInstruction::TextByteLen { dst, value } => {
                let text = expect_text(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                registers[dst as usize] = Some(VmValue::Usize(text.len() as u64));
            }
            VmInstruction::TextConcat { dst, left, right } => {
                let left = expect_text(
                    registers[left as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let right = expect_text(
                    registers[right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let length = left.len().checked_add(right.len()).ok_or(
                    VmArtifactError::AllocationLimit {
                        limit: budget.limits.max_allocation_elements,
                    },
                )?;
                budget.reserve_value("text bytes", length)?;
                registers[dst as usize] = Some(VmValue::Text(Arc::from(format!("{left}{right}"))));
            }
            VmInstruction::TextEq { dst, left, right } => {
                let left = expect_text(
                    registers[left as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let right = expect_text(
                    registers[right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                registers[dst as usize] = Some(VmValue::U32(u32::from(left == right)));
            }
            VmInstruction::TextFromUtf8Checked { dst, value } => {
                let bytes = expect_bytes(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                budget.reserve_value("text bytes", bytes.len())?;
                let text =
                    String::from_utf8(bytes.to_vec()).map_err(|_| VmArtifactError::InvalidUtf8)?;
                registers[dst as usize] = Some(VmValue::Text(Arc::from(text)));
            }
            VmInstruction::TextAsBytes { dst, value } => {
                let text = expect_text(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                budget.reserve_value("bytes", text.len())?;
                registers[dst as usize] = Some(VmValue::Bytes(Arc::from(text.as_bytes())));
            }
            VmInstruction::CharFromU32Checked { dst, value } => {
                let value = expect_u32(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let character =
                    char::from_u32(value).ok_or(VmArtifactError::InvalidChar { value })?;
                registers[dst as usize] = Some(VmValue::Char(character));
            }
            VmInstruction::CharToU32 { dst, value } => {
                let value = expect_char(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                registers[dst as usize] = Some(VmValue::U32(value as u32));
            }
            VmInstruction::BytesLen { dst, value } => {
                let value = expect_bytes(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                registers[dst as usize] = Some(VmValue::Usize(value.len() as u64));
            }
            VmInstruction::BytesConcat { dst, left, right } => {
                let left = expect_bytes(
                    registers[left as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let right = expect_bytes(
                    registers[right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let length = left.len().checked_add(right.len()).ok_or(
                    VmArtifactError::AllocationLimit {
                        limit: budget.limits.max_allocation_elements,
                    },
                )?;
                budget.reserve_value("bytes", length)?;
                let mut value = left.to_vec();
                value.extend_from_slice(&right);
                registers[dst as usize] = Some(VmValue::Bytes(Arc::from(value)));
            }
            VmInstruction::BytesGet { dst, bytes, index } => {
                let bytes = expect_bytes(
                    registers[bytes as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let index = expect_usize(
                    registers[index as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as usize;
                let value = *bytes.get(index).ok_or(VmArtifactError::InvalidRegister {
                    register: index as u32,
                })?;
                registers[dst as usize] = Some(VmValue::U8(value));
            }
            VmInstruction::BytesSlice {
                dst,
                bytes,
                start,
                end,
            } => {
                let bytes = expect_bytes(
                    registers[bytes as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let start = expect_usize(
                    registers[start as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as usize;
                let end =
                    expect_usize(registers[end as usize].as_ref().expect("verified register"))?
                        as usize;
                let value = bytes
                    .get(start..end)
                    .ok_or(VmArtifactError::InvalidRegister {
                        register: start as u32,
                    })?;
                budget.reserve_value("bytes", value.len())?;
                registers[dst as usize] = Some(VmValue::Bytes(Arc::from(value)));
            }
            VmInstruction::BytesFromArrayMove { dst, value } => {
                let values = match registers[value as usize]
                    .as_ref()
                    .expect("verified register")
                {
                    VmValue::Array { values, .. } => values,
                    value => {
                        return Err(VmArtifactError::ResultType {
                            expected: VmType::Array(Box::new(VmType::U8)),
                            found: value.ty(),
                        });
                    }
                };
                budget.reserve_value("bytes", values.len())?;
                let value = values
                    .iter()
                    .map(expect_u8)
                    .collect::<Result<Vec<_>, _>>()?;
                registers[dst as usize] = Some(VmValue::Bytes(Arc::from(value)));
            }
            VmInstruction::BytesToArray { dst, value } => {
                let bytes = expect_bytes(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                budget.reserve_value("array elements", bytes.len())?;
                let values = bytes.iter().copied().map(VmValue::U8).collect::<Vec<_>>();
                registers[dst as usize] = Some(VmValue::Array {
                    capacity: values.len(),
                    values: Arc::from(values),
                });
            }
            VmInstruction::BytesUtf8ValidUpTo { dst, value } => {
                let bytes = expect_bytes(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                registers[dst as usize] = Some(VmValue::Usize(valid_utf8_prefix(&bytes) as u64));
            }
            VmInstruction::ArrayUtf8ValidUpTo { dst, value } => {
                let valid = referenced_array_utf8_valid_prefix(
                    &registers,
                    &[],
                    registers[value as usize].as_ref().expect("verified register"),
                )?;
                registers[dst as usize] = Some(VmValue::Usize(valid as u64));
            }
            VmInstruction::Blake3 { dst, value } => {
                let bytes = expect_bytes(
                    registers[value as usize].as_ref().expect("verified register"),
                )?;
                budget.reserve_value("bytes", blake3::OUT_LEN)?;
                registers[dst as usize] = Some(VmValue::Bytes(Arc::from(
                    blake3::hash(&bytes).as_bytes().as_slice(),
                )));
            }
            instruction @ (VmInstruction::ArrayNew { .. }
            | VmInstruction::ArrayLen { .. }
            | VmInstruction::ArrayGetCopy { .. }
            | VmInstruction::ArrayGetMove { .. }
            | VmInstruction::ArrayGetBorrow { .. }
            | VmInstruction::ArraySetMove { .. }
            | VmInstruction::ArrayEmpty { .. }
            | VmInstruction::ArrayPushMove { .. }
            | VmInstruction::ArrayPushUtf8Char { .. }
            | VmInstruction::ArrayInsertUtf8FromSlice { .. }
            | VmInstruction::ArrayPopUtf8Char { .. }
            | VmInstruction::ArrayUtf8CharAt { .. }
            | VmInstruction::ArrayExtendFromSlice { .. }
            | VmInstruction::ArrayInsertMove { .. }
            | VmInstruction::ArrayRemoveMove { .. }
            | VmInstruction::ArrayAppendMove { .. }
            | VmInstruction::ArrayTruncateDiscard { .. }
            | VmInstruction::ArrayReverseMove { .. }
            | VmInstruction::ArraySplitOffMove { .. }
            | VmInstruction::ArraySplitBorrowUnique { .. }
            | VmInstruction::ArrayInsertFromSlice { .. }
            | VmInstruction::ArrayPopMove { .. }
            | VmInstruction::ArrayCapacity { .. }
            | VmInstruction::ArrayReserve { .. }
            | VmInstruction::ArrayFinishDrained { .. }) => {
                execute_array_primitive(&mut registers, &mut [], &instruction, budget)?
            }
            VmInstruction::U32CheckedAdd { dst, left, right } => {
                u32_checked_binary(&mut registers, dst, left, right, u32::checked_add)?
            }
            VmInstruction::U32CheckedSub { dst, left, right } => {
                u32_checked_binary(&mut registers, dst, left, right, u32::checked_sub)?
            }
            VmInstruction::U32CheckedMul { dst, left, right } => {
                u32_checked_binary(&mut registers, dst, left, right, u32::checked_mul)?
            }
            VmInstruction::U32CheckedDiv { dst, left, right } => {
                u32_checked_division(&mut registers, dst, left, right, false)?
            }
            VmInstruction::U32CheckedRem { dst, left, right } => {
                u32_checked_division(&mut registers, dst, left, right, true)?
            }
            VmInstruction::U32WrappingAdd { dst, left, right } => {
                u32_wrapping_binary(&mut registers, dst, left, right, u32::wrapping_add)?
            }
            VmInstruction::U32WrappingSub { dst, left, right } => {
                u32_wrapping_binary(&mut registers, dst, left, right, u32::wrapping_sub)?
            }
            VmInstruction::U32WrappingMul { dst, left, right } => {
                u32_wrapping_binary(&mut registers, dst, left, right, u32::wrapping_mul)?
            }
            VmInstruction::U32WrappingShl { dst, left, right } => {
                u32_wrapping_binary(&mut registers, dst, left, right, u32::wrapping_shl)?
            }
            VmInstruction::U32WrappingShr { dst, left, right } => {
                u32_wrapping_binary(&mut registers, dst, left, right, u32::wrapping_shr)?
            }
            VmInstruction::U32CheckedShl { dst, left, right } => {
                u32_checked_binary(&mut registers, dst, left, right, u32::checked_shl)?
            }
            VmInstruction::U32CheckedShr { dst, left, right } => {
                u32_checked_binary(&mut registers, dst, left, right, u32::checked_shr)?
            }
            VmInstruction::U32Eq { dst, left, right } => {
                u32_compare(&mut registers, dst, left, right, |left, right| {
                    left == right
                })?
            }
            VmInstruction::U32Lt { dst, left, right } => {
                u32_compare(&mut registers, dst, left, right, |left, right| left < right)?
            }
            VmInstruction::U32Le { dst, left, right } => {
                u32_compare(&mut registers, dst, left, right, |left, right| {
                    left <= right
                })?
            }
            VmInstruction::U32ToUsize { dst, value } => {
                let value = expect_u32(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                registers[dst as usize] = Some(VmValue::Usize(value as u64));
            }
            VmInstruction::UsizeToU32Checked { dst, value } => {
                let value = expect_usize(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let value =
                    u32::try_from(value).map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[dst as usize] = Some(VmValue::U32(value));
            }
            VmInstruction::I64ToU32Checked { dst, value } => {
                let value = expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let value =
                    u32::try_from(value).map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[dst as usize] = Some(VmValue::U32(value));
            }
            VmInstruction::I64ToU32Wrapping { dst, value } => {
                registers[dst as usize] = Some(VmValue::U32(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as u32));
            }
            VmInstruction::I64ToUsizeChecked { dst, value } => {
                let value = expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let value =
                    u64::try_from(value).map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[dst as usize] = Some(VmValue::Usize(value));
            }
            VmInstruction::I64ToUsizeWrapping { dst, value } => {
                registers[dst as usize] = Some(VmValue::Usize(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as u64));
            }
            VmInstruction::I64ToU8Checked { dst, value } => {
                let value = expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let value = u8::try_from(value).map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[dst as usize] = Some(VmValue::U8(value));
            }
            VmInstruction::I64ToU8Wrapping { dst, value } => {
                registers[dst as usize] = Some(VmValue::U8(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as u8));
            }
            VmInstruction::I64ToU16Checked { dst, value } => {
                let value = expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let value =
                    u16::try_from(value).map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[dst as usize] = Some(VmValue::U16(value));
            }
            VmInstruction::I64ToU16Wrapping { dst, value } => {
                registers[dst as usize] = Some(VmValue::U16(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as u16));
            }
            VmInstruction::I64ToI16Checked { dst, value } => {
                let value = i16::try_from(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?)
                .map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[dst as usize] = Some(VmValue::I16(value));
            }
            VmInstruction::I64ToI16Wrapping { dst, value } => {
                registers[dst as usize] = Some(VmValue::I16(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as i16));
            }
            VmInstruction::I64ToI32Checked { dst, value } => {
                let value = i32::try_from(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?)
                .map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[dst as usize] = Some(VmValue::I32(value));
            }
            VmInstruction::I64ToI32Wrapping { dst, value } => {
                registers[dst as usize] = Some(VmValue::I32(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as i32));
            }
            VmInstruction::I64ToI8Checked { dst, value } => {
                let value = i8::try_from(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?)
                .map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[dst as usize] = Some(VmValue::I8(value));
            }
            VmInstruction::I64ToI8Wrapping { dst, value } => {
                registers[dst as usize] = Some(VmValue::I8(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as i8));
            }
            VmInstruction::I64ToU64Checked { dst, value } => {
                let value = u64::try_from(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?)
                .map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[dst as usize] = Some(VmValue::U64(value));
            }
            VmInstruction::I64ToU64Wrapping { dst, value } => {
                registers[dst as usize] = Some(VmValue::U64(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as u64));
            }
            VmInstruction::I64ToIsizeChecked { dst, value } => {
                registers[dst as usize] = Some(VmValue::Isize(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?));
            }
            VmInstruction::I64ToIsizeWrapping { dst, value } => {
                registers[dst as usize] = Some(VmValue::Isize(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?));
            }
            VmInstruction::I64ToU128Checked { dst, value } => {
                let value = u128::try_from(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?)
                .map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[dst as usize] = Some(VmValue::U128(value));
            }
            VmInstruction::I64ToU128Wrapping { dst, value } => {
                registers[dst as usize] = Some(VmValue::U128(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as u128));
            }
            VmInstruction::I64ToI128Checked { dst, value } => {
                registers[dst as usize] = Some(VmValue::I128(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as i128));
            }
            VmInstruction::I64ToI128Wrapping { dst, value } => {
                registers[dst as usize] = Some(VmValue::I128(expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as i128));
            }
            VmInstruction::MakeTuple { dst, fields } => {
                budget.reserve_value("tuple fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| {
                        registers[*field as usize]
                            .as_ref()
                            .expect("verified register")
                            .clone()
                    })
                    .collect::<Vec<_>>();
                registers[dst as usize] = Some(VmValue::Tuple(Arc::from(values)));
            }
            VmInstruction::MakeArray { dst, fields, .. } => {
                budget.reserve_value("array elements", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| {
                        registers[*field as usize]
                            .as_ref()
                            .expect("verified register")
                            .clone()
                    })
                    .collect::<Vec<_>>();
                registers[dst as usize] = Some(VmValue::Array {
                    capacity: values.len(),
                    values: Arc::from(values),
                });
            }
            VmInstruction::MakeRecord {
                dst,
                definition,
                fields,
                ..
            } => {
                budget.reserve_value("record fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| {
                        registers[*field as usize]
                            .as_ref()
                            .expect("verified register")
                            .clone()
                    })
                    .collect::<Vec<_>>();
                let signature = register_type(function, dst)?;
                registers[dst as usize] = Some(VmValue::Record {
                    definition,
                    fields: Arc::from(values),
                    signature,
                });
            }
            VmInstruction::MakeEnum {
                dst,
                definition,
                variant,
                fields,
                ..
            } => {
                budget.reserve_value("enum fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| {
                        registers[*field as usize]
                            .as_ref()
                            .expect("verified register")
                            .clone()
                    })
                    .collect::<Vec<_>>();
                let signature = register_type(function, dst)?;
                registers[dst as usize] = Some(VmValue::Enum {
                    definition,
                    variant,
                    fields: Arc::from(values),
                    signature,
                });
            }
            VmInstruction::ProjectRecord {
                dst,
                base,
                index,
                field_count,
                field_type,
            } => {
                let fields = match registers[base as usize]
                    .as_ref()
                    .expect("verified register")
                {
                    VmValue::Record { fields, .. } | VmValue::Enum { fields, .. } => fields,
                    _ => return Err(VmArtifactError::InvalidRegister { register: base }),
                };
                if fields.len() != field_count as usize {
                    return Err(VmArtifactError::CallArity {
                        expected: field_count,
                        found: fields.len() as u32,
                    });
                }
                let value = fields
                    .get(index as usize)
                    .ok_or(VmArtifactError::InvalidRegister { register: index })?
                    .clone();
                if !value_matches_vm_type(&value, &field_type) {
                    return Err(VmArtifactError::ResultType {
                        expected: field_type.clone(),
                        found: value.ty(),
                    });
                }
                registers[dst as usize] = Some(value);
            }
            VmInstruction::ProjectArray {
                dst,
                base,
                index,
                field_count,
                ..
            } => {
                let VmValue::Array { values: fields, .. } = registers[base as usize]
                    .as_ref()
                    .expect("verified register")
                else {
                    return Err(VmArtifactError::InvalidRegister { register: base });
                };
                if fields.len() != field_count as usize {
                    return Err(VmArtifactError::CallArity {
                        expected: field_count,
                        found: fields.len() as u32,
                    });
                }
                registers[dst as usize] = Some(
                    fields
                        .get(index as usize)
                        .ok_or(VmArtifactError::InvalidRegister { register: index })?
                        .clone(),
                );
            }
            VmInstruction::ProjectTuple {
                dst,
                base,
                index,
                field_count,
                ..
            } => {
                let VmValue::Tuple(fields) = registers[base as usize]
                    .as_ref()
                    .expect("verified register")
                else {
                    return Err(VmArtifactError::InvalidRegister { register: base });
                };
                if fields.len() != field_count as usize {
                    return Err(VmArtifactError::CallArity {
                        expected: field_count,
                        found: fields.len() as u32,
                    });
                }
                registers[dst as usize] = Some(
                    fields
                        .get(index as usize)
                        .ok_or(VmArtifactError::InvalidRegister { register: index })?
                        .clone(),
                );
            }
            VmInstruction::UpdateRecord {
                dst,
                base,
                index,
                field_count,
                value,
                ..
            } => {
                let VmValue::Record {
                    definition,
                    fields,
                    signature,
                } = registers[base as usize]
                    .as_ref()
                    .expect("verified register")
                else {
                    return Err(VmArtifactError::InvalidRegister { register: base });
                };
                if fields.len() != field_count as usize {
                    return Err(VmArtifactError::CallArity {
                        expected: field_count,
                        found: fields.len() as u32,
                    });
                }
                budget.reserve_value("record update fields", fields.len())?;
                let mut fields = fields.to_vec();
                let index = index as usize;
                let Some(field) = fields.get_mut(index) else {
                    return Err(VmArtifactError::InvalidRegister {
                        register: index as u32,
                    });
                };
                *field = registers[value as usize]
                    .as_ref()
                    .expect("verified register")
                    .clone();
                registers[dst as usize] = Some(VmValue::Record {
                    definition: *definition,
                    fields: Arc::from(fields),
                    signature: signature.clone(),
                });
            }
            VmInstruction::PatternTest {
                dst,
                subject,
                pattern,
            } => {
                registers[dst as usize] = Some(VmValue::Bool(matches_pattern(
                    registers[subject as usize]
                        .as_ref()
                        .expect("verified register"),
                    &pattern,
                )));
            }
            VmInstruction::Perform {
                dst,
                effect,
                effect_arguments,
                operation,
                arguments,
            } => {
                budget.reserve_value("handler payload", arguments.len())?;
                let values = arguments
                    .iter()
                    .map(|argument| {
                        registers[*argument as usize]
                            .clone()
                            .ok_or(VmArtifactError::ReadBeforeWrite {
                                register: *argument,
                            })
                            .and_then(|value| freeze_frame_value(&value, &registers, &[]))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let Some(index) = handlers.iter().rposition(|frame| {
                    frame.suspended.is_none()
                        && frame.effect == effect
                        && frame.effect_arguments == effect_arguments
                        && frame.operation == operation
                }) else {
                    return Err(VmArtifactError::UnhandledEffect {
                        effect,
                        effect_arguments,
                        operation,
                    });
                };
                let above = handlers.split_off(index + 1);
                if handlers
                    .iter()
                    .filter(|handler| handler.suspended.is_some())
                    .count()
                    >= budget.limits.max_retained_continuations as usize
                {
                    return Err(VmArtifactError::ContinuationLimit {
                        limit: budget.limits.max_retained_continuations,
                    });
                }
                let frame = &mut handlers[index];
                if frame.payload_destinations.len() != values.len() {
                    return Err(VmArtifactError::CallArity {
                        expected: frame.payload_destinations.len() as u32,
                        found: values.len() as u32,
                    });
                }
                budget.reserve_allocation(registers.len())?;
                let saved = registers.clone();
                for (destination, value) in frame
                    .payload_destinations
                    .iter()
                    .zip(values.iter().cloned())
                {
                    registers[*destination as usize] = Some(value);
                }
                frame.suspended = Some(RuntimeContinuation {
                    target: pc + 1,
                    dst,
                    registers: saved,
                    performed: RuntimePerformed {
                        effect,
                        effect_arguments,
                        operation,
                        payloads: values,
                    },
                    above,
                    pending_leave: None,
                    remaining_replays: frame.continuation.replay_uses().unwrap_or(0),
                    program: None,
                });
                pc = frame.target as usize;
                continue;
            }
            VmInstruction::InstallHandler {
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                continuation,
                target,
                ..
            } => {
                if handlers.len() >= budget.limits.max_handler_depth as usize {
                    return Err(VmArtifactError::HandlerDepthLimit {
                        limit: budget.limits.max_handler_depth,
                    });
                }
                handlers.push(RuntimeHandlerFrame {
                    id: {
                        let id = next_handler_id;
                        next_handler_id = next_handler_id.saturating_add(1);
                        id
                    },
                    call_depth: 0,
                    effect,
                    effect_arguments,
                    operation,
                    payload_destinations,
                    continuation,
                    target,
                    suspended: None,
                })
            }
            VmInstruction::UninstallHandler => {
                let Some(frame) = handlers.pop() else {
                    return Err(VmArtifactError::HandlerStackUnderflow);
                };
                if frame.suspended.is_some() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
            }
            VmInstruction::Resume { value } => {
                let resumed = registers[value as usize]
                    .clone()
                    .ok_or(VmArtifactError::ReadBeforeWrite { register: value })?;
                let Some(frame) = handlers.last_mut() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.continuation.is_replay() {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                let continuation = match frame.continuation {
                    VmContinuationPolicy::Consume => frame.suspended.take(),
                    VmContinuationPolicy::Replay { .. } => frame.suspended.clone(),
                    VmContinuationPolicy::Terminal => {
                        return Err(VmArtifactError::HandlerResumeUnavailable);
                    }
                };
                let Some(continuation) = continuation else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.continuation.is_replay() {
                    frame.suspended = None;
                }
                let RuntimeContinuation {
                    target,
                    dst,
                    registers: saved_registers,
                    above,
                    pending_leave,
                    ..
                } = continuation;
                if let Some(leave) = pending_leave {
                    registers = saved_registers;
                    handlers.extend(above);
                    pc = complete_pending_leave(&mut registers, &mut handlers, leave)?;
                    continue;
                }
                registers = saved_registers;
                registers[dst as usize] = Some(resumed);
                handlers.extend(above);
                pc = target;
                continue;
            }
            VmInstruction::ResumeReturn { dst, value } => {
                let resumed = registers[value as usize]
                    .clone()
                    .ok_or(VmArtifactError::ReadBeforeWrite { register: value })?;
                let Some(frame) = handlers.last_mut() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.continuation == VmContinuationPolicy::Terminal {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let replaying = frame.continuation.is_replay();
                let continuation = if replaying {
                    frame.suspended.clone()
                } else {
                    frame.suspended.take()
                }
                .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                if replaying && continuation.remaining_replays == 0 {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                budget.reserve_allocation(registers.len())?;
                let RuntimeContinuation {
                    target,
                    dst: continuation_dst,
                    registers: saved_registers,
                    above,
                    pending_leave,
                    ..
                } = continuation;
                if pending_leave.is_some() {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                let resumed_handler_ids = handlers
                    .iter()
                    .map(|frame| frame.id)
                    .chain(above.iter().map(|frame| frame.id))
                    .collect();
                let mut return_handlers = handlers.clone();
                if replaying {
                    return_handlers
                        .last_mut()
                        .and_then(|frame| frame.suspended.as_mut())
                        .expect("checked suspended replay handler")
                        .remaining_replays -= 1;
                }
                resumption_returns.push(RuntimeResumptionReturn {
                    pc: pc + 1,
                    dst,
                    registers: registers.clone(),
                    handlers: return_handlers,
                    program: None,
                    resumed_handler_ids,
                });
                // The active execution gets a clean handler frame so its
                // protected `UninstallHandler` can run. The clause snapshot
                // above retains the suspended continuation for the next use.
                if replaying {
                    handlers.last_mut().expect("active frame exists").suspended = None;
                }
                handlers.extend(above);
                registers = saved_registers;
                registers[continuation_dst as usize] = Some(resumed);
                pc = target;
                continue;
            }
            VmInstruction::CaptureResumption { dst } => {
                let Some(frame) = handlers.last() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.suspended.is_none() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let signature = register_type(function, dst)?;
                if !matches!(signature, VmType::Callable { .. }) {
                    return Err(VmArtifactError::NotCallable { register: dst });
                }
                registers[dst as usize] = Some(VmValue::Resumption {
                    frame: frame.id,
                    signature,
                });
            }
            VmInstruction::ResumeSnapshot { snapshot, value } => {
                let resumed = registers[value as usize]
                    .clone()
                    .ok_or(VmArtifactError::ReadBeforeWrite { register: value })?;
                let VmValue::Resumption { frame: id, .. } =
                    registers[snapshot as usize]
                        .as_ref()
                        .ok_or(VmArtifactError::ReadBeforeWrite { register: snapshot })?
                else {
                    return Err(VmArtifactError::NotCallable { register: snapshot });
                };
                let Some(index) = handlers.iter().rposition(|frame| frame.id == *id) else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                let continuation = match handlers[index].continuation {
                    VmContinuationPolicy::Consume => handlers[index].suspended.take(),
                    VmContinuationPolicy::Replay { .. } => handlers[index].suspended.clone(),
                    VmContinuationPolicy::Terminal => {
                        return Err(VmArtifactError::HandlerResumeUnavailable);
                    }
                }
                .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                if handlers[index].continuation.is_replay() {
                    handlers[index].suspended = None;
                }
                // Resumption is a non-local transfer. Frames installed after
                // the captured frame belong to the abandoned clause path;
                // only the deep frames recorded at the original `Perform`
                // are reinstated with the continuation.
                handlers.truncate(index + 1);
                let RuntimeContinuation {
                    target,
                    dst,
                    registers: saved_registers,
                    above,
                    pending_leave,
                    ..
                } = continuation;
                if let Some(leave) = pending_leave {
                    registers = saved_registers;
                    handlers.extend(above);
                    pc = complete_pending_leave(&mut registers, &mut handlers, leave)?;
                    continue;
                }
                registers = saved_registers;
                registers[dst as usize] = Some(resumed);
                handlers.extend(above);
                pc = target;
                continue;
            }
            VmInstruction::Forward => {
                let Some(mut declined) = handlers.pop() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                let Some(continuation) = declined.suspended.take() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                let Some(index) = handlers.iter().rposition(|frame| {
                    frame.suspended.is_none()
                        && frame.effect == continuation.performed.effect
                        && frame.effect_arguments == continuation.performed.effect_arguments
                        && frame.operation == continuation.performed.operation
                }) else {
                    return Err(VmArtifactError::UnhandledEffect {
                        effect: continuation.performed.effect,
                        effect_arguments: continuation.performed.effect_arguments,
                        operation: continuation.performed.operation,
                    });
                };
                let mut crossed = handlers.split_off(index + 1);
                crossed.push(declined);
                crossed.extend(continuation.above.clone());
                let frame = &mut handlers[index];
                if frame.payload_destinations.len() != continuation.performed.payloads.len() {
                    return Err(VmArtifactError::CallArity {
                        expected: frame.payload_destinations.len() as u32,
                        found: continuation.performed.payloads.len() as u32,
                    });
                }
                budget.reserve_allocation(continuation.registers.len())?;
                registers = continuation.registers.clone();
                for (destination, payload) in frame
                    .payload_destinations
                    .iter()
                    .zip(continuation.performed.payloads.iter().cloned())
                {
                    registers[*destination as usize] = Some(payload);
                }
                frame.suspended = Some(RuntimeContinuation {
                    target: continuation.target,
                    dst: continuation.dst,
                    registers: continuation.registers,
                    performed: continuation.performed,
                    above: crossed,
                    pending_leave: continuation.pending_leave,
                    remaining_replays: continuation.remaining_replays,
                    program: None,
                });
                pc = frame.target as usize;
                continue;
            }
            VmInstruction::Cancel => {
                let Some(frame) = handlers.pop() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.suspended.is_none() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                if frame.continuation == VmContinuationPolicy::Terminal {
                    resumption_returns.clear();
                }
            }
            VmInstruction::Copy { dst, src } => {
                registers[dst as usize] = registers[src as usize].clone()
            }
            VmInstruction::StorageLive { local, .. } => {
                if registers[local as usize].is_some() {
                    return Err(VmArtifactError::ReadBeforeWrite { register: local });
                }
                // `None` is the runtime representation of a live but
                // uninitialized addressable slot; verification carries the
                // distinction from dead storage.
            }
            VmInstruction::StorageDead { local, .. } => {
                if registers[local as usize].is_some() {
                    return Err(VmArtifactError::ReadBeforeWrite { register: local });
                }
            }
            VmInstruction::SetDropFlag { flag, value } => {
                registers[flag as usize] = Some(VmValue::Bool(value))
            }
            VmInstruction::DestroyIf { local, flag } => {
                match registers[flag as usize].as_ref() {
                    Some(VmValue::Bool(_)) => {}
                    _ => return Err(VmArtifactError::ReadBeforeWrite { register: flag }),
                }
                registers[local as usize] = None;
            }
            VmInstruction::Store { dst, src } => {
                registers[dst as usize] = registers[src as usize].clone()
            }
            VmInstruction::Move { dst, src } => {
                registers[dst as usize] = registers[src as usize].take()
            }
            VmInstruction::Borrow {
                dst,
                src,
                fields,
                unique,
                reborrow,
            } => {
                let VmType::Reference { referent, .. } = &function.registers[dst as usize] else {
                    return Err(VmArtifactError::InvalidRegister { register: dst });
                };
                registers[dst as usize] = Some(borrow_value(
                    &registers,
                    &[],
                    src,
                    registers[src as usize].as_ref().expect("verified register"),
                    &fields,
                    unique,
                    reborrow,
                    referent,
                )?);
            }
            VmInstruction::DerefCopy { dst, reference } => {
                let VmValue::Reference { target, fields, .. } = registers[reference as usize]
                    .as_ref()
                    .expect("verified register")
                else {
                    return Err(VmArtifactError::InvalidRegister {
                        register: reference,
                    });
                };
                registers[dst as usize] = Some(load_reference_target(&registers, &[], target, fields, budget)?);
            }
            VmInstruction::DerefMove { dst, reference } => {
                let VmValue::Reference { target, fields, .. } = registers[reference as usize]
                    .as_ref()
                    .expect("verified register")
                else {
                    return Err(VmArtifactError::InvalidRegister { register: reference });
                };
                // The verifier has made the unique loan unreadable until its
                // matching store. Runtime storage can retain the old value in
                // that interval because no verified instruction can observe
                // it; cloning here is representation sharing, not language
                // copying.
                registers[dst as usize] = Some(load_reference_target(&registers, &[], target, fields, budget)?);
            }
            VmInstruction::DerefStore { reference, src } => {
                let VmValue::Reference {
                    target,
                    fields,
                    unique: true,
                    ..
                } = registers[reference as usize]
                    .as_ref()
                    .expect("verified register")
                else {
                    return Err(VmArtifactError::InvalidRegister {
                        register: reference,
                    });
                };
                let (target, fields) = (target.clone(), fields.clone());
                let replacement = registers[src as usize]
                    .as_ref()
                    .expect("verified register")
                    .clone();
                store_reference_target(&mut registers, &mut [], &target, &fields, replacement, budget)?;
            }
            VmInstruction::NotBool { dst, value } => {
                registers[dst as usize] = Some(VmValue::Bool(!expect_bool(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?))
            }
            VmInstruction::AddI64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .checked_add(expect_i64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?)
                    .ok_or(VmArtifactError::ArithmeticOverflow)?,
                ))
            }
            VmInstruction::WrappingAddI64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .wrapping_add(expect_i64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?),
                ))
            }
            VmInstruction::WrappingSubI64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .wrapping_sub(expect_i64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?),
                ))
            }
            VmInstruction::WrappingMulI64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .wrapping_mul(expect_i64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?),
                ))
            }
            VmInstruction::IntEqualI64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::U32(
                    (expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? == expect_i64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?) as u32,
                ))
            }
            VmInstruction::IntLessI64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::U32(
                    (expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? < expect_i64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?) as u32,
                ))
            }
            VmInstruction::IntGreaterI64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::U32(
                    (expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? > expect_i64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?) as u32,
                ))
            }
            VmInstruction::BitAndI64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? & expect_i64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::BitAndU32 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::U32(
                    expect_u32(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? & expect_u32(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::BitAndU64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::U64(
                    expect_u64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? & expect_u64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::BitXorI64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? ^ expect_i64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::IntShrI64 { dst, left, right } => {
                let count = expect_u32(
                    registers[right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                if count >= 64 {
                    return Err(VmArtifactError::ArithmeticOverflow);
                }
                registers[dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .wrapping_shr(count),
                ))
            }
            VmInstruction::BitOrI64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? | expect_i64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::BitNotI64 { dst, value } => {
                registers[dst as usize] = Some(VmValue::I64(!expect_i64(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?))
            }
            VmInstruction::ShlI64 { dst, value, count } => {
                let count = expect_u32(
                    registers[count as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                if count >= 64 {
                    return Err(VmArtifactError::ArithmeticOverflow);
                }
                registers[dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[value as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .wrapping_shl(count),
                ))
            }
            VmInstruction::SubI64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .checked_sub(expect_i64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?)
                    .ok_or(VmArtifactError::ArithmeticOverflow)?,
                ))
            }
            VmInstruction::MulI64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .checked_mul(expect_i64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?)
                    .ok_or(VmArtifactError::ArithmeticOverflow)?,
                ))
            }
            VmInstruction::DivI64 { dst, left, right } => {
                let right = expect_i64(
                    registers[right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let value = expect_i64(
                    registers[left as usize]
                        .as_ref()
                        .expect("verified register"),
                )?
                .checked_div(right)
                .ok_or(if right == 0 {
                    VmArtifactError::DivisionByZero
                } else {
                    VmArtifactError::ArithmeticOverflow
                })?;
                registers[dst as usize] = Some(VmValue::I64(value));
            }
            VmInstruction::RemI64 { dst, left, right } => {
                let right = expect_i64(
                    registers[right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let value = expect_i64(
                    registers[left as usize]
                        .as_ref()
                        .expect("verified register"),
                )?
                .checked_rem(right)
                .ok_or(if right == 0 {
                    VmArtifactError::DivisionByZero
                } else {
                    VmArtifactError::ArithmeticOverflow
                })?;
                registers[dst as usize] = Some(VmValue::I64(value));
            }
            VmInstruction::AddF64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::F64(canonical_vm_f64(
                    expect_f64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? + expect_f64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                )))
            }
            VmInstruction::ConcatText { dst, left, right } => {
                let left = expect_text(
                    registers[left as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let right = expect_text(
                    registers[right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let length = left.len().checked_add(right.len()).ok_or(
                    VmArtifactError::AllocationLimit {
                        limit: budget.limits.max_allocation_elements,
                    },
                )?;
                budget.reserve_value("text bytes", length)?;
                registers[dst as usize] = Some(VmValue::Text(Arc::from(format!("{left}{right}"))));
            }
            VmInstruction::SubF64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::F64(canonical_vm_f64(
                    expect_f64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? - expect_f64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                )))
            }
            VmInstruction::MulF64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::F64(canonical_vm_f64(
                    expect_f64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? * expect_f64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                )))
            }
            VmInstruction::DivF64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::F64(canonical_vm_f64(
                    expect_f64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? / expect_f64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                )))
            }
            VmInstruction::RemF64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::F64(canonical_vm_f64(
                    expect_f64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? % expect_f64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                )))
            }
            VmInstruction::CompareI64 {
                dst,
                left,
                right,
                op,
            } => {
                registers[dst as usize] = Some(VmValue::Bool(compare_i64_values(
                    expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    expect_i64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    op,
                )))
            }
            VmInstruction::CompareF64 {
                dst,
                left,
                right,
                op,
            } => {
                registers[dst as usize] = Some(VmValue::Bool(compare_f64_values(
                    expect_f64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    expect_f64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    op,
                )))
            }
            VmInstruction::EqBool { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::Bool(
                    expect_bool(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? == expect_bool(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::CompareU32 {
                dst,
                left,
                right,
                op,
            } => {
                registers[dst as usize] = Some(VmValue::Bool(compare_u32_values(
                    expect_u32(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    expect_u32(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    op,
                )))
            }
            VmInstruction::CompareU64 {
                dst,
                left,
                right,
                op,
            } => {
                registers[dst as usize] = Some(VmValue::Bool(compare_u64_values(
                    expect_u64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    expect_u64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    op,
                )))
            }
            VmInstruction::NeBool { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::Bool(
                    expect_bool(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? != expect_bool(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::EqText { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::Bool(
                    expect_text(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? == expect_text(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::NeText { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::Bool(
                    expect_text(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? != expect_text(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::CompareChar {
                dst,
                left,
                right,
                op,
            } => {
                registers[dst as usize] = Some(VmValue::Bool(compare_char_values(
                    expect_char(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    expect_char(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    op,
                )))
            }
            VmInstruction::MakeLabel {
                dst,
                brand_owner,
                brand_label,
                target,
                destination,
            } => {
                let signature = register_type(function, dst)?;
                registers[dst as usize] = Some(VmValue::Label {
                    owner: brand_owner,
                    label: brand_label,
                    target,
                    destination,
                    call_depth: 0,
                    handler_depth: handlers.len(),
                    signature,
                });
            }
            VmInstruction::CallIndirect {
                callee, arguments, ..
            } => {
                let VmValue::Label {
                    target,
                    destination,
                    handler_depth,
                    ..
                } = registers[callee as usize]
                    .as_ref()
                    .expect("verified register")
                    .clone()
                else {
                    return Err(VmArtifactError::CallRequiresProgram);
                };
                let [argument] = arguments.as_slice() else {
                    return Err(VmArtifactError::CallArity {
                        expected: 1,
                        found: arguments.len() as u32,
                    });
                };
                registers[destination as usize] = registers[*argument as usize].clone();
                handlers.truncate(handler_depth);
                // A dynamic label invocation is the same nonlocal control
                // boundary as a direct Leave: no suspended clause-return
                // path may survive to resurrect an abandoned replay frame.
                resumption_returns.clear();
                pc = target as usize;
                continue;
            }
            VmInstruction::Call { .. } | VmInstruction::MakeCallable { .. } => {
                return Err(VmArtifactError::CallRequiresProgram);
            }
            VmInstruction::HostCall {
                capability, symbol, ..
            } => {
                return Err(VmArtifactError::HostCallRequiresAuthority { capability, symbol });
            }
            VmInstruction::Jump { target } => {
                pc = target as usize;
                continue;
            }
            VmInstruction::Leave {
                brand_owner,
                brand_label,
                handler_depth,
                target,
                arguments,
                destinations,
                cleanup,
            } => {
                pc = complete_pending_leave(
                    &mut registers,
                    &mut handlers,
                    PendingLeave {
                        brand_owner,
                        brand_label,
                        handler_depth,
                        target,
                        arguments,
                        destinations,
                        cleanup,
                    },
                )?;
                // A lexical leave abandons every suspended clause-return
                // path it crosses.  Restoring one after reaching the label
                // would resurrect the cancelled continuation and its frames.
                resumption_returns.clear();
                continue;
            }
            VmInstruction::BranchBool {
                condition,
                then_target,
                else_target,
            } => {
                pc = if expect_bool(
                    registers[condition as usize]
                        .as_ref()
                        .expect("verified register"),
                )? {
                    then_target as usize
                } else {
                    else_target as usize
                };
                continue;
            }
            VmInstruction::Return { value } => {
                if let Some(return_to_clause) = resumption_returns.last() {
                    if handlers
                        .iter()
                        .any(|handler| !return_to_clause.resumed_handler_ids.contains(&handler.id))
                    {
                        return Err(VmArtifactError::HandlerStillActive);
                    }
                    let value = registers[value as usize]
                        .as_ref()
                        .expect("verified register")
                        .clone();
                    let return_to_clause = resumption_returns
                        .pop()
                        .expect("checked clause-return frame exists");
                    registers = return_to_clause.registers;
                    registers[return_to_clause.dst as usize] = Some(value);
                    handlers = return_to_clause.handlers;
                    pc = return_to_clause.pc;
                    continue;
                }
                if !handlers.is_empty() {
                    return Err(VmArtifactError::HandlerStillActive);
                }
                return Ok(registers[value as usize]
                    .as_ref()
                    .expect("verified register")
                    .clone());
            }
            VmInstruction::Trap => return Err(VmArtifactError::Trap),
        }
        pc += 1;
    }
    Err(VmArtifactError::NoReturn)
}
/// Apply a verifier-checked pending nonlocal exit.  Parallel materialization
/// is essential: a label edge may swap block parameters, so writing one
/// destination before reading all arguments would corrupt a legal transfer.
fn complete_pending_leave(
    registers: &mut [Option<VmValue>],
    handlers: &mut Vec<RuntimeHandlerFrame>,
    leave: PendingLeave,
) -> Result<usize, VmArtifactError> {
    if !leave.cleanup.validate()
        || !leave
            .cleanup
            .storage_erasure
            .validate(&leave.arguments, registers.len())
        || leave.arguments.len() != leave.destinations.len()
    {
        return Err(VmArtifactError::HandlerStateMismatch);
    }
    let values = leave
        .arguments
        .iter()
        .map(|argument| {
            registers
                .get(*argument as usize)
                .and_then(Clone::clone)
                .ok_or(VmArtifactError::ReadBeforeWrite {
                    register: *argument,
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    for (&destination, value) in leave.destinations.iter().zip(values) {
        let slot =
            registers
                .get_mut(destination as usize)
                .ok_or(VmArtifactError::InvalidRegister {
                    register: destination,
                })?;
        *slot = Some(value);
    }
    // A leave has crossed every active lexical handler. Any captured one-shot
    // continuation was abandoned by the source control transfer, so no frame
    // survives that could later re-authorize a stale snapshot.
    let handler_depth = leave.handler_depth as usize;
    if handler_depth > handlers.len() {
        return Err(VmArtifactError::HandlerStateMismatch);
    }
    handlers.truncate(handler_depth);
    Ok(leave.target as usize)
}
fn encode_instruction(value: &VmInstruction, output: &mut Vec<u8>) {
    match value {
        VmInstruction::DeclareResult { result, returns } => {
            output.push(172);
            encode_type(result, output);
            output.push(u8::from(*returns));
        }
        VmInstruction::ConstUnit { dst } => {
            output.push(28);
            output.extend_from_slice(&dst.to_le_bytes());
        }
        VmInstruction::ConstI64 { dst, value } => {
            output.push(0);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstU8 { dst, value } => {
            output.push(157);
            output.extend_from_slice(&dst.to_le_bytes());
            output.push(*value)
        }
        VmInstruction::ConstU16 { dst, value } => {
            output.push(158);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstU32 { dst, value } => {
            output.push(151);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstU64 { dst, value } => {
            output.push(152);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstUsize { dst, value } => {
            output.push(159);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstU128 { dst, value } => {
            output.push(160);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstI8 { dst, value } => {
            output.push(161);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstI16 { dst, value } => {
            output.push(162);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstI32 { dst, value } => {
            output.push(163);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstIsize { dst, value } => {
            output.push(164);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstI128 { dst, value } => {
            output.push(165);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstF64 { dst, bits } => {
            output.push(7);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&bits.to_le_bytes())
        }
        VmInstruction::ConstF32 { dst, bits } => {
            output.push(171);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&bits.to_le_bytes())
        }
        VmInstruction::MemoryIntrinsic { dst, primitive, types, arguments } => {
            output.push(194);
            output.extend_from_slice(&dst.to_le_bytes());
            output.push(primitive.ordinal());
            output.extend_from_slice(&(types.len() as u64).to_le_bytes());
            for ty in types { encode_type(ty, output); }
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments { output.extend_from_slice(&argument.to_le_bytes()); }
        }
        VmInstruction::FloatIntrinsic {
            dst,
            primitive,
            arguments,
        } => {
            output.push(138);
            output.extend_from_slice(&dst.to_le_bytes());
            let selector = primitive.selector_name();
            output.extend_from_slice(&(selector.len() as u64).to_le_bytes());
            output.extend_from_slice(selector.as_bytes());
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
        }
        VmInstruction::IntIntrinsic {
            dst,
            primitive,
            scalar,
            arguments,
        } => {
            output.push(166);
            output.extend_from_slice(&dst.to_le_bytes());
            let selector = primitive.selector_name();
            output.extend_from_slice(&(selector.len() as u64).to_le_bytes());
            output.extend_from_slice(selector.as_bytes());
            output.push(
                encode_integer_scalar(*scalar)
                    .expect("integer intrinsic has a runtime integer scalar"),
            );
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
        }
        VmInstruction::ConstBool { dst, value } => {
            output.push(16);
            output.extend_from_slice(&dst.to_le_bytes());
            output.push(u8::from(*value));
        }
        VmInstruction::ConstChar { dst, value } => {
            output.push(20);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::ArrayUtf8CharAt { dst, value, start, length, index } => {
            output.push(192);
            for register in [dst, value, start, length, index] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::ConstText { dst, value } => {
            output.push(24);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&(value.len() as u64).to_le_bytes());
            output.extend_from_slice(value.as_bytes());
        }
        VmInstruction::ConstStaticData {
            dst,
            tag,
            alignment,
            bytes,
        } => {
            output.push(175);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&tag.to_le_bytes());
            output.extend_from_slice(&alignment.to_le_bytes());
            output.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
            output.extend_from_slice(bytes);
        }
        VmInstruction::StaticLen { dst, value } => {
            output.push(176);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::StaticSubslice { dst, value, start, length } => {
            output.push(177);
            for value in [dst, value, start, length] {
                output.extend_from_slice(&value.to_le_bytes());
            }
        }
        VmInstruction::StaticGetBorrowShared { dst, value, index } => {
            output.push(178);
            for value in [dst, value, index] {
                output.extend_from_slice(&value.to_le_bytes());
            }
        }
        VmInstruction::StaticAsArrayBorrow { dst, value } => { output.push(179); output.extend_from_slice(&dst.to_le_bytes()); output.extend_from_slice(&value.to_le_bytes()); }
        VmInstruction::MakeTuple { dst, fields } => {
            output.push(33);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for field in fields {
                output.extend_from_slice(&field.to_le_bytes());
            }
        }
        VmInstruction::MakeArray {
            dst,
            fields,
            element_type,
        } => {
            output.push(37);
            output.extend_from_slice(&dst.to_le_bytes());
            encode_type(element_type, output);
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for field in fields {
                output.extend_from_slice(&field.to_le_bytes());
            }
        }
        VmInstruction::MakeRecord {
            dst,
            definition,
            fields,
            field_types,
        } => {
            output.push(34);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&definition.0.as_bytes());
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for (field, field_type) in fields.iter().zip(field_types) {
                output.extend_from_slice(&field.to_le_bytes());
                encode_type(field_type, output);
            }
        }
        VmInstruction::ProjectRecord {
            dst,
            base,
            index,
            field_count,
            field_type,
        } => {
            output.push(35);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&base.to_le_bytes());
            output.extend_from_slice(&index.to_le_bytes());
            output.extend_from_slice(&field_count.to_le_bytes());
            encode_type(field_type, output);
        }
        VmInstruction::ProjectTuple {
            dst,
            base,
            index,
            field_count,
            field_type,
        } => {
            output.push(42);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&base.to_le_bytes());
            output.extend_from_slice(&index.to_le_bytes());
            output.extend_from_slice(&field_count.to_le_bytes());
            encode_type(field_type, output);
        }
        VmInstruction::ProjectArray {
            dst,
            base,
            index,
            field_count,
            element_type,
        } => {
            output.push(57);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&base.to_le_bytes());
            output.extend_from_slice(&index.to_le_bytes());
            output.extend_from_slice(&field_count.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::UpdateRecord {
            dst,
            base,
            index,
            field_count,
            value,
            field_type,
        } => {
            output.push(39);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&base.to_le_bytes());
            output.extend_from_slice(&index.to_le_bytes());
            output.extend_from_slice(&field_count.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
            encode_type(field_type, output);
        }
        VmInstruction::PatternTest {
            dst,
            subject,
            pattern,
        } => {
            output.push(40);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&subject.to_le_bytes());
            encode_pattern(pattern, output);
        }
        VmInstruction::Perform {
            dst,
            effect,
            effect_arguments,
            operation,
            arguments,
        } => {
            output.push(41);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&effect.0.as_bytes());
            encode_vm_generic_arguments(effect_arguments, output);
            output.extend_from_slice(&operation.to_le_bytes());
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
        }
        VmInstruction::InstallHandler {
            effect,
            effect_arguments,
            operation,
            payload_destinations,
            resume_type,
            continuation,
            target,
        } => {
            output.push(44);
            output.extend_from_slice(&effect.0.as_bytes());
            encode_vm_generic_arguments(effect_arguments, output);
            output.extend_from_slice(&operation.to_le_bytes());
            output.extend_from_slice(&(payload_destinations.len() as u64).to_le_bytes());
            for destination in payload_destinations {
                output.extend_from_slice(&destination.to_le_bytes());
            }
            encode_type(resume_type, output);
            match continuation {
                VmContinuationPolicy::Consume => output.push(0),
                VmContinuationPolicy::Replay { uses } => {
                    output.push(1);
                    output.extend_from_slice(&uses.to_le_bytes());
                }
                VmContinuationPolicy::Terminal => output.push(2),
            }
            output.extend_from_slice(&target.to_le_bytes());
        }
        VmInstruction::UninstallHandler => output.push(45),
        VmInstruction::Resume { value } => {
            output.push(46);
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::ResumeReturn { dst, value } => {
            output.push(51);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::Forward => output.push(47),
        VmInstruction::Cancel => output.push(69),
        VmInstruction::CaptureResumption { dst } => {
            output.push(70);
            output.extend_from_slice(&dst.to_le_bytes());
        }
        VmInstruction::ResumeSnapshot { snapshot, value } => {
            output.push(50);
            output.extend_from_slice(&snapshot.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::Leave {
            brand_owner,
            brand_label,
            handler_depth,
            target,
            arguments,
            destinations,
            cleanup,
        } => {
            output.push(55);
            output.extend_from_slice(&brand_owner.0.as_bytes());
            output.extend_from_slice(&brand_label.to_le_bytes());
            output.extend_from_slice(&handler_depth.to_le_bytes());
            output.extend_from_slice(&target.to_le_bytes());
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
            output.extend_from_slice(&(destinations.len() as u64).to_le_bytes());
            for destination in destinations {
                output.extend_from_slice(&destination.to_le_bytes());
            }
            encode_cleanup_proof(cleanup, output);
        }
        VmInstruction::MakeEnum {
            dst,
            definition,
            variant,
            fields,
            field_types,
        } => {
            output.push(36);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&definition.0.as_bytes());
            output.extend_from_slice(&variant.to_le_bytes());
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for (field, field_type) in fields.iter().zip(field_types) {
                output.extend_from_slice(&field.to_le_bytes());
                encode_type(field_type, output);
            }
        }
        VmInstruction::StorageLive { binding, local } => {
            output.push(167);
            output.extend_from_slice(&binding.to_le_bytes());
            output.extend_from_slice(&local.to_le_bytes());
        }
        VmInstruction::StorageDead { binding, local } => {
            output.push(168);
            output.extend_from_slice(&binding.to_le_bytes());
            output.extend_from_slice(&local.to_le_bytes());
        }
        VmInstruction::SetDropFlag { flag, value } => {
            output.push(169);
            output.extend_from_slice(&flag.to_le_bytes());
            output.push(*value as u8);
        }
        VmInstruction::DestroyIf { local, flag } => {
            output.push(170);
            output.extend_from_slice(&local.to_le_bytes());
            output.extend_from_slice(&flag.to_le_bytes());
        }
        VmInstruction::Copy { dst, src }
        | VmInstruction::Store { dst, src }
        | VmInstruction::Move { dst, src } => {
            output.push(match value {
                VmInstruction::Copy { .. } => 1,
                VmInstruction::Move { .. } => 2,
                VmInstruction::Store { .. } => 38,
                _ => unreachable!("instruction family matched above"),
            });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&src.to_le_bytes())
        }
        VmInstruction::Borrow {
            dst,
            src,
            fields,
            unique,
            reborrow,
        } => {
            output.push(52);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&src.to_le_bytes());
            output.push(*unique as u8);
            output.push(*reborrow as u8);
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for field in fields {
                output.extend_from_slice(&field.to_le_bytes());
            }
        }
        VmInstruction::DerefCopy { dst, reference } => {
            output.push(53);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&reference.to_le_bytes());
        }
        VmInstruction::DerefMove { dst, reference } => {
            output.push(174);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&reference.to_le_bytes());
        }
        VmInstruction::DerefStore { reference, src } => {
            output.push(54);
            output.extend_from_slice(&reference.to_le_bytes());
            output.extend_from_slice(&src.to_le_bytes());
        }
        VmInstruction::NotBool { dst, value } => {
            output.push(19);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::BitNotI64 { dst, value } => {
            output.push(113);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::ShlI64 { dst, value, count } => {
            output.push(114);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
            output.extend_from_slice(&count.to_le_bytes());
        }
        VmInstruction::EqBool { dst, left, right } | VmInstruction::NeBool { dst, left, right } => {
            output.push(if matches!(value, VmInstruction::EqBool { .. }) {
                21
            } else {
                22
            });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&left.to_le_bytes());
            output.extend_from_slice(&right.to_le_bytes());
        }
        VmInstruction::EqText { dst, left, right } | VmInstruction::NeText { dst, left, right } => {
            output.push(if matches!(value, VmInstruction::EqText { .. }) {
                25
            } else {
                26
            });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&left.to_le_bytes());
            output.extend_from_slice(&right.to_le_bytes());
        }
        VmInstruction::AddI64 { dst, left, right }
        | VmInstruction::WrappingAddI64 { dst, left, right }
        | VmInstruction::WrappingSubI64 { dst, left, right }
        | VmInstruction::WrappingMulI64 { dst, left, right }
        | VmInstruction::IntEqualI64 { dst, left, right }
        | VmInstruction::IntLessI64 { dst, left, right }
        | VmInstruction::IntGreaterI64 { dst, left, right }
        | VmInstruction::BitAndI64 { dst, left, right }
        | VmInstruction::BitXorI64 { dst, left, right }
        | VmInstruction::BitOrI64 { dst, left, right }
        | VmInstruction::IntShrI64 { dst, left, right }
        | VmInstruction::SubI64 { dst, left, right }
        | VmInstruction::MulI64 { dst, left, right }
        | VmInstruction::DivI64 { dst, left, right }
        | VmInstruction::RemI64 { dst, left, right }
        | VmInstruction::AddF64 { dst, left, right }
        | VmInstruction::SubF64 { dst, left, right }
        | VmInstruction::MulF64 { dst, left, right }
        | VmInstruction::DivF64 { dst, left, right }
        | VmInstruction::RemF64 { dst, left, right } => {
            output.push(match value {
                VmInstruction::AddI64 { .. } => 3,
                VmInstruction::WrappingAddI64 { .. } => 104,
                VmInstruction::WrappingSubI64 { .. } => 106,
                VmInstruction::WrappingMulI64 { .. } => 107,
                VmInstruction::IntEqualI64 { .. } => 105,
                VmInstruction::IntLessI64 { .. } => 109,
                VmInstruction::IntGreaterI64 { .. } => 110,
                VmInstruction::BitAndI64 { .. } => 108,
                VmInstruction::BitXorI64 { .. } => 112,
                VmInstruction::BitOrI64 { .. } => 111,
                VmInstruction::IntShrI64 { .. } => 115,
                VmInstruction::SubI64 { .. } => 4,
                VmInstruction::MulI64 { .. } => 5,
                VmInstruction::DivI64 { .. } => 8,
                VmInstruction::RemI64 { .. } => 9,
                VmInstruction::AddF64 { .. } => 10,
                VmInstruction::SubF64 { .. } => 11,
                VmInstruction::MulF64 { .. } => 12,
                VmInstruction::DivF64 { .. } => 13,
                VmInstruction::RemF64 { .. } => 14,
                _ => unreachable!("matched arithmetic instruction"),
            });
            for r in [dst, left, right] {
                output.extend_from_slice(&r.to_le_bytes())
            }
        }
        VmInstruction::ConcatText { dst, left, right } => {
            output.push(27);
            for register in [dst, left, right] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::BitAndU32 { dst, left, right }
        | VmInstruction::BitAndU64 { dst, left, right } => {
            output.push(if matches!(value, VmInstruction::BitAndU32 { .. }) {
                153
            } else {
                154
            });
            for register in [dst, left, right] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::CompareI64 {
            dst,
            left,
            right,
            op,
        }
        | VmInstruction::CompareF64 {
            dst,
            left,
            right,
            op,
        }
        | VmInstruction::CompareChar {
            dst,
            left,
            right,
            op,
        } => {
            output.push(match value {
                VmInstruction::CompareI64 { .. } => 17,
                VmInstruction::CompareF64 { .. } => 18,
                VmInstruction::CompareChar { .. } => 23,
                _ => unreachable!("matched comparison instruction"),
            });
            for register in [dst, left, right] {
                output.extend_from_slice(&register.to_le_bytes());
            }
            output.push(match op {
                VmCompare::Equal => 0,
                VmCompare::NotEqual => 1,
                VmCompare::Less => 2,
                VmCompare::LessEqual => 3,
                VmCompare::Greater => 4,
                VmCompare::GreaterEqual => 5,
            });
        }
        VmInstruction::CompareU32 {
            dst,
            left,
            right,
            op,
        }
        | VmInstruction::CompareU64 {
            dst,
            left,
            right,
            op,
        } => {
            output.push(if matches!(value, VmInstruction::CompareU32 { .. }) {
                155
            } else {
                156
            });
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&left.to_le_bytes());
            output.extend_from_slice(&right.to_le_bytes());
            output.push(match op {
                VmCompare::Equal => 0,
                VmCompare::NotEqual => 1,
                VmCompare::Less => 2,
                VmCompare::LessEqual => 3,
                VmCompare::Greater => 4,
                VmCompare::GreaterEqual => 5,
            });
        }
        VmInstruction::Call {
            dst,
            callee,
            arguments,
        } => {
            output.push(6);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&callee.0.as_bytes());
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
        }
        VmInstruction::HostCall {
            dst,
            capability,
            symbol,
            parameters,
            result,
            arguments,
        } => {
            output.push(56);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&(capability.len() as u64).to_le_bytes());
            output.extend_from_slice(capability.as_bytes());
            output.extend_from_slice(&(symbol.len() as u64).to_le_bytes());
            output.extend_from_slice(symbol.as_bytes());
            output.extend_from_slice(&(parameters.len() as u64).to_le_bytes());
            for parameter in parameters {
                encode_type(parameter, output);
            }
            encode_type(result, output);
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
        }
        VmInstruction::TextByteLen { dst, value } => {
            output.push(64);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::TextConcat { dst, left, right } => {
            output.push(65);
            for register in [dst, left, right] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::TextEq { dst, left, right } => {
            output.push(66);
            for register in [dst, left, right] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::TextFromUtf8Checked { dst, value } => {
            output.push(67);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::TextAsBytes { dst, value } => {
            output.push(68);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::CharFromU32Checked { dst, value } => {
            output.push(48);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::CharToU32 { dst, value } => {
            output.push(49);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::BytesLen { dst, value } => {
            output.push(80);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::BytesUtf8ValidUpTo { dst, value } => {
            output.push(86);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::Blake3 { dst, value } => {
            output.push(173);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::ArrayNew {
            dst,
            length,
            fill,
            element_type,
        } => {
            output.push(139);
            for register in [dst, length, fill] {
                output.extend_from_slice(&register.to_le_bytes());
            }
            encode_type(element_type, output);
        }
        VmInstruction::ArrayLen {
            dst,
            value,
            element_type,
        } => {
            output.push(140);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::ArrayUtf8ValidUpTo { dst, value } => {
            output.push(180);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::ArrayPushUtf8Char { value, character } => {
            output.push(181);
            output.extend_from_slice(&value.to_le_bytes());
            output.extend_from_slice(&character.to_le_bytes());
        }
        VmInstruction::ArrayInsertUtf8FromSlice {
            dst,
            value,
            index,
            source,
            start,
            length,
        } => {
            output.push(187);
            for register in [dst, value, index, source, start, length] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::ArrayTruncateDiscard {
            value,
            length,
            element_type,
        } => {
            output.push(188);
            output.extend_from_slice(&value.to_le_bytes());
            output.extend_from_slice(&length.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::ArrayReverseMove { value, element_type } => {
            output.push(189);
            output.extend_from_slice(&value.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::ArraySplitOffMove {
            dst,
            value,
            index,
            element_type,
        } => {
            output.push(190);
            for register in [dst, value, index] {
                output.extend_from_slice(&register.to_le_bytes());
            }
            encode_type(element_type, output);
        }
        VmInstruction::ArraySplitBorrowUnique {
            dst,
            value,
            start,
            length,
            index,
            element_type,
        } => {
            output.push(193);
            for register in [dst, value, start, length, index] {
                output.extend_from_slice(&register.to_le_bytes());
            }
            encode_type(element_type, output);
        }
        VmInstruction::ArrayPopUtf8Char { dst, value } => {
            output.push(191);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::ArrayExtendFromSlice {
            value,
            source,
            start,
            length,
            element_type,
        } => {
            output.push(182);
            output.extend_from_slice(&value.to_le_bytes());
            output.extend_from_slice(&source.to_le_bytes());
            output.extend_from_slice(&start.to_le_bytes());
            output.extend_from_slice(&length.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::ArrayInsertMove {
            value,
            index,
            item,
            element_type,
        } => {
            output.push(183);
            for register in [value, index, item] {
                output.extend_from_slice(&register.to_le_bytes());
            }
            encode_type(element_type, output);
        }
        VmInstruction::ArrayRemoveMove {
            dst,
            value,
            index,
            element_type,
        } => {
            output.push(184);
            for register in [dst, value, index] {
                output.extend_from_slice(&register.to_le_bytes());
            }
            encode_type(element_type, output);
        }
        VmInstruction::ArrayAppendMove {
            value,
            source,
            element_type,
        } => {
            output.push(185);
            output.extend_from_slice(&value.to_le_bytes());
            output.extend_from_slice(&source.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::ArrayInsertFromSlice {
            value,
            index,
            source,
            start,
            length,
            element_type,
        } => {
            output.push(186);
            for register in [value, index, source, start, length] {
                output.extend_from_slice(&register.to_le_bytes());
            }
            encode_type(element_type, output);
        }
        VmInstruction::ArrayGetCopy {
            dst,
            value,
            index,
            element_type,
        } => {
            output.push(141);
            for register in [dst, value, index] {
                output.extend_from_slice(&register.to_le_bytes());
            }
            encode_type(element_type, output);
        }
        VmInstruction::ArrayGetMove {
            dst,
            value,
            index,
            element_type,
        } => {
            output.push(142);
            for register in [dst, value, index] {
                output.extend_from_slice(&register.to_le_bytes());
            }
            encode_type(element_type, output);
        }
        VmInstruction::ArrayGetBorrow {
            dst,
            value,
            index,
            unique,
            element_type,
        } => {
            output.push(143);
            for register in [dst, value, index] {
                output.extend_from_slice(&register.to_le_bytes());
            }
            output.push(u8::from(*unique));
            encode_type(element_type, output);
        }
        VmInstruction::ArraySetMove {
            value,
            index,
            item,
            element_type,
        } => {
            output.push(144);
            for register in [value, index, item] {
                output.extend_from_slice(&register.to_le_bytes());
            }
            encode_type(element_type, output);
        }
        VmInstruction::ArrayEmpty { dst, element_type } => {
            output.push(145);
            output.extend_from_slice(&dst.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::ArrayPushMove {
            value,
            item,
            element_type,
        } => {
            output.push(146);
            output.extend_from_slice(&value.to_le_bytes());
            output.extend_from_slice(&item.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::ArrayPopMove {
            dst,
            value,
            element_type,
        } => {
            output.push(147);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::ArrayCapacity {
            dst,
            value,
            element_type,
        } => {
            output.push(148);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::ArrayReserve {
            value,
            additional,
            element_type,
        } => {
            output.push(149);
            output.extend_from_slice(&value.to_le_bytes());
            output.extend_from_slice(&additional.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::ArrayFinishDrained {
            value,
            element_type,
        } => {
            output.push(150);
            output.extend_from_slice(&value.to_le_bytes());
            encode_type(element_type, output);
        }
        VmInstruction::BytesConcat { dst, left, right } => {
            output.push(81);
            for register in [dst, left, right] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::BytesGet { dst, bytes, index } => {
            output.push(82);
            for register in [dst, bytes, index] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::BytesSlice {
            dst,
            bytes,
            start,
            end,
        } => {
            output.push(83);
            for register in [dst, bytes, start, end] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::BytesFromArrayMove { dst, value } => {
            output.push(84);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::BytesToArray { dst, value } => {
            output.push(85);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::U32CheckedAdd { dst, left, right }
        | VmInstruction::U32CheckedSub { dst, left, right }
        | VmInstruction::U32CheckedMul { dst, left, right }
        | VmInstruction::U32CheckedDiv { dst, left, right }
        | VmInstruction::U32CheckedRem { dst, left, right }
        | VmInstruction::U32WrappingAdd { dst, left, right }
        | VmInstruction::U32WrappingSub { dst, left, right }
        | VmInstruction::U32WrappingMul { dst, left, right }
        | VmInstruction::U32WrappingShl { dst, left, right }
        | VmInstruction::U32WrappingShr { dst, left, right }
        | VmInstruction::U32CheckedShl { dst, left, right }
        | VmInstruction::U32CheckedShr { dst, left, right }
        | VmInstruction::U32Eq { dst, left, right }
        | VmInstruction::U32Lt { dst, left, right }
        | VmInstruction::U32Le { dst, left, right } => {
            output.push(match value {
                VmInstruction::U32CheckedAdd { .. } => 87,
                VmInstruction::U32CheckedSub { .. } => 88,
                VmInstruction::U32CheckedMul { .. } => 89,
                VmInstruction::U32CheckedDiv { .. } => 90,
                VmInstruction::U32CheckedRem { .. } => 91,
                VmInstruction::U32WrappingAdd { .. } => 92,
                VmInstruction::U32WrappingSub { .. } => 93,
                VmInstruction::U32WrappingMul { .. } => 94,
                VmInstruction::U32WrappingShl { .. } => 95,
                VmInstruction::U32WrappingShr { .. } => 96,
                VmInstruction::U32CheckedShl { .. } => 97,
                VmInstruction::U32CheckedShr { .. } => 98,
                VmInstruction::U32Eq { .. } => 99,
                VmInstruction::U32Lt { .. } => 100,
                VmInstruction::U32Le { .. } => 101,
                _ => unreachable!("instruction family matched above"),
            });
            for register in [dst, left, right] {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
        VmInstruction::U32ToUsize { dst, value } => {
            output.push(102);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::UsizeToU32Checked { dst, value } => {
            output.push(103);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU32Checked { dst, value } => {
            output.push(116);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU32Wrapping { dst, value } => {
            output.push(117);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToUsizeChecked { dst, value } => {
            output.push(118);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToUsizeWrapping { dst, value } => {
            output.push(119);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU8Checked { dst, value } => {
            output.push(120);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU8Wrapping { dst, value } => {
            output.push(121);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU16Checked { dst, value } => {
            output.push(122);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU16Wrapping { dst, value } => {
            output.push(123);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI16Checked { dst, value } => {
            output.push(124);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI16Wrapping { dst, value } => {
            output.push(125);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI32Checked { dst, value } => {
            output.push(126);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI32Wrapping { dst, value } => {
            output.push(127);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI8Checked { dst, value } => {
            output.push(128);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI8Wrapping { dst, value } => {
            output.push(129);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU64Checked { dst, value } => {
            output.push(130);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU64Wrapping { dst, value } => {
            output.push(131);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToIsizeChecked { dst, value } => {
            output.push(132);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToIsizeWrapping { dst, value } => {
            output.push(133);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU128Checked { dst, value } => {
            output.push(134);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToU128Wrapping { dst, value } => {
            output.push(135);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI128Checked { dst, value } => {
            output.push(136);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::I64ToI128Wrapping { dst, value } => {
            output.push(137);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::MakeCallable {
            dst,
            callee,
            captures,
            environment,
        } => {
            output.push(29);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&callee.0.as_bytes());
            output.extend_from_slice(&(captures.len() as u64).to_le_bytes());
            for capture in captures {
                output.extend_from_slice(&capture.to_le_bytes());
            }
            encode_capture_environment(environment.as_ref(), output);
        }
        VmInstruction::MakeLabel {
            dst,
            brand_owner,
            brand_label,
            target,
            destination,
        } => {
            output.push(71);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&brand_owner.0.as_bytes());
            output.extend_from_slice(&brand_label.to_le_bytes());
            output.extend_from_slice(&target.to_le_bytes());
            output.extend_from_slice(&destination.to_le_bytes());
        }
        VmInstruction::CallIndirect {
            dst,
            callee,
            arguments,
        } => {
            output.push(30);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&callee.to_le_bytes());
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                output.extend_from_slice(&argument.to_le_bytes());
            }
        }
        VmInstruction::Jump { target } => {
            output.push(31);
            output.extend_from_slice(&target.to_le_bytes());
        }
        VmInstruction::BranchBool {
            condition,
            then_target,
            else_target,
        } => {
            output.push(32);
            output.extend_from_slice(&condition.to_le_bytes());
            output.extend_from_slice(&then_target.to_le_bytes());
            output.extend_from_slice(&else_target.to_le_bytes());
        }
        VmInstruction::Return { value } => {
            output.push(15);
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::Trap => output.push(43),
    }
}
fn encode_pattern(value: &VmPattern, output: &mut Vec<u8>) {
    match value {
        VmPattern::Any => output.push(0),
        VmPattern::Literal(value) => {
            output.push(1);
            output.extend_from_slice(&(value.len() as u64).to_le_bytes());
            output.extend_from_slice(value.as_bytes());
        }
        VmPattern::Tuple(values) => {
            output.push(2);
            output.extend_from_slice(&(values.len() as u64).to_le_bytes());
            for value in values {
                encode_pattern(value, output);
            }
        }
        VmPattern::Array { element, elements } => {
            output.push(5);
            encode_type(element, output);
            output.extend_from_slice(&(elements.len() as u64).to_le_bytes());
            for value in elements {
                encode_pattern(value, output);
            }
        }
        VmPattern::Record {
            definition,
            field_types,
            field_count,
            fields,
        } => {
            output.push(3);
            output.extend_from_slice(&definition.0.as_bytes());
            output.extend_from_slice(&field_count.to_le_bytes());
            output.extend_from_slice(&(field_types.len() as u64).to_le_bytes());
            for field_type in field_types {
                encode_type(field_type, output);
            }
            encode_pattern_fields(fields, output);
        }
        VmPattern::Enum {
            definition,
            variant,
            field_types,
            field_count,
            fields,
        } => {
            output.push(4);
            output.extend_from_slice(&definition.0.as_bytes());
            output.extend_from_slice(&variant.to_le_bytes());
            output.extend_from_slice(&field_count.to_le_bytes());
            output.extend_from_slice(&(field_types.len() as u64).to_le_bytes());
            for field_type in field_types {
                encode_type(field_type, output);
            }
            encode_pattern_fields(fields, output);
        }
    }
}
fn encode_cleanup_proof(value: &VmCleanupProof, output: &mut Vec<u8>) {
    output.extend_from_slice(&(value.moved_places.len() as u64).to_le_bytes());
    for place in &value.moved_places {
        output.extend_from_slice(&place.path.to_le_bytes());
        output.extend_from_slice(&place.binding.to_le_bytes());
        output.extend_from_slice(&(place.root.len() as u64).to_le_bytes());
        output.extend_from_slice(place.root.as_bytes());
        output.extend_from_slice(&(place.fields.len() as u64).to_le_bytes());
        for field in &place.fields {
            output.extend_from_slice(&field.to_le_bytes());
        }
    }
    output.extend_from_slice(&(value.active_loans.len() as u64).to_le_bytes());
    for loan in &value.active_loans {
        match &loan.owner {
            None => output.push(0),
            Some(owner) => {
                output.push(1);
                output.extend_from_slice(&(owner.len() as u64).to_le_bytes());
                output.extend_from_slice(owner.as_bytes());
            }
        }
        output.extend_from_slice(&loan.binding.to_le_bytes());
        output.extend_from_slice(&(loan.root.len() as u64).to_le_bytes());
        output.extend_from_slice(loan.root.as_bytes());
        output.extend_from_slice(&(loan.fields.len() as u64).to_le_bytes());
        for field in &loan.fields {
            output.extend_from_slice(&field.to_le_bytes());
        }
        output.push(u8::from(loan.unique));
    }
    encode_storage_erasure_witness(&value.storage_erasure, output);
}
fn encode_storage_erasure_witness(value: &VmStorageErasureWitness, output: &mut Vec<u8>) {
    match value {
        VmStorageErasureWitness::Missing => output.push(0),
        VmStorageErasureWitness::Verified {
            storages,
            actions,
            protected_registers,
        } => {
            output.push(1);
            output.extend_from_slice(&(storages.len() as u64).to_le_bytes());
            for storage in storages {
                output.extend_from_slice(&storage.storage.to_le_bytes());
                output.extend_from_slice(&storage.binding.to_le_bytes());
                output.extend_from_slice(&storage.value_register.to_le_bytes());
                output.push(u8::from(storage.initialized));
                match storage.drop_flag {
                    None => output.push(0),
                    Some(drop_flag) => {
                        output.push(1);
                        output.extend_from_slice(&drop_flag.to_le_bytes());
                    }
                }
            }
            output.extend_from_slice(&(actions.len() as u64).to_le_bytes());
            for action in actions {
                match action {
                    VmStorageErasureAction::EndBorrow { storage } => {
                        output.push(0);
                        output.extend_from_slice(&storage.to_le_bytes());
                    }
                    VmStorageErasureAction::Protect { storage, register } => {
                        output.push(1);
                        output.extend_from_slice(&storage.to_le_bytes());
                        output.extend_from_slice(&register.to_le_bytes());
                    }
                    VmStorageErasureAction::Destroy { storage } => {
                        output.push(2);
                        output.extend_from_slice(&storage.to_le_bytes());
                    }
                    VmStorageErasureAction::SetDropFlag {
                        drop_flag,
                        initialized,
                    } => {
                        output.push(3);
                        output.extend_from_slice(&drop_flag.to_le_bytes());
                        output.push(u8::from(*initialized));
                    }
                    VmStorageErasureAction::StorageDead { storage } => {
                        output.push(4);
                        output.extend_from_slice(&storage.to_le_bytes());
                    }
                }
            }
            output.extend_from_slice(&(protected_registers.len() as u64).to_le_bytes());
            for register in protected_registers {
                output.extend_from_slice(&register.to_le_bytes());
            }
        }
    }
}
fn encode_pattern_fields(fields: &[VmPatternField], output: &mut Vec<u8>) {
    output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
    for field in fields {
        output.extend_from_slice(&field.index.to_le_bytes());
        encode_type(&field.ty, output);
        encode_pattern(&field.pattern, output);
    }
}
fn execute_with_arguments(
    program: &CandidateVmProgram,
    definition: DefKey,
    arguments: &[VmValue],
    depth: u32,
    budget: &mut ExecutionBudget,
) -> Result<VmValue, VmArtifactError> {
    let mut host = None;
    execute_with_arguments_with_host(program, definition, arguments, depth, budget, &mut host)
}

fn execute_with_arguments_with_host(
    program: &CandidateVmProgram,
    definition: DefKey,
    arguments: &[VmValue],
    depth: u32,
    budget: &mut ExecutionBudget,
    host: &mut Option<&mut dyn VmHost>,
) -> Result<VmValue, VmArtifactError> {
    execute_program_profiled(program, definition, arguments, depth, budget, host, None)
}

// Recycling leaves the caller stack unchanged. Loans into surviving callers
// therefore retain their coordinates, while loans into the current register
// frame must prevent recycling. Referenced owners and captured shared storage
// must themselves be free of frame-relative capabilities: a surviving outer
// allocation can still contain a label belonging to the frame being recycled.
// The scan is iterative, budgeted, and measured.
fn recyclable_tail_arguments(
    registers: &[Option<VmValue>],
    arguments: &[u32],
    callers: &[RuntimeProgramCaller],
    budget: &mut ExecutionBudget,
    profile: &mut VmAuthoringProfile,
) -> Result<bool, VmArtifactError> {
    let mut pending = Vec::new();
    budget.reserve_allocation(arguments.len())?;
    for argument in arguments {
        pending.push((registers[*argument as usize].as_ref().ok_or(
            VmArtifactError::ReadBeforeWrite { register: *argument },
        )?, true));
    }
    while let Some((value, allow_callers)) = pending.pop() {
        budget.tick()?;
        profile.inspected_tail_argument_elements += 1;
        let fields = match value {
            VmValue::Reference {
                target: target @ ReferenceTarget::Caller { caller_depth, .. }, ..
            } if allow_callers && (*caller_depth as usize) < callers.len() => {
                budget.reserve_allocation(1)?;
                // Deliberately inspect the whole owner, not only a projection.
                // Nested frame-relative loans fail closed rather than following
                // an unbounded/cyclic reference graph without a retention proof.
                pending.push((reference_target(registers, callers, target)?, false));
                continue;
            }
            VmValue::Reference {
                target: ReferenceTarget::Captured(value), unique: false, ..
            } => {
                budget.reserve_allocation(1)?;
                pending.push((value.as_ref(), false));
                continue;
            }
            VmValue::Reference { .. } | VmValue::Label { .. } | VmValue::Resumption { .. } => {
                return Ok(false);
            }
            VmValue::Tuple(fields)
            | VmValue::Array { values: fields, .. }
            | VmValue::Record { fields, .. }
            | VmValue::Enum { fields, .. }
            | VmValue::Callable { captures: fields, .. } => fields.as_ref(),
            _ => continue,
        };
        budget.reserve_allocation(fields.len())?;
        pending.extend(fields.iter().map(|value| (value, allow_callers)));
    }
    Ok(true)
}

// Block results may forward a call result through Copy/Move before returning.
// Only a straight result-forwarding chain is erasable here: no stores, drops,
// calls, jumps, or other work may be skipped. Charge even unsuccessful scans.
fn tail_return_suffix(
    instructions: &[VmInstruction],
    mut result: u32,
    budget: &mut ExecutionBudget,
) -> Result<bool, VmArtifactError> {
    for instruction in instructions {
        budget.tick()?;
        match instruction {
            VmInstruction::Copy { dst, src } | VmInstruction::Move { dst, src } if *src == result => {
                result = *dst;
            }
            VmInstruction::Return { value } => return Ok(*value == result),
            _ => return Ok(false),
        }
    }
    Ok(false)
}

fn execute_program_profiled(
    program: &CandidateVmProgram,
    definition: DefKey,
    arguments: &[VmValue],
    depth: u32,
    budget: &mut ExecutionBudget,
    host: &mut Option<&mut dyn VmHost>,
    mut profile: Option<&mut VmAuthoringProfile>,
) -> Result<VmValue, VmArtifactError> {
    if depth >= budget.limits.max_call_depth {
        return Err(VmArtifactError::CallDepthLimit {
            limit: budget.limits.max_call_depth,
        });
    }
    let function = program
        .functions
        .get(&definition)
        .ok_or(VmArtifactError::MissingFunction { definition })?;
    require_execution_contract(function, budget)?;
    if function.parameters != arguments.len() as u32 {
        return Err(VmArtifactError::CallArity {
            expected: function.parameters,
            found: arguments.len() as u32,
        });
    }
    budget.reserve_allocation(function.registers.len())?;
    let mut registers = vec![None; function.registers.len()];
    for (index, value) in arguments.iter().enumerate() {
        registers[index] = Some(value.clone());
    }
    // The program engine deliberately keeps ordinary calls explicit rather
    // than recursively invoking a fresh interpreter. Handler frames are
    // dynamically scoped, so a `Perform` in any callee must be able to find
    // a frame installed by an ancestor. A continuation records this exact
    // call stack and restores it on `Resume`.
    let mut definition = definition;
    let mut callers = Vec::<RuntimeProgramCaller>::new();
    let mut handlers = Vec::<RuntimeHandlerFrame>::new();
    let mut resumption_returns = Vec::<RuntimeResumptionReturn>::new();
    let mut next_handler_id = 0u64;
    let mut pc = 0usize;
    loop {
        if let Some(profile) = profile.as_deref_mut() {
            profile.peak_call_depth = profile.peak_call_depth.max(
                depth.saturating_add(callers.len() as u32).saturating_add(1),
            );
        }
        let function = program
            .functions
            .get(&definition)
            .ok_or(VmArtifactError::MissingFunction { definition })?;
        require_execution_contract(function, budget)?;
        let Some(instruction) = function.instructions.get(pc) else {
            return Err(VmArtifactError::NoReturn);
        };
        budget.tick()?;
        match instruction {
            VmInstruction::DeclareResult { .. } => {}
            VmInstruction::ConstUnit { dst } => registers[*dst as usize] = Some(VmValue::Unit),
            VmInstruction::MemoryIntrinsic { dst, primitive, types, arguments } => {
                registers[*dst as usize] = Some(execute_memory_intrinsic(*primitive, types, arguments, function, &mut registers, budget)?);
            }
            VmInstruction::ConstI64 { dst, value } => {
                registers[*dst as usize] = Some(VmValue::I64(*value))
            }
            VmInstruction::ConstU8 { dst, value } => {
                registers[*dst as usize] = Some(VmValue::U8(*value))
            }
            VmInstruction::ConstU16 { dst, value } => {
                registers[*dst as usize] = Some(VmValue::U16(*value))
            }
            VmInstruction::ConstU32 { dst, value } => {
                registers[*dst as usize] = Some(VmValue::U32(*value))
            }
            VmInstruction::ConstU64 { dst, value } => {
                registers[*dst as usize] = Some(VmValue::U64(*value))
            }
            VmInstruction::ConstUsize { dst, value } => {
                registers[*dst as usize] = Some(VmValue::Usize(*value))
            }
            VmInstruction::ConstU128 { dst, value } => {
                registers[*dst as usize] = Some(VmValue::U128(*value))
            }
            VmInstruction::ConstI8 { dst, value } => {
                registers[*dst as usize] = Some(VmValue::I8(*value))
            }
            VmInstruction::ConstI16 { dst, value } => {
                registers[*dst as usize] = Some(VmValue::I16(*value))
            }
            VmInstruction::ConstI32 { dst, value } => {
                registers[*dst as usize] = Some(VmValue::I32(*value))
            }
            VmInstruction::ConstIsize { dst, value } => {
                registers[*dst as usize] = Some(VmValue::Isize(*value))
            }
            VmInstruction::ConstI128 { dst, value } => {
                registers[*dst as usize] = Some(VmValue::I128(*value))
            }
            VmInstruction::ConstF64 { dst, bits } => {
                registers[*dst as usize] =
                    Some(VmValue::F64(canonical_vm_f64(f64::from_bits(*bits))))
            }
            VmInstruction::ConstF32 { dst, bits } => {
                registers[*dst as usize] =
                    Some(VmValue::F32(canonical_vm_f32(f32::from_bits(*bits))))
            }
            VmInstruction::FloatIntrinsic {
                dst,
                primitive,
                arguments,
            } => {
                registers[*dst as usize] =
                    Some(execute_float_intrinsic(*primitive, arguments, &registers)?)
            }
            VmInstruction::IntIntrinsic {
                dst,
                primitive,
                scalar,
                arguments,
            } => {
                registers[*dst as usize] = Some(execute_integer_intrinsic(
                    *primitive, *scalar, arguments, &registers,
                )?)
            }
            VmInstruction::ConstBool { dst, value } => {
                registers[*dst as usize] = Some(VmValue::Bool(*value))
            }
            VmInstruction::ConstChar { dst, value } => {
                registers[*dst as usize] = Some(VmValue::Char(
                    char::from_u32(*value).expect("verified char"),
                ))
            }
            VmInstruction::ConstText { dst, value } => {
                budget.reserve_value("text bytes", value.len())?;
                registers[*dst as usize] = Some(VmValue::Text(Arc::from(value.as_str())));
            }
            VmInstruction::ConstStaticData {
                dst,
                tag,
                alignment,
                bytes,
            } => {
                budget.reserve_value("static-data bytes", bytes.len())?;
                registers[*dst as usize] = Some(VmValue::StaticData {
                    tag: *tag,
                    alignment: *alignment,
                    bytes: Arc::from(bytes.as_slice()),
                    offset: 0,
                    length: bytes.len(),
                });
            }
            VmInstruction::StaticLen { dst, value } => {
                let (_, _, length) = expect_static_utf8(
                    registers[*value as usize].as_ref().expect("verified register"),
                )?;
                registers[*dst as usize] = Some(VmValue::Usize(length as u64));
            }
            VmInstruction::StaticSubslice { dst, value, start, length } => {
                let (bytes, offset, available) = expect_static_utf8(
                    registers[*value as usize].as_ref().expect("verified register"),
                )?;
                let start = expect_usize(registers[*start as usize].as_ref().expect("verified register"))? as usize;
                let length = expect_usize(registers[*length as usize].as_ref().expect("verified register"))? as usize;
                let end = start.checked_add(length).filter(|end| *end <= available)
                    .ok_or(VmArtifactError::InvalidRegister { register: start as u32 })?;
                registers[*dst as usize] = Some(VmValue::StaticData {
                    tag: 0x4752_414e_4449_4f53_455f_5354_4154_4943,
                    alignment: 1,
                    bytes,
                    offset: offset + start,
                    length: end - start,
                });
            }
            VmInstruction::StaticGetBorrowShared { dst, value, index } => {
                let (bytes, offset, length) = expect_static_utf8(
                    registers[*value as usize].as_ref().expect("verified register"),
                )?;
                let index = expect_usize(registers[*index as usize].as_ref().expect("verified register"))? as usize;
                let byte = *bytes.get(offset.checked_add(index).filter(|_| index < length).ok_or(
                    VmArtifactError::InvalidRegister { register: index as u32 },
                )?).ok_or(VmArtifactError::InvalidRegister { register: index as u32 })?;
                registers[*dst as usize] = Some(VmValue::Reference {
                    target: ReferenceTarget::Captured(Arc::new(VmValue::U8(byte))),
                    fields: Arc::from([]),
                    unique: false,
                    referent: VmType::U8,
                });
            }
            VmInstruction::StaticAsArrayBorrow { dst, value } => {
                let (bytes, offset, length) = expect_static_utf8(registers[*value as usize].as_ref().expect("verified register"))?;
                registers[*dst as usize] = Some(VmValue::Reference { target: ReferenceTarget::Captured(Arc::new(VmValue::StaticArray { bytes, offset, length })), fields: Arc::from([]), unique: false, referent: VmType::Array(Box::new(VmType::U8)) });
            }
            VmInstruction::TextByteLen { dst, value } => {
                let text = expect_text(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                registers[*dst as usize] = Some(VmValue::Usize(text.len() as u64));
            }
            VmInstruction::TextConcat { dst, left, right } => {
                let left = expect_text(
                    registers[*left as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let right = expect_text(
                    registers[*right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let length = left.len().checked_add(right.len()).ok_or(
                    VmArtifactError::AllocationLimit {
                        limit: budget.limits.max_allocation_elements,
                    },
                )?;
                budget.reserve_value("text bytes", length)?;
                registers[*dst as usize] = Some(VmValue::Text(Arc::from(format!("{left}{right}"))));
            }
            VmInstruction::TextEq { dst, left, right } => {
                let left = expect_text(
                    registers[*left as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let right = expect_text(
                    registers[*right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                registers[*dst as usize] = Some(VmValue::U32(u32::from(left == right)));
            }
            VmInstruction::TextFromUtf8Checked { dst, value } => {
                let bytes = expect_bytes(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                budget.reserve_value("text bytes", bytes.len())?;
                let text =
                    String::from_utf8(bytes.to_vec()).map_err(|_| VmArtifactError::InvalidUtf8)?;
                registers[*dst as usize] = Some(VmValue::Text(Arc::from(text)));
            }
            VmInstruction::TextAsBytes { dst, value } => {
                let text = expect_text(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                budget.reserve_value("bytes", text.len())?;
                registers[*dst as usize] = Some(VmValue::Bytes(Arc::from(text.as_bytes())));
            }
            VmInstruction::CharFromU32Checked { dst, value } => {
                let value = expect_u32(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let character =
                    char::from_u32(value).ok_or(VmArtifactError::InvalidChar { value })?;
                registers[*dst as usize] = Some(VmValue::Char(character));
            }
            VmInstruction::CharToU32 { dst, value } => {
                let value = expect_char(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                registers[*dst as usize] = Some(VmValue::U32(value as u32));
            }
            VmInstruction::BytesLen { dst, value } => {
                let value = expect_bytes(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                registers[*dst as usize] = Some(VmValue::Usize(value.len() as u64));
            }
            VmInstruction::BytesConcat { dst, left, right } => {
                let left = expect_bytes(
                    registers[*left as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let right = expect_bytes(
                    registers[*right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let length = left.len().checked_add(right.len()).ok_or(
                    VmArtifactError::AllocationLimit {
                        limit: budget.limits.max_allocation_elements,
                    },
                )?;
                budget.reserve_value("bytes", length)?;
                let mut value = left.to_vec();
                value.extend_from_slice(&right);
                registers[*dst as usize] = Some(VmValue::Bytes(Arc::from(value)));
            }
            VmInstruction::BytesGet { dst, bytes, index } => {
                let bytes = expect_bytes(
                    registers[*bytes as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let index = expect_usize(
                    registers[*index as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as usize;
                let value = *bytes.get(index).ok_or(VmArtifactError::InvalidRegister {
                    register: index as u32,
                })?;
                registers[*dst as usize] = Some(VmValue::U8(value));
            }
            VmInstruction::BytesSlice {
                dst,
                bytes,
                start,
                end,
            } => {
                let bytes = expect_bytes(
                    registers[*bytes as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let start = expect_usize(
                    registers[*start as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as usize;
                let end = expect_usize(
                    registers[*end as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as usize;
                let value = bytes
                    .get(start..end)
                    .ok_or(VmArtifactError::InvalidRegister {
                        register: start as u32,
                    })?;
                budget.reserve_value("bytes", value.len())?;
                registers[*dst as usize] = Some(VmValue::Bytes(Arc::from(value)));
            }
            VmInstruction::BytesFromArrayMove { dst, value } => {
                let values = match registers[*value as usize]
                    .as_ref()
                    .expect("verified register")
                {
                    VmValue::Array { values, .. } => values,
                    value => {
                        return Err(VmArtifactError::ResultType {
                            expected: VmType::Array(Box::new(VmType::U8)),
                            found: value.ty(),
                        });
                    }
                };
                budget.reserve_value("bytes", values.len())?;
                let value = values
                    .iter()
                    .map(expect_u8)
                    .collect::<Result<Vec<_>, _>>()?;
                registers[*dst as usize] = Some(VmValue::Bytes(Arc::from(value)));
            }
            VmInstruction::BytesToArray { dst, value } => {
                let bytes = expect_bytes(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                budget.reserve_value("array elements", bytes.len())?;
                let values = bytes.iter().copied().map(VmValue::U8).collect::<Vec<_>>();
                registers[*dst as usize] = Some(VmValue::Array {
                    capacity: values.len(),
                    values: Arc::from(values),
                });
            }
            VmInstruction::BytesUtf8ValidUpTo { dst, value } => {
                let bytes = expect_bytes(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                registers[*dst as usize] = Some(VmValue::Usize(valid_utf8_prefix(&bytes) as u64));
            }
            VmInstruction::ArrayUtf8ValidUpTo { dst, value } => {
                let valid = referenced_array_utf8_valid_prefix(
                    &registers,
                    &callers,
                    registers[*value as usize].as_ref().expect("verified register"),
                )?;
                registers[*dst as usize] = Some(VmValue::Usize(valid as u64));
            }
            VmInstruction::Blake3 { dst, value } => {
                let bytes = expect_bytes(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                budget.reserve_value("bytes", blake3::OUT_LEN)?;
                registers[*dst as usize] = Some(VmValue::Bytes(Arc::from(
                    blake3::hash(&bytes).as_bytes().as_slice(),
                )));
            }
            instruction @ (VmInstruction::ArrayNew { .. }
            | VmInstruction::ArrayLen { .. }
            | VmInstruction::ArrayGetCopy { .. }
            | VmInstruction::ArrayGetMove { .. }
            | VmInstruction::ArrayGetBorrow { .. }
            | VmInstruction::ArraySetMove { .. }
            | VmInstruction::ArrayEmpty { .. }
            | VmInstruction::ArrayPushMove { .. }
            | VmInstruction::ArrayPushUtf8Char { .. }
            | VmInstruction::ArrayInsertUtf8FromSlice { .. }
            | VmInstruction::ArrayPopUtf8Char { .. }
            | VmInstruction::ArrayUtf8CharAt { .. }
            | VmInstruction::ArrayExtendFromSlice { .. }
            | VmInstruction::ArrayInsertMove { .. }
            | VmInstruction::ArrayRemoveMove { .. }
            | VmInstruction::ArrayAppendMove { .. }
            | VmInstruction::ArrayTruncateDiscard { .. }
            | VmInstruction::ArrayReverseMove { .. }
            | VmInstruction::ArraySplitOffMove { .. }
            | VmInstruction::ArraySplitBorrowUnique { .. }
            | VmInstruction::ArrayInsertFromSlice { .. }
            | VmInstruction::ArrayPopMove { .. }
            | VmInstruction::ArrayCapacity { .. }
            | VmInstruction::ArrayReserve { .. }
            | VmInstruction::ArrayFinishDrained { .. }) => {
                execute_array_primitive(&mut registers, &mut callers, instruction, budget)?
            }
            VmInstruction::U32CheckedAdd { dst, left, right } => {
                u32_checked_binary(&mut registers, *dst, *left, *right, u32::checked_add)?
            }
            VmInstruction::U32CheckedSub { dst, left, right } => {
                u32_checked_binary(&mut registers, *dst, *left, *right, u32::checked_sub)?
            }
            VmInstruction::U32CheckedMul { dst, left, right } => {
                u32_checked_binary(&mut registers, *dst, *left, *right, u32::checked_mul)?
            }
            VmInstruction::U32CheckedDiv { dst, left, right } => {
                u32_checked_division(&mut registers, *dst, *left, *right, false)?
            }
            VmInstruction::U32CheckedRem { dst, left, right } => {
                u32_checked_division(&mut registers, *dst, *left, *right, true)?
            }
            VmInstruction::U32WrappingAdd { dst, left, right } => {
                u32_wrapping_binary(&mut registers, *dst, *left, *right, u32::wrapping_add)?
            }
            VmInstruction::U32WrappingSub { dst, left, right } => {
                u32_wrapping_binary(&mut registers, *dst, *left, *right, u32::wrapping_sub)?
            }
            VmInstruction::U32WrappingMul { dst, left, right } => {
                u32_wrapping_binary(&mut registers, *dst, *left, *right, u32::wrapping_mul)?
            }
            VmInstruction::U32WrappingShl { dst, left, right } => {
                u32_wrapping_binary(&mut registers, *dst, *left, *right, u32::wrapping_shl)?
            }
            VmInstruction::U32WrappingShr { dst, left, right } => {
                u32_wrapping_binary(&mut registers, *dst, *left, *right, u32::wrapping_shr)?
            }
            VmInstruction::U32CheckedShl { dst, left, right } => {
                u32_checked_binary(&mut registers, *dst, *left, *right, u32::checked_shl)?
            }
            VmInstruction::U32CheckedShr { dst, left, right } => {
                u32_checked_binary(&mut registers, *dst, *left, *right, u32::checked_shr)?
            }
            VmInstruction::U32Eq { dst, left, right } => {
                u32_compare(&mut registers, *dst, *left, *right, |left, right| {
                    left == right
                })?
            }
            VmInstruction::U32Lt { dst, left, right } => {
                u32_compare(&mut registers, *dst, *left, *right, |left, right| {
                    left < right
                })?
            }
            VmInstruction::U32Le { dst, left, right } => {
                u32_compare(&mut registers, *dst, *left, *right, |left, right| {
                    left <= right
                })?
            }
            VmInstruction::U32ToUsize { dst, value } => {
                let value = expect_u32(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                registers[*dst as usize] = Some(VmValue::Usize(value as u64));
            }
            VmInstruction::UsizeToU32Checked { dst, value } => {
                let value = expect_usize(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let value =
                    u32::try_from(value).map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[*dst as usize] = Some(VmValue::U32(value));
            }
            VmInstruction::I64ToU32Checked { dst, value } => {
                let value = expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let value =
                    u32::try_from(value).map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[*dst as usize] = Some(VmValue::U32(value));
            }
            VmInstruction::I64ToU32Wrapping { dst, value } => {
                registers[*dst as usize] = Some(VmValue::U32(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as u32));
            }
            VmInstruction::I64ToUsizeChecked { dst, value } => {
                let value = expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let value =
                    u64::try_from(value).map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[*dst as usize] = Some(VmValue::Usize(value));
            }
            VmInstruction::I64ToUsizeWrapping { dst, value } => {
                registers[*dst as usize] = Some(VmValue::Usize(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as u64));
            }
            VmInstruction::I64ToU8Checked { dst, value } => {
                let value = expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let value = u8::try_from(value).map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[*dst as usize] = Some(VmValue::U8(value));
            }
            VmInstruction::I64ToU8Wrapping { dst, value } => {
                registers[*dst as usize] = Some(VmValue::U8(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as u8));
            }
            VmInstruction::I64ToU16Checked { dst, value } => {
                let value = expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let value =
                    u16::try_from(value).map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[*dst as usize] = Some(VmValue::U16(value));
            }
            VmInstruction::I64ToU16Wrapping { dst, value } => {
                registers[*dst as usize] = Some(VmValue::U16(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as u16));
            }
            VmInstruction::I64ToI16Checked { dst, value } => {
                let value = i16::try_from(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?)
                .map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[*dst as usize] = Some(VmValue::I16(value));
            }
            VmInstruction::I64ToI16Wrapping { dst, value } => {
                registers[*dst as usize] = Some(VmValue::I16(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as i16));
            }
            VmInstruction::I64ToI32Checked { dst, value } => {
                let value = i32::try_from(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?)
                .map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[*dst as usize] = Some(VmValue::I32(value));
            }
            VmInstruction::I64ToI32Wrapping { dst, value } => {
                registers[*dst as usize] = Some(VmValue::I32(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as i32));
            }
            VmInstruction::I64ToI8Checked { dst, value } => {
                let value = i8::try_from(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?)
                .map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[*dst as usize] = Some(VmValue::I8(value));
            }
            VmInstruction::I64ToI8Wrapping { dst, value } => {
                registers[*dst as usize] = Some(VmValue::I8(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as i8));
            }
            VmInstruction::I64ToU64Checked { dst, value } => {
                let value = u64::try_from(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?)
                .map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[*dst as usize] = Some(VmValue::U64(value));
            }
            VmInstruction::I64ToU64Wrapping { dst, value } => {
                registers[*dst as usize] = Some(VmValue::U64(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as u64));
            }
            VmInstruction::I64ToIsizeChecked { dst, value } => {
                registers[*dst as usize] = Some(VmValue::Isize(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?));
            }
            VmInstruction::I64ToIsizeWrapping { dst, value } => {
                registers[*dst as usize] = Some(VmValue::Isize(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?));
            }
            VmInstruction::I64ToU128Checked { dst, value } => {
                let value = u128::try_from(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?)
                .map_err(|_| VmArtifactError::ArithmeticOverflow)?;
                registers[*dst as usize] = Some(VmValue::U128(value));
            }
            VmInstruction::I64ToU128Wrapping { dst, value } => {
                registers[*dst as usize] = Some(VmValue::U128(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as u128));
            }
            VmInstruction::I64ToI128Checked { dst, value } => {
                registers[*dst as usize] = Some(VmValue::I128(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as i128));
            }
            VmInstruction::I64ToI128Wrapping { dst, value } => {
                registers[*dst as usize] = Some(VmValue::I128(expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )? as i128));
            }
            VmInstruction::MakeTuple { dst, fields } => {
                budget.reserve_value("tuple fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| {
                        registers[*field as usize]
                            .as_ref()
                            .expect("verified register")
                            .clone()
                    })
                    .collect::<Vec<_>>();
                registers[*dst as usize] = Some(VmValue::Tuple(Arc::from(values)));
            }
            VmInstruction::MakeArray { dst, fields, .. } => {
                budget.reserve_value("array elements", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| {
                        registers[*field as usize]
                            .as_ref()
                            .expect("verified register")
                            .clone()
                    })
                    .collect::<Vec<_>>();
                registers[*dst as usize] = Some(VmValue::Array {
                    capacity: values.len(),
                    values: Arc::from(values),
                });
            }
            VmInstruction::MakeRecord {
                dst,
                definition,
                fields,
                ..
            } => {
                budget.reserve_value("record fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| {
                        registers[*field as usize]
                            .as_ref()
                            .expect("verified register")
                            .clone()
                    })
                    .collect::<Vec<_>>();
                let signature = register_type(function, *dst)?;
                registers[*dst as usize] = Some(VmValue::Record {
                    definition: *definition,
                    fields: Arc::from(values),
                    signature,
                });
            }
            VmInstruction::MakeEnum {
                dst,
                definition,
                variant,
                fields,
                ..
            } => {
                budget.reserve_value("enum fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| {
                        registers[*field as usize]
                            .as_ref()
                            .expect("verified register")
                            .clone()
                    })
                    .collect::<Vec<_>>();
                let signature = register_type(function, *dst)?;
                registers[*dst as usize] = Some(VmValue::Enum {
                    definition: *definition,
                    variant: *variant,
                    fields: Arc::from(values),
                    signature,
                });
            }
            VmInstruction::ProjectRecord {
                dst,
                base,
                index,
                field_count,
                field_type,
            } => {
                let fields = match registers[*base as usize]
                    .as_ref()
                    .expect("verified register")
                {
                    VmValue::Record { fields, .. } | VmValue::Enum { fields, .. } => fields,
                    _ => return Err(VmArtifactError::InvalidRegister { register: *base }),
                };
                if fields.len() != *field_count as usize {
                    return Err(VmArtifactError::CallArity {
                        expected: *field_count,
                        found: fields.len() as u32,
                    });
                }
                let value = fields
                    .get(*index as usize)
                    .ok_or(VmArtifactError::InvalidRegister { register: *index })?
                    .clone();
                if !value_matches_vm_type(&value, field_type) {
                    return Err(VmArtifactError::ResultType {
                        expected: field_type.clone(),
                        found: value.ty(),
                    });
                }
                registers[*dst as usize] = Some(value);
            }
            VmInstruction::ProjectTuple {
                dst,
                base,
                index,
                field_count,
                ..
            } => {
                let VmValue::Tuple(fields) = registers[*base as usize]
                    .as_ref()
                    .expect("verified register")
                else {
                    return Err(VmArtifactError::InvalidRegister { register: *base });
                };
                if fields.len() != *field_count as usize {
                    return Err(VmArtifactError::CallArity {
                        expected: *field_count,
                        found: fields.len() as u32,
                    });
                }
                registers[*dst as usize] = Some(
                    fields
                        .get(*index as usize)
                        .ok_or(VmArtifactError::InvalidRegister { register: *index })?
                        .clone(),
                );
            }
            VmInstruction::ProjectArray {
                dst,
                base,
                index,
                field_count,
                ..
            } => {
                let VmValue::Array { values: fields, .. } = registers[*base as usize]
                    .as_ref()
                    .expect("verified register")
                else {
                    return Err(VmArtifactError::InvalidRegister { register: *base });
                };
                if fields.len() != *field_count as usize {
                    return Err(VmArtifactError::CallArity {
                        expected: *field_count,
                        found: fields.len() as u32,
                    });
                }
                registers[*dst as usize] = Some(
                    fields
                        .get(*index as usize)
                        .ok_or(VmArtifactError::InvalidRegister { register: *index })?
                        .clone(),
                );
            }
            VmInstruction::UpdateRecord {
                dst,
                base,
                index,
                field_count,
                value,
                ..
            } => {
                let VmValue::Record {
                    definition,
                    fields,
                    signature,
                } = registers[*base as usize]
                    .as_ref()
                    .expect("verified register")
                else {
                    return Err(VmArtifactError::InvalidRegister { register: *base });
                };
                if fields.len() != *field_count as usize {
                    return Err(VmArtifactError::CallArity {
                        expected: *field_count,
                        found: fields.len() as u32,
                    });
                }
                budget.reserve_value("record update fields", fields.len())?;
                let mut fields = fields.to_vec();
                let index = *index as usize;
                let Some(field) = fields.get_mut(index) else {
                    return Err(VmArtifactError::InvalidRegister {
                        register: index as u32,
                    });
                };
                *field = registers[*value as usize]
                    .as_ref()
                    .expect("verified register")
                    .clone();
                registers[*dst as usize] = Some(VmValue::Record {
                    definition: *definition,
                    fields: Arc::from(fields),
                    signature: signature.clone(),
                });
            }
            VmInstruction::PatternTest {
                dst,
                subject,
                pattern,
            } => {
                registers[*dst as usize] = Some(VmValue::Bool(matches_pattern(
                    registers[*subject as usize]
                        .as_ref()
                        .expect("verified register"),
                    pattern,
                )));
            }
            VmInstruction::Perform {
                dst,
                effect,
                effect_arguments,
                operation,
                arguments,
            } => {
                budget.reserve_value("handler payload", arguments.len())?;
                let values = arguments
                    .iter()
                    .map(|argument| {
                        registers[*argument as usize].clone().ok_or(
                            VmArtifactError::ReadBeforeWrite {
                                register: *argument,
                            },
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let Some(index) = handlers.iter().rposition(|frame| {
                    frame.suspended.is_none()
                        && frame.effect == *effect
                        && frame.effect_arguments == *effect_arguments
                        && frame.operation == *operation
                }) else {
                    return Err(VmArtifactError::UnhandledEffect {
                        effect: *effect,
                        effect_arguments: effect_arguments.clone(),
                        operation: *operation,
                    });
                };
                let above = handlers.split_off(index + 1);
                if handlers
                    .iter()
                    .filter(|handler| handler.suspended.is_some())
                    .count()
                    >= budget.limits.max_retained_continuations as usize
                {
                    return Err(VmArtifactError::ContinuationLimit {
                        limit: budget.limits.max_retained_continuations,
                    });
                }
                let owner_depth = handlers[index].call_depth;
                if owner_depth > callers.len() {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                let payload_destinations = handlers[index].payload_destinations.clone();
                let handler_target = handlers[index].target;
                if payload_destinations.len() != values.len() {
                    return Err(VmArtifactError::CallArity {
                        expected: payload_destinations.len() as u32,
                        found: values.len() as u32,
                    });
                }
                budget.reserve_allocation(registers.len())?;
                let saved = registers.clone();
                let continuation_program = RuntimeProgramContinuation {
                    definition,
                    callers: callers.clone(),
                };
                budget.reserve_value("handler clause payload", values.len())?;
                let clause_values = values.iter().cloned().map(|value| {
                    transfer_to_ancestor_frame(value, &registers, &callers, owner_depth, budget)
                }).collect::<Result<Vec<_>, _>>()?;
                // A matching ancestor owns the handler clause. Discard the
                // active callee path from live execution only after storing
                // it in the continuation; `Resume` restores it below.
                if owner_depth < callers.len() {
                    let owner = callers
                        .get(owner_depth)
                        .cloned()
                        .ok_or(VmArtifactError::HandlerStateMismatch)?;
                    definition = owner.definition;
                    registers = owner.registers;
                    callers.truncate(owner_depth);
                }
                for (destination, value) in payload_destinations.iter().zip(clause_values)
                {
                    registers[*destination as usize] = Some(value);
                }
                handlers[index].suspended = Some(RuntimeContinuation {
                    target: pc + 1,
                    dst: *dst,
                    registers: saved,
                    performed: RuntimePerformed {
                        effect: *effect,
                        effect_arguments: effect_arguments.clone(),
                        operation: *operation,
                        payloads: values,
                    },
                    above,
                    pending_leave: None,
                    remaining_replays: handlers[index].continuation.replay_uses().unwrap_or(0),
                    program: Some(continuation_program),
                });
                pc = handler_target as usize;
                continue;
            }
            VmInstruction::InstallHandler {
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                continuation,
                target,
                ..
            } => {
                if handlers.len() >= budget.limits.max_handler_depth as usize {
                    return Err(VmArtifactError::HandlerDepthLimit {
                        limit: budget.limits.max_handler_depth,
                    });
                }
                handlers.push(RuntimeHandlerFrame {
                    id: {
                        let id = next_handler_id;
                        next_handler_id = next_handler_id.saturating_add(1);
                        id
                    },
                    call_depth: callers.len(),
                    effect: *effect,
                    effect_arguments: effect_arguments.clone(),
                    operation: *operation,
                    payload_destinations: payload_destinations.clone(),
                    continuation: *continuation,
                    target: *target,
                    suspended: None,
                });
            }
            VmInstruction::UninstallHandler => {
                let Some(frame) = handlers.pop() else {
                    return Err(VmArtifactError::HandlerStackUnderflow);
                };
                if frame.suspended.is_some() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
            }
            VmInstruction::Resume { value } => {
                let resumed = registers[*value as usize]
                    .clone()
                    .ok_or(VmArtifactError::ReadBeforeWrite { register: *value })?;
                let Some(frame) = handlers.last_mut() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.continuation.is_replay() {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                let continuation = match frame.continuation {
                    VmContinuationPolicy::Consume => frame.suspended.take(),
                    VmContinuationPolicy::Replay { .. } => frame.suspended.clone(),
                    VmContinuationPolicy::Terminal => {
                        return Err(VmArtifactError::HandlerResumeUnavailable);
                    }
                };
                let Some(continuation) = continuation else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.continuation.is_replay() {
                    frame.suspended = None;
                }
                let resumed = transfer_to_resumed_frame(
                    resumed, &registers, &callers, frame.call_depth,
                    continuation.program.as_ref().map(|program| program.callers.len()).unwrap_or(callers.len()),
                    budget,
                )?;
                let RuntimeContinuation {
                    target,
                    dst,
                    registers: saved_registers,
                    above,
                    pending_leave,
                    program,
                    ..
                } = continuation;
                if let Some(program) = program {
                    definition = program.definition;
                    callers = program.callers;
                }
                if let Some(leave) = pending_leave {
                    registers = saved_registers;
                    handlers.extend(above);
                    pc = complete_pending_leave(&mut registers, &mut handlers, leave)?;
                    continue;
                }
                registers = saved_registers;
                registers[dst as usize] = Some(resumed);
                handlers.extend(above);
                pc = target;
                continue;
            }
            VmInstruction::ResumeReturn { dst, value } => {
                let resumed = registers[*value as usize]
                    .clone()
                    .ok_or(VmArtifactError::ReadBeforeWrite { register: *value })?;
                let Some(frame) = handlers.last_mut() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.continuation == VmContinuationPolicy::Terminal {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let replaying = frame.continuation.is_replay();
                let continuation = if replaying {
                    frame.suspended.clone()
                } else {
                    frame.suspended.take()
                }
                .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                if replaying && continuation.remaining_replays == 0 {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                budget.reserve_allocation(registers.len())?;
                let resumed = transfer_to_resumed_frame(
                    resumed, &registers, &callers, frame.call_depth,
                    continuation.program.as_ref().map(|program| program.callers.len()).unwrap_or(callers.len()),
                    budget,
                )?;
                let RuntimeContinuation {
                    target,
                    dst: continuation_dst,
                    registers: saved_registers,
                    above,
                    pending_leave,
                    program,
                    ..
                } = continuation;
                if pending_leave.is_some() {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                let resumed_handler_ids = handlers
                    .iter()
                    .map(|frame| frame.id)
                    .chain(above.iter().map(|frame| frame.id))
                    .collect();
                let mut return_handlers = handlers.clone();
                if replaying {
                    return_handlers
                        .last_mut()
                        .and_then(|frame| frame.suspended.as_mut())
                        .expect("checked suspended replay handler")
                        .remaining_replays -= 1;
                }
                resumption_returns.push(RuntimeResumptionReturn {
                    pc: pc + 1,
                    dst: *dst,
                    registers: registers.clone(),
                    handlers: return_handlers,
                    program: Some(RuntimeProgramContinuation {
                        definition,
                        callers: callers.clone(),
                    }),
                    resumed_handler_ids,
                });
                if replaying {
                    handlers.last_mut().expect("active frame exists").suspended = None;
                }
                handlers.extend(above);
                if let Some(program) = program {
                    definition = program.definition;
                    callers = program.callers;
                }
                registers = saved_registers;
                registers[continuation_dst as usize] = Some(resumed);
                pc = target;
                continue;
            }
            VmInstruction::CaptureResumption { dst } => {
                let Some(frame) = handlers.last() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.suspended.is_none() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let signature = register_type(function, *dst)?;
                if !matches!(signature, VmType::Callable { .. }) {
                    return Err(VmArtifactError::NotCallable { register: *dst });
                }
                registers[*dst as usize] = Some(VmValue::Resumption {
                    frame: frame.id,
                    signature,
                });
            }
            VmInstruction::ResumeSnapshot { snapshot, value } => {
                let resumed = registers[*value as usize]
                    .clone()
                    .ok_or(VmArtifactError::ReadBeforeWrite { register: *value })?;
                let VmValue::Resumption { frame: id, .. } = registers[*snapshot as usize]
                    .as_ref()
                    .ok_or(VmArtifactError::ReadBeforeWrite {
                        register: *snapshot,
                    })?
                else {
                    return Err(VmArtifactError::NotCallable {
                        register: *snapshot,
                    });
                };
                let Some(index) = handlers.iter().rposition(|frame| frame.id == *id) else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                let continuation = match handlers[index].continuation {
                    VmContinuationPolicy::Consume => handlers[index].suspended.take(),
                    VmContinuationPolicy::Replay { .. } => handlers[index].suspended.clone(),
                    VmContinuationPolicy::Terminal => {
                        return Err(VmArtifactError::HandlerResumeUnavailable);
                    }
                }
                .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                if handlers[index].continuation.is_replay() {
                    handlers[index].suspended = None;
                }
                // See the standalone-artifact interpreter above: an explicit
                // snapshot abandons dynamically newer frames before restoring
                // the continuation's original deep-frame suffix.
                handlers.truncate(index + 1);
                let resumed = transfer_to_resumed_frame(
                    resumed, &registers, &callers, handlers[index].call_depth,
                    continuation.program.as_ref().map(|program| program.callers.len()).unwrap_or(callers.len()),
                    budget,
                )?;
                let RuntimeContinuation {
                    target,
                    dst,
                    registers: saved_registers,
                    above,
                    pending_leave,
                    program,
                    ..
                } = continuation;
                if let Some(program) = program {
                    definition = program.definition;
                    callers = program.callers;
                }
                if let Some(leave) = pending_leave {
                    registers = saved_registers;
                    handlers.extend(above);
                    pc = complete_pending_leave(&mut registers, &mut handlers, leave)?;
                    continue;
                }
                registers = saved_registers;
                registers[dst as usize] = Some(resumed);
                handlers.extend(above);
                pc = target;
                continue;
            }
            VmInstruction::Forward => {
                let Some(mut declined) = handlers.pop() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                let Some(continuation) = declined.suspended.take() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                let Some(index) = handlers.iter().rposition(|frame| {
                    frame.suspended.is_none()
                        && frame.effect == continuation.performed.effect
                        && frame.effect_arguments == continuation.performed.effect_arguments
                        && frame.operation == continuation.performed.operation
                }) else {
                    return Err(VmArtifactError::UnhandledEffect {
                        effect: continuation.performed.effect,
                        effect_arguments: continuation.performed.effect_arguments,
                        operation: continuation.performed.operation,
                    });
                };
                let mut crossed = handlers.split_off(index + 1);
                crossed.push(declined);
                crossed.extend(continuation.above.clone());
                let owner_depth = handlers[index].call_depth;
                let payload_destinations = handlers[index].payload_destinations.clone();
                let handler_target = handlers[index].target;
                if payload_destinations.len() != continuation.performed.payloads.len() {
                    return Err(VmArtifactError::CallArity {
                        expected: payload_destinations.len() as u32,
                        found: continuation.performed.payloads.len() as u32,
                    });
                }
                budget.reserve_allocation(continuation.registers.len())?;
                let continuation_program = continuation.program.clone();
                let original_callers = continuation_program.as_ref()
                    .map(|program| program.callers.as_slice()).unwrap_or(&[]);
                budget.reserve_value("forwarded clause payload", continuation.performed.payloads.len())?;
                let clause_values = continuation.performed.payloads.iter().cloned().map(|value| {
                    transfer_to_ancestor_frame(value, &continuation.registers, original_callers, owner_depth, budget)
                }).collect::<Result<Vec<_>, _>>()?;
                if let Some(program) = &continuation_program {
                    if owner_depth > program.callers.len() {
                        return Err(VmArtifactError::HandlerStateMismatch);
                    }
                    if owner_depth < program.callers.len() {
                        let owner = program
                            .callers
                            .get(owner_depth)
                            .cloned()
                            .ok_or(VmArtifactError::HandlerStateMismatch)?;
                        definition = owner.definition;
                        registers = owner.registers;
                        callers = program.callers[..owner_depth].to_vec();
                    } else {
                        registers = continuation.registers.clone();
                    }
                } else {
                    registers = continuation.registers.clone();
                }
                for (destination, payload) in payload_destinations
                    .iter()
                    .zip(clause_values)
                {
                    registers[*destination as usize] = Some(payload);
                }
                handlers[index].suspended = Some(RuntimeContinuation {
                    target: continuation.target,
                    dst: continuation.dst,
                    registers: continuation.registers,
                    performed: continuation.performed,
                    above: crossed,
                    pending_leave: continuation.pending_leave,
                    remaining_replays: continuation.remaining_replays,
                    program: continuation_program,
                });
                pc = handler_target as usize;
                continue;
            }
            VmInstruction::Cancel => {
                let Some(frame) = handlers.pop() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.suspended.is_none() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                if frame.continuation == VmContinuationPolicy::Terminal {
                    resumption_returns.clear();
                }
            }
            VmInstruction::Copy { dst, src } => {
                registers[*dst as usize] = registers[*src as usize].clone()
            }
            VmInstruction::StorageLive { local, .. } => {
                if registers[*local as usize].is_some() {
                    return Err(VmArtifactError::ReadBeforeWrite { register: *local });
                }
            }
            VmInstruction::StorageDead { local, .. } => {
                if registers[*local as usize].is_some() {
                    return Err(VmArtifactError::ReadBeforeWrite { register: *local });
                }
            }
            VmInstruction::SetDropFlag { flag, value } => {
                registers[*flag as usize] = Some(VmValue::Bool(*value))
            }
            VmInstruction::DestroyIf { local, flag } => {
                match registers[*flag as usize].as_ref() {
                    Some(VmValue::Bool(_)) => {}
                    _ => return Err(VmArtifactError::ReadBeforeWrite { register: *flag }),
                }
                registers[*local as usize] = None;
            }
            VmInstruction::Store { dst, src } => {
                registers[*dst as usize] = registers[*src as usize].clone()
            }
            VmInstruction::Move { dst, src } => {
                registers[*dst as usize] = registers[*src as usize].take()
            }
            VmInstruction::Borrow {
                dst,
                src,
                fields,
                unique,
                reborrow,
            } => {
                let VmType::Reference { referent, .. } = &function.registers[*dst as usize] else {
                    return Err(VmArtifactError::InvalidRegister { register: *dst });
                };
                registers[*dst as usize] = Some(borrow_value(
                    &registers,
                    &callers,
                    *src,
                    registers[*src as usize]
                        .as_ref()
                        .expect("verified register"),
                    fields,
                    *unique,
                    *reborrow,
                    referent,
                )?);
            }
            VmInstruction::DerefCopy { dst, reference } => {
                let VmValue::Reference { target, fields, .. } = registers[*reference as usize]
                    .as_ref()
                    .expect("verified register")
                else {
                    return Err(VmArtifactError::InvalidRegister {
                        register: *reference,
                    });
                };
                let value = load_reference_target(&registers, &callers, target, fields, budget)?;
                // Dereferencing a reference into a caller frame materializes
                // a value whose nested references are still expressed in the
                // caller's register coordinate system. Rebase those paths
                // before exposing the value in this callee; otherwise a
                // custom Drop hook that projects `self.field` would interpret
                // the field's reference target as one of its own registers.
                let value = match target {
                    ReferenceTarget::Caller { caller_depth, .. } => {
                        rebase_caller_references(value, *caller_depth)?
                    }
                    ReferenceTarget::Register(_) | ReferenceTarget::Captured(_) | ReferenceTarget::Native(_) => value,
                };
                registers[*dst as usize] = Some(value);
            }
            VmInstruction::DerefMove { dst, reference } => {
                let VmValue::Reference { target, fields, .. } = registers[*reference as usize]
                    .as_ref()
                    .expect("verified register")
                else {
                    return Err(VmArtifactError::InvalidRegister { register: *reference });
                };
                let value = load_reference_target(&registers, &callers, target, fields, budget)?;
                let value = match target {
                    ReferenceTarget::Caller { caller_depth, .. } => {
                        rebase_caller_references(value, *caller_depth)?
                    }
                    ReferenceTarget::Register(_) | ReferenceTarget::Captured(_) | ReferenceTarget::Native(_) => value,
                };
                registers[*dst as usize] = Some(value);
            }
            VmInstruction::DerefStore { reference, src } => {
                let VmValue::Reference {
                    target,
                    fields,
                    unique: true,
                    ..
                } = registers[*reference as usize]
                    .as_ref()
                    .expect("verified register")
                else {
                    return Err(VmArtifactError::InvalidRegister {
                        register: *reference,
                    });
                };
                let (target, fields) = (target.clone(), fields.clone());
                let mut replacement = registers[*src as usize]
                    .as_ref()
                    .expect("verified register")
                    .clone();
                // `DerefCopy` rebases references nested inside a value read
                // from a caller frame into this callee's coordinate system.
                // Before writing that aggregate back through the same caller
                // reference, translate those nested paths in the other
                // direction. Otherwise the stored aggregate retains a
                // caller-depth that is one frame too large on its next use.
                if let ReferenceTarget::Caller { caller_depth, .. } = target {
                    for _ in 0..=caller_depth {
                        replacement = transfer_call_frame_value(
                            &replacement,
                            &registers,
                            &callers,
                            UniqueReferenceTransfer::ToCaller,
                        )?;
                    }
                }
                store_reference_target(
                    &mut registers,
                    &mut callers,
                    &target,
                    &fields,
                    replacement,
                    budget,
                )?;
            }
            VmInstruction::NotBool { dst, value } => {
                registers[*dst as usize] = Some(VmValue::Bool(!expect_bool(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?))
            }
            VmInstruction::AddI64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .checked_add(expect_i64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?)
                    .ok_or(VmArtifactError::ArithmeticOverflow)?,
                ))
            }
            VmInstruction::WrappingAddI64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .wrapping_add(expect_i64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?),
                ))
            }
            VmInstruction::WrappingSubI64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .wrapping_sub(expect_i64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?),
                ))
            }
            VmInstruction::WrappingMulI64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .wrapping_mul(expect_i64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?),
                ))
            }
            VmInstruction::IntEqualI64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::U32(
                    (expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? == expect_i64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?) as u32,
                ))
            }
            VmInstruction::IntLessI64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::U32(
                    (expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? < expect_i64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?) as u32,
                ))
            }
            VmInstruction::IntGreaterI64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::U32(
                    (expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? > expect_i64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?) as u32,
                ))
            }
            VmInstruction::BitAndI64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? & expect_i64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::BitAndU32 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::U32(
                    expect_u32(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? & expect_u32(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::BitAndU64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::U64(
                    expect_u64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? & expect_u64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::BitXorI64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? ^ expect_i64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::IntShrI64 { dst, left, right } => {
                let count = expect_u32(
                    registers[*right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                if count >= 64 {
                    return Err(VmArtifactError::ArithmeticOverflow);
                }
                registers[*dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .wrapping_shr(count),
                ))
            }
            VmInstruction::BitOrI64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? | expect_i64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::BitNotI64 { dst, value } => {
                registers[*dst as usize] = Some(VmValue::I64(!expect_i64(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?))
            }
            VmInstruction::ShlI64 { dst, value, count } => {
                let count = expect_u32(
                    registers[*count as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                if count >= 64 {
                    return Err(VmArtifactError::ArithmeticOverflow);
                }
                registers[*dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[*value as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .wrapping_shl(count),
                ))
            }
            VmInstruction::SubI64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .checked_sub(expect_i64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?)
                    .ok_or(VmArtifactError::ArithmeticOverflow)?,
                ))
            }
            VmInstruction::MulI64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .checked_mul(expect_i64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?)
                    .ok_or(VmArtifactError::ArithmeticOverflow)?,
                ))
            }
            VmInstruction::DivI64 { dst, left, right } => {
                let right = expect_i64(
                    registers[*right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let value = expect_i64(
                    registers[*left as usize]
                        .as_ref()
                        .expect("verified register"),
                )?
                .checked_div(right)
                .ok_or(if right == 0 {
                    VmArtifactError::DivisionByZero
                } else {
                    VmArtifactError::ArithmeticOverflow
                })?;
                registers[*dst as usize] = Some(VmValue::I64(value));
            }
            VmInstruction::RemI64 { dst, left, right } => {
                let right = expect_i64(
                    registers[*right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let value = expect_i64(
                    registers[*left as usize]
                        .as_ref()
                        .expect("verified register"),
                )?
                .checked_rem(right)
                .ok_or(if right == 0 {
                    VmArtifactError::DivisionByZero
                } else {
                    VmArtifactError::ArithmeticOverflow
                })?;
                registers[*dst as usize] = Some(VmValue::I64(value));
            }
            VmInstruction::AddF64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::F64(canonical_vm_f64(
                    expect_f64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? + expect_f64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                )))
            }
            VmInstruction::ConcatText { dst, left, right } => {
                let left = expect_text(
                    registers[*left as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let right = expect_text(
                    registers[*right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                let length = left.len().checked_add(right.len()).ok_or(
                    VmArtifactError::AllocationLimit {
                        limit: budget.limits.max_allocation_elements,
                    },
                )?;
                budget.reserve_value("text bytes", length)?;
                registers[*dst as usize] = Some(VmValue::Text(Arc::from(format!("{left}{right}"))));
            }
            VmInstruction::SubF64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::F64(canonical_vm_f64(
                    expect_f64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? - expect_f64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                )))
            }
            VmInstruction::MulF64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::F64(canonical_vm_f64(
                    expect_f64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? * expect_f64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                )))
            }
            VmInstruction::DivF64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::F64(canonical_vm_f64(
                    expect_f64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? / expect_f64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                )))
            }
            VmInstruction::RemF64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::F64(canonical_vm_f64(
                    expect_f64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? % expect_f64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                )))
            }
            VmInstruction::CompareI64 {
                dst,
                left,
                right,
                op,
            } => {
                registers[*dst as usize] = Some(VmValue::Bool(compare_i64_values(
                    expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    expect_i64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    *op,
                )))
            }
            VmInstruction::CompareF64 {
                dst,
                left,
                right,
                op,
            } => {
                registers[*dst as usize] = Some(VmValue::Bool(compare_f64_values(
                    expect_f64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    expect_f64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    *op,
                )))
            }
            VmInstruction::EqBool { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::Bool(
                    expect_bool(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? == expect_bool(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::CompareU32 {
                dst,
                left,
                right,
                op,
            } => {
                registers[*dst as usize] = Some(VmValue::Bool(compare_u32_values(
                    expect_u32(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    expect_u32(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    *op,
                )))
            }
            VmInstruction::CompareU64 {
                dst,
                left,
                right,
                op,
            } => {
                registers[*dst as usize] = Some(VmValue::Bool(compare_u64_values(
                    expect_u64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    expect_u64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    *op,
                )))
            }
            VmInstruction::NeBool { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::Bool(
                    expect_bool(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? != expect_bool(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::EqText { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::Bool(
                    expect_text(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? == expect_text(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::NeText { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::Bool(
                    expect_text(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? != expect_text(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::CompareChar {
                dst,
                left,
                right,
                op,
            } => {
                registers[*dst as usize] = Some(VmValue::Bool(compare_char_values(
                    expect_char(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    expect_char(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                    *op,
                )))
            }
            VmInstruction::HostCall {
                dst,
                capability,
                symbol,
                arguments,
                ..
            } => {
                let Some(host) = host.as_deref_mut() else {
                    return Err(VmArtifactError::HostCallRequiresAuthority {
                        capability: capability.clone(),
                        symbol: symbol.clone(),
                    });
                };
                let values = arguments
                    .iter()
                    .map(|argument| {
                        registers[*argument as usize]
                            .as_ref()
                            .cloned()
                            .ok_or(VmArtifactError::ReadBeforeWrite {
                                register: *argument,
                            })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                registers[*dst as usize] = Some(execute_host_call(
                    host,
                    capability,
                    symbol,
                    &values,
                )?);
            }
            VmInstruction::Call {
                dst,
                callee,
                arguments,
            } => {
                budget.reserve_value("call arguments", arguments.len())?;
                if *callee == definition
                    && handlers.is_empty()
                    && resumption_returns.is_empty()
                    && let Some(profile) = profile.as_deref_mut()
                    && tail_return_suffix(&function.instructions[pc + 1..], *dst, budget)?
                    && recyclable_tail_arguments(&registers, arguments, &callers, budget, profile)?
                {
                    // Clone only the small argument vector before clearing
                    // registers; aggregate contents retain their Arc backing.
                    // Do not run the ordinary call rebasing here: no frame
                    // is pushed, so surviving caller loans must not move.
                    // No source-visible storage destructor is skipped: the
                    // verified suffix only forwards and returns call_result.
                    let values: Vec<_> = arguments.iter().map(|argument| {
                        registers[*argument as usize].clone()
                    }).collect();
                    registers.fill(None);
                    for (index, value) in values.into_iter().enumerate() {
                        registers[index] = value;
                    }
                    profile.recycled_tail_calls += 1;
                    pc = 0;
                    continue;
                }
                let values = arguments
                    .iter()
                    .map(|argument| {
                        registers[*argument as usize]
                            .clone()
                            .ok_or(VmArtifactError::ReadBeforeWrite {
                                register: *argument,
                            })
                            .and_then(|value| {
                                transfer_call_frame_value(
                                    &value,
                                    &registers,
                                    &callers,
                                    UniqueReferenceTransfer::IntoCallee,
                                )
                            })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                if depth.saturating_add(callers.len() as u32).saturating_add(1)
                    >= budget.limits.max_call_depth
                {
                    return Err(VmArtifactError::CallDepthLimit {
                        limit: budget.limits.max_call_depth,
                    });
                }
                let callee_function =
                    program
                        .functions
                        .get(callee)
                        .ok_or(VmArtifactError::MissingFunction {
                            definition: *callee,
                        })?;
                budget.reserve_allocation(callee_function.registers.len())?;
                callers.push(RuntimeProgramCaller {
                    definition,
                    registers: std::mem::take(&mut registers),
                    pc,
                    return_destination: *dst,
                });
                definition = *callee;
                registers = vec![None; callee_function.registers.len()];
                for (index, value) in values.into_iter().enumerate() {
                    registers[index] = Some(value);
                }
                pc = 0;
                continue;
            }
            VmInstruction::MakeCallable {
                dst,
                callee,
                captures,
                ..
            } => {
                budget.reserve_value("callable captures", captures.len())?;
                let values = captures
                    .iter()
                    .map(|capture| {
                        registers[*capture as usize]
                            .as_ref()
                            .ok_or(VmArtifactError::ReadBeforeWrite { register: *capture })
                            .and_then(|value| freeze_frame_value(value, &registers, &callers))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let signature = register_type(function, *dst)?;
                registers[*dst as usize] = Some(VmValue::Callable {
                    callee: *callee,
                    captures: Arc::from(values),
                    signature,
                });
            }
            VmInstruction::MakeLabel {
                dst,
                brand_owner,
                brand_label,
                target,
                destination,
            } => {
                let signature = register_type(function, *dst)?;
                registers[*dst as usize] = Some(VmValue::Label {
                    owner: *brand_owner,
                    label: *brand_label,
                    target: *target,
                    destination: *destination,
                    call_depth: callers.len(),
                    handler_depth: handlers.len(),
                    signature,
                });
            }
            VmInstruction::CallIndirect {
                dst,
                callee,
                arguments,
            } => {
                let callee_value = registers[*callee as usize]
                    .as_ref()
                    .expect("verified register")
                    .clone();
                if let VmValue::Label {
                    owner,
                    target,
                    destination,
                    call_depth,
                    handler_depth,
                    ..
                } = callee_value
                {
                    let [argument] = arguments.as_slice() else {
                        return Err(VmArtifactError::CallArity {
                            expected: 1,
                            found: arguments.len() as u32,
                        });
                    };
                    let payload = registers[*argument as usize].clone().ok_or(
                        VmArtifactError::ReadBeforeWrite {
                            register: *argument,
                        },
                    )?;
                    while callers.len() > call_depth {
                        let caller = callers.pop().expect("checked dynamic call depth");
                        definition = caller.definition;
                        registers = caller.registers;
                    }
                    if callers.len() != call_depth || definition != owner {
                        return Err(VmArtifactError::HandlerStateMismatch);
                    }
                    let slot = registers.get_mut(destination as usize).ok_or(
                        VmArtifactError::InvalidRegister {
                            register: destination,
                        },
                    )?;
                    *slot = Some(payload);
                    handlers.truncate(handler_depth);
                    // See the standalone interpreter above. Restoring the
                    // captured lexical label prefix abandons every pending
                    // handler-clause return path it crossed.
                    resumption_returns.clear();
                    pc = target as usize;
                    continue;
                }
                let VmValue::Callable {
                    callee, captures, ..
                } = callee_value
                else {
                    return Err(VmArtifactError::NotCallable { register: *callee });
                };
                let value_count = captures.len().checked_add(arguments.len()).ok_or(
                    VmArtifactError::AllocationLimit {
                        limit: budget.limits.max_allocation_elements,
                    },
                )?;
                budget.reserve_value("indirect call arguments", value_count)?;
                let mut values = captures.as_ref().to_vec();
                values.extend(
                    arguments
                        .iter()
                        .map(|argument| {
                            registers[*argument as usize]
                                .as_ref()
                                .expect("verified register")
                        })
                        .map(|value| {
                            transfer_call_frame_value(
                                value,
                                &registers,
                                &callers,
                                UniqueReferenceTransfer::IntoCallee,
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                );
                if depth.saturating_add(callers.len() as u32).saturating_add(1)
                    >= budget.limits.max_call_depth
                {
                    return Err(VmArtifactError::CallDepthLimit {
                        limit: budget.limits.max_call_depth,
                    });
                }
                let callee_function = program
                    .functions
                    .get(&callee)
                    .ok_or(VmArtifactError::MissingFunction { definition: callee })?;
                budget.reserve_allocation(callee_function.registers.len())?;
                callers.push(RuntimeProgramCaller {
                    definition,
                    registers: std::mem::take(&mut registers),
                    pc,
                    return_destination: *dst,
                });
                definition = callee;
                registers = vec![None; callee_function.registers.len()];
                for (index, value) in values.into_iter().enumerate() {
                    registers[index] = Some(value);
                }
                pc = 0;
                continue;
            }
            VmInstruction::Jump { target } => {
                pc = *target as usize;
                continue;
            }
            VmInstruction::Leave {
                brand_owner,
                brand_label,
                handler_depth,
                target,
                arguments,
                destinations,
                cleanup,
            } => {
                pc = complete_pending_leave(
                    &mut registers,
                    &mut handlers,
                    PendingLeave {
                        brand_owner: *brand_owner,
                        brand_label: *brand_label,
                        handler_depth: *handler_depth,
                        target: *target,
                        arguments: arguments.clone(),
                        destinations: destinations.clone(),
                        cleanup: cleanup.clone(),
                    },
                )?;
                // See the standalone interpreter above. A branded leave is
                // terminal with respect to replay clause-return frames.
                resumption_returns.clear();
                continue;
            }
            VmInstruction::BranchBool {
                condition,
                then_target,
                else_target,
            } => {
                pc = if expect_bool(
                    registers[*condition as usize]
                        .as_ref()
                        .expect("verified register"),
                )? {
                    *then_target as usize
                } else {
                    *else_target as usize
                };
                continue;
            }
            VmInstruction::Return { value } => {
                let value = registers[*value as usize]
                    .as_ref()
                    .expect("verified register")
                    .clone();
                if !callers.is_empty() {
                    // Ancestor handlers remain dynamically active across a
                    // callee return. Only a handler installed by this frame
                    // may make its ordinary return ill-formed.
                    if handlers
                        .iter()
                        .any(|handler| handler.call_depth == callers.len())
                    {
                        return Err(VmArtifactError::HandlerStillActive);
                    }
                    let value = transfer_call_frame_value(
                        &value,
                        &registers,
                        &callers,
                        UniqueReferenceTransfer::ToCaller,
                    )?;
                    let caller = callers.pop().expect("checked nonempty call stack");
                    definition = caller.definition;
                    registers = caller.registers;
                    registers[caller.return_destination as usize] = Some(value);
                    pc = caller.pc + 1;
                    continue;
                }
                if let Some(return_to_clause) = resumption_returns.last() {
                    if handlers
                        .iter()
                        .any(|handler| !return_to_clause.resumed_handler_ids.contains(&handler.id))
                    {
                        return Err(VmArtifactError::HandlerStillActive);
                    }
                    let return_to_clause = resumption_returns
                        .pop()
                        .expect("checked clause-return frame exists");
                    if let Some(program) = return_to_clause.program {
                        definition = program.definition;
                        callers = program.callers;
                    }
                    registers = return_to_clause.registers;
                    registers[return_to_clause.dst as usize] = Some(value);
                    handlers = return_to_clause.handlers;
                    pc = return_to_clause.pc;
                    continue;
                }
                if !handlers.is_empty() {
                    return Err(VmArtifactError::HandlerStillActive);
                }
                return Ok(value);
            }
            VmInstruction::Trap => return Err(VmArtifactError::Trap),
        }
        pc += 1;
    }
}

fn execute_host_call(
    host: &mut dyn VmHost,
    capability: &str,
    symbol: &str,
    arguments: &[VmValue],
) -> Result<VmValue, VmArtifactError> {
    let failed = |message| VmArtifactError::HostCallFailed {
        capability: capability.to_owned(),
        symbol: symbol.to_owned(),
        message,
    };
    match (capability, symbol, arguments) {
        ("process_args", "__g1_process_args_get", []) => {
            let arguments = host.process_args().map_err(failed)?;
            let values = arguments
                .into_iter()
                .map(|value| VmValue::Text(Arc::from(value)))
                .collect::<Vec<_>>();
            Ok(VmValue::Array {
                capacity: values.len(),
                values: Arc::from(values),
            })
        }
        ("file_read", "__g1_fs_read", [path]) => {
            let path = expect_text(path)?.to_owned();
            let bytes = host.read_file(&path).map_err(failed)?;
            Ok(VmValue::Bytes(Arc::from(bytes)))
        }
        ("file_write", "__g1_fs_write", [path, bytes]) => {
            let path = expect_text(path)?.to_owned();
            let bytes = expect_bytes(bytes)?;
            host.write_file(&path, &bytes).map_err(failed)?;
            Ok(VmValue::Unit)
        }
        ("file_write_atomic", "__g1_fs_write_atomic", [path, bytes]) => {
            let path = expect_text(path)?.to_owned();
            let bytes = expect_bytes(bytes)?;
            host.write_file_atomically(&path, &bytes).map_err(failed)?;
            Ok(VmValue::Unit)
        }
        ("diagnostic", "__g1_diagnostic_write", [text]) => {
            let text = expect_text(text)?.to_owned();
            host.write_diagnostic(&text).map_err(failed)?;
            Ok(VmValue::Unit)
        }
        _ => Err(VmArtifactError::HostCallRequiresAuthority {
            capability: capability.to_owned(),
            symbol: symbol.to_owned(),
        }),
    }
}
struct ExecutionBudget {
    native_memory: NativeMemory,
    /// Set only by the unsafe Rust execution entry, never decoded from bytes.
    unsafe_execution: bool,
    limits: VmExecutionLimits,
    instructions: u64,
    allocated_elements: u64,
}
impl ExecutionBudget {
    fn tick(&mut self) -> Result<(), VmArtifactError> {
        self.instructions =
            self.instructions
                .checked_add(1)
                .ok_or(VmArtifactError::InstructionLimit {
                    limit: self.limits.max_instructions,
                })?;
        if self.instructions > self.limits.max_instructions {
            Err(VmArtifactError::InstructionLimit {
                limit: self.limits.max_instructions,
            })
        } else {
            Ok(())
        }
    }
    fn reserve_allocation(&mut self, count: usize) -> Result<(), VmArtifactError> {
        let count = count as u64;
        let Some(next) = self.allocated_elements.checked_add(count) else {
            return Err(VmArtifactError::AllocationLimit {
                limit: self.limits.max_allocation_elements,
            });
        };
        if next > self.limits.max_allocation_elements {
            return Err(VmArtifactError::AllocationLimit {
                limit: self.limits.max_allocation_elements,
            });
        }
        self.allocated_elements = next;
        Ok(())
    }
    fn reserve_value(&mut self, kind: &'static str, count: usize) -> Result<(), VmArtifactError> {
        let count = count as u64;
        if count > self.limits.max_value_elements {
            return Err(VmArtifactError::ValueSizeLimit {
                kind,
                limit: self.limits.max_value_elements,
                found: count,
            });
        }
        self.reserve_allocation(count as usize)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{MirBlock, MirScopeId, PrimitiveRole};

    fn cow_budget() -> ExecutionBudget {
        ExecutionBudget { native_memory: NativeMemory::default(), unsafe_execution: false, limits: VmExecutionLimits::default(), instructions: 0, allocated_elements: 0 }
    }

    fn cow_owner() -> VmValue {
        VmValue::Tuple(Arc::from([VmValue::Array {
            values: (0..128).map(VmValue::I64).collect::<Vec<_>>().into(), capacity: 256,
        }]))
    }

    fn cow_backing(owner: &VmValue) -> (*const VmValue, *const VmValue) {
        let VmValue::Tuple(fields) = owner else { panic!("tuple owner") };
        let VmValue::Array { values, capacity } = &fields[0] else { panic!("array field") };
        assert_eq!(*capacity, 256);
        (fields.as_ptr(), values.as_ptr())
    }

    #[test]
    fn projected_cow_updates_reuse_unique_backing_and_preserve_shared_snapshots() {
        let mut owner = cow_owner();
        let original = cow_backing(&owner);
        let mut budget = cow_budget();
        *project_reference_mut(&mut owner, &[0, 64], &mut budget).unwrap() = VmValue::I64(42);
        assert_eq!(cow_backing(&owner), original);
        assert_eq!(budget.allocated_elements, 129, "logical charges are not discounted by physical reuse");
        assert!(matches!(project_reference(&owner, &[0, 64]).unwrap(), VmValue::I64(42)));

        let snapshot = owner.clone();
        *project_reference_mut(&mut owner, &[0, 64], &mut budget).unwrap() = VmValue::I64(43);
        let changed = cow_backing(&owner);
        assert_ne!(changed.0, original.0);
        assert_ne!(changed.1, original.1);
        assert_eq!(cow_backing(&snapshot), original);
        assert!(matches!(project_reference(&snapshot, &[0, 64]).unwrap(), VmValue::I64(42)));
        assert!(matches!(project_reference(&owner, &[0, 64]).unwrap(), VmValue::I64(43)));
        assert_eq!(budget.allocated_elements, 258);
        *project_reference_mut(&mut owner, &[0, 65], &mut budget).unwrap() = VmValue::I64(99);
        assert_eq!(cow_backing(&owner), changed, "detaching once makes subsequent updates unique");
        assert!(matches!(project_reference(&snapshot, &[0, 65]).unwrap(), VmValue::I64(65)));
    }

    #[test]
    fn projected_cow_rejects_invalid_paths_and_budgets_without_partial_value_updates() {
        let mut owner = cow_owner();
        let snapshot = owner.clone();
        let mut budget = cow_budget();
        budget.limits.max_allocation_elements = 1;
        assert!(matches!(project_reference_mut(&mut owner, &[0, 64], &mut budget),
            Err(VmArtifactError::AllocationLimit { limit: 1 })));
        assert_eq!(budget.allocated_elements, 1);
        assert!(matches!(project_reference(&owner, &[0, 64]).unwrap(), VmValue::I64(64)));
        assert!(matches!(project_reference(&snapshot, &[0, 64]).unwrap(), VmValue::I64(64)));
        let mut budget = cow_budget();
        assert!(matches!(project_reference_mut(&mut owner, &[0, 128], &mut budget),
            Err(VmArtifactError::InvalidRegister { register: 128 })));
        assert_eq!(budget.allocated_elements, 129);
        let mut budget = cow_budget();
        budget.limits.max_value_elements = 127;
        assert!(matches!(project_reference_mut(&mut owner, &[0, 1], &mut budget),
            Err(VmArtifactError::ValueSizeLimit { kind: "reference update fields", limit: 127, found: 128 })));
        assert!(matches!(project_reference(&owner, &[0, 1]).unwrap(), VmValue::I64(1)));
        let captured = ReferenceTarget::Captured(Arc::new(snapshot));
        assert!(matches!(store_reference_target(&mut [], &mut [], &captured, &[0, 1], VmValue::I64(0), &mut cow_budget()),
            Err(VmArtifactError::UnsupportedEscapingUniqueReference)));
    }

    #[test]
    fn array_cow_primitives_preserve_caller_writeback_move_holes_and_snapshots() {
        for caller in [false, true] {
            let owner = cow_owner();
            let mut callers = Vec::new();
            let mut registers = vec![None, None, Some(VmValue::Usize(64)), Some(VmValue::I64(42)), None];
            let target = if caller {
                callers.push(tail_caller(owner));
                ReferenceTarget::Caller { caller_depth: 0, register: 1 }
            } else {
                registers[0] = Some(owner);
                ReferenceTarget::Register(0)
            };
            let reference = VmValue::Reference { target: target.clone(), fields: Arc::from([0]),
                unique: true, referent: VmType::Array(Box::new(VmType::I64)) };
            registers[1] = Some(reference.clone());
            let original = cow_backing(reference_target(&registers, &callers, &target).unwrap());
            let mut budget = cow_budget();
            execute_array_primitive(&mut registers, &mut callers, &VmInstruction::ArraySetMove {
                value: 1, index: 2, item: 3, element_type: VmType::I64,
            }, &mut budget).unwrap();
            assert!(registers[3].is_none());
            assert_eq!(budget.allocated_elements, 1);
            assert_eq!(cow_backing(reference_target(&registers, &callers, &target).unwrap()), original);
            let snapshot = reference_target(&registers, &callers, &target).unwrap().clone();
            execute_array_primitive(&mut registers, &mut callers, &VmInstruction::ArrayGetMove {
                dst: 4, value: 1, index: 2, element_type: VmType::I64,
            }, &mut budget).unwrap();
            assert!(matches!(&registers[4], Some(VmValue::I64(42))));
            assert!(matches!(referenced_array_get(&registers, &callers, &reference, 64).unwrap(), VmValue::Unit));
            assert!(matches!(project_reference(&snapshot, &[0, 64]).unwrap(), VmValue::I64(42)));
            assert_eq!(budget.allocated_elements, 2);
            let current = cow_backing(reference_target(&registers, &callers, &target).unwrap());
            execute_array_primitive(&mut registers, &mut callers, &VmInstruction::ArrayReverseMove {
                value: 1, element_type: VmType::I64,
            }, &mut budget).unwrap();
            assert_eq!(cow_backing(reference_target(&registers, &callers, &target).unwrap()), current);
            assert!(matches!(referenced_array_get(&registers, &callers, &reference, 63).unwrap(), VmValue::Unit));
            assert!(matches!(project_reference(&snapshot, &[0, 63]).unwrap(), VmValue::I64(63)));
            assert_eq!(budget.allocated_elements, 3);
        }
    }

    #[test]
    fn array_cow_never_upgrades_shared_or_captured_borrow_authority() {
        let mut registers = vec![Some(cow_owner())];
        for reference in [
            VmValue::Reference { target: ReferenceTarget::Register(0), fields: Arc::from([0]),
                unique: false, referent: VmType::Array(Box::new(VmType::I64)) },
            VmValue::Reference { target: ReferenceTarget::Captured(Arc::new(cow_owner())), fields: Arc::from([0]),
                unique: true, referent: VmType::Array(Box::new(VmType::I64)) },
        ] {
            assert!(matches!(referenced_array_mut(&mut registers, &mut [], &reference, &mut cow_budget()),
                Err(VmArtifactError::UnsupportedEscapingUniqueReference)));
        }
    }

    #[test]
    fn borrowing_empty_projected_arrays_preserves_verified_element_types() {
        let bytes = VmType::Array(Box::new(VmType::U8));
        let empty = VmValue::Array { values: Arc::from([]), capacity: 0 };
        let tuple = VmValue::Tuple(Arc::from([empty.clone()]));
        let layout = VmType::Tuple(vec![bytes.clone()]);
        let registers = vec![Some(tuple.clone())];
        for unique in [false, true] {
            let parent = borrow_value(&registers, &[], 0, &tuple, &[], unique, false, &layout).unwrap();
            let projected = borrow_value(&registers, &[], 0, &parent, &[0], unique, true, &bytes).unwrap();
            assert!(value_matches_vm_type(&projected, &VmType::Reference {
                unique, referent: Box::new(bytes.clone()),
            }));
            assert!(matches!(projected, VmValue::Reference {
                target: ReferenceTarget::Register(0), fields, ..
            } if fields.as_ref() == [0]));
        }
        let nested = VmValue::Array { values: Arc::from([empty]), capacity: 1 };
        let nested_layout = VmType::Array(Box::new(bytes.clone()));
        assert_eq!(borrowed_value_type(&nested, &nested_layout), nested_layout);

        // Existing residents are not retyped to fit a forged destination, and
        // shared loans still cannot be upgraded to unique loans.
        let units = VmValue::Array { values: Arc::from([VmValue::Unit]), capacity: 1 };
        let reference = borrow_value(&[], &[], 0, &units, &[], false, false, &bytes).unwrap();
        assert!(!value_matches_vm_type(&reference, &VmType::Reference {
            unique: false, referent: Box::new(bytes),
        }));
        let shared = borrow_value(&registers, &[], 0, &tuple, &[], false, false, &layout).unwrap();
        assert!(borrow_value(&registers, &[], 0, &shared, &[], true, true, &layout).is_err());
    }

    #[test]
    fn ordinary_call_shared_loans_keep_the_surviving_owner_and_projection() {
        let registers = vec![Some(VmValue::Tuple(Arc::from([VmValue::I64(42)])))];
        let fields = Arc::from([0]);
        let reference = VmValue::Reference {
            target: ReferenceTarget::Register(0), fields: Arc::clone(&fields),
            unique: false, referent: VmType::I64,
        };
        let incoming = transfer_call_frame_value(
            &reference, &registers, &[], UniqueReferenceTransfer::IntoCallee,
        ).unwrap();
        assert!(matches!(&incoming, VmValue::Reference {
            target: ReferenceTarget::Caller { caller_depth: 0, register: 0 },
            fields: actual, unique: false, ..
        } if Arc::ptr_eq(actual, &fields)));
        let nested = transfer_call_frame_value(
            &incoming, &[], &[], UniqueReferenceTransfer::IntoCallee,
        ).unwrap();
        assert!(matches!(&nested, VmValue::Reference {
            target: ReferenceTarget::Caller { caller_depth: 1, register: 0 }, ..
        }));
        let returned = transfer_call_frame_value(
            &nested, &[], &[], UniqueReferenceTransfer::ToCaller,
        ).unwrap();
        let returned = transfer_call_frame_value(
            &returned, &[], &[], UniqueReferenceTransfer::ToCaller,
        ).unwrap();
        assert!(matches!(&returned, VmValue::Reference {
            target: ReferenceTarget::Register(0), fields: actual, unique: false, ..
        } if Arc::ptr_eq(actual, &fields)));
    }

    #[test]
    fn ordinary_call_reuses_the_frozen_capture_without_rebuilding_it() {
        let owner = Arc::new(VmValue::Tuple(Arc::from([VmValue::I64(42)])));
        let fields = Arc::from([0]);
        let reference = VmValue::Reference {
            target: ReferenceTarget::Captured(Arc::clone(&owner)), fields: Arc::clone(&fields),
            unique: false, referent: VmType::I64,
        };
        for direction in [UniqueReferenceTransfer::IntoCallee, UniqueReferenceTransfer::ToCaller] {
            let transferred = transfer_call_frame_value(&reference, &[], &[], direction).unwrap();
            assert!(matches!(&transferred, VmValue::Reference {
                target: ReferenceTarget::Captured(actual), fields: actual_fields, unique: false, ..
            } if Arc::ptr_eq(actual, &owner) && Arc::ptr_eq(actual_fields, &fields)));
        }
    }

    #[test]
    fn ordinary_call_still_freezes_shared_local_returns_and_rejects_unique_escape() {
        let registers = vec![Some(VmValue::I64(42))];
        let reference = VmValue::Reference {
            target: ReferenceTarget::Register(0), fields: Arc::from([]),
            unique: false, referent: VmType::I64,
        };
        let returned = transfer_call_frame_value(
            &reference, &registers, &[], UniqueReferenceTransfer::ToCaller,
        ).unwrap();
        assert!(matches!(returned, VmValue::Reference {
            target: ReferenceTarget::Captured(value), unique: false, ..
        } if matches!(*value, VmValue::I64(42))));
        let reference = VmValue::Reference {
            target: ReferenceTarget::Register(0), fields: Arc::from([]),
            unique: true, referent: VmType::I64,
        };
        assert!(matches!(transfer_call_frame_value(
            &reference, &registers, &[], UniqueReferenceTransfer::ToCaller,
        ), Err(VmArtifactError::UnsupportedEscapingUniqueReference)));
        assert!(matches!(freeze_frame_value(&reference, &registers, &[]),
            Err(VmArtifactError::UnsupportedEscapingUniqueReference)));
    }

    #[test]
    fn ordinary_call_frame_translation_checks_scope_and_work_limits() {
        let callers = vec![tail_caller(VmValue::I64(42)); 3];
        let reference = VmValue::Reference {
            target: ReferenceTarget::Caller { caller_depth: 1, register: 1 },
            fields: Arc::from([]), unique: false, referent: VmType::I64,
        };
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits::default(), instructions: 0, allocated_elements: 0,
        };
        let sibling = transfer_to_resumed_frame(reference.clone(), &[], &callers, 1, 2, &mut budget).unwrap();
        assert!(matches!(sibling, VmValue::Reference {
            target: ReferenceTarget::Caller { caller_depth: 0, register: 1 }, ..
        }));
        assert_eq!(budget.instructions, 3);
        assert!(matches!(transfer_to_ancestor_frame(reference.clone(), &[], &callers, 4, &mut budget),
            Err(VmArtifactError::HandlerStateMismatch)));
        assert!(matches!(transfer_to_resumed_frame(reference.clone(), &[], &callers, 2, 1, &mut budget),
            Err(VmArtifactError::HandlerStateMismatch)));
        budget.limits.max_instructions = budget.instructions;
        assert!(matches!(transfer_to_ancestor_frame(reference, &[], &callers, 1, &mut budget),
            Err(VmArtifactError::InstructionLimit { .. })));
    }

    #[test]
    fn authoring_tail_suffix_only_erases_straight_result_forwarding() {
        let cases = [
            (vec![VmInstruction::Return { value: 0 }], true),
            (vec![VmInstruction::Copy { dst: 1, src: 0 }, VmInstruction::Move { dst: 2, src: 1 },
                VmInstruction::Return { value: 2 }], true),
            (vec![VmInstruction::Return { value: 1 }], false),
            (vec![VmInstruction::Copy { dst: 1, src: 2 }, VmInstruction::Return { value: 1 }], false),
            (vec![VmInstruction::ConstI64 { dst: 1, value: 42 }, VmInstruction::Return { value: 0 }], false),
            (vec![VmInstruction::Store { dst: 1, src: 0 }, VmInstruction::Return { value: 1 }], false),
            (vec![VmInstruction::Jump { target: 0 }], false),
            (vec![], false),
        ];
        for (instructions, expected) in cases {
            let mut budget = ExecutionBudget {
                native_memory: NativeMemory::default(),
                unsafe_execution: false,
                limits: VmExecutionLimits::default(), instructions: 0, allocated_elements: 0,
            };
            assert_eq!(tail_return_suffix(&instructions, 0, &mut budget).unwrap(), expected);
        }
    }

    #[test]
    fn authoring_tail_suffix_inspection_is_budgeted() {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits { max_instructions: 1, ..Default::default() },
            instructions: 0, allocated_elements: 0,
        };
        assert!(matches!(tail_return_suffix(&[
            VmInstruction::Copy { dst: 1, src: 0 }, VmInstruction::Return { value: 1 },
        ], 0, &mut budget), Err(VmArtifactError::InstructionLimit { limit: 1 })));
    }

    #[test]
    fn authoring_tail_recycling_rejects_nested_frame_capabilities() {
        let definition = DefKey(Digest::of_bytes(b"tail-safety"));
        let capabilities = vec![
            VmValue::Reference {
                target: ReferenceTarget::Register(1), fields: Arc::from([]),
                unique: true, referent: VmType::I64,
            },
            VmValue::Reference {
                target: ReferenceTarget::Register(1), fields: Arc::from([]),
                unique: false, referent: VmType::I64,
            },
            VmValue::Reference {
                target: ReferenceTarget::Caller { caller_depth: 1, register: 0 }, fields: Arc::from([]),
                unique: true, referent: VmType::I64,
            },
            VmValue::Reference {
                target: ReferenceTarget::Captured(Arc::new(VmValue::I64(1))), fields: Arc::from([]),
                unique: true, referent: VmType::I64,
            },
            VmValue::Label {
                owner: definition, label: 0, target: 0, destination: 0,
                call_depth: 0, handler_depth: 0, signature: VmType::Unit,
            },
            VmValue::Resumption { frame: 1, signature: VmType::Unit },
        ];
        for capability in capabilities {
            let registers = vec![Some(VmValue::Callable {
                callee: definition,
                captures: Arc::from([VmValue::Tuple(Arc::from([capability]))]),
                signature: VmType::Unit,
            })];
            let mut budget = ExecutionBudget {
                native_memory: NativeMemory::default(),
                unsafe_execution: false,
                limits: VmExecutionLimits::default(), instructions: 0, allocated_elements: 0,
            };
            let mut profile = VmAuthoringProfile::default();
            assert!(!recyclable_tail_arguments(&registers, &[0], &[], &mut budget, &mut profile).unwrap());
            assert_eq!(profile.inspected_tail_argument_elements, 3);
        }
    }

    #[test]
    fn authoring_tail_recycling_accepts_surviving_caller_loans_and_shared_captures() {
        let definition = DefKey(Digest::of_bytes(b"tail-surviving-owner"));
        let callers = vec![tail_caller(VmValue::I64(42)); 3];
        for target in [
            ReferenceTarget::Caller { caller_depth: 0, register: 1 },
            ReferenceTarget::Caller { caller_depth: 2, register: 1 },
            ReferenceTarget::Captured(Arc::new(VmValue::Tuple(Arc::from([VmValue::I64(42)])))),
        ] {
            for unique in [false, true] {
                let captured = matches!(&target, ReferenceTarget::Captured(_));
                let registers = vec![Some(VmValue::Callable {
                    callee: definition,
                    captures: Arc::from([VmValue::Tuple(Arc::from([VmValue::Reference {
                        target: target.clone(), fields: Arc::from([]), unique, referent: VmType::I64,
                    }]))]),
                    signature: VmType::Unit,
                })];
                let mut budget = ExecutionBudget {
                    native_memory: NativeMemory::default(),
                    unsafe_execution: false,
                    limits: VmExecutionLimits::default(), instructions: 0, allocated_elements: 0,
                };
                let mut profile = VmAuthoringProfile::default();
                assert_eq!(recyclable_tail_arguments(&registers, &[0], &callers, &mut budget, &mut profile).unwrap(),
                    !(captured && unique));
                assert_eq!(profile.inspected_tail_argument_elements, if !captured { 4 } else if !unique { 5 } else { 3 });
            }
        }
    }

    #[test]
    fn authoring_tail_recycling_inspects_capabilities_hidden_in_shared_captures() {
        for target in [
            ReferenceTarget::Register(0),
            ReferenceTarget::Caller { caller_depth: 0, register: 0 },
        ] {
            let registers = vec![Some(VmValue::Reference {
                target: ReferenceTarget::Captured(Arc::new(VmValue::Tuple(Arc::from([VmValue::Reference {
                    target, fields: Arc::from([]), unique: false, referent: VmType::I64,
                }])))),
                fields: Arc::from([]), unique: false, referent: VmType::I64,
            })];
            let mut budget = ExecutionBudget {
                native_memory: NativeMemory::default(),
                unsafe_execution: false,
                limits: VmExecutionLimits::default(), instructions: 0, allocated_elements: 0,
            };
            let mut profile = VmAuthoringProfile::default();
            assert!(!recyclable_tail_arguments(&registers, &[0], &[], &mut budget, &mut profile).unwrap());
            assert_eq!(profile.inspected_tail_argument_elements, 3);
        }
    }

    fn tail_caller(value: VmValue) -> RuntimeProgramCaller {
        RuntimeProgramCaller {
            definition: DefKey(Digest::of_bytes(b"tail-owner")),
            registers: vec![None, Some(value)], pc: 0, return_destination: 0,
        }
    }

    #[test]
    fn authoring_tail_recycling_checks_capabilities_inside_surviving_owners() {
        let definition = DefKey(Digest::of_bytes(b"tail-owner-capability"));
        let capabilities = vec![
            VmValue::Label {
                owner: definition, label: 0, target: 0, destination: 0,
                call_depth: 1, handler_depth: 0, signature: VmType::Unit,
            },
            VmValue::Resumption { frame: 1, signature: VmType::Unit },
            VmValue::Reference {
                target: ReferenceTarget::Register(1), fields: Arc::from([]),
                unique: false, referent: VmType::I64,
            },
        ];
        for capability in capabilities {
            let callers = vec![tail_caller(VmValue::Callable {
                callee: definition, captures: Arc::from([VmValue::Tuple(Arc::from([capability]))]),
                signature: VmType::Unit,
            })];
            let registers = vec![Some(VmValue::Reference {
                target: ReferenceTarget::Caller { caller_depth: 0, register: 1 },
                fields: Arc::from([]), unique: true, referent: VmType::Unit,
            })];
            let mut budget = ExecutionBudget {
                native_memory: NativeMemory::default(),
                unsafe_execution: false,
                limits: VmExecutionLimits::default(), instructions: 0, allocated_elements: 0,
            };
            let mut profile = VmAuthoringProfile::default();
            assert!(!recyclable_tail_arguments(&registers, &[0], &callers, &mut budget, &mut profile).unwrap());
            assert_eq!(profile.inspected_tail_argument_elements, 4);
        }
    }

    #[test]
    fn authoring_tail_argument_inspection_obeys_work_and_allocation_limits() {
        let registers = vec![Some(VmValue::I64(42))];
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: VmExecutionLimits { max_instructions: 0, ..Default::default() },
            instructions: 0, allocated_elements: 0,
        };
        assert!(matches!(recyclable_tail_arguments(&registers, &[0], &[], &mut budget, &mut VmAuthoringProfile::default()),
            Err(VmArtifactError::InstructionLimit { limit: 0 })));
        budget.limits.max_instructions = 100;
        budget.limits.max_allocation_elements = 0;
        budget.allocated_elements = 0;
        assert!(matches!(recyclable_tail_arguments(&registers, &[0], &[], &mut budget, &mut VmAuthoringProfile::default()),
            Err(VmArtifactError::AllocationLimit { limit: 0 })));
    }

    fn edge_target(parameters: Vec<MirLocal>) -> MirBlock {
        MirBlock {
            scope: MirScopeId::ROOT,
            parameters,
            instructions: vec![],
            terminator: MirTerminator::Unreachable,
        }
    }

    #[test]
    fn parallel_edge_transfer_schedule_orders_chains_without_temporaries() {
        let target = edge_target(vec![MirLocal(1), MirLocal(2)]);
        let schedule = parallel_edge_transfers(&[MirLocal(0), MirLocal(1)], &target);

        assert_eq!(
            schedule,
            vec![
                EdgeTransfer::Direct {
                    dst: MirLocal(2),
                    src: MirLocal(1),
                },
                EdgeTransfer::Direct {
                    dst: MirLocal(1),
                    src: MirLocal(0),
                },
            ],
            "the destination that no later transfer reads is written first"
        );
        assert_eq!(edge_length(&[MirLocal(0), MirLocal(1)], &target), 3);
    }

    #[test]
    fn parallel_edge_transfer_schedule_breaks_each_cycle_once() {
        let target = edge_target(vec![MirLocal(0), MirLocal(1), MirLocal(2)]);
        let schedule = parallel_edge_transfers(&[MirLocal(1), MirLocal(2), MirLocal(0)], &target);

        assert_eq!(
            schedule,
            vec![EdgeTransfer::Cycle(vec![
                (MirLocal(0), MirLocal(1)),
                (MirLocal(1), MirLocal(2)),
                (MirLocal(2), MirLocal(0)),
            ])]
        );
        assert_eq!(
            edge_length(&[MirLocal(1), MirLocal(2), MirLocal(0)], &target),
            5,
            "three assignments use one save plus three writes and one jump"
        );
    }

    #[test]
    fn edge_emission_uses_one_temporary_for_a_three_way_parallel_cycle() {
        let target = edge_target(vec![MirLocal(0), MirLocal(1), MirLocal(2)]);
        let mut registers = vec![VmType::I64, VmType::I64, VmType::I64];
        let mut instructions = vec![];

        emit_edge(
            &[MirLocal(1), MirLocal(2), MirLocal(0)],
            &target,
            17,
            &mut registers,
            &mut instructions,
        );

        assert_eq!(registers, vec![VmType::I64, VmType::I64, VmType::I64, VmType::I64]);
        assert_eq!(
            instructions,
            vec![
                VmInstruction::Move { dst: 3, src: 1 },
                VmInstruction::Move { dst: 1, src: 2 },
                VmInstruction::Move { dst: 2, src: 0 },
                VmInstruction::Move { dst: 0, src: 3 },
                VmInstruction::Jump { target: 17 },
            ]
        );
    }


    fn artifact(registers: Vec<VmType>, instructions: Vec<VmInstruction>) -> CandidateVmArtifact {
        let mut artifact = CandidateVmArtifact {
            schema: STAGE0_VM_SCHEMA,
            runtime_manifest: None,
            function: VmFunction {
                safety: Safety::Safe,
                unsafe_execution: false,
                definition: DefKey(Digest::of_bytes(b"float-intrinsic-test")),
                nominal_copy_descriptors: vec![],
                captures: 0,
                parameters: 0,
                registers,
                instructions,
            },
            fingerprint: Digest::of_bytes(b"uninitialized"),
        };
        artifact.fingerprint = artifact.computed_fingerprint();
        artifact
    }

    #[test]
    fn manifest_bound_blake3_round_trips_through_encoding_and_verification() {
        let artifact = artifact(
            vec![VmType::Text, VmType::Bytes, VmType::Bytes],
            vec![
                VmInstruction::ConstText {
                    dst: 0,
                    value: "abc".into(),
                },
                VmInstruction::TextAsBytes { dst: 1, value: 0 },
                VmInstruction::Blake3 { dst: 2, value: 1 },
                VmInstruction::Return { value: 2 },
            ],
        );
        let bytes = encode_artifact(&artifact);
        let decoded = decode_artifact(&bytes).expect("BLAKE3 artifact decodes");
        let expected = blake3::hash(b"abc");
        let candidate = expect_bytes(
            execute(
                &decoded.function,
                &mut ExecutionBudget {
                    native_memory: NativeMemory::default(),
                    unsafe_execution: false,
                    limits: VmExecutionLimits::default(),
                    instructions: 0,
                    allocated_elements: 0,
                },
            )
            .unwrap(),
        )
        .unwrap();
        let verified = verify(decoded).unwrap();
        let verified_value = expect_bytes(verified.execute_with_limits(VmExecutionLimits::default()).unwrap())
            .unwrap();
        assert_eq!(candidate.as_ref(), expected.as_bytes());
        assert_eq!(verified_value.as_ref(), expected.as_bytes());
    }

    #[test]
    fn float_intrinsics_round_trip_f32_bits_and_checked_conversion() {
        let f64_to_f32 = PrimitiveRole::parse_selector_name("f64-to-f32").unwrap();
        let f32_bits = PrimitiveRole::parse_selector_name("f32-to-bits").unwrap();
        let f32_to_i32 = PrimitiveRole::parse_selector_name("f32-to-i32-checked").unwrap();
        let PrimitiveRole::Float(f64_to_f32) = f64_to_f32 else {
            panic!("float role")
        };
        let PrimitiveRole::Float(f32_bits) = f32_bits else {
            panic!("float role")
        };
        let PrimitiveRole::Float(f32_to_i32) = f32_to_i32 else {
            panic!("float role")
        };
        let artifact = artifact(
            vec![VmType::F64, VmType::F32, VmType::U32, VmType::I32],
            vec![
                VmInstruction::ConstF64 {
                    dst: 0,
                    bits: 3.5f64.to_bits(),
                },
                VmInstruction::FloatIntrinsic {
                    dst: 1,
                    primitive: f64_to_f32,
                    arguments: vec![0],
                },
                VmInstruction::FloatIntrinsic {
                    dst: 2,
                    primitive: f32_bits,
                    arguments: vec![1],
                },
                VmInstruction::FloatIntrinsic {
                    dst: 3,
                    primitive: f32_to_i32,
                    arguments: vec![1],
                },
                VmInstruction::Return { value: 3 },
            ],
        );
        let bytes = encode_artifact(&artifact);
        assert_eq!(
            decode_and_verify_artifact(&bytes)
                .unwrap()
                .run_i32()
                .unwrap(),
            3
        );
        assert_eq!(decode_artifact(&bytes).unwrap(), artifact);
    }

    #[test]
    fn checked_float_conversion_rejects_nan_and_out_of_range_values() {
        let PrimitiveRole::Float(primitive) =
            PrimitiveRole::parse_selector_name("f64-to-u8-checked").unwrap()
        else {
            panic!("float role")
        };
        let artifact = artifact(
            vec![VmType::F64, VmType::U8],
            vec![
                VmInstruction::ConstF64 {
                    dst: 0,
                    bits: f64::NAN.to_bits(),
                },
                VmInstruction::FloatIntrinsic {
                    dst: 1,
                    primitive,
                    arguments: vec![0],
                },
                VmInstruction::Return { value: 1 },
            ],
        );
        assert_eq!(
            verify(artifact).unwrap().run_u8(),
            Err(VmArtifactError::Trap)
        );
    }

    #[test]
    fn wide_integer_to_f32_rounds_once_at_halfway_boundaries() {
        let input = 9_223_372_586_610_589_697_u64;
        assert_ne!(input as f32, (input as f64) as f32);
        for (from, value) in [
            (ScalarType::U64, VmValue::U64(input)),
            (ScalarType::Usize, VmValue::Usize(input)),
            (ScalarType::U128, VmValue::U128(input as u128)),
            (ScalarType::I128, VmValue::I128(input as i128)),
        ] {
            let converted = execute_float_intrinsic(
                FloatPrimitive::Convert { from, to: ScalarType::F32, checked: false },
                &[0], &[Some(value)],
            ).unwrap();
            assert_eq!(expect_f32(converted).unwrap().to_bits(), (input as f32).to_bits());
        }
    }

    #[test]
    fn float_intrinsics_cover_arithmetic_comparison_and_integer_to_float() {
        let PrimitiveRole::Float(i64_to_f64) =
            PrimitiveRole::parse_selector_name("i64-to-f64").unwrap()
        else {
            panic!("float role")
        };
        let PrimitiveRole::Float(add) = PrimitiveRole::parse_selector_name("f64-add").unwrap()
        else {
            panic!("float role")
        };
        let PrimitiveRole::Float(compare) = PrimitiveRole::parse_selector_name("f64-gt").unwrap()
        else {
            panic!("float role")
        };
        let artifact = artifact(
            vec![
                VmType::I64,
                VmType::F64,
                VmType::F64,
                VmType::F64,
                VmType::U32,
            ],
            vec![
                VmInstruction::ConstI64 { dst: 0, value: 40 },
                VmInstruction::FloatIntrinsic {
                    dst: 1,
                    primitive: i64_to_f64,
                    arguments: vec![0],
                },
                VmInstruction::ConstF64 {
                    dst: 2,
                    bits: 2.0f64.to_bits(),
                },
                VmInstruction::FloatIntrinsic {
                    dst: 3,
                    primitive: add,
                    arguments: vec![1, 2],
                },
                VmInstruction::FloatIntrinsic {
                    dst: 4,
                    primitive: compare,
                    arguments: vec![3, 1],
                },
                VmInstruction::Return { value: 4 },
            ],
        );
        assert_eq!(verify(artifact).unwrap().run_u32().unwrap(), 1);
    }

    #[test]
    fn execution_budget_fails_closed_when_accounting_counters_overflow() {
        let limits = VmExecutionLimits {
            max_instructions: u64::MAX,
            max_allocation_elements: u64::MAX,
            ..VmExecutionLimits::default()
        };
        let mut instructions = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits,
            instructions: u64::MAX,
            allocated_elements: 0,
        };
        assert_eq!(
            instructions.tick(),
            Err(VmArtifactError::InstructionLimit {
                limit: u64::MAX,
            })
        );

        let mut allocations = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits,
            instructions: 0,
            allocated_elements: u64::MAX,
        };
        assert_eq!(
            allocations.reserve_allocation(1),
            Err(VmArtifactError::AllocationLimit {
                limit: u64::MAX,
            })
        );
    }
}
