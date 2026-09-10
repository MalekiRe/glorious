//! Deterministic stage-zero VM artifact emission and independent verification.
//!
//! This is a deliberately narrow artifact contract owned by the new compiler,
//! not a wrapper around the legacy compiler. Its candidate/verified split is
//! retained as instructions and types grow toward the repository `.grbc`
//! contract: execution receives only `VerifiedVmArtifact`.

use std::{
    borrow::Borrow,
    cell::RefCell,
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
        ConstKind, EffectTail, GenericArgument, Lifetime, PointerMutability, Safety, ScalarType, IntegerConstExpr, Type,
    },
};

use crate::MemoryPrimitive;

mod codec;
pub(crate) mod float_env;
pub use codec::{
    STAGE0_ARTIFACT_MAGIC, STAGE0_MAX_DECODE_FUNCTIONS, STAGE0_MAX_DECODE_INSTRUCTIONS,
    STAGE0_MAX_DECODE_REGISTERS, STAGE0_MAX_DECODE_TEXT_BYTES, STAGE0_PROGRAM_MAGIC,
    STAGE0_VM_SCHEMA, decode_artifact,
    decode_program, encode_artifact, encode_program,
};
use codec::{
    artifact_fingerprint, encode_integer_scalar, program_fingerprint, vm_effect_instance_key,
    vm_effect_row_projection_key,
};
pub(crate) use codec::vm_nominal_copy_descriptor_key;
mod native_memory;
mod native_residents;
mod native_profile;
mod native_bridge;
mod native_storage;
mod replay;
mod coverage;
mod tail_provenance;
mod label_dispatch;
mod resumption_values;
use resumption_values::ResumptionValue;
mod callable_access;
pub mod llvm;
mod reference_origins;
use reference_origins::ReferenceOriginSet;
pub use native_bridge::{
    VmNativeAbi, VmNativeCall, VmNativeCallback, VmNativeImport, VmNativeImports,
    VmNativeLayout, VmNativeLayoutField, VmNativeLayoutShape, VmNativeResidentContract, VmNativeStatus,
};
use native_memory::{NativeMemory, NativeReference, execute_memory_intrinsic};
pub use native_profile::VmNativeMemoryProfile;

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
    ConstInteger(crate::types::integer_const::IntegerConst),
    ConstIntegerExpr(IntegerConstExpr),
    ConstQuantity {
        lower: u64,
        upper: Option<u64>,
    },
    ConstGeneric {
        index: u32,
        kind: ConstKind,
    },
    Array(Box<VmType>),
    /// A sealed inline homogeneous product; unlike Array it has no resize ABI.
    FixedArray { element: Box<VmType>, length: u64 },
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
        arguments: Vec<VmGenericArgument>,
    },
    Callable {
        /// Receiver authority reconstructed from the executable capture body
        /// at every producer; these bits are not a trusted source annotation.
        shared_receiver: bool,
        unique_receiver: bool,
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

impl VmType {
    fn callable_receiver(&self) -> Option<&Self> {
        match self {
            Self::Callable { .. } => Some(self),
            Self::Reference { unique, referent } => match referent.as_ref() {
                Self::Callable { shared_receiver, unique_receiver, .. }
                    if if *unique { *unique_receiver } else { *shared_receiver } => Some(referent),
                _ => None,
            },
            _ => None,
        }
    }

    fn array_element(&self) -> Option<&VmType> {
        match self {
            Self::Array(element) | Self::FixedArray { element, .. } => Some(element),
            _ => None,
        }
    }

    pub(crate) fn array_accepts_pattern(&self, count: usize, rest: Option<crate::pattern::ArrayPatternRest>) -> bool {
        (rest.is_none() || matches!(self, Self::FixedArray { .. }))
            && crate::pattern::ArrayPatternRest::length(rest, count).is_some_and(|count| self.array_accepts_count(count))
    }

    fn array_accepts_count(&self, count: usize) -> bool {
        match self {
            Self::Array(_) => true,
            Self::FixedArray { length, .. } => u64::try_from(count).ok() == Some(*length),
            _ => false,
        }
    }
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
    /// Exact emitted glue for this environment's owned captures, if any.
    pub destructor: Option<DefKey>,
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
    ConstInteger(crate::types::integer_const::IntegerConst),
    /// Symbolic arithmetic remains a frozen, canonical const identity until
    /// the declaration binder is instantiated.  Do not replace it with an
    /// error type: handlers select on this full protocol identity.
    ConstIntegerExpr(IntegerConstExpr),
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
    pub tails: std::collections::BTreeSet<EffectTail>,
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
        rest: Option<crate::pattern::ArrayPatternRest>,
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

/// Inspection is not a whole-owner read. Wildcards inspect no bytes; structural
/// shells can survive moved fields, while array matching validates every element.
/// Explicit nominal fields additionally require their complete declared value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PatternRead { None, Root, Value }

impl VmPattern {
    pub(super) fn read_requirement(&self) -> PatternRead {
        match self {
            Self::Any => PatternRead::None,
            Self::Literal(_) | Self::Array { .. } => PatternRead::Value,
            Self::Tuple(_) | Self::Record { .. } | Self::Enum { .. } => PatternRead::Root,
        }
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmPatternField {
    pub index: u32,
    pub ty: VmType,
    pub pattern: VmPattern,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmFrameDrop {
    pub owner: u32,
    pub destructor: DefKey,
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
    /// Immutable whole-frame cleanup plan. When present, this is the unique
    /// second header instruction, never an executable control-flow choice.
    DeclareFrameCleanup {
        actions: Vec<VmFrameDrop>,
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
    /// Read the extent without copying or consuming the array.
    ArrayLen { dst: u32, value: u32 },
    /// Assign a compiler-owned, activation-local loop counter.
    StoreUsize { dst: u32, value: u32 },
    /// Probe a dynamically indexed move hole.
    ArrayElementIsInitialized { dst: u32, value: u32, index: u32 },
    /// Move one element out, leaving a hole in the owning array.
    TakeArrayElement { dst: u32, value: u32, index: u32 },
    ArrayGetBorrowShared {
        dst: u32,
        value: u32,
        index: u32,
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
    MakeTupleOwned { dst: u32, fields: Vec<u32> },
    MakeArrayOwned { dst: u32, fields: Vec<u32>, element_type: VmType },
    MakeRecordOwned { dst: u32, definition: DefKey, fields: Vec<u32>, field_types: Vec<VmType> },
    MakeEnumOwned { dst: u32, definition: DefKey, variant: u32, fields: Vec<u32>, field_types: Vec<VmType> },
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
    TakeProjection {
        dst: u32,
        base: u32,
        fields: Vec<u32>,
    },
    IsInitialized {
        dst: u32,
        base: u32,
        fields: Vec<u32>,
    },
    DestroyCallable {
        dst: u32,
        value: u32,
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
    /// Consumes every outgoing carrier before capturing the continuation.
    PerformOwned {
        dst: u32,
        effect: DefKey,
        effect_arguments: Vec<VmGenericArgument>,
        operation: u32,
        arguments: Vec<u32>,
    },
    /// Payload destinations are observation-only until explicitly claimed.
    InstallHandlerOwned {
        effect: DefKey,
        effect_arguments: Vec<VmGenericArgument>,
        operation: u32,
        payload_destinations: Vec<u32>,
        resume_type: VmType,
        continuation: VmContinuationPolicy,
        target: u32,
        replay_owned: Vec<u32>,
    },
    ClaimEffectPayloads { payloads: Vec<u32> },
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
    /// Return the protected value to a pending resumption of this exact
    /// handler activation, or fall through on ordinary completion.
    CompleteHandler { value: u32 },
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
    DerefIsInitialized {
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
    /// Consuming Runtime ABI. Legacy Call remains a test-compatibility opcode.
    CallOwned { dst: u32, callee: DefKey, arguments: Vec<u32> },
    /// Mandatory activation transfer. No result register or local continuation.
    TailCallOwned { callee: DefKey, arguments: Vec<u32> },
    /// Publish a prepared owner into source storage, consuming its carrier.
    /// Legacy Store is retained only for in-memory compatibility fixtures.
    StoreOwned { dst: u32, src: u32 },
    CallIndirectOwned { dst: u32, callee: u32, arguments: Vec<u32> },
    HostCallOwned {
        dst: u32,
        capability: String,
        symbol: String,
        source_contract: Digest,
        parameters: Vec<VmType>,
        result: VmType,
        resident_operations: Vec<VmNativeResident>,
        arguments: Vec<u32>,
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
        /// Declaration-owned safety/lifetime/use/evidence identity retained
        /// before lowering source types to their runtime representation.
        source_contract: Digest,
        parameters: Vec<VmType>,
        result: VmType,
        resident_operations: Vec<VmNativeResident>,
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
impl VmInstruction {
    pub(crate) fn with_owned_aggregate(self) -> Self {
        match self {
            Self::MakeTuple { dst, fields } => Self::MakeTupleOwned { dst, fields },
            Self::MakeArray { dst, fields, element_type } => Self::MakeArrayOwned { dst, fields, element_type },
            Self::MakeRecord { dst, definition, fields, field_types } => Self::MakeRecordOwned { dst, definition, fields, field_types },
            Self::MakeEnum { dst, definition, variant, fields, field_types } => Self::MakeEnumOwned { dst, definition, variant, fields, field_types },
            _ => unreachable!("only an aggregate constructor owns its prepared fields"),
        }
    }
    pub(crate) fn with_owned_effect_payloads(self) -> Self {
        match self {
            Self::Perform { dst, effect, effect_arguments, operation, arguments } =>
                Self::PerformOwned { dst, effect, effect_arguments, operation, arguments },
            Self::InstallHandler { effect, effect_arguments, operation, payload_destinations, resume_type, continuation, target } =>
                Self::InstallHandlerOwned { effect, effect_arguments, operation, payload_destinations, resume_type, continuation, target, replay_owned: vec![] },
            value => value,
        }
    }
    fn with_consumed_arguments(self) -> Self {
        match self {
            Self::Call { dst, callee, arguments } => Self::CallOwned { dst, callee, arguments },
            Self::CallIndirect { dst, callee, arguments } => Self::CallIndirectOwned { dst, callee, arguments },
            Self::HostCall { dst, capability, symbol, source_contract, parameters, result, resident_operations, arguments } =>
                Self::HostCallOwned { dst, capability, symbol, source_contract, parameters, result, resident_operations, arguments },
            _ => unreachable!("only a call ABI can consume prepared arguments"),
        }
    }
    fn consumed_arguments(&self) -> Option<&[u32]> {
        match self {
            Self::CallOwned { arguments, .. } | Self::CallIndirectOwned { arguments, .. }
            | Self::HostCallOwned { arguments, .. } | Self::TailCallOwned { arguments, .. } => Some(arguments),
            Self::StoreOwned { src, .. } => Some(std::slice::from_ref(src)),
            Self::MakeTupleOwned { fields, .. } | Self::MakeArrayOwned { fields, .. }
            | Self::MakeRecordOwned { fields, .. } | Self::MakeEnumOwned { fields, .. } => Some(fields),
            _ => None,
        }
    }
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
pub struct VmNativeResident {
    pub ty: VmType,
    /// Concrete source identity before lifetime erasure. Several source
    /// residents may have the same physical layout without the same contract.
    pub source_type: Digest,
    pub destructor: Option<DefKey>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmNominalCopyDescriptor {
    pub definition: DefKey,
    /// Source declaration identity retained across VM region erasure.
    pub source_contract: Digest,
    pub is_enum: bool,
    pub arguments: Vec<VmGenericArgument>,
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
    NativeAbi {
        message: &'static str,
    },
    UnsupportedNativeLayout {
        ty: VmType,
    },
    MalformedEncoding {
        message: &'static str,
    },
    UnprovenTailCarrier {
        message: &'static str,
        function: DefKey,
        pc: u32,
        register: u32,
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
    /// Live raw-buffer + native-home backing bytes, separate from logical
    /// register/element charges. This is not allocator overhead or RSS.
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

/// Authoring-runtime measurements, not compiler semantic counters. Logical
/// VM-budget charges and observed native backing extents are separate; neither
/// is a Rust allocator census.
/// The opt-in authoring runner can recycle caller-preserving self-tail calls
/// and reuse cleared register buffers from normally returned callees;
/// ordinary execution retains its existing call-depth behavior.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct VmAuthoringProfile {
    pub work_ticks: u64,
    pub charged_allocation_elements: u64,
    pub peak_call_depth: u32,
    pub recycled_tail_calls: u64,
    pub reused_call_register_buffers: u64,
    pub inspected_tail_argument_elements: u64,
    pub native_memory: VmNativeMemoryProfile,
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
/// Decode an untrusted envelope, then independently verify its candidate payload.
pub fn decode_and_verify_artifact(bytes: &[u8]) -> Result<VerifiedVmArtifact, VmArtifactError> {
    verify(decode_artifact(bytes)?)
}

/// Decode an untrusted program, then independently verify its candidate payload.
pub fn decode_and_verify_program(bytes: &[u8]) -> Result<VerifiedVmProgram, VmArtifactError> {
    verify_program(decode_program(bytes)?)
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
        format_vm_value(&value, &mut budget)
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
        let value = execute_with_arguments(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
        )?;
        format_vm_value(&value, &mut budget)
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
        let value = execute_with_arguments_with_host(
            &self.program,
            self.program.entry,
            &[],
            0,
            &mut budget,
            &mut host,
        )?;
        format_vm_value(&value, &mut budget)
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
        let (result, profile) = self.run_value_for_authoring(limits, false)?;
        Ok((expect_i64(result)?, profile))
    }

    /// Profile locally compiled source, including a trusted unsafe library.
    ///
    /// # Safety
    /// The caller upholds the per-execution obligations of `run_i64_with_unsafe`.
    pub unsafe fn run_i64_for_authoring_with_unsafe(
        &self, limits: VmExecutionLimits,
    ) -> Result<(i64, VmAuthoringProfile), VmArtifactError> {
        let (result, profile) = self.run_value_for_authoring(limits, true)?;
        Ok((expect_i64(result)?, profile))
    }

    /// Execute a batch while retaining every result for independent comparison.
    /// The batch shares the existing execution budget; it does not receive a
    /// larger limit or a fresh budget for each tuple element.
    pub fn run_tuple_i64_for_authoring(
        &self,
        limits: VmExecutionLimits,
    ) -> Result<(Vec<i64>, VmAuthoringProfile), VmArtifactError> {
        let (result, profile) = self.run_value_for_authoring(limits, false)?;
        Ok((expect_tuple_i64(result)?, profile))
    }

    /// Profile a source batch within one shared native-memory/budget domain.
    ///
    /// # Safety
    /// The caller upholds the per-execution obligations of `run_i64_with_unsafe`.
    pub unsafe fn run_tuple_i64_for_authoring_with_unsafe(
        &self, limits: VmExecutionLimits,
    ) -> Result<(Vec<i64>, VmAuthoringProfile), VmArtifactError> {
        let (result, profile) = self.run_value_for_authoring(limits, true)?;
        Ok((expect_tuple_i64(result)?, profile))
    }

    fn run_value_for_authoring(
        &self,
        limits: VmExecutionLimits,
        unsafe_execution: bool,
    ) -> Result<(VmValue, VmAuthoringProfile), VmArtifactError> {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::profiled(),
            unsafe_execution,
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
            false,
            None,
            None,
        )?;
        profile.work_ticks = budget.instructions;
        profile.charged_allocation_elements = budget.allocated_elements;
        profile.native_memory = budget.native_memory.measurements.as_ref()
            .expect("authoring execution owns native measurements").snapshot();
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

/// MIR block identities survive splitting and need not describe layout order.
/// The bytecode contract places each private handler entry after every site
/// installing it. Preserve source order where possible while satisfying those
/// dependencies, including installs relocated into appended cleanup blocks.
fn emission_block_order(function: &MirFunction) -> Result<Vec<usize>, VmArtifactError> {
    let mut successors = vec![BTreeSet::new(); function.blocks.len()];
    let mut predecessors = vec![0usize; function.blocks.len()];
    for (index, block) in function.blocks.iter().enumerate() {
        for instruction in &block.instructions {
            if let MirInstruction::InstallHandler { target, .. } = instruction {
                let target = target.0 as usize;
                if target >= function.blocks.len() {
                    return Err(VmArtifactError::UnsupportedControlFlow);
                }
                if successors[index].insert(target) {
                    predecessors[target] += 1;
                }
            }
        }
    }
    let mut ready = predecessors.iter().enumerate()
        .filter_map(|(index, count)| (*count == 0).then_some(index))
        .collect::<BTreeSet<_>>();
    let mut order = Vec::with_capacity(function.blocks.len());
    while let Some(index) = ready.pop_first() {
        order.push(index);
        for target in &successors[index] {
            predecessors[*target] -= 1;
            if predecessors[*target] == 0 { ready.insert(*target); }
        }
    }
    if order.len() != function.blocks.len() || order.first() != Some(&0) {
        return Err(VmArtifactError::UnsupportedControlFlow);
    }
    Ok(order)
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
    let order = emission_block_order(function)?;
    let mut starts = vec![0; function.blocks.len()];
    // Every emitted body starts with its sealed result/control declaration.
    let mut next = 1u32 + u32::from(!function.control.frame_cleanup.is_empty());
    for block_index in &order {
        let block = &function.blocks[*block_index];
        starts[*block_index] = next;
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
    if !function.control.frame_cleanup.is_empty() {
        instructions.push(VmInstruction::DeclareFrameCleanup {
            actions: function.control.frame_cleanup.iter().map(|action| VmFrameDrop {
                owner: action.owner.0, destructor: action.destructor,
            }).collect(),
        });
    }
    for block_index in order {
        let block = &function.blocks[block_index];
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
pub(crate) fn vm_instructions_may_return(instructions: &[VmInstruction]) -> bool {
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
            | VmInstruction::TailCallOwned { .. }
            | VmInstruction::Resume { .. }
            | VmInstruction::ResumeSnapshot { .. }
            | VmInstruction::Forward => {}
            VmInstruction::Jump { target }
            | VmInstruction::Leave { target, .. } => pending.push(*target),
            // These instructions register a dynamic entry and then continue
            // normally. Either continuation can eventually return: a terminal
            // perform in the protected computation does not make its handler's
            // returning clause unreachable.
            VmInstruction::MakeLabel { target, .. }
            | VmInstruction::InstallHandler { target, .. }
            | VmInstruction::InstallHandlerOwned { target, .. } => {
                pending.push(*target);
                pending.push(pc.saturating_add(1));
            }
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
    parallel_edge_transfers(arguments, &target.parameters)
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
    emit_parallel_moves(arguments, &target.parameters, registers, instructions);
    instructions.push(VmInstruction::Jump { target: destination });
}

/// Shared machine-level parallel assignment scheduler; it knows no source
/// semantics and is also used when VM LIR splits branch edges.
pub(crate) fn emit_parallel_moves(
    arguments: &[MirLocal],
    destinations: &[MirLocal],
    registers: &mut Vec<VmType>,
    instructions: &mut Vec<VmInstruction>,
) {
    for transfer in parallel_edge_transfers(arguments, destinations) {
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
    destinations: &[MirLocal],
) -> Vec<EdgeTransfer> {
    let mut pending = arguments
        .iter()
        .zip(destinations)
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
pub(crate) fn vm_nominal_copy_descriptor(
    descriptor: &crate::mir::MirNominalCopyDescriptor,
) -> Result<VmNominalCopyDescriptor, VmArtifactError> {
    Ok(VmNominalCopyDescriptor {
        is_enum: descriptor.is_enum,
        definition: descriptor.definition,
        source_contract: descriptor.source_contract,
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
pub(crate) fn vm_type(value: &Type) -> Result<VmType, Box<Type>> {
    // The existing VM control-capability carrier shares an invocation shape
    // with callable registers. Source nominal identity is not reconstructed
    // from this physical view: MakeLabel retains the exact branded target.
    if let Some(callable) = crate::types::label::callable(value) { return vm_type(&callable); }
    match value {
        // A pending environment witness is proof-only. Until the control
        // producer supplies a sealed runtime owner and disposal plan, an
        // ordinary nominal layout cannot represent it (even as a ZST).
        Type::Nominal { definition, .. }
            if *definition == crate::intrinsic_available_type_definition() => Err(Box::new(value.clone())),
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
        Type::ConstInteger(value) => Ok(VmType::ConstInteger((*value).into())),
        Type::ConstQuantity(value) => Ok(VmType::ConstQuantity {
            lower: value.lower,
            upper: value.upper,
        }),
        Type::ConstGeneric { index, kind } => Ok(VmType::ConstGeneric {
            index: *index,
            kind: *kind,
        }),
        Type::Array(element) => Ok(VmType::Array(Box::new(vm_type(element)?))),
        Type::FixedArray { element, .. } => Ok(VmType::FixedArray {
            element: Box::new(vm_type(element)?),
            length: value.fixed_array_length().ok_or_else(|| Box::new(value.clone()))?,
        }),
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
            contract,
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
                shared_receiver: contract.shared_receiver,
                unique_receiver: contract.unique_receiver,
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
        tails: value.tails.clone(),
    })
}

/// Body-region identity is source proof, not an effect dispatch token. Keep
/// declaration identities as before; erase only closed body existentials at
/// the same boundary that removes reference regions from value layouts.
fn vm_lifetime(value: Lifetime) -> Lifetime {
    match value {
        Lifetime::Inferred(_) => Lifetime::Elided,
        value => value,
    }
}

fn vm_effect_generic_argument(
    value: &crate::GenericArgument,
) -> Result<VmGenericArgument, Box<Type>> {
    use crate::GenericArgument;

    Ok(match value {
        GenericArgument::Type(value) => VmGenericArgument::Type(vm_type(value)?),
        GenericArgument::EffectRow(value) => VmGenericArgument::EffectRow(vm_effect_row(value)?),
        GenericArgument::Lifetime(value) => VmGenericArgument::Lifetime(vm_lifetime(*value)),
        GenericArgument::ConstInteger(value) => VmGenericArgument::ConstInteger((*value).into()),
        GenericArgument::ConstIntegerExpr(value) => VmGenericArgument::ConstIntegerExpr(value.clone()),
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

/// Preserve type/row/const kinds in nominal identity. The caller erases
/// lifetime slots only after source field substitution has checked them.
fn vm_nominal_argument(value: &GenericArgument) -> Result<VmGenericArgument, Box<Type>> {
    vm_effect_generic_argument(value)
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
                tails: value.tails.clone(),
            })
        }
        GenericArgument::Lifetime(value) => VmGenericArgument::Lifetime(vm_lifetime(*value)),
        GenericArgument::ConstInteger(value) => VmGenericArgument::ConstInteger((*value).into()),
        GenericArgument::ConstIntegerExpr(value) => VmGenericArgument::ConstIntegerExpr(value.clone()),
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
pub fn verify_program(program: CandidateVmProgram) -> Result<VerifiedVmProgram, VmArtifactError> {
    validate_program(&program, None)?;
    Ok(VerifiedVmProgram { program })
}

/// One checked program-wide layout table. Function-local descriptor demands
/// need not include types reached only through reference handles; their
/// defining residents elsewhere in this graph supply the same layout authority.
fn program_nominal_layouts(program: &CandidateVmProgram)
    -> Result<BTreeMap<Vec<u8>, VmNominalCopyDescriptor>, VmArtifactError> {
    let mut layouts = BTreeMap::new();
    for descriptor in program.functions.values().flat_map(|function| &function.nominal_copy_descriptors) {
        let key = vm_nominal_copy_descriptor_key(descriptor);
        if let Some(previous) = layouts.get(&key) {
            if previous != descriptor {
                return Err(VmArtifactError::MalformedEncoding {
                    message: "program nominal layout declarations disagree",
                });
            }
        } else {
            layouts.insert(key, descriptor.clone());
        }
    }
    Ok(layouts)
}

// Public/decoded bytecode always reconstructs semantics from its own bodies.
// The optional source is used only by the private compiler-generated native
// execution adapter, never to produce a portable VerifiedVmProgram.
fn validate_program(program: &CandidateVmProgram, native_semantics: Option<&VerifiedVmProgram>) -> Result<(), VmArtifactError> {
    let semantics = native_semantics.map_or(program, |source| &source.program);
    let source_layouts = program_nominal_layouts(semantics)?;
    if native_semantics.is_some() && (program.functions.keys().ne(semantics.functions.keys())
        || program.callable_environments != semantics.callable_environments
        || program.functions.iter().any(|(key, adapter)| {
            let source = &semantics.functions[key];
            adapter.captures != source.captures || adapter.parameters != source.parameters
                || adapter.registers.get(..adapter.parameters as usize) != source.registers.get(..source.parameters as usize)
                || adapter.instructions.first() != source.instructions.first()
                // Adapter imports require a transitive ABI layout closure,
                // including borrowed pointees. Those descriptors may be
                // declared by a different source function, but every one
                // must come unchanged from this exact sealed source graph.
                || source.nominal_copy_descriptors.iter().any(|descriptor|
                    !adapter.nominal_copy_descriptors.contains(descriptor))
                || adapter.nominal_copy_descriptors.iter().any(|descriptor|
                    source_layouts.get(&vm_nominal_copy_descriptor_key(descriptor)) != Some(descriptor))
                || adapter.safety != source.safety
        })) {
        return Err(VmArtifactError::MalformedEncoding { message: "generated adapter differs from its source invocation contract" });
    }
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
    if native_semantics.is_some() { program_nominal_layouts(program)?; }
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
    for function in semantics.functions.values() {
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
        if let Some(destructor) = environment.destructor {
            if destructor != crate::mir::callable_environment_destructor_definition(*callee) {
                return Err(VmArtifactError::InvalidCallableEnvironment {
                    message: "capture destruction does not belong to its callable",
                });
            }
            let cleanup = program.functions.get(&destructor)
                .ok_or(VmArtifactError::MissingFunction { definition: destructor })?;
            if cleanup.captures != 0 || cleanup.parameters as usize != environment.captures.len()
                || !matches!(declared_result(cleanup)?, Some((VmType::Unit, true))) || cleanup.safety != Safety::Safe
                || environment.captures.iter().enumerate().any(|(index, capture)|
                    cleanup.registers.get(index) != Some(&capture.ty))
            {
                return Err(VmArtifactError::InvalidCallableEnvironment {
                    message: "capture destruction has an incompatible environment ABI",
                });
            }
        }
    }
    let transfer_proofs = tail_provenance::summaries(
        &semantics.functions)?;
    let mut intact_captures = BTreeMap::new();
    for function in program.functions.values() {
        let control = verify_function_control(function, true, false, &transfer_proofs)?;
        let intact = if native_semantics.is_some() && function.captures != 0 {
            verify_function_control(&semantics.functions[&function.definition], true, false, &transfer_proofs)?.captures_intact_at_boundaries
        } else { control.captures_intact_at_boundaries };
        intact_captures.insert(function.definition, intact);
        for action in declared_frame_cleanup(function)? {
            let target = program.functions.get(&action.destructor)
                .ok_or(VmArtifactError::MissingFunction { definition: action.destructor })?;
            if target.captures != 0 || target.parameters != 1 || target.safety != Safety::Safe
                || target.registers.first() != function.registers.get(action.owner as usize)
                || !matches!(declared_result(target)?, Some((VmType::Unit, true)))
            {
                return Err(VmArtifactError::MalformedEncoding {
                    message: "frame cleanup target has an incompatible owner ABI",
                });
            }
        }
    }
    native_bridge::validate_resident_operations(&program)?;
    verify_program_effect_operation_abis(&program.functions)?;
    for function in program.functions.values() {
        for instruction in &function.instructions {
            if let VmInstruction::TailCallOwned { callee, arguments } = instruction {
                let target = program.functions.get(callee)
                    .ok_or(VmArtifactError::MissingFunction { definition: *callee })?;
                if target.safety == Safety::Unsafe && !function.unsafe_execution {
                    return Err(VmArtifactError::MalformedEncoding { message: "mandatory tail target has an incompatible activation-transfer ABI" });
                }
                verify_direct_call_abi(function, target, arguments, DirectCallResult::CallerContinuation)?;
            }
            if let VmInstruction::CallOwned { dst, callee, arguments }
            | VmInstruction::Call {
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
                verify_direct_call_abi(function, target, arguments, DirectCallResult::Register(*dst))?;
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
                    shared_receiver, unique_receiver, safety, parameters, result, ..
                } = register_type(function, *dst)?
                else {
                    return Err(VmArtifactError::NotCallable { register: *dst });
                };
                if safety != target.safety {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "callable value safety does not match its target",
                    });
                }
                callable_access::verify_claim(&semantics.functions[callee], shared_receiver, unique_receiver,
                    intact_captures.get(callee) == Some(&true))?;
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
                    && !unify_call_type_variance(&declared_return, result.as_ref(), &mut generic_bindings, ReceiverVariance::Contravariant)
                {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: declared_return,
                        found: *result,
                    });
                }
                verify_effect_operation_specialization(target, &generic_bindings)?;
                let expected = instantiate_vm_type(&declared_return, &generic_bindings);
                if target_returns && !vm_type_matches(&expected, result.as_ref()) {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected,
                        found: *result,
                    });
                }
            }
        }
    }
    Ok(())
}

/// Tail activation transfer inherits a continuation instead of allocating a
/// local result slot. This changes control, not the target's value ABI.
#[derive(Clone, Copy)]
enum DirectCallResult {
    Register(u32),
    CallerContinuation,
}

fn verify_direct_call_abi(
    caller: &VmFunction,
    target: &VmFunction,
    arguments: &[u32],
    result: DirectCallResult,
) -> Result<(), VmArtifactError> {
    if target.captures != 0 {
        return Err(VmArtifactError::CallArity { expected: 0, found: target.captures });
    }
    if target.parameters as usize != arguments.len() {
        return Err(VmArtifactError::CallArity {
            expected: target.parameters, found: arguments.len() as u32,
        });
    }
    let mut generic_bindings = BTreeMap::new();
    for (index, argument) in arguments.iter().enumerate() {
        let expected = register_type(target, index as u32)?;
        let found = register_type(caller, *argument)?;
        if !unify_call_type(&expected, &found, &mut generic_bindings) {
            return Err(VmArtifactError::TypeMismatch { register: *argument, expected, found });
        }
    }
    let target_result = declared_result(target)?;
    let found = match result {
        DirectCallResult::Register(register) => register_type(caller, register)?,
        DirectCallResult::CallerContinuation => match (declared_result(caller)?, target_result) {
            // A terminal target has no normal payload. A returning target
            // still cannot inherit a continuation declared non-returning.
            (Some((source, _)), Some((_, false)))
            | (Some((source, true)), Some((_, true))) => source.clone(),
            _ => return Err(VmArtifactError::MalformedEncoding {
                message: "mandatory tail target has an incompatible activation-transfer ABI",
            }),
        },
    };
    let mismatch = |expected, found| match result {
        DirectCallResult::Register(register) => VmArtifactError::TypeMismatch { register, expected, found },
        DirectCallResult::CallerContinuation => VmArtifactError::MalformedEncoding {
            message: "mandatory tail target has an incompatible activation-transfer ABI",
        },
    };
    // Only the sealed control declaration, not a synthetic Unit leaf,
    // determines whether a bottom-coerced call supplies a normal result.
    let target_returns = target_result.map(|(_, returns)| returns).unwrap_or(true);
    let declared_return = return_type(target)?;
    // Inputs and the destination constrain the same target-local binders.
    // The destination can be the only evidence for a zero-input constructor.
    // Reverse receiver variance because the target supplies this value.
    if target_returns && !unify_call_type_variance(
        &declared_return, &found, &mut generic_bindings, ReceiverVariance::Contravariant,
    ) {
        return Err(mismatch(declared_return, found));
    }
    verify_effect_operation_specialization(target, &generic_bindings)?;
    let expected = instantiate_vm_type(&declared_return, &generic_bindings);
    if target_returns && !vm_type_matches(&expected, &found) {
        return Err(mismatch(expected, found));
    }
    Ok(())
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
            VmInstruction::PerformOwned {
                dst,
                effect_arguments,
                arguments,
                ..
            }
            | VmInstruction::Perform {
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
            VmInstruction::InstallHandlerOwned {
                effect_arguments,
                payload_destinations,
                resume_type,
                ..
            }
            | VmInstruction::InstallHandler {
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
    let mut operations = Vec::<(DefKey, Vec<VmGenericArgument>, u32, Vec<VmType>, VmType, bool, bool)>::new();
    for function in functions.values() {
        for instruction in &function.instructions {
            let (effect, effect_arguments, operation, payloads, resume_type) = match instruction {
                VmInstruction::PerformOwned {
                    dst,
                    effect,
                    effect_arguments,
                    operation,
                    arguments,
                }
                | VmInstruction::Perform {
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
                VmInstruction::InstallHandlerOwned {
                    effect,
                    effect_arguments,
                    operation,
                    payload_destinations,
                    resume_type,
                    ..
                }
                | VmInstruction::InstallHandler {
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
            let owned_payloads = matches!(instruction, VmInstruction::PerformOwned { .. } | VmInstruction::InstallHandlerOwned { .. });
            let producer = matches!(instruction, VmInstruction::PerformOwned { .. } | VmInstruction::Perform { .. });
            for (_, _, _, expected_payloads, expected_resume_type, expected_owned_payloads, previous_producer) in operations
                .iter()
                .filter(|(known_effect, known_arguments, known_operation, _, _, _, _)| {
                    *known_effect == effect
                        && *known_arguments == effect_arguments
                        && *known_operation == operation
                })
            {
                let same_shape = expected_payloads.len() == payloads.len()
                    && expected_payloads.iter().zip(&payloads).all(|(expected, actual)|
                        receiver_types_match(expected, actual, ReceiverVariance::Shape))
                    && receiver_types_match(expected_resume_type, &resume_type, ReceiverVariance::Shape);
                // Every potential dynamic handler must accept every sender.
                // Its resume argument travels in the opposite direction.
                // Comparing only the first sighting is insufficient when two
                // senders provide different callable receiver permissions.
                let transfers = producer == *previous_producer || if producer {
                    expected_payloads.iter().zip(&payloads).all(|(expected, actual)|
                        receiver_types_match(expected, actual, ReceiverVariance::Covariant))
                        && receiver_types_match(&resume_type, expected_resume_type, ReceiverVariance::Covariant)
                } else {
                    payloads.iter().zip(expected_payloads).all(|(expected, actual)|
                        receiver_types_match(expected, actual, ReceiverVariance::Covariant))
                        && receiver_types_match(expected_resume_type, &resume_type, ReceiverVariance::Covariant)
                };
                if !same_shape || !transfers || *expected_owned_payloads != owned_payloads {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "program effect operation ABI declarations disagree",
                    });
                }
            }
            let contract = (effect, effect_arguments, operation, payloads, resume_type, owned_payloads, producer);
            if !operations.contains(&contract) { operations.push(contract); }
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
pub(crate) fn reachable_host_capabilities(
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
                VmInstruction::HostCallOwned { capability, resident_operations, .. }
                | VmInstruction::HostCall { capability, resident_operations, .. } => {
                    capabilities.insert(capability.clone());
                    pending.extend(resident_operations.iter().filter_map(|resident| resident.destructor));
                }
                VmInstruction::MakeCallable { callee, environment, .. } => {
                    pending.push(*callee);
                    pending.extend(environment.as_ref().and_then(|environment| environment.destructor));
                }
                VmInstruction::CallOwned { callee, .. } | VmInstruction::Call { callee, .. }
                | VmInstruction::TailCallOwned { callee, .. } => {
                    pending.push(*callee)
                }
                VmInstruction::DeclareFrameCleanup { actions } => {
                    pending.extend(actions.iter().map(|action| action.destructor));
                }
                _ => {}
            }
        }
    }
    capabilities.into_iter().collect()
}

/// Receiver permissions follow callable variance, not structural covariance:
/// inputs reverse it, mutable storage fixes it, and results preserve it.
#[derive(Clone, Copy)]
enum ReceiverVariance { Covariant, Contravariant, Invariant, Shape }

impl ReceiverVariance {
    fn reversed(self) -> Self {
        match self { Self::Covariant => Self::Contravariant, Self::Contravariant => Self::Covariant, Self::Invariant => Self::Invariant, Self::Shape => Self::Shape }
    }

    fn permits(self, expected: bool, actual: bool) -> bool {
        match self { Self::Covariant => !expected || actual, Self::Contravariant => !actual || expected, Self::Invariant => expected == actual, Self::Shape => true }
    }
}

/// Compare types in one already-scoped activation. Unlike call inference,
/// this operation cannot instantiate a generic register with another type.
fn receiver_types_match(expected: &VmType, actual: &VmType, variance: ReceiverVariance) -> bool {
    let mut bindings = BTreeMap::new();
    unify_call_type_variance(expected, actual, &mut bindings, variance)
        && bindings.iter().all(|(index, value)| *value == VmType::Generic(*index))
}

/// A shared view may forget callable permissions, while writable referents
/// remain invariant. Concrete storage views do not infer generic arguments
/// or change the backing origin's layout. VM borrowing and native reference
/// byte admission consume this same relation.
fn reference_view_matches(expected: &VmType, actual: &VmType, unique: bool) -> bool {
    receiver_types_match(expected, actual,
        if unique { ReceiverVariance::Invariant } else { ReceiverVariance::Covariant })
}

/// Match a callee-side type against one caller-side type while collecting the
/// callee's binder-local generic arguments. These binders are scoped to the
/// target function, so identical numeric indices in two functions never alias.
fn unify_call_type(
    expected: &VmType,
    found: &VmType,
    bindings: &mut BTreeMap<u32, VmType>,
) -> bool {
    unify_call_type_variance(expected, found, bindings, ReceiverVariance::Covariant)
}

fn unify_call_type_variance(
    expected: &VmType,
    found: &VmType,
    bindings: &mut BTreeMap<u32, VmType>,
    variance: ReceiverVariance,
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
                .all(|(expected, found)| unify_call_type_variance(expected, found, bindings, variance)),
            _ => false,
        },
        VmType::FixedArray { element, length } => match found {
            VmType::FixedArray { element: found, length: count } if length == count => unify_call_type_variance(element, found, bindings, variance),
            _ => false,
        },
        VmType::Array(expected) => match found {
            VmType::Array(found) => unify_call_type_variance(expected, found, bindings, variance),
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
                unify_call_type_variance(expected_element, found_element, bindings, variance)
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
                unify_call_type_variance(expected_referent, found_referent, bindings,
                    if *expected_unique { ReceiverVariance::Invariant } else { variance })
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
                    .all(|(expected, found)| unify_vm_generic_argument(expected, found, bindings))
            }
            _ => false,
        },
        VmType::Callable {
            shared_receiver: expected_shared,
            unique_receiver: expected_unique,
            safety: expected_safety,
            parameters: expected_parameters,
            result: expected_result,
            effects: expected_effects,
        } => match found {
            VmType::Callable {
                shared_receiver: found_shared,
                unique_receiver: found_unique,
                safety: found_safety,
                parameters: found_parameters,
                result: found_result,
                effects: found_effects,
            } if variance.permits(*expected_shared, *found_shared) && variance.permits(*expected_unique, *found_unique)
                && expected_safety == found_safety && expected_parameters.len() == found_parameters.len() => {
                expected_parameters
                    .iter()
                    .zip(found_parameters)
                    .all(|(expected, found)| unify_call_type_variance(expected, found, bindings, variance.reversed()))
                    && unify_call_type_variance(expected_result, found_result, bindings, variance)
                    && unify_vm_effect_row(expected_effects, found_effects, bindings)
            }
            _ => false,
        },
        VmType::RawPointer { mutability, pointee } => match found {
            VmType::RawPointer { mutability: found_mutability, pointee: found_pointee }
                if mutability == found_mutability => unify_call_type_variance(pointee, found_pointee, bindings, ReceiverVariance::Invariant),
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
        VmType::FixedArray { element, length } => VmType::FixedArray {
            element: Box::new(instantiate_vm_type(element, bindings)), length: *length,
        },
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
                .map(|argument| instantiate_vm_generic_argument(argument, bindings))
                .collect(),
        },
        VmType::Callable {
            shared_receiver,
            unique_receiver,
            safety,
            parameters,
            result,
            effects,
        } => VmType::Callable {
            shared_receiver: *shared_receiver,
            unique_receiver: *unique_receiver,
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
    expected.tails == found.tails
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
                unify_call_type_variance(&expected.subject, &found.subject, bindings, ReceiverVariance::Invariant)
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
            unify_call_type_variance(expected, found, bindings, ReceiverVariance::Invariant)
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
        tails: value.tails.clone(),
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

fn declared_frame_cleanup(function: &VmFunction) -> Result<&[VmFrameDrop], VmArtifactError> {
    let mut found = &[][..];
    for (index, instruction) in function.instructions.iter().enumerate() {
        if let VmInstruction::DeclareFrameCleanup { actions } = instruction {
            if index != 1 || !matches!(function.instructions.first(), Some(VmInstruction::DeclareResult { .. }))
                || actions.is_empty()
            {
                return Err(VmArtifactError::MalformedEncoding {
                    message: "frame cleanup declaration must be a nonempty second header",
                });
            }
            let mut owners = BTreeSet::new();
            for action in actions {
                register_type(function, action.owner)?;
                if action.owner < function.captures || !owners.insert(action.owner) {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "frame cleanup repeats an owner or owns an invocation capture",
                    });
                }
            }
            found = actions.as_slice();
        }
    }
    Ok(found)
}

pub(crate) fn lower_instruction(
    value: &MirInstruction,
    starts: &[u32],
) -> Result<VmInstruction, VmArtifactError> {
    let instruction = match value {
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
        MirInstruction::StoreUsize { dst, value } => VmInstruction::StoreUsize { dst: dst.0, value: value.0 },
        MirInstruction::ArrayLen { dst, value } => VmInstruction::ArrayLen { dst: dst.0, value: value.0 },
        MirInstruction::ArrayElementIsInitialized { dst, value, index } => VmInstruction::ArrayElementIsInitialized { dst: dst.0, value: value.0, index: index.0 },
        MirInstruction::TakeArrayElement { dst, value, index } => VmInstruction::TakeArrayElement { dst: dst.0, value: value.0, index: index.0 },
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
        MirInstruction::ArrayGetBorrowShared {
            dst,
            value,
            index,
            element_type,
        } => VmInstruction::ArrayGetBorrowShared {
            dst: dst.0,
            value: value.0,
            index: index.0,
            element_type: vm_type(element_type)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
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
        MirInstruction::Drop { .. } => return Err(VmArtifactError::MalformedEncoding {
            message: "unelaborated destruction reached VM lowering",
        }),
        MirInstruction::TakeProjection { dst, base, fields } => VmInstruction::TakeProjection {
            dst: dst.0, base: base.0, fields: fields.clone(),
        },
        MirInstruction::IsInitialized { dst, base, fields } => VmInstruction::IsInitialized {
            dst: dst.0, base: base.0, fields: fields.clone(),
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
        MirInstruction::ClaimEffectPayloads { payloads } => VmInstruction::ClaimEffectPayloads {
            payloads: payloads.iter().map(|value| value.0).collect(),
        },
        MirInstruction::UninstallHandler => VmInstruction::UninstallHandler,
        MirInstruction::CompleteHandler { value } => VmInstruction::CompleteHandler { value: value.0 },
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
        MirInstruction::DerefIsInitialized { dst, reference } => VmInstruction::DerefIsInitialized {
            dst: dst.0, reference: reference.0,
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
        MirInstruction::CallOwned { dst, callee, arguments }
        | MirInstruction::Call {
            dst,
            callee,
            arguments,
            ..
        } => VmInstruction::Call {
            dst: dst.0,
            callee: *callee,
            arguments: arguments.iter().map(|argument| argument.0).collect(),
        },
        MirInstruction::HostCallOwned { dst, capability, symbol, source_contract, parameters, result, resident_operations, arguments }
        | MirInstruction::HostCall {
            dst,
            capability,
            symbol,
            source_contract,
            parameters,
            result,
            resident_operations,
            arguments,
        } => VmInstruction::HostCall {
            dst: dst.0,
            capability: capability.clone(),
            symbol: symbol.clone(),
            source_contract: *source_contract,
            parameters: parameters
                .iter()
                .map(vm_type)
                .collect::<Result<Vec<_>, _>>()
                .map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
            result: vm_type(result)
                .map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
            resident_operations: {
                let mut residents = resident_operations.iter().map(|(ty, destructor)| Ok(VmNativeResident {
                    ty: vm_type(ty).map_err(|ty| VmArtifactError::UnsupportedType { local: dst.0, ty })?,
                    source_type: Digest::of_bytes(&crate::types::canonical_type_encoding(ty)),
                    destructor: *destructor,
                })).collect::<Result<Vec<_>, VmArtifactError>>()?;
                residents.sort_by_key(|resident| resident.source_type);
                residents
            },
            arguments: arguments.iter().map(|argument| argument.0).collect(),
        },
        MirInstruction::Abort => VmInstruction::Trap,
        MirInstruction::DestroyCallable { dst, value } => VmInstruction::DestroyCallable {
            dst: dst.0, value: value.0,
        },
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
                        destructor: environment.destructor,
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
        MirInstruction::CallIndirectOwned { dst, callee, arguments }
        | MirInstruction::CallIndirect {
            dst,
            callee,
            arguments,
        } => VmInstruction::CallIndirect {
            dst: dst.0,
            callee: callee.0,
            arguments: arguments.iter().map(|argument| argument.0).collect(),
        },
    };
    Ok(if matches!(value, MirInstruction::CallOwned { .. } | MirInstruction::CallIndirectOwned { .. } | MirInstruction::HostCallOwned { .. }) {
        instruction.with_consumed_arguments()
    } else { instruction })
}
fn lower_pattern(value: &MirPattern) -> VmPattern {
    match value {
        MirPattern::Any => VmPattern::Any,
        MirPattern::Literal(value) => VmPattern::Literal(value.clone()),
        MirPattern::Tuple(values) => VmPattern::Tuple(values.iter().map(lower_pattern).collect()),
        MirPattern::Array { element, elements, rest } => VmPattern::Array {
            rest: *rest,
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
    if !matches!(pattern, VmPattern::Any) && let VmType::Reference { referent, .. } = subject {
        return verify_pattern(pattern, referent);
    }
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
        VmPattern::Array { element, elements, rest } => match subject {
            actual if actual.array_element() == Some(element) && actual.array_accepts_pattern(elements.len(), *rest) => elements
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
        VmType::F32 => matches!(exact_scalar_literal_kind(value), Some(TokenKind::Integer | TokenKind::Float))
            && crate::mir::parse_f32_literal(value).is_ok(),
        VmType::F64 => matches!(exact_scalar_literal_kind(value), Some(TokenKind::Integer | TokenKind::Float))
            && parse_f64_literal(value).is_ok(),
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
    owned_payloads: bool,
    /// None while active, false while testing a packet, true after its claim.
    payload_claim: Option<bool>,
    payload_domain: Option<coverage::Domain>,
    payload_probe: Option<(u32, usize, VmPattern)>,
    /// A verifier join can represent several concrete one-shot suspensions
    /// reaching one shared handler body. Runtime execution has exactly one.
    continuations: Vec<VerifierContinuation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct VerifierContinuation {
    target: u32,
    dst: u32,
    registers: Vec<Option<bool>>,
    may_initialized: Vec<bool>,
    /// The continuation resumes the exact source-storage lifetime state at
    /// the performance site.  Register initialization alone cannot recover
    /// this fact: `Some(false)` means either a moved SSA value or a live,
    /// uninitialized addressable slot.
    storage_live: Vec<bool>,
    /// Every source-storage root a reference value may address.  A join of
    /// two references with distinct roots must retain both possibilities:
    /// preserving only the predecessor that happened to arrive first would
    /// permit `StorageDead` to erase the other live loan.
    reference_origins: Vec<ReferenceOriginSet>,
    frame_independent: Vec<bool>,
    referent_independent: Vec<bool>,
    local_labels: Vec<Option<label_dispatch::LocalLabel>>,
    destruction_preserves_frames: Vec<bool>,
    invocation_preserves_frames: Vec<bool>,
    labels: Vec<bool>,
    /// The same resident-value provenance is restored with the continuation.
    resumptions: Vec<ResumptionValue>,
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
    /// Exact immediate CFG predecessor, when all paths agree. Adjacency in
    /// the instruction vector alone does not authenticate a runtime probe.
    last_instruction: Option<usize>,
    registers: Vec<Option<bool>>,
    /// A may fact, distinct from readability's must fact. A branch-local
    /// carrier is unreadable after a join but can still owe destruction.
    may_initialized: Vec<bool>,
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
    reference_origins: Vec<ReferenceOriginSet>,
    /// Positive must evidence that every embedded address/control carrier
    /// survives replacement of this activation. Unknown producers are false.
    frame_independent: Vec<bool>,
    /// A reference can address a local slot whose resident graph contains no
    /// activation address. This does not certify the reference itself.
    referent_independent: Vec<bool>,
    local_labels: Vec<Option<label_dispatch::LocalLabel>>,
    destruction_preserves_frames: Vec<bool>,
    invocation_preserves_frames: Vec<bool>,
    /// A first-class lexical label shares the callable ABI but can only be
    /// invoked in the frame that minted it. This taint is propagated through
    /// aggregates because a label cannot be frozen into another callable
    /// environment even when nested inside an otherwise ordinary value.
    labels: Vec<bool>,
    /// One structural value domain retains both possible resumption contents
    /// and exact callable leaves. Only a leaf naming a live frame can resume;
    /// unknown/expired contents still forbid an escaping frame transfer.
    resumptions: Vec<ResumptionValue>,
    handlers: Vec<VerifierHandlerFrame>,
    pending_leave: Option<PendingLeave>,
    /// Whether `Return` belongs to a callable resumption rather than to the
    /// enclosing function. Dynamic recursion depth is not a static fact.
    resuming: bool,
    /// Handler brands that may remain active while the current protected
    /// replay returns to its clause. A nested operation can cancel its own
    /// frame and still leave an outer replay frame to be restored by that
    /// clause-return edge; unrelated frames remain an error.
    resumption_return_handler_ids: Vec<u32>,
    /// Exact handler brand and result ABI of the pending callable resumption.
    resumption_return_result: Vec<(u32, VmType)>,
}

/// Facts owned by a resident value, as distinct from its register's storage
/// lifetime. Parallel ownership edges snapshot these before retiring any
/// source or overwriting a destination.
struct VerifierValue {
    references: ReferenceOriginSet,
    independent: bool,
    referent_independent: bool,
    label: Option<label_dispatch::LocalLabel>,
    destruction_preserves: bool,
    invocation_preserves: bool,
    labels: bool,
    resumptions: ResumptionValue,
}

impl VerifierValue {
    fn snapshot(function: &VmFunction, states: &VerifierState, register: u32) -> Self {
        let index = register as usize;
        Self {
            references: states.reference_origins[index].clone(),
            independent: tail_provenance::independent(function, states, register),
            referent_independent: tail_provenance::referent_independent(function, states, register),
            label: states.local_labels[index],
            destruction_preserves: tail_provenance::destruction_preserving(function, states, register),
            invocation_preserves: tail_provenance::invocation_preserving(function, states, register),
            labels: states.labels[index],
            resumptions: states.resumptions[index].clone(),
        }
    }

    fn install(self, function: &VmFunction, states: &mut VerifierState, register: u32) -> Result<(), VmArtifactError> {
        write(states, register)?;
        let index = register as usize;
        states.reference_origins[index] = self.references;
        states.frame_independent[index] = self.independent;
        states.referent_independent[index] = self.referent_independent;
        states.local_labels[index] = label_dispatch::retain_at(function, register, self.label);
        states.destruction_preserves_frames[index] = self.destruction_preserves;
        states.invocation_preserves_frames[index] = self.invocation_preserves;
        states.labels[index] = self.labels;
        states.resumptions[index] = self.resumptions;
        Ok(())
    }
}

/// A handler dispatch PC can be entered both initially and by a deep
/// resumption. These are separate return contexts, not an ordinary CFG join.
/// Within each context all register, ownership and handler-stack joins remain
/// strict. Call-site result ABIs are still merged and checked universally.
#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
struct VerifierContext {
    resuming: bool,
    handlers: Vec<u32>,
}

impl VerifierState {
    fn retire_value(&mut self, register: u32) {
        let index = register as usize;
        self.registers[index] = Some(false);
        self.may_initialized[index] = false;
        self.reference_origins[index].clear();
        self.frame_independent[index] = false;
        self.referent_independent[index] = false;
        self.local_labels[index] = None;
        self.destruction_preserves_frames[index] = false;
        self.invocation_preserves_frames[index] = false;
        self.labels[index] = false;
        self.resumptions[index] = ResumptionValue::None;
    }

    fn context(&self) -> VerifierContext {
        VerifierContext {
            resuming: self.resuming,
            handlers: self.resumption_return_handler_ids.clone(),
        }
    }
}

type VerifierIncoming = Vec<BTreeMap<VerifierContext, VerifierState>>;
type VerifierWorklist = Vec<(usize, VerifierContext)>;

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
    let proofs = tail_provenance::summaries(&BTreeMap::from([(function.definition, function.clone())]))?;
    verify_function_control(function, true, false, &proofs).map(|_| ())
}

/// Infer the normal-return half of the ABI using the machine verifier's full
/// handler/resumption state machine, not a static-PC approximation. During
/// lowering only the provisional `returns` bit is ignored; all type, storage,
/// control and authority checks are unchanged.
pub(crate) fn infer_function_returns(function: &VmFunction) -> Result<bool, VmArtifactError> {
    // A lexical label can be invoked by a descendant ordinary call. Its
    // destination is therefore an externally enterable continuation, even
    // when the local verifier worklist has no ordinary predecessor for it.
    Ok(verify_function_control(function, false, false, &tail_provenance::TransferProofs::default())?.returns
        || vm_instructions_may_return(&function.instructions))
}

struct VerifiedFunctionControl {
    returns: bool,
    result_independent: bool,
    result_destruction_preserving: bool,
    preserves_frame_memory: bool,
    preserves_independent_frame_memory: bool,
    captures_intact_at_boundaries: bool,
}

fn verify_function_control(function: &VmFunction, check_return_flag: bool, assume_parameter_destructors: bool, transfer_proofs: &tail_provenance::TransferProofs) -> Result<VerifiedFunctionControl, VmArtifactError> {
    verify_function_control_with_reference_inputs(function, check_return_flag, assume_parameter_destructors, &BTreeSet::new(), false, transfer_proofs)
}

fn verify_function_control_with_reference_inputs(function: &VmFunction, check_return_flag: bool, assume_parameter_destructors: bool, referent_only_inputs: &BTreeSet<u32>, assume_parameter_invocations: bool, transfer_proofs: &tail_provenance::TransferProofs) -> Result<VerifiedFunctionControl, VmArtifactError> {
    // `decode_artifact` checks these invariants while reading bytes, but a
    // candidate can also be assembled directly by an embedding host. Keep
    // the verifier boundary equally strict so two spellings of one effect
    // identity cannot receive distinct executable fingerprints.
    let layouts = &function.nominal_copy_descriptors;
    for register in &function.registers {
        validate_vm_type_with_layouts(register, &layouts)?;
    }
    let declared_result = declared_result(function)?;
    if check_return_flag && declared_result.is_some() {
        // Label continuations may be entered by a descendant call rather
        // than by this local worklist. Check that half of the result ABI too,
        // including an entry function with no ordinary caller.
        return_type(function)?;
    }
    declared_frame_cleanup(function)?;
    validate_vm_nominal_copy_descriptors(&function.nominal_copy_descriptors)?;
    for field in function.nominal_copy_descriptors.iter().flat_map(|layout| &layout.variants).flatten() {
        validate_vm_type_with_layouts(field, &layouts)?;
    }
    for instruction in &function.instructions {
        match instruction {
            VmInstruction::PerformOwned {
                effect_arguments, ..
            }
            | VmInstruction::Perform {
                effect_arguments, ..
            }
            | VmInstruction::InstallHandler {
                effect_arguments, ..
            }
            | VmInstruction::InstallHandlerOwned {
                effect_arguments, ..
            } => validate_vm_generic_arguments(effect_arguments)?,
            _ => {}
        }
    }
    verify_label_brand_contracts(function)?;
    verify_source_storage_identity_contracts(function)?;
    verify_handler_entry_boundaries(function)?;
    verify_handler_payload_claims(function)?;
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
    let mut incoming: VerifierIncoming = vec![BTreeMap::new(); function.instructions.len()];
    let exposed_storage = tail_provenance::exposed_storage(function);
    if let Some(entry) = incoming.first_mut() {
        entry.insert(VerifierContext::default(), VerifierState {
            last_instruction: None,
            may_initialized: initial.iter().map(|state| *state == Some(true)).collect(),
            registers: initial,
            storage_live: initial_storage_live,
            source_storage,
            reference_origins: vec![ReferenceOriginSet::Empty; function.registers.len()],
            frame_independent: (0..function.registers.len()).map(|index| index < function.parameters as usize
                && !referent_only_inputs.contains(&(index as u32))).collect(),
            referent_independent: (0..function.registers.len()).map(|index| index < function.parameters as usize).collect(),
            local_labels: vec![None; function.registers.len()],
            destruction_preserves_frames: (0..function.registers.len())
                .map(|index| assume_parameter_destructors && index < function.parameters as usize).collect(),
            invocation_preserves_frames: (0..function.registers.len())
                .map(|index| assume_parameter_invocations && index < function.parameters as usize).collect(),
            labels: vec![false; function.registers.len()],
            resumptions: vec![ResumptionValue::None; function.registers.len()],
            handlers: Vec::new(),
            pending_leave: None,
            resuming: false,
            resumption_return_handler_ids: Vec::new(),
            resumption_return_result: Vec::new(),
        });
    }
    let mut worklist = if function.instructions.is_empty() {
        vec![]
    } else {
        vec![(0usize, VerifierContext::default())]
    };
    let mut returned: Option<VmType> = None;
    let mut result_independent = true;
    let mut captures_intact_at_boundaries = true;
    let mut result_destruction_preserving = true;
    let mut preserves_frame_memory = true;
    let mut preserves_independent_frame_memory = true;
    let mut opaque_label_targets = BTreeSet::new();
    // A verified VM function may be intentionally terminal: `Trap` is the
    // executable representation of the trusted source `!` abort leaf. Such
    // a function has no return edge, but it is still a complete control-flow
    // graph and must not be rejected as a malformed fallthrough.
    let mut trapped = false;
    let mut terminal_audits = Vec::<(u32, VerifierState)>::new();
    loop {
        let (pc, context) = if let Some(entry) = worklist.pop() { entry } else {
            // Unreachable declared terminal entries still need an authority
            // audit. Do not seed already-reachable dispatch entries with an
            // unconstrained packet from the earlier installation point.
            let Some((target, audit)) = terminal_audits.iter().find(|(target, _)| incoming[*target as usize].is_empty()) else { break; };
            propagate_state(&mut incoming, &mut worklist, *target, audit)?;
            continue;
        };
        let mut states = incoming[pc].get(&context).cloned().expect("scheduled verifier state");
        let previous_instruction = states.last_instruction;
        states.last_instruction = Some(pc);
        let mut advances = true;
        let instruction = &function.instructions[pc];
        if let Some((target, transferred)) = label_dispatch::transfer(function, instruction, &states, &transfer_proofs.label_dispatches)? {
            propagate_state(&mut incoming, &mut worklist, target, &transferred)?;
            continue;
        }
        let local_label_update = label_dispatch::produced(function, instruction, &states);
        let possible_label_targets = label_dispatch::opaque_targets(function, instruction, &states);
        let (tail_update, preserves_memory, preserves_independent_memory) = tail_provenance::before_instruction(function, instruction, &mut states, transfer_proofs);
        if !preserves_independent_memory { opaque_label_targets.extend(possible_label_targets); }
        preserves_frame_memory &= preserves_memory;
        preserves_independent_frame_memory &= preserves_independent_memory;
        if states.handlers.last().is_some_and(|frame| frame.payload_claim == Some(false))
            && !allowed_before_payload_claim(instruction) {
            return Err(VmArtifactError::HandlerStateMismatch);
        }
        // First-class resumptions use the ordinary callable ABI, but select
        // the captured activation rather than the newest installed handler.
        let captured_call = match instruction {
            VmInstruction::CallIndirect { dst, callee, arguments }
            | VmInstruction::CallIndirectOwned { dst, callee, arguments }
                if states.resumptions.get(*callee as usize).is_some_and(ResumptionValue::contains) => {
                read(&states, *callee)?;
                let [value] = arguments.as_slice() else { return Err(VmArtifactError::CallArity { expected: 1, found: arguments.len() as u32 }); };
                let frame = states.resumptions[*callee as usize].frame().ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                let index = states.handlers.iter().rposition(|handler| handler.id == frame)
                    .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                let VmType::Callable { safety: Safety::Safe, parameters, result, .. } = register_type(function, *callee)? else {
                    return Err(VmArtifactError::NotCallable { register: *callee });
                };
                if parameters.len() != 1 { return Err(VmArtifactError::CallArity { expected: 1, found: parameters.len() as u32 }); }
                expect_type(function, *value, parameters[0].clone())?;
                expect_type(function, *dst, *result)?;
                Some((VmInstruction::ResumeReturn { dst: *dst, value: *value }, index))
            }
            _ => None,
        };
        let resumption_index = captured_call.as_ref().map(|(_, index)| *index);
        let resumption_consumes = instruction.consumed_arguments().is_some();
        let instruction = captured_call.as_ref().map_or(instruction, |(instruction, _)| instruction);
        if function.captures != 0 && callable_access::is_execution_boundary(instruction) {
            captures_intact_at_boundaries &= states.registers.iter().take(function.captures as usize).all(|state| *state == Some(true));
        }
        if let VmInstruction::Call { dst, arguments, .. } | VmInstruction::CallOwned { dst, arguments, .. }
            | VmInstruction::CallIndirect { dst, arguments, .. } | VmInstruction::CallIndirectOwned { dst, arguments, .. } = instruction {
            seed_terminal_call_handlers(function, pc, *dst, arguments, resumption_consumes, &states, &mut incoming, &mut worklist)?;
        }
        // The non-consuming constructor opcodes copy their input carriers.
        // They must not provide a second spelling of Copy that bypasses its
        // affine/unique-reference permission check in an edited artifact.
        let copied_fields = match instruction {
            VmInstruction::MakeTuple { fields, .. } | VmInstruction::MakeArray { fields, .. }
            | VmInstruction::MakeRecord { fields, .. } | VmInstruction::MakeEnum { fields, .. } => Some(fields),
            _ => None,
        };
        if let Some(fields) = copied_fields {
            for field in fields {
                if !vm_type_is_duplicable(&register_type(function, *field)?, &function.nominal_copy_descriptors) {
                    return Err(VmArtifactError::AffineValueCopy { register: *field });
                }
            }
        }
        match instruction {
            VmInstruction::DeclareResult { .. } | VmInstruction::DeclareFrameCleanup { .. } => {
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
                for ty in types { validate_vm_type_with_layouts(ty, &layouts)?; }
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
                } else if *primitive == MemoryPrimitive::Forget {
                    states[arguments[0] as usize] = Some(false);
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
            VmInstruction::StoreUsize { dst, value } => {
                expect_type(function, *dst, VmType::Usize)?;
                expect_type(function, *value, VmType::Usize)?;
                read(&states, *value)?;
                if *dst < function.parameters || states.source_storage[*dst as usize] {
                    return Err(VmArtifactError::MalformedEncoding { message: "runtime counter cannot overwrite source storage or parameters" });
                }
                states.registers[*dst as usize] = Some(true);
            }
            VmInstruction::ArrayLen { dst, value } => {
                if register_type(function, *value)?.array_element().is_none() {
                    return Err(VmArtifactError::MalformedEncoding { message: "array length requires an array" });
                }
                expect_type(function, *dst, VmType::Usize)?;
                read(&states, *value)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArrayElementIsInitialized { dst, value, index }
            | VmInstruction::TakeArrayElement { dst, value, index } => {
                let array = register_type(function, *value)?;
                let Some(element) = array.array_element() else {
                    return Err(VmArtifactError::MalformedEncoding { message: "dynamic array storage requires an array" });
                };
                expect_type(function, *index, VmType::Usize)?;
                expect_type(function, *dst, if matches!(instruction, VmInstruction::TakeArrayElement { .. }) { element.clone() } else { VmType::Bool })?;
                if dst == value {
                    return Err(VmArtifactError::MalformedEncoding { message: "array storage requires a distinct destination" });
                }
                read(&states, *value)?;
                read(&states, *index)?;
                write(&mut states, *dst)?;
                if matches!(instruction, VmInstruction::TakeArrayElement { .. }) {
                    states.labels[*dst as usize] = states.labels[*value as usize];
                    states.resumptions[*dst as usize] = states.resumptions[*value as usize].opaque();
                    states.resumptions[*value as usize] = states.resumptions[*value as usize].opaque();
                    states.reference_origins[*dst as usize] = states.reference_origins[*value as usize].clone();
                }
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
            VmInstruction::ArrayEmpty { dst, element_type } => {
                expect_type(
                    function,
                    *dst,
                    VmType::Array(Box::new(element_type.clone())),
                )?;
                write(&mut states, *dst)?;
            }
            VmInstruction::ArrayGetBorrowShared {
                dst,
                value,
                index,
                element_type,
            } => {
                expect_type(
                    function,
                    *dst,
                    VmType::Reference {
                        unique: false,
                        referent: Box::new(element_type.clone()),
                    },
                )?;
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
            VmInstruction::MakeTupleOwned { dst, fields } | VmInstruction::MakeTuple { dst, fields } => {
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
                    if !receiver_types_match(&expected, &found, ReceiverVariance::Covariant) {
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
                states.resumptions[*dst as usize] = ResumptionValue::product(fields.iter().map(|field| states.resumptions[*field as usize].clone()));
            }
            VmInstruction::MakeArrayOwned { dst, fields, element_type } | VmInstruction::MakeArray {
                dst,
                fields,
                element_type,
            } => {
                let expected = VmType::Array(Box::new(element_type.clone()));
                let found = register_type(function, *dst)?;
                if found.array_element() != Some(element_type) || !found.array_accepts_count(fields.len()) {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected,
                        found,
                    });
                }
                for field in fields {
                    read(&states, *field)?;
                    let found = register_type(function, *field)?;
                    if !receiver_types_match(element_type, &found, ReceiverVariance::Covariant) {
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
                states.resumptions[*dst as usize] = ResumptionValue::product(fields.iter().map(|field| states.resumptions[*field as usize].clone()));
            }
            VmInstruction::MakeRecordOwned { dst, definition, fields, field_types } | VmInstruction::MakeRecord {
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
                if field_types.len() != layout.len() || !field_types.iter().zip(layout).all(|(actual, expected)|
                    receiver_types_match(expected, actual, ReceiverVariance::Covariant)) {
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
                states.resumptions[*dst as usize] = ResumptionValue::product(fields.iter().map(|field| states.resumptions[*field as usize].clone()));
            }
            VmInstruction::MakeEnumOwned { dst, definition, variant, fields, field_types } | VmInstruction::MakeEnum {
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
                if field_types.len() != layout.len() || !field_types.iter().zip(layout).all(|(actual, expected)|
                    receiver_types_match(expected, actual, ReceiverVariance::Covariant)) {
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
                states.resumptions[*dst as usize] = ResumptionValue::product(fields.iter().map(|field| states.resumptions[*field as usize].clone()));
            }
            VmInstruction::IsInitialized { dst, base, fields } => {
                if dst == base {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "initialization probe requires a distinct destination",
                    });
                }
                projected_storage_types(function, &register_type(function, *base)?, fields)?;
                expect_type(function, *dst, VmType::Bool)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::DerefIsInitialized { dst, reference } => {
                if !matches!(states.registers.get(*reference as usize), Some(Some(_))) {
                    return Err(VmArtifactError::ReadBeforeWrite { register: *reference });
                }
                if !matches!(register_type(function, *reference)?, VmType::Reference { unique: true, .. }) {
                    return Err(VmArtifactError::MalformedEncoding { message: "referent initialization probe requires a unique reference" });
                }
                expect_type(function, *dst, VmType::Bool)?;
                write(&mut states, *dst)?;
            }
            VmInstruction::TakeProjection { dst, base, fields } => {
                if fields.is_empty() || dst == base {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "projection move requires a nonempty path and distinct destination",
                    });
                }
                read(&states, *base)?;
                let candidates = projected_storage_types(function, &register_type(function, *base)?, fields)?;
                if !candidates.contains(&register_type(function, *dst)?) {
                    return Err(VmArtifactError::MalformedEncoding {
                        message: "projection move type does not match frozen storage layout",
                    });
                }
                write(&mut states, *dst)?;
                states.labels[*dst as usize] = states.labels[*base as usize];
                states.resumptions[*dst as usize] = states.resumptions[*base as usize].take(fields);
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
                states.resumptions[*dst as usize] = states.resumptions[*base as usize].project(&[*index]);
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
                states.resumptions[*dst as usize] = states.resumptions[*base as usize].project(&[*index]);
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
                let array = register_type(function, *base)?;
                let Some(actual) = array.array_element() else {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *base,
                        expected: VmType::Array(Box::new(element_type.clone())),
                        found: register_type(function, *base)?,
                    });
                };
                if actual != element_type || !array.array_accepts_count(*field_count as usize)
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
                states.resumptions[*dst as usize] = states.resumptions[*base as usize].project(&[*index]);
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
                let mut resumptions = states.resumptions[*base as usize].clone();
                resumptions.replace(&[*index], states.resumptions[*value as usize].clone());
                write(&mut states, *dst)?;
                states.resumptions[*dst as usize] = resumptions;
                states.labels[*dst as usize] = states.labels[*base as usize] || states.labels[*value as usize];
            }
            VmInstruction::PatternTest {
                dst,
                subject,
                pattern,
            } => {
                if !states.handlers.last().is_some_and(|frame|
                    frame.payload_claim == Some(false) && frame.payload_destinations.contains(subject)
                    && states.registers[*subject as usize] == Some(false)) {
                    read(&states, *subject)?;
                }
                expect_type(function, *dst, VmType::Bool)?;
                verify_pattern(pattern, &register_type(function, *subject)?)?;
                write(&mut states, *dst)?;
                if let Some(frame) = states.handlers.last_mut()
                    && frame.payload_claim == Some(false)
                    && let Some(column) = frame.payload_destinations.iter().position(|payload| payload == subject) {
                    frame.payload_probe = Some((*dst, column, pattern.clone()));
                }
            }
            VmInstruction::PerformOwned {
                dst,
                effect,
                effect_arguments,
                operation,
                arguments,
            }
            | VmInstruction::Perform {
                dst,
                effect,
                effect_arguments,
                operation,
                arguments,
            } => {
                let owned_payloads = matches!(instruction, VmInstruction::PerformOwned { .. });
                let mut seen = BTreeSet::new();
                for argument in arguments {
                    read(&states, *argument)?;
                    if owned_payloads && !seen.insert(*argument) { return Err(VmArtifactError::UseAfterMove { register: *argument }); }
                }
                if owned_payloads {
                    for argument in arguments { states.registers[*argument as usize] = Some(false); }
                }
                let payload_metadata = arguments.iter().map(|argument| {
                    let index = *argument as usize;
                    (states.reference_origins[index].clone(), states.labels[index], states.resumptions[index].clone())
                }).collect::<Vec<_>>();
                if let Some(index) = states.handlers.iter().rposition(|frame| {
                    frame.continuations.is_empty()
                        && frame.effect == *effect
                        && frame.effect_arguments == *effect_arguments
                        && frame.operation == *operation
                }) {
                    let above = states.handlers.split_off(index + 1);
                    let frame = states.handlers[index].clone();
                    if frame.owned_payloads != owned_payloads { return Err(VmArtifactError::HandlerStateMismatch); }
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
                    for ((destination, argument), metadata) in frame.payload_destinations.iter().zip(arguments).zip(&payload_metadata)
                    {
                        same_type(function, *destination, *argument)?;
                        write(&mut states, *destination)?;
                        if owned_payloads {
                            let index = *destination as usize;
                            states.registers[index] = Some(false);
                            states.reference_origins[index] = metadata.0.clone();
                            states.labels[index] = metadata.1;
                            states.resumptions[index] = metadata.2.clone();
                        }
                    }
                    states.handlers[index].payload_claim = owned_payloads.then_some(false);
                    states.handlers[index].payload_domain = if owned_payloads { coverage::packet(function, &frame.payload_destinations) } else { None };
                    states.handlers[index].payload_probe = None;
                    states.handlers[index].continuations = vec![VerifierContinuation {
                        may_initialized: states.may_initialized.clone(),
                        target: (pc + 1) as u32,
                        dst: *dst,
                        registers: saved,
                        storage_live: states.storage_live.clone(),
                        reference_origins: states.reference_origins.clone(),
                        frame_independent: states.frame_independent.clone(),
                        referent_independent: states.referent_independent.clone(),
                        local_labels: states.local_labels.clone(),
                        destruction_preserves_frames: states.destruction_preserves_frames.clone(),
                        invocation_preserves_frames: states.invocation_preserves_frames.clone(),
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
            VmInstruction::ClaimEffectPayloads { payloads } => {
                let frame = states.handlers.last_mut().ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                if !frame.owned_payloads || frame.payload_claim != Some(false) || frame.payload_destinations != *payloads {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                frame.payload_claim = Some(true);
                frame.payload_domain = None;
                frame.payload_probe = None;
                for payload in payloads {
                    if states.registers[*payload as usize] != Some(false) { return Err(VmArtifactError::HandlerStateMismatch); }
                    let origins = states.reference_origins[*payload as usize].clone();
                    states.registers[*payload as usize] = None;
                    write(&mut states, *payload)?;
                    states.reference_origins[*payload as usize] = origins;
                }
            }
            VmInstruction::InstallHandlerOwned {
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                resume_type,
                continuation,
                target,
                ..
            }
            | VmInstruction::InstallHandler {
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                resume_type,
                continuation,
                target,
            } => {
                // A function-local installation brand names one live frame.
                // Re-entering an installation without closing its old frame
                // cannot manufacture arbitrarily many static return contexts.
                if states.handlers.iter().any(|frame| frame.id == pc as u32) {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                if matches!(continuation, VmContinuationPolicy::Replay { uses } if *uses < 2) {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                if let VmInstruction::InstallHandlerOwned { replay_owned, .. } = instruction {
                    if replay_owned.windows(2).any(|pair| pair[0] >= pair[1])
                        || (!replay_owned.is_empty() && !continuation.is_replay())
                    {
                        return Err(VmArtifactError::HandlerStateMismatch);
                    }
                    for root in replay_owned { register_type(function, *root)?; }
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
                    owned_payloads: matches!(instruction, VmInstruction::InstallHandlerOwned { .. }),
                    payload_claim: None,
                    payload_domain: None,
                    payload_probe: None,
                    continuations: Vec::new(),
                });
                if *continuation == VmContinuationPolicy::Terminal {
                    let mut audit = states.clone();
                    for payload in payload_destinations {
                        write(&mut audit, *payload)?;
                        if matches!(instruction, VmInstruction::InstallHandlerOwned { .. }) {
                            audit.registers[*payload as usize] = Some(false);
                        }
                    }
                    audit.handlers.last_mut().unwrap().payload_claim =
                        matches!(instruction, VmInstruction::InstallHandlerOwned { .. }).then_some(false);
                    audit.handlers.last_mut().unwrap().payload_domain =
                        if matches!(instruction, VmInstruction::InstallHandlerOwned { .. }) { coverage::packet(function, payload_destinations) } else { None };
                    if !terminal_audits.iter().any(|(entry, state)| entry == target && state == &audit) {
                        terminal_audits.push((*target, audit));
                    }
                }
            }
            VmInstruction::CompleteHandler { value } => {
                read(&states, *value)?;
                let frame = states.handlers.last()
                    .ok_or(VmArtifactError::HandlerStackUnderflow)?;
                if !frame.continuations.is_empty() || states.resumptions[*value as usize].contains() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                if !states.resumption_return_result.is_empty() {
                    for (_, expected) in states.resumption_return_result.iter()
                        .filter(|(brand, _)| *brand == frame.id) {
                        expect_type(function, *value, expected.clone())?;
                    }
                    states.resumption_return_result.retain(|(brand, _)| *brand != frame.id);
                    advances = !states.resumption_return_result.is_empty();
                }
            }
            VmInstruction::UninstallHandler => {
                let Some(frame) = states.handlers.pop() else {
                    return Err(VmArtifactError::HandlerStackUnderflow);
                };
                if !frame.continuations.is_empty() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                expire_snapshot_brand(&mut states.resumptions, frame.id);
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
                if frame.owned_payloads {
                    states.registers[*value as usize] = Some(false);
                }
                for continuation in continuations {
                    let mut resumed_handlers = states.handlers.clone();
                    resumed_handlers.last_mut().unwrap().payload_claim = None;
                    if replaying {
                        resumed_handlers
                            .last_mut()
                            .expect("active handler frame exists")
                            .continuations
                            .clear();
                    }
                    resumed_handlers.extend(continuation.above);
                    let mut resumed = VerifierState {
                        last_instruction: Some(pc),
                        may_initialized: continuation.may_initialized,
                        registers: continuation.registers,
                        storage_live: continuation.storage_live,
                        source_storage: states.source_storage.clone(),
                        reference_origins: continuation.reference_origins,
                        frame_independent: continuation.frame_independent,
                        referent_independent: continuation.referent_independent,
                        local_labels: continuation.local_labels,
                        destruction_preserves_frames: continuation.destruction_preserves_frames,
                        invocation_preserves_frames: continuation.invocation_preserves_frames,
                        labels: continuation.labels,
                        resumptions: continuation.resumptions,
                        handlers: resumed_handlers,
                        pending_leave: continuation.pending_leave,
                        resuming: states.resuming,
                        resumption_return_handler_ids: states.resumption_return_handler_ids.clone(),
                        resumption_return_result: states.resumption_return_result.clone(),
                    };
                    write(&mut resumed, continuation.dst)?;
                    propagate_state(&mut incoming, &mut worklist, continuation.target, &resumed)?;
                }
                advances = false;
            }
            VmInstruction::ResumeReturn { dst, value } => {
                read(&states, *value)?;
                let index = resumption_index.or_else(|| states.handlers.len().checked_sub(1))
                    .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                let Some(frame) = states.handlers.get(index) else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.continuation == VmContinuationPolicy::Terminal
                    || frame.continuations.is_empty()
                {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let continuations = frame.continuations.clone();
                let found = register_type(function, *value)?;
                if found != frame.resume_type {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *value,
                        expected: frame.resume_type.clone(),
                        found,
                    });
                }
                // The destination ABI is checked at the completion boundary,
                // not against the operation parameter or enclosing function.
                let result = register_type(function, *dst)?;
                if frame.owned_payloads || resumption_consumes {
                    states.registers[*value as usize] = Some(false);
                }
                let resumption_return_result = vec![(frame.id, result)];
                let mut resumed_handlers = states.handlers[..index].to_vec();
                resumed_handlers.extend_from_slice(&states.handlers[index + 1..]);
                resumed_handlers.push(states.handlers[index].clone());
                resumed_handlers.last_mut().unwrap().payload_claim = None;
                resumed_handlers
                    .last_mut()
                    .expect("active resumable handler exists")
                    .continuations
                    .clear();
                // A shared clause can be reached from several performance
                // sites. Every possible suspended suffix must satisfy the
                // resumption ABI; checking only the first would miss paths.
                for continuation in continuations {
                    let mut handlers = resumed_handlers.clone();
                    handlers.extend(continuation.above);
                    let resumption_return_handler_ids =
                        handlers.iter().map(|frame| frame.id).collect::<Vec<_>>();
                    if resumption_return_handler_ids.iter().copied().collect::<BTreeSet<_>>().len()
                        != resumption_return_handler_ids.len()
                    {
                        return Err(VmArtifactError::HandlerStateMismatch);
                    }
                    let mut resumed = VerifierState {
                        last_instruction: Some(pc),
                        may_initialized: continuation.may_initialized,
                        registers: continuation.registers,
                        storage_live: continuation.storage_live,
                        source_storage: states.source_storage.clone(),
                        reference_origins: continuation.reference_origins,
                        frame_independent: continuation.frame_independent,
                        referent_independent: continuation.referent_independent,
                        local_labels: continuation.local_labels,
                        destruction_preserves_frames: continuation.destruction_preserves_frames,
                        invocation_preserves_frames: continuation.invocation_preserves_frames,
                        labels: continuation.labels,
                        resumptions: continuation.resumptions,
                        handlers,
                        pending_leave: continuation.pending_leave,
                        resuming: true,
                        resumption_return_handler_ids,
                        resumption_return_result: resumption_return_result.clone(),
                    };
                    write(&mut resumed, continuation.dst)?;
                    propagate_state(&mut incoming, &mut worklist, continuation.target, &resumed)?;
                }
                if states.handlers[index].continuation == VmContinuationPolicy::Consume {
                    states.handlers[index].continuations.clear();
                }
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
                    shared_receiver: false,
                    unique_receiver: false,
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
                states.labels[*dst as usize] = false;
                states.resumptions[*dst as usize] = ResumptionValue::Token(frame_id);
            }
            VmInstruction::ResumeSnapshot { snapshot, value } => {
                read(&states, *snapshot)?;
                read(&states, *value)?;
                let Some(frame_id) = states.resumptions[*snapshot as usize].frame() else {
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
                if frame.owned_payloads {
                    states.registers[*value as usize] = Some(false);
                }
                let prefix = states.handlers[..=index].to_vec();
                for continuation in continuations {
                    let mut resumed_handlers = prefix.clone();
                    resumed_handlers.last_mut().unwrap().payload_claim = None;
                    if replaying {
                        resumed_handlers
                            .last_mut()
                            .expect("captured handler frame exists")
                            .continuations
                            .clear();
                    }
                    resumed_handlers.extend(continuation.above);
                    let mut resumed = VerifierState {
                        last_instruction: Some(pc),
                        may_initialized: continuation.may_initialized,
                        registers: continuation.registers,
                        storage_live: continuation.storage_live,
                        source_storage: states.source_storage.clone(),
                        reference_origins: continuation.reference_origins,
                        frame_independent: continuation.frame_independent,
                        referent_independent: continuation.referent_independent,
                        local_labels: continuation.local_labels,
                        destruction_preserves_frames: continuation.destruction_preserves_frames,
                        invocation_preserves_frames: continuation.invocation_preserves_frames,
                        labels: continuation.labels,
                        resumptions: continuation.resumptions,
                        handlers: resumed_handlers,
                        pending_leave: continuation.pending_leave,
                        resuming: states.resuming,
                        resumption_return_handler_ids: states.resumption_return_handler_ids.clone(),
                        resumption_return_result: states.resumption_return_result.clone(),
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
                if declined.owned_payloads && declined.payload_claim != Some(false) {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                declined.payload_claim = None;
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
                    if outer.owned_payloads != declined.owned_payloads { return Err(VmArtifactError::HandlerStateMismatch); }
                    if outer.payload_destinations.len() != continuation.performed.arguments.len() {
                        return Err(VmArtifactError::CallArity {
                            expected: outer.payload_destinations.len() as u32,
                            found: continuation.performed.arguments.len() as u32,
                        });
                    }
                    forwarded.registers = continuation.registers.clone();
                    forwarded.storage_live = continuation.storage_live.clone();
                    forwarded.reference_origins = continuation.reference_origins.clone();
                    forwarded.frame_independent = continuation.frame_independent.clone();
                    forwarded.referent_independent = continuation.referent_independent.clone();
                    forwarded.local_labels = continuation.local_labels.clone();
                    forwarded.destruction_preserves_frames = continuation.destruction_preserves_frames.clone();
                    forwarded.invocation_preserves_frames = continuation.invocation_preserves_frames.clone();
                    forwarded.labels = continuation.labels.clone();
                    forwarded.resumptions = continuation.resumptions.clone();
                    for (destination, argument) in outer
                        .payload_destinations
                        .iter()
                        .zip(&continuation.performed.arguments)
                    {
                        same_type(function, *destination, *argument)?;
                        write(&mut forwarded, *destination)?;
                        if outer.owned_payloads {
                            let index = *destination as usize;
                            let source = *argument as usize;
                            forwarded.registers[index] = Some(false);
                            forwarded.reference_origins[index] = continuation.reference_origins[source].clone();
                            forwarded.labels[index] = continuation.labels[source];
                            forwarded.resumptions[index] = continuation.resumptions[source].clone();
                        }
                    }
                    forwarded.handlers[index].payload_claim = outer.owned_payloads.then_some(false);
                    forwarded.handlers[index].payload_domain = declined.payload_domain.clone();
                    forwarded.handlers[index].payload_probe = None;
                    let declined_active = declined.clone();
                    crossed.push(declined_active);
                    crossed.extend(continuation.above.clone());
                    forwarded.handlers[index].continuations = vec![VerifierContinuation {
                        may_initialized: states.may_initialized.clone(),
                        target: continuation.target,
                        dst: continuation.dst,
                        registers: continuation.registers,
                        storage_live: continuation.storage_live,
                        reference_origins: continuation.reference_origins,
                        frame_independent: continuation.frame_independent,
                        referent_independent: continuation.referent_independent,
                        local_labels: continuation.local_labels,
                        destruction_preserves_frames: continuation.destruction_preserves_frames,
                        invocation_preserves_frames: continuation.invocation_preserves_frames,
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
                expire_snapshot_brand(&mut states.resumptions, frame.id);
                // A terminal handler result is a non-local completion of the
                // protected computation. In particular, it must not return
                // through a pending `ResumeReturn` clause after a resumed
                // callee performs its later terminal operation.
                if frame.continuation == VmContinuationPolicy::Terminal {
                    states.resuming = false;
                    states.resumption_return_handler_ids.clear();
                    states.resumption_return_result.clear();
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
                states.labels[*dst as usize] = states.labels[*src as usize];
                states.resumptions[*dst as usize] = states.resumptions[*src as usize].clone();
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
                states.labels[*local as usize] = false;
                states.resumptions[*local as usize] = ResumptionValue::None;
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
                states.labels[*local as usize] = false;
                states.resumptions[*local as usize] = ResumptionValue::None;
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
                states.labels[*flag as usize] = false;
                states.resumptions[*flag as usize] = ResumptionValue::None;
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
                states.labels[*local as usize] = false;
                states.resumptions[*local as usize] = ResumptionValue::None;
            }
            VmInstruction::Store { dst, src } | VmInstruction::StoreOwned { dst, src } => {
                // Store deliberately permits overwrites and does not use
                // `write`; it still invalidates loans of the replaced slot.
                tail_provenance::invalidate_referent_storage(&mut states, *dst);
                if matches!(instruction, VmInstruction::StoreOwned { .. }) && dst == src {
                    return Err(VmArtifactError::MalformedEncoding { message: "owned store aliases its consumed carrier" });
                }
                if matches!(instruction, VmInstruction::StoreOwned { .. })
                    && states.registers.get(*dst as usize) == Some(&Some(true)) {
                    return Err(VmArtifactError::DoubleWrite { register: *dst });
                }
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
                states.labels[*dst as usize] = states.labels[*src as usize];
                states.resumptions[*dst as usize] = states.resumptions[*src as usize].clone();
                if matches!(register_type(function, *dst)?, VmType::Reference { .. }) {
                    states.reference_origins[*dst as usize] = states.reference_origins[*src as usize].clone();
                } else {
                    states.reference_origins[*dst as usize].clear();
                }
            }
            VmInstruction::Move { dst, src } => {
                read(&states, *src)?;
                same_type(function, *dst, *src)?;
                let value = VerifierValue::snapshot(function, &states, *src);
                states.retire_value(*src);
                value.install(function, &mut states, *dst)?;
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
                // A borrowed view may subsequently observe replacement of
                // this storage. It retains possible control contents, but
                // cannot certify a particular snapshot identity.
                states.resumptions[*dst as usize] = states.resumptions[*src as usize].opaque();
                states.resumptions[*src as usize] = states.resumptions[*src as usize].opaque();
                states.reference_origins[*dst as usize] = if *reborrow {
                    states.reference_origins[*src as usize].clone()
                } else {
                    ReferenceOriginSet::One(*src)
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
                states.resumptions[*dst as usize] = states.resumptions[*reference as usize].opaque();
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
                states.resumptions[*dst as usize] = states.resumptions[*reference as usize].opaque();
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
                if states.resumptions[*src as usize].contains() {
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
            VmInstruction::CallOwned { dst, arguments, .. }
            | VmInstruction::Call { dst, arguments, .. } => {
                for &argument in arguments {
                    read(&states, argument)?;
                    verify_call_frame_resumption_transfer(&states, argument)?;
                }
                write(&mut states, *dst)?
            }
            VmInstruction::HostCallOwned { dst, capability, symbol, parameters, result, arguments, .. }
            | VmInstruction::HostCall {
                dst,
                capability,
                symbol,
                parameters,
                result,
                arguments,
                ..
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
            VmInstruction::DestroyCallable { dst, value } => {
                read(&states, *value)?;
                if !matches!(register_type(function, *value)?, VmType::Callable { .. }) {
                    return Err(VmArtifactError::NotCallable { register: *value });
                }
                expect_type(function, *dst, VmType::Unit)?;
                states.registers[*value as usize] = Some(false);
                write(&mut states, *dst)?;
            }
            VmInstruction::TailCallOwned { arguments, callee } => {
                if !states.handlers.is_empty() || states.resuming || function.captures != 0 {
                    return Err(VmArtifactError::HandlerStillActive);
                }
                for argument in arguments {
                    read(&states, *argument)?;
                    if check_return_flag && !tail_provenance::independent(function, &states, *argument) {
                        return Err(VmArtifactError::UnprovenTailCarrier {
                            message: "mandatory tail carrier has no frame-independent provenance proof",
                            function: function.definition,
                            pc: pc as u32,
                            register: *argument,
                        });
                    }
                }
                preserves_frame_memory &= tail_provenance::call_preserving(transfer_proofs, callee,
                    arguments.iter().all(|argument| tail_provenance::destruction_preserving(function, &states, *argument)));
                preserves_independent_frame_memory &= tail_provenance::call_preserving_independent(
                    function, &states, transfer_proofs, callee, arguments);
                for action in declared_frame_cleanup(function)? {
                    if !arguments.contains(&action.owner) && states.may_initialized[action.owner as usize] {
                        return Err(VmArtifactError::MalformedEncoding { message: "mandatory tail transfer bypasses frame destruction" });
                    }
                    // Moving an owner out of its source slot does not discharge
                    // its destructor. Prepared carriers of the same frozen
                    // resident contract must also leave or be consumed.
                    let owner_type = register_type(function, action.owner)?;
                    if function.registers.iter().enumerate().any(|(index, ty)|
                        *ty == owner_type && states.may_initialized[index]
                            && !arguments.contains(&(index as u32))) {
                        return Err(VmArtifactError::MalformedEncoding { message: "mandatory tail transfer retains an undisposed destructor carrier" });
                    }
                }
                let Some((result, returns)) = declared_result else {
                    return Err(VmArtifactError::MalformedEncoding { message: "mandatory tail transfer requires a declared result destination" });
                };
                if returns {
                    returned = Some(result.clone());
                    result_independent &= transfer_proofs.independent_results.contains(callee)
                        && arguments.iter().all(|argument| tail_provenance::independent(function, &states, *argument)
                            && tail_provenance::destruction_preserving(function, &states, *argument));
                    result_destruction_preserving &= transfer_proofs.preserving_result_destruction.contains(callee)
                        && arguments.iter().all(|argument| tail_provenance::destruction_preserving(function, &states, *argument));
                } else { trapped = true; }
                advances = false;
            }
            VmInstruction::MakeCallable { dst, captures, environment, .. } => {
                for &capture in captures {
                    read(&states, capture)?;
                    // Native-backed references retain their original storage.
                    // Only unique references to private frame-relative values
                    // still lack a retained write-back representation.
                    if vm_type_contains_unanchored_unique_reference(
                        &register_type(function, capture)?,
                        &function.nominal_copy_descriptors,
                    ) {
                        return Err(VmArtifactError::UnsupportedEscapingUniqueReference);
                    }
                    if states.labels[capture as usize] {
                        return Err(VmArtifactError::InvalidLabelContract {
                            message: "callable capture cannot retain a lexical label",
                        });
                    }
                    if states.resumptions[capture as usize].contains() {
                        return Err(VmArtifactError::HandlerResumeUnavailable);
                    }
                }
                if !matches!(register_type(function, *dst)?, VmType::Callable { .. }) {
                    return Err(VmArtifactError::NotCallable { register: *dst });
                }
                if let Some(environment) = environment {
                    for (capture, descriptor) in captures.iter().zip(&environment.captures) {
                        if matches!(descriptor.mode, VmCaptureMode::Copy | VmCaptureMode::Move) {
                            states.registers[*capture as usize] = Some(false);
                        }
                    }
                }
                write(&mut states, *dst)?;
                states.labels[*dst as usize] = false;
                states.resumptions[*dst as usize] = ResumptionValue::None;
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
                states.resumptions[*dst as usize] = ResumptionValue::None;
            }
            VmInstruction::CallIndirectOwned { dst, callee, arguments }
            | VmInstruction::CallIndirect {
                dst,
                callee,
                arguments,
            } => {
                read(&states, *callee)?;
                // A captured resumption is callable-shaped but is not an
                // ordinary function value. It may be invoked only through
                // `ResumeSnapshot`, which proves the originating handler
                // frame remains active.
                if states.resumptions[*callee as usize].contains() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let receiver = register_type(function, *callee)?;
                let Some(VmType::Callable { parameters, result, safety, .. }) = receiver.callable_receiver() else {
                    return Err(VmArtifactError::NotCallable { register: *callee });
                };
                if *safety == Safety::Unsafe && !function.unsafe_execution {
                    return Err(VmArtifactError::MalformedEncoding { message: "unsafe indirect invocation lacks execution authority" });
                }
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
                if **result != found {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: (**result).clone(),
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
                let mut consumed = BTreeSet::new();
                for (&argument, &destination) in arguments.iter().zip(destinations) {
                    read(&states, argument)?;
                    same_type(function, destination, argument)?;
                    if !consumed.insert(argument) {
                        return Err(VmArtifactError::MalformedEncoding { message: "label transfer repeats an owned payload carrier" });
                    }
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
                for value in &mut states.resumptions { *value = value.opaque(); }
                let transferred = arguments.iter().map(|argument| VerifierValue::snapshot(function, &states, *argument)).collect::<Vec<_>>();
                for argument in arguments { states.retire_value(*argument); }
                for (&destination, value) in destinations.iter().zip(transferred) {
                    // A parallel phi edge may rotate or retain one of its
                    // consumed carriers. Its old resident was already moved;
                    // this is not permission to overwrite an unrelated owner.
                    if consumed.contains(&destination) && !states.source_storage[destination as usize] {
                        states.registers[destination as usize] = None;
                    }
                    value.install(function, &mut states, destination)?;
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
                let mut then_states = states.clone();
                let mut else_states = states.clone();
                let mut definitely_empty = false;
                if let Some(VmInstruction::DerefIsInitialized { dst, reference }) = pc.checked_sub(1).and_then(|previous| function.instructions.get(previous))
                    && dst == condition && previous_instruction == pc.checked_sub(1) {
                    then_states[*reference as usize] = Some(true);
                    else_states[*reference as usize] = Some(false);
                }
                if let Some(VmInstruction::IsInitialized { dst, base, fields }) = pc.checked_sub(1).and_then(|previous| function.instructions.get(previous))
                    && dst == condition && previous_instruction == pc.checked_sub(1) {
                    definitely_empty = fields.is_empty() && !exposed_storage[*base as usize]
                        && states.registers[*base as usize] == Some(false);
                    then_states[*base as usize] = Some(true);
                    if fields.is_empty() { else_states[*base as usize] = Some(false); }
                }
                for (outcome, target, mut branch) in [(true, *then_target, then_states), (false, *else_target, else_states)] {
                    if outcome && definitely_empty { continue; }
                    if let Some(frame) = branch.handlers.last_mut()
                        && frame.payload_claim == Some(false)
                        && let Some((probe, column, pattern)) = &frame.payload_probe
                        && probe == condition
                        && let Some(domain) = &mut frame.payload_domain {
                        coverage::refine(domain, *column, pattern, outcome);
                        if domain.is_empty() { continue; }
                    }
                    propagate_state(&mut incoming, &mut worklist, target, &branch)?;
                }
                advances = false;
            }
            VmInstruction::Return { value } => {
                read(&states, *value)?;
                // Return leaves this activation (or exposes the value to the
                // embedding host). A captured resumption is instead valid
                // only while its branded handler frame remains live.
                if states.resumptions[*value as usize].contains() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                if states.resuming {
                    if states.resumption_return_result.is_empty() {
                        return Err(VmArtifactError::HandlerStateMismatch);
                    }
                    for (_, expected) in &states.resumption_return_result {
                        expect_type(function, *value, expected.clone())?;
                    }
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
                result_independent &= tail_provenance::independent(function, &states, *value);
                result_destruction_preserving &= tail_provenance::destruction_preserving(function, &states, *value);
                let found = register_type(function, *value)?;
                // Every normal return must honor the declaration, including
                // entrypoints which have no call site to check their ABI.
                // Clause returns above belong to ResumeReturn's separate ABI.
                if let Some((expected, returns)) = declared_result {
                    if check_return_flag && !returns {
                        return Err(VmArtifactError::MalformedEncoding {
                            message: "non-returning function has a reachable normal return",
                        });
                    }
                    if *expected != found {
                        return Err(VmArtifactError::ResultType {
                            expected: expected.clone(),
                            found,
                        });
                    }
                }
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
        if let Some((destination, independent, referent_independent, destruction_preserves, invocation_preserves)) = tail_update {
            states.frame_independent[destination as usize] = independent;
            states.referent_independent[destination as usize] = referent_independent;
            states.destruction_preserves_frames[destination as usize] = destruction_preserves;
            states.invocation_preserves_frames[destination as usize] = invocation_preserves;
        }
        if let Some((destination, label)) = local_label_update {
            states.local_labels[destination as usize] = label;
        }
        if let Some(arguments) = instruction.consumed_arguments() {
            let mut seen = BTreeSet::new();
            for &argument in arguments {
                if !seen.insert(argument) {
                    return Err(VmArtifactError::MalformedEncoding { message: "consuming call repeats an argument carrier" });
                }
                states.retire_value(argument);
            }
        }
        if advances {
            propagate_state(&mut incoming, &mut worklist, (pc + 1) as u32, &states)?;
        }
    }
    if check_return_flag { label_dispatch::check_opaque_tail_frontier(function, opaque_label_targets)?; }
    if returned.is_some() || trapped || matches!(declared_result, Some((_, false))) {
        Ok(VerifiedFunctionControl { returns: returned.is_some(), result_independent,
            result_destruction_preserving, preserves_frame_memory, preserves_independent_frame_memory,
            captures_intact_at_boundaries })
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
    if states.resumptions[register as usize].contains() {
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
            VmGenericArgument::Lifetime(Lifetime::Infer(_) | Lifetime::Inferred(_)) => return Err(VmArtifactError::MalformedEncoding {
                message: "VM identity retains a body-local lifetime inference variable",
            }),
            VmGenericArgument::ConstInteger(_) => {}
            VmGenericArgument::ConstIntegerExpr(value) => validate_vm_structural_integer_expr(value)?,
            VmGenericArgument::Lifetime(Lifetime::Bound { .. } | Lifetime::Placeholder(_)) => {
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
    validate_vm_type_with_layouts(value, &[])
}

fn validate_vm_type_with_layouts(value: &VmType, layouts: &[VmNominalCopyDescriptor]) -> Result<(), VmArtifactError> {
    let validate = |value: &VmType| validate_vm_type_with_layouts(value, layouts);
    match value {
        VmType::Array(value) => validate(value),
        VmType::FixedArray { element, .. } => {
            validate(element)?;
            // Private VM representations remain available for element kinds
            // without a native ABI. A known inline size overflow is different:
            // reject it at admission, even when no resident is constructed.
            match native_memory::native_layout(value, &Arc::from(layouts), &mut vec![]) {
                Err(error @ VmArtifactError::NativeMemory { message:
                    "native layout size overflow" | "invalid raw allocation layout"
                    | "fixed array count exceeds target indexing width" }) => Err(error),
                _ => Ok(()),
            }
        }
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
            validate(element)
        }
        VmType::Tuple(values) => values.iter().try_for_each(validate),
        VmType::Nominal { definition, .. }
            if *definition == crate::intrinsic_available_type_definition() => {
                Err(VmArtifactError::MalformedEncoding {
                    message: "availability witness requires sealed runtime environment disposal",
                })
            }
        VmType::Nominal { arguments, .. } => {
            for argument in arguments {
                validate_vm_nominal_argument_type(argument)?;
                if let VmGenericArgument::Type(value) = argument { validate(value)?; }
            }
            Ok(())
        }
        VmType::Callable {
            shared_receiver,
            unique_receiver,
            parameters,
            result,
            effects,
            ..
        } => {
            if *shared_receiver && !*unique_receiver {
                return Err(VmArtifactError::InvalidCallableEnvironment { message: "shared callable authority requires unique receiver authority" });
            }
            parameters.iter().try_for_each(validate)?;
            validate(result)?;
            validate_vm_effect_row(effects)
        }
        VmType::Reference { referent, .. } => validate(referent),
        VmType::RawPointer { pointee, .. } => validate(pointee),
        // Consts are metadata slots inside a nominal identity, not VM value
        // layouts. Reject direct candidate registers/parameters/results and
        // any attempt to smuggle one through a tuple, array, callable, or
        // reference type.
        VmType::ConstInteger(_)
        | VmType::ConstIntegerExpr(_)
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

fn validate_vm_nominal_argument_type(value: &VmGenericArgument) -> Result<(), VmArtifactError> {
    if matches!(value, VmGenericArgument::Lifetime(_)) {
        return Err(VmArtifactError::MalformedEncoding { message: "VM nominal identity retains an unerased lifetime argument" });
    }
    validate_vm_generic_arguments(std::slice::from_ref(value))
}

fn validate_vm_structural_integer_expr(value: &IntegerConstExpr) -> Result<(), VmArtifactError> {
    if matches!(value, IntegerConstExpr::Literal(_) | IntegerConstExpr::Param { .. }) {
        return Err(VmArtifactError::NonCanonicalEncoding);
    }
    match value.clone().normalized() {
        Ok(normalized) if normalized == *value => Ok(()),
        Ok(_) => Err(VmArtifactError::NonCanonicalEncoding),
        Err(_) => Err(VmArtifactError::MalformedEncoding {
            message: "invalid structural integer expression",
        }),
    }
}

fn validate_vm_effect_row(row: &VmEffectRow) -> Result<(), VmArtifactError> {
    if row.tails.iter().any(|tail| matches!(tail, EffectTail::Infer(_))) {
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
fn verify_handler_payload_claims(function: &VmFunction) -> Result<(), VmArtifactError> {
    for instruction in &function.instructions {
        let VmInstruction::InstallHandlerOwned { target, payload_destinations, .. } = instruction else { continue; };
        let mut pending = vec![*target];
        let mut seen = BTreeSet::new();
        while let Some(pc) = pending.pop() {
            if !seen.insert(pc) { continue; }
            let instruction = function.instructions.get(pc as usize)
                .ok_or(VmArtifactError::InvalidInstructionTarget { target: pc })?;
            match instruction {
                VmInstruction::ClaimEffectPayloads { payloads } if payloads == payload_destinations => {}
                VmInstruction::Forward => {}
                VmInstruction::Jump { target } => pending.push(*target),
                VmInstruction::BranchBool { condition, then_target, else_target }
                    if !payload_destinations.contains(condition) => {
                    expect_type(function, *condition, VmType::Bool)?;
                    pending.extend([*then_target, *else_target]);
                }
                VmInstruction::PatternTest { dst, subject, pattern }
                    if payload_destinations.contains(subject) && !payload_destinations.contains(dst) => {
                    expect_type(function, *dst, VmType::Bool)?;
                    verify_pattern(pattern, &register_type(function, *subject)?)?;
                    pending.push(pc + 1);
                }
                VmInstruction::SetDropFlag { flag: dst, .. } | VmInstruction::ConstBool { dst, .. }
                    if !payload_destinations.contains(dst) => {
                    expect_type(function, *dst, VmType::Bool)?;
                    pending.push(pc + 1);
                }
                VmInstruction::StorageLive { local, .. } if !payload_destinations.contains(local) => {
                    register_type(function, *local)?;
                    pending.push(pc + 1);
                }
                _ => return Err(VmArtifactError::MalformedEncoding {
                    message: "handler must claim its untouched payload packet before use",
                }),
            }
        }
    }
    Ok(())
}

fn verify_handler_entry_boundaries(function: &VmFunction) -> Result<(), VmArtifactError> {
    let mut targets = BTreeSet::new();
    for (pc, instruction) in function.instructions.iter().enumerate() {
        let (VmInstruction::InstallHandler { target, .. } | VmInstruction::InstallHandlerOwned { target, .. }) = instruction else {
            continue;
        };
        if *target as usize <= pc || function.instructions.get(*target as usize).is_none() {
            return Err(VmArtifactError::InvalidInstructionTarget { target: *target });
        }
        targets.insert(*target);
    }

    for (pc, instruction) in function.instructions.iter().enumerate() {
        let enters_handler = match instruction {
            VmInstruction::DeclareResult { .. } | VmInstruction::DeclareFrameCleanup { .. } => false,
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
/// Join already allocated fact tables in place. The transfer function and
/// changed bit are identical to constructing a new table and comparing it,
/// but the common unchanged edge does not allocate or rebuild every field.
fn join_verifier_facts<T: Copy + PartialEq>(
    existing: &mut [T],
    incoming: &[T],
    mut join: impl FnMut(T, T) -> T,
) -> bool {
    debug_assert_eq!(existing.len(), incoming.len());
    let mut changed = false;
    for (left, right) in existing.iter_mut().zip(incoming) {
        let value = join(*left, *right);
        if *left != value { *left = value; changed = true; }
    }
    changed
}

fn propagate_state(
    incoming: &mut [BTreeMap<VerifierContext, VerifierState>],
    worklist: &mut VerifierWorklist,
    target: u32,
    state: &VerifierState,
) -> Result<(), VmArtifactError> {
    let Some(slot) = incoming.get_mut(target as usize) else {
        return Err(VmArtifactError::InvalidInstructionTarget { target });
    };
    let context = state.context();
    match slot.get_mut(&context) {
        None => {
            let mut initial = state.clone();
            for (possible, definite) in initial.may_initialized.iter_mut().zip(&state.registers) {
                *possible = definite.unwrap_or(*possible);
            }
            slot.insert(context.clone(), initial);
            worklist.push((target as usize, context));
            Ok(())
        }
        Some(existing) => {
            let mut changed = merge_handler_states(&mut existing.handlers, &state.handlers)
                .ok_or(VmArtifactError::HandlerStateMismatch)?;
            // Forwarding can resume one protected path from distinct arms.
            // Every caller ABI remains an obligation at completion.
            for result in &state.resumption_return_result {
                if !existing.resumption_return_result.contains(result) {
                    existing.resumption_return_result.push(result.clone());
                    changed = true;
                }
            }
            if existing.last_instruction != state.last_instruction
                && existing.last_instruction.take().is_some() {
                changed = true;
            }
            for ((possible, incoming_possible), definite) in existing.may_initialized.iter_mut()
                .zip(&state.may_initialized).zip(&state.registers) {
                let joined = *possible || definite.unwrap_or(*incoming_possible);
                if *possible != joined { *possible = joined; changed = true; }
            }
            // Readability and source-storage liveness are must facts. In
            // particular Some(false) and None remain distinct: neither an
            // absent SSA resident nor dead storage becomes writable here.
            changed |= join_verifier_facts(&mut existing.registers, &state.registers, |left, right| match (left, right) {
                (Some(true), Some(true)) => Some(true),
                (Some(false), Some(false)) => Some(false),
                _ => None,
            });
            changed |= join_verifier_facts(&mut existing.storage_live, &state.storage_live, |left, right| left && right);
            // Reference provenance is a may fact. Retain every possible root
            // so StorageDead continues respecting loans from all branches.
            for (left, right) in existing.reference_origins.iter_mut().zip(&state.reference_origins) {
                changed |= left.union_with(right);
            }
            changed |= join_verifier_facts(&mut existing.frame_independent, &state.frame_independent, |left, right| left && right);
            changed |= join_verifier_facts(&mut existing.referent_independent, &state.referent_independent, |left, right| left && right);
            changed |= join_verifier_facts(&mut existing.local_labels, &state.local_labels, |left, right| if left == right { left } else { None });
            changed |= join_verifier_facts(&mut existing.destruction_preserves_frames, &state.destruction_preserves_frames, |left, right| left && right);
            changed |= join_verifier_facts(&mut existing.invocation_preserves_frames, &state.invocation_preserves_frames, |left, right| left && right);
            // Labels/resumptions are capability may-taints, not readability.
            // An arm cannot erase authority carried on another predecessor.
            changed |= join_verifier_facts(&mut existing.labels, &state.labels, |left, right| left || right);
            for (left, right) in existing.resumptions.iter_mut().zip(&state.resumptions) {
                let joined = left.join(right);
                if *left != joined { *left = joined; changed = true; }
            }
            if existing.pending_leave != state.pending_leave && existing.pending_leave.take().is_some() {
                changed = true;
            }
            if changed { worklist.push((target as usize, context)); }
            Ok(())
        }
    }
}
/// A callee can perform terminal effects. Seed first-match dispatch at the
/// call boundary, after all currently active handlers have been installed.
fn seed_terminal_call_handlers(
    function: &VmFunction, pc: usize, dst: u32, arguments: &[u32], consumes: bool,
    states: &VerifierState, incoming: &mut [BTreeMap<VerifierContext, VerifierState>], worklist: &mut VerifierWorklist,
) -> Result<(), VmArtifactError> {
    let mut seen = Vec::new();
    for (index, frame) in states.handlers.iter().enumerate().rev() {
        if !frame.continuations.is_empty() { continue; }
        let key = (frame.effect, frame.effect_arguments.clone(), frame.operation);
        if seen.contains(&key) { continue; }
        seen.push(key);
        if frame.continuation != VmContinuationPolicy::Terminal { continue; }
        let mut terminal = states.clone();
        for argument in arguments {
            read(&terminal, *argument)?;
            if consumes {
                let slot = *argument as usize;
                terminal.registers[slot] = Some(false);
                terminal.reference_origins[slot].clear();
                terminal.labels[slot] = false;
                terminal.resumptions[slot] = ResumptionValue::None;
            }
        }
        let above = terminal.handlers.split_off(index + 1);
        for payload in &frame.payload_destinations {
            write(&mut terminal, *payload)?;
            if frame.owned_payloads { terminal.registers[*payload as usize] = Some(false); }
        }
        terminal.handlers[index].payload_claim = frame.owned_payloads.then_some(false);
        terminal.handlers[index].payload_domain = if frame.owned_payloads { coverage::packet(function, &frame.payload_destinations) } else { None };
        terminal.handlers[index].payload_probe = None;
        terminal.handlers[index].continuations = vec![VerifierContinuation {
            may_initialized: terminal.may_initialized.clone(),
            target: (pc + 1) as u32, dst, registers: terminal.registers.clone(),
            storage_live: terminal.storage_live.clone(), reference_origins: terminal.reference_origins.clone(),
            frame_independent: terminal.frame_independent.clone(),
            referent_independent: terminal.referent_independent.clone(),
            local_labels: terminal.local_labels.clone(),
            destruction_preserves_frames: terminal.destruction_preserves_frames.clone(),
            invocation_preserves_frames: terminal.invocation_preserves_frames.clone(),
            labels: terminal.labels.clone(), resumptions: terminal.resumptions.clone(),
            performed: VerifierPerformed { effect: frame.effect, effect_arguments: frame.effect_arguments.clone(),
                operation: frame.operation, arguments: frame.payload_destinations.clone() },
            above, pending_leave: terminal.pending_leave.clone(),
        }];
        propagate_state(incoming, worklist, frame.target, &terminal)?;
    }
    Ok(())
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
            || left.owned_payloads != right.owned_payloads
            || left.payload_claim != right.payload_claim
        {
            return None;
        }
        for continuation in &right.continuations {
            if !left.continuations.contains(continuation) {
                left.continuations.push(continuation.clone());
                changed = true;
            }
        }
        changed |= coverage::merge(&mut left.payload_domain, &right.payload_domain);
        if left.payload_probe != right.payload_probe && left.payload_probe.take().is_some() {
            changed = true;
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
/// activation remains live. Invalidating exact identity throughout stored
/// products prevents a stale token from becoming valid if bytecode revisits
/// the same lexical `InstallHandler`. Possible control contents remain tainted.
fn expire_snapshot_brand(values: &mut [ResumptionValue], frame: u32) {
    for value in values { value.expire(frame); }
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
        if descriptor.definition == crate::refinement::bindings_definition() {
            let ty = VmType::Nominal { definition: descriptor.definition, arguments: descriptor.arguments.clone() };
            let fields = crate::refinement::vm_binding_pack_fields(&ty).ok_or(VmArtifactError::MalformedEncoding {
                message: "binding pack has no canonical environment layout",
            })?;
            if descriptor.is_enum || descriptor.variants.as_slice() != [fields.to_vec()]
                || descriptor.source_contract != crate::refinement::bindings_layout_contract() {
                return Err(VmArtifactError::MalformedEncoding { message: "binding pack layout disagrees with its sealed environment" });
            }
        }
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

/// Enumerate only declaration-authorized projected types. Enum dispatch can
/// select a payload at runtime; a path must still occur in a frozen variant.
fn projected_storage_types(
    function: &VmFunction,
    root: &VmType,
    fields: &[u32],
) -> Result<Vec<VmType>, VmArtifactError> {
    let mut candidates = vec![root.clone()];
    for field in fields {
        let mut next = Vec::new();
        let mut insert = |ty: &VmType| {
            if !next.contains(ty) { next.push(ty.clone()); }
        };
        for candidate in candidates {
            match candidate {
                VmType::Tuple(elements) => {
                    if let Some(ty) = elements.get(*field as usize) { insert(ty); }
                }
                VmType::Array(element) => { insert(&element); }
                VmType::FixedArray { element, length } if u64::from(*field) < length => { insert(&element); }
                nominal @ VmType::Nominal { .. } => {
                    for variant in &nominal_layout_descriptor(function, &nominal)?.variants {
                        if let Some(ty) = variant.get(*field as usize) { insert(ty); }
                    }
                }
                _ => {}
            }
        }
        if next.is_empty() {
            return Err(VmArtifactError::MalformedEncoding {
                message: "storage projection has no field in its frozen layout",
            });
        }
        candidates = next;
    }
    Ok(candidates)
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
            VmType::FixedArray { element, length } if u64::from(*field) < *length => element,
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
        active: &mut Vec<(DefKey, Vec<VmGenericArgument>)>,
    ) -> bool {
        match ty {
            VmType::Reference { unique, .. } => !*unique,
            VmType::Tuple(elements) => elements
                .iter()
                .all(|element| visit(element, descriptors, active)),
            VmType::Array(element) => visit(element, descriptors, active),
            VmType::FixedArray { element, length } => *length == 0 || visit(element, descriptors, active),
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

fn vm_tail_owned_type(ty: &VmType, descriptors: &[VmNominalCopyDescriptor],
    active: &mut Vec<(DefKey, Vec<VmGenericArgument>)>) -> bool {
    match ty {
        VmType::Reference { .. } | VmType::RawPointer { .. } | VmType::Callable { .. }
        | VmType::Generic(_) | VmType::ConstGeneric { .. } | VmType::ConstIntegerExpr(_) => false,
        VmType::Tuple(fields) => fields.iter().all(|field| vm_tail_owned_type(field, descriptors, active)),
        VmType::Array(element) | VmType::FixedArray { element, .. } | VmType::StaticData { element, .. } => vm_tail_owned_type(element, descriptors, active),
        VmType::Nominal { definition, arguments } => {
            let key = (*definition, arguments.clone());
            let Some(descriptor) = descriptors.iter().find(|descriptor|
                descriptor.definition == *definition && descriptor.arguments == *arguments) else { return false; };
            if active.contains(&key) { return true; }
            active.push(key);
            let safe = descriptor.variants.iter().flatten().all(|field| vm_tail_owned_type(field, descriptors, active));
            active.pop();
            safe
        }
        _ => true,
    }
}

/// A native-representable referent has an address-stable source home. Private
/// referents still cannot retain a unique frame-relative write-back target.
fn vm_type_contains_unanchored_unique_reference(ty: &VmType, descriptors: &[VmNominalCopyDescriptor]) -> bool {
    fn visit(
        ty: &VmType,
        descriptors: &[VmNominalCopyDescriptor],
        active: &mut Vec<(DefKey, Vec<VmGenericArgument>)>,
    ) -> bool {
        match ty {
            VmType::Reference { unique, referent } => {
                (*unique && native_memory::native_layout(referent, &Arc::from(descriptors), &mut vec![]).is_err())
                    || visit(referent, descriptors, active)
            }
            VmType::Tuple(elements) => elements.iter().any(|element| visit(element, descriptors, active)),
            VmType::Array(element) => visit(element, descriptors, active),
            VmType::FixedArray { element, length } => *length != 0 && visit(element, descriptors, active),
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

fn same_type(function: &VmFunction, destination: u32, source: u32) -> Result<(), VmArtifactError> {
    let expected = register_type(function, destination)?;
    let found = register_type(function, source)?;
    // A transfer may forget borrowed receiver permission, but it cannot
    // specialize one of this activation's already scoped generic registers.
    // Other ABI structure, mutable carriers and nominal arguments stay exact.
    if receiver_types_match(&expected, &found, ReceiverVariance::Covariant) {
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
    // Replacing an addressable slot must not leave a child reference carrying
    // an earlier resident-graph proof, including in saved continuations.
    tail_provenance::invalidate_referent_storage(states, register);
    for frame in &mut states.handlers {
        if frame.payload_probe.as_ref().is_some_and(|(probe, _, _)| *probe == register) {
            frame.payload_probe = None;
        }
    }
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
    states.frame_independent[index] = false;
    states.referent_independent[index] = false;
    states.local_labels[index] = None;
    states.destruction_preserves_frames[index] = false;
    states.invocation_preserves_frames[index] = false;
    states.resumptions[index] = ResumptionValue::None;
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
    /// A typed, addressable source resident. Bytes live only in its native
    /// home; cloning this carrier retains storage identity, not a value copy.
    Resident(Arc<native_storage::NativeHome>),
    /// A unique loan whose resident was moved out. Its address survives so
    /// assignment can restore it, but it is not a readable language value.
    SuspendedReference(Box<VmValue>),
    /// Private register-storage state, never a language value or a native
    /// object representation. Retain the type of a moved field so the parent
    /// layout does not change when part of an aggregate is consumed.
    Uninitialized(VmType),
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
        bytes: native_memory::StaticBytes,
        offset: usize,
        length: usize,
    },
    Tuple(Arc<[VmValue]>),
    Array {
        values: Arc<[VmValue]>,
    },
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
        captures: Arc<RuntimeCaptureEnvironment>,
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
    /// A frame-branded callable token. Returning indirect calls and terminal
    /// `ResumeSnapshot` transfers both resolve this exact activation.
    Resumption {
        frame: u64,
        signature: VmType,
    },
}

/// Idle callables own their captured values here. An invocation borrows that
/// ownership by transferring the slots into its frame; this environment is
/// vacant until the frame releases the loan. There is no second initialized
/// capture snapshot for cancellation or destruction to mistake for an owner.
#[derive(Debug)]
struct RuntimeCaptureEnvironment {
    values: RefCell<Vec<VmValue>>,
    owned: Vec<bool>,
    live: std::cell::Cell<bool>,
}

impl RuntimeCaptureEnvironment {
    fn new(values: Vec<VmValue>) -> Arc<Self> {
        let owned = vec![true; values.len()];
        Self::with_ownership(values, owned)
    }

    fn with_ownership(values: Vec<VmValue>, owned: Vec<bool>) -> Arc<Self> {
        debug_assert_eq!(values.len(), owned.len());
        Arc::new(Self { values: RefCell::new(values), owned, live: std::cell::Cell::new(true) })
    }

    fn duplicate(&self, budget: &mut ExecutionBudget) -> Result<Arc<Self>, VmArtifactError> {
        if !self.live.get() {
            return Err(VmArtifactError::NativeMemory { message: "cannot copy a destroyed callable environment" });
        }
        let captured = self.values.borrow();
        budget.reserve_value("copied callable captures", captured.len())?;
        budget.reserve_allocation(self.owned.len())?;
        let values = captured.iter().zip(&self.owned).map(|(value, owned)| {
            if *owned { copy_owned_value(value, budget) } else { Ok(value.clone()) }
        }).collect::<Result<Vec<_>, _>>()?;
        Ok(Self::with_ownership(values, self.owned.clone()))
    }

    fn len(&self) -> usize { self.values.borrow().len() }

    fn lend_to_invocation(&self) -> Vec<VmValue> { self.take() }

    fn take(&self) -> Vec<VmValue> {
        self.values.borrow_mut().iter_mut().map(|value| {
            let ty = value.ty();
            std::mem::replace(value, VmValue::Uninitialized(ty))
        }).collect()
    }
}

/// A source Copy creates independent owned storage. Interpreter bookkeeping
/// clones remain shallow; borrowed captures keep the same referent authority.
fn copy_owned_value(value: &VmValue, budget: &mut ExecutionBudget) -> Result<VmValue, VmArtifactError> {
    budget.tick()?;
    let fields = |values: &[VmValue], budget: &mut ExecutionBudget| -> Result<Arc<[VmValue]>, VmArtifactError> {
        budget.reserve_value("copied aggregate fields", values.len())?;
        Ok(values.iter().map(|value| copy_owned_value(value, budget))
            .collect::<Result<Vec<_>, _>>()?.into())
    };
    Ok(match value {
        VmValue::Callable { callee, captures, signature } => VmValue::Callable {
            callee: *callee, captures: captures.duplicate(budget)?, signature: signature.clone(),
        },
        VmValue::Resident(home) => {
            let copied = native_storage::NativeHome::new(home.layout.clone(), budget)?;
            if home.layout.owns_callable() {
                let loaded = home.load(&[], budget)?;
                let value = copy_owned_value(&loaded, budget)?;
                copied.store(&[], &value, budget)?;
            } else { copied.store(&[], value, budget)?; }
            VmValue::Resident(copied)
        }
        VmValue::Tuple(values) => VmValue::Tuple(fields(values, budget)?),
        VmValue::Array { values } => VmValue::Array { values: fields(values, budget)? },
        VmValue::Record { definition, fields: values, signature } => VmValue::Record {
            definition: *definition, fields: fields(values, budget)?, signature: signature.clone(),
        },
        VmValue::Enum { definition, variant, fields: values, signature } => VmValue::Enum {
            definition: *definition, variant: *variant, fields: fields(values, budget)?, signature: signature.clone(),
        },
        _ => value.clone(),
    })
}

#[derive(Clone, Debug)]
enum ReferenceTarget {
    /// Checked source storage with a stable address and tracked initialization.
    Home(Arc<native_storage::NativeHome>),
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
    owned_payloads: bool,
    /// Source allocations and SSA carriers already outside this delimiter.
    shared_registers: BTreeMap<u32, Option<u64>>,
    suspended: Option<RuntimeContinuation>,
}

/// SSA temporaries are restored with a continuation; live source storage is
/// shared by that continuation and its clause. An allocation brand prevents
/// a later lexical activation of the same register from impersonating the
/// storage captured by an older snapshot.
#[derive(Clone, Default)]
struct RuntimeRegisters {
    values: Vec<Option<VmValue>>,
    source_storage: BTreeMap<u32, u64>,
    native_plan: Option<Arc<native_storage::NativeFramePlan>>,
    native_homes: BTreeMap<u32, Arc<native_storage::NativeHome>>,
    pending_native: Vec<u32>,
    capture_environment: Option<Arc<RuntimeCaptureEnvironment>>,
    /// A replay of an active callback can own copied capture slots without
    /// owning its outer callable. These slots use the same selected cleanup
    /// as an ordinary environment instead of being returned to that outer one.
    detached_captures: bool,
}

impl RuntimeRegisters {
    fn as_slice(&self) -> &[Option<VmValue>] { &self.values }

    fn for_function(function: &VmFunction, budget: &mut ExecutionBudget) -> Result<Self, VmArtifactError> {
        Self::for_function_with_native_return(function, budget, false)
    }

    fn for_function_with_native_return(function: &VmFunction, budget: &mut ExecutionBudget, native_return: bool) -> Result<Self, VmArtifactError> {
        Self::with_values(function, budget, native_return, vec![None; function.registers.len()])
    }

    fn with_values(function: &VmFunction, budget: &mut ExecutionBudget, native_return: bool, values: Vec<Option<VmValue>>) -> Result<Self, VmArtifactError> {
        debug_assert_eq!(values.len(), function.registers.len());
        debug_assert!(values.iter().all(Option::is_none));
        let mut registers = Self { values, ..Self::default() };
        registers.native_plan = Some(if native_return { budget.native_memory.native_return_plan(function) }
            else { budget.native_memory.storage_plan(function) });
        let results = registers.native_plan.as_ref().expect("installed native plan").native_results.clone();
        for result in results { registers.native_home(result, budget)?; }
        for parameter in 0..function.parameters { registers.native_write(parameter); }
        Ok(registers)
    }

    fn install_argument(&mut self, index: usize, value: VmValue) {
        if let VmValue::Resident(home) = &value && home.is_external() {
            self.native_homes.insert(index as u32, home.clone());
        }
        self.values[index] = Some(value);
    }

    fn install_captures(&mut self, environment: Arc<RuntimeCaptureEnvironment>) {
        // A noncapturing callable has no residual slots to restore. Do not
        // introduce a restoration boundary that blocks its first tail call.
        if environment.len() == 0 { return; }
        // Captured native storage is already an owner home. Borrow it for this
        // invocation instead of constructing a second metadata/payload home.
        for index in 0..environment.len() {
            if let Some(VmValue::Resident(home)) = &self.values[index] {
                self.native_homes.insert(index as u32, home.clone());
            }
        }
        self.capture_environment = Some(environment);
    }

    fn release_capture_loan(&mut self, budget: &mut ExecutionBudget) -> Result<(), VmArtifactError> {
        if let Some(environment) = self.capture_environment.take() {
            for (index, captured) in environment.values.borrow_mut().iter_mut().enumerate() {
                budget.tick()?;
                *captured = self.values[index].take().unwrap_or_else(|| VmValue::Uninitialized(captured.ty()));
            }
        }
        Ok(())
    }

    fn wants_native(&self, local: u32) -> bool {
        self.native_homes.contains_key(&local)
            || self.native_plan.as_ref().is_some_and(|plan| plan.layouts[local as usize].is_some())
    }

    fn native_write(&mut self, local: u32) {
        if self.wants_native(local) {
            self.pending_native.push(local);
        }
    }

    fn instruction_result(&mut self, pc: usize) {
        if let Some(local) = self.native_plan.as_ref().and_then(|plan| plan.results[pc]) {
            self.native_write(local);
        }
    }

    fn read_projection(&self, pc: usize) -> Option<(u32, u32)> {
        self.native_plan.as_ref().and_then(|plan| plan.read_projections[pc])
    }

    fn native_home(&mut self, local: u32, budget: &mut ExecutionBudget) -> Result<Arc<native_storage::NativeHome>, VmArtifactError> {
        if let Some(home) = self.native_homes.get(&local) { return Ok(home.clone()); }
        let layout = self.native_plan.as_ref().and_then(|plan| plan.layouts[local as usize].clone())
            .ok_or(VmArtifactError::InvalidRegister { register: local })?;
        let home = if let Some(home) = self.native_homes.get(&local) { home.clone() }
            else {
                let home = native_storage::NativeHome::new(layout, budget)?;
                self.native_homes.insert(local, home.clone()); home
            };
        Ok(home)
    }

    fn materialize_native(&mut self, local: u32, value: &VmValue, budget: &mut ExecutionBudget) -> Result<VmValue, VmArtifactError> {
        let home = self.native_home(local, budget)?;
        home.store(&[], value, budget)?;
        Ok(VmValue::Resident(home))
    }

    fn finish_native_writes(&mut self, budget: &mut ExecutionBudget) -> Result<(), VmArtifactError> {
        while let Some(local) = self.pending_native.pop() {
            if let Some(value) = self.values[local as usize].take() {
                self.values[local as usize] = Some(self.materialize_native(local, &value, budget)?);
            }
        }
        Ok(())
    }

    fn copy_value(&self, local: u32, budget: &mut ExecutionBudget) -> Result<VmValue, VmArtifactError> {
        let value = self.values[local as usize].as_ref().ok_or(VmArtifactError::UseAfterMove { register: local })?;
        match value { VmValue::Resident(home) => home.load(&[], budget), value => Ok(value.clone()) }
    }

    fn constructor_field(&self, destination: u32, field: u32, budget: &mut ExecutionBudget) -> Result<VmValue, VmArtifactError> {
        if self.native_plan.as_ref().is_some_and(|plan| plan.layouts[destination as usize].is_some()) {
            self.values[field as usize].clone().ok_or(VmArtifactError::UseAfterMove { register: field })
        } else { self.copy_value(field, budget) }
    }

    fn copy_into(&mut self, dst: u32, src: u32, budget: &mut ExecutionBudget) -> Result<(), VmArtifactError> {
        let native = self.native_plan.as_ref().is_some_and(|plan| plan.layouts[dst as usize].is_some());
        let environments = self.native_plan.as_ref().is_some_and(|plan| plan.copy_environments[dst as usize]);
        self.values[dst as usize] = Some(if environments {
            let value = self.copy_value(src, budget)?;
            copy_owned_value(&value, budget)?
        } else if native {
            self.values[src as usize].as_ref().ok_or(VmArtifactError::UseAfterMove { register: src })?.clone()
        } else {
            let value = self.copy_value(src, budget)?;
            if self.native_plan.as_ref().is_some_and(|plan| plan.copy_environments[dst as usize]) {
                copy_owned_value(&value, budget)?
            } else { value }
        });
        Ok(())
    }

    fn move_into(&mut self, dst: u32, src: u32, budget: &mut ExecutionBudget) -> Result<(), VmArtifactError> {
        if dst == src { return Ok(()); }
        let value = self.values[src as usize].take().ok_or(VmArtifactError::UseAfterMove { register: src })?;
        let value = if let VmValue::Resident(home) = &value {
            // A uniquely owned, never-exposed temporary has no address
            // identity to preserve. Transfer its backing to an as-yet-vacant
            // destination instead of allocating a second block just to move
            // its bytes. The two strong owners are this value and the source
            // home table; references, captures, or continuation snapshots
            // conservatively keep the ordinary copy/retirement path.
            if !home.address_was_exposed()
                && Arc::strong_count(home) == 2
                && self.native_homes.get(&src).is_some_and(|owner| Arc::ptr_eq(owner, home))
                && !self.native_homes.contains_key(&dst)
                && self.native_plan.as_ref().and_then(|plan| plan.layouts[dst as usize].as_ref())
                    .is_some_and(|layout| layout.ty == home.layout.ty)
            {
                let owner = self.native_homes.remove(&src).expect("checked source owner");
                self.native_homes.insert(dst, owner);
                self.values[dst as usize] = Some(value);
                return Ok(());
            }
            let moved = if self.native_plan.as_ref().is_some_and(|plan| plan.layouts[dst as usize].is_some()) {
                let moved = self.materialize_native(dst, &value, budget)?;
                home.clear(&[]); moved
            } else { home.take(&[], budget)? };
            // A checked whole-owner move cannot retain a live source loan.
            // Reclaim its vacant backing when no raw/native observer has seen
            // the address. Exposed slots retain their stable storage until the
            // lexical lifetime ends, including across later reinitialization.
            if !home.address_was_exposed() {
                home.retire();
                self.native_homes.remove(&src);
            }
            moved
        } else { value };
        self.values[dst as usize] = Some(value); Ok(())
    }

    fn clear_value(&mut self, local: u32) {
        if let Some(VmValue::Resident(home)) = self.values[local as usize].take() { home.clear(&[]); }
    }

    /// The callee's carriers must be installed before retiring these homes.
    /// This disarms ownership without running source destruction a second time.
    fn retire_call_arguments(&mut self, arguments: &[u32]) {
        for &argument in arguments {
            self.clear_value(argument);
            if let Some(home) = self.native_homes.get(&argument)
                && !home.address_was_exposed()
            {
                home.retire();
                self.native_homes.remove(&argument);
            }
        }
    }

    fn synchronize_source_storage(&mut self, current: &Self) {
        for (local, brand) in &self.source_storage {
            if current.source_storage.get(local) == Some(brand) {
                self.values[*local as usize] = current.values[*local as usize].clone();
            }
        }
    }
}

impl Deref for RuntimeRegisters {
    type Target = [Option<VmValue>];
    fn deref(&self) -> &Self::Target { &self.values }
}

impl DerefMut for RuntimeRegisters {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.values }
}

#[derive(Clone)]
struct RuntimeContinuation {
    target: usize,
    dst: u32,
    registers: RuntimeRegisters,
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
    registers: RuntimeRegisters,
    pc: usize,
    return_destination: u32,
}

#[derive(Clone)]
struct RuntimeProgramContinuation {
    definition: DefKey,
    callers: Vec<RuntimeProgramCaller>,
}

/// Copy only shared, still-live source allocations between saved executions.
/// Their SSA values and clause-local temporaries remain independent. The
/// protected computation may currently be deeper in the ordinary call stack.
fn synchronize_saved_source_storage(
    saved: &mut RuntimeRegisters,
    saved_program: Option<&mut RuntimeProgramContinuation>,
    current: &RuntimeRegisters,
    current_callers: &[RuntimeProgramCaller],
) {
    let Some(saved_program) = saved_program else {
        saved.synchronize_source_storage(current);
        return;
    };
    for (saved_caller, current_caller) in saved_program.callers.iter_mut().zip(current_callers) {
        saved_caller.registers.synchronize_source_storage(&current_caller.registers);
    }
    match saved_program.callers.len().cmp(&current_callers.len()) {
        std::cmp::Ordering::Equal => saved.synchronize_source_storage(current),
        std::cmp::Ordering::Less => {
            saved.synchronize_source_storage(&current_callers[saved_program.callers.len()].registers);
        }
        std::cmp::Ordering::Greater => {
            saved_program.callers[current_callers.len()].registers.synchronize_source_storage(current);
        }
    }
}

/// A clause-side call frame for `ResumeReturn`.  It is intentionally separate
/// from ordinary function calls: resumption return restores the handler
/// environment captured immediately before the transfer, including the
/// retained replay snapshot.
struct RuntimeResumptionReturn {
    pc: usize,
    dst: u32,
    /// The captured delimiter may precede newer call-site handlers.
    handler_id: u64,
    registers: RuntimeRegisters,
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
    payloads: Option<Vec<VmValue>>,
}

fn allowed_before_payload_claim(instruction: &VmInstruction) -> bool {
    matches!(instruction, VmInstruction::PatternTest { .. } | VmInstruction::BranchBool { .. }
        | VmInstruction::Jump { .. } | VmInstruction::ClaimEffectPayloads { .. }
        | VmInstruction::Forward | VmInstruction::SetDropFlag { .. }
        | VmInstruction::StorageLive { .. } | VmInstruction::ConstBool { .. })
}

impl VmValue {
    fn ty(&self) -> VmType {
        match self {
            Self::Resident(home) => home.ty().clone(),
            Self::RawPointer { signature, .. } => signature.clone(),
            Self::Uninitialized(ty) => ty.clone(),
            Self::SuspendedReference(reference) => reference.ty(),
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

fn storage_is_initialized(value: Option<&VmValue>, fields: &[u32]) -> bool {
    let Some(value) = value else { return false; };
    if let VmValue::Resident(home) = value { return home.is_initialized(fields); }
    if matches!(value, VmValue::Uninitialized(_)) { return false; }
    let Some((field, rest)) = fields.split_first() else { return true; };
    let values = match value {
        VmValue::Tuple(values) | VmValue::Array { values }
        | VmValue::Record { fields: values, .. } | VmValue::Enum { fields: values, .. } => values,
        _ => return false,
    };
    storage_is_initialized(values.get(*field as usize), rest)
}

fn take_storage_projection(
    registers: &mut [Option<VmValue>],
    base: u32,
    fields: &[u32],
    expected: &VmType,
    budget: &mut ExecutionBudget,
) -> Result<VmValue, VmArtifactError> {
    let value = registers.get_mut(base as usize)
        .ok_or(VmArtifactError::InvalidRegister { register: base })?
        .as_mut().ok_or(VmArtifactError::UseAfterMove { register: base })?;
    if let VmValue::Resident(home) = value {
        let value = home.take(fields, budget)?;
        if !value_matches_vm_layout(&value, expected, Initialization::Storage) {
            return Err(VmArtifactError::ResultType { expected: expected.clone(), found: value.ty() });
        }
        return Ok(value);
    }
    let slot = project_reference_mut(value, fields, budget)?;
    if matches!(slot, VmValue::Uninitialized(_)) {
        return Err(VmArtifactError::UseAfterMove { register: base });
    }
    // Taking storage relocates its initialization mask as well as its
    // contents. A nested partially consumed product must remain available
    // to structural cleanup; this does not make its holes readable values.
    if !value_matches_vm_layout(slot, expected, Initialization::Storage) {
        return Err(VmArtifactError::ResultType { expected: expected.clone(), found: slot.ty() });
    }
    let ty = slot.ty();
    Ok(std::mem::replace(slot, VmValue::Uninitialized(ty)))
}

fn project_reference(value: &VmValue, fields: &[u32]) -> Result<VmValue, VmArtifactError> {
    let Some((field, rest)) = fields.split_first() else {
        return Ok(value.clone());
    };
    let values: &[VmValue] = match value {
        VmValue::Tuple(values) => values,
        VmValue::Array { values, .. } => values,
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

fn project_native_home(value: &VmValue, index: u32, count: u32, expected: &VmType, budget: &mut ExecutionBudget)
    -> Result<Option<VmValue>, VmArtifactError>
{
    let VmValue::Resident(home) = value else { return Ok(None); };
    let fields = home.field_count(&[])?;
    if fields != count as usize { return Err(VmArtifactError::CallArity { expected: count, found: fields as u32 }); }
    let value = home.load(&[index], budget)?;
    if !value_matches_vm_type(&value, expected) {
        return Err(VmArtifactError::ResultType { expected: expected.clone(), found: value.ty() });
    }
    Ok(Some(value))
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
        (VmValue::Array { values, .. }, VmType::FixedArray { element, length }) => VmType::FixedArray {
            element: Box::new(values.first().map(|value| borrowed_value_type(value, element)).unwrap_or((**element).clone())),
            length: if values.len() as u64 == *length { *length } else { values.len() as u64 },
        },
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
        if let ReferenceTarget::Home(home) = target {
            let (_, layout) = home.project(&path)?;
            if !reference_view_matches(declared_referent, &layout.ty, unique) {
                return Err(VmArtifactError::ResultType { expected: declared_referent.clone(), found: layout.ty.clone() });
            }
            return Ok(VmValue::Reference { target: target.clone(), fields: path.into(), unique, referent: declared_referent.clone() });
        }
        if let ReferenceTarget::Native(native) = target {
            let projected = native.project(&path)?;
            let referent = projected.ty().clone();
            if !reference_view_matches(declared_referent, &referent, unique) {
                return Err(VmArtifactError::ResultType { expected: declared_referent.clone(), found: referent });
            }
            return Ok(VmValue::Reference { target: ReferenceTarget::Native(projected), fields: Arc::from([]), unique, referent: declared_referent.clone() });
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
    if let VmValue::Resident(home) = value {
        let (_, layout) = home.project(fields)?;
        if !unique && !home.is_initialized(fields) { return Err(VmArtifactError::UseAfterMove { register: source }); }
        if !reference_view_matches(declared_referent, &layout.ty, unique) {
            return Err(VmArtifactError::ResultType { expected: declared_referent.clone(), found: layout.ty.clone() });
        }
        return Ok(VmValue::Reference { target: ReferenceTarget::Home(home.clone()), fields: fields.to_vec().into(), unique, referent: declared_referent.clone() });
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
        ReferenceTarget::Home(_) => Err(VmArtifactError::NativeMemory { message: "native home requires a typed memory access" }),
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
        ReferenceTarget::Home(home) => home.load(fields, budget),
        ReferenceTarget::Native(native) => native.read(fields, budget),
        _ => project_reference(reference_target(registers, callers, target)?, fields),
    }
}

fn take_reference_target(
    registers: &mut [Option<VmValue>], callers: &mut [RuntimeProgramCaller], target: &ReferenceTarget,
    fields: &[u32], budget: &mut ExecutionBudget,
) -> Result<VmValue, VmArtifactError> {
    match target {
        ReferenceTarget::Home(home) => home.take(fields, budget),
        ReferenceTarget::Native(native) => native.take(fields, budget),
        _ => {
            let owner = reference_target_mut(registers, callers, target)?;
            let resident = project_reference_mut(owner, fields, budget)?;
            if matches!(resident, VmValue::Uninitialized(_)) {
                return Err(VmArtifactError::NativeMemory { message: "reference resident was moved out" });
            }
            let ty = resident.ty();
            Ok(std::mem::replace(resident, VmValue::Uninitialized(ty)))
        }
    }
}

fn referent_is_initialized(registers: &[Option<VmValue>], callers: &[RuntimeProgramCaller],
    reference: &VmValue) -> Result<bool, VmArtifactError> {
    match reference {
        VmValue::SuspendedReference(_) => Ok(false),
        VmValue::Reference { target: ReferenceTarget::Home(home), fields, .. } => Ok(home.is_initialized(fields)),
        VmValue::Reference { target: ReferenceTarget::Native(native), fields, .. } => Ok(native.is_initialized(fields)),
        VmValue::Reference { target, fields, .. } =>
            Ok(storage_is_initialized(Some(reference_target(registers, callers, target)?), fields)),
        _ => Err(VmArtifactError::InvalidRegister { register: 0 }),
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
    if let ReferenceTarget::Home(home) = target {
        return home.store(fields, &replacement, budget);
    }
    if let ReferenceTarget::Native(native) = target {
        return native.write(fields, replacement, budget);
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
        ReferenceTarget::Home(_) => return Err(VmArtifactError::NativeMemory { message: "native home requires a typed memory store" }),
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

fn replace_referenced_array(
    registers: &mut [Option<VmValue>],
    callers: &mut [RuntimeProgramCaller],
    reference: &VmValue,
    values: Vec<VmValue>,
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
    store_reference_target(
        registers,
        callers,
        target,
        fields,
        VmValue::Array {
            values: values.into(),
        },
        budget,
    )
}

fn array_element_borrow(
    reference: &VmValue,
    index: u32,
    element_type: &VmType,
) -> Result<VmValue, VmArtifactError> {
    let VmValue::Reference {
        target,
        fields,
        ..
    } = reference
    else {
        return Err(VmArtifactError::InvalidRegister { register: 0 });
    };
    let mut fields = fields.to_vec();
    fields.push(index);
    Ok(VmValue::Reference {
        target: target.clone(),
        fields: fields.into(),
        unique: false,
        referent: element_type.clone(),
    })
}

/// Storage-only array operations: no destructor lookup or semantic callback.
fn execute_array_storage(
    registers: &mut [Option<VmValue>],
    function: &VmFunction,
    instruction: &VmInstruction,
    budget: &mut ExecutionBudget,
) -> Result<(), VmArtifactError> {
    match instruction {
        VmInstruction::StoreUsize { dst, value } => {
            registers[*dst as usize] = Some(VmValue::Usize(expect_usize(registers[*value as usize].as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *value })?)?));
        }
        VmInstruction::ArrayLen { dst, value } => {
            let count = match registers[*value as usize].as_ref() {
                Some(VmValue::Array { values }) => values.len(),
                Some(VmValue::Resident(home)) if matches!(home.ty(), VmType::FixedArray { .. }) => home.field_count(&[])?,
                _ => return Err(VmArtifactError::InvalidRegister { register: *value }),
            };
            registers[*dst as usize] = Some(VmValue::Usize(count as u64));
        }
        VmInstruction::ArrayElementIsInitialized { dst, value, index }
        | VmInstruction::TakeArrayElement { dst, value, index } => {
            let index = expect_usize(registers[*index as usize].as_ref()
                .ok_or(VmArtifactError::InvalidRegister { register: *index })?)?;
            let index = u32::try_from(index).map_err(|_| VmArtifactError::InvalidRegister { register: *value })?;
            let count = match registers[*value as usize].as_ref() {
                Some(VmValue::Array { values }) => values.len(),
                Some(VmValue::Resident(home)) if matches!(home.ty(), VmType::FixedArray { .. }) => home.field_count(&[])?,
                _ => return Err(VmArtifactError::InvalidRegister { register: *value }),
            };
            if index as usize >= count {
                return Err(VmArtifactError::InvalidRegister { register: *value });
            }
            let result = if matches!(instruction, VmInstruction::TakeArrayElement { .. }) {
                take_storage_projection(registers, *value, &[index], &register_type(function, *dst)?, budget)?
            } else {
                VmValue::Bool(storage_is_initialized(registers[*value as usize].as_ref(), &[index]))
            };
            registers[*dst as usize] = Some(result);
        }
        _ => unreachable!("non-storage operation passed to array storage executor"),
    }
    Ok(())
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
        VmInstruction::ArrayEmpty { dst, .. } => {
            registers[*dst as usize] = Some(VmValue::Array {
                values: Arc::from([]),
            })
        }
        VmInstruction::ArrayGetBorrowShared {
            dst,
            value,
            index: position,
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
                    registers[*dst as usize] = Some(array_element_borrow(reference, position as u32, element_type)?);
                }
                _ => return Err(VmArtifactError::InvalidRegister { register: *value }),
            }
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
        VmValue::Reference { target: ReferenceTarget::Native(_) | ReferenceTarget::Home(_), .. } => Ok(value.clone()),
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
                ReferenceTarget::Captured(_) | ReferenceTarget::Native(_) | ReferenceTarget::Home(_) => (&[][..], &[][..]),
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
        VmValue::Array { values } => Ok(VmValue::Array {
            values: values
                .iter()
                .map(|value| freeze_frame_value(value, registers, callers))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
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
                ReferenceTarget::Home(home) => ReferenceTarget::Home(home),
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
        VmValue::Array { values } => Ok(VmValue::Array {
            values: values
                .iter()
                .cloned()
                .map(|value| rebase_caller_references(value, caller_depth))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
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
                (_, ReferenceTarget::Home(home)) => ReferenceTarget::Home(home.clone()),
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
        VmValue::Array { values } => Ok(VmValue::Array {
            values: values
                .iter()
                .map(|value| transfer_call_frame_value(value, registers, callers, transfer))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
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

fn format_vm_value(value: &VmValue, budget: &mut ExecutionBudget) -> Result<String, VmArtifactError> {
    Ok(match value {
        VmValue::Resident(home) => return format_vm_value(&home.load(&[], budget)?, budget),
        VmValue::Uninitialized(_) | VmValue::SuspendedReference(_) => "<uninitialized storage>".into(),
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
                .map(|value| format_vm_value(value, budget))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ")
        ),
        VmValue::Array { values, .. } => format!(
            "[{}]",
            values
                .iter()
                .map(|value| format_vm_value(value, budget))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ")
        ),
        VmValue::Record {
            definition, fields, ..
        } => format!(
            "record@{definition:?}({})",
            fields
                .iter()
                .map(|value| format_vm_value(value, budget))
                .collect::<Result<Vec<_>, _>>()?
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
                .map(|value| format_vm_value(value, budget))
                .collect::<Result<Vec<_>, _>>()?
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
                ReferenceTarget::Native(_) | ReferenceTarget::Home(_) => "native".into(),
            };
            format!("reference@{target}[fields={}]", fields.len())
        }
    })
}
fn expect_unit(value: impl Borrow<VmValue>) -> Result<(), VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_unit(home.scalar_value()?),
        VmValue::Unit => Ok(()),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Unit,
            found: value.ty(),
        }),
    }
}
fn expect_i64(value: impl Borrow<VmValue>) -> Result<i64, VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_i64(home.scalar_value()?),
        VmValue::I64(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::I64,
            found: value.ty(),
        }),
    }
}
fn expect_usize(value: impl Borrow<VmValue>) -> Result<u64, VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_usize(home.scalar_value()?),
        VmValue::Usize(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Usize,
            found: value.ty(),
        }),
    }
}
fn expect_u32(value: impl Borrow<VmValue>) -> Result<u32, VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_u32(home.scalar_value()?),
        VmValue::U32(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::U32,
            found: value.ty(),
        }),
    }
}
fn expect_u8(value: impl Borrow<VmValue>) -> Result<u8, VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_u8(home.scalar_value()?),
        VmValue::U8(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::U8,
            found: value.ty(),
        }),
    }
}
fn expect_u16(value: impl Borrow<VmValue>) -> Result<u16, VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_u16(home.scalar_value()?),
        VmValue::U16(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::U16,
            found: value.ty(),
        }),
    }
}
fn expect_i16(value: impl Borrow<VmValue>) -> Result<i16, VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_i16(home.scalar_value()?),
        VmValue::I16(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::I16,
            found: value.ty(),
        }),
    }
}
fn expect_i32(value: impl Borrow<VmValue>) -> Result<i32, VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_i32(home.scalar_value()?),
        VmValue::I32(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::I32,
            found: value.ty(),
        }),
    }
}
fn expect_i8(value: impl Borrow<VmValue>) -> Result<i8, VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_i8(home.scalar_value()?),
        VmValue::I8(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::I8,
            found: value.ty(),
        }),
    }
}
fn expect_u64(value: impl Borrow<VmValue>) -> Result<u64, VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_u64(home.scalar_value()?),
        VmValue::U64(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::U64,
            found: value.ty(),
        }),
    }
}
fn expect_isize(value: impl Borrow<VmValue>) -> Result<i64, VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_isize(home.scalar_value()?),
        VmValue::Isize(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Isize,
            found: value.ty(),
        }),
    }
}
fn expect_u128(value: impl Borrow<VmValue>) -> Result<u128, VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_u128(home.scalar_value()?),
        VmValue::U128(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::U128,
            found: value.ty(),
        }),
    }
}
fn expect_i128(value: impl Borrow<VmValue>) -> Result<i128, VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_i128(home.scalar_value()?),
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
        VmValue::Resident(home) => expect_f64(home.scalar_value()?),
        VmValue::F64(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::F64,
            found: value.ty(),
        }),
    }
}
fn expect_f32(value: impl Borrow<VmValue>) -> Result<f32, VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_f32(home.scalar_value()?),
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
        VmValue::Resident(home) => expect_bool(home.scalar_value()?),
        VmValue::Bool(value) => Ok(*value),
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Bool,
            found: value.ty(),
        }),
    }
}

fn returning_resumption_call(
    instruction: &VmInstruction,
    registers: &RuntimeRegisters,
) -> Result<Option<(VmInstruction, u64)>, VmArtifactError> {
    let (dst, callee, arguments) = match instruction {
        VmInstruction::CallIndirect { dst, callee, arguments }
        | VmInstruction::CallIndirectOwned { dst, callee, arguments } => (*dst, *callee, arguments),
        _ => return Ok(None),
    };
    let Some(Some(VmValue::Resumption { frame, .. })) = registers.values.get(callee as usize) else { return Ok(None); };
    let [value] = arguments.as_slice() else { return Err(VmArtifactError::CallArity { expected: 1, found: arguments.len() as u32 }); };
    Ok(Some((VmInstruction::ResumeReturn { dst, value: *value }, *frame)))
}
fn expect_char(value: impl Borrow<VmValue>) -> Result<char, VmArtifactError> {
    match value.borrow() {
        VmValue::Resident(home) => expect_char(home.scalar_value()?),
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
) -> Result<(native_memory::StaticBytes, usize, usize), VmArtifactError> {
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
    if pattern.read_requirement() != PatternRead::None
        && matches!(value, VmValue::Uninitialized(_)) { return false; }
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
        VmPattern::Array { element, elements, rest } => match value {
            VmValue::Array { values, .. }
                if crate::pattern::ArrayPatternRest::length(*rest, elements.len()) == Some(values.len())
                    && values
                        .iter()
                        .all(|value| value_matches_vm_type(value, element)) =>
            {
                elements.iter().enumerate().all(|(index, pattern)|
                    matches_pattern(&values[crate::pattern::ArrayPatternRest::index(*rest, index)], pattern))
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

fn matches_runtime_pattern(value: &VmValue, pattern: &VmPattern,
    registers: &[Option<VmValue>], callers: &[RuntimeProgramCaller],
    budget: &mut ExecutionBudget) -> Result<bool, VmArtifactError> {
    if matches!(pattern, VmPattern::Any) { return Ok(true); }
    match value {
        VmValue::Resident(home) => home.matches_pattern(&mut vec![], pattern, budget),
        VmValue::Reference { target: ReferenceTarget::Home(home), fields, .. } =>
            home.matches_pattern(&mut fields.to_vec(), pattern, budget),
        VmValue::Reference { target, fields, .. } => {
            let value = load_reference_target(registers, callers, target, fields, budget)?;
            matches_runtime_pattern(&value, pattern, registers, callers, budget)
        }
        _ => Ok(matches_pattern(value, pattern)),
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
            .all(|(value, ty)| value_matches_vm_layout(value, ty, Initialization::Storage))
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Initialization { Value, Storage }

/// A VM generic is a declaration-local wildcard at runtime; every other
/// structural component must agree exactly with the value's concrete shape.
fn value_matches_vm_type(value: &VmValue, expected: &VmType) -> bool {
    value_matches_vm_layout(value, expected, Initialization::Value)
}

/// Value reads require initialized leaves. Storage relocation and tag-only
/// destruction dispatch retain typed holes recursively, but never erase a
/// hole or confer permission to read it. Both modes use the same layout rules.
fn value_matches_vm_layout(value: &VmValue, expected: &VmType, initialization: Initialization) -> bool {
    if let VmValue::Uninitialized(actual) = value {
        return initialization == Initialization::Storage && vm_type_matches(actual, expected);
    }
    if matches!(value, VmValue::SuspendedReference(_)) { return false; }
    if let VmValue::Resident(home) = value {
        return (match initialization {
            Initialization::Value => home.is_fully_initialized(&[]),
            Initialization::Storage => home.is_initialized(&[]),
        }) && vm_type_matches(home.ty(), expected);
    }
    match expected {
        VmType::Generic(_) => true,
        // Structural constants inhabit nominal identity only; no standalone
        // runtime value may claim one of these metadata-only layouts.
        VmType::ConstInteger(_)
        | VmType::ConstIntegerExpr(_)
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
            matches!(value, VmValue::Tuple(values) if values.len() == expected.len() && values.iter().zip(expected).all(|(value, ty)| value_matches_vm_layout(value, ty, initialization)))
        }
        VmType::Array(expected) => {
            matches!(value, VmValue::Array { values, .. } if values.iter().all(|value| value_matches_vm_layout(value, expected, initialization)))
        }
        VmType::FixedArray { element, length } => {
            matches!(value, VmValue::Array { values, .. } if values.len() as u64 == *length
                && values.iter().all(|value| value_matches_vm_layout(value, element, initialization)))
        }
        VmType::Nominal {
            definition,
            arguments,
        } => {
            matches!(value, VmValue::Record { definition: actual, signature: VmType::Nominal { definition: signature_definition, arguments: actual_arguments }, .. } | VmValue::Enum { definition: actual, signature: VmType::Nominal { definition: signature_definition, arguments: actual_arguments }, .. } if actual == definition && signature_definition == definition && actual_arguments.len() == arguments.len() && actual_arguments.iter().zip(arguments).all(|(actual, expected)| vm_generic_argument_matches(actual, expected)))
        }
        // Control tokens expose the same checked source callable signature.
        // Matching that value layout does not supply invocation authority:
        // label/resumption dispatch still authenticates the live destination.
        VmType::Callable { .. } => matches!(value,
            VmValue::Callable { signature, .. } | VmValue::Label { signature, .. }
                | VmValue::Resumption { signature, .. } if vm_type_matches(signature, expected)),
        VmType::RawPointer { .. } => matches!(value, VmValue::RawPointer { signature, .. } if vm_type_matches(signature, expected)),
        VmType::Reference { unique, referent } => {
            matches!(value, VmValue::Reference { unique: actual_unique, referent: actual_referent, .. } if actual_unique == unique && vm_type_matches(actual_referent, referent))
        }
    }
}

fn vm_type_matches(actual: &VmType, expected: &VmType) -> bool {
    vm_type_matches_variance(actual, expected, ReceiverVariance::Covariant)
}

fn vm_type_matches_variance(actual: &VmType, expected: &VmType, variance: ReceiverVariance) -> bool {
    match expected {
        VmType::FixedArray { element, length } => matches!(actual, VmType::FixedArray { element: actual, length: count }
            if length == count && vm_type_matches_variance(actual, element, variance)),
        VmType::Generic(_) => true,
        VmType::Array(expected) => {
            matches!(actual, VmType::Array(actual) if vm_type_matches_variance(actual, expected, variance))
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
            && vm_type_matches_variance(actual_element, expected_element, variance)),
        VmType::Tuple(expected) => {
            matches!(actual, VmType::Tuple(actual) if actual.len() == expected.len() && actual.iter().zip(expected).all(|(actual, expected)| vm_type_matches_variance(actual, expected, variance)))
        }
        VmType::Nominal {
            definition,
            arguments,
        } => {
            matches!(actual, VmType::Nominal { definition: actual_definition, arguments: actual_arguments } if actual_definition == definition && actual_arguments.len() == arguments.len() && actual_arguments.iter().zip(arguments).all(|(actual, expected)| vm_generic_argument_matches(actual, expected)))
        }
        VmType::Callable {
            shared_receiver,
            unique_receiver,
            safety,
            parameters,
            result,
            effects,
        } => {
            matches!(actual, VmType::Callable { shared_receiver: actual_shared, unique_receiver: actual_unique, safety: actual_safety, parameters: actual_parameters, result: actual_result, effects: actual_effects }
                if variance.permits(*shared_receiver, *actual_shared) && variance.permits(*unique_receiver, *actual_unique)
                    && actual_safety == safety && actual_parameters.len() == parameters.len()
                    && actual_parameters.iter().zip(parameters).all(|(actual, expected)| vm_type_matches_variance(actual, expected, variance.reversed()))
                    && vm_type_matches_variance(actual_result, result, variance) && vm_effect_row_matches(actual_effects, effects))
        }
        VmType::RawPointer { mutability, pointee } => matches!(actual,
            VmType::RawPointer { mutability: actual_mutability, pointee: actual_pointee }
                if actual_mutability == mutability && vm_type_matches_variance(actual_pointee, pointee, ReceiverVariance::Invariant)),
        VmType::Reference { unique, referent } => {
            matches!(actual, VmType::Reference { unique: actual_unique, referent: actual_referent } if actual_unique == unique
                && vm_type_matches_variance(actual_referent, referent, if *unique { ReceiverVariance::Invariant } else { variance }))
        }
        _ => actual == expected,
    }
}

fn vm_effect_row_matches(actual: &VmEffectRow, expected: &VmEffectRow) -> bool {
    actual.tails == expected.tails
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
                vm_type_matches_variance(&actual.subject, &expected.subject, ReceiverVariance::Invariant)
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
            vm_type_matches_variance(actual, expected, ReceiverVariance::Invariant)
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
        VmValue::F64(value) => parse_pattern_f64(literal).is_some_and(|literal|
            canonical_f64_bits(literal.to_bits()) == canonical_f64_bits(value.to_bits())),
        VmValue::F32(value) => {
            crate::mir::parse_f32_literal(literal).is_ok_and(|literal|
                crate::mir::canonical_f32_bits(literal.to_bits()) == crate::mir::canonical_f32_bits(value.to_bits()))
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
    crate::mir::normalized_integer_literal(text, ScalarType::I64).ok()?.parse().ok()
}
fn parse_pattern_u64(text: &str) -> Option<u64> {
    crate::mir::normalized_integer_literal(text, ScalarType::U64).ok()?.parse().ok()
}
fn parse_pattern_u128(text: &str) -> Option<u128> {
    crate::mir::normalized_integer_literal(text, ScalarType::U128).ok()?.parse().ok()
}
fn parse_pattern_i128(text: &str) -> Option<i128> {
    crate::mir::normalized_integer_literal(text, ScalarType::I128).ok()?.parse().ok()
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
    float_env::with_profile(|| execute_in_float_profile(function, budget))
}

fn execute_in_float_profile(
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
    let mut registers = RuntimeRegisters::for_function(function, budget)?;
    let mut next_storage_id = 0u64;
    let mut handlers = Vec::<RuntimeHandlerFrame>::new();
    let mut resumption_returns = Vec::<RuntimeResumptionReturn>::new();
    let mut next_handler_id = 0u64;
    let mut pc = 0usize;
    while let Some(instruction) = function.instructions.get(pc).cloned() {
        registers.finish_native_writes(budget)?;
        budget.tick()?;
        registers.instruction_result(pc);
        let consumes_arguments = instruction.consumed_arguments().is_some();
        let owned_payloads = matches!(instruction, VmInstruction::PerformOwned { .. } | VmInstruction::InstallHandlerOwned { .. });
        let replay_owned = match &instruction {
            VmInstruction::InstallHandlerOwned { replay_owned, .. } => replay_owned.clone(),
            _ => vec![],
        };
        if handlers.last().is_some_and(|frame| frame.owned_payloads && frame.suspended.as_ref().is_some_and(|continuation| continuation.performed.payloads.is_some()))
            && !allowed_before_payload_claim(&instruction) {
            return Err(VmArtifactError::HandlerStateMismatch);
        }
        let captured_call = returning_resumption_call(&instruction, &registers)?;
        let resumption_index = captured_call.as_ref().map(|(_, id)| handlers.iter().rposition(|frame| frame.id == *id)
            .ok_or(VmArtifactError::HandlerResumeUnavailable)).transpose()?;
        let instruction = captured_call.map_or(instruction, |(instruction, _)| instruction);
        match instruction {
            VmInstruction::DeclareResult { .. } | VmInstruction::DeclareFrameCleanup { .. } => {}
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
                    bytes: budget.native_memory.static_literal(function.definition, pc, &bytes),
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
            VmInstruction::Blake3 { dst, value } => {
                let bytes = expect_bytes(
                    registers[value as usize].as_ref().expect("verified register"),
                )?;
                budget.reserve_value("bytes", blake3::OUT_LEN)?;
                registers[dst as usize] = Some(VmValue::Bytes(Arc::from(
                    blake3::hash(&bytes).as_bytes().as_slice(),
                )));
            }
            instruction @ (VmInstruction::StoreUsize { .. } | VmInstruction::ArrayLen { .. } | VmInstruction::ArrayElementIsInitialized { .. } | VmInstruction::TakeArrayElement { .. }) => {
                execute_array_storage(&mut registers, function, &instruction, budget)?
            }
            instruction @ (VmInstruction::ArrayGetBorrowShared { .. } | VmInstruction::ArrayEmpty { .. } | VmInstruction::ArrayPushMove { .. }) => {
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
            VmInstruction::MakeTupleOwned { dst, fields } | VmInstruction::MakeTuple { dst, fields } => {
                budget.reserve_value("tuple fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| registers.constructor_field(dst, *field, budget))
                    .collect::<Result<Vec<_>, _>>()?;
                registers[dst as usize] = Some(VmValue::Tuple(Arc::from(values)));
                if consumes_arguments { registers.finish_native_writes(budget)?; registers.retire_call_arguments(&fields); }
            }
            VmInstruction::MakeArrayOwned { dst, fields, .. } | VmInstruction::MakeArray { dst, fields, .. } => {
                budget.reserve_value("array elements", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| registers.constructor_field(dst, *field, budget))
                    .collect::<Result<Vec<_>, _>>()?;
                registers[dst as usize] = Some(VmValue::Array {
                    values: Arc::from(values),
                });
                if consumes_arguments { registers.finish_native_writes(budget)?; registers.retire_call_arguments(&fields); }
            }
            VmInstruction::MakeRecordOwned { dst, definition, fields, .. } | VmInstruction::MakeRecord {
                dst,
                definition,
                fields,
                ..
            } => {
                budget.reserve_value("record fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| registers.constructor_field(dst, *field, budget))
                    .collect::<Result<Vec<_>, _>>()?;
                let signature = register_type(function, dst)?;
                registers[dst as usize] = Some(VmValue::Record {
                    definition,
                    fields: Arc::from(values),
                    signature,
                });
                if consumes_arguments { registers.finish_native_writes(budget)?; registers.retire_call_arguments(&fields); }
            }
            VmInstruction::MakeEnumOwned { dst, definition, variant, fields, .. } | VmInstruction::MakeEnum {
                dst,
                definition,
                variant,
                fields,
                ..
            } => {
                budget.reserve_value("enum fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| registers.constructor_field(dst, *field, budget))
                    .collect::<Result<Vec<_>, _>>()?;
                let signature = register_type(function, dst)?;
                registers[dst as usize] = Some(VmValue::Enum {
                    definition,
                    variant,
                    fields: Arc::from(values),
                    signature,
                });
                if consumes_arguments { registers.finish_native_writes(budget)?; registers.retire_call_arguments(&fields); }
            }
            VmInstruction::IsInitialized { dst, base, fields } => {
                registers[dst as usize] = Some(VmValue::Bool(storage_is_initialized(
                    registers[base as usize].as_ref(), &fields,
                )));
            }
            VmInstruction::DerefIsInitialized { dst, reference } => {
                let initialized = referent_is_initialized(&registers, &[],
                    &registers.copy_value(reference, budget)?)?;
                registers[dst as usize] = Some(VmValue::Bool(initialized));
            }
            VmInstruction::TakeProjection { dst, base, fields } => {
                let expected = register_type(function, dst)?;
                registers[dst as usize] = Some(take_storage_projection(
                    &mut registers, base, &fields, &expected, budget,
                )?);
            }
            VmInstruction::ProjectRecord {
                dst,
                base,
                index,
                field_count,
                field_type,
            } => {
                if let Some(value) = project_native_home(registers[base as usize].as_ref().expect("verified register"),
                    index, field_count, &field_type, budget)? {
                    registers[dst as usize] = Some(value); pc += 1; continue;
                }
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
                if let Some(value) = project_native_home(registers[base as usize].as_ref().expect("verified register"),
                    index, field_count, &function.registers[dst as usize], budget)? {
                    registers[dst as usize] = Some(value); pc += 1; continue;
                }
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
                if let Some(value) = project_native_home(registers[base as usize].as_ref().expect("verified register"),
                    index, field_count, &function.registers[dst as usize], budget)? {
                    registers[dst as usize] = Some(value); pc += 1; continue;
                }
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
                let base_value = registers.copy_value(base, budget)?;
                let VmValue::Record {
                    definition,
                    fields,
                    signature,
                } = &base_value
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
                *field = registers.copy_value(value, budget)?;
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
                registers[dst as usize] = Some(VmValue::Bool(matches_runtime_pattern(
                    registers[subject as usize]
                        .as_ref()
                        .expect("verified register"),
                    &pattern, &registers, &[], budget,
                )?));
            }
            VmInstruction::PerformOwned {
                dst,
                effect,
                effect_arguments,
                operation,
                arguments,
            }
            | VmInstruction::Perform {
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
                        registers.copy_value(*argument, budget)
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
                if frame.owned_payloads != owned_payloads { return Err(VmArtifactError::HandlerStateMismatch); }
                if frame.payload_destinations.len() != values.len() {
                    return Err(VmArtifactError::CallArity {
                        expected: frame.payload_destinations.len() as u32,
                        found: values.len() as u32,
                    });
                }
                budget.reserve_allocation(registers.len())?;
                if owned_payloads { registers.retire_call_arguments(&arguments); }
                let saved = registers.clone();
                for (destination, value) in frame
                    .payload_destinations
                    .iter()
                    .zip(values.iter().cloned())
                {
                    registers[*destination as usize] = Some(value);
                    registers.native_write(*destination);
                }
                frame.suspended = Some(RuntimeContinuation {
                    target: pc + 1,
                    dst,
                    registers: saved,
                    performed: RuntimePerformed {
                        effect,
                        effect_arguments,
                        operation,
                        payloads: Some(values),
                    },
                    above,
                    pending_leave: None,
                    remaining_replays: frame.continuation.replay_uses().unwrap_or(0),
                    program: None,
                });
                pc = frame.target as usize;
                continue;
            }
            VmInstruction::ClaimEffectPayloads { payloads } => {
                let frame = handlers.last_mut().ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                if !frame.owned_payloads || frame.payload_destinations != payloads {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                frame.suspended.as_mut().and_then(|continuation| continuation.performed.payloads.take())
                    .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
            }
            VmInstruction::InstallHandlerOwned {
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                continuation,
                target,
                ..
            }
            | VmInstruction::InstallHandler {
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
                    owned_payloads,
                    shared_registers: replay::shared_registers(&registers, owned_payloads && continuation.is_replay(), &replay_owned, budget)?,
                    suspended: None,
                })
            }
            VmInstruction::CompleteHandler { value } => {
                let frame = handlers.last().ok_or(VmArtifactError::HandlerStackUnderflow)?;
                if frame.suspended.is_some() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                if resumption_returns.last().is_some_and(|pending| {
                    pending.handler_id == frame.id
                }) {
                    let result = registers.copy_value(value, budget)?;
                    let mut pending = resumption_returns.pop().expect("checked pending resumption");
                    expect_type(function, value, register_type(function, pending.dst)?)?;
                    pending.registers.synchronize_source_storage(&registers);
                    registers = pending.registers;
                    registers[pending.dst as usize] = Some(result);
                    registers.native_write(pending.dst);
                    handlers = pending.handlers;
                    pc = pending.pc;
                    continue;
                }
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
                let resumed = registers.copy_value(value, budget)?;
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
                if frame.owned_payloads {
                    registers.retire_call_arguments(&[value]);
                }
                let RuntimeContinuation {
                    target,
                    dst,
                    registers: mut saved_registers,
                    above,
                    pending_leave,
                    ..
                } = continuation;
                saved_registers.synchronize_source_storage(&registers);
                if let Some(leave) = pending_leave {
                    registers = saved_registers;
                    handlers.extend(above);
                    pc = complete_pending_leave(&mut registers, &mut handlers, leave, budget)?;
                    continue;
                }
                registers = saved_registers;
                registers[dst as usize] = Some(resumed);
                registers.native_write(dst);
                handlers.extend(above);
                pc = target;
                continue;
            }
            VmInstruction::ResumeReturn { dst, value } => {
                let resumed = registers.copy_value(value, budget)?;
                let index = resumption_index.or_else(|| handlers.len().checked_sub(1))
                    .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                let Some(frame) = handlers.get_mut(index) else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.continuation == VmContinuationPolicy::Terminal {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let replaying = frame.continuation.is_replay();
                let continuation = if replaying {
                    if frame.owned_payloads {
                        frame.suspended.as_ref().map(|saved| replay::fork(saved, frame.call_depth,
                            &frame.shared_registers, &mut next_storage_id, budget)).transpose()?
                    } else { frame.suspended.clone() }
                } else {
                    frame.suspended.take()
                }
                .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                if replaying && continuation.remaining_replays == 0 {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                budget.reserve_allocation(registers.len())?;
                // The clause snapshot must not retain the carrier just
                // transferred to the resumed computation.
                if frame.owned_payloads || consumes_arguments {
                    registers.retire_call_arguments(&[value]);
                }
                let RuntimeContinuation {
                    target,
                    dst: continuation_dst,
                    registers: mut saved_registers,
                    above,
                    pending_leave,
                    ..
                } = continuation;
                saved_registers.synchronize_source_storage(&registers);
                if pending_leave.is_some() {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                let mut active_handlers = handlers[..index].to_vec();
                active_handlers.extend_from_slice(&handlers[index + 1..]);
                active_handlers.push(handlers[index].clone());
                let resumed_handler_ids = active_handlers
                    .iter()
                    .map(|frame| frame.id)
                    .chain(above.iter().map(|frame| frame.id))
                    .collect();
                let mut return_handlers = handlers.clone();
                if replaying {
                    return_handlers
                        .get_mut(index)
                        .and_then(|frame| frame.suspended.as_mut())
                        .expect("checked suspended replay handler")
                        .remaining_replays -= 1;
                }
                resumption_returns.push(RuntimeResumptionReturn {
                    pc: pc + 1,
                    dst,
                    handler_id: handlers[index].id,
                    registers: registers.clone(),
                    handlers: return_handlers,
                    program: None,
                    resumed_handler_ids,
                });
                // The active execution gets a clean handler frame so its
                // protected `UninstallHandler` can run. The clause snapshot
                // above retains the suspended continuation for the next use.
                handlers = active_handlers;
                if replaying {
                    handlers.last_mut().expect("active frame exists").suspended = None;
                }
                handlers.extend(above);
                registers = saved_registers;
                registers[continuation_dst as usize] = Some(resumed);
                registers.native_write(continuation_dst);
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
                let resumed = registers.copy_value(value, budget)?;
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
                    VmContinuationPolicy::Consume | VmContinuationPolicy::Replay { .. } => {
                        handlers[index].suspended.take()
                    }
                    VmContinuationPolicy::Terminal => {
                        return Err(VmArtifactError::HandlerResumeUnavailable);
                    }
                }
                .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                if handlers[index].owned_payloads {
                    registers.retire_call_arguments(&[value]);
                }
                // Resumption is a non-local transfer. Frames installed after
                // the captured frame belong to the abandoned clause path;
                // only the deep frames recorded at the original `Perform`
                // are reinstated with the continuation.
                handlers.truncate(index + 1);
                let RuntimeContinuation {
                    target,
                    dst,
                    registers: mut saved_registers,
                    above,
                    pending_leave,
                    ..
                } = continuation;
                saved_registers.synchronize_source_storage(&registers);
                if let Some(leave) = pending_leave {
                    registers = saved_registers;
                    handlers.extend(above);
                    pc = complete_pending_leave(&mut registers, &mut handlers, leave, budget)?;
                    continue;
                }
                registers = saved_registers;
                registers[dst as usize] = Some(resumed);
                registers.native_write(dst);
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
                let payloads = continuation.performed.payloads.as_ref().ok_or(VmArtifactError::HandlerResumeUnavailable)?;
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
                if handlers[index].owned_payloads != declined.owned_payloads { return Err(VmArtifactError::HandlerStateMismatch); }
                let mut crossed = handlers.split_off(index + 1);
                crossed.push(declined);
                crossed.extend(continuation.above.clone());
                let frame = &mut handlers[index];
                if frame.payload_destinations.len() != payloads.len() {
                    return Err(VmArtifactError::CallArity {
                        expected: frame.payload_destinations.len() as u32,
                        found: payloads.len() as u32,
                    });
                }
                budget.reserve_allocation(continuation.registers.len())?;
                registers = continuation.registers.clone();
                for (destination, payload) in frame
                    .payload_destinations
                    .iter()
                    .zip(payloads.iter().cloned())
                {
                    registers[*destination as usize] = Some(payload);
                    registers.native_write(*destination);
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
                registers.copy_into(dst, src, budget)?;
            }
            VmInstruction::StorageLive { local, .. } => {
                if registers[local as usize].is_some() {
                    return Err(VmArtifactError::ReadBeforeWrite { register: local });
                }
                next_storage_id = next_storage_id.checked_add(1).ok_or(VmArtifactError::HandlerStateMismatch)?;
                registers.source_storage.insert(local, next_storage_id);
            }
            VmInstruction::StorageDead { local, .. } => {
                if registers[local as usize].is_some() {
                    return Err(VmArtifactError::ReadBeforeWrite { register: local });
                }
                registers.source_storage.remove(&local);
                if let Some(home) = registers.native_homes.remove(&local) { home.retire(); }
            }
            VmInstruction::SetDropFlag { flag, value } => {
                registers[flag as usize] = Some(VmValue::Bool(value))
            }
            VmInstruction::DestroyIf { local, flag } => {
                match registers[flag as usize].as_ref() {
                    Some(VmValue::Bool(_)) => {}
                    _ => return Err(VmArtifactError::ReadBeforeWrite { register: flag }),
                }
                registers.clear_value(local);
            }
            VmInstruction::Store { dst, src } => {
                registers.copy_into(dst, src, budget)?;
            }
            VmInstruction::StoreOwned { dst, src } => {
                registers.move_into(dst, src, budget)?;
            }
            VmInstruction::Move { dst, src } => {
                registers.move_into(dst, src, budget)?;
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
                let carrier = if reborrow { registers.copy_value(src, budget)? }
                    else { registers[src as usize].as_ref().expect("verified register").clone() };
                registers[dst as usize] = Some(borrow_value(
                    &registers,
                    &[],
                    src,
                    &carrier,
                    &fields,
                    unique,
                    reborrow,
                    referent,
                )?);
            }
            VmInstruction::DerefCopy { dst, reference } => {
                let carrier = registers.copy_value(reference, budget)?;
                let VmValue::Reference { target, fields, .. } = &carrier
                else {
                    return Err(VmArtifactError::InvalidRegister {
                        register: reference,
                    });
                };
                if matches!(target, ReferenceTarget::Home(_) | ReferenceTarget::Native(_))
                    && let Some((result, index)) = registers.read_projection(pc)
                {
                    // The intervening value has one producer and exactly this
                    // one adjacent consumer. Read only the selected native field;
                    // no aggregate snapshot is observable or needs allocation.
                    let mut path = fields.to_vec(); path.push(index);
                    budget.tick()?;
                    registers[result as usize] = Some(load_reference_target(&registers, &[], target, &path, budget)?);
                    registers.native_write(result);
                    pc += 2; continue;
                }
                registers[dst as usize] = Some(load_reference_target(&registers, &[], target, fields, budget)?);
            }
            VmInstruction::DerefMove { dst, reference } => {
                let carrier = registers.copy_value(reference, budget)?;
                let VmValue::Reference { target, fields, .. } = &carrier
                else {
                    return Err(VmArtifactError::InvalidRegister { register: reference });
                };
                // The loan retains its address but becomes unreadable until
                // restoration. This state also prevents replacement cleanup
                // from destroying the resident transferred out by this move.
                registers[dst as usize] = Some(take_reference_target(&mut registers, &mut [], target, fields, budget)?);
                registers[reference as usize] = Some(VmValue::SuspendedReference(Box::new(carrier)));
            }
            VmInstruction::DerefStore { reference, src } => {
                registers[reference as usize] = registers[reference as usize].take().map(|capability| match capability {
                    VmValue::SuspendedReference(reference) => *reference,
                    reference => reference,
                });
                let carrier = registers.copy_value(reference, budget)?;
                registers.native_write(reference);
                let VmValue::Reference {
                    target,
                    fields,
                    unique: true,
                    ..
                } = &carrier
                else {
                    return Err(VmArtifactError::InvalidRegister {
                        register: reference,
                    });
                };
                let (target, fields) = (target.clone(), fields.clone());
                let replacement = registers.copy_value(src, budget)?;
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
            VmInstruction::CallIndirectOwned { callee, arguments, .. }
            | VmInstruction::CallIndirect {
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
                let payload = registers.copy_value(*argument, budget)?;
                if consumes_arguments { registers.retire_call_arguments(&arguments); }
                registers[destination as usize] = Some(payload);
                registers.native_write(destination);
                handlers.truncate(handler_depth);
                // A dynamic label invocation is the same nonlocal control
                // boundary as a direct Leave: no suspended clause-return
                // path may survive to resurrect an abandoned replay frame.
                resumption_returns.clear();
                pc = target as usize;
                continue;
            }
            VmInstruction::CallOwned { .. } | VmInstruction::Call { .. } | VmInstruction::TailCallOwned { .. } | VmInstruction::MakeCallable { .. }
            | VmInstruction::DestroyCallable { .. } => {
                return Err(VmArtifactError::CallRequiresProgram);
            }
            VmInstruction::HostCallOwned { capability, symbol, .. }
            | VmInstruction::HostCall {
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
                    budget,
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
                    let value = registers.copy_value(value, budget)?;
                    let mut return_to_clause = resumption_returns
                        .pop()
                        .expect("checked clause-return frame exists");
                    return_to_clause.registers.synchronize_source_storage(&registers);
                    registers = return_to_clause.registers;
                    registers[return_to_clause.dst as usize] = Some(value);
                    registers.native_write(return_to_clause.dst);
                    handlers = return_to_clause.handlers;
                    pc = return_to_clause.pc;
                    continue;
                }
                if !handlers.is_empty() {
                    return Err(VmArtifactError::HandlerStillActive);
                }
                return registers.copy_value(value, budget);
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
    registers: &mut RuntimeRegisters,
    handlers: &mut Vec<RuntimeHandlerFrame>,
    leave: PendingLeave,
    budget: &mut ExecutionBudget,
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
    let handler_depth = leave.handler_depth as usize;
    if handler_depth > handlers.len() {
        return Err(VmArtifactError::HandlerStateMismatch);
    }
    let mut consumed = BTreeSet::new();
    for argument in &leave.arguments {
        if !consumed.insert(*argument) {
            return Err(VmArtifactError::MalformedEncoding { message: "label transfer repeats an owned payload carrier" });
        }
    }
    let values = leave
        .arguments
        .iter()
        .map(|argument| registers.copy_value(*argument, budget))
        .collect::<Result<Vec<_>, _>>()?;
    // Materialization above is a parallel transport snapshot, not source
    // Copy. Retire all predecessor carriers before installing any successor
    // value, including cycles and identity edges. Cleanup must not destroy a
    // second owner of the same callable environment after the rejoin.
    for argument in &leave.arguments { registers.clear_value(*argument); }
    for (&destination, value) in leave.destinations.iter().zip(values) {
        let slot =
            registers
                .get_mut(destination as usize)
                .ok_or(VmArtifactError::InvalidRegister {
                    register: destination,
                })?;
        *slot = Some(value);
        registers.native_write(destination);
    }
    // A leave has crossed every active lexical handler. Any captured one-shot
    // continuation was abandoned by the source control transfer, so no frame
    // survives that could later re-authorize a stale snapshot.
    handlers.truncate(handler_depth);
    Ok(leave.target as usize)
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
    execute_program_profiled(program, definition, arguments, depth, budget, host, None, false, None, None)
}

// Recycling leaves the caller stack unchanged. Loans into surviving callers
// therefore retain their coordinates, while loans into the current register
// frame must prevent recycling. Referenced owners and captured shared storage
// must themselves be free of frame-relative capabilities: a surviving outer
// allocation can still contain a label belonging to the frame being recycled.
// The scan is iterative, budgeted, and measured.
fn recyclable_tail_arguments(
    registers: &[Option<VmValue>],
    homes: &BTreeMap<u32, Arc<native_storage::NativeHome>>,
    arguments: &[u32],
    callers: &[RuntimeProgramCaller],
    budget: &mut ExecutionBudget,
    profile: &mut VmAuthoringProfile,
) -> Result<bool, VmArtifactError> {
    // A raw/native recipient may have stored an address somewhere outside the
    // argument graph. Keep the source frame alive for its ordinary lifetime.
    for home in homes.values() {
        budget.tick()?;
        if home.address_was_exposed() { return Ok(false); }
    }
    let mut pending = Vec::new();
    budget.reserve_allocation(arguments.len())?;
    for argument in arguments {
        pending.push((registers[*argument as usize].as_ref().ok_or(
            VmArtifactError::ReadBeforeWrite { register: *argument },
        )?.clone(), true));
    }
    while let Some((value, allow_callers)) = pending.pop() {
        budget.tick()?;
        profile.inspected_tail_argument_elements += 1;
        let fields = match &value {
            VmValue::Reference { target: ReferenceTarget::Home(home), fields, .. } => {
                if !allow_callers || !home.is_initialized(fields)
                    || homes.values().any(|current| Arc::ptr_eq(current, home))
                    || !callers.iter().any(|caller| caller.registers.native_homes.values().any(|owner| Arc::ptr_eq(owner, home)))
                    || home.has_reference_fields(budget)?
                { return Ok(false); }
                continue;
            }
            VmValue::Resident(_) => return Ok(false),
            VmValue::RawPointer { pointer, .. } if homes.values().any(|home| home.contains_address(*pointer)) => return Ok(false),
            VmValue::Reference {
                target: target @ ReferenceTarget::Caller { caller_depth, .. }, ..
            } if allow_callers && (*caller_depth as usize) < callers.len() => {
                budget.reserve_allocation(1)?;
                // Deliberately inspect the whole owner, not only a projection.
                // Nested frame-relative loans fail closed rather than following
                // an unbounded/cyclic reference graph without a retention proof.
                pending.push((reference_target(registers, callers, target)?.clone(), false));
                continue;
            }
            VmValue::Reference {
                target: ReferenceTarget::Captured(value), unique: false, ..
            } => {
                budget.reserve_allocation(1)?;
                pending.push((value.as_ref().clone(), false));
                continue;
            }
            VmValue::Reference { .. } | VmValue::Label { .. } | VmValue::Resumption { .. } => {
                return Ok(false);
            }
            VmValue::Tuple(fields)
            | VmValue::Array { values: fields, .. }
            | VmValue::Record { fields, .. }
            | VmValue::Enum { fields, .. } => fields.as_ref(),
            VmValue::Callable { captures, .. } => {
                let values = captures.values.borrow();
                budget.reserve_allocation(values.len())?;
                pending.extend(values.iter().cloned().map(|value| (value, allow_callers)));
                continue;
            }
            _ => continue,
        };
        budget.reserve_allocation(fields.len())?;
        pending.extend(fields.iter().cloned().map(|value| (value, allow_callers)));
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

// Structural cleanup can leave a guarded CFG after a tail call even when
// every owned payload has already moved. Prove that this *particular* suffix
// only examines frame-local tags/initialization and forwards the unknown call
// result. Never execute or erase a call, load, store, trap, or source destructor.
// A callable with no registered environment destructor has no cleanup effect.
// The caller separately proves that no argument can mutate this frame.
fn tail_cleanup_suffix(
    function: &VmFunction,
    mut pc: usize,
    result: u32,
    registers: &[Option<VmValue>],
    environments: &BTreeMap<DefKey, VmCaptureEnvironment>,
    budget: &mut ExecutionBudget,
) -> Result<bool, VmArtifactError> {
    // Explicit invocation continuations may start with result forwarding or
    // a CFG jump before reaching cleanup. The bounded proof below checks
    // every instruction; its first opcode is not an admission criterion.
    #[derive(Clone)]
    enum Value { Known(VmValue), Result }
    // Read untouched slots from the existing frame. Only proof writes need
    // scratch storage; copying every unused register would cost a whole new
    // frame per recycled call. Each new scratch entry is still charged.
    fn read(values: &BTreeMap<u32, Option<Value>>, registers: &[Option<VmValue>], register: u32) -> Option<Value> {
        values.get(&register).cloned().unwrap_or_else(|| registers[register as usize].clone().map(Value::Known))
    }
    fn write(values: &mut BTreeMap<u32, Option<Value>>, register: u32, value: Option<Value>, budget: &mut ExecutionBudget) -> Result<(), VmArtifactError> {
        if !values.contains_key(&register) { budget.reserve_allocation(1)?; }
        values.insert(register, value);
        Ok(())
    }
    let mut values = BTreeMap::new();
    write(&mut values, result, Some(Value::Result), budget)?;
    // A valid erasable path cannot revisit an instruction. This bound also
    // makes cyclic or malformed suffixes fail closed without an endless scan.
    for _ in 0..function.instructions.len() {
        budget.tick()?;
        let Some(instruction) = function.instructions.get(pc) else { return Ok(false); };
        match instruction {
            VmInstruction::Copy { dst, src } => {
                let value = read(&values, registers, *src);
                if value.is_none() { return Ok(false); }
                write(&mut values, *dst, value, budget)?;
            }
            VmInstruction::Move { dst, src } => {
                let value = read(&values, registers, *src);
                if value.is_none() { return Ok(false); }
                write(&mut values, *src, None, budget)?;
                write(&mut values, *dst, value, budget)?;
            }
            VmInstruction::DestroyCallable { dst, value } => {
                let Some(Value::Known(VmValue::Callable { callee, .. })) = read(&values, registers, *value)
                    else { return Ok(false); };
                if environments.get(&callee).is_some_and(|environment| environment.destructor.is_some()) {
                    return Ok(false);
                }
                write(&mut values, *value, None, budget)?;
                write(&mut values, *dst, Some(Value::Known(VmValue::Unit)), budget)?;
            }
            VmInstruction::IsInitialized { dst, base, fields } => {
                let value = read(&values, registers, *base);
                let value = match &value {
                    Some(Value::Known(value)) => Some(value),
                    None => None,
                    Some(Value::Result) => return Ok(false),
                };
                for _ in fields { budget.tick()?; }
                let initialized = storage_is_initialized(value, fields);
                write(&mut values, *dst, Some(Value::Known(VmValue::Bool(initialized))), budget)?;
            }
            VmInstruction::PatternTest {
                dst, subject, pattern: pattern @ VmPattern::Enum { fields, .. },
            } if fields.is_empty() => {
                let Some(Value::Known(value)) = read(&values, registers, *subject) else { return Ok(false); };
                // This optimization does not own the caller-reference
                // coordinate system. Let normal execution inspect those
                // borrowed subjects instead of speculating through them.
                if matches!(value, VmValue::Reference { .. }) { return Ok(false); }
                let matched = matches_runtime_pattern(&value, pattern, registers, &[], budget)?;
                write(&mut values, *dst, Some(Value::Known(VmValue::Bool(matched))), budget)?;
            }
            VmInstruction::BranchBool { condition, then_target, else_target } => {
                let Some(Value::Known(VmValue::Bool(condition))) = read(&values, registers, *condition)
                    else { return Ok(false); };
                pc = if condition { *then_target } else { *else_target } as usize;
                continue;
            }
            VmInstruction::Jump { target } => {
                pc = *target as usize;
                continue;
            }
            VmInstruction::Return { value } => {
                return Ok(matches!(read(&values, registers, *value), Some(Value::Result)));
            }
            _ => return Ok(false),
        }
        pc += 1;
    }
    Ok(false)
}

/// Execute compiler-selected frame obligations while retaining the original
/// caller path. A destructor's checked references must observe and update the
/// same owners as an ordinary call; freezing a private snapshot would sever
/// unique loans. The borrowed call prefix cannot become a return destination.
fn destroy_program_frame(
    program: &CandidateVmProgram,
    definition: DefKey,
    registers: &mut RuntimeRegisters,
    callers: &mut Vec<RuntimeProgramCaller>,
    transferred: Option<u32>,
    depth: u32,
    budget: &mut ExecutionBudget,
    host: &mut Option<&mut dyn VmHost>,
) -> Result<(), VmArtifactError> {
    destroy_program_frame_except(program, definition, registers, callers, transferred,
        None, depth, budget, host)
}

fn release_program_capture_loan(
    program: &CandidateVmProgram,
    definition: DefKey,
    registers: &mut RuntimeRegisters,
    callers: &mut Vec<RuntimeProgramCaller>,
    depth: u32,
    budget: &mut ExecutionBudget,
    host: &mut Option<&mut dyn VmHost>,
) -> Result<(), VmArtifactError> {
    let detached = registers.detached_captures.then(|| registers.capture_environment.clone()).flatten();
    registers.detached_captures = false;
    registers.release_capture_loan(budget)?;
    let Some(environment) = detached else { return Ok(()); };
    let Some(destructor) = program.callable_environments.get(&definition)
        .and_then(|environment| environment.destructor) else { return Ok(()); };
    budget.reserve_value("detached capture destruction arguments", environment.len())?;
    let arguments = environment.take().into_iter().map(|value|
        transfer_call_frame_value(&value, registers, callers, UniqueReferenceTransfer::IntoCallee))
        .collect::<Result<Vec<_>, _>>()?;
    budget.reserve_allocation(1)?;
    callers.push(RuntimeProgramCaller {
        definition, registers: std::mem::take(registers), pc: 0, return_destination: 0,
    });
    execute_program_profiled(program, destructor, &arguments, depth, budget, host,
        None, false, None, Some(callers))?;
    *registers = callers.pop().ok_or(VmArtifactError::HandlerStateMismatch)?.registers;
    Ok(())
}

fn destroy_program_frame_except(
    program: &CandidateVmProgram,
    definition: DefKey,
    registers: &mut RuntimeRegisters,
    callers: &mut Vec<RuntimeProgramCaller>,
    transferred: Option<u32>,
    shared: Option<&BTreeMap<u32, Option<u64>>>,
    depth: u32,
    budget: &mut ExecutionBudget,
    host: &mut Option<&mut dyn VmHost>,
) -> Result<(), VmArtifactError> {
    let function = program.functions.get(&definition)
        .ok_or(VmArtifactError::MissingFunction { definition })?;
    // Header placement and target ABIs were validated before execution.
    // Reading the plan must not perform an uncharged scan of the whole body.
    let actions = match function.instructions.get(1) {
        Some(VmInstruction::DeclareFrameCleanup { actions }) => actions.as_slice(),
        _ => &[],
    };
    for action in actions {
        budget.tick()?;
        if Some(action.owner) == transferred { continue; }
        if shared.is_some_and(|outer| replay::shared(registers, action.owner, outer)) { continue; }
        if !storage_is_initialized(registers.values[action.owner as usize].as_ref(), &[]) {
            continue;
        }
        let value = registers.values[action.owner as usize].take()
            .ok_or(VmArtifactError::UseAfterMove { register: action.owner })?;
        let value = match value {
            VmValue::Resident(home) => home.take(&[], budget)?,
            value => value,
        };
        let argument = transfer_call_frame_value(&value, registers, callers, UniqueReferenceTransfer::IntoCallee)?;
        budget.reserve_value("frame destruction arguments", 1)?;
        budget.reserve_allocation(1)?;
        callers.push(RuntimeProgramCaller {
            definition, registers: std::mem::take(registers), pc: 0, return_destination: 0,
        });
        execute_program_profiled(program, action.destructor, &[argument], depth, budget, host,
            None, false, None, Some(callers))?;
        *registers = callers.pop().ok_or(VmArtifactError::HandlerStateMismatch)?.registers;
    }
    if shared.is_none() {
        release_program_capture_loan(program, definition, registers, callers, depth, budget, host)?;
    }
    Ok(())
}

/// Abandon the retained branches of a discarded handler suffix before its
/// live call path is unwound. Suspended computations are not ordinary callers
/// of the clause currently executing, but still own their deeper frames.
fn abandon_program_handlers(
    program: &CandidateVmProgram,
    handlers: &mut Vec<RuntimeHandlerFrame>,
    retained_depth: usize,
    current: &mut RuntimeRegisters,
    current_callers: &mut [RuntimeProgramCaller],
    depth: u32,
    budget: &mut ExecutionBudget,
    host: &mut Option<&mut dyn VmHost>,
) -> Result<(), VmArtifactError> {
    if retained_depth > handlers.len() {
        return Err(VmArtifactError::HandlerStateMismatch);
    }
    while handlers.len() > retained_depth {
        budget.tick()?;
        let mut frame = handlers.pop().expect("checked handler suffix");
        if let Some(suspended) = frame.suspended.take() {
            abandon_program_continuation(program, suspended, frame.call_depth,
                (frame.owned_payloads && frame.continuation.is_replay()).then_some(frame.shared_registers),
                current, current_callers, depth, budget, host)?;
        }
    }
    Ok(())
}

/// Abandon only the call frames strictly inside the handler's owner. That
/// owner's source storage survives in the clause and is cleaned by its own
/// exit. The clause may itself have called a helper before transferring out.
/// Process retained inner branches and deeper frames before their callers so
/// a destructor never observes an already-ended ancestor loan.
fn abandon_program_continuation(
    program: &CandidateVmProgram,
    mut suspended: RuntimeContinuation,
    owner_depth: usize,
    replay_outer: Option<BTreeMap<u32, Option<u64>>>,
    current: &mut RuntimeRegisters,
    current_callers: &mut [RuntimeProgramCaller],
    depth: u32,
    budget: &mut ExecutionBudget,
    host: &mut Option<&mut dyn VmHost>,
) -> Result<(), VmArtifactError> {
    synchronize_saved_source_storage(&mut suspended.registers, suspended.program.as_mut(), current, current_callers);
    let saved = suspended.program.as_ref().ok_or(VmArtifactError::HandlerStateMismatch)?;
    if owner_depth > current_callers.len() || saved.callers.len() < owner_depth {
        return Err(VmArtifactError::HandlerStateMismatch);
    }
    // Explicit postorder traversal: deeply nested retained handlers must not
    // recurse on the Rust stack. Every visited edge and saved path is charged.
    budget.reserve_value("abandoned continuation paths", 1)?;
    budget.reserve_allocation(1)?;
    let mut pending = vec![(suspended, owner_depth, replay_outer)];
    while let Some((parent, _, _)) = pending.last_mut() {
        if let Some(mut frame) = parent.above.pop() {
            budget.tick()?;
            if let Some(mut child) = frame.suspended.take() {
                let parent_program = parent.program.as_ref().ok_or(VmArtifactError::HandlerStateMismatch)?;
                synchronize_saved_source_storage(&mut child.registers, child.program.as_mut(),
                    &parent.registers, &parent_program.callers);
                if frame.call_depth > parent_program.callers.len()
                    || child.program.as_ref().is_none_or(|saved| saved.callers.len() < frame.call_depth) {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                budget.reserve_value("abandoned continuation paths", pending.len() + 1)?;
                budget.reserve_allocation(1)?;
                pending.push((child, frame.call_depth,
                    (frame.owned_payloads && frame.continuation.is_replay()).then_some(frame.shared_registers)));
            }
            continue;
        }
        let (mut finished, owner_depth, replay_outer) = pending.pop().expect("checked pending path");
        let saved = finished.program.as_mut().ok_or(VmArtifactError::HandlerStateMismatch)?;
        while saved.callers.len() > owner_depth {
            budget.tick()?;
            destroy_program_frame(program, saved.definition, &mut finished.registers,
                &mut saved.callers, None, depth, budget, host)?;
            let caller = saved.callers.pop().ok_or(VmArtifactError::HandlerStateMismatch)?;
            saved.definition = caller.definition;
            finished.registers = caller.registers;
        }
        if let Some(outer) = &replay_outer {
            destroy_program_frame_except(program, saved.definition, &mut finished.registers,
                &mut saved.callers, None, Some(outer), depth, budget, host)?;
        }
        if let Some((parent, _, _)) = pending.last_mut() {
            let parent_program = parent.program.as_mut().ok_or(VmArtifactError::HandlerStateMismatch)?;
            synchronize_abandoned_source_storage(&finished.registers, &saved.callers,
                &mut parent.registers, &mut parent_program.callers);
        } else {
            synchronize_abandoned_source_storage(&finished.registers, &saved.callers,
                current, current_callers);
        }
    }
    Ok(())
}

fn synchronize_abandoned_source_storage(
    saved: &RuntimeRegisters,
    saved_callers: &[RuntimeProgramCaller],
    current: &mut RuntimeRegisters,
    current_callers: &mut [RuntimeProgramCaller],
) {
    // Propagate checked writes performed by cleanup through retained caller
    // loans. SSA temporaries stay private; source storage uses activation IDs.
    let owner_depth = saved_callers.len();
    if owner_depth == current_callers.len() {
        current.synchronize_source_storage(saved);
    } else {
        current_callers[owner_depth].registers.synchronize_source_storage(saved);
    }
    for (current, saved) in current_callers.iter_mut().zip(saved_callers) {
        current.registers.synchronize_source_storage(&saved.registers);
    }
}

fn execute_program_profiled(
    program: &CandidateVmProgram,
    definition: DefKey,
    arguments: &[VmValue],
    depth: u32,
    budget: &mut ExecutionBudget,
    host: &mut Option<&mut dyn VmHost>,
    profile: Option<&mut VmAuthoringProfile>,
    native_return: bool,
    capture_environment: Option<Arc<RuntimeCaptureEnvironment>>,
    borrowed_callers: Option<&mut Vec<RuntimeProgramCaller>>,
) -> Result<VmValue, VmArtifactError> {
    match execute_program_with_tail_boundary(program, definition, arguments, depth, budget, host,
        profile, native_return, capture_environment, borrowed_callers, None)? {
        RuntimeExecutionOutcome::Returned(value) => Ok(value),
        RuntimeExecutionOutcome::TailTransferred => Err(VmArtifactError::HandlerStateMismatch),
    }
}

/// Private, synchronous engine handoff. The recipient must move the verified
/// arguments into storage that survives this activation before accepting it.
/// No public import, serialized instruction, or ordinary call can install this.
trait RuntimeTailBoundary {
    fn transfer(&mut self, callee: DefKey, registers: &mut RuntimeRegisters,
        arguments: &[u32], budget: &mut ExecutionBudget) -> Result<bool, VmArtifactError>;
}

enum RuntimeExecutionOutcome {
    Returned(VmValue),
    TailTransferred,
}

fn execute_program_with_tail_boundary(
    program: &CandidateVmProgram,
    definition: DefKey,
    arguments: &[VmValue],
    depth: u32,
    budget: &mut ExecutionBudget,
    host: &mut Option<&mut dyn VmHost>,
    profile: Option<&mut VmAuthoringProfile>,
    native_return: bool,
    capture_environment: Option<Arc<RuntimeCaptureEnvironment>>,
    borrowed_callers: Option<&mut Vec<RuntimeProgramCaller>>,
    tail_boundary: Option<&mut dyn RuntimeTailBoundary>,
) -> Result<RuntimeExecutionOutcome, VmArtifactError> {
    float_env::with_profile(|| execute_program_in_float_profile(program, definition, arguments, depth,
        budget, host, profile, native_return, capture_environment, borrowed_callers, tail_boundary))
}

fn execute_program_in_float_profile(
    program: &CandidateVmProgram,
    definition: DefKey,
    arguments: &[VmValue],
    depth: u32,
    budget: &mut ExecutionBudget,
    host: &mut Option<&mut dyn VmHost>,
    mut profile: Option<&mut VmAuthoringProfile>,
    native_return: bool,
    capture_environment: Option<Arc<RuntimeCaptureEnvironment>>,
    mut borrowed_callers: Option<&mut Vec<RuntimeProgramCaller>>,
    mut tail_boundary: Option<&mut dyn RuntimeTailBoundary>,
) -> Result<RuntimeExecutionOutcome, VmArtifactError> {
    let return_floor = borrowed_callers.as_ref().map_or(0, |callers| callers.len());
    if depth.saturating_add(return_floor as u32) >= budget.limits.max_call_depth {
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
    budget.native_memory.install_program_layouts(program)?;
    let mut registers = RuntimeRegisters::for_function_with_native_return(function, budget, native_return)?;
    let mut next_storage_id = 0u64;
    for (index, value) in arguments.iter().enumerate() {
        registers.install_argument(index, value.clone());
    }
    if let Some(environment) = capture_environment { registers.install_captures(environment); }
    // The program engine deliberately keeps ordinary calls explicit rather
    // than recursively invoking a fresh interpreter. Handler frames are
    // dynamically scoped, so a `Perform` in any callee must be able to find
    // a frame installed by an ancestor. A continuation records this exact
    // call stack and restores it on `Resume`.
    let mut definition = definition;
    let mut callers = borrowed_callers.as_deref_mut().map(std::mem::take).unwrap_or_default();
    // One empty allocation per function, local to this execution. Keep map
    // entries stable so warm calls do not allocate/remove bookkeeping nodes.
    // Never retain homes, lexical brands, loans, or continuation state here.
    let mut spare_registers = BTreeMap::<DefKey, Option<Vec<Option<VmValue>>>>::new();
    let mut handlers = Vec::<RuntimeHandlerFrame>::new();
    let mut resumption_returns = Vec::<RuntimeResumptionReturn>::new();
    let mut next_handler_id = 0u64;
    let mut pc = 0usize;
    loop {
        registers.finish_native_writes(budget)?;
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
        registers.instruction_result(pc);
        let consumes_arguments = instruction.consumed_arguments().is_some();
        let owned_payloads = matches!(instruction, VmInstruction::PerformOwned { .. } | VmInstruction::InstallHandlerOwned { .. });
        let replay_owned = match instruction {
            VmInstruction::InstallHandlerOwned { replay_owned, .. } => replay_owned.as_slice(),
            _ => &[],
        };
        if handlers.last().is_some_and(|frame| frame.owned_payloads && frame.suspended.as_ref().is_some_and(|continuation| continuation.performed.payloads.is_some()))
            && !allowed_before_payload_claim(instruction) {
            return Err(VmArtifactError::HandlerStateMismatch);
        }
        let captured_call = returning_resumption_call(instruction, &registers)?;
        let resumption_index = captured_call.as_ref().map(|(_, id)| handlers.iter().rposition(|frame| frame.id == *id)
            .ok_or(VmArtifactError::HandlerResumeUnavailable)).transpose()?;
        let instruction = captured_call.as_ref().map_or(instruction, |(instruction, _)| instruction);
        match instruction {
            VmInstruction::DeclareResult { .. } | VmInstruction::DeclareFrameCleanup { .. } => {}
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
                    bytes: budget.native_memory.static_literal(function.definition, pc, bytes),
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
            instruction @ (VmInstruction::StoreUsize { .. } | VmInstruction::ArrayLen { .. } | VmInstruction::ArrayElementIsInitialized { .. } | VmInstruction::TakeArrayElement { .. }) => {
                execute_array_storage(&mut registers, function, instruction, budget)?
            }
            instruction @ (VmInstruction::ArrayGetBorrowShared { .. } | VmInstruction::ArrayEmpty { .. } | VmInstruction::ArrayPushMove { .. }) => {
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
            VmInstruction::MakeTupleOwned { dst, fields } | VmInstruction::MakeTuple { dst, fields } => {
                budget.reserve_value("tuple fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| registers.constructor_field(*dst, *field, budget))
                    .collect::<Result<Vec<_>, _>>()?;
                registers[*dst as usize] = Some(VmValue::Tuple(Arc::from(values)));
                if consumes_arguments { registers.finish_native_writes(budget)?; registers.retire_call_arguments(fields); }
            }
            VmInstruction::MakeArrayOwned { dst, fields, .. } | VmInstruction::MakeArray { dst, fields, .. } => {
                budget.reserve_value("array elements", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| registers.constructor_field(*dst, *field, budget))
                    .collect::<Result<Vec<_>, _>>()?;
                registers[*dst as usize] = Some(VmValue::Array {
                    values: Arc::from(values),
                });
                if consumes_arguments { registers.finish_native_writes(budget)?; registers.retire_call_arguments(fields); }
            }
            VmInstruction::MakeRecordOwned { dst, definition, fields, .. } | VmInstruction::MakeRecord {
                dst,
                definition,
                fields,
                ..
            } => {
                budget.reserve_value("record fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| registers.constructor_field(*dst, *field, budget))
                    .collect::<Result<Vec<_>, _>>()?;
                let signature = register_type(function, *dst)?;
                registers[*dst as usize] = Some(VmValue::Record {
                    definition: *definition,
                    fields: Arc::from(values),
                    signature,
                });
                if consumes_arguments { registers.finish_native_writes(budget)?; registers.retire_call_arguments(fields); }
            }
            VmInstruction::MakeEnumOwned { dst, definition, variant, fields, .. } | VmInstruction::MakeEnum {
                dst,
                definition,
                variant,
                fields,
                ..
            } => {
                budget.reserve_value("enum fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| registers.constructor_field(*dst, *field, budget))
                    .collect::<Result<Vec<_>, _>>()?;
                let signature = register_type(function, *dst)?;
                registers[*dst as usize] = Some(VmValue::Enum {
                    definition: *definition,
                    variant: *variant,
                    fields: Arc::from(values),
                    signature,
                });
                if consumes_arguments { registers.finish_native_writes(budget)?; registers.retire_call_arguments(fields); }
            }
            VmInstruction::IsInitialized { dst, base, fields } => {
                registers[*dst as usize] = Some(VmValue::Bool(storage_is_initialized(
                    registers[*base as usize].as_ref(), fields,
                )));
            }
            VmInstruction::DerefIsInitialized { dst, reference } => {
                let initialized = referent_is_initialized(&registers, &callers,
                    &registers.copy_value(*reference, budget)?)?;
                registers[*dst as usize] = Some(VmValue::Bool(initialized));
            }
            VmInstruction::TakeProjection { dst, base, fields } => {
                let expected = register_type(function, *dst)?;
                registers[*dst as usize] = Some(take_storage_projection(
                    &mut registers, *base, fields, &expected, budget,
                )?);
            }
            VmInstruction::ProjectRecord {
                dst,
                base,
                index,
                field_count,
                field_type,
            } => {
                if let Some(value) = project_native_home(registers[*base as usize].as_ref().expect("verified register"),
                    *index, *field_count, field_type, budget)? {
                    registers[*dst as usize] = Some(value); pc += 1; continue;
                }
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
                if let Some(value) = project_native_home(registers[*base as usize].as_ref().expect("verified register"),
                    *index, *field_count, &function.registers[*dst as usize], budget)? {
                    registers[*dst as usize] = Some(value); pc += 1; continue;
                }
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
                if let Some(value) = project_native_home(registers[*base as usize].as_ref().expect("verified register"),
                    *index, *field_count, &function.registers[*dst as usize], budget)? {
                    registers[*dst as usize] = Some(value); pc += 1; continue;
                }
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
                let base_value = registers.copy_value(*base, budget)?;
                let VmValue::Record {
                    definition,
                    fields,
                    signature,
                } = &base_value
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
                *field = registers.copy_value(*value, budget)?;
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
                registers[*dst as usize] = Some(VmValue::Bool(matches_runtime_pattern(
                    registers[*subject as usize]
                        .as_ref()
                        .expect("verified register"),
                    pattern, &registers, &callers, budget,
                )?));
            }
            VmInstruction::PerformOwned {
                dst,
                effect,
                effect_arguments,
                operation,
                arguments,
            }
            | VmInstruction::Perform {
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
                        registers.copy_value(*argument, budget)
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
                if handlers[index].owned_payloads != owned_payloads { return Err(VmArtifactError::HandlerStateMismatch); }
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
                if owned_payloads { registers.retire_call_arguments(arguments); }
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
                    registers.native_write(*destination);
                }
                handlers[index].suspended = Some(RuntimeContinuation {
                    target: pc + 1,
                    dst: *dst,
                    registers: saved,
                    performed: RuntimePerformed {
                        effect: *effect,
                        effect_arguments: effect_arguments.clone(),
                        operation: *operation,
                        payloads: Some(values),
                    },
                    above,
                    pending_leave: None,
                    remaining_replays: handlers[index].continuation.replay_uses().unwrap_or(0),
                    program: Some(continuation_program),
                });
                pc = handler_target as usize;
                continue;
            }
            VmInstruction::ClaimEffectPayloads { payloads } => {
                let frame = handlers.last_mut().ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                if !frame.owned_payloads || frame.payload_destinations != *payloads {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                frame.suspended.as_mut().and_then(|continuation| continuation.performed.payloads.take())
                    .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
            }
            VmInstruction::InstallHandlerOwned {
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                continuation,
                target,
                ..
            }
            | VmInstruction::InstallHandler {
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
                    owned_payloads,
                    shared_registers: replay::shared_registers(&registers, owned_payloads && continuation.is_replay(), replay_owned, budget)?,
                    suspended: None,
                });
            }
            VmInstruction::CompleteHandler { value } => {
                let frame = handlers.last().ok_or(VmArtifactError::HandlerStackUnderflow)?;
                if frame.suspended.is_some() || frame.call_depth != callers.len() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                if resumption_returns.last().is_some_and(|pending| {
                    pending.handler_id == frame.id
                }) {
                    let result = registers.copy_value(*value, budget)?;
                    let mut pending = resumption_returns.pop().expect("checked pending resumption");
                    synchronize_saved_source_storage(&mut pending.registers, pending.program.as_mut(), &registers, &callers);
                    let saved_program = pending.program.ok_or(VmArtifactError::HandlerStateMismatch)?;
                    let expected = register_type(
                        program.functions.get(&saved_program.definition).ok_or(VmArtifactError::MissingFunction { definition: saved_program.definition })?,
                        pending.dst,
                    )?;
                    expect_type(function, *value, expected)?;
                    definition = saved_program.definition;
                    callers = saved_program.callers;
                    registers = pending.registers;
                    registers[pending.dst as usize] = Some(result);
                    registers.native_write(pending.dst);
                    handlers = pending.handlers;
                    pc = pending.pc;
                    continue;
                }
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
                let resumed = registers.copy_value(*value, budget)?;
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
                if frame.owned_payloads {
                    registers.retire_call_arguments(&[*value]);
                }
                let RuntimeContinuation {
                    target,
                    dst,
                    registers: mut saved_registers,
                    above,
                    pending_leave,
                    mut program,
                    ..
                } = continuation;
                synchronize_saved_source_storage(&mut saved_registers, program.as_mut(), &registers, &callers);
                if let Some(program) = program {
                    definition = program.definition;
                    callers = program.callers;
                }
                if let Some(leave) = pending_leave {
                    registers = saved_registers;
                    handlers.extend(above);
                    pc = complete_pending_leave(&mut registers, &mut handlers, leave, budget)?;
                    continue;
                }
                registers = saved_registers;
                registers[dst as usize] = Some(resumed);
                registers.native_write(dst);
                handlers.extend(above);
                pc = target;
                continue;
            }
            VmInstruction::ResumeReturn { dst, value } => {
                let resumed = registers.copy_value(*value, budget)?;
                let index = resumption_index.or_else(|| handlers.len().checked_sub(1))
                    .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                let Some(frame) = handlers.get_mut(index) else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.continuation == VmContinuationPolicy::Terminal {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let replaying = frame.continuation.is_replay();
                let continuation = if replaying {
                    if frame.owned_payloads {
                        frame.suspended.as_ref().map(|saved| replay::fork(saved, frame.call_depth,
                            &frame.shared_registers, &mut next_storage_id, budget)).transpose()?
                    } else { frame.suspended.clone() }
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
                if frame.owned_payloads || consumes_arguments {
                    registers.retire_call_arguments(&[*value]);
                }
                let RuntimeContinuation {
                    target,
                    dst: continuation_dst,
                    registers: mut saved_registers,
                    above,
                    pending_leave,
                    mut program,
                    ..
                } = continuation;
                synchronize_saved_source_storage(&mut saved_registers, program.as_mut(), &registers, &callers);
                if pending_leave.is_some() {
                    return Err(VmArtifactError::HandlerStateMismatch);
                }
                let mut active_handlers = handlers[..index].to_vec();
                active_handlers.extend_from_slice(&handlers[index + 1..]);
                active_handlers.push(handlers[index].clone());
                let resumed_handler_ids = active_handlers
                    .iter()
                    .map(|frame| frame.id)
                    .chain(above.iter().map(|frame| frame.id))
                    .collect();
                let mut return_handlers = handlers.clone();
                if replaying {
                    return_handlers
                        .get_mut(index)
                        .and_then(|frame| frame.suspended.as_mut())
                        .expect("checked suspended replay handler")
                        .remaining_replays -= 1;
                }
                resumption_returns.push(RuntimeResumptionReturn {
                    pc: pc + 1,
                    dst: *dst,
                    handler_id: handlers[index].id,
                    registers: registers.clone(),
                    handlers: return_handlers,
                    program: Some(RuntimeProgramContinuation {
                        definition,
                        callers: callers.clone(),
                    }),
                    resumed_handler_ids,
                });
                handlers = active_handlers;
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
                registers.native_write(continuation_dst);
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
                let resumed = registers.copy_value(*value, budget)?;
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
                    VmContinuationPolicy::Consume | VmContinuationPolicy::Replay { .. } => {
                        handlers[index].suspended.take()
                    }
                    VmContinuationPolicy::Terminal => {
                        return Err(VmArtifactError::HandlerResumeUnavailable);
                    }
                }
                .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                // See the standalone-artifact interpreter above: an explicit
                // snapshot abandons dynamically newer frames before restoring
                // the continuation's original deep-frame suffix.
                abandon_program_handlers(program, &mut handlers, index + 1,
                    &mut registers, &mut callers, depth, budget, host)?;
                let resumed = transfer_to_resumed_frame(
                    resumed, &registers, &callers, handlers[index].call_depth,
                    continuation.program.as_ref().map(|program| program.callers.len()).unwrap_or(callers.len()),
                    budget,
                )?;
                if handlers[index].owned_payloads {
                    registers.retire_call_arguments(&[*value]);
                }
                let RuntimeContinuation {
                    target,
                    dst,
                    registers: mut saved_registers,
                    above,
                    pending_leave,
                    mut program,
                    ..
                } = continuation;
                synchronize_saved_source_storage(&mut saved_registers, program.as_mut(), &registers, &callers);
                if let Some(program) = program {
                    definition = program.definition;
                    callers = program.callers;
                }
                if let Some(leave) = pending_leave {
                    registers = saved_registers;
                    handlers.extend(above);
                    pc = complete_pending_leave(&mut registers, &mut handlers, leave, budget)?;
                    continue;
                }
                registers = saved_registers;
                registers[dst as usize] = Some(resumed);
                registers.native_write(dst);
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
                let payloads = continuation.performed.payloads.as_ref().ok_or(VmArtifactError::HandlerResumeUnavailable)?;
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
                if handlers[index].owned_payloads != declined.owned_payloads { return Err(VmArtifactError::HandlerStateMismatch); }
                let mut crossed = handlers.split_off(index + 1);
                crossed.push(declined);
                crossed.extend(continuation.above.clone());
                let owner_depth = handlers[index].call_depth;
                let payload_destinations = handlers[index].payload_destinations.clone();
                let handler_target = handlers[index].target;
                if payload_destinations.len() != payloads.len() {
                    return Err(VmArtifactError::CallArity {
                        expected: payload_destinations.len() as u32,
                        found: payloads.len() as u32,
                    });
                }
                budget.reserve_allocation(continuation.registers.len())?;
                let continuation_program = continuation.program.clone();
                let original_callers = continuation_program.as_ref()
                    .map(|program| program.callers.as_slice()).unwrap_or(&[]);
                budget.reserve_value("forwarded clause payload", payloads.len())?;
                let clause_values = payloads.iter().cloned().map(|value| {
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
                    registers.native_write(*destination);
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
                let Some(mut frame) = handlers.pop() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                let suspended = frame.suspended.take().ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                abandon_program_continuation(program, suspended, frame.call_depth,
                    (frame.owned_payloads && frame.continuation.is_replay()).then_some(frame.shared_registers),
                    &mut registers, &mut callers, depth, budget, host)?;
                if frame.continuation == VmContinuationPolicy::Terminal {
                    resumption_returns.clear();
                }
            }
            VmInstruction::Copy { dst, src } => {
                registers.copy_into(*dst, *src, budget)?;
            }
            VmInstruction::StorageLive { local, .. } => {
                if registers[*local as usize].is_some() {
                    return Err(VmArtifactError::ReadBeforeWrite { register: *local });
                }
                next_storage_id = next_storage_id.checked_add(1).ok_or(VmArtifactError::HandlerStateMismatch)?;
                registers.source_storage.insert(*local, next_storage_id);
            }
            VmInstruction::StorageDead { local, .. } => {
                if registers[*local as usize].is_some() {
                    return Err(VmArtifactError::ReadBeforeWrite { register: *local });
                }
                registers.source_storage.remove(local);
                if let Some(home) = registers.native_homes.remove(local) { home.retire(); }
            }
            VmInstruction::SetDropFlag { flag, value } => {
                registers[*flag as usize] = Some(VmValue::Bool(*value))
            }
            VmInstruction::DestroyIf { local, flag } => {
                match registers[*flag as usize].as_ref() {
                    Some(VmValue::Bool(_)) => {}
                    _ => return Err(VmArtifactError::ReadBeforeWrite { register: *flag }),
                }
                registers.clear_value(*local);
            }
            VmInstruction::Store { dst, src } => {
                registers.copy_into(*dst, *src, budget)?;
            }
            VmInstruction::StoreOwned { dst, src } => {
                registers.move_into(*dst, *src, budget)?;
            }
            VmInstruction::Move { dst, src } => {
                registers.move_into(*dst, *src, budget)?;
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
                let carrier = if *reborrow { registers.copy_value(*src, budget)? }
                    else { registers[*src as usize].as_ref().expect("verified register").clone() };
                registers[*dst as usize] = Some(borrow_value(
                    &registers,
                    &callers,
                    *src,
                    &carrier,
                    fields,
                    *unique,
                    *reborrow,
                    referent,
                )?);
            }
            VmInstruction::DerefCopy { dst, reference } => {
                let carrier = registers.copy_value(*reference, budget)?;
                let VmValue::Reference { target, fields, .. } = &carrier
                else {
                    return Err(VmArtifactError::InvalidRegister {
                        register: *reference,
                    });
                };
                if matches!(target, ReferenceTarget::Home(_) | ReferenceTarget::Native(_))
                    && let Some((result, index)) = registers.read_projection(pc)
                {
                    let mut path = fields.to_vec(); path.push(index);
                    budget.tick()?;
                    registers[result as usize] = Some(load_reference_target(&registers, &callers, target, &path, budget)?);
                    registers.native_write(result);
                    pc += 2; continue;
                }
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
                    ReferenceTarget::Register(_) | ReferenceTarget::Captured(_) | ReferenceTarget::Native(_) | ReferenceTarget::Home(_) => value,
                };
                registers[*dst as usize] = Some(value);
            }
            VmInstruction::DerefMove { dst, reference } => {
                let carrier = registers.copy_value(*reference, budget)?;
                let VmValue::Reference { target, fields, .. } = &carrier
                else {
                    return Err(VmArtifactError::InvalidRegister { register: *reference });
                };
                let value = take_reference_target(&mut registers, &mut callers, target, fields, budget)?;
                let value = match target {
                    ReferenceTarget::Caller { caller_depth, .. } => {
                        rebase_caller_references(value, *caller_depth)?
                    }
                    ReferenceTarget::Register(_) | ReferenceTarget::Captured(_) | ReferenceTarget::Native(_) | ReferenceTarget::Home(_) => value,
                };
                registers[*dst as usize] = Some(value);
                registers[*reference as usize] = Some(VmValue::SuspendedReference(Box::new(carrier)));
            }
            VmInstruction::DerefStore { reference, src } => {
                registers[*reference as usize] = registers[*reference as usize].take().map(|capability| match capability {
                    VmValue::SuspendedReference(reference) => *reference,
                    reference => reference,
                });
                let carrier = registers.copy_value(*reference, budget)?;
                registers.native_write(*reference);
                let VmValue::Reference {
                    target,
                    fields,
                    unique: true,
                    ..
                } = &carrier
                else {
                    return Err(VmArtifactError::InvalidRegister {
                        register: *reference,
                    });
                };
                let (target, fields) = (target.clone(), fields.clone());
                let mut replacement = registers.copy_value(*src, budget)?;
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
            VmInstruction::HostCallOwned { dst, capability, symbol, arguments, .. }
            | VmInstruction::HostCall {
                dst,
                capability,
                symbol,
                arguments,
                ..
            } => {
                if let Some(imports) = budget.native_memory.imports.clone() {
                    let current_depth = depth.saturating_add(callers.len() as u32).saturating_add(1);
                    registers[*dst as usize] = Some(native_bridge::execute(
                        program, imports, capability, symbol, &mut registers, arguments, *dst, budget, current_depth, consumes_arguments,
                    )?);
                    pc += 1;
                    continue;
                }
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
                if consumes_arguments { registers.retire_call_arguments(arguments); }
            }
            VmInstruction::TailCallOwned { callee, arguments } => {
                // Enclosing callers' handlers keep their original depth.
                // Only a delimiter owned by the ending activation is illegal.
                if handlers.iter().any(|handler| handler.call_depth >= callers.len())
                    || registers.capture_environment.is_some()
                    || resumption_returns.last().is_some_and(|pending|
                        pending.program.as_ref().is_some_and(|saved|
                            saved.definition == definition && saved.callers.len() == callers.len())) {
                    return Err(VmArtifactError::HandlerStillActive);
                }
                let target = program.functions.get(callee)
                    .ok_or(VmArtifactError::MissingFunction { definition: *callee })?;
                require_execution_contract(target, budget)?;
                // Only the boundary activation can be handed back. Surviving
                // ordinary VM callers keep their frames and result destinations.
                // The normal verified tail checks above remain authoritative.
                if callers.is_empty() && return_floor == 0
                    && let Some(boundary) = tail_boundary.as_deref_mut()
                    && boundary.transfer(*callee, &mut registers, arguments, budget)? {
                    registers.retire_call_arguments(arguments);
                    return Ok(RuntimeExecutionOutcome::TailTransferred);
                }
                budget.reserve_value("mandatory tail arguments", arguments.len())?;
                let values = arguments.iter().map(|argument| registers.copy_value(*argument, budget))
                    .collect::<Result<Vec<_>, _>>()?;
                let native_return = registers.native_plan.as_ref().is_some_and(|plan| plan.native_return);
                budget.reserve_allocation(target.registers.len())?;
                let mut incoming = RuntimeRegisters::for_function_with_native_return(target, budget, native_return)?;
                for (index, value) in values.into_iter().enumerate() { incoming.install_argument(index, value); }
                incoming.finish_native_writes(budget)?;
                // No rebasing into a deeper caller index, no saved registers,
                // and no RuntimeProgramCaller push: the destination remains
                // exactly the destination inherited by this activation.
                registers = incoming;
                definition = *callee;
                if let Some(profile) = profile.as_deref_mut() { profile.recycled_tail_calls += 1; }
                pc = 0;
                continue;
            }
            VmInstruction::CallOwned { dst, callee, arguments }
            | VmInstruction::Call {
                dst,
                callee,
                arguments,
            } => {
                budget.reserve_value("call arguments", arguments.len())?;
                if *callee == definition
                    && handlers.is_empty()
                    && resumption_returns.is_empty()
                    && let Some(profile) = profile.as_deref_mut()
                    && registers.capture_environment.is_none()
                    && (tail_return_suffix(&function.instructions[pc + 1..], *dst, budget)?
                        || tail_cleanup_suffix(function, pc + 1, *dst, &registers, &program.callable_environments, budget)?)
                    && recyclable_tail_arguments(&registers, &registers.native_homes, arguments, &callers, budget, profile)?
                {
                    // Clone only the small argument vector before clearing
                    // registers; aggregate contents retain their Arc backing.
                    // Do not run the ordinary call rebasing here: no frame
                    // is pushed, so surviving caller loans must not move.
                    // No source-visible storage destructor is skipped: the
                    // verified suffix only forwards call_result and may
                    // inspect already-vacant frame-local cleanup slots.
                    let values: Vec<_> = arguments.iter().map(|argument| {
                        registers[*argument as usize].clone()
                    }).collect();
                    registers.fill(None);
                    registers.source_storage.clear();
                    for home in registers.native_homes.values() { home.clear(&[]); }
                    registers.pending_native.clear();
                    for (index, value) in values.into_iter().enumerate() {
                        registers[index] = value;
                        registers.native_write(index as u32);
                    }
                    profile.recycled_tail_calls += 1;
                    pc = 0;
                    continue;
                }
                let callee_function = program.functions.get(callee)
                    .ok_or(VmArtifactError::MissingFunction { definition: *callee })?;
                let native_return = registers.wants_native(*dst);
                let callee_plan = if native_return { budget.native_memory.native_return_plan(callee_function) }
                    else { budget.native_memory.storage_plan(callee_function) };
                let values = arguments
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        // Native parameters still receive their own home. Carry
                        // resident bytes to that copy without first rebuilding
                        // every aggregate field as a temporary VM value.
                        (if callee_plan.layouts[index].is_some() {
                            registers[*argument as usize].clone()
                                .ok_or(VmArtifactError::UseAfterMove { register: *argument })
                        } else { registers.copy_value(*argument, budget) })
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
                let callee_values = if let Some(profile) = profile.as_deref_mut()
                    && let Some(values) = spare_registers.get_mut(callee).and_then(Option::take) {
                    profile.reused_call_register_buffers += 1;
                    values
                } else {
                    budget.reserve_allocation(callee_function.registers.len())?;
                    vec![None; callee_function.registers.len()]
                };
                let mut incoming = RuntimeRegisters::with_values(callee_function, budget, native_return, callee_values)?;
                for (index, value) in values.into_iter().enumerate() {
                    incoming[index] = Some(value);
                }
                if consumes_arguments {
                    incoming.finish_native_writes(budget)?;
                    registers.retire_call_arguments(arguments);
                }
                callers.push(RuntimeProgramCaller {
                    definition,
                    registers: std::mem::take(&mut registers),
                    pc,
                    return_destination: *dst,
                });
                definition = *callee;
                registers = incoming;
                pc = 0;
                continue;
            }
            VmInstruction::DestroyCallable { dst, value } => {
                let callable = registers.values[*value as usize].take()
                    .ok_or(VmArtifactError::UseAfterMove { register: *value })?;
                let callable = match callable {
                    VmValue::Resident(home) => home.take(&[], budget)?, value => value,
                };
                let (callee, captures) = match callable {
                    VmValue::Callable { callee, captures, .. } => (callee, captures),
                    // Labels and resumptions expose a callable source ABI,
                    // but carry only a capability into the control engine.
                    // Disposing the token owns no capture environment and
                    // must not repeat an already checked Cancel/Leave.
                    VmValue::Label { .. } | VmValue::Resumption { .. } => {
                        registers[*dst as usize] = Some(VmValue::Unit);
                        pc += 1;
                        continue;
                    }
                    _ => return Err(VmArtifactError::NotCallable { register: *value }),
                };
                let destructor = program.callable_environments.get(&callee)
                    .and_then(|environment| environment.destructor);
                captures.live.set(false);
                let Some(callee) = destructor else {
                    captures.take();
                    registers[*dst as usize] = Some(VmValue::Unit);
                    pc += 1;
                    continue;
                };
                budget.reserve_value("callable destruction arguments", captures.len())?;
                let values = captures.take();
                let callee_function = program.functions.get(&callee)
                    .ok_or(VmArtifactError::MissingFunction { definition: callee })?;
                if depth.saturating_add(callers.len() as u32).saturating_add(1)
                    >= budget.limits.max_call_depth {
                    return Err(VmArtifactError::CallDepthLimit { limit: budget.limits.max_call_depth });
                }
                budget.reserve_allocation(callee_function.registers.len())?;
                callers.push(RuntimeProgramCaller {
                    definition,
                    registers: std::mem::take(&mut registers),
                    pc,
                    return_destination: *dst,
                });
                definition = callee;
                registers = RuntimeRegisters::for_function(callee_function, budget)?;
                for (index, value) in values.into_iter().enumerate() {
                    registers.install_argument(index, value);
                }
                pc = 0;
                continue;
            }
            VmInstruction::MakeCallable {
                dst,
                callee,
                captures,
                environment,
            } => {
                budget.reserve_value("callable captures", captures.len())?;
                budget.reserve_allocation(captures.len())?;
                let ownership = (0..captures.len()).map(|index| environment.as_ref().is_some_and(|environment|
                    matches!(environment.captures[index].mode, VmCaptureMode::Copy | VmCaptureMode::Move)))
                    .collect::<Vec<_>>();
                let values = captures
                    .iter()
                    .enumerate()
                    .map(|(index, capture)| {
                        let value = if ownership[index] {
                            registers.values[*capture as usize].take()
                                .ok_or(VmArtifactError::UseAfterMove { register: *capture })?
                        } else {
                            registers.values[*capture as usize].clone()
                                .ok_or(VmArtifactError::UseAfterMove { register: *capture })?
                        };
                        freeze_frame_value(&value, &registers, &callers)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let signature = register_type(function, *dst)?;
                registers[*dst as usize] = Some(VmValue::Callable {
                    callee: *callee,
                    captures: RuntimeCaptureEnvironment::with_ownership(values, ownership),
                    signature,
                });
            }
            VmInstruction::MakeLabel {
                dst,
                brand_owner: _,
                brand_label,
                target,
                destination,
            } => {
                let signature = register_type(function, *dst)?;
                registers[*dst as usize] = Some(VmValue::Label {
                    // The lexical brand names the source definition; its
                    // specialized runtime frame can have a different key.
                    owner: definition,
                    label: *brand_label,
                    target: *target,
                    destination: *destination,
                    call_depth: callers.len(),
                    handler_depth: handlers.len(),
                    signature,
                });
            }
            VmInstruction::CallIndirectOwned { dst, callee, arguments }
            | VmInstruction::CallIndirect {
                dst,
                callee,
                arguments,
            } => {
                let callee_value = registers[*callee as usize]
                    .as_ref()
                    .expect("verified register")
                    .clone();
                // This is a receiver loan, not a source-level Copy. Loading
                // it must preserve the exact Arc-backed capture environment
                // so unique invocations observe prior capture mutations.
                // A captured reference can itself occupy a native home.
                // Resolve that carrier before following its receiver loan.
                let callee_value = match callee_value {
                    VmValue::Resident(home) => home.load(&[], budget)?,
                    value => value,
                };
                let callee_value = match callee_value {
                    VmValue::Reference { target, fields, .. } => {
                        let value = load_reference_target(&registers, &callers, &target, &fields, budget)?;
                        let value = match value {
                            VmValue::Resident(home) => home.load(&[], budget)?,
                            value => value,
                        };
                        if !matches!(value, VmValue::Callable { .. }) {
                            return Err(VmArtifactError::NotCallable { register: *callee });
                        }
                        value
                    }
                    value => value,
                };
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
                    let destination_owner = if call_depth == callers.len() { Some(definition) }
                        else { callers.get(call_depth).map(|caller| caller.definition) };
                    if call_depth < return_floor || destination_owner != Some(owner) {
                        return Err(VmArtifactError::HandlerStateMismatch);
                    }
                    let payload = transfer_to_ancestor_frame(registers.copy_value(*argument, budget)?,
                        &registers, &callers, call_depth, budget)?;
                    if consumes_arguments { registers.retire_call_arguments(arguments); }
                    abandon_program_handlers(program, &mut handlers, handler_depth,
                        &mut registers, &mut callers, depth, budget, host)?;
                    let mut transferred = Some(*argument);
                    while callers.len() > call_depth {
                        destroy_program_frame(program, definition, &mut registers, &mut callers,
                            transferred, depth, budget, host)?;
                        transferred = None;
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
                    registers.native_write(destination);
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
                let callee_function = program.functions.get(&callee)
                    .ok_or(VmArtifactError::MissingFunction { definition: callee })?;
                let native_return = registers.wants_native(*dst);
                let callee_plan = if native_return { budget.native_memory.native_return_plan(callee_function) }
                    else { budget.native_memory.storage_plan(callee_function) };
                let mut values = captures.lend_to_invocation();
                values.extend(
                    arguments
                        .iter()
                        .enumerate()
                        .map(|(index, argument)| {
                            let value = if callee_plan.layouts[captures.len() + index].is_some() {
                                registers[*argument as usize].clone()
                                    .ok_or(VmArtifactError::UseAfterMove { register: *argument })?
                            } else { registers.copy_value(*argument, budget)? };
                            transfer_call_frame_value(
                                &value,
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
                let callee_values = if let Some(profile) = profile.as_deref_mut()
                    && let Some(values) = spare_registers.get_mut(&callee).and_then(Option::take) {
                    profile.reused_call_register_buffers += 1;
                    values
                } else {
                    budget.reserve_allocation(callee_function.registers.len())?;
                    vec![None; callee_function.registers.len()]
                };
                let mut incoming = RuntimeRegisters::with_values(callee_function, budget, native_return, callee_values)?;
                for (index, value) in values.into_iter().enumerate() {
                    incoming[index] = Some(value);
                }
                incoming.install_captures(captures);
                if consumes_arguments {
                    incoming.finish_native_writes(budget)?;
                    registers.retire_call_arguments(arguments);
                }
                callers.push(RuntimeProgramCaller {
                    definition,
                    registers: std::mem::take(&mut registers),
                    pc,
                    return_destination: *dst,
                });
                definition = callee;
                registers = incoming;
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
                abandon_program_handlers(program, &mut handlers, *handler_depth as usize,
                    &mut registers, &mut callers, depth, budget, host)?;
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
                    budget,
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
                let value = if registers.native_plan.as_ref().is_some_and(|plan| plan.native_return) {
                    registers[*value as usize].clone().ok_or(VmArtifactError::UseAfterMove { register: *value })?
                } else { registers.copy_value(*value, budget)? };
                // A root handler's delimiter can be the current function's
                // return, even when that function has ordinary callers. Do
                // not replay those callers' suffixes before returning to the
                // clause. This is not an exit from the owning frame, so its
                // capture loan remains installed until its actual return.
                if let Some(return_to_clause) = resumption_returns.last()
                    && (callers.len() == return_floor
                        || return_to_clause.program.as_ref().is_some_and(|saved|
                            saved.definition == definition && saved.callers.len() == callers.len())) {
                    if handlers.iter().any(|handler|
                        !return_to_clause.resumed_handler_ids.contains(&handler.id)) {
                        return Err(VmArtifactError::HandlerStillActive);
                    }
                    let mut return_to_clause = resumption_returns.pop()
                        .expect("checked clause-return frame exists");
                    synchronize_saved_source_storage(&mut return_to_clause.registers,
                        return_to_clause.program.as_mut(), &registers, &callers);
                    if let Some(program) = return_to_clause.program {
                        definition = program.definition;
                        callers = program.callers;
                    }
                    registers = return_to_clause.registers;
                    registers[return_to_clause.dst as usize] = Some(value);
                    registers.native_write(return_to_clause.dst);
                    handlers = return_to_clause.handlers;
                    pc = return_to_clause.pc;
                    continue;
                }
                release_program_capture_loan(program, definition, &mut registers, &mut callers, depth, budget, host)?;
                if callers.len() > return_floor {
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
                    if profile.is_some() {
                        // The returned value has already been transferred out.
                        // Clear every slot before pooling only its Vec backing;
                        // replacing the frame below releases all other state.
                        let mut values = std::mem::take(&mut registers.values);
                        values.fill(None);
                        spare_registers.entry(definition).or_default().get_or_insert(values);
                    }
                    definition = caller.definition;
                    registers = caller.registers;
                    registers[caller.return_destination as usize] = Some(value);
                    registers.native_write(caller.return_destination);
                    pc = caller.pc + 1;
                    continue;
                }
                if !handlers.is_empty() {
                    return Err(VmArtifactError::HandlerStillActive);
                }
                if let Some(borrowed) = borrowed_callers.as_deref_mut() {
                    *borrowed = callers;
                }
                return Ok(RuntimeExecutionOutcome::Returned(value));
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
    float_env::with_profile(|| execute_host_call_in_float_profile(host, capability, symbol, arguments))
}

fn execute_host_call_in_float_profile(
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
    #[test]
    fn vm_identity_rejects_proof_local_universal_regions() {
        let value = super::VmGenericArgument::Lifetime(crate::Lifetime::Placeholder(crate::types::UniversalRegion {
            universe: 1, index: 0,
        }));
        assert!(super::validate_vm_generic_arguments(&[value]).is_err());
    }
    #[test]
    fn return_reachability_includes_dynamic_handler_entries() {
        use super::*;
        let install = VmInstruction::InstallHandler {
            effect: DefKey(Digest::of_bytes(b"returning-terminal-handler")),
            effect_arguments: vec![],
            operation: 0,
            payload_destinations: vec![],
            resume_type: VmType::Unit,
            continuation: VmContinuationPolicy::Terminal,
            target: 2,
        };
        for install in [install.clone(), install.with_owned_effect_payloads()] {
            assert_eq!(reachable_return_values(&[
                install,
                VmInstruction::Trap,
                VmInstruction::Return { value: 0 },
            ]), [0]);
        }
        assert!(reachable_return_values(&[
            VmInstruction::Trap,
            VmInstruction::Return { value: 0 },
        ]).is_empty(), "a trap must not reach a syntactically later return");
        assert_eq!(reachable_return_values(&[
            VmInstruction::Cancel,
            VmInstruction::Return { value: 0 },
        ]), [0], "cancellation continues the clause after abandoning its snapshot");
    }

    #[test]
    fn resumption_storage_sync_preserves_allocations_not_register_spellings() {
        use super::*;
        let mut saved = RuntimeRegisters {
            values: vec![Some(VmValue::I64(1)), Some(VmValue::I64(2)), Some(VmValue::I64(3)), None],
            source_storage: BTreeMap::from([(0, 10), (1, 11), (3, 13)]),
            ..Default::default()
        };
        let mut current = RuntimeRegisters {
            values: vec![Some(VmValue::I64(42)), Some(VmValue::I64(99)), Some(VmValue::I64(100)), Some(VmValue::I64(7))],
            source_storage: BTreeMap::from([(0, 10), (1, 99), (3, 13)]),
            ..Default::default()
        };
        saved.synchronize_source_storage(&current);
        assert!(matches!(saved[0], Some(VmValue::I64(42))));
        assert!(matches!(saved[1], Some(VmValue::I64(2))), "a fresh allocation must not overwrite the captured one");
        assert!(matches!(saved[2], Some(VmValue::I64(3))), "SSA temporaries belong to their saved execution");
        assert!(matches!(saved[3], Some(VmValue::I64(7))), "initialization is shared even when the old slot was empty");
        current[0] = None;
        saved.synchronize_source_storage(&current);
        assert!(saved[0].is_none(), "a moved resident must not be revived by restoration");
    }

    #[test]
    fn partial_enum_layout_allows_tag_inspection_but_not_reading_a_hole() {
        use super::*;
        let definition = DefKey(Digest::of_bytes(b"partial-enum-pattern"));
        let value = VmValue::Enum {
            definition,
            signature: VmType::Nominal { definition, arguments: vec![] },
            variant: 0,
            fields: vec![VmValue::Uninitialized(VmType::I64), VmValue::I64(42)].into(),
        };
        let tag = VmPattern::Enum {
            definition, variant: 0, field_types: vec![VmType::I64, VmType::I64],
            field_count: 2, fields: vec![],
        };
        assert!(matches_pattern(&value, &tag));
        let VmPattern::Enum { definition, variant, field_types, field_count, .. } = tag else { unreachable!() };
        let hole = VmPattern::Enum { definition, variant, field_types, field_count,
            fields: vec![VmPatternField { index: 0, ty: VmType::I64, pattern: VmPattern::Any }],
        };
        assert!(!matches_pattern(&value, &hole));
        assert!(!aggregate_matches_layout(&[VmValue::Uninitialized(VmType::Bool)], &[VmType::I64]));
    }
    use super::*;
    use crate::{MirBlock, MirScopeId, PrimitiveRole};

    fn cow_budget() -> ExecutionBudget {
        ExecutionBudget { native_memory: NativeMemory::default(), unsafe_execution: false, limits: VmExecutionLimits::default(), instructions: 0, allocated_elements: 0 }
    }

    #[test]
    fn moving_through_a_register_reference_clears_the_shared_source_path() {
        let mut registers = vec![Some(VmValue::Tuple(vec![VmValue::I64(42), VmValue::Unit].into()))];
        let mut budget = cow_budget();
        let target = ReferenceTarget::Register(0);
        let alias = VmValue::Reference { target: target.clone(), fields: vec![0].into(),
            unique: true, referent: VmType::I64 };
        assert!(matches!(take_reference_target(&mut registers, &mut [], &target, &[0], &mut budget).unwrap(), VmValue::I64(42)));
        assert!(!referent_is_initialized(&registers, &[], &alias).unwrap());
        assert!(take_reference_target(&mut registers, &mut [], &target, &[0], &mut budget).is_err());
        assert!(storage_is_initialized(registers[0].as_ref(), &[1]));
        store_reference_target(&mut registers, &mut [], &target, &[0], VmValue::I64(19), &mut budget).unwrap();
        assert!(referent_is_initialized(&registers, &[], &alias).unwrap());
        assert!(matches!(load_reference_target(&registers, &[], &target, &[0], &mut budget).unwrap(), VmValue::I64(19)));
    }

    #[test]
    fn taking_fixed_array_storage_checks_concrete_extent_and_clears_only_that_path() {
        for (element, values) in [
            (VmType::I64, vec![VmValue::I64(20), VmValue::I64(22)]),
            (VmType::U8, vec![]),
            (VmType::Unit, vec![VmValue::Unit, VmValue::Unit]),
        ] {
            let array = VmType::FixedArray {
                element: Box::new(element), length: values.len() as u64,
            };
            let value = VmValue::Tuple(vec![
                VmValue::Array { values: values.into() }, VmValue::I64(42),
            ].into());
            for resident in [false, true] {
                let mut budget = cow_budget();
                let value = if resident {
                    let layout = native_memory::native_layout(
                        &VmType::Tuple(vec![array.clone(), VmType::I64]), &Arc::from([]), &mut vec![],
                    ).unwrap();
                    let home = native_storage::NativeHome::new(Arc::new(layout), &mut budget).unwrap();
                    home.store(&[], &value, &mut budget).unwrap();
                    VmValue::Resident(home)
                } else { value.clone() };
                let mut registers = vec![Some(value)];
                let moved = take_storage_projection(&mut registers, 0, &[0], &array, &mut budget).unwrap();
                assert!(value_matches_vm_type(&moved, &array));
                assert!(!storage_is_initialized(registers[0].as_ref(), &[0]));
                assert!(storage_is_initialized(registers[0].as_ref(), &[1]));
                assert!(take_storage_projection(&mut registers, 0, &[0], &array, &mut budget).is_err());
            }
        }
        for expected in [
            VmType::FixedArray { element: Box::new(VmType::I64), length: 3 },
            VmType::FixedArray { element: Box::new(VmType::Bool), length: 2 },
        ] {
            let mut registers = vec![Some(VmValue::Array {
                values: vec![VmValue::I64(20), VmValue::I64(22)].into(),
            })];
            assert!(matches!(take_storage_projection(&mut registers, 0, &[], &expected, &mut cow_budget()),
                Err(VmArtifactError::ResultType { .. })));
            assert!(storage_is_initialized(registers[0].as_ref(), &[]));
        }
    }

    #[test]
    fn capture_loans_transfer_authority_and_return_only_residual_slots() {
        let environment = RuntimeCaptureEnvironment::new(vec![VmValue::Tuple(
            vec![VmValue::I64(11), VmValue::I64(22)].into(),
        )]);
        let mut budget = cow_budget();
        let values = environment.lend_to_invocation();
        assert!(!storage_is_initialized(environment.values.borrow().first(), &[]));
        let mut registers = RuntimeRegisters {
            values: values.into_iter().map(Some).collect(), ..RuntimeRegisters::default()
        };
        registers.install_captures(environment.clone());
        let moved = take_storage_projection(&mut registers, 0, &[0], &VmType::I64, &mut budget).unwrap();
        assert!(matches!(moved, VmValue::I64(11)));
        registers.release_capture_loan(&mut budget).unwrap();
        assert!(registers.values[0].is_none());
        assert!(!storage_is_initialized(environment.values.borrow().first(), &[0]));
        assert!(storage_is_initialized(environment.values.borrow().first(), &[1]));
        // Releasing an already-ended frame loan cannot republish stale slots.
        registers.release_capture_loan(&mut budget).unwrap();
        assert!(storage_is_initialized(environment.values.borrow().first(), &[1]));
    }

    fn cow_owner() -> VmValue {
        VmValue::Tuple(Arc::from([VmValue::Array {
            values: (0..128).map(VmValue::I64).collect::<Vec<_>>().into(),
        }]))
    }

    fn cow_backing(owner: &VmValue) -> (*const VmValue, *const VmValue) {
        let VmValue::Tuple(fields) = owner else { panic!("tuple owner") };
        let VmValue::Array { values } = &fields[0] else { panic!("array field") };
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
    fn array_cow_never_upgrades_shared_or_captured_borrow_authority() {
        let mut registers = vec![Some(cow_owner())];
        for reference in [
            VmValue::Reference { target: ReferenceTarget::Register(0), fields: Arc::from([0]),
                unique: false, referent: VmType::Array(Box::new(VmType::I64)) },
            VmValue::Reference { target: ReferenceTarget::Captured(Arc::new(cow_owner())), fields: Arc::from([0]),
                unique: true, referent: VmType::Array(Box::new(VmType::I64)) },
        ] {
            assert!(matches!(replace_referenced_array(&mut registers, &mut [], &reference, vec![], &mut cow_budget()),
                Err(VmArtifactError::UnsupportedEscapingUniqueReference)));
        }
    }

    #[test]
    fn resumption_product_cleanup_relocates_nested_holes_without_reviving_them() {
        let signature = VmType::Callable { shared_receiver: false, unique_receiver: false,
            safety: Safety::Safe, parameters: vec![VmType::I64], result: Box::new(VmType::I64),
            effects: Box::default() };
        let inner = VmType::Tuple(vec![signature.clone(), VmType::I64]);
        let mut registers = vec![Some(VmValue::Tuple(vec![VmValue::Tuple(vec![
            VmValue::Resumption { frame: 3, signature: signature.clone() }, VmValue::I64(42),
        ].into())].into()))];
        let mut budget = cow_budget();
        let token = take_storage_projection(&mut registers, 0, &[0, 0], &signature, &mut budget).unwrap();
        assert!(matches!(token, VmValue::Resumption { frame: 3, .. }));
        let partial = take_storage_projection(&mut registers, 0, &[0], &inner, &mut budget).unwrap();
        assert!(!storage_is_initialized(registers[0].as_ref(), &[0]));
        assert!(!value_matches_vm_type(&partial, &inner));
        assert!(aggregate_matches_layout(&[partial.clone()], &[inner.clone()]));
        assert!(!aggregate_matches_layout(&[partial.clone()], &[VmType::Tuple(vec![VmType::Unit, VmType::I64])]));
        registers.push(Some(partial));
        assert!(!storage_is_initialized(registers[1].as_ref(), &[0]));
        assert!(storage_is_initialized(registers[1].as_ref(), &[1]));
        assert!(matches!(take_storage_projection(&mut registers, 1, &[0], &signature, &mut budget),
            Err(VmArtifactError::UseAfterMove { .. })));
        assert!(matches!(take_storage_projection(&mut registers, 1, &[1], &VmType::I64, &mut budget).unwrap(), VmValue::I64(42)));
        assert!(matches!(take_storage_projection(&mut registers, 0, &[0], &inner, &mut budget),
            Err(VmArtifactError::UseAfterMove { .. })));
    }

    #[test]
    fn resumption_value_layout_checks_the_retained_callable_contract() {
        let signature = VmType::Callable { shared_receiver: false, unique_receiver: false,
            safety: Safety::Safe, parameters: vec![VmType::I64], result: Box::new(VmType::I64),
            effects: Box::default() };
        let value = VmValue::Resumption { frame: 3, signature: signature.clone() };
        assert!(value_matches_vm_type(&value, &signature));
        let mut wrong = signature.clone();
        let VmType::Callable { parameters, .. } = &mut wrong else { unreachable!() };
        *parameters = vec![VmType::Unit];
        assert!(!value_matches_vm_type(&value, &wrong));
        let tuple = VmValue::Tuple(Arc::from([value]));
        assert!(value_matches_vm_type(&tuple, &VmType::Tuple(vec![signature])));
        assert!(!value_matches_vm_type(&tuple, &VmType::Tuple(vec![wrong])));
    }

    #[test]
    fn borrowing_empty_projected_arrays_preserves_verified_element_types() {
        let bytes = VmType::Array(Box::new(VmType::U8));
        let empty = VmValue::Array { values: Arc::from([]),  };
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
        let nested = VmValue::Array { values: Arc::from([empty]),  };
        let nested_layout = VmType::Array(Box::new(bytes.clone()));
        assert_eq!(borrowed_value_type(&nested, &nested_layout), nested_layout);

        // Existing residents are not retyped to fit a forged destination, and
        // shared loans still cannot be upgraded to unique loans.
        let units = VmValue::Array { values: Arc::from([VmValue::Unit]),  };
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
    fn authoring_cleanup_suffix_proves_only_vacant_paths_and_preserves_the_unknown_result() {
        let definition = DefKey(Digest::of_bytes(b"tail-cleanup-proof"));
        let mut function = VmFunction {
            definition, safety: Safety::Safe, unsafe_execution: false,
            nominal_copy_descriptors: vec![], captures: 0, parameters: 0,
            registers: vec![VmType::I64, VmType::I64, VmType::Bool, VmType::I64],
            instructions: vec![
                VmInstruction::IsInitialized { dst: 2, base: 1, fields: vec![] },
                VmInstruction::BranchBool { condition: 2, then_target: 2, else_target: 3 },
                VmInstruction::Call { dst: 3, callee: definition, arguments: vec![1] },
                VmInstruction::Move { dst: 3, src: 0 },
                VmInstruction::Return { value: 3 },
            ],
        };
        let empty = [None, None, None, None];
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(), unsafe_execution: false,
            limits: VmExecutionLimits::default(), instructions: 0, allocated_elements: 0,
        };
        let environments = BTreeMap::new();
        assert!(tail_cleanup_suffix(&function, 0, 0, &empty, &environments, &mut budget).unwrap());
        assert_eq!(budget.allocated_elements, 3);
        let live = [None, Some(VmValue::I64(42)), None, None];
        assert!(!tail_cleanup_suffix(&function, 0, 0, &live, &environments, &mut budget).unwrap());
        function.instructions[0] = VmInstruction::IsInitialized { dst: 2, base: 0, fields: vec![] };
        assert!(!tail_cleanup_suffix(&function, 0, 0, &empty, &environments, &mut budget).unwrap(),
            "the call result is unknown, not its old register content");
        function.instructions[0] = VmInstruction::IsInitialized { dst: 2, base: 1, fields: vec![] };
        function.instructions[3] = VmInstruction::Jump { target: 0 };
        assert!(!tail_cleanup_suffix(&function, 0, 0, &empty, &environments, &mut budget).unwrap(),
            "an endless cleanup cycle is not a return suffix");
        function.instructions[3] = VmInstruction::Move { dst: 3, src: 0 };
        function.instructions[4] = VmInstruction::Return { value: 1 };
        assert!(!tail_cleanup_suffix(&function, 0, 0, &live, &environments, &mut budget).unwrap());
        budget.limits.max_allocation_elements = budget.allocated_elements;
        assert!(matches!(tail_cleanup_suffix(&function, 0, 0, &empty, &environments, &mut budget),
            Err(VmArtifactError::AllocationLimit { .. })));
        budget.limits.max_allocation_elements = u64::MAX;
        budget.limits.max_instructions = budget.instructions;
        assert!(matches!(tail_cleanup_suffix(&function, 0, 0, &empty, &environments, &mut budget),
            Err(VmArtifactError::InstructionLimit { .. })));
    }

    #[test]
    fn authoring_tail_cleanup_never_erases_registered_capture_destruction() {
        let callee = DefKey(Digest::of_bytes(b"tail-callable-cleanup"));
        let signature = VmType::Callable { shared_receiver: false, unique_receiver: false,
            safety: Safety::Safe, parameters: vec![], result: Box::new(VmType::I64),
            effects: Box::default(),
        };
        let function = VmFunction {
            definition: callee, safety: Safety::Safe, unsafe_execution: false,
            nominal_copy_descriptors: vec![], captures: 0, parameters: 0,
            registers: vec![VmType::I64, signature.clone(), VmType::Bool, VmType::Unit],
            instructions: vec![
                VmInstruction::IsInitialized { dst: 2, base: 1, fields: vec![] },
                VmInstruction::BranchBool { condition: 2, then_target: 2, else_target: 3 },
                VmInstruction::DestroyCallable { dst: 3, value: 1 },
                VmInstruction::Return { value: 0 },
            ],
        };
        let registers = [None, Some(VmValue::Callable {
            callee, captures: RuntimeCaptureEnvironment::new(vec![]), signature,
        }), None, None];
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(), unsafe_execution: false,
            limits: VmExecutionLimits::default(), instructions: 0, allocated_elements: 0,
        };
        let mut environments = BTreeMap::new();
        assert!(tail_cleanup_suffix(&function, 0, 0, &registers, &environments, &mut budget).unwrap());
        environments.insert(callee, VmCaptureEnvironment {
            owner: callee, callable: 0, instance: None, captures: vec![],
            destructor: Some(crate::mir::callable_environment_destructor_definition(callee)),
        });
        assert!(!tail_cleanup_suffix(&function, 0, 0, &registers, &environments, &mut budget).unwrap());
        assert!(matches!(&registers[1], Some(VmValue::Callable { .. })), "proof inspection cannot consume the live closure");
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
                captures: RuntimeCaptureEnvironment::new(vec![VmValue::Tuple(Arc::from([capability]))]),
                signature: VmType::Unit,
            })];
            let mut budget = ExecutionBudget {
                native_memory: NativeMemory::default(),
                unsafe_execution: false,
                limits: VmExecutionLimits::default(), instructions: 0, allocated_elements: 0,
            };
            let mut profile = VmAuthoringProfile::default();
            assert!(!recyclable_tail_arguments(&registers, &BTreeMap::new(), &[0], &[], &mut budget, &mut profile).unwrap());
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
                    captures: RuntimeCaptureEnvironment::new(vec![VmValue::Tuple(Arc::from([VmValue::Reference {
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
                assert_eq!(recyclable_tail_arguments(&registers, &BTreeMap::new(), &[0], &callers, &mut budget, &mut profile).unwrap(),
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
            assert!(!recyclable_tail_arguments(&registers, &BTreeMap::new(), &[0], &[], &mut budget, &mut profile).unwrap());
            assert_eq!(profile.inspected_tail_argument_elements, 3);
        }
    }

    fn tail_caller(value: VmValue) -> RuntimeProgramCaller {
        RuntimeProgramCaller {
            definition: DefKey(Digest::of_bytes(b"tail-owner")),
            registers: RuntimeRegisters { values: vec![None, Some(value)], ..Default::default() }, pc: 0, return_destination: 0,
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
                callee: definition, captures: RuntimeCaptureEnvironment::new(vec![VmValue::Tuple(Arc::from([capability]))]),
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
            assert!(!recyclable_tail_arguments(&registers, &BTreeMap::new(), &[0], &callers, &mut budget, &mut profile).unwrap());
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
        assert!(matches!(recyclable_tail_arguments(&registers, &BTreeMap::new(), &[0], &[], &mut budget, &mut VmAuthoringProfile::default()),
            Err(VmArtifactError::InstructionLimit { limit: 0 })));
        budget.limits.max_instructions = 100;
        budget.limits.max_allocation_elements = 0;
        budget.allocated_elements = 0;
        assert!(matches!(recyclable_tail_arguments(&registers, &BTreeMap::new(), &[0], &[], &mut budget, &mut VmAuthoringProfile::default()),
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
        let schedule = parallel_edge_transfers(&[MirLocal(0), MirLocal(1)], &target.parameters);

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
        let schedule = parallel_edge_transfers(&[MirLocal(1), MirLocal(2), MirLocal(0)], &target.parameters);

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
