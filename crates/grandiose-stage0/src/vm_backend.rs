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
    core::{CallableId, CaptureMode, EnvironmentBrand},
    identity::{DefKey, Digest},
    mir::{
        MirContinuationPolicy, MirFunction, MirInstruction, MirLocal, MirPattern, MirPatternField,
        MirProgram, MirTerminator, canonical_f64_bits, is_canonical_f64_bits,
        lifted_callable_definition, parse_char_literal, parse_f64_literal, parse_text_literal,
    },
    source::{TokenKind, exact_scalar_literal_kind},
    types::{
        ConstKind, EffectTail, GenericArgument, Lifetime, ScalarType, StructuralU32Expr, Type,
    },
};

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
    Tuple(Vec<VmType>),
    Nominal {
        definition: DefKey,
        arguments: Vec<VmType>,
    },
    Callable {
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
}

/// Source-free capture authority carried by a verified callable value.  It is
/// deliberately distinct from the runtime reference representation: this is
/// the sealed compile-time layout contract that an independently decoded VM
/// artifact checks before it can construct the value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VmCaptureMode {
    SharedBorrow,
    UniqueBorrow,
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
    ConstUnit {
        dst: u32,
    },
    ConstI64 {
        dst: u32,
        value: i64,
    },
    ConstF64 {
        dst: u32,
        bits: u64,
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
    /// Exact manifest-bound i64 bitwise-xor. This remains distinct from all
    /// source arithmetic in the frozen bytecode contract.
    BitXorI64 {
        dst: u32,
        left: u32,
        right: u32,
    },
    /// Exact manifest-bound i64 right shift with a u32 count masked modulo
    /// 64. This remains distinct from checked source arithmetic.
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
    /// Exact manifest-bound i64 left shift with a u32 wrapping count.
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
/// It deliberately contains only structural place text and indices—not MIR
/// locals, Core arena IDs, or host pointers—so a decoded artifact can verify
/// the same proof without compiler-session state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmCleanupProof {
    pub moved_places: Vec<VmCleanupPlace>,
    pub active_loans: Vec<VmCleanupLoan>,
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
    target: u32,
    arguments: Vec<u32>,
    destinations: Vec<u32>,
    cleanup: VmCleanupProof,
}
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct VmCleanupPlace {
    pub root: String,
    pub fields: Vec<u32>,
}
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct VmCleanupLoan {
    pub owner: Option<String>,
    pub root: String,
    pub fields: Vec<u32>,
    pub unique: bool,
}
impl VmCleanupProof {
    pub fn from_mir(plan: &crate::MirCleanupPlan) -> Self {
        debug_assert!(plan.validate().is_ok());
        let moved_places = plan
            .moved_places
            .iter()
            .map(|place| VmCleanupPlace {
                root: place.root.clone(),
                fields: place.fields.clone(),
            })
            .collect::<Vec<_>>();
        let active_loans = plan
            .active_loans
            .iter()
            .map(|loan| VmCleanupLoan {
                owner: loan.owner.clone(),
                root: loan.root.clone(),
                fields: loan.fields.clone(),
                unique: loan.unique,
            })
            .collect::<Vec<_>>();
        Self {
            moved_places,
            active_loans,
        }
    }
    pub fn validate(&self) -> bool {
        if self.moved_places.iter().any(|place| place.root.is_empty())
            || self.active_loans.iter().any(|loan| loan.root.is_empty())
            || !self.moved_places.windows(2).all(|pair| pair[0] < pair[1])
            || !self.active_loans.windows(2).all(|pair| pair[0] < pair[1])
        {
            return false;
        }
        if self.moved_places.iter().enumerate().any(|(index, place)| {
            self.moved_places[index + 1..].iter().any(|other| {
                place.root == other.root
                    && (place.fields.starts_with(&other.fields)
                        || other.fields.starts_with(&place.fields))
            })
        }) {
            return false;
        }
        !self.moved_places.iter().any(|moved| {
            self.active_loans.iter().any(|loan| {
                moved.root == loan.root
                    && (moved.fields.starts_with(&loan.fields)
                        || loan.fields.starts_with(&moved.fields))
            })
        })
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmNominalCopyDescriptor {
    pub definition: DefKey,
    pub arguments: Vec<VmType>,
    pub variants: Vec<Vec<VmType>>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmFunction {
    pub definition: DefKey,
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
    /// Stage 0 can rebase shared references into frame-independent callable
    /// captures, but must not snapshot a unique reference and lose write-back.
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
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct VmExecutionLimits {
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
impl Default for VmExecutionLimits {
    fn default() -> Self {
        Self {
            max_call_depth: 4_096,
            max_handler_depth: 4_096,
            max_retained_continuations: 4_096,
            max_instructions: 10_000_000,
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
/// Schema 59 adds opcode 118 for manifest-bound checked i64-to-usize
/// conversion, rejecting negative values deterministically. Schema 58 adds
/// opcode 117 for manifest-bound wrapping i64-to-u32
/// conversion, retaining the low two's-complement bits. Schema 57 adds opcode
/// 116 for manifest-bound checked i64-to-u32 conversion. Schema 56 adds opcode
/// 114 for manifest-bound i64 left shift with a u32
/// count and wrapping count semantics. Schema 55 adds opcode 115 for manifest-bound i64 right shift with a u32
/// count and wrapping count semantics. Schema 54 adds opcode 113 for
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
/// manifest-bound generic i64 equality leaf, whose public ABI returns a
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
pub const STAGE0_VM_SCHEMA: u32 = 59;
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
    pub fn fingerprint(&self) -> Digest {
        self.artifact.fingerprint
    }
    pub fn runtime_manifest(&self) -> Option<Digest> {
        self.artifact.runtime_manifest
    }
    fn execute_with_limits(&self, limits: VmExecutionLimits) -> Result<VmValue, VmArtifactError> {
        let mut budget = ExecutionBudget {
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
    pub fn run_bool(&self) -> Result<bool, VmArtifactError> {
        expect_bool(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_char(&self) -> Result<char, VmArtifactError> {
        expect_char(self.execute_with_limits(VmExecutionLimits::default())?)
    }
    pub fn run_text(&self) -> Result<String, VmArtifactError> {
        Ok(expect_text(self.execute_with_limits(VmExecutionLimits::default())?)?.to_string())
    }
}
impl VerifiedVmProgram {
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
    pub fn runtime_manifest(&self) -> Option<Digest> {
        self.program.runtime_manifest
    }
    pub fn run_i64(&self) -> Result<i64, VmArtifactError> {
        self.run_i64_with_limits(VmExecutionLimits::default())
    }
    pub fn run_usize(&self) -> Result<u64, VmArtifactError> {
        let mut budget = ExecutionBudget {
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
    pub fn run_tuple_i64(&self) -> Result<Vec<i64>, VmArtifactError> {
        let mut budget = ExecutionBudget {
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
    pub fn run_i64_with_limits(&self, limits: VmExecutionLimits) -> Result<i64, VmArtifactError> {
        let mut budget = ExecutionBudget {
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
    pub fn run_bool(&self) -> Result<bool, VmArtifactError> {
        self.run_bool_with_limits(VmExecutionLimits::default())
    }
    pub fn run_bool_with_limits(&self, limits: VmExecutionLimits) -> Result<bool, VmArtifactError> {
        let mut budget = ExecutionBudget {
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
    if function.validate().is_err()
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
    let mut next = 0u32;
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
    for block in &function.blocks {
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
            } => {
                let target = *starts
                    .get(target.0 as usize)
                    .ok_or(VmArtifactError::UnsupportedControlFlow)?;
                instructions.push(VmInstruction::Leave {
                    brand_owner: brand.owner,
                    brand_label: brand.label,
                    target,
                    arguments: arguments.iter().map(|argument| argument.0).collect(),
                    destinations: function.blocks[target_index(target, &starts)?]
                        .parameters
                        .iter()
                        .map(|parameter| parameter.0)
                        .collect(),
                    cleanup: VmCleanupProof::from_mir(cleanup),
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
    let function = VmFunction {
        nominal_copy_descriptors: function
            .nominal_copy_descriptors
            .iter()
            .map(vm_nominal_copy_descriptor)
            .collect::<Result<Vec<_>, _>>()?,
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
fn edge_length(arguments: &[MirLocal], target: &crate::mir::MirBlock) -> u32 {
    let transfers = arguments
        .iter()
        .zip(&target.parameters)
        .filter(|(argument, parameter)| argument != parameter)
        .count();
    transfers as u32 * 2 + 1
}
fn target_index(target: u32, starts: &[u32]) -> Result<usize, VmArtifactError> {
    starts
        .iter()
        .position(|start| *start == target)
        .ok_or(VmArtifactError::UnsupportedControlFlow)
}
/// Materialize a CFG edge through fresh temporaries. Identity transfers are
/// omitted; every remaining argument is read before any destination is
/// written, preserving the MIR's parallel edge-argument semantics for swaps
/// and other cycles.
fn emit_edge(
    arguments: &[MirLocal],
    target: &crate::mir::MirBlock,
    destination: u32,
    registers: &mut Vec<VmType>,
    instructions: &mut Vec<VmInstruction>,
) {
    let mut temporaries = Vec::with_capacity(arguments.len());
    for (argument, parameter) in arguments.iter().zip(&target.parameters) {
        if argument == parameter {
            continue;
        }
        let temporary = registers.len() as u32;
        registers.push(registers[argument.0 as usize].clone());
        instructions.push(VmInstruction::Copy {
            dst: temporary,
            src: argument.0,
        });
        temporaries.push((temporary, *parameter));
    }
    for (temporary, parameter) in temporaries {
        instructions.push(VmInstruction::Copy {
            dst: parameter.0,
            src: temporary,
        });
    }
    instructions.push(VmInstruction::Jump {
        target: destination,
    });
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
    program
        .validate()
        .map_err(|_| VmArtifactError::MissingFunction {
            definition: program.entry,
        })?;
    let functions = program
        .functions
        .iter()
        .map(|(definition, function)| Ok((*definition, emit(function)?.function)))
        .collect::<Result<BTreeMap<_, _>, VmArtifactError>>()?;
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
        definition: descriptor.definition,
        arguments: descriptor
            .arguments
            .iter()
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
                .map(vm_nominal_argument)
                .collect::<Result<Vec<_>, _>>()?,
        }),
        Type::Callable {
            parameters,
            result,
            effects,
            ..
        } => Ok(VmType::Callable {
            parameters: parameters
                .iter()
                .map(vm_type)
                .collect::<Result<Vec<_>, _>>()?,
            result: Box::new(vm_type(result)?),
            effects: Box::new(vm_effect_row(effects)?),
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
        VmType::F64 => 2,
        VmType::Bool => 3,
        VmType::Char => 4,
        VmType::Text => 5,
        VmType::Bytes => 18,
        VmType::Generic(_) => 9,
        VmType::Array(_) => 10,
        VmType::Callable { .. } => 6,
        VmType::Tuple(_) => 7,
        VmType::Nominal { .. } => 8,
        VmType::Reference { .. } => 11,
        VmType::ConstU32(_) => 12,
        VmType::ConstU32Expr(_) => 13,
        VmType::ConstQuantity { .. } => 14,
        VmType::ConstGeneric { .. } => 15,
    });
    match value {
        VmType::Callable {
            parameters,
            result,
            effects,
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
            output.extend_from_slice(&(value.captures.len() as u64).to_le_bytes());
            for capture in &value.captures {
                output.push(match capture.mode {
                    VmCaptureMode::SharedBorrow => 0,
                    VmCaptureMode::UniqueBorrow => 1,
                    VmCaptureMode::Move => 2,
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
    let mut bytes = b"grandiose-stage0-vm-v22".to_vec();
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
    let mut bytes = b"grandiose-stage0-vm-program-v23".to_vec();
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
    output.extend_from_slice(&function.captures.to_le_bytes());
    output.extend_from_slice(&function.parameters.to_le_bytes());
    output.extend_from_slice(&(function.registers.len() as u64).to_le_bytes());
    for register in &function.registers {
        encode_type(register, output);
    }
    output.extend_from_slice(&(function.nominal_copy_descriptors.len() as u64).to_le_bytes());
    for descriptor in &function.nominal_copy_descriptors {
        output.extend_from_slice(&descriptor.definition.0.as_bytes());
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
    fn u32(&mut self) -> Result<u32, VmArtifactError> {
        Ok(u32::from_le_bytes(self.bytes(4)?.try_into().unwrap()))
    }
    fn u64(&mut self) -> Result<u64, VmArtifactError> {
        Ok(u64::from_le_bytes(self.bytes(8)?.try_into().unwrap()))
    }
    fn i64(&mut self) -> Result<i64, VmArtifactError> {
        Ok(i64::from_le_bytes(self.bytes(8)?.try_into().unwrap()))
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
                let count = self.count("callable environment captures", MAX_DECODE_REGISTERS)?;
                let mut captures = Vec::with_capacity(count);
                for _ in 0..count {
                    let mode = match self.byte()? {
                        0 => VmCaptureMode::SharedBorrow,
                        1 => VmCaptureMode::UniqueBorrow,
                        2 => VmCaptureMode::Move,
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
            2 => Ok(VmType::F64),
            3 => Ok(VmType::Bool),
            4 => Ok(VmType::Char),
            5 => Ok(VmType::Text),
            18 => Ok(VmType::Bytes),
            6 => {
                let count = self.count("callable parameters", MAX_DECODE_REGISTERS)?;
                let mut parameters = Vec::with_capacity(count);
                for _ in 0..count {
                    parameters.push(self.vm_type_at_depth(depth + 1)?);
                }
                Ok(VmType::Callable {
                    parameters,
                    result: Box::new(self.vm_type_at_depth(depth + 1)?),
                    effects: Box::new(self.vm_effect_row_at_depth(depth + 1)?),
                })
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
            let root = self.text()?;
            let field_count = self.count("cleanup moved place fields", MAX_DECODE_REGISTERS)?;
            let mut fields = Vec::with_capacity(field_count);
            for _ in 0..field_count {
                fields.push(self.u32()?);
            }
            moved_places.push(VmCleanupPlace { root, fields });
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
                root,
                fields,
                unique,
            });
        }
        Ok(VmCleanupProof {
            moved_places,
            active_loans,
        })
    }
    fn function(&mut self) -> Result<VmFunction, VmArtifactError> {
        let definition = self.def_key()?;
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
            1 => {
                let (dst, src) = self.register_pair()?;
                Ok(VmInstruction::Copy { dst, src })
            }
            2 => {
                let (dst, src) = self.register_pair()?;
                Ok(VmInstruction::Move { dst, src })
            }
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
    let declared = program
        .host_capabilities
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    if declared.len() != program.host_capabilities.len()
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
        let Some(target) = program.functions.get(callee) else {
            return Err(VmArtifactError::MissingFunction {
                definition: *callee,
            });
        };
        if *callee
            != lifted_callable_definition(EnvironmentBrand {
                owner: environment.owner,
                callable: CallableId(environment.callable),
            })
        {
            return Err(VmArtifactError::InvalidCallableEnvironment {
                message: "callable environment registry brand does not match lifted target",
            });
        }
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
                let expected = instantiate_vm_type(&return_type(target)?, &generic_bindings);
                let found = register_type(function, *dst)?;
                if expected != found {
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
                        let expected_callee = lifted_callable_definition(EnvironmentBrand {
                            owner: environment.owner,
                            callable: CallableId(environment.callable),
                        });
                        if *callee != expected_callee {
                            return Err(VmArtifactError::InvalidCallableEnvironment {
                                message: "callable environment brand does not match lifted target",
                            });
                        }
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
                    parameters, result, ..
                } = register_type(function, *dst)?
                else {
                    return Err(VmArtifactError::NotCallable { register: *dst });
                };
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
                let expected = instantiate_vm_type(&return_type(target)?, &generic_bindings);
                if expected != *result {
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
            parameters: expected_parameters,
            result: expected_result,
            effects: expected_effects,
        } => match found {
            VmType::Callable {
                parameters: found_parameters,
                result: found_result,
                effects: found_effects,
            } if expected_parameters.len() == found_parameters.len() => {
                expected_parameters
                    .iter()
                    .zip(found_parameters)
                    .all(|(expected, found)| unify_call_type(expected, found, bindings))
                    && unify_call_type(expected_result, found_result, bindings)
                    && unify_vm_effect_row(expected_effects, found_effects, bindings)
            }
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
            parameters,
            result,
            effects,
        } => VmType::Callable {
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
        MirInstruction::ConstF64 { dst, bits } => VmInstruction::ConstF64 {
            dst: dst.0,
            bits: *bits,
        },
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
        MirInstruction::CaptureResumption { dst } => {
            VmInstruction::CaptureResumption { dst: dst.0 }
        }
        MirInstruction::Resume { value } => VmInstruction::Resume { value: value.0 },
        MirInstruction::ResumeReturn { dst, value } => VmInstruction::ResumeReturn {
            dst: dst.0,
            value: value.0,
        },
        MirInstruction::ResumeSnapshot { snapshot, value } => VmInstruction::ResumeSnapshot {
            snapshot: snapshot.0,
            value: value.0,
        },
        MirInstruction::Forward => VmInstruction::Forward,
        MirInstruction::Cancel => VmInstruction::Cancel,
        MirInstruction::Copy { dst, src } => VmInstruction::Copy {
            dst: dst.0,
            src: src.0,
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
                        captures: environment
                            .captures
                            .iter()
                            .map(|capture| {
                                Ok(VmCapture {
                                    mode: match capture.mode {
                                        CaptureMode::SharedBorrow => VmCaptureMode::SharedBorrow,
                                        CaptureMode::UniqueBorrow => VmCaptureMode::UniqueBorrow,
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
    snapshots: Vec<Option<u32>>,
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
    /// Provenance for first-class continuation values. `Some(frame)` means
    /// this register was produced by `CaptureResumption` for that exact live
    /// frame. The type system still sees a callable; this parallel proof fact
    /// is what prevents capability forgery through an equally typed callable.
    snapshots: Vec<Option<u32>>,
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
        let VmInstruction::Leave {
            brand_owner,
            brand_label,
            target,
            destinations,
            ..
        } = instruction
        else {
            continue;
        };
        if *target as usize >= function.instructions.len() {
            return Err(VmArtifactError::InvalidInstructionTarget { target: *target });
        }
        let layout = destinations
            .iter()
            .map(|destination| register_type(function, *destination))
            .collect::<Result<Vec<_>, _>>()?;
        let contract = (*target, destinations.clone(), layout);
        match contracts.get(&(*brand_owner, *brand_label)) {
            Some(previous) if previous != &contract => {
                return Err(VmArtifactError::InvalidLabelContract {
                    message: "label brand has contradictory destination or payload layout",
                });
            }
            Some(_) => {}
            None => {
                contracts.insert((*brand_owner, *brand_label), contract);
            }
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
    let mut incoming = vec![None; function.instructions.len()];
    if let Some(entry) = incoming.first_mut() {
        *entry = Some(VerifierState {
            registers: initial,
            snapshots: vec![None; function.registers.len()],
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
    while let Some(pc) = worklist.pop() {
        let mut states = incoming[pc].clone().expect("scheduled verifier state");
        let mut advances = true;
        let instruction = &function.instructions[pc];
        match instruction {
            VmInstruction::ConstUnit { dst } => {
                expect_type(function, *dst, VmType::Unit)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstI64 { dst, .. } => {
                expect_type(function, *dst, VmType::I64)?;
                write(&mut states, *dst)?
            }
            VmInstruction::ConstF64 { dst, bits } => {
                if !is_canonical_f64_bits(*bits) {
                    return Err(VmArtifactError::NonCanonicalFloat { bits: *bits });
                }
                expect_type(function, *dst, VmType::F64)?;
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
                write(&mut states, *dst)?
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
                write(&mut states, *dst)?
            }
            VmInstruction::MakeRecord {
                dst,
                definition,
                fields,
                field_types,
            } => {
                match register_type(function, *dst)? {
                    VmType::Nominal {
                        definition: actual, ..
                    } if actual == *definition => {}
                    found => {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *dst,
                            expected: VmType::Nominal {
                                definition: *definition,
                                arguments: Vec::new(),
                            },
                            found,
                        });
                    }
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
                write(&mut states, *dst)?
            }
            VmInstruction::MakeEnum {
                dst,
                definition,
                fields,
                field_types,
                ..
            } => {
                match register_type(function, *dst)? {
                    VmType::Nominal {
                        definition: actual, ..
                    } if actual == *definition => {}
                    found => {
                        return Err(VmArtifactError::TypeMismatch {
                            register: *dst,
                            expected: VmType::Nominal {
                                definition: *definition,
                                arguments: Vec::new(),
                            },
                            found,
                        });
                    }
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
                write(&mut states, *dst)?
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
                if !matches!(register_type(function, *base)?, VmType::Nominal { .. }) {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *base,
                        expected: VmType::Nominal {
                            definition: DefKey(Digest::of_bytes(b"record-base")),
                            arguments: Vec::new(),
                        },
                        found: register_type(function, *base)?,
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
                let VmType::Nominal { .. } = register_type(function, *base)? else {
                    unreachable!("checked nominal base")
                };
                write(&mut states, *dst)?
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
                write(&mut states, *dst)?
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
                write(&mut states, *dst)?
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
                        snapshots: states.snapshots.clone(),
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
                        snapshots: continuation.snapshots,
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
                    snapshots: continuation.snapshots,
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
                        snapshots: continuation.snapshots,
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
                    forwarded.snapshots = continuation.snapshots.clone();
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
                        snapshots: continuation.snapshots,
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
            }
            VmInstruction::Store { dst, src } => {
                read(&states, *src)?;
                same_type(function, *dst, *src)?;
                let state = states
                    .get_mut(*dst as usize)
                    .ok_or(VmArtifactError::InvalidRegister { register: *dst })?;
                *state = Some(true);
                states.snapshots[*dst as usize] = states.snapshots[*src as usize];
            }
            VmInstruction::Move { dst, src } => {
                read(&states, *src)?;
                same_type(function, *dst, *src)?;
                states[*src as usize] = Some(false);
                states.snapshots[*dst as usize] = states.snapshots[*src as usize];
                states.snapshots[*src as usize] = None;
                write(&mut states, *dst)?
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
                write(&mut states, *dst)?
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
                write(&mut states, *dst)?
            }
            VmInstruction::DerefStore { reference, src } => {
                read(&states, *reference)?;
                read(&states, *src)?;
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
                }
                if !matches!(register_type(function, *dst)?, VmType::Callable { .. }) {
                    return Err(VmArtifactError::NotCallable { register: *dst });
                }
                write(&mut states, *dst)?
            }
            VmInstruction::CallIndirect {
                dst,
                callee,
                arguments,
            } => {
                read(&states, *callee)?;
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
                states.handlers.clear();
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
            VmInstruction::Trap => advances = false,
        }
        if advances {
            propagate_state(&mut incoming, &mut worklist, (pc + 1) as u32, &states)?;
        }
    }
    if returned.is_some() {
        Ok(())
    } else {
        Err(VmArtifactError::NoReturn)
    }
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
        VmType::Tuple(values) => values.iter().try_for_each(validate_vm_type),
        VmType::Nominal { arguments, .. } => arguments
            .iter()
            .try_for_each(validate_vm_nominal_argument_type),
        VmType::Callable {
            parameters,
            result,
            effects,
        } => {
            parameters.iter().try_for_each(validate_vm_type)?;
            validate_vm_type(result)?;
            validate_vm_effect_row(effects)
        }
        VmType::Reference { referent, .. } => validate_vm_type(referent),
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
/// one through an ordinary jump, branch, or fallthrough would let hostile
/// bytecode execute a clause without the `Perform` transition that initializes
/// payload destinations and records the continuation consumed by `Resume`,
/// `Forward`, or `Cancel`.
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
            VmInstruction::Jump { target } | VmInstruction::Leave { target, .. } => {
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
                VmInstruction::Jump { target } | VmInstruction::Leave { target, .. } => *target,
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
            let snapshots = existing
                .snapshots
                .iter()
                .zip(&state.snapshots)
                .map(|(left, right)| if left == right { *left } else { None })
                .collect::<Vec<_>>();
            let pending_leave = if existing.pending_leave == state.pending_leave {
                existing.pending_leave.clone()
            } else {
                None
            };
            if existing.registers != joined
                || existing.snapshots != snapshots
                || existing.pending_leave != pending_leave
                || handler_changed
            {
                existing.registers = joined;
                existing.snapshots = snapshots;
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
    for (index, descriptor) in descriptors.iter().enumerate() {
        if descriptor.variants.is_empty()
            || descriptors[..index].iter().any(|previous| {
                previous.definition == descriptor.definition
                    && previous.arguments == descriptor.arguments
            })
        {
            return Err(VmArtifactError::InvalidCallableEnvironment {
                message: "invalid nominal copy descriptor",
            });
        }
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

fn write(states: &mut [Option<bool>], register: u32) -> Result<(), VmArtifactError> {
    let state = states
        .get_mut(register as usize)
        .ok_or(VmArtifactError::InvalidRegister { register })?;
    if state.is_some() {
        Err(VmArtifactError::DoubleWrite { register })
    } else {
        *state = Some(true);
        Ok(())
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
    Unit,
    I64(i64),
    Usize(u64),
    U32(u32),
    U8(u8),
    F64(f64),
    Bool(bool),
    Char(char),
    Text(Arc<str>),
    Bytes(Arc<[u8]>),
    Tuple(Arc<[VmValue]>),
    Array(Arc<[VmValue]>),
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
    /// A frame-branded callable token. Only `ResumeSnapshot` may consume it;
    /// ordinary indirect calls reject it.
    Resumption {
        frame: u64,
        signature: VmType,
    },
}

#[derive(Clone, Debug)]
enum ReferenceTarget {
    Register(u32),
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
            Self::Unit => VmType::Unit,
            Self::I64(_) => VmType::I64,
            Self::Usize(_) => VmType::Usize,
            Self::U32(_) => VmType::U32,
            Self::U8(_) => VmType::U8,
            Self::F64(_) => VmType::F64,
            Self::Bool(_) => VmType::Bool,
            Self::Char(_) => VmType::Char,
            Self::Text(_) => VmType::Text,
            Self::Bytes(_) => VmType::Bytes,
            Self::Tuple(values) => VmType::Tuple(values.iter().map(VmValue::ty).collect()),
            Self::Array(values) => VmType::Array(Box::new(
                values.first().map(VmValue::ty).unwrap_or(VmType::Unit),
            )),
            Self::Record { signature, .. } => signature.clone(),
            Self::Enum { signature, .. } => signature.clone(),
            Self::Callable { signature, .. } => signature.clone(),
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
        VmValue::Tuple(values) | VmValue::Array(values) => values,
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

fn store_reference(
    value: &VmValue,
    fields: &[u32],
    replacement: VmValue,
    budget: &mut ExecutionBudget,
) -> Result<VmValue, VmArtifactError> {
    let Some((field, rest)) = fields.split_first() else {
        return Ok(replacement);
    };
    match value {
        VmValue::Tuple(values) => {
            budget.reserve_value("reference update fields", values.len())?;
            let mut values = values.to_vec();
            let slot = values
                .get_mut(*field as usize)
                .ok_or(VmArtifactError::InvalidRegister { register: *field })?;
            *slot = store_reference(slot, rest, replacement, budget)?;
            Ok(VmValue::Tuple(values.into()))
        }
        VmValue::Array(values) => {
            budget.reserve_value("reference update fields", values.len())?;
            let mut values = values.to_vec();
            let slot = values
                .get_mut(*field as usize)
                .ok_or(VmArtifactError::InvalidRegister { register: *field })?;
            *slot = store_reference(slot, rest, replacement, budget)?;
            Ok(VmValue::Array(values.into()))
        }
        VmValue::Record {
            definition,
            fields: old,
            signature,
        } => {
            budget.reserve_value("reference update fields", old.len())?;
            let mut fields = old.to_vec();
            let slot = fields
                .get_mut(*field as usize)
                .ok_or(VmArtifactError::InvalidRegister { register: *field })?;
            *slot = store_reference(slot, rest, replacement, budget)?;
            Ok(VmValue::Record {
                definition: *definition,
                fields: fields.into(),
                signature: signature.clone(),
            })
        }
        VmValue::Enum {
            definition,
            variant,
            fields: old,
            signature,
        } => {
            budget.reserve_value("reference update fields", old.len())?;
            let mut fields = old.to_vec();
            let slot = fields
                .get_mut(*field as usize)
                .ok_or(VmArtifactError::InvalidRegister { register: *field })?;
            *slot = store_reference(slot, rest, replacement, budget)?;
            Ok(VmValue::Enum {
                definition: *definition,
                variant: *variant,
                fields: fields.into(),
                signature: signature.clone(),
            })
        }
        value => Err(VmArtifactError::ResultType {
            expected: VmType::Tuple(Vec::new()),
            found: value.ty(),
        }),
    }
}

fn borrow_value(
    source: u32,
    value: &VmValue,
    fields: &[u32],
    unique: bool,
    reborrow: bool,
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
        return Ok(VmValue::Reference {
            target: target.clone(),
            fields: path.into(),
            unique,
            referent: if fields.is_empty() {
                parent_referent.clone()
            } else {
                project_reference(value, fields)?.ty()
            },
        });
    }
    Ok(VmValue::Reference {
        target: ReferenceTarget::Register(source),
        fields: fields.to_vec().into(),
        unique,
        referent: project_reference(value, fields)?.ty(),
    })
}

fn reference_target<'a>(
    registers: &'a [Option<VmValue>],
    target: &'a ReferenceTarget,
) -> Result<&'a VmValue, VmArtifactError> {
    match target {
        ReferenceTarget::Register(target) => registers
            .get(*target as usize)
            .and_then(Option::as_ref)
            .ok_or(VmArtifactError::InvalidRegister { register: *target }),
        ReferenceTarget::Captured(value) => Ok(value),
    }
}

/// A callable runs in a fresh frame, so a shared reference captured from its
/// creator must not retain a raw creator-register index. Rebase it to the
/// immutable referent snapshot. Unique references are deliberately refused:
/// snapshotting would silently lose their write-back alias.
fn freeze_callable_capture(
    value: &VmValue,
    registers: &[Option<VmValue>],
) -> Result<VmValue, VmArtifactError> {
    match value {
        VmValue::Reference { unique: true, .. } => {
            Err(VmArtifactError::UnsupportedEscapingUniqueReference)
        }
        VmValue::Reference {
            target,
            fields,
            unique: false,
            referent,
        } => Ok(VmValue::Reference {
            target: ReferenceTarget::Captured(Arc::new(project_reference(
                reference_target(registers, target)?,
                fields,
            )?)),
            fields: Arc::from([]),
            unique: false,
            referent: referent.clone(),
        }),
        value => Ok(value.clone()),
    }
}

fn format_vm_value(value: &VmValue) -> String {
    match value {
        VmValue::Unit => "()".into(),
        VmValue::I64(value) => value.to_string(),
        VmValue::Usize(value) => value.to_string(),
        VmValue::U32(value) => value.to_string(),
        VmValue::U8(value) => value.to_string(),
        VmValue::F64(value) => value.to_string(),
        VmValue::Bool(value) => value.to_string(),
        VmValue::Char(value) => format!("{value:?}"),
        VmValue::Text(value) => format!("{value:?}"),
        VmValue::Bytes(value) => format!("{value:?}"),
        VmValue::Tuple(values) => format!(
            "({})",
            values
                .iter()
                .map(format_vm_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        VmValue::Array(values) => format!(
            "[{}]",
            values
                .iter()
                .map(format_vm_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
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
        VmValue::Resumption { frame, .. } => format!("resumption@{frame}"),
        VmValue::Reference { target, fields, .. } => {
            let target = match target {
                ReferenceTarget::Register(target) => format!("register@{target}"),
                ReferenceTarget::Captured(_) => "captured".into(),
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
        VmValue::Array(values) => values.iter().map(expect_i64).collect(),
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

/// Keep the VM's observable IEEE-754 representation independent of the host
/// NaN payload selected by an arithmetic instruction.  The numerical
/// comparison rules remain ordinary IEEE rules; only the non-semantic payload
/// encoding is collapsed.
fn canonical_vm_f64(value: f64) -> f64 {
    f64::from_bits(canonical_f64_bits(value.to_bits()))
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
            VmValue::Array(values)
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
        VmType::F64 => matches!(value, VmValue::F64(_)),
        VmType::Bool => matches!(value, VmValue::Bool(_)),
        VmType::Char => matches!(value, VmValue::Char(_)),
        VmType::Text => matches!(value, VmValue::Text(_)),
        VmType::Bytes => matches!(value, VmValue::Bytes(_)),
        VmType::Tuple(expected) => {
            matches!(value, VmValue::Tuple(values) if values.len() == expected.len() && values.iter().zip(expected).all(|(value, ty)| value_matches_vm_type(value, ty)))
        }
        VmType::Array(expected) => {
            matches!(value, VmValue::Array(values) if values.iter().all(|value| value_matches_vm_type(value, expected)))
        }
        VmType::Nominal {
            definition,
            arguments,
        } => {
            matches!(value, VmValue::Record { definition: actual, signature: VmType::Nominal { definition: signature_definition, arguments: actual_arguments }, .. } | VmValue::Enum { definition: actual, signature: VmType::Nominal { definition: signature_definition, arguments: actual_arguments }, .. } if actual == definition && signature_definition == definition && actual_arguments.len() == arguments.len() && actual_arguments.iter().zip(arguments).all(|(actual, expected)| vm_type_matches(actual, expected)))
        }
        VmType::Callable {
            parameters,
            result,
            effects,
        } => {
            matches!(value, VmValue::Callable { signature: VmType::Callable { parameters: actual_parameters, result: actual_result, effects: actual_effects }, .. } if actual_parameters.len() == parameters.len() && actual_parameters.iter().zip(parameters).all(|(actual, expected)| vm_type_matches(actual, expected)) && vm_type_matches(actual_result, result) && vm_effect_row_matches(actual_effects, effects))
        }
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
            parameters,
            result,
            effects,
        } => {
            matches!(actual, VmType::Callable { parameters: actual_parameters, result: actual_result, effects: actual_effects } if actual_parameters.len() == parameters.len() && actual_parameters.iter().zip(parameters).all(|(actual, expected)| vm_type_matches(actual, expected)) && vm_type_matches(actual_result, result) && vm_effect_row_matches(actual_effects, effects))
        }
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
        VmValue::F64(value) => parse_pattern_f64(literal).is_some_and(|literal| literal == *value),
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
            VmInstruction::ConstUnit { dst } => registers[dst as usize] = Some(VmValue::Unit),
            VmInstruction::ConstI64 { dst, value } => {
                registers[dst as usize] = Some(VmValue::I64(value))
            }
            VmInstruction::ConstF64 { dst, bits } => {
                registers[dst as usize] = Some(VmValue::F64(canonical_vm_f64(f64::from_bits(bits))))
            }
            VmInstruction::ConstBool { dst, value } => {
                registers[dst as usize] = Some(VmValue::Bool(value))
            }
            VmInstruction::ConstChar { dst, value } => {
                registers[dst as usize] =
                    Some(VmValue::Char(char::from_u32(value).expect("verified char")))
            }
            VmInstruction::ConstText { dst, value } => {
                registers[dst as usize] = Some(VmValue::Text(Arc::from(value)));
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
                let mut value = expect_bytes(
                    registers[left as usize]
                        .as_ref()
                        .expect("verified register"),
                )?
                .to_vec();
                value.extend_from_slice(&expect_bytes(
                    registers[right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?);
                budget.reserve_value("bytes", value.len())?;
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
                    VmValue::Array(values) => values,
                    value => {
                        return Err(VmArtifactError::ResultType {
                            expected: VmType::Array(Box::new(VmType::U8)),
                            found: value.ty(),
                        });
                    }
                };
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
                registers[dst as usize] = Some(VmValue::Array(Arc::from(
                    bytes.iter().copied().map(VmValue::U8).collect::<Vec<_>>(),
                )));
            }
            VmInstruction::BytesUtf8ValidUpTo { dst, value } => {
                let bytes = expect_bytes(
                    registers[value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                registers[dst as usize] = Some(VmValue::Usize(valid_utf8_prefix(&bytes) as u64));
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
                registers[dst as usize] = Some(VmValue::Array(Arc::from(values)));
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
                ..
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
                registers[dst as usize] = Some(
                    fields
                        .get(index as usize)
                        .ok_or(VmArtifactError::InvalidRegister { register: index })?
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
                let VmValue::Array(fields) = registers[base as usize]
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
                        registers[*argument as usize].clone().ok_or(
                            VmArtifactError::ReadBeforeWrite {
                                register: *argument,
                            },
                        )
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
            }
            VmInstruction::Copy { dst, src } => {
                registers[dst as usize] = registers[src as usize].clone()
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
                registers[dst as usize] = Some(borrow_value(
                    src,
                    registers[src as usize].as_ref().expect("verified register"),
                    &fields,
                    unique,
                    reborrow,
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
                registers[dst as usize] = Some(project_reference(
                    reference_target(&registers, target)?,
                    fields,
                )?);
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
                let ReferenceTarget::Register(target) = target else {
                    return Err(VmArtifactError::UnsupportedEscapingUniqueReference);
                };
                let (target, fields) = (*target, fields.clone());
                let replacement = registers[src as usize]
                    .as_ref()
                    .expect("verified register")
                    .clone();
                let updated = store_reference(
                    registers[target as usize]
                        .as_ref()
                        .expect("live reference target"),
                    &fields,
                    replacement,
                    budget,
                )?;
                registers[target as usize] = Some(updated);
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
                registers[dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .wrapping_shr(expect_u32(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?),
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
                registers[dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[value as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .wrapping_shl(expect_u32(
                        registers[count as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?),
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
            VmInstruction::Call { .. }
            | VmInstruction::MakeCallable { .. }
            | VmInstruction::CallIndirect { .. } => {
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
                        target,
                        arguments,
                        destinations,
                        cleanup,
                    },
                )?;
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
    if !leave.cleanup.validate() || leave.arguments.len() != leave.destinations.len() {
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
    handlers.clear();
    Ok(leave.target as usize)
}
fn encode_instruction(value: &VmInstruction, output: &mut Vec<u8>) {
    match value {
        VmInstruction::ConstUnit { dst } => {
            output.push(28);
            output.extend_from_slice(&dst.to_le_bytes());
        }
        VmInstruction::ConstI64 { dst, value } => {
            output.push(0);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&value.to_le_bytes())
        }
        VmInstruction::ConstF64 { dst, bits } => {
            output.push(7);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&bits.to_le_bytes())
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
        VmInstruction::ConstText { dst, value } => {
            output.push(24);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&(value.len() as u64).to_le_bytes());
            output.extend_from_slice(value.as_bytes());
        }
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
            target,
            arguments,
            destinations,
            cleanup,
        } => {
            output.push(55);
            output.extend_from_slice(&brand_owner.0.as_bytes());
            output.extend_from_slice(&brand_label.to_le_bytes());
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
        output.extend_from_slice(&(loan.root.len() as u64).to_le_bytes());
        output.extend_from_slice(loan.root.as_bytes());
        output.extend_from_slice(&(loan.fields.len() as u64).to_le_bytes());
        for field in &loan.fields {
            output.extend_from_slice(&field.to_le_bytes());
        }
        output.push(u8::from(loan.unique));
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
    if depth >= budget.limits.max_call_depth {
        return Err(VmArtifactError::CallDepthLimit {
            limit: budget.limits.max_call_depth,
        });
    }
    let function = program
        .functions
        .get(&definition)
        .ok_or(VmArtifactError::MissingFunction { definition })?;
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
        let function = program
            .functions
            .get(&definition)
            .ok_or(VmArtifactError::MissingFunction { definition })?;
        let Some(instruction) = function.instructions.get(pc) else {
            return Err(VmArtifactError::NoReturn);
        };
        budget.tick()?;
        match instruction {
            VmInstruction::ConstUnit { dst } => registers[*dst as usize] = Some(VmValue::Unit),
            VmInstruction::ConstI64 { dst, value } => {
                registers[*dst as usize] = Some(VmValue::I64(*value))
            }
            VmInstruction::ConstF64 { dst, bits } => {
                registers[*dst as usize] =
                    Some(VmValue::F64(canonical_vm_f64(f64::from_bits(*bits))))
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
                registers[*dst as usize] = Some(VmValue::Text(Arc::from(value.as_str())));
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
                let mut value = expect_bytes(
                    registers[*left as usize]
                        .as_ref()
                        .expect("verified register"),
                )?
                .to_vec();
                value.extend_from_slice(&expect_bytes(
                    registers[*right as usize]
                        .as_ref()
                        .expect("verified register"),
                )?);
                budget.reserve_value("bytes", value.len())?;
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
                    VmValue::Array(values) => values,
                    value => {
                        return Err(VmArtifactError::ResultType {
                            expected: VmType::Array(Box::new(VmType::U8)),
                            found: value.ty(),
                        });
                    }
                };
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
                registers[*dst as usize] = Some(VmValue::Array(Arc::from(
                    bytes.iter().copied().map(VmValue::U8).collect::<Vec<_>>(),
                )));
            }
            VmInstruction::BytesUtf8ValidUpTo { dst, value } => {
                let bytes = expect_bytes(
                    registers[*value as usize]
                        .as_ref()
                        .expect("verified register"),
                )?;
                registers[*dst as usize] = Some(VmValue::Usize(valid_utf8_prefix(&bytes) as u64));
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
                registers[*dst as usize] = Some(VmValue::Array(Arc::from(values)));
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
                ..
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
                registers[*dst as usize] = Some(
                    fields
                        .get(*index as usize)
                        .ok_or(VmArtifactError::InvalidRegister { register: *index })?
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
                let VmValue::Array(fields) = registers[*base as usize]
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
                for (destination, value) in payload_destinations.iter().zip(values.iter().cloned())
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
                    .zip(continuation.performed.payloads.iter().cloned())
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
            }
            VmInstruction::Copy { dst, src } => {
                registers[*dst as usize] = registers[*src as usize].clone()
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
                registers[*dst as usize] = Some(borrow_value(
                    *src,
                    registers[*src as usize]
                        .as_ref()
                        .expect("verified register"),
                    fields,
                    *unique,
                    *reborrow,
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
                registers[*dst as usize] = Some(project_reference(
                    reference_target(&registers, target)?,
                    fields,
                )?);
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
                let ReferenceTarget::Register(target) = target else {
                    return Err(VmArtifactError::UnsupportedEscapingUniqueReference);
                };
                let (target, fields) = (*target, fields.clone());
                let replacement = registers[*src as usize]
                    .as_ref()
                    .expect("verified register")
                    .clone();
                let updated = store_reference(
                    registers[target as usize]
                        .as_ref()
                        .expect("live reference target"),
                    &fields,
                    replacement,
                    budget,
                )?;
                registers[target as usize] = Some(updated);
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
                registers[*dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .wrapping_shr(expect_u32(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?),
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
                registers[*dst as usize] = Some(VmValue::I64(
                    expect_i64(
                        registers[*value as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?
                    .wrapping_shl(expect_u32(
                        registers[*count as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?),
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
                capability, symbol, ..
            } => {
                return Err(VmArtifactError::HostCallRequiresAuthority {
                    capability: capability.clone(),
                    symbol: symbol.clone(),
                });
            }
            VmInstruction::Call {
                dst,
                callee,
                arguments,
            } => {
                budget.reserve_value("call arguments", arguments.len())?;
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
                            .and_then(|value| freeze_callable_capture(value, &registers))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let signature = register_type(function, *dst)?;
                registers[*dst as usize] = Some(VmValue::Callable {
                    callee: *callee,
                    captures: Arc::from(values),
                    signature,
                });
            }
            VmInstruction::CallIndirect {
                dst,
                callee,
                arguments,
            } => {
                let VmValue::Callable {
                    callee, captures, ..
                } = registers[*callee as usize]
                    .as_ref()
                    .expect("verified register")
                    .clone()
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
                values.extend(arguments.iter().map(|argument| {
                    registers[*argument as usize]
                        .as_ref()
                        .expect("verified register")
                        .clone()
                }));
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
                        target: *target,
                        arguments: arguments.clone(),
                        destinations: destinations.clone(),
                        cleanup: cleanup.clone(),
                    },
                )?;
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
struct ExecutionBudget {
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
