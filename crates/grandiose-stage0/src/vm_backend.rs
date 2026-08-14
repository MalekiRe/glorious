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
    identity::{DefKey, Digest},
    mir::{
        MirFunction, MirInstruction, MirLocal, MirPattern, MirPatternField, MirProgram,
        MirTerminator,
    },
    types::{ScalarType, Type},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VmType {
    Unit,
    I64,
    F64,
    Bool,
    Char,
    Text,
    /// Binder-local type variable in a generic VM function. The program
    /// verifier instantiates it at each direct call before execution begins.
    Generic(u32),
    Array(Box<VmType>),
    Tuple(Vec<VmType>),
    Nominal {
        definition: DefKey,
        arguments: Vec<VmType>,
    },
    Callable {
        parameters: Vec<VmType>,
        result: Box<VmType>,
    },
    Reference {
        unique: bool,
        referent: Box<VmType>,
    },
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
/// Canonically encoded structural pattern for the standalone VM verifier.
/// It contains no source binder identity; fields carry their expected runtime
/// types so decoding and verification do not depend on compiler interfaces.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VmPattern {
    Any,
    Literal(String),
    Tuple(Vec<VmPattern>),
    Record {
        definition: DefKey,
        fields: Vec<VmPatternField>,
    },
    Enum {
        definition: DefKey,
        variant: u32,
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
        effect_arguments: Vec<VmType>,
        operation: u32,
        arguments: Vec<u32>,
    },
    /// Install one lexical, one-shot handler frame. The frame is active while
    /// its protected continuation executes; an intercepted operation transfers
    /// to `target`, writes its payload into `payload_destinations`, and makes a
    /// single continuation available to `Resume`.
    InstallHandler {
        effect: DefKey,
        effect_arguments: Vec<VmType>,
        operation: u32,
        payload_destinations: Vec<u32>,
        resume_type: VmType,
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
    MakeCallable {
        dst: u32,
        callee: DefKey,
        captures: Vec<u32>,
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
        let mut moved_places = plan
            .moved_places
            .iter()
            .map(|place| VmCleanupPlace {
                root: place.root.clone(),
                fields: place.fields.clone(),
            })
            .collect::<Vec<_>>();
        let mut active_loans = plan
            .active_loans
            .iter()
            .map(|loan| VmCleanupLoan {
                owner: loan.owner.clone(),
                root: loan.root.clone(),
                fields: loan.fields.clone(),
                unique: loan.unique,
            })
            .collect::<Vec<_>>();
        moved_places.sort();
        moved_places.dedup();
        active_loans.sort();
        active_loans.dedup();
        Self {
            moved_places,
            active_loans,
        }
    }
    pub fn validate(&self) -> bool {
        self.moved_places.windows(2).all(|pair| pair[0] < pair[1])
            && self.active_loans.windows(2).all(|pair| pair[0] < pair[1])
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmFunction {
    pub definition: DefKey,
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
    pub entry: DefKey,
    pub functions: BTreeMap<DefKey, VmFunction>,
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
        ty: Type,
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
    NoReturn,
    Trap,
    InstructionAfterReturn,
    MissingFunction {
        definition: DefKey,
    },
    CallRequiresProgram,
    CallArity {
        expected: u32,
        found: u32,
    },
    NotCallable {
        register: u32,
    },
    CallDepthLimit {
        limit: u32,
    },
    HandlerDepthLimit {
        limit: u32,
    },
    InstructionLimit {
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
    DivisionByZero,
    ArithmeticOverflow,
    UnhandledEffect {
        effect: DefKey,
        /// The exact nominal protocol instance that escaped the handler
        /// stack. This is required to distinguish e.g. `State<i64>` from
        /// `State<Text>` at the VM boundary.
        effect_arguments: Vec<VmType>,
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
    pub max_instructions: u64,
}
impl Default for VmExecutionLimits {
    fn default() -> Self {
        Self {
            max_call_depth: 4_096,
            max_handler_depth: 4_096,
            max_instructions: 10_000_000,
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
/// Schema 26 adds canonical cleanup-carrying `Leave` edges.
/// Older layouts cannot be decoded safely because the operation field now
/// follows a sequence of canonical VM types.
pub const STAGE0_VM_SCHEMA: u32 = 26;
const MAX_DECODE_FUNCTIONS: u64 = 1 << 16;
const MAX_DECODE_REGISTERS: u64 = 1 << 20;
const MAX_DECODE_INSTRUCTIONS: u64 = 1 << 22;
const MAX_DECODE_TEXT_BYTES: u64 = 1 << 26;
const MAX_DECODE_TYPE_DEPTH: u64 = 128;

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
    bytes.extend_from_slice(&(program.functions.len() as u64).to_le_bytes());
    for function in program.functions.values() {
        encode_function(function, &mut bytes);
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
    if decoder.remaining() != 0 {
        return Err(VmArtifactError::MalformedEncoding {
            message: "trailing bytes after program payload",
        });
    }
    let program = CandidateVmProgram {
        schema,
        runtime_manifest,
        entry,
        functions,
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
        program_fingerprint(self.entry, self.runtime_manifest, &self.functions)
    }
}
impl VerifiedVmArtifact {
    pub fn fingerprint(&self) -> Digest {
        self.artifact.fingerprint
    }
    pub fn runtime_manifest(&self) -> Option<Digest> {
        self.artifact.runtime_manifest
    }
    pub fn run_i64(&self) -> Result<i64, VmArtifactError> {
        expect_i64(execute(&self.artifact.function)?)
    }
    pub fn run_tuple_i64(&self) -> Result<Vec<i64>, VmArtifactError> {
        expect_tuple_i64(execute(&self.artifact.function)?)
    }
    pub fn run_array_i64(&self) -> Result<Vec<i64>, VmArtifactError> {
        expect_array_i64(execute(&self.artifact.function)?)
    }
    pub fn run_record_i64(&self) -> Result<Vec<i64>, VmArtifactError> {
        expect_record_i64(execute(&self.artifact.function)?)
    }
    pub fn run_enum_i64(&self) -> Result<Vec<i64>, VmArtifactError> {
        expect_enum_i64(execute(&self.artifact.function)?)
    }
    pub fn run_unit(&self) -> Result<(), VmArtifactError> {
        expect_unit(execute(&self.artifact.function)?)
    }
    pub fn run_f64(&self) -> Result<f64, VmArtifactError> {
        expect_f64(execute(&self.artifact.function)?)
    }
    pub fn run_bool(&self) -> Result<bool, VmArtifactError> {
        expect_bool(execute(&self.artifact.function)?)
    }
    pub fn run_char(&self) -> Result<char, VmArtifactError> {
        expect_char(execute(&self.artifact.function)?)
    }
    pub fn run_text(&self) -> Result<String, VmArtifactError> {
        Ok(expect_text(execute(&self.artifact.function)?)?.to_string())
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
    pub fn run_tuple_i64(&self) -> Result<Vec<i64>, VmArtifactError> {
        let mut budget = ExecutionBudget {
            limits: VmExecutionLimits::default(),
            instructions: 0,
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
                .map(|instruction| lower_instruction(instruction, &starts)),
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
    Ok(CandidateVmProgram {
        schema: STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        entry: program.entry,
        fingerprint: program_fingerprint(program.entry, None, &functions),
        functions,
    })
}
fn vm_type(value: &Type) -> Result<VmType, Type> {
    match value {
        Type::Unit => Ok(VmType::Unit),
        Type::Scalar(ScalarType::I64) => Ok(VmType::I64),
        Type::Scalar(ScalarType::F64) => Ok(VmType::F64),
        Type::Scalar(ScalarType::Bool) => Ok(VmType::Bool),
        Type::Scalar(ScalarType::Char) => Ok(VmType::Char),
        Type::Scalar(ScalarType::Text) => Ok(VmType::Text),
        Type::Generic(index) => Ok(VmType::Generic(*index)),
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
                .map(vm_type)
                .collect::<Result<Vec<_>, _>>()?,
        }),
        Type::Callable {
            parameters, result, ..
        } => Ok(VmType::Callable {
            parameters: parameters
                .iter()
                .map(vm_type)
                .collect::<Result<Vec<_>, _>>()?,
            result: Box::new(vm_type(result)?),
        }),
        Type::Reference {
            mutability,
            referent,
            ..
        } => Ok(VmType::Reference {
            unique: matches!(mutability, crate::types::Mutability::Unique),
            referent: Box::new(vm_type(referent)?),
        }),
        value => Err(value.clone()),
    }
}
fn encode_type(value: &VmType, output: &mut Vec<u8>) {
    output.push(match value {
        VmType::Unit => 0,
        VmType::I64 => 1,
        VmType::F64 => 2,
        VmType::Bool => 3,
        VmType::Char => 4,
        VmType::Text => 5,
        VmType::Generic(_) => 9,
        VmType::Array(_) => 10,
        VmType::Callable { .. } => 6,
        VmType::Tuple(_) => 7,
        VmType::Nominal { .. } => 8,
        VmType::Reference { .. } => 11,
    });
    match value {
        VmType::Callable { parameters, result } => {
            output.extend_from_slice(&(parameters.len() as u64).to_le_bytes());
            for parameter in parameters {
                encode_type(parameter, output);
            }
            encode_type(result, output);
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
        VmType::Reference { unique, referent } => {
            output.push(*unique as u8);
            encode_type(referent, output);
        }
        VmType::Array(element) => encode_type(element, output),
        _ => {}
    }
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
    let mut bytes = b"grandiose-stage0-vm-v21".to_vec();
    encode_optional_digest(runtime_manifest, &mut bytes);
    encode_function(function, &mut bytes);
    Digest::of_bytes(&bytes)
}
fn program_fingerprint(
    entry: DefKey,
    runtime_manifest: Option<Digest>,
    functions: &BTreeMap<DefKey, VmFunction>,
) -> Digest {
    let mut bytes = b"grandiose-stage0-vm-program-v21".to_vec();
    bytes.extend_from_slice(&entry.0.as_bytes());
    encode_optional_digest(runtime_manifest, &mut bytes);
    for function in functions.values() {
        encode_function(function, &mut bytes);
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
            2 => Ok(VmType::F64),
            3 => Ok(VmType::Bool),
            4 => Ok(VmType::Char),
            5 => Ok(VmType::Text),
            6 => {
                let count = self.count("callable parameters", MAX_DECODE_REGISTERS)?;
                let mut parameters = Vec::with_capacity(count);
                for _ in 0..count {
                    parameters.push(self.vm_type_at_depth(depth + 1)?);
                }
                Ok(VmType::Callable {
                    parameters,
                    result: Box::new(self.vm_type_at_depth(depth + 1)?),
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
            _ => Err(VmArtifactError::MalformedEncoding {
                message: "unknown VM register type",
            }),
        }
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
            tag @ (3 | 4) => {
                let definition = self.def_key()?;
                let variant = (tag == 4).then(|| self.u32()).transpose()?;
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
                        fields,
                    }),
                    None => Ok(VmPattern::Record { definition, fields }),
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
        let instruction_count = self.count("instructions", MAX_DECODE_INSTRUCTIONS)?;
        let mut instructions = Vec::with_capacity(instruction_count);
        for _ in 0..instruction_count {
            instructions.push(self.instruction()?);
        }
        Ok(VmFunction {
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
                let effect_argument_count =
                    self.count("effect protocol arguments", MAX_DECODE_TYPE_DEPTH)?;
                let mut effect_arguments = Vec::with_capacity(effect_argument_count);
                for _ in 0..effect_argument_count {
                    effect_arguments.push(self.vm_type()?);
                }
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
            43 => Ok(VmInstruction::Trap),
            44 => {
                let effect = self.def_key()?;
                let effect_argument_count =
                    self.count("handler protocol arguments", MAX_DECODE_TYPE_DEPTH)?;
                let mut effect_arguments = Vec::with_capacity(effect_argument_count);
                for _ in 0..effect_argument_count {
                    effect_arguments.push(self.vm_type()?);
                }
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
                    target: self.u32()?,
                })
            }
            45 => Ok(VmInstruction::UninstallHandler),
            46 => Ok(VmInstruction::Resume { value: self.u32()? }),
            47 => Ok(VmInstruction::Forward),
            48 => Ok(VmInstruction::Cancel),
            49 => Ok(VmInstruction::CaptureResumption { dst: self.u32()? }),
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
            3 => self.i64_arithmetic(|dst, left, right| VmInstruction::AddI64 { dst, left, right }),
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
            7 => Ok(VmInstruction::ConstF64 {
                dst: self.u32()?,
                bits: self.u64()?,
            }),
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
                let VmType::Callable { parameters, result } = register_type(function, *dst)? else {
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
        } => match found {
            VmType::Callable {
                parameters: found_parameters,
                result: found_result,
            } if expected_parameters.len() == found_parameters.len() => {
                expected_parameters
                    .iter()
                    .zip(found_parameters)
                    .all(|(expected, found)| unify_call_type(expected, found, bindings))
                    && unify_call_type(expected_result, found_result, bindings)
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
        VmType::Callable { parameters, result } => VmType::Callable {
            parameters: parameters
                .iter()
                .map(|parameter| instantiate_vm_type(parameter, bindings))
                .collect(),
            result: Box::new(instantiate_vm_type(result, bindings)),
        },
        VmType::Reference { unique, referent } => VmType::Reference {
            unique: *unique,
            referent: Box::new(instantiate_vm_type(referent, bindings)),
        },
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

fn lower_instruction(value: &MirInstruction, starts: &[u32]) -> VmInstruction {
    match value {
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
                .map(|argument| {
                    vm_type(argument).expect("validated MIR has VM-representable effect arguments")
                })
                .collect(),
            operation: *operation,
            arguments: arguments.iter().map(|argument| argument.0).collect(),
        },
        MirInstruction::InstallHandler {
            effect,
            effect_arguments,
            operation,
            payload_destinations,
            resume_type,
            target,
        } => VmInstruction::InstallHandler {
            effect: *effect,
            effect_arguments: effect_arguments
                .iter()
                .map(|argument| {
                    vm_type(argument).expect("validated MIR has VM-representable effect arguments")
                })
                .collect(),
            operation: *operation,
            payload_destinations: payload_destinations
                .iter()
                .map(|destination| destination.0)
                .collect(),
            resume_type: vm_type(resume_type)
                .expect("validated MIR has VM-representable handler result type"),
            target: *starts
                .get(target.0 as usize)
                .expect("validated MIR handler target exists"),
        },
        MirInstruction::UninstallHandler => VmInstruction::UninstallHandler,
        MirInstruction::CaptureResumption { dst } => {
            VmInstruction::CaptureResumption { dst: dst.0 }
        }
        MirInstruction::Resume { value } => VmInstruction::Resume { value: value.0 },
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
        } => VmInstruction::Borrow {
            dst: dst.0,
            src: src.0,
            fields: fields.clone(),
            unique: *unique,
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
        } => VmInstruction::Call {
            dst: dst.0,
            callee: *callee,
            arguments: arguments.iter().map(|argument| argument.0).collect(),
        },
        MirInstruction::MakeCallable {
            dst,
            callee,
            captures,
            ..
        } => VmInstruction::MakeCallable {
            dst: dst.0,
            callee: *callee,
            captures: captures.iter().map(|capture| capture.0).collect(),
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
    }
}
fn lower_pattern(value: &MirPattern) -> VmPattern {
    match value {
        MirPattern::Any => VmPattern::Any,
        MirPattern::Literal(value) => VmPattern::Literal(value.clone()),
        MirPattern::Tuple(values) => VmPattern::Tuple(values.iter().map(lower_pattern).collect()),
        MirPattern::Record { definition, fields } => VmPattern::Record {
            definition: *definition,
            fields: lower_pattern_fields(fields),
        },
        MirPattern::Enum {
            definition,
            variant,
            fields,
        } => VmPattern::Enum {
            definition: *definition,
            variant: *variant,
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
        VmPattern::Literal(value) if literal_vm_type(value) == *subject => Ok(()),
        VmPattern::Literal(_) => Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: literal_vm_type(match pattern {
                VmPattern::Literal(value) => value,
                _ => unreachable!(),
            }),
            found: subject.clone(),
        }),
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
        VmPattern::Record { definition, fields }
        | VmPattern::Enum {
            definition, fields, ..
        } => match subject {
            VmType::Nominal {
                definition: actual, ..
            } if actual == definition => verify_pattern_fields(fields),
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
fn verify_pattern_fields(fields: &[VmPatternField]) -> Result<(), VmArtifactError> {
    let mut previous = None;
    for field in fields {
        if previous.is_some_and(|previous| previous >= field.index) {
            return Err(VmArtifactError::MalformedEncoding {
                message: "pattern fields are not strictly ordered",
            });
        }
        previous = Some(field.index);
        verify_pattern(&field.pattern, &field.ty)?;
    }
    Ok(())
}
fn literal_vm_type(value: &str) -> VmType {
    if matches!(value, "true" | "false") {
        VmType::Bool
    } else if value.starts_with('"') {
        VmType::Text
    } else if value.starts_with('\'') {
        VmType::Char
    } else if value.contains('.') || value.contains('e') || value.contains('E') {
        VmType::F64
    } else {
        VmType::I64
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
    effect_arguments: Vec<VmType>,
    operation: u32,
    payload_destinations: Vec<u32>,
    resume_type: VmType,
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
    effect_arguments: Vec<VmType>,
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

fn verify_function(function: &VmFunction) -> Result<(), VmArtifactError> {
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
            VmInstruction::ConstF64 { dst, .. } => {
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
                target,
            } => {
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
                    target: *target,
                    continuations: Vec::new(),
                });
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
                if frame.continuations.is_empty() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let found = register_type(function, *value)?;
                if found != frame.resume_type {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *value,
                        expected: frame.resume_type.clone(),
                        found,
                    });
                }
                let continuations = std::mem::take(&mut frame.continuations);
                for continuation in continuations {
                    let mut resumed_handlers = states.handlers.clone();
                    resumed_handlers.extend(continuation.above);
                    let mut resumed = VerifierState {
                        registers: continuation.registers,
                        snapshots: continuation.snapshots,
                        handlers: resumed_handlers,
                        pending_leave: continuation.pending_leave,
                    };
                    write(&mut resumed, continuation.dst)?;
                    propagate_state(&mut incoming, &mut worklist, continuation.target, &resumed)?;
                }
                advances = false;
            }
            VmInstruction::CaptureResumption { dst } => {
                let Some(frame) = states.handlers.last() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if frame.continuations.is_empty() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                let VmType::Callable { parameters, .. } = register_type(function, *dst)? else {
                    return Err(VmArtifactError::NotCallable { register: *dst });
                };
                let frame_id = frame.id;
                if parameters.as_slice() != [frame.resume_type.clone()] {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: VmType::Callable {
                            parameters: vec![frame.resume_type.clone()],
                            result: Box::new(VmType::Unit),
                        },
                        found: register_type(function, *dst)?,
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
                if frame.continuations.is_empty() {
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
                let continuations = std::mem::take(&mut frame.continuations);
                // A non-local snapshot transfer abandons frames installed
                // after the captured frame, then reinstates precisely the
                // frames saved with its continuation. This is the verifier
                // counterpart of the VM's deep-handler restoration rule.
                let prefix = states.handlers[..=index].to_vec();
                for continuation in continuations {
                    let mut resumed_handlers = prefix.clone();
                    resumed_handlers.extend(continuation.above);
                    let mut resumed = VerifierState {
                        registers: continuation.registers,
                        snapshots: continuation.snapshots,
                        handlers: resumed_handlers,
                        pending_leave: continuation.pending_leave,
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
                if frame.continuations.is_empty() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                expire_snapshot_brand(&mut states.snapshots, frame.id);
            }
            VmInstruction::Copy { dst, src } => {
                read(&states, *src)?;
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
                dst, src, unique, ..
            } => {
                read(&states, *src)?;
                let found = register_type(function, *dst)?;
                if !matches!(found, VmType::Reference { unique: actual, .. } if actual == *unique) {
                    return Err(VmArtifactError::TypeMismatch {
                        register: *dst,
                        expected: VmType::Reference {
                            unique: *unique,
                            referent: Box::new(VmType::Unit),
                        },
                        found,
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
            VmInstruction::AddI64 { dst, left, right }
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
                let VmType::Callable { parameters, result } = register_type(function, *callee)?
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
    F64(f64),
    Bool(bool),
    Char(char),
    Text(Arc<str>),
    Tuple(Arc<[VmValue]>),
    Array(Arc<[VmValue]>),
    Record {
        definition: DefKey,
        fields: Arc<[VmValue]>,
        signature: VmType,
    },
    Reference {
        target: u32,
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

#[derive(Clone)]
struct RuntimeHandlerFrame {
    id: u64,
    effect: DefKey,
    effect_arguments: Vec<VmType>,
    operation: u32,
    payload_destinations: Vec<u32>,
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
}

#[derive(Clone)]
struct RuntimePerformed {
    effect: DefKey,
    effect_arguments: Vec<VmType>,
    operation: u32,
    payloads: Vec<VmValue>,
}

impl VmValue {
    fn ty(&self) -> VmType {
        match self {
            Self::Unit => VmType::Unit,
            Self::I64(_) => VmType::I64,
            Self::F64(_) => VmType::F64,
            Self::Bool(_) => VmType::Bool,
            Self::Char(_) => VmType::Char,
            Self::Text(_) => VmType::Text,
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
) -> Result<VmValue, VmArtifactError> {
    let Some((field, rest)) = fields.split_first() else {
        return Ok(replacement);
    };
    match value {
        VmValue::Tuple(values) => {
            let mut values = values.to_vec();
            let slot = values
                .get_mut(*field as usize)
                .ok_or(VmArtifactError::InvalidRegister { register: *field })?;
            *slot = store_reference(slot, rest, replacement)?;
            Ok(VmValue::Tuple(values.into()))
        }
        VmValue::Array(values) => {
            let mut values = values.to_vec();
            let slot = values
                .get_mut(*field as usize)
                .ok_or(VmArtifactError::InvalidRegister { register: *field })?;
            *slot = store_reference(slot, rest, replacement)?;
            Ok(VmValue::Array(values.into()))
        }
        VmValue::Record {
            definition,
            fields: old,
            signature,
        } => {
            let mut fields = old.to_vec();
            let slot = fields
                .get_mut(*field as usize)
                .ok_or(VmArtifactError::InvalidRegister { register: *field })?;
            *slot = store_reference(slot, rest, replacement)?;
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
            let mut fields = old.to_vec();
            let slot = fields
                .get_mut(*field as usize)
                .ok_or(VmArtifactError::InvalidRegister { register: *field })?;
            *slot = store_reference(slot, rest, replacement)?;
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
) -> Result<VmValue, VmArtifactError> {
    if let VmValue::Reference {
        target,
        fields: parent_fields,
        unique: parent_unique,
        referent: parent_referent,
    } = value
    {
        if unique && !parent_unique {
            return Err(VmArtifactError::InvalidRegister { register: *target });
        }
        let mut path = parent_fields.to_vec();
        path.extend_from_slice(fields);
        return Ok(VmValue::Reference {
            target: *target,
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
        target: source,
        fields: fields.to_vec().into(),
        unique,
        referent: project_reference(value, fields)?.ty(),
    })
}

fn format_vm_value(value: &VmValue) -> String {
    match value {
        VmValue::Unit => "()".into(),
        VmValue::I64(value) => value.to_string(),
        VmValue::F64(value) => value.to_string(),
        VmValue::Bool(value) => value.to_string(),
        VmValue::Char(value) => format!("{value:?}"),
        VmValue::Text(value) => format!("{value:?}"),
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
        VmPattern::Record { definition, fields } => match value {
            VmValue::Record {
                definition: actual,
                fields: values,
                ..
            } if actual == definition => matches_pattern_fields(values, fields),
            _ => false,
        },
        VmPattern::Enum {
            definition,
            variant,
            fields,
        } => match value {
            VmValue::Enum {
                definition: actual,
                variant: actual_variant,
                fields: values,
                ..
            } if actual == definition && actual_variant == variant => {
                matches_pattern_fields(values, fields)
            }
            _ => false,
        },
    }
}
fn matches_pattern_fields(values: &[VmValue], fields: &[VmPatternField]) -> bool {
    fields.iter().all(|field| {
        values
            .get(field.index as usize)
            .is_some_and(|value| matches_pattern(value, &field.pattern))
    })
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
    text.replace('_', "").parse().ok()
}
fn parse_pattern_char(text: &str) -> Option<char> {
    let body = text.strip_prefix('\'')?.strip_suffix('\'')?;
    match body {
        "\\n" => Some('\n'),
        "\\r" => Some('\r'),
        "\\t" => Some('\t'),
        "\\\\" => Some('\\'),
        "\\'" => Some('\''),
        _ if !body.starts_with('\\') => {
            let mut values = body.chars();
            let value = values.next()?;
            values.next().is_none().then_some(value)
        }
        _ => None,
    }
}
fn parse_pattern_text(text: &str) -> Option<String> {
    let body = text.strip_prefix('"')?.strip_suffix('"')?;
    let mut output = String::new();
    let mut values = body.chars();
    while let Some(value) = values.next() {
        if value != '\\' {
            output.push(value);
            continue;
        }
        output.push(match values.next()? {
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            '\\' => '\\',
            '"' => '"',
            other => other,
        });
    }
    Some(output)
}
fn execute(function: &VmFunction) -> Result<VmValue, VmArtifactError> {
    let mut registers = vec![None; function.registers.len()];
    let mut handlers = Vec::<RuntimeHandlerFrame>::new();
    let mut next_handler_id = 0u64;
    let mut pc = 0usize;
    while let Some(instruction) = function.instructions.get(pc).cloned() {
        match instruction {
            VmInstruction::ConstUnit { dst } => registers[dst as usize] = Some(VmValue::Unit),
            VmInstruction::ConstI64 { dst, value } => {
                registers[dst as usize] = Some(VmValue::I64(value))
            }
            VmInstruction::ConstF64 { dst, bits } => {
                registers[dst as usize] = Some(VmValue::F64(f64::from_bits(bits)))
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
            VmInstruction::MakeTuple { dst, fields } => {
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
                let frame = &mut handlers[index];
                if frame.payload_destinations.len() != values.len() {
                    return Err(VmArtifactError::CallArity {
                        expected: frame.payload_destinations.len() as u32,
                        found: values.len() as u32,
                    });
                }
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
                });
                pc = frame.target as usize;
                continue;
            }
            VmInstruction::InstallHandler {
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                target,
                ..
            } => handlers.push(RuntimeHandlerFrame {
                id: {
                    let id = next_handler_id;
                    next_handler_id = next_handler_id.saturating_add(1);
                    id
                },
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                target,
                suspended: None,
            }),
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
                let Some(continuation) = frame.suspended.take() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if let Some(leave) = continuation.pending_leave.clone() {
                    registers = continuation.registers;
                    handlers.extend(continuation.above);
                    pc = complete_pending_leave(&mut registers, &mut handlers, leave)?;
                    continue;
                }
                registers = continuation.registers;
                registers[continuation.dst as usize] = Some(resumed);
                handlers.extend(continuation.above);
                pc = continuation.target;
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
                let continuation = handlers[index]
                    .suspended
                    .take()
                    .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                // Resumption is a non-local transfer. Frames installed after
                // the captured frame belong to the abandoned clause path;
                // only the deep frames recorded at the original `Perform`
                // are reinstated with the continuation.
                handlers.truncate(index + 1);
                if let Some(leave) = continuation.pending_leave.clone() {
                    registers = continuation.registers;
                    handlers.extend(continuation.above);
                    pc = complete_pending_leave(&mut registers, &mut handlers, leave)?;
                    continue;
                }
                registers = continuation.registers;
                registers[continuation.dst as usize] = Some(resumed);
                handlers.extend(continuation.above);
                pc = continuation.target;
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
            } => {
                registers[dst as usize] = Some(borrow_value(
                    src,
                    registers[src as usize].as_ref().expect("verified register"),
                    &fields,
                    unique,
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
                    registers[*target as usize]
                        .as_ref()
                        .expect("live reference target"),
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
                registers[dst as usize] = Some(VmValue::F64(
                    expect_f64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? + expect_f64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
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
                registers[dst as usize] = Some(VmValue::F64(
                    expect_f64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? - expect_f64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::MulF64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::F64(
                    expect_f64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? * expect_f64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::DivF64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::F64(
                    expect_f64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? / expect_f64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::RemF64 { dst, left, right } => {
                registers[dst as usize] = Some(VmValue::F64(
                    expect_f64(
                        registers[left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? % expect_f64(
                        registers[right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
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
            output.extend_from_slice(&(effect_arguments.len() as u64).to_le_bytes());
            for argument in effect_arguments {
                encode_type(argument, output);
            }
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
            target,
        } => {
            output.push(44);
            output.extend_from_slice(&effect.0.as_bytes());
            output.extend_from_slice(&(effect_arguments.len() as u64).to_le_bytes());
            for argument in effect_arguments {
                encode_type(argument, output);
            }
            output.extend_from_slice(&operation.to_le_bytes());
            output.extend_from_slice(&(payload_destinations.len() as u64).to_le_bytes());
            for destination in payload_destinations {
                output.extend_from_slice(&destination.to_le_bytes());
            }
            encode_type(resume_type, output);
            output.extend_from_slice(&target.to_le_bytes());
        }
        VmInstruction::UninstallHandler => output.push(45),
        VmInstruction::Resume { value } => {
            output.push(46);
            output.extend_from_slice(&value.to_le_bytes());
        }
        VmInstruction::Forward => output.push(47),
        VmInstruction::Cancel => output.push(48),
        VmInstruction::CaptureResumption { dst } => {
            output.push(49);
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
        } => {
            output.push(52);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&src.to_le_bytes());
            output.push(*unique as u8);
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
        VmInstruction::MakeCallable {
            dst,
            callee,
            captures,
        } => {
            output.push(29);
            output.extend_from_slice(&dst.to_le_bytes());
            output.extend_from_slice(&callee.0.as_bytes());
            output.extend_from_slice(&(captures.len() as u64).to_le_bytes());
            for capture in captures {
                output.extend_from_slice(&capture.to_le_bytes());
            }
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
        VmPattern::Record { definition, fields } => {
            output.push(3);
            output.extend_from_slice(&definition.0.as_bytes());
            encode_pattern_fields(fields, output);
        }
        VmPattern::Enum {
            definition,
            variant,
            fields,
        } => {
            output.push(4);
            output.extend_from_slice(&definition.0.as_bytes());
            output.extend_from_slice(&variant.to_le_bytes());
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
    let mut registers = vec![None; function.registers.len()];
    for (index, value) in arguments.iter().enumerate() {
        registers[index] = Some(value.clone());
    }
    let mut handlers = Vec::<RuntimeHandlerFrame>::new();
    let mut next_handler_id = 0u64;
    let mut pc = 0usize;
    while let Some(instruction) = function.instructions.get(pc) {
        budget.tick()?;
        match instruction {
            VmInstruction::ConstUnit { dst } => registers[*dst as usize] = Some(VmValue::Unit),
            VmInstruction::ConstI64 { dst, value } => {
                registers[*dst as usize] = Some(VmValue::I64(*value))
            }
            VmInstruction::ConstF64 { dst, bits } => {
                registers[*dst as usize] = Some(VmValue::F64(f64::from_bits(*bits)))
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
            VmInstruction::MakeTuple { dst, fields } => {
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
                let frame = &mut handlers[index];
                if frame.payload_destinations.len() != values.len() {
                    return Err(VmArtifactError::CallArity {
                        expected: frame.payload_destinations.len() as u32,
                        found: values.len() as u32,
                    });
                }
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
                });
                pc = frame.target as usize;
                continue;
            }
            VmInstruction::InstallHandler {
                effect,
                effect_arguments,
                operation,
                payload_destinations,
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
                    effect: *effect,
                    effect_arguments: effect_arguments.clone(),
                    operation: *operation,
                    payload_destinations: payload_destinations.clone(),
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
                let Some(continuation) = frame.suspended.take() else {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                };
                if let Some(leave) = continuation.pending_leave.clone() {
                    registers = continuation.registers;
                    handlers.extend(continuation.above);
                    pc = complete_pending_leave(&mut registers, &mut handlers, leave)?;
                    continue;
                }
                registers = continuation.registers;
                registers[continuation.dst as usize] = Some(resumed);
                handlers.extend(continuation.above);
                pc = continuation.target;
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
                let continuation = handlers[index]
                    .suspended
                    .take()
                    .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                // See the standalone-artifact interpreter above: an explicit
                // snapshot abandons dynamically newer frames before restoring
                // the continuation's original deep-frame suffix.
                handlers.truncate(index + 1);
                if let Some(leave) = continuation.pending_leave.clone() {
                    registers = continuation.registers;
                    handlers.extend(continuation.above);
                    pc = complete_pending_leave(&mut registers, &mut handlers, leave)?;
                    continue;
                }
                registers = continuation.registers;
                registers[continuation.dst as usize] = Some(resumed);
                handlers.extend(continuation.above);
                pc = continuation.target;
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
            } => {
                registers[*dst as usize] = Some(borrow_value(
                    *src,
                    registers[*src as usize]
                        .as_ref()
                        .expect("verified register"),
                    fields,
                    *unique,
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
                    registers[*target as usize]
                        .as_ref()
                        .expect("live reference target"),
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
                registers[*dst as usize] = Some(VmValue::F64(
                    expect_f64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? + expect_f64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
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
                registers[*dst as usize] = Some(VmValue::F64(
                    expect_f64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? - expect_f64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::MulF64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::F64(
                    expect_f64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? * expect_f64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::DivF64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::F64(
                    expect_f64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? / expect_f64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
            }
            VmInstruction::RemF64 { dst, left, right } => {
                registers[*dst as usize] = Some(VmValue::F64(
                    expect_f64(
                        registers[*left as usize]
                            .as_ref()
                            .expect("verified register"),
                    )? % expect_f64(
                        registers[*right as usize]
                            .as_ref()
                            .expect("verified register"),
                    )?,
                ))
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
            VmInstruction::Call {
                dst,
                callee,
                arguments,
            } => {
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
                registers[*dst as usize] = Some(execute_with_arguments(
                    program,
                    *callee,
                    &values,
                    depth + 1,
                    budget,
                )?);
            }
            VmInstruction::MakeCallable {
                dst,
                callee,
                captures,
            } => {
                let values = captures
                    .iter()
                    .map(|capture| {
                        registers[*capture as usize]
                            .clone()
                            .ok_or(VmArtifactError::ReadBeforeWrite { register: *capture })
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
                let mut values = captures.as_ref().to_vec();
                values.extend(arguments.iter().map(|argument| {
                    registers[*argument as usize]
                        .as_ref()
                        .expect("verified register")
                        .clone()
                }));
                registers[*dst as usize] = Some(execute_with_arguments(
                    program,
                    callee,
                    &values,
                    depth + 1,
                    budget,
                )?);
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
                if !handlers.is_empty() {
                    return Err(VmArtifactError::HandlerStillActive);
                }
                return Ok(registers[*value as usize]
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
struct ExecutionBudget {
    limits: VmExecutionLimits,
    instructions: u64,
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
}
