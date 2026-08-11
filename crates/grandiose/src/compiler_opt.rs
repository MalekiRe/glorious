//! Deterministic optimizer foundation for ownership-aware MIR.
//!
//! The initial passes are deliberately small.  They establish phase tracking,
//! structural validation, fixed scheduling, feature filtering, and transactional
//! budgets before transformations which need the richer flow analyses described
//! by `docs/mir-design.md` are enabled.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

use grandiose_vm::bytecode::{HandlerDef, Protocol};
use grandiose_vm::{
    BYTES, CHAR, Constant, F32, F64, I8, I16, I32, I64, I128, ISIZE, Primitive, TEXT, Type, TypeId,
    U8, U16, U32, U64, U128, UNIT, USIZE,
};

use super::{
    BasicBlock, BlockKind, BlockParam, BlockParamRole, CleanupAction, CleanupEdge, CleanupPlanFact,
    CleanupPlanId, DropGlueKind, Edge, FlowProvenance, Function, HandlerSiteFact, Instruction,
    InstructionKind, JoinSiteFact, LabelId, LoanId, LocalFact, MovePathId, MovePaths, Operand,
    OwnershipCategory, PerformSiteFact, Program, Projection, RegionId, Register, RegisterUseKind,
    ResumptionSiteFact, ScopeId, SourceInfoId, Terminator, UseMode, analysis,
};
use crate::compiler_mir::analyses::{
    AnalysisErrorKind, ControlFlowAnalysis, EdgeLiveness, PhysicalRegisterAllocation,
    RegisterClass, RegisterIntervals,
};
use crate::compiler_mir::mutation::{CheckedCfg, ResourceLimits, check_resource_limits};
use crate::compiler_regions as regions;
use crate::compiler_traits::HostImportRole;
use crate::span::Span;

#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub enum OptimizationLevel {
    O0,
    O1,
    #[default]
    O2,
    O3,
}

impl OptimizationLevel {
    fn at_least(self, other: Self) -> bool {
        self >= other
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub enum MirPhase {
    #[default]
    Raw,
    Owned,
    Cleanup,
    Optimized,
    Lowered,
}

/// Cheap, stable body-property mask. Bits are part of MIR fingerprints, so new
/// properties must use fresh bits and inference must not depend on hash order.
#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct FeatureBits(u32);

impl FeatureBits {
    pub const AGGREGATES: Self = Self(1 << 0);
    pub const INDIRECT_CALLS: Self = Self(1 << 1);
    pub const HANDLERS: Self = Self(1 << 2);
    pub const RESUMPTIONS: Self = Self(1 << 3);
    pub const DROPS: Self = Self(1 << 4);
    pub const LOANS: Self = Self(1 << 5);
    pub const SWITCHES: Self = Self(1 << 6);
    pub const TAIL_CALLS: Self = Self(1 << 7);
    pub const CONTROL_FLOW: Self = Self(1 << 8);

    pub const fn empty() -> Self {
        Self(0)
    }

    pub const fn bits(self) -> u32 {
        self.0
    }

    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    fn insert(&mut self, other: Self) {
        self.0 |= other.0;
    }
}

impl fmt::Debug for FeatureBits {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "FeatureBits({:#x})", self.0)
    }
}

/// FIFO worklist for dense compiler arenas. Scheduling an item already pending
/// is a no-op; popping it makes the item eligible to be scheduled again. This
/// is the common fixpoint discipline used by sparse register and block flows.
struct DenseWorklist {
    pending: VecDeque<usize>,
    scheduled: Vec<bool>,
}

impl DenseWorklist {
    fn new(capacity: usize) -> Self {
        Self {
            pending: VecDeque::new(),
            scheduled: vec![false; capacity],
        }
    }

    fn schedule(&mut self, index: usize) {
        if !self.scheduled[index] {
            self.scheduled[index] = true;
            self.pending.push_back(index);
        }
    }

    fn pop(&mut self) -> Option<usize> {
        let index = self.pending.pop_front()?;
        self.scheduled[index] = false;
        Some(index)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PassId {
    ValidateRawMir,
    ImportAndValidatePlaceFlow,
    ElaborateCleanup,
    ValidateCleanupMir,
    NormalizeCfg,
    SparseSimplify,
    ScalarizeLocals,
    SimplifyCleanup,
    GlobalSimplify,
    SpecializeDirectCalls,
    ScalarizeCallables,
    SpecializeControl,
    SpecializeCleanup,
    InlineByCost,
    EraseLoanProofsAndScalarizedReferences,
    FormTailCallsAndHoist,
    LowerRegistersAndEdges,
    LayoutAndPeephole,
    ValidateBytecodeInput,
    ValidateFinalArtifact,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PassOutcome {
    Unchanged,
    Changed,
    SkippedUnavailable,
    BudgetExhausted,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PassReport {
    pub pass: PassId,
    pub outcome: PassOutcome,
    pub work_units: u64,
}

/// Deterministic pass report. The MIR optimizer constructs the semantic pass
/// prefix; the enclosing compiler appends bytecode lowering, layout/peephole,
/// and final-artifact verification entries only after those stages actually
/// run. A named pass is never reported as successful speculatively.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OptimizationReport {
    pub level: OptimizationLevel,
    pub initial_operations: u64,
    pub final_operations: u64,
    pub passes: Vec<PassReport>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ValidationError {
    pub(crate) function: String,
    pub(crate) block: Option<u32>,
    pub(crate) message: String,
}

impl fmt::Display for ValidationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "function `{}`", self.function)?;
        if let Some(block) = self.block {
            write!(formatter, " block {block}")?;
        }
        write!(formatter, ": {}", self.message)
    }
}

impl std::error::Error for ValidationError {}

fn error(function: &Function, block: Option<u32>, message: impl Into<String>) -> ValidationError {
    ValidationError {
        function: function.name.clone(),
        block,
        message: message.into(),
    }
}

fn operation_count(program: &Program) -> u64 {
    program
        .functions
        .iter()
        .flat_map(|function| &function.blocks)
        .map(|block| block.statements.len() as u64 + 1)
        .sum()
}

fn body_size(function: &Function) -> u64 {
    function
        .blocks
        .iter()
        .map(|block| block.statements.len() as u64 + 1)
        .sum()
}

fn successors(terminator: &Terminator) -> Vec<u32> {
    let mut result = Vec::new();
    for_each_edge(terminator, |edge| result.push(edge.target));
    result
}

fn for_each_edge(terminator: &Terminator, mut visit: impl FnMut(&Edge)) {
    match terminator {
        Terminator::Goto(edge) => visit(edge),
        Terminator::Switch {
            cases, otherwise, ..
        } => {
            for (_, edge) in cases {
                visit(edge);
            }
            visit(otherwise);
        }
        Terminator::Call { normal, .. }
        | Terminator::CallSelf { normal, .. }
        | Terminator::CallKnownReceiver { normal, .. }
        | Terminator::HostCall { normal, .. }
        | Terminator::CallIndirect { normal, .. }
        | Terminator::Handle { normal, .. }
        | Terminator::Resume { normal, .. }
        | Terminator::Cancel { normal, .. } => visit(normal),
        Terminator::Perform { resume, .. } => {
            if let Some(edge) = resume {
                visit(edge);
            }
        }
        Terminator::Leave { target, .. } => visit(target),
        Terminator::Return { .. }
        | Terminator::TailResume { .. }
        | Terminator::TailCall { .. }
        | Terminator::TailCallSelf { .. }
        | Terminator::TailCallKnownReceiver { .. }
        | Terminator::TailCallIndirect { .. }
        | Terminator::Abort { .. }
        | Terminator::Unreachable => {}
    }
}

fn for_each_edge_mut(terminator: &mut Terminator, mut visit: impl FnMut(&mut Edge)) {
    match terminator {
        Terminator::Goto(edge) => visit(edge),
        Terminator::Switch {
            cases, otherwise, ..
        } => {
            for (_, edge) in cases {
                visit(edge);
            }
            visit(otherwise);
        }
        Terminator::Call { normal, .. }
        | Terminator::CallSelf { normal, .. }
        | Terminator::CallKnownReceiver { normal, .. }
        | Terminator::HostCall { normal, .. }
        | Terminator::CallIndirect { normal, .. }
        | Terminator::Handle { normal, .. }
        | Terminator::Resume { normal, .. }
        | Terminator::Cancel { normal, .. } => visit(normal),
        Terminator::Perform { resume, .. } => {
            if let Some(edge) = resume {
                visit(edge);
            }
        }
        Terminator::Leave { target, .. } => visit(target),
        Terminator::Return { .. }
        | Terminator::TailResume { .. }
        | Terminator::TailCall { .. }
        | Terminator::TailCallSelf { .. }
        | Terminator::TailCallKnownReceiver { .. }
        | Terminator::TailCallIndirect { .. }
        | Terminator::Abort { .. }
        | Terminator::Unreachable => {}
    }
}

pub(crate) fn infer_feature_bits(function: &Function) -> FeatureBits {
    let mut features = FeatureBits::empty();
    if function.blocks.len() > 1 {
        features.insert(FeatureBits::CONTROL_FLOW);
    }
    for block in &function.blocks {
        for statement in &block.statements {
            match &statement.kind {
                InstructionKind::Construct { .. }
                | InstructionKind::MakeBindingPack { .. }
                | InstructionKind::ProjectCopy { .. }
                | InstructionKind::ProjectMove { .. }
                | InstructionKind::Deconstruct { .. }
                | InstructionKind::EnumTag { .. } => features.insert(FeatureBits::AGGREGATES),
                InstructionKind::Borrow { .. }
                | InstructionKind::ProjectBorrow { .. }
                | InstructionKind::Reborrow { .. }
                | InstructionKind::DerefCopy { .. }
                | InstructionKind::DerefReborrow { .. }
                | InstructionKind::DerefMove { .. }
                | InstructionKind::DerefStore { .. }
                | InstructionKind::EndBorrow { .. } => features.insert(FeatureBits::LOANS),
                InstructionKind::MakeHandler { .. } | InstructionKind::MakeHandlerShared { .. } => {
                    features.insert(FeatureBits::HANDLERS)
                }
                InstructionKind::Drop { .. } => features.insert(FeatureBits::DROPS),
                InstructionKind::LabelPush { .. } | InstructionKind::LabelPop { .. } => {
                    features.insert(FeatureBits::CONTROL_FLOW)
                }
                InstructionKind::Const { .. }
                | InstructionKind::Copy { .. }
                | InstructionKind::Move { .. }
                | InstructionKind::Primitive { .. }
                | InstructionKind::MakeCallable { .. } => {}
            }
        }
        match &block.terminator {
            Terminator::Switch { .. } => features.insert(FeatureBits::SWITCHES),
            Terminator::CallIndirect { .. } => features.insert(FeatureBits::INDIRECT_CALLS),
            Terminator::Handle { .. } => features.insert(FeatureBits::HANDLERS),
            Terminator::Perform { resume, .. } => {
                features.insert(FeatureBits::HANDLERS);
                if resume.is_some() {
                    features.insert(FeatureBits::RESUMPTIONS);
                }
            }
            Terminator::Resume { .. } | Terminator::Cancel { .. } => {
                features.insert(FeatureBits::RESUMPTIONS)
            }
            Terminator::TailCall { .. }
            | Terminator::TailCallSelf { .. }
            | Terminator::TailCallKnownReceiver { .. } => features.insert(FeatureBits::TAIL_CALLS),
            Terminator::TailResume { .. } => {
                features.insert(FeatureBits::RESUMPTIONS);
                features.insert(FeatureBits::TAIL_CALLS);
            }
            Terminator::TailCallIndirect { .. } => {
                features.insert(FeatureBits::INDIRECT_CALLS);
                features.insert(FeatureBits::TAIL_CALLS);
            }
            Terminator::Leave { .. } => features.insert(FeatureBits::CONTROL_FLOW),
            Terminator::Goto(_)
            | Terminator::Return { .. }
            | Terminator::Call { .. }
            | Terminator::CallSelf { .. }
            | Terminator::CallKnownReceiver { .. }
            | Terminator::HostCall { .. }
            | Terminator::Abort { .. }
            | Terminator::Unreachable => {}
        }
    }
    features
}

fn constant_type(value: &Constant) -> TypeId {
    match value {
        Constant::Unit => UNIT,
        Constant::U8(_) => U8,
        Constant::U16(_) => U16,
        Constant::U32(_) => U32,
        Constant::U64(_) => U64,
        Constant::U128(_) => U128,
        Constant::I8(_) => I8,
        Constant::I16(_) => I16,
        Constant::I32(_) => I32,
        Constant::I64(_) => I64,
        Constant::I128(_) => I128,
        Constant::Usize(_) => USIZE,
        Constant::Isize(_) => ISIZE,
        Constant::F32(_) => F32,
        Constant::F64(_) => F64,
        Constant::Char(_) => CHAR,
        Constant::Text(_) => TEXT,
        Constant::Bytes(_) => BYTES,
    }
}

fn operand_type(
    function: &Function,
    block: u32,
    operand: &Operand,
) -> Result<TypeId, ValidationError> {
    function
        .register_types
        .get(operand.register as usize)
        .copied()
        .ok_or_else(|| {
            error(
                function,
                Some(block),
                format!("operand r{} is out of range", operand.register),
            )
        })
}

fn register_type(
    function: &Function,
    block: u32,
    register: Register,
) -> Result<TypeId, ValidationError> {
    function
        .register_types
        .get(register as usize)
        .copied()
        .ok_or_else(|| {
            error(
                function,
                Some(block),
                format!("register r{register} is out of range"),
            )
        })
}

fn validate_edge(
    function: &Function,
    blocks: &BTreeMap<u32, &BasicBlock>,
    source: u32,
    edge: &Edge,
    implicit_result: Option<(BlockParamRole, Register)>,
) -> Result<(), ValidationError> {
    let target = blocks.get(&edge.target).ok_or_else(|| {
        error(
            function,
            Some(source),
            format!("edge targets missing block {}", edge.target),
        )
    })?;
    let skip = usize::from(implicit_result.is_some());
    if let Some((role, result)) = implicit_result {
        let Some(first) = target.params.first() else {
            return Err(error(
                function,
                Some(source),
                format!(
                    "edge to block {} is missing its {role:?} parameter",
                    edge.target
                ),
            ));
        };
        if first.role != role {
            return Err(error(
                function,
                Some(source),
                format!(
                    "edge to block {} expected first parameter role {role:?}",
                    edge.target
                ),
            ));
        }
        if first.register != result {
            return Err(error(
                function,
                Some(source),
                format!(
                    "edge to block {} carries result r{result}, but its {role:?} parameter is r{}",
                    edge.target, first.register
                ),
            ));
        }
    }
    if edge.args.len() + skip != target.params.len() {
        return Err(error(
            function,
            Some(source),
            format!(
                "edge to block {} has {} explicit arguments for {} parameters",
                edge.target,
                edge.args.len(),
                target.params.len()
            ),
        ));
    }
    let mut moved_sources = BTreeSet::new();
    for (argument, parameter) in edge.args.iter().zip(target.params.iter().skip(skip)) {
        if argument.mode == UseMode::Move && !moved_sources.insert(argument.register) {
            return Err(error(
                function,
                Some(source),
                format!(
                    "edge to block {} moves r{} more than once; arguments={:?}; parameters={:?}",
                    edge.target, argument.register, edge.args, target.params
                ),
            ));
        }
        let actual = operand_type(function, source, argument)?;
        if actual != parameter.ty {
            return Err(error(
                function,
                Some(source),
                format!(
                    "edge argument type t{actual} does not match parameter type t{}",
                    parameter.ty
                ),
            ));
        }
    }
    Ok(())
}

/// Validate the compact MIR invariants required by the currently enabled
/// transformations. Rich ownership facts remain a prerequisite for enabling
/// the later optimizer passes.
pub(crate) fn validate_program(
    program: &Program,
    types: &[Type],
    expected_phase: MirPhase,
) -> Result<(), ValidationError> {
    let mut declarations = BTreeSet::new();
    for function in &program.functions {
        if !declarations.insert(function.declaration) {
            return Err(error(
                function,
                None,
                format!("duplicate function declaration {}", function.declaration),
            ));
        }
    }
    for function in &program.functions {
        check_resource_limits(function, ResourceLimits::default()).map_err(|mutation| {
            error(
                function,
                mutation.block.map(|block| block.0),
                mutation.to_string(),
            )
        })?;
        if function.phase != expected_phase {
            return Err(error(
                function,
                None,
                format!(
                    "has phase {:?}, expected {expected_phase:?}",
                    function.phase
                ),
            ));
        }
        for (label, ty) in [
            ("result", function.result),
            ("receiver", function.receiver_type),
        ] {
            if ty as usize >= types.len() {
                return Err(error(
                    function,
                    None,
                    format!("{label} type t{ty} is out of range"),
                ));
            }
        }
        if function
            .params
            .iter()
            .chain(&function.register_types)
            .any(|ty| *ty as usize >= types.len())
        {
            return Err(error(
                function,
                None,
                "parameter or register type is out of range",
            ));
        }
        if function.receiver_mode.is_some()
            && function.register_types.first().copied() != Some(function.receiver_type)
        {
            return Err(error(
                function,
                None,
                "receiver ABI register r0 is missing or has the wrong type",
            ));
        }
        for (index, expected) in function.params.iter().enumerate() {
            let register = index + 1;
            if function.register_types.get(register).copied() != Some(*expected) {
                return Err(error(
                    function,
                    None,
                    format!(
                        "parameter ABI register r{register} does not have parameter type t{expected}"
                    ),
                ));
            }
        }
        let mut blocks = BTreeMap::new();
        for block in &function.blocks {
            if blocks.insert(block.id, block).is_some() {
                return Err(error(function, Some(block.id), "duplicate block ID"));
            }
        }
        if !blocks.contains_key(&function.entry) {
            return Err(error(
                function,
                None,
                format!("entry block {} is missing", function.entry),
            ));
        }
        let mut definitions = BTreeMap::<Register, String>::new();
        let mut definition_blocks = BTreeMap::<Register, u32>::new();
        if function.receiver_mode.is_some() {
            definitions.insert(0, "receiver ABI register".into());
        }
        for register in 1..=function.params.len() as Register {
            definitions.insert(register, format!("parameter ABI register r{register}"));
        }
        for block in &function.blocks {
            let mut physically_empty = BTreeSet::new();
            let lowered_backedge_assignments = matches!(
                expected_phase,
                MirPhase::Cleanup | MirPhase::Optimized | MirPhase::Lowered
            )
            .then(|| lowered_self_tail_assignment_start(function, block))
            .flatten();
            let mut params = BTreeSet::new();
            for param in &block.params {
                let actual = register_type(function, block.id, param.register)?;
                if actual != param.ty {
                    return Err(error(
                        function,
                        Some(block.id),
                        "block parameter register/type mismatch",
                    ));
                }
                if !params.insert(param.register) {
                    return Err(error(
                        function,
                        Some(block.id),
                        "duplicate block parameter register",
                    ));
                }
                record_definition(
                    function,
                    block.id,
                    &mut definitions,
                    param.register,
                    format!("block {} parameter", block.id),
                )?;
                definition_blocks.insert(param.register, block.id);
            }
            for (index, statement) in block.statements.iter().enumerate() {
                if let Some(dst) = statement.kind.destination() {
                    // ABI parameters are source-storage `Place` locals in the
                    // compact MIR. Pattern fallback may exhaustively move an
                    // aggregate parameter and reconstruct that same place so
                    // an outer handler can receive the original payload. The
                    // artifact ownership verifier proves the place is empty at
                    // each store; all other destinations remain SSA-unique.
                    let reconstructs_parameter_place = matches!(
                        statement.kind,
                        InstructionKind::Construct { dst: place, ty, .. }
                            if place == dst
                                && (1..=function.params.len() as Register).contains(&place)
                                && function.register_types[place as usize] == ty
                    );
                    // Literal/refinement tests temporarily open aggregate
                    // shells and reconstruct the root in place. The root can
                    // be a call-derived temporary rather than an ABI
                    // parameter; only treat that store as reinitialization
                    // when this block has already physically consumed it.
                    let reconstructs_consumed_place = matches!(
                        statement.kind,
                        InstructionKind::Construct { dst: place, ty, .. }
                            if place == dst
                                && physically_empty.remove(&place)
                                && function.register_types[place as usize] == ty
                    );
                    let exempt_definition = reconstructs_parameter_place
                        || reconstructs_consumed_place
                        || lowered_backedge_assignments.is_some_and(|start| index >= start);
                    if !exempt_definition {
                        if expected_phase == MirPhase::Lowered
                            && physically_empty.remove(&dst)
                            && definition_blocks.get(&dst) == Some(&block.id)
                        {
                            definitions.remove(&dst);
                        }
                        record_definition(
                            function,
                            block.id,
                            &mut definitions,
                            dst,
                            format!("{:?} destination in block {}", statement.kind, block.id),
                        )?;
                        definition_blocks.insert(dst, block.id);
                    }
                }
                // Even definition-exempt stores can consume their inputs. In
                // particular, reconstructing a pattern-test parameter shell
                // moves every projected field back into that place; those
                // now-empty slots are then eligible for verified physical
                // reuse by later constants and temporaries in the same block.
                physically_empty.extend(instruction_consumed_registers(&statement.kind));
            }
            validate_statements(function, block, program, types)?;
            validate_terminator(function, block, &blocks, program, types)?;
        }
        for &register in &function.return_cleanup {
            register_type(function, function.entry, register)?;
        }
        let inferred = infer_feature_bits(function);
        if expected_phase != MirPhase::Raw && function.features != inferred {
            return Err(error(
                function,
                None,
                format!(
                    "stale feature bits {:?}; inferred {inferred:?}",
                    function.features
                ),
            ));
        }
    }
    Ok(())
}

#[allow(dead_code)]
fn used_registers(block: &BasicBlock) -> Vec<Register> {
    let mut used = Vec::new();
    for statement in &block.statements {
        statement
            .kind
            .for_each_register_use(|register, _| used.push(register));
    }
    block
        .terminator
        .for_each_register_use(|register, _| used.push(register));
    used
}

/// Recognize the one deliberately non-SSA form introduced immediately before
/// bytecode lowering: a self-tail edge snapshots every argument into a fresh
/// temporary and then assigns those temporaries to the ABI parameter places.
/// Returning only the start of the ABI-assignment suffix keeps all other
/// register definitions subject to the ordinary uniqueness rule.
fn lowered_self_tail_assignment_start(function: &Function, block: &BasicBlock) -> Option<usize> {
    let Terminator::Goto(Edge { target, args }) = &block.terminator else {
        return None;
    };
    let count = function.params.len();
    if *target != function.entry
        || !args.is_empty()
        || count == 0
        || block.statements.len() < 2 * count
    {
        return None;
    }
    let snapshot_start = block.statements.len() - 2 * count;
    let assignment_start = block.statements.len() - count;
    let snapshots = &block.statements[snapshot_start..assignment_start];
    let assignments = &block.statements[assignment_start..];
    let first_fresh = 1 + count as Register;
    let mut fresh = BTreeSet::new();
    for (index, (snapshot, assignment)) in snapshots.iter().zip(assignments).enumerate() {
        let InstructionKind::Move {
            dst: temporary,
            src: snapshot_source,
        } = &snapshot.kind
        else {
            return None;
        };
        let InstructionKind::Move {
            dst: parameter,
            src: assignment_source,
        } = &assignment.kind
        else {
            return None;
        };
        if *temporary < first_fresh
            || !fresh.insert(*temporary)
            || snapshot_source.mode != UseMode::Move
            || assignment_source.mode != UseMode::Move
            || assignment_source.register != *temporary
            || *parameter != index as Register + 1
            || register_type(function, block.id, *temporary).ok()
                != register_type(function, block.id, *parameter).ok()
        {
            return None;
        }
    }
    Some(assignment_start)
}

fn instruction_consumed_registers(instruction: &InstructionKind) -> BTreeSet<Register> {
    let mut consumed = BTreeSet::new();
    instruction.for_each_register_use(|register, kind| {
        if kind == RegisterUseKind::Consume {
            consumed.insert(register);
        }
    });
    consumed
}

fn record_definition(
    function: &Function,
    block: u32,
    definitions: &mut BTreeMap<Register, String>,
    register: Register,
    origin: String,
) -> Result<(), ValidationError> {
    register_type(function, block, register)?;
    if let Some(previous) = definitions.insert(register, origin.clone()) {
        return Err(error(
            function,
            Some(block),
            format!("register r{register} is defined by both {previous} and {origin}"),
        ));
    }
    Ok(())
}

fn validate_statements(
    function: &Function,
    block: &BasicBlock,
    program: &Program,
    types: &[Type],
) -> Result<(), ValidationError> {
    let ty = |register| register_type(function, block.id, register);
    let operand = |value: &Operand| operand_type(function, block.id, value);
    for statement in &block.statements {
        match &statement.kind {
            InstructionKind::Const { dst, value } => {
                if ty(*dst)? != constant_type(value) {
                    return Err(error(
                        function,
                        Some(block.id),
                        "constant destination type mismatch",
                    ));
                }
            }
            InstructionKind::Copy { dst, src } | InstructionKind::Move { dst, src } => {
                if ty(*dst)? != operand(src)? {
                    return Err(error(function, Some(block.id), "copy/move type mismatch"));
                }
            }
            InstructionKind::Borrow { dst, src, unique }
            | InstructionKind::Reborrow { dst, src, unique } => {
                let source = ty(*src)?;
                let referent = if matches!(&statement.kind, InstructionKind::Reborrow { .. }) {
                    match types[source as usize].representation() {
                        Type::RefShared { referent } | Type::RefUnique { referent } => *referent,
                        _ => {
                            return Err(error(
                                function,
                                Some(block.id),
                                "reborrow source is not a reference",
                            ));
                        }
                    }
                } else {
                    source
                };
                let expected = if *unique {
                    Type::RefUnique { referent }
                } else {
                    Type::RefShared { referent }
                };
                if types[ty(*dst)? as usize].representation() != &expected {
                    return Err(error(
                        function,
                        Some(block.id),
                        "borrow destination type mismatch",
                    ));
                }
            }
            InstructionKind::DerefCopy { dst, src } => {
                let referent = match types[ty(*src)? as usize].representation() {
                    Type::RefShared { referent } | Type::RefUnique { referent } => *referent,
                    _ => {
                        return Err(error(
                            function,
                            Some(block.id),
                            "DerefCopy source is not a reference",
                        ));
                    }
                };
                if ty(*dst)? != referent || !types[referent as usize].claimed_duplicable() {
                    return Err(error(
                        function,
                        Some(block.id),
                        "DerefCopy requires a duplicable referent destination",
                    ));
                }
            }
            InstructionKind::DerefReborrow { dst, src, unique } => {
                let outer = match types[ty(*src)? as usize].representation() {
                    Type::RefUnique { referent } => *referent,
                    Type::RefShared { referent } if !*unique => *referent,
                    _ => {
                        return Err(error(
                            function,
                            Some(block.id),
                            "DerefReborrow source lacks compatible outer reference authority",
                        ));
                    }
                };
                let inner = match types[outer as usize].representation() {
                    Type::RefUnique { referent } => *referent,
                    Type::RefShared { referent } if !*unique => *referent,
                    _ => {
                        return Err(error(
                            function,
                            Some(block.id),
                            "DerefReborrow referent is not a compatible stored reference",
                        ));
                    }
                };
                let expected = if *unique {
                    Type::RefUnique { referent: inner }
                } else {
                    Type::RefShared { referent: inner }
                };
                if types[ty(*dst)? as usize].representation() != &expected {
                    return Err(error(
                        function,
                        Some(block.id),
                        "DerefReborrow destination type mismatch",
                    ));
                }
            }
            InstructionKind::DerefMove { dst, src } => {
                let referent = match types[ty(*src)? as usize].representation() {
                    Type::RefUnique { referent } => *referent,
                    _ => {
                        return Err(error(
                            function,
                            Some(block.id),
                            "DerefMove source is not a unique reference",
                        ));
                    }
                };
                if ty(*dst)? != referent {
                    return Err(error(
                        function,
                        Some(block.id),
                        "DerefMove destination does not match its referent",
                    ));
                }
            }
            InstructionKind::DerefStore { dst, src } => {
                let referent = match types[ty(*dst)? as usize].representation() {
                    Type::RefUnique { referent } => *referent,
                    _ => {
                        return Err(error(
                            function,
                            Some(block.id),
                            "DerefStore destination is not a unique reference",
                        ));
                    }
                };
                if operand(src)? != referent {
                    return Err(error(
                        function,
                        Some(block.id),
                        "DerefStore source does not match its referent",
                    ));
                }
            }
            InstructionKind::ProjectBorrow { dst, src, .. } => {
                ty(*dst)?;
                ty(*src)?;
            }
            InstructionKind::EndBorrow { reference } => {
                let reference = ty(*reference)?;
                if !matches!(
                    types[reference as usize].representation(),
                    Type::RefShared { .. } | Type::RefUnique { .. }
                ) {
                    return Err(error(
                        function,
                        Some(block.id),
                        "EndBorrow operand is not a reference",
                    ));
                }
            }
            InstructionKind::Construct {
                dst,
                ty: made,
                fields,
                ..
            } => {
                if *made as usize >= types.len() || ty(*dst)? != *made {
                    return Err(error(
                        function,
                        Some(block.id),
                        "constructed type is invalid or mismatched",
                    ));
                }
                for field in fields {
                    operand(field)?;
                }
            }
            InstructionKind::MakeBindingPack {
                dst,
                binding_type,
                payloads,
            } => {
                if *binding_type as usize >= types.len() || ty(*dst)? != *binding_type {
                    return Err(error(
                        function,
                        Some(block.id),
                        "binding-pack destination type mismatch",
                    ));
                }
                if !matches!(
                    types[*binding_type as usize].representation(),
                    Type::BindingPack { .. }
                ) {
                    return Err(error(
                        function,
                        Some(block.id),
                        "MakeBindingPack type is not a binding pack",
                    ));
                }
                for payload in payloads {
                    operand(payload)?;
                }
            }
            InstructionKind::ProjectCopy { dst, src, .. }
            | InstructionKind::ProjectMove { dst, src, .. } => {
                ty(*dst)?;
                operand(src)?;
            }
            InstructionKind::Deconstruct { src } => {
                let source = ty(*src)?;
                if !matches!(
                    types[source as usize].representation(),
                    Type::Tuple { .. } | Type::Struct { .. } | Type::Enum { .. }
                ) {
                    return Err(error(
                        function,
                        Some(block.id),
                        "Deconstruct source is not an aggregate",
                    ));
                }
            }
            InstructionKind::EnumTag { dst, src } => {
                if ty(*dst)? != U32 {
                    return Err(error(
                        function,
                        Some(block.id),
                        "enum tag destination is not u32",
                    ));
                }
                let source = ty(*src)?;
                let source = match types[source as usize].representation() {
                    Type::RefShared { referent } | Type::RefUnique { referent } => *referent,
                    _ => source,
                };
                if !matches!(types[source as usize].representation(), Type::Enum { .. }) {
                    return Err(error(
                        function,
                        Some(block.id),
                        "EnumTag source is not an enum",
                    ));
                }
            }
            InstructionKind::Primitive { dst, args, .. } => {
                ty(*dst)?;
                for argument in args {
                    operand(argument)?;
                }
            }
            InstructionKind::MakeCallable {
                dst,
                callable_type,
                function: target,
                captures,
            } => {
                if *callable_type as usize >= types.len() || ty(*dst)? != *callable_type {
                    return Err(error(
                        function,
                        Some(block.id),
                        "callable destination type mismatch",
                    ));
                }
                let Type::Callable {
                    signature,
                    capture_type,
                    receiver_mode,
                    ..
                } = types[*callable_type as usize].representation()
                else {
                    return Err(error(
                        function,
                        Some(block.id),
                        "MakeCallable type is not callable",
                    ));
                };
                let target = direct_target(program, *target).ok_or_else(|| {
                    error(
                        function,
                        Some(block.id),
                        format!("MakeCallable target {target} is missing"),
                    )
                })?;
                let Some(target_mode) = target.receiver_mode else {
                    return Err(error(
                        function,
                        Some(block.id),
                        "MakeCallable target has no receiver ABI",
                    ));
                };
                if signature.params != target.params
                    || signature.result != target.result
                    || signature.outward_protocols != target.outward_protocols
                    || *receiver_mode != target_mode
                {
                    return Err(error(
                        function,
                        Some(block.id),
                        "MakeCallable descriptor does not match target signature",
                    ));
                }
                let expected_capture =
                    receiver_capture_type(types, target_mode, target.receiver_type).ok_or_else(
                        || {
                            error(
                                function,
                                Some(block.id),
                                "MakeCallable target receiver type is inconsistent with its mode",
                            )
                        },
                    )?;
                if *capture_type != expected_capture {
                    return Err(error(
                        function,
                        Some(block.id),
                        "MakeCallable descriptor capture type does not match target receiver",
                    ));
                }
                let fields = capture_fields(types, *capture_type).ok_or_else(|| {
                    error(
                        function,
                        Some(block.id),
                        "MakeCallable capture layout is not constructible",
                    )
                })?;
                if fields.len() != captures.len() {
                    return Err(error(
                        function,
                        Some(block.id),
                        "MakeCallable capture count does not match its layout",
                    ));
                }
                for (capture, expected) in captures.iter().zip(fields) {
                    if operand(capture)? != expected {
                        return Err(error(
                            function,
                            Some(block.id),
                            "MakeCallable capture type does not match its layout",
                        ));
                    }
                }
            }
            InstructionKind::MakeHandler { dst, clauses, .. } => {
                ty(*dst)?;
                for clause in clauses {
                    operand(clause)?;
                }
            }
            InstructionKind::MakeHandlerShared { dst, captures, .. } => {
                ty(*dst)?;
                for capture in captures {
                    operand(capture)?;
                }
            }
            InstructionKind::LabelPush {
                label,
                result,
                target,
            } => {
                let fact = function.flow.labels.get(label.index()).ok_or_else(|| {
                    error(function, Some(block.id), "LabelPush label is out of range")
                })?;
                let destination = function
                    .blocks
                    .iter()
                    .find(|candidate| candidate.id == *target)
                    .ok_or_else(|| {
                        error(
                            function,
                            Some(block.id),
                            format!(
                                "LabelPush target block {target} is missing from {:?}",
                                function
                                    .blocks
                                    .iter()
                                    .map(|block| block.id)
                                    .collect::<Vec<_>>()
                            ),
                        )
                    })?;
                if fact.destination != *target
                    || ty(*result)? != fact.result_type
                    || destination.params.first()
                        != Some(&BlockParam {
                            register: *result,
                            ty: fact.result_type,
                            role: BlockParamRole::ProtectedExitValue,
                        })
                    || destination.params[1..]
                        .iter()
                        .any(|parameter| parameter.role != BlockParamRole::Ordinary)
                {
                    return Err(error(
                        function,
                        Some(block.id),
                        "LabelPush disagrees with its label fact or protected-exit destination",
                    ));
                }
            }
            InstructionKind::LabelPop { label } => {
                if function.flow.labels.get(label.index()).is_none() {
                    return Err(error(
                        function,
                        Some(block.id),
                        "LabelPop label is out of range",
                    ));
                }
            }
            InstructionKind::Drop { owner } => {
                operand(owner)?;
            }
        }
    }
    Ok(())
}

fn receiver_capture_type(types: &[Type], mode: u32, receiver: TypeId) -> Option<TypeId> {
    match (mode, types.get(receiver as usize)?.representation()) {
        (0, Type::RefShared { referent }) | (1, Type::RefUnique { referent }) => Some(*referent),
        (2, _) => Some(receiver),
        _ => None,
    }
}

fn capture_fields(types: &[Type], capture: TypeId) -> Option<Vec<TypeId>> {
    if capture == UNIT {
        return Some(Vec::new());
    }
    let fields = match types.get(capture as usize)?.representation() {
        Type::Tuple { fields, .. } => fields.clone(),
        Type::Struct { fields, .. } => fields.iter().map(|field| field.ty).collect(),
        _ => return None,
    };
    Some(
        fields
            .into_iter()
            .filter(|field| {
                !matches!(
                    types.get(*field as usize).map(Type::representation),
                    Some(Type::Available { .. })
                )
            })
            .collect(),
    )
}

fn direct_target(program: &Program, id: u32) -> Option<&Function> {
    program
        .functions
        .iter()
        .find(|function| function.declaration == id)
}

fn validate_direct_call(
    function: &Function,
    block: u32,
    program: &Program,
    target: u32,
    args: &[Operand],
    result: Option<Register>,
    tail: bool,
) -> Result<(), ValidationError> {
    let called = direct_target(program, target).ok_or_else(|| {
        error(
            function,
            Some(block),
            format!("direct call target {target} is missing"),
        )
    })?;
    if called.params.len() != args.len() {
        return Err(error(
            function,
            Some(block),
            "direct call argument count mismatch",
        ));
    }
    if args.iter().any(|argument| argument.mode != UseMode::Move) {
        return Err(error(
            function,
            Some(block),
            "direct calls and tail calls must transfer every argument by move",
        ));
    }
    for (argument, expected) in args.iter().zip(&called.params) {
        if operand_type(function, block, argument)? != *expected {
            return Err(error(
                function,
                Some(block),
                "direct call argument type mismatch",
            ));
        }
    }
    if tail && called.result != function.result {
        return Err(error(
            function,
            Some(block),
            "tail-call result type does not match its caller",
        ));
    }
    match (result, called.result == UNIT || called.no_return || tail) {
        (Some(register), _) if register_type(function, block, register)? != called.result => Err(
            error(function, Some(block), "direct call result type mismatch"),
        ),
        (None, false) => Err(error(
            function,
            Some(block),
            "value-returning call has no result register",
        )),
        _ => Ok(()),
    }
}

fn validate_known_callable_target(
    function: &Function,
    block: u32,
    program: &Program,
    types: &[Type],
    callable_ty: TypeId,
    known_function: Option<u32>,
) -> Result<(), ValidationError> {
    let Some(target_id) = known_function else {
        return Ok(());
    };
    let called = direct_target(program, target_id).ok_or_else(|| {
        error(
            function,
            Some(block),
            format!("known indirect-call target {target_id} is missing"),
        )
    })?;
    let Type::Callable {
        signature,
        capture_type,
        receiver_mode,
        ..
    } = types[callable_ty as usize].representation()
    else {
        return Err(error(
            function,
            Some(block),
            "known indirect-call target is attached to a non-callable operand",
        ));
    };
    let Some(target_mode) = called.receiver_mode else {
        return Err(error(
            function,
            Some(block),
            "known indirect-call target has no receiver ABI",
        ));
    };
    let expected_capture = receiver_capture_type(types, target_mode, called.receiver_type)
        .ok_or_else(|| {
            error(
                function,
                Some(block),
                "known indirect-call target receiver type is inconsistent with its mode",
            )
        })?;
    if signature.params != called.params
        || signature.result != called.result
        || signature.outward_protocols != called.outward_protocols
        || *receiver_mode != target_mode
        || *capture_type != expected_capture
    {
        return Err(error(
            function,
            Some(block),
            "known indirect-call target does not match its callable descriptor",
        ));
    }
    Ok(())
}

struct KnownReceiverCall<'a> {
    target: u32,
    receiver: &'a Operand,
    args: &'a [Operand],
    result: Option<Register>,
    tail: bool,
}

fn validate_known_receiver_call(
    function: &Function,
    block: u32,
    program: &Program,
    call: KnownReceiverCall<'_>,
) -> Result<(), ValidationError> {
    validate_direct_call(
        function,
        block,
        program,
        call.target,
        call.args,
        call.result,
        call.tail,
    )?;
    let called = direct_target(program, call.target).ok_or_else(|| {
        error(
            function,
            Some(block),
            format!("known receiver target {} is missing", call.target),
        )
    })?;
    if called.receiver_mode != Some(0)
        || call.receiver.mode != UseMode::Copy
        || operand_type(function, block, call.receiver)? != called.receiver_type
        || !called
            .outward_protocols
            .iter()
            .all(|protocol| function.outward_protocols.contains(protocol))
    {
        return Err(error(
            function,
            Some(block),
            "known receiver call requires an exact mode-0 target and shared receiver type/effects",
        ));
    }
    Ok(())
}

fn validate_tail_resume(
    function: &Function,
    block: u32,
    types: &[Type],
    resumption: &Operand,
    receiver_mode: u32,
    value: &Operand,
) -> Result<(), ValidationError> {
    let resumption_ty = operand_type(function, block, resumption)?;
    let value_ty = operand_type(function, block, value)?;
    let Type::Resumption {
        input_type,
        output_type,
        effect_signature,
        upper_uses,
        ..
    } = types[resumption_ty as usize].representation()
    else {
        return Err(error(
            function,
            Some(block),
            "tail resume operand is not a resumption",
        ));
    };
    let receiver_mode_valid = match upper_uses {
        Some(0) => false,
        Some(1) => receiver_mode == 2,
        None | Some(2..) => receiver_mode <= 2,
    };
    if !receiver_mode_valid
        || (receiver_mode == 2 && resumption.mode != UseMode::Move)
        || (receiver_mode != 2 && resumption.mode != UseMode::Copy)
        || value.mode != UseMode::Move
        || value_ty != *input_type
        || *output_type != function.result
        || !effect_signature
            .outward_protocols
            .iter()
            .all(|protocol| function.outward_protocols.contains(protocol))
    {
        return Err(error(
            function,
            Some(block),
            "tail resume type, effect, receiver, or operand mode mismatch",
        ));
    }
    Ok(())
}

fn validate_terminator(
    function: &Function,
    block: &BasicBlock,
    blocks: &BTreeMap<u32, &BasicBlock>,
    program: &Program,
    types: &[Type],
) -> Result<(), ValidationError> {
    match &block.terminator {
        Terminator::Goto(edge) => validate_edge(function, blocks, block.id, edge, None),
        Terminator::Switch {
            discr,
            cases,
            otherwise,
        } => {
            let discr_ty = operand_type(function, block.id, discr)?;
            let mut constants = BTreeSet::new();
            for (constant, edge) in cases {
                if constant_type(constant) != discr_ty {
                    return Err(error(
                        function,
                        Some(block.id),
                        "switch case/discriminator type mismatch",
                    ));
                }
                let key = format!("{constant:?}");
                if !constants.insert(key) {
                    return Err(error(function, Some(block.id), "duplicate switch case"));
                }
                validate_edge(function, blocks, block.id, edge, None)?;
            }
            validate_edge(function, blocks, block.id, otherwise, None)
        }
        Terminator::Return { value } => {
            if let Some(value) = value {
                if operand_type(function, block.id, value)? != function.result {
                    return Err(error(
                        function,
                        Some(block.id),
                        "return value type mismatch",
                    ));
                }
            } else if function.result != UNIT && !function.no_return {
                return Err(error(
                    function,
                    Some(block.id),
                    "non-unit return has no value",
                ));
            }
            Ok(())
        }
        Terminator::Call {
            result,
            function: target,
            args,
            normal,
        } => {
            validate_direct_call(function, block.id, program, *target, args, *result, false)?;
            validate_edge(
                function,
                blocks,
                block.id,
                normal,
                result.map(|register| (BlockParamRole::CallResult, register)),
            )
        }
        Terminator::CallSelf {
            result,
            args,
            normal,
        } => {
            if !matches!(function.receiver_mode, Some(0 | 1))
                || args.len() != function.params.len()
                || args
                    .iter()
                    .zip(&function.params)
                    .any(|(argument, expected)| {
                        operand_type(function, block.id, argument).ok() != Some(*expected)
                    })
                || result.is_some_and(|register| {
                    register_type(function, block.id, register).ok() != Some(function.result)
                })
            {
                return Err(error(
                    function,
                    Some(block.id),
                    "invalid self call signature",
                ));
            }
            validate_edge(
                function,
                blocks,
                block.id,
                normal,
                result.map(|register| (BlockParamRole::CallResult, register)),
            )
        }
        Terminator::CallKnownReceiver {
            result,
            function: target,
            receiver,
            args,
            normal,
        } => {
            validate_known_receiver_call(
                function,
                block.id,
                program,
                KnownReceiverCall {
                    target: *target,
                    receiver,
                    args,
                    result: *result,
                    tail: false,
                },
            )?;
            validate_edge(
                function,
                blocks,
                block.id,
                normal,
                result.map(|register| (BlockParamRole::CallResult, register)),
            )
        }
        Terminator::HostCall {
            result,
            import,
            args,
            normal,
        } => {
            let (params, result_ty) = match import {
                HostImportRole::ProcessArgsGet => {
                    let result_ty = result
                        .and_then(|register| register_type(function, block.id, register).ok())
                        .ok_or_else(|| {
                            error(
                                function,
                                Some(block.id),
                                "process.args.get requires a result",
                            )
                        })?;
                    if !matches!(types[result_ty as usize].representation(), Type::Array { element } if *element == TEXT)
                    {
                        return Err(error(
                            function,
                            Some(block.id),
                            "process.args.get result must be Array<Text>",
                        ));
                    }
                    (vec![], result_ty)
                }
                HostImportRole::FsRead => (vec![TEXT], BYTES),
                HostImportRole::FsWrite => (vec![TEXT, BYTES], UNIT),
                HostImportRole::DiagnosticWrite => (vec![TEXT], UNIT),
            };
            if args.len() != params.len()
                || args.iter().zip(&params).any(|(argument, expected)| {
                    operand_type(function, block.id, argument).ok() != Some(*expected)
                })
            {
                return Err(error(
                    function,
                    Some(block.id),
                    "host call argument signature mismatch",
                ));
            }
            match result {
                Some(register) if register_type(function, block.id, *register)? != result_ty => {
                    return Err(error(
                        function,
                        Some(block.id),
                        "host call result signature mismatch",
                    ));
                }
                None if result_ty != UNIT => {
                    return Err(error(
                        function,
                        Some(block.id),
                        "non-unit host call has no result",
                    ));
                }
                _ => {}
            }
            validate_edge(
                function,
                blocks,
                block.id,
                normal,
                result.map(|register| (BlockParamRole::CallResult, register)),
            )
        }
        Terminator::CallIndirect {
            result,
            callable,
            known_function,
            receiver_mode,
            cleanup_callable,
            args,
            normal,
        } => {
            if *receiver_mode > 2 {
                return Err(error(
                    function,
                    Some(block.id),
                    "invalid indirect receiver mode",
                ));
            }
            let callable_ty = operand_type(function, block.id, callable)?;
            let Type::Callable {
                signature,
                receiver_mode: declared,
                ..
            } = types[callable_ty as usize].representation()
            else {
                return Err(error(
                    function,
                    Some(block.id),
                    "indirect callee is not callable",
                ));
            };
            validate_known_callable_target(
                function,
                block.id,
                program,
                types,
                callable_ty,
                *known_function,
            )?;
            if signature.result as usize >= types.len()
                || signature
                    .params
                    .iter()
                    .any(|ty| *ty as usize >= types.len())
            {
                return Err(error(
                    function,
                    Some(block.id),
                    "indirect callable signature contains an invalid type",
                ));
            }
            // A call may consume more authority than the callable minimally
            // requires (shared < unique < owned), matching the bytecode
            // verifier's receiver-access lattice.
            if receiver_mode < declared || signature.params.len() != args.len() {
                return Err(error(
                    function,
                    Some(block.id),
                    "indirect call signature mismatch",
                ));
            }
            if (*receiver_mode == 2 && callable.mode != UseMode::Move)
                || (*receiver_mode != 2 && callable.mode != UseMode::Copy)
            {
                return Err(error(
                    function,
                    Some(block.id),
                    "indirect callable operand mode disagrees with receiver mode",
                ));
            }
            if *receiver_mode == 2 && *cleanup_callable {
                return Err(error(
                    function,
                    Some(block.id),
                    "owned indirect call cannot separately clean up its consumed callable",
                ));
            }
            for (argument, expected) in args.iter().zip(&signature.params) {
                if operand_type(function, block.id, argument)? != *expected {
                    return Err(error(
                        function,
                        Some(block.id),
                        "indirect call argument type mismatch",
                    ));
                }
            }
            match result {
                Some(register) => {
                    if register_type(function, block.id, *register)? != signature.result {
                        return Err(error(
                            function,
                            Some(block.id),
                            "indirect call result type mismatch",
                        ));
                    }
                }
                None if !matches!(
                    types[signature.result as usize].representation(),
                    Type::Unit | Type::Never
                ) =>
                {
                    return Err(error(
                        function,
                        Some(block.id),
                        "value-returning indirect call has no result register",
                    ));
                }
                None => {}
            }
            validate_edge(
                function,
                blocks,
                block.id,
                normal,
                result.map(|register| (BlockParamRole::CallResult, register)),
            )
        }
        Terminator::Handle {
            result,
            handler,
            body,
            normal,
        } => {
            register_type(function, block.id, *result)?;
            operand_type(function, block.id, handler)?;
            operand_type(function, block.id, body)?;
            validate_edge(
                function,
                blocks,
                block.id,
                normal,
                Some((BlockParamRole::CallResult, *result)),
            )
        }
        Terminator::Perform {
            result,
            payloads,
            capture,
            resume,
            ..
        } => {
            if let Some(result) = result {
                register_type(function, block.id, *result)?;
            }
            for payload in payloads {
                operand_type(function, block.id, payload)?;
            }
            for register in capture
                .captured_owners
                .iter()
                .chain(&capture.captured_references)
                .chain(capture.captured_residuals.iter().map(|fact| &fact.register))
            {
                register_type(function, block.id, *register)?;
            }
            if result.is_some() != resume.is_some() {
                return Err(error(
                    function,
                    Some(block.id),
                    "perform result/resume edge disagree",
                ));
            }
            if let Some(resume) = resume {
                validate_edge(
                    function,
                    blocks,
                    block.id,
                    resume,
                    Some((BlockParamRole::ResumeResult, result.expect("checked above"))),
                )?;
            }
            Ok(())
        }
        Terminator::Resume {
            result,
            resumption,
            receiver_mode,
            value,
            normal,
        } => {
            if *receiver_mode > 2 {
                return Err(error(
                    function,
                    Some(block.id),
                    "invalid resumption receiver mode",
                ));
            }
            register_type(function, block.id, *result)?;
            operand_type(function, block.id, resumption)?;
            operand_type(function, block.id, value)?;
            validate_edge(
                function,
                blocks,
                block.id,
                normal,
                Some((BlockParamRole::ResumeResult, *result)),
            )
        }
        Terminator::TailResume {
            resumption,
            receiver_mode,
            value,
        } => validate_tail_resume(function, block.id, types, resumption, *receiver_mode, value),
        Terminator::Cancel {
            result,
            resumption,
            normal,
        } => {
            if register_type(function, block.id, *result)? != UNIT {
                return Err(error(function, Some(block.id), "cancel result is not unit"));
            }
            operand_type(function, block.id, resumption)?;
            validate_edge(
                function,
                blocks,
                block.id,
                normal,
                Some((BlockParamRole::ResumeResult, *result)),
            )
        }
        Terminator::TailCall {
            function: target,
            args,
        } => validate_direct_call(function, block.id, program, *target, args, None, true),
        Terminator::TailCallSelf { args } => {
            if function.receiver_mode.is_none()
                || args.len() != function.params.len()
                || args
                    .iter()
                    .zip(&function.params)
                    .any(|(argument, expected)| {
                        operand_type(function, block.id, argument).ok() != Some(*expected)
                    })
            {
                Err(error(
                    function,
                    Some(block.id),
                    "invalid tail self call signature",
                ))
            } else {
                Ok(())
            }
        }
        Terminator::TailCallKnownReceiver {
            function: target,
            receiver,
            args,
        } => validate_known_receiver_call(
            function,
            block.id,
            program,
            KnownReceiverCall {
                target: *target,
                receiver,
                args,
                result: None,
                tail: true,
            },
        ),
        Terminator::TailCallIndirect {
            callable,
            known_function,
            receiver_mode,
            args,
        } => {
            if *receiver_mode > 2 {
                return Err(error(
                    function,
                    Some(block.id),
                    "invalid tail receiver mode",
                ));
            }
            let callable_ty = operand_type(function, block.id, callable)?;
            let Type::Callable {
                signature,
                receiver_mode: declared,
                ..
            } = types[callable_ty as usize].representation()
            else {
                return Err(error(
                    function,
                    Some(block.id),
                    "indirect tail callee is not callable",
                ));
            };
            validate_known_callable_target(
                function,
                block.id,
                program,
                types,
                callable_ty,
                *known_function,
            )?;
            if signature.result as usize >= types.len()
                || signature
                    .params
                    .iter()
                    .any(|ty| *ty as usize >= types.len())
            {
                return Err(error(
                    function,
                    Some(block.id),
                    "indirect tail callable signature contains an invalid type",
                ));
            }
            if receiver_mode < declared
                || signature.params.len() != args.len()
                || signature.result != function.result
            {
                return Err(error(
                    function,
                    Some(block.id),
                    "indirect tail call signature mismatch",
                ));
            }
            if (*receiver_mode == 2 && callable.mode != UseMode::Move)
                || (*receiver_mode != 2 && callable.mode != UseMode::Copy)
            {
                return Err(error(
                    function,
                    Some(block.id),
                    "indirect tail callable operand mode disagrees with receiver mode",
                ));
            }
            for (argument, expected) in args.iter().zip(&signature.params) {
                if operand_type(function, block.id, argument)? != *expected {
                    return Err(error(
                        function,
                        Some(block.id),
                        "indirect tail call argument type mismatch",
                    ));
                }
            }
            Ok(())
        }
        Terminator::Leave { label, target } => {
            let fact =
                function.flow.labels.get(label.index()).ok_or_else(|| {
                    error(function, Some(block.id), "Leave label is out of range")
                })?;
            let destination = blocks
                .get(&target.target)
                .ok_or_else(|| error(function, Some(block.id), "Leave target block is missing"))?;
            if fact.destination != target.target
                || target.args.len() != destination.params.len()
                || destination.params.first().is_none_or(|parameter| {
                    parameter.role != BlockParamRole::ProtectedExitValue
                        || parameter.ty != fact.result_type
                })
                || destination.params[1..]
                    .iter()
                    .any(|parameter| parameter.role != BlockParamRole::Ordinary)
            {
                return Err(error(
                    function,
                    Some(block.id),
                    "Leave disagrees with its label fact or protected-exit destination",
                ));
            }
            validate_edge(function, blocks, block.id, target, None)
        }
        Terminator::Abort { .. } | Terminator::Unreachable => Ok(()),
    }
}

fn for_each_edge_with_implicit(terminator: &Terminator, mut visit: impl FnMut(&Edge, usize)) {
    match terminator {
        Terminator::Goto(edge) => visit(edge, 0),
        Terminator::Switch {
            cases, otherwise, ..
        } => {
            for (_, edge) in cases {
                visit(edge, 0);
            }
            visit(otherwise, 0);
        }
        Terminator::Call { result, normal, .. }
        | Terminator::CallSelf { result, normal, .. }
        | Terminator::CallKnownReceiver { result, normal, .. }
        | Terminator::CallIndirect { result, normal, .. }
        | Terminator::HostCall { result, normal, .. } => {
            visit(normal, usize::from(result.is_some()))
        }
        Terminator::Handle { normal, .. }
        | Terminator::Resume { normal, .. }
        | Terminator::Cancel { normal, .. } => visit(normal, 1),
        Terminator::Perform { resume, .. } => {
            if let Some(edge) = resume {
                visit(edge, 1);
            }
        }
        Terminator::Leave { target, .. } => visit(target, 0),
        Terminator::Return { .. }
        | Terminator::TailResume { .. }
        | Terminator::TailCall { .. }
        | Terminator::TailCallSelf { .. }
        | Terminator::TailCallKnownReceiver { .. }
        | Terminator::TailCallIndirect { .. }
        | Terminator::Abort { .. }
        | Terminator::Unreachable => {}
    }
}

fn for_each_edge_with_implicit_mut(
    terminator: &mut Terminator,
    mut visit: impl FnMut(&mut Edge, usize),
) {
    match terminator {
        Terminator::Goto(edge) => visit(edge, 0),
        Terminator::Switch {
            cases, otherwise, ..
        } => {
            for (_, edge) in cases {
                visit(edge, 0);
            }
            visit(otherwise, 0);
        }
        Terminator::Call { result, normal, .. }
        | Terminator::CallSelf { result, normal, .. }
        | Terminator::CallKnownReceiver { result, normal, .. }
        | Terminator::CallIndirect { result, normal, .. }
        | Terminator::HostCall { result, normal, .. } => {
            visit(normal, usize::from(result.is_some()))
        }
        Terminator::Handle { normal, .. }
        | Terminator::Resume { normal, .. }
        | Terminator::Cancel { normal, .. } => visit(normal, 1),
        Terminator::Perform { resume, .. } => {
            if let Some(edge) = resume {
                visit(edge, 1);
            }
        }
        Terminator::Leave { target, .. } => visit(target, 0),
        Terminator::Return { .. }
        | Terminator::TailResume { .. }
        | Terminator::TailCall { .. }
        | Terminator::TailCallSelf { .. }
        | Terminator::TailCallKnownReceiver { .. }
        | Terminator::TailCallIndirect { .. }
        | Terminator::Abort { .. }
        | Terminator::Unreachable => {}
    }
}

fn replace_operand_register(operand: &mut Operand, from: Register, to: Register) {
    if operand.register == from {
        operand.register = to;
    }
}

/// Replace uses in one block without changing any definition.  NormalizeCfg
/// calls this only after proving that the eliminated parameter has no use in
/// any other block.
fn replace_block_uses(block: &mut BasicBlock, from: Register, to: Register) {
    for statement in &mut block.statements {
        match &mut statement.kind {
            InstructionKind::Const { .. } => {}
            InstructionKind::Copy { src, .. } | InstructionKind::Move { src, .. } => {
                replace_operand_register(src, from, to)
            }
            InstructionKind::Borrow { src, .. }
            | InstructionKind::ProjectBorrow { src, .. }
            | InstructionKind::Reborrow { src, .. }
            | InstructionKind::DerefCopy { src, .. }
            | InstructionKind::DerefReborrow { src, .. }
            | InstructionKind::DerefMove { src, .. }
            | InstructionKind::EndBorrow { reference: src }
            | InstructionKind::Deconstruct { src }
            | InstructionKind::EnumTag { src, .. } => {
                if *src == from {
                    *src = to;
                }
            }
            InstructionKind::Construct { fields, .. } => {
                for operand in fields {
                    replace_operand_register(operand, from, to);
                }
            }
            InstructionKind::ProjectCopy { src, .. }
            | InstructionKind::ProjectMove { src, .. }
            | InstructionKind::Drop { owner: src } => replace_operand_register(src, from, to),
            InstructionKind::DerefStore { dst, src } => {
                if *dst == from {
                    *dst = to;
                }
                replace_operand_register(src, from, to);
            }
            InstructionKind::Primitive { args, .. } => {
                for operand in args {
                    replace_operand_register(operand, from, to);
                }
            }
            InstructionKind::MakeCallable { captures, .. }
            | InstructionKind::MakeHandlerShared { captures, .. } => {
                for operand in captures {
                    replace_operand_register(operand, from, to);
                }
            }
            InstructionKind::MakeHandler { clauses, .. } => {
                for operand in clauses {
                    replace_operand_register(operand, from, to);
                }
            }
            InstructionKind::MakeBindingPack { payloads, .. } => {
                for operand in payloads {
                    replace_operand_register(operand, from, to);
                }
            }
            InstructionKind::LabelPush { .. } | InstructionKind::LabelPop { .. } => {}
        }
    }
    match &mut block.terminator {
        Terminator::Switch { discr, .. } => replace_operand_register(discr, from, to),
        Terminator::Return { value } => {
            if let Some(value) = value {
                replace_operand_register(value, from, to);
            }
        }
        Terminator::Call { args, .. }
        | Terminator::CallSelf { args, .. }
        | Terminator::HostCall { args, .. }
        | Terminator::TailCall { args, .. }
        | Terminator::TailCallSelf { args } => {
            for operand in args {
                replace_operand_register(operand, from, to);
            }
        }
        Terminator::CallKnownReceiver { receiver, args, .. }
        | Terminator::TailCallKnownReceiver { receiver, args, .. } => {
            replace_operand_register(receiver, from, to);
            for operand in args {
                replace_operand_register(operand, from, to);
            }
        }
        Terminator::CallIndirect { callable, args, .. }
        | Terminator::TailCallIndirect { callable, args, .. } => {
            replace_operand_register(callable, from, to);
            for operand in args {
                replace_operand_register(operand, from, to);
            }
        }
        Terminator::Handle { handler, body, .. } => {
            replace_operand_register(handler, from, to);
            replace_operand_register(body, from, to);
        }
        Terminator::Perform {
            payloads, capture, ..
        } => {
            for operand in payloads {
                replace_operand_register(operand, from, to);
            }
            for register in capture
                .captured_owners
                .iter_mut()
                .chain(&mut capture.captured_references)
            {
                if *register == from {
                    *register = to;
                }
            }
            for residual in &mut capture.captured_residuals {
                if residual.register == from {
                    residual.register = to;
                }
            }
        }
        Terminator::Resume {
            resumption, value, ..
        } => {
            replace_operand_register(resumption, from, to);
            replace_operand_register(value, from, to);
        }
        Terminator::TailResume {
            resumption, value, ..
        } => {
            replace_operand_register(resumption, from, to);
            replace_operand_register(value, from, to);
        }
        Terminator::Cancel { resumption, .. } => replace_operand_register(resumption, from, to),
        Terminator::Leave { target, .. } => {
            for operand in &mut target.args {
                replace_operand_register(operand, from, to);
            }
        }
        Terminator::Goto(_) | Terminator::Abort { .. } | Terminator::Unreachable => {}
    }
    for_each_edge_mut(&mut block.terminator, |edge| {
        for operand in &mut edge.args {
            replace_operand_register(operand, from, to);
        }
    });
}

fn reachable_from(function: &Function, start: u32, sought: u32) -> bool {
    let mut seen = BTreeSet::new();
    let mut queue = VecDeque::from([start]);
    while let Some(id) = queue.pop_front() {
        if id == sought {
            return true;
        }
        if !seen.insert(id) {
            continue;
        }
        if let Some(block) = function.blocks.iter().find(|block| block.id == id) {
            queue.extend(successors(&block.terminator));
        }
    }
    false
}

/// Eliminate a deliberately narrow identity-transfer phi.  A Move edge merely
/// renames one owner, so retaining the source register in the target preserves
/// its dynamic disposition. Copy edges are not aliases and are never folded.
/// Requiring all uses to be local to the target, no other source uses, and no
/// loop backedge avoids relying on dominance or Use facts absent from compact
/// generation-1 MIR.
fn simplify_identity_block_parameter(
    function: &mut Function,
    liveness: &EdgeLiveness,
    target_id: u32,
) -> bool {
    debug_assert!(!EdgeLiveness::invalidated_by(analysis::VALUES));
    let Some(target_index) = function
        .blocks
        .iter()
        .position(|block| block.id == target_id)
    else {
        return false;
    };
    if target_id == function.entry {
        return false;
    }
    for parameter_index in 0..function.blocks[target_index].params.len() {
        let parameter = function.blocks[target_index].params[parameter_index].clone();
        if parameter.role != BlockParamRole::Ordinary
            || function.return_cleanup.contains(&parameter.register)
        {
            continue;
        }

        let mut incoming = Vec::<(u32, Operand, usize)>::new();
        for source in &function.blocks {
            for_each_edge_with_implicit(&source.terminator, |edge, implicit| {
                if edge.target != target_id || parameter_index < implicit {
                    return;
                }
                let argument_index = parameter_index - implicit;
                if let Some(argument) = edge.args.get(argument_index) {
                    incoming.push((source.id, *argument, argument_index));
                }
            });
        }
        let Some((_, identity, _)) = incoming.first().copied() else {
            continue;
        };
        if identity.mode != UseMode::Move
            || identity.register == parameter.register
            || function.register_types.get(identity.register as usize) != Some(&parameter.ty)
            || incoming.iter().any(|(_, operand, _)| *operand != identity)
            || incoming
                .iter()
                .any(|(source, _, _)| reachable_from(function, target_id, *source))
            || incoming.iter().any(|(source, _, _)| {
                !liveness.live_on_any_edge(
                    super::BlockId(*source),
                    super::BlockId(target_id),
                    identity.register,
                )
            })
        {
            continue;
        }
        if matches!(
            &function.blocks[target_index].terminator,
            Terminator::Perform { capture, .. }
                if capture.captured_owners.contains(&parameter.register)
                    || capture.captured_references.contains(&parameter.register)
                    || capture
                        .captured_residuals
                        .iter()
                        .any(|residual| residual.register == parameter.register)
        ) {
            continue;
        }
        if function.blocks[target_index]
            .params
            .iter()
            .any(|other| other.register == identity.register)
            || function.blocks[target_index]
                .statements
                .iter()
                .any(|statement| statement.kind.destination() == Some(identity.register))
        {
            continue;
        }
        let parameter_uses = function
            .blocks
            .iter()
            .enumerate()
            .map(|(index, block)| {
                used_registers(block)
                    .into_iter()
                    .filter(|register| *register == parameter.register)
                    .count()
                    * usize::from(index == target_index)
            })
            .sum::<usize>();
        if parameter_uses == 0
            || function.blocks.iter().enumerate().any(|(index, block)| {
                index != target_index
                    && liveness
                        .live_in(super::BlockId(block.id))
                        .is_some_and(|live| live.contains(&parameter.register))
            })
            || register_uses(function)[identity.register as usize] != incoming.len() as u32
        {
            continue;
        }

        for block in &mut function.blocks {
            for_each_edge_with_implicit_mut(&mut block.terminator, |edge, implicit| {
                if edge.target == target_id && parameter_index >= implicit {
                    edge.args.remove(parameter_index - implicit);
                }
            });
        }
        let target = &mut function.blocks[target_index];
        target.params.remove(parameter_index);
        replace_block_uses(target, parameter.register, identity.register);
        return true;
    }
    false
}

#[derive(Clone, Copy)]
enum SwitchEdgeSlot {
    Case(usize),
    Otherwise,
}

fn split_critical_switch_edges(
    function: &mut Function,
    budget: u64,
    work: &mut u64,
    next_block: Option<u32>,
) -> Result<bool, ()> {
    let mut incoming = BTreeMap::<u32, u32>::new();
    for block in &function.blocks {
        for_each_edge(&block.terminator, |edge| {
            *incoming.entry(edge.target).or_default() += 1;
        });
    }
    let mut sources = function
        .blocks
        .iter()
        .filter_map(|block| {
            let Terminator::Switch {
                cases, otherwise, ..
            } = &block.terminator
            else {
                return None;
            };
            (cases.len() + 1 > 1).then_some((block.id, cases.clone(), otherwise.clone()))
        })
        .collect::<Vec<_>>();
    sources.sort_by_key(|(id, _, _)| *id);
    let mut candidates = Vec::<(u32, SwitchEdgeSlot, u32)>::new();
    for (source, cases, otherwise) in sources {
        for (index, (_, edge)) in cases.iter().enumerate() {
            if incoming.get(&edge.target).copied().unwrap_or(0) > 1 {
                candidates.push((source, SwitchEdgeSlot::Case(index), edge.target));
            }
        }
        if incoming.get(&otherwise.target).copied().unwrap_or(0) > 1 {
            candidates.push((source, SwitchEdgeSlot::Otherwise, otherwise.target));
        }
    }

    if candidates.is_empty() {
        return Ok(false);
    }
    let mut next_block = next_block.ok_or(())?;
    let mut changed = false;
    for (source_id, slot, target_id) in candidates {
        let target_params = function
            .blocks
            .iter()
            .find(|block| block.id == target_id)
            .ok_or(())?
            .params
            .clone();
        if target_params.first().is_some_and(|parameter| {
            matches!(
                parameter.role,
                BlockParamRole::CallResult | BlockParamRole::ResumeResult
            )
        }) {
            continue;
        }
        if next_block == u32::MAX {
            return Err(());
        }
        *work = work.saturating_add(target_params.len() as u64 + 1);
        if *work > budget {
            return Err(());
        }
        let original = {
            let source = function
                .blocks
                .iter_mut()
                .find(|block| block.id == source_id)
                .ok_or(())?;
            let Terminator::Switch {
                cases, otherwise, ..
            } = &mut source.terminator
            else {
                return Err(());
            };
            let edge = match slot {
                SwitchEdgeSlot::Case(index) => &mut cases[index].1,
                SwitchEdgeSlot::Otherwise => otherwise,
            };
            let original = edge.clone();
            edge.target = next_block;
            original
        };
        let mut params = Vec::with_capacity(target_params.len());
        let mut args = Vec::with_capacity(target_params.len());
        for parameter in &target_params {
            let register = function.register_types.len() as Register;
            function.register_types.push(parameter.ty);
            params.push(super::BlockParam {
                register,
                ty: parameter.ty,
                role: parameter.role,
            });
            args.push(Operand {
                register,
                mode: UseMode::Move,
            });
        }
        function.blocks.push(BasicBlock {
            id: next_block,
            params,
            statements: vec![],
            terminator: Terminator::Goto(Edge {
                target: original.target,
                args,
            }),
        });
        next_block = next_block.checked_add(1).ok_or(())?;
        changed = true;
    }
    Ok(changed)
}

/// Thread the exact constant-test diamonds emitted by refutable pattern
/// lowering before they reach the structural bytecode verifier.
///
/// The source shape moves one locally constructed scalar into an empty
/// dispatcher block, copies that block parameter into a Switch, and moves
/// into an arm whose first action consumes the parameter.  Keeping the
/// dispatcher merges the unrelated constant/tag proofs of its predecessors;
/// structural flow can then combine arms which source semantics proved
/// mutually exclusive.  Threading each known predecessor directly to its
/// selected arm preserves the original scalar move and Drop while removing
/// only that impossible cross-product.
///
/// This deliberately recognizes no general jump-threading case.  Every
/// ownership, parameter, predecessor, and target invariant must have the
/// generated pattern shape or the candidate is left untouched.
fn thread_one_constant_switch_parameter_diamond(
    function: &mut Function,
    budget: u64,
    work: &mut u64,
) -> Result<bool, ()> {
    #[derive(Clone)]
    struct Incoming {
        source: u32,
        argument: Operand,
        selected: Edge,
    }

    let mut candidates = function
        .blocks
        .iter()
        .filter(|block| {
            let [parameter] = block.params.as_slice() else {
                return false;
            };
            parameter.role == BlockParamRole::ProtectedExitValue
                && predefined_no_drop_scalar(parameter.ty)
                && block.statements.is_empty()
                && matches!(
                    &block.terminator,
                    Terminator::Switch { discr, .. }
                        if discr.register == parameter.register && discr.mode == UseMode::Copy
                )
        })
        .map(|block| block.id)
        .collect::<Vec<_>>();
    if candidates.is_empty() {
        return Ok(false);
    }
    candidates.sort_unstable();
    let label_targets = function
        .flow
        .labels
        .iter()
        .map(|label| label.destination)
        .collect::<BTreeSet<_>>();
    let block_indices = function
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| (block.id, index))
        .collect::<BTreeMap<_, _>>();
    let mut predecessor_sources = BTreeMap::<u32, BTreeSet<u32>>::new();
    let mut analysis_work = function.blocks.len() as u64;
    for source in &function.blocks {
        analysis_work = analysis_work.saturating_add(source.statements.len() as u64);
        for_each_edge(&source.terminator, |edge| {
            analysis_work = analysis_work.saturating_add(1);
            predecessor_sources
                .entry(edge.target)
                .or_default()
                .insert(source.id);
        });
    }
    *work = work.saturating_add(analysis_work);
    if *work > budget {
        return Err(());
    }
    // Candidate inspection is transactional: the function is unchanged until
    // one candidate commits, at which point this helper returns immediately.
    // Compute whole-function use counts once rather than once per dispatcher.
    let uses = register_uses(function);
    // A scalar-only dispatcher can still carry hidden ownership state: loans
    // remain live in their reference registers even though they are not edge
    // arguments. Bypassing such a dispatcher can combine path refinements
    // across a loop and change the strict loan state seen at a later join.
    // This narrow transform has no loan-state equivalence proof, so retain the
    // dispatcher whenever an explicit loan reference or external reference
    // local crosses an incoming edge.
    let loan_sensitive_references = function
        .flow
        .loans
        .iter()
        .map(|loan| loan.reference)
        .chain(
            function
                .flow
                .locals
                .iter()
                .enumerate()
                .filter_map(|(register, local)| {
                    matches!(
                        local.ownership,
                        super::OwnershipCategory::SharedRef | super::OwnershipCategory::UniqueRef
                    )
                    .then_some(register as Register)
                }),
        )
        .collect::<BTreeSet<_>>();
    let reference_liveness = if loan_sensitive_references.is_empty() {
        None
    } else {
        let remaining = budget.saturating_sub(*work);
        let liveness = EdgeLiveness::compute(function, remaining).map_err(|_| ())?;
        *work = work.saturating_add(liveness.work());
        if *work > budget {
            return Err(());
        }
        Some(liveness)
    };

    for dispatcher_id in candidates {
        *work = work.saturating_add(1);
        if *work > budget {
            return Err(());
        }
        if dispatcher_id == function.entry || label_targets.contains(&dispatcher_id) {
            continue;
        }
        let Some(&dispatcher_index) = block_indices.get(&dispatcher_id) else {
            continue;
        };
        let dispatcher = &function.blocks[dispatcher_index];
        let [parameter] = dispatcher.params.as_slice() else {
            continue;
        };
        if parameter.role != BlockParamRole::ProtectedExitValue
            || !predefined_no_drop_scalar(parameter.ty)
            || !dispatcher.statements.is_empty()
        {
            continue;
        }
        let Terminator::Switch {
            discr,
            cases,
            otherwise,
        } = &dispatcher.terminator
        else {
            continue;
        };
        if discr.register != parameter.register || discr.mode != UseMode::Copy {
            continue;
        }
        let parameter = parameter.clone();
        let cases = cases.clone();
        let otherwise = otherwise.clone();
        let outgoing = cases
            .iter()
            .map(|(_, edge)| edge.clone())
            .chain(std::iter::once(otherwise.clone()))
            .collect::<Vec<_>>();
        // Generated pattern dispatch carries no values to its arms. Requiring
        // that exact shape also prevents appending a second move of an
        // incoming predecessor-local constant to an existing arm argument.
        if outgoing.iter().any(|edge| !edge.args.is_empty()) {
            continue;
        }
        let successors = outgoing
            .iter()
            .map(|edge| edge.target)
            .collect::<BTreeSet<_>>();
        if successors.is_empty()
            || successors
                .iter()
                .any(|target| *target == function.entry || label_targets.contains(target))
        {
            continue;
        }

        // Every arm must be private to this dispatcher.  Its only use of the
        // transferred test owner is the leading Drop which pattern lowering
        // emits after selecting the arm.
        if successors
            .iter()
            .any(|target| predecessor_sources.get(target) != Some(&BTreeSet::from([dispatcher_id])))
        {
            continue;
        }
        let arms_have_exact_drop = successors.iter().all(|target| {
            block_indices
                .get(target)
                .and_then(|index| function.blocks.get(*index))
                .is_some_and(|block| {
                    matches!(
                        block.statements.first().map(|statement| &statement.kind),
                        Some(InstructionKind::Drop {
                            owner: Operand {
                                register,
                                mode: UseMode::Move
                            }
                        }) if *register == parameter.register
                    )
                })
        });
        if !arms_have_exact_drop
            || uses[parameter.register as usize] != 1_u32.saturating_add(successors.len() as u32)
        {
            continue;
        }

        let mut incoming = Vec::new();
        let mut invalid_incoming = false;
        for source_id in predecessor_sources
            .get(&dispatcher_id)
            .into_iter()
            .flatten()
        {
            let Some(&source_index) = block_indices.get(source_id) else {
                invalid_incoming = true;
                break;
            };
            let source = &function.blocks[source_index];
            let Terminator::Goto(edge) = &source.terminator else {
                invalid_incoming = true;
                break;
            };
            let [argument] = edge.args.as_slice() else {
                invalid_incoming = true;
                break;
            };
            if edge.target != dispatcher_id
                || argument.mode != UseMode::Move
                || function
                    .register_types
                    .get(argument.register as usize)
                    .copied()
                    != Some(parameter.ty)
            {
                invalid_incoming = true;
                break;
            }
            let Some(Instruction {
                kind:
                    InstructionKind::Const {
                        dst,
                        value: constant,
                    },
                ..
            }) = source.statements.last()
            else {
                invalid_incoming = true;
                break;
            };
            if *dst != argument.register {
                invalid_incoming = true;
                break;
            }
            let selected = cases
                .iter()
                .find_map(|(candidate, edge)| {
                    frozen_constant_eq(candidate, constant).then(|| edge.clone())
                })
                .unwrap_or_else(|| otherwise.clone());
            incoming.push(Incoming {
                source: source.id,
                argument: *argument,
                selected,
            });
        }
        if invalid_incoming || incoming.is_empty() {
            continue;
        }
        if reference_liveness.as_ref().is_some_and(|liveness| {
            incoming.iter().any(|incoming| {
                loan_sensitive_references.iter().any(|reference| {
                    liveness.live_on_any_edge(
                        super::BlockId(incoming.source),
                        super::BlockId(dispatcher_id),
                        *reference,
                    )
                })
            })
        }) {
            continue;
        }

        let first_register = function.register_types.len();
        let Some(register_end) = first_register.checked_add(successors.len()) else {
            return Err(());
        };
        if register_end > u32::MAX as usize {
            return Err(());
        }
        let fresh_by_target = successors
            .iter()
            .copied()
            .enumerate()
            .map(|(offset, target)| (target, (first_register + offset) as Register))
            .collect::<BTreeMap<_, _>>();

        // All proof has completed. Commit the candidate atomically.
        function
            .register_types
            .extend(std::iter::repeat_n(parameter.ty, successors.len()));
        for target in &successors {
            let fresh = fresh_by_target[target];
            let arm = function
                .blocks
                .get_mut(*block_indices.get(target).ok_or(())?)
                .ok_or(())?;
            arm.params.push(BlockParam {
                register: fresh,
                ty: parameter.ty,
                role: BlockParamRole::Ordinary,
            });
            let Some(InstructionKind::Drop { owner }) = arm
                .statements
                .first_mut()
                .map(|statement| &mut statement.kind)
            else {
                return Err(());
            };
            owner.register = fresh;
        }
        for incoming in incoming {
            let target = incoming.selected.target;
            let mut args = incoming.selected.args;
            args.push(Operand {
                register: incoming.argument.register,
                mode: UseMode::Move,
            });
            let source = function
                .blocks
                .get_mut(*block_indices.get(&incoming.source).ok_or(())?)
                .ok_or(())?;
            source.terminator = Terminator::Goto(Edge { target, args });
        }
        function.blocks.retain(|block| block.id != dispatcher_id);
        return Ok(true);
    }
    Ok(false)
}

fn normalize_cfg(function: &mut Function, budget: u64) -> (PassOutcome, u64) {
    let mut scratch = function.clone();
    // Reserve IDs from the original arena before deleting unreachable or
    // merged blocks. NormalizeCfg never recycles an ID during this run.
    let first_fresh_block = scratch
        .blocks
        .iter()
        .map(|block| block.id)
        .max()
        .unwrap_or(0)
        .checked_add(1);
    let mut work = 0_u64;
    let mut reachable = BTreeSet::new();
    let mut queue = VecDeque::from([scratch.entry]);
    while let Some(block) = queue.pop_front() {
        work += 1;
        if work > budget {
            return (PassOutcome::BudgetExhausted, work);
        }
        if !reachable.insert(block) {
            continue;
        }
        if let Some(body) = scratch
            .blocks
            .iter()
            .find(|candidate| candidate.id == block)
        {
            // A label destination is a hidden structural CFG root. It may be
            // reached dynamically by a `Leave` from anywhere in the active
            // label region, and the VM validates every executed LabelPush
            // target even when no statically reachable Leave selects it.
            for statement in &body.statements {
                if let InstructionKind::LabelPush { target, .. } = statement.kind {
                    queue.push_back(target);
                }
            }
            for successor in successors(&body.terminator) {
                queue.push_back(successor);
            }
        }
    }
    let unreachable = scratch
        .blocks
        .iter()
        .filter(|block| !reachable.contains(&block.id))
        .map(|block| super::BlockId(block.id))
        .collect::<Vec<_>>();
    let mut changed = !unreachable.is_empty();
    if changed {
        // NormalizeCfg runs only after structural validation. The checked
        // editor retains stable slots as tombstones during this transaction,
        // verifies that no live edge/label targets a deletion, and commits the
        // precise invalidation mask with the surviving IDs unchanged.
        let mut editor = CheckedCfg::new(&scratch, ResourceLimits::default())
            .expect("validated MIR must open in the checked CFG editor");
        debug_assert!(unreachable.iter().all(|id| editor.block_kind(*id).is_ok()));
        editor
            .tombstone_many(unreachable.iter().copied())
            .expect("reachability deletion never removes the entry block");
        debug_assert!(unreachable.iter().all(|id| editor.is_tombstone(*id)));
        debug_assert_eq!(editor.invalidated(), analysis::ALL);
        editor
            .commit(&mut scratch)
            .expect("unreachable deletion cannot leave a live dangling edge");
    }

    let mut threaded_any = false;
    loop {
        match thread_one_constant_switch_parameter_diamond(&mut scratch, budget, &mut work) {
            Ok(true) => {
                changed = true;
                threaded_any = true;
            }
            Ok(false) => break,
            Err(()) => return (PassOutcome::BudgetExhausted, work),
        }
    }
    // Threading selects one constant successor per predecessor and can make
    // the other generated arm unreachable. Re-run structural reachability
    // before later normalization so those dead arms cannot survive merely
    // because they were reachable through the dispatcher we just removed.
    if threaded_any {
        let threaded_block_indices = scratch
            .blocks
            .iter()
            .enumerate()
            .map(|(index, block)| (block.id, index))
            .collect::<BTreeMap<_, _>>();
        let mut threaded_reachable = BTreeSet::new();
        let mut threaded_queue = VecDeque::from([scratch.entry]);
        while let Some(block) = threaded_queue.pop_front() {
            work = work.saturating_add(1);
            if work > budget {
                return (PassOutcome::BudgetExhausted, work);
            }
            if !threaded_reachable.insert(block) {
                continue;
            }
            if let Some(body) = threaded_block_indices
                .get(&block)
                .and_then(|index| scratch.blocks.get(*index))
            {
                let body_successors = successors(&body.terminator);
                work = work
                    .saturating_add(body.statements.len() as u64)
                    .saturating_add(body_successors.len() as u64);
                if work > budget {
                    return (PassOutcome::BudgetExhausted, work);
                }
                for statement in &body.statements {
                    if let InstructionKind::LabelPush { target, .. } = statement.kind {
                        threaded_queue.push_back(target);
                    }
                }
                for successor in body_successors {
                    threaded_queue.push_back(successor);
                }
            }
        }
        let threaded_unreachable = scratch
            .blocks
            .iter()
            .filter(|block| !threaded_reachable.contains(&block.id))
            .map(|block| super::BlockId(block.id))
            .collect::<Vec<_>>();
        if !threaded_unreachable.is_empty() {
            let mut editor = CheckedCfg::new(&scratch, ResourceLimits::default())
                .expect("threaded validated MIR must open in the checked CFG editor");
            editor
                .tombstone_many(threaded_unreachable.iter().copied())
                .expect("threading reachability never removes the entry block");
            editor
                .commit(&mut scratch)
                .expect("threaded reachability cannot leave a live dangling edge");
            changed = true;
        }
    }

    // Fold only ownership-preserving Move aliases. The compact MIR has no
    // general dominance/Use proof attached to parameters, so Copy phis,
    // cross-block uses, loop phis, and every special parameter role remain.
    loop {
        // Parameter simplification does not mutate the body until it commits
        // one candidate, so every target in this iteration observes the same
        // valid edge-liveness snapshot. A successful mutation immediately
        // restarts the loop and recomputes the analysis before another target
        // is inspected.
        let Ok(liveness) = EdgeLiveness::compute(&scratch, u64::MAX) else {
            break;
        };
        let _analysis_work = liveness.work();
        let mut targets = scratch
            .blocks
            .iter()
            .map(|block| block.id)
            .collect::<Vec<_>>();
        targets.sort_unstable();
        let mut simplified = false;
        for target in targets {
            work = work.saturating_add(scratch.blocks.len() as u64 + 1);
            if work > budget {
                return (PassOutcome::BudgetExhausted, work);
            }
            if simplify_identity_block_parameter(&mut scratch, &liveness, target) {
                changed = true;
                simplified = true;
                break;
            }
        }
        if !simplified {
            break;
        }
    }

    // Only erase empty, parameter-free forwarding blocks. They contain no
    // ownership event, cleanup, borrow, handler, effect, or resumption barrier.
    // Select by BlockId rather than storage order so normalization is stable
    // when an importer presents the same arena in a different order.
    loop {
        let candidate = scratch
            .blocks
            .iter()
            .filter_map(|block| {
                if !block.params.is_empty() || !block.statements.is_empty() {
                    return None;
                }
                let Terminator::Goto(edge) = &block.terminator else {
                    return None;
                };
                if !edge.args.is_empty() || edge.target == block.id {
                    return None;
                }
                Some((block.id, edge.target))
            })
            .min_by_key(|(block, _)| *block);
        let Some((removed, replacement)) = candidate else {
            break;
        };
        work += scratch.blocks.len() as u64;
        if work > budget {
            return (PassOutcome::BudgetExhausted, work);
        }
        if scratch.entry == removed {
            scratch.entry = replacement;
        }
        for block in &mut scratch.blocks {
            for_each_edge_mut(&mut block.terminator, |edge| {
                if edge.target == removed {
                    edge.target = replacement;
                }
            });
        }
        scratch.blocks.retain(|block| block.id != removed);
        changed = true;
    }

    // Coalesce a uniquely-entered straight-line target into its sole ordinary
    // predecessor. Requiring a plain, argument-free Goto and a parameter-free
    // target is intentionally strict: call results, handler results, resumed
    // values, and protected exit values are implicit edge transfers and must
    // retain their continuation boundary. Appending the target body preserves
    // every ownership/cleanup event in program order.
    loop {
        let mut incoming = BTreeMap::<u32, u32>::new();
        for block in &scratch.blocks {
            for_each_edge(&block.terminator, |edge| {
                *incoming.entry(edge.target).or_default() += 1;
            });
        }
        let candidate = scratch
            .blocks
            .iter()
            .filter_map(|source| {
                let Terminator::Goto(edge) = &source.terminator else {
                    return None;
                };
                if !edge.args.is_empty()
                    || edge.target == source.id
                    || edge.target == scratch.entry
                    || incoming.get(&edge.target) != Some(&1)
                {
                    return None;
                }
                let target = scratch
                    .blocks
                    .iter()
                    .find(|target| target.id == edge.target)?;
                target.params.is_empty().then_some((source.id, target.id))
            })
            .min_by_key(|(source, _)| *source);
        let Some((source_id, target_id)) = candidate else {
            break;
        };
        work += scratch.blocks.len() as u64;
        if work > budget {
            return (PassOutcome::BudgetExhausted, work);
        }
        let target_index = scratch
            .blocks
            .iter()
            .position(|block| block.id == target_id)
            .expect("selected target exists");
        let target = scratch.blocks.remove(target_index);
        let source = scratch
            .blocks
            .iter_mut()
            .find(|block| block.id == source_id)
            .expect("selected source exists");
        source.statements.extend(target.statements);
        source.terminator = target.terminator;
        changed = true;
    }
    match split_critical_switch_edges(&mut scratch, budget, &mut work, first_fresh_block) {
        Ok(split) => changed |= split,
        Err(()) => return (PassOutcome::BudgetExhausted, work),
    }
    scratch.features = infer_feature_bits(&scratch);
    *function = scratch;
    (
        if changed {
            PassOutcome::Changed
        } else {
            PassOutcome::Unchanged
        },
        work,
    )
}

fn register_uses(function: &Function) -> Vec<u32> {
    let mut uses = vec![0_u32; function.register_types.len()];
    for &register in &function.return_cleanup {
        uses[register as usize] = uses[register as usize].saturating_add(1);
    }
    for block in &function.blocks {
        for statement in &block.statements {
            statement.kind.for_each_register_use(|register, _| {
                uses[register as usize] = uses[register as usize].saturating_add(1);
            });
        }
        block.terminator.for_each_register_use(|register, _| {
            uses[register as usize] = uses[register as usize].saturating_add(1);
        });
    }
    uses
}

fn aggregate_field_types(ty: TypeId, types: &[Type]) -> Option<Vec<TypeId>> {
    match types.get(ty as usize)?.representation() {
        Type::Tuple { fields, .. } => Some(fields.clone()),
        Type::Struct { fields, .. } => Some(fields.iter().map(|field| field.ty).collect()),
        // Enums need discriminant and variant facts supplied by SCCP.
        _ => None,
    }
}

#[derive(Clone)]
struct ScalarizeCandidate {
    construct: usize,
    deconstruct: usize,
    owner: Register,
    field_types: Vec<TypeId>,
    fields: Vec<Operand>,
}

/// Replace a nonescaping, completely deconstructed local tuple/struct with
/// scalar registers. Fields are initialized at the original `Construct`
/// position, preserving transfer, trap, and destruction ordering. Requiring
/// all aggregate uses to be local projections plus the final deconstruction is
/// also the barrier for loans, calls, captures, handlers, cleanup, and edges.
fn scalarize_locals(function: &mut Function, types: &[Type], budget: u64) -> (PassOutcome, u64) {
    if !function.features.contains(FeatureBits::AGGREGATES) {
        return (PassOutcome::Unchanged, 0);
    }

    let aggregate_candidates = function
        .blocks
        .iter()
        .flat_map(|block| &block.statements)
        .filter(|statement| matches!(statement.kind, InstructionKind::Construct { .. }))
        .count() as u64;
    let work = body_size(function)
        .saturating_add(function.register_types.len() as u64)
        .saturating_add(
            function
                .blocks
                .iter()
                .map(|block| block.statements.len() as u64)
                .sum::<u64>(),
        )
        .saturating_add(aggregate_candidates.saturating_mul(body_size(function)));
    if work > budget {
        return (PassOutcome::BudgetExhausted, work);
    }

    let mut definitions = vec![0_u32; function.register_types.len()];
    for block in &function.blocks {
        for parameter in &block.params {
            definitions[parameter.register as usize] =
                definitions[parameter.register as usize].saturating_add(1);
        }
        for statement in &block.statements {
            let dst = statement.kind.destination();
            if let Some(dst) = dst {
                definitions[dst as usize] = definitions[dst as usize].saturating_add(1);
            }
        }
    }

    let uses = register_uses(function);
    let mut scratch = function.clone();
    let mut changed = false;
    for block_index in 0..function.blocks.len() {
        let original = &function.blocks[block_index];
        let mut candidates = Vec::<ScalarizeCandidate>::new();
        for (construct_index, statement) in original.statements.iter().enumerate() {
            let InstructionKind::Construct {
                dst,
                ty,
                variant: None,
                fields,
            } = &statement.kind
            else {
                continue;
            };
            if *dst as usize <= function.params.len()
                || definitions[*dst as usize] != 1
                || function.return_cleanup.contains(dst)
                || fields.len() < 2
            {
                continue;
            }
            let Some(field_types) = aggregate_field_types(*ty, types) else {
                continue;
            };
            if field_types.len() != fields.len()
                // Storing a reference in an aggregate deliberately detaches
                // it from the named parent handle while retaining its exact
                // referent provenance. Replacing that store with an ordinary
                // SSA `Move` would instead keep the parent/child reborrow
                // edge live and can make a following `EndBorrow` invalid.
                // Scalar reference carriers need a dedicated provenance
                // transfer operation before they can participate here.
                || field_types
                    .iter()
                    .any(|field| type_carries_reference(types, *field))
                || fields.iter().zip(&field_types).any(|(field, expected)| {
                    function.register_types.get(field.register as usize) != Some(expected)
                })
            {
                continue;
            }

            let mut seen_moves = vec![false; fields.len()];
            let mut aggregate_uses = 0_u32;
            let mut deconstruct = None;
            let mut legal = true;
            for (index, candidate_use) in original.statements.iter().enumerate() {
                match &candidate_use.kind {
                    InstructionKind::ProjectCopy {
                        dst: projected,
                        src,
                        field,
                    } if src.register == *dst => {
                        aggregate_uses += 1;
                        let field = *field as usize;
                        if index <= construct_index
                            || deconstruct.is_some()
                            || src.mode != UseMode::Copy
                            || field >= field_types.len()
                            || seen_moves[field]
                            || function.register_types[*projected as usize] != field_types[field]
                        {
                            legal = false;
                        }
                    }
                    InstructionKind::ProjectMove {
                        dst: projected,
                        src,
                        field,
                    } if src.register == *dst => {
                        aggregate_uses += 1;
                        let field = *field as usize;
                        if index <= construct_index
                            || deconstruct.is_some()
                            || src.mode != UseMode::Move
                            || field >= field_types.len()
                            || seen_moves.get(field).copied().unwrap_or(true)
                            || function.register_types[*projected as usize] != field_types[field]
                        {
                            legal = false;
                        } else {
                            seen_moves[field] = true;
                        }
                    }
                    InstructionKind::Deconstruct { src } if *src == *dst => {
                        aggregate_uses += 1;
                        if index <= construct_index || deconstruct.replace(index).is_some() {
                            legal = false;
                        }
                    }
                    _ => {}
                }
            }
            let Some(deconstruct) = deconstruct else {
                continue;
            };
            if !legal
                || !seen_moves.iter().all(|moved| *moved)
                || uses[*dst as usize] != aggregate_uses
            {
                continue;
            }
            candidates.push(ScalarizeCandidate {
                construct: construct_index,
                deconstruct,
                owner: *dst,
                field_types,
                fields: fields.clone(),
            });
        }

        if candidates.is_empty() {
            continue;
        }
        let by_owner = candidates
            .iter()
            .enumerate()
            .map(|(index, candidate)| (candidate.owner, index))
            .collect::<BTreeMap<_, _>>();
        let mut scalar_registers = Vec::with_capacity(candidates.len());
        for candidate in &candidates {
            let mut fields = Vec::with_capacity(candidate.field_types.len());
            for ty in &candidate.field_types {
                let register = scratch.register_types.len() as Register;
                scratch.register_types.push(*ty);
                fields.push(register);
            }
            scalar_registers.push(fields);
        }

        let mut rewritten = Vec::new();
        for (statement_index, statement) in original.statements.iter().enumerate() {
            if let Some((candidate_index, candidate)) = candidates
                .iter()
                .enumerate()
                .find(|(_, candidate)| candidate.construct == statement_index)
            {
                for (field, scalar) in candidate
                    .fields
                    .iter()
                    .zip(&scalar_registers[candidate_index])
                {
                    let kind = match field.mode {
                        UseMode::Copy => InstructionKind::Copy {
                            dst: *scalar,
                            src: *field,
                        },
                        UseMode::Move => InstructionKind::Move {
                            dst: *scalar,
                            src: *field,
                        },
                    };
                    rewritten.push(Instruction {
                        span: statement.span,
                        kind,
                    });
                }
                continue;
            }
            match &statement.kind {
                InstructionKind::ProjectCopy { dst, src, field }
                    if by_owner.contains_key(&src.register) =>
                {
                    let candidate = by_owner[&src.register];
                    rewritten.push(Instruction {
                        span: statement.span,
                        kind: InstructionKind::Copy {
                            dst: *dst,
                            src: Operand {
                                register: scalar_registers[candidate][*field as usize],
                                mode: UseMode::Copy,
                            },
                        },
                    });
                }
                InstructionKind::ProjectMove { dst, src, field }
                    if by_owner.contains_key(&src.register) =>
                {
                    let candidate = by_owner[&src.register];
                    rewritten.push(Instruction {
                        span: statement.span,
                        kind: InstructionKind::Move {
                            dst: *dst,
                            src: Operand {
                                register: scalar_registers[candidate][*field as usize],
                                mode: UseMode::Move,
                            },
                        },
                    });
                }
                InstructionKind::Deconstruct { src }
                    if by_owner.get(src).is_some_and(|candidate| {
                        candidates[*candidate].deconstruct == statement_index
                    }) => {}
                _ => rewritten.push(statement.clone()),
            }
        }
        scratch.blocks[block_index].statements = rewritten;
        changed = true;
    }
    scratch.features = infer_feature_bits(&scratch);
    *function = scratch;
    (
        if changed {
            PassOutcome::Changed
        } else {
            PassOutcome::Unchanged
        },
        work,
    )
}

#[derive(Clone, Copy)]
struct IntSpec {
    signed: bool,
    bits: u32,
}

fn int_spec(ty: TypeId) -> Option<IntSpec> {
    Some(match ty {
        U8 => IntSpec {
            signed: false,
            bits: 8,
        },
        U16 => IntSpec {
            signed: false,
            bits: 16,
        },
        U32 => IntSpec {
            signed: false,
            bits: 32,
        },
        U64 | USIZE => IntSpec {
            signed: false,
            bits: 64,
        },
        U128 => IntSpec {
            signed: false,
            bits: 128,
        },
        I8 => IntSpec {
            signed: true,
            bits: 8,
        },
        I16 => IntSpec {
            signed: true,
            bits: 16,
        },
        I32 => IntSpec {
            signed: true,
            bits: 32,
        },
        I64 | ISIZE => IntSpec {
            signed: true,
            bits: 64,
        },
        I128 => IntSpec {
            signed: true,
            bits: 128,
        },
        _ => return None,
    })
}

fn int_mask(bits: u32) -> u128 {
    if bits == 128 {
        u128::MAX
    } else {
        (1_u128 << bits) - 1
    }
}

fn signed_value(spec: IntSpec, value: &Constant) -> Option<i128> {
    let raw = match (spec.bits, value) {
        (128, Constant::I128(value)) => *value as u128,
        (1..=127, Constant::I8(value)) => *value as u128,
        (1..=127, Constant::I16(value)) => *value as u128,
        (1..=127, Constant::I32(value)) => *value as u128,
        (1..=127, Constant::I64(value) | Constant::Isize(value)) => *value as u128,
        _ => return None,
    } & int_mask(spec.bits);
    Some(if spec.bits == 128 {
        raw as i128
    } else {
        ((raw << (128 - spec.bits)) as i128) >> (128 - spec.bits)
    })
}

fn unsigned_value(spec: IntSpec, value: &Constant) -> Option<u128> {
    let raw = match (spec.bits, value) {
        (128, Constant::U128(value)) => *value,
        (1..=127, Constant::U8(value)) => u128::from(*value),
        (1..=127, Constant::U16(value)) => u128::from(*value),
        (1..=127, Constant::U32(value)) => u128::from(*value),
        (1..=127, Constant::U64(value) | Constant::Usize(value)) => u128::from(*value),
        _ => return None,
    };
    Some(raw & int_mask(spec.bits))
}

fn int_raw_value(spec: IntSpec, value: &Constant) -> Option<u128> {
    if spec.signed {
        Some(signed_value(spec, value)? as u128 & int_mask(spec.bits))
    } else {
        unsigned_value(spec, value)
    }
}

fn shift_count(value: &Constant) -> Option<u32> {
    let value = match value {
        Constant::U8(value) => u64::from(*value),
        Constant::U16(value) => u64::from(*value),
        Constant::U32(value) => u64::from(*value),
        Constant::U64(value) | Constant::Usize(value) => *value,
        _ => return None,
    };
    u32::try_from(value).ok()
}

fn signed_bounds(bits: u32) -> (i128, i128) {
    if bits == 128 {
        (i128::MIN, i128::MAX)
    } else {
        let limit = 1_i128 << (bits - 1);
        (-limit, limit - 1)
    }
}

fn make_int_constant(ty: TypeId, raw: u128) -> Option<Constant> {
    let spec = int_spec(ty)?;
    let raw = raw & int_mask(spec.bits);
    Some(match ty {
        U8 => Constant::U8(raw as u8),
        U16 => Constant::U16(raw as u16),
        U32 => Constant::U32(raw as u32),
        U64 => Constant::U64(raw as u64),
        U128 => Constant::U128(raw),
        USIZE => Constant::Usize(raw as u64),
        I8 => Constant::I8(raw as i8),
        I16 => Constant::I16(raw as i16),
        I32 => Constant::I32(raw as i32),
        I64 => Constant::I64(raw as i64),
        I128 => Constant::I128(raw as i128),
        ISIZE => Constant::Isize(raw as i64),
        _ => return None,
    })
}

fn make_checked_signed(ty: TypeId, value: Option<i128>) -> Option<Constant> {
    let value = value?;
    let spec = int_spec(ty)?;
    let (min, max) = signed_bounds(spec.bits);
    (value >= min && value <= max)
        .then(|| make_int_constant(ty, value as u128))
        .flatten()
}

fn make_checked_unsigned(ty: TypeId, value: Option<u128>) -> Option<Constant> {
    let value = value?;
    let spec = int_spec(ty)?;
    (value <= int_mask(spec.bits))
        .then(|| make_int_constant(ty, value))
        .flatten()
}

fn canonical_f32(value: f32) -> f32 {
    if value.is_nan() {
        f32::from_bits(0x7fc0_0000)
    } else {
        value
    }
}

fn canonical_f64(value: f64) -> f64 {
    if value.is_nan() {
        f64::from_bits(0x7ff8_0000_0000_0000)
    } else {
        value
    }
}

fn fold_float_primitive(
    result_type: TypeId,
    primitive: Primitive,
    arg_types: &[TypeId],
    args: &[Constant],
) -> Option<Constant> {
    use Primitive::*;

    let comparison = matches!(
        primitive,
        FloatEq | FloatNe | FloatLt | FloatLe | FloatGt | FloatGe
    );
    let arithmetic = matches!(
        primitive,
        FloatAdd | FloatSub | FloatMul | FloatDiv | FloatRem
    );
    if !comparison && !arithmetic && primitive != FloatNeg {
        return None;
    }

    let source_type = *arg_types.first()?;
    if args.len() != arg_types.len()
        || arg_types.iter().any(|ty| *ty != source_type)
        || args
            .iter()
            .any(|constant| constant_type(constant) != source_type)
    {
        return None;
    }
    if comparison && result_type != U32 {
        return None;
    }
    if !comparison && result_type != source_type {
        return None;
    }

    match source_type {
        F32 => {
            if primitive == FloatNeg {
                let [Constant::F32(value)] = args else {
                    return None;
                };
                return Some(Constant::F32(canonical_f32(-value)));
            }
            let [Constant::F32(left), Constant::F32(right)] = args else {
                return None;
            };
            if comparison {
                let value = match primitive {
                    FloatEq => left == right,
                    FloatNe => left != right,
                    FloatLt => left < right,
                    FloatLe => left <= right,
                    FloatGt => left > right,
                    FloatGe => left >= right,
                    _ => unreachable!(),
                };
                Some(Constant::U32(u32::from(value)))
            } else {
                let value = match primitive {
                    FloatAdd => left + right,
                    FloatSub => left - right,
                    FloatMul => left * right,
                    FloatDiv => left / right,
                    FloatRem => left % right,
                    _ => unreachable!(),
                };
                Some(Constant::F32(canonical_f32(value)))
            }
        }
        F64 => {
            if primitive == FloatNeg {
                let [Constant::F64(value)] = args else {
                    return None;
                };
                return Some(Constant::F64(canonical_f64(-value)));
            }
            let [Constant::F64(left), Constant::F64(right)] = args else {
                return None;
            };
            if comparison {
                let value = match primitive {
                    FloatEq => left == right,
                    FloatNe => left != right,
                    FloatLt => left < right,
                    FloatLe => left <= right,
                    FloatGt => left > right,
                    FloatGe => left >= right,
                    _ => unreachable!(),
                };
                Some(Constant::U32(u32::from(value)))
            } else {
                let value = match primitive {
                    FloatAdd => left + right,
                    FloatSub => left - right,
                    FloatMul => left * right,
                    FloatDiv => left / right,
                    FloatRem => left % right,
                    _ => unreachable!(),
                };
                Some(Constant::F64(canonical_f64(value)))
            }
        }
        _ => None,
    }
}

/// Evaluate only frozen, allocation-free primitives. `None` deliberately means
/// both "unsupported" and "would trap": in either case the original MIR
/// operation remains in place, preserving its exact runtime behavior and span.
fn fold_primitive(
    result_type: TypeId,
    primitive: Primitive,
    arg_types: &[TypeId],
    args: &[Constant],
) -> Option<Constant> {
    use Primitive::*;

    if primitive == CharToU32 {
        let [Constant::Char(value)] = args else {
            return None;
        };
        return (result_type == U32).then_some(Constant::U32(*value as u32));
    }
    if primitive == CharFromU32Checked {
        let [Constant::U32(value)] = args else {
            return None;
        };
        return (result_type == CHAR)
            .then(|| char::from_u32(*value).map(Constant::Char))
            .flatten();
    }
    match (primitive, result_type, arg_types, args) {
        (TextByteLen, USIZE, [TEXT], [Constant::Text(value)]) => {
            return Some(Constant::Usize(value.len() as u64));
        }
        (TextEq, U32, [TEXT, TEXT], [Constant::Text(left), Constant::Text(right)]) => {
            return Some(Constant::U32(u32::from(left == right)));
        }
        (BytesLen, USIZE, [BYTES], [Constant::Bytes(value)]) => {
            return Some(Constant::Usize(value.len() as u64));
        }
        (BytesUtf8ValidUpTo, USIZE, [BYTES], [Constant::Bytes(value)]) => {
            return Some(Constant::Usize(
                std::str::from_utf8(value)
                    .map_or_else(|error| error.valid_up_to(), |_| value.len()) as u64,
            ));
        }
        _ => {}
    }
    if matches!(
        primitive,
        FloatAdd
            | FloatSub
            | FloatMul
            | FloatDiv
            | FloatRem
            | FloatEq
            | FloatNe
            | FloatLt
            | FloatLe
            | FloatGt
            | FloatGe
            | FloatNeg
    ) {
        return fold_float_primitive(result_type, primitive, arg_types, args);
    }

    let source_type = *arg_types.first()?;
    let source = int_spec(source_type)?;
    if args
        .iter()
        .zip(arg_types)
        .any(|(value, ty)| constant_type(value) != *ty)
    {
        return None;
    }
    let unary = || args.first();
    let binary = || match args {
        [left, right] => Some((left, right)),
        _ => None,
    };

    match primitive {
        IntConvertChecked | IntConvertWrapping => {
            let target = int_spec(result_type)?;
            if primitive == IntConvertWrapping {
                let raw = if source.signed {
                    signed_value(source, unary()?)? as u128
                } else {
                    unsigned_value(source, unary()?)?
                };
                return make_int_constant(result_type, raw);
            }
            if source.signed {
                let value = signed_value(source, unary()?)?;
                if target.signed {
                    make_checked_signed(result_type, Some(value))
                } else if value < 0 {
                    None
                } else {
                    make_checked_unsigned(result_type, Some(value as u128))
                }
            } else {
                let value = unsigned_value(source, unary()?)?;
                if target.signed {
                    (value <= signed_bounds(target.bits).1 as u128)
                        .then(|| make_int_constant(result_type, value))
                        .flatten()
                } else {
                    make_checked_unsigned(result_type, Some(value))
                }
            }
        }
        IntEq | IntNe | IntLt | IntLe | IntGt | IntGe => {
            let (left, right) = binary()?;
            let result = if source.signed {
                let (left, right) = (signed_value(source, left)?, signed_value(source, right)?);
                match primitive {
                    IntEq => left == right,
                    IntNe => left != right,
                    IntLt => left < right,
                    IntLe => left <= right,
                    IntGt => left > right,
                    IntGe => left >= right,
                    _ => unreachable!(),
                }
            } else {
                let (left, right) = (
                    unsigned_value(source, left)?,
                    unsigned_value(source, right)?,
                );
                match primitive {
                    IntEq => left == right,
                    IntNe => left != right,
                    IntLt => left < right,
                    IntLe => left <= right,
                    IntGt => left > right,
                    IntGe => left >= right,
                    _ => unreachable!(),
                }
            };
            (result_type == U32).then(|| Constant::U32(u32::from(result)))
        }
        IntBitNot if result_type == source_type => {
            make_int_constant(result_type, !int_raw_value(source, unary()?)?)
        }
        IntCheckedNeg => {
            if result_type != source_type {
                return None;
            }
            if source.signed {
                make_checked_signed(result_type, signed_value(source, unary()?)?.checked_neg())
            } else if unsigned_value(source, unary()?)? == 0 {
                make_int_constant(result_type, 0)
            } else {
                None
            }
        }
        IntWrappingNeg if result_type == source_type => {
            make_int_constant(result_type, int_raw_value(source, unary()?)?.wrapping_neg())
        }
        IntShl | IntShr => {
            if result_type != source_type {
                return None;
            }
            let (value, count) = binary()?;
            let count = shift_count(count)?;
            if count >= source.bits {
                return None;
            }
            let raw = if primitive == IntShl {
                int_raw_value(source, value)? << count
            } else if source.signed {
                (signed_value(source, value)? >> count) as u128
            } else {
                unsigned_value(source, value)? >> count
            };
            make_int_constant(result_type, raw)
        }
        IntCheckedAdd | IntCheckedSub | IntCheckedMul | IntCheckedDiv | IntCheckedRem => {
            if result_type != source_type {
                return None;
            }
            let (left, right) = binary()?;
            if source.signed {
                let (left, right) = (signed_value(source, left)?, signed_value(source, right)?);
                if matches!(primitive, IntCheckedDiv | IntCheckedRem) && right == 0 {
                    return None;
                }
                if matches!(primitive, IntCheckedDiv | IntCheckedRem)
                    && left == signed_bounds(source.bits).0
                    && right == -1
                {
                    return None;
                }
                let value = match primitive {
                    IntCheckedAdd => left.checked_add(right),
                    IntCheckedSub => left.checked_sub(right),
                    IntCheckedMul => left.checked_mul(right),
                    IntCheckedDiv => left.checked_div(right),
                    IntCheckedRem => left.checked_rem(right),
                    _ => unreachable!(),
                };
                make_checked_signed(result_type, value)
            } else {
                let (left, right) = (
                    unsigned_value(source, left)?,
                    unsigned_value(source, right)?,
                );
                if matches!(primitive, IntCheckedDiv | IntCheckedRem) && right == 0 {
                    return None;
                }
                let value = match primitive {
                    IntCheckedAdd => left.checked_add(right),
                    IntCheckedSub => left.checked_sub(right),
                    IntCheckedMul => left.checked_mul(right),
                    IntCheckedDiv => left.checked_div(right),
                    IntCheckedRem => left.checked_rem(right),
                    _ => unreachable!(),
                };
                make_checked_unsigned(result_type, value)
            }
        }
        IntWrappingAdd | IntWrappingSub | IntWrappingMul | IntBitAnd | IntBitOr | IntBitXor => {
            if result_type != source_type {
                return None;
            }
            let (left, right) = binary()?;
            let (left, right) = (int_raw_value(source, left)?, int_raw_value(source, right)?);
            let raw = match primitive {
                IntWrappingAdd => left.wrapping_add(right),
                IntWrappingSub => left.wrapping_sub(right),
                IntWrappingMul => left.wrapping_mul(right),
                IntBitAnd => left & right,
                IntBitOr => left | right,
                IntBitXor => left ^ right,
                _ => unreachable!(),
            };
            make_int_constant(result_type, raw)
        }
        _ => None,
    }
}

#[derive(Clone, Debug, PartialEq)]
enum SparseConstant {
    Unknown,
    Constant(Constant),
    Overdefined,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SparseVariant {
    Unknown,
    Variant(u32),
    Overdefined,
}

fn frozen_constant_eq(left: &Constant, right: &Constant) -> bool {
    match (left, right) {
        (Constant::F32(left), Constant::F32(right)) => left.to_bits() == right.to_bits(),
        (Constant::F64(left), Constant::F64(right)) => left.to_bits() == right.to_bits(),
        _ => left == right,
    }
}

fn sparse_constant_eq(left: &SparseConstant, right: &SparseConstant) -> bool {
    use SparseConstant::{Constant, Overdefined, Unknown};
    match (left, right) {
        (Unknown, Unknown) | (Overdefined, Overdefined) => true,
        (Constant(left), Constant(right)) => frozen_constant_eq(left, right),
        _ => false,
    }
}

fn merge_sparse_constant(slot: &mut SparseConstant, incoming: SparseConstant) -> bool {
    use SparseConstant::{Constant, Overdefined, Unknown};
    let merged = match (&*slot, incoming) {
        (Overdefined, _) | (_, Overdefined) => Overdefined,
        (Unknown, value) => value,
        (value, Unknown) => value.clone(),
        (Constant(left), Constant(right)) if frozen_constant_eq(left, &right) => {
            Constant(left.clone())
        }
        (Constant(_), Constant(_)) => Overdefined,
    };
    if sparse_constant_eq(slot, &merged) {
        false
    } else {
        *slot = merged;
        true
    }
}

fn merge_sparse_variant(slot: &mut SparseVariant, incoming: SparseVariant) -> bool {
    use SparseVariant::{Overdefined, Unknown, Variant};
    let merged = match (*slot, incoming) {
        (Overdefined, _) | (_, Overdefined) => Overdefined,
        (Unknown, value) => value,
        (value, Unknown) => value,
        (Variant(left), Variant(right)) if left == right => Variant(left),
        (Variant(_), Variant(_)) => Overdefined,
    };
    if *slot == merged {
        false
    } else {
        *slot = merged;
        true
    }
}

fn sparse_operand(facts: &[SparseConstant], operand: &Operand) -> SparseConstant {
    facts
        .get(operand.register as usize)
        .cloned()
        .unwrap_or(SparseConstant::Overdefined)
}

fn simplify_integer_identity(
    destination: Register,
    result_type: TypeId,
    primitive: Primitive,
    arguments: &[Operand],
    facts: &[SparseConstant],
    register_types: &[TypeId],
) -> Option<InstructionKind> {
    use Primitive::*;

    if matches!(primitive, IntEq | IntNe | IntLt | IntLe | IntGt | IntGe) {
        let [left, right] = arguments else {
            return None;
        };
        let operand_type = *register_types.get(left.register as usize)?;
        if result_type != U32
            || left.register != right.register
            || left.mode != UseMode::Copy
            || right.mode != UseMode::Copy
            || register_types.get(right.register as usize).copied() != Some(operand_type)
            || int_spec(operand_type).is_none()
        {
            return None;
        }
        let value = matches!(primitive, IntEq | IntLe | IntGe);
        return Some(InstructionKind::Const {
            dst: destination,
            value: Constant::U32(u32::from(value)),
        });
    }

    let result_spec = int_spec(result_type)?;
    let argument_type = |operand: &Operand| {
        register_types
            .get(operand.register as usize)
            .copied()
            .filter(|ty| int_spec(*ty).is_some())
    };
    let raw_constant = |operand: &Operand| {
        let ty = argument_type(operand)?;
        let SparseConstant::Constant(value) = facts.get(operand.register as usize)? else {
            return None;
        };
        int_raw_value(int_spec(ty)?, value)
    };
    let forward = |operand: &Operand| {
        (argument_type(operand)? == result_type).then_some(match operand.mode {
            UseMode::Copy => InstructionKind::Copy {
                dst: destination,
                src: *operand,
            },
            UseMode::Move => InstructionKind::Move {
                dst: destination,
                src: *operand,
            },
        })
    };
    let zero = || {
        Some(InstructionKind::Const {
            dst: destination,
            value: make_int_constant(result_type, 0)?,
        })
    };

    if matches!(primitive, IntConvertChecked | IntConvertWrapping) {
        let [value] = arguments else {
            return None;
        };
        return (argument_type(value)? == result_type)
            .then(|| forward(value))
            .flatten();
    }

    let [left, right] = arguments else {
        return None;
    };
    let left_type = argument_type(left)?;
    let right_type = argument_type(right)?;
    if matches!(primitive, IntShl | IntShr) {
        if left_type != result_type || int_spec(right_type)?.signed {
            return None;
        }
        return (raw_constant(right)? == 0).then(|| forward(left)).flatten();
    }
    if left_type != result_type || right_type != result_type {
        return None;
    }
    let left_constant = raw_constant(left);
    let right_constant = raw_constant(right);
    let all_ones = int_mask(result_spec.bits);
    match primitive {
        IntCheckedAdd | IntWrappingAdd => {
            if left_constant == Some(0) {
                forward(right)
            } else if right_constant == Some(0) {
                forward(left)
            } else {
                None
            }
        }
        IntCheckedSub | IntWrappingSub => {
            (right_constant == Some(0)).then(|| forward(left)).flatten()
        }
        IntCheckedMul | IntWrappingMul => {
            if left_constant == Some(0) || right_constant == Some(0) {
                zero()
            } else if left_constant == Some(1) {
                forward(right)
            } else if right_constant == Some(1) {
                forward(left)
            } else {
                None
            }
        }
        IntCheckedDiv => (right_constant == Some(1)).then(|| forward(left)).flatten(),
        IntCheckedRem => (right_constant == Some(1)).then(zero).flatten(),
        IntBitOr | IntBitXor => {
            if left_constant == Some(0) {
                forward(right)
            } else if right_constant == Some(0) {
                forward(left)
            } else {
                None
            }
        }
        IntBitAnd => {
            if left_constant == Some(0) || right_constant == Some(0) {
                zero()
            } else if left_constant == Some(all_ones) {
                forward(right)
            } else if right_constant == Some(all_ones) {
                forward(left)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn sparse_statement_value(
    statement: &InstructionKind,
    facts: &[SparseConstant],
    variants: &[SparseVariant],
    register_types: &[TypeId],
) -> SparseConstant {
    match statement {
        InstructionKind::Const { value, .. } => SparseConstant::Constant(value.clone()),
        InstructionKind::Copy { src, .. } | InstructionKind::Move { src, .. } => {
            sparse_operand(facts, src)
        }
        InstructionKind::Primitive {
            dst,
            primitive,
            args,
        } => {
            let values = args
                .iter()
                .map(|argument| match sparse_operand(facts, argument) {
                    SparseConstant::Constant(value) => Some(value),
                    SparseConstant::Unknown | SparseConstant::Overdefined => None,
                })
                .collect::<Option<Vec<_>>>();
            let Some(values) = values else {
                return if args.iter().any(|argument| {
                    matches!(sparse_operand(facts, argument), SparseConstant::Overdefined)
                }) {
                    SparseConstant::Overdefined
                } else {
                    SparseConstant::Unknown
                };
            };
            let argument_types = args
                .iter()
                .map(|argument| register_types[argument.register as usize])
                .collect::<Vec<_>>();
            fold_primitive(
                register_types[*dst as usize],
                *primitive,
                &argument_types,
                &values,
            )
            .map(SparseConstant::Constant)
            .unwrap_or(SparseConstant::Overdefined)
        }
        InstructionKind::EnumTag { src, .. } => match variants[*src as usize] {
            SparseVariant::Variant(variant) => SparseConstant::Constant(Constant::U32(variant)),
            SparseVariant::Unknown => SparseConstant::Unknown,
            SparseVariant::Overdefined => SparseConstant::Overdefined,
        },
        InstructionKind::Borrow { .. }
        | InstructionKind::ProjectBorrow { .. }
        | InstructionKind::Reborrow { .. }
        | InstructionKind::DerefCopy { .. }
        | InstructionKind::DerefReborrow { .. }
        | InstructionKind::DerefMove { .. }
        | InstructionKind::Construct { .. }
        | InstructionKind::ProjectCopy { .. }
        | InstructionKind::ProjectMove { .. }
        | InstructionKind::MakeCallable { .. }
        | InstructionKind::MakeHandler { .. }
        | InstructionKind::MakeHandlerShared { .. }
        | InstructionKind::MakeBindingPack { .. } => SparseConstant::Overdefined,
        InstructionKind::EndBorrow { .. }
        | InstructionKind::DerefStore { .. }
        | InstructionKind::Deconstruct { .. }
        | InstructionKind::LabelPush { .. }
        | InstructionKind::LabelPop { .. }
        | InstructionKind::Drop { .. } => SparseConstant::Unknown,
    }
}

fn sparse_statement_variant(
    statement: &InstructionKind,
    variants: &[SparseVariant],
) -> SparseVariant {
    match statement {
        InstructionKind::Construct {
            variant: Some(variant),
            ..
        } => SparseVariant::Variant(*variant),
        InstructionKind::Copy { src, .. } | InstructionKind::Move { src, .. } => {
            variants[src.register as usize]
        }
        InstructionKind::Const { .. }
        | InstructionKind::Borrow { .. }
        | InstructionKind::ProjectBorrow { .. }
        | InstructionKind::Reborrow { .. }
        | InstructionKind::DerefCopy { .. }
        | InstructionKind::DerefReborrow { .. }
        | InstructionKind::DerefMove { .. }
        | InstructionKind::Construct { variant: None, .. }
        | InstructionKind::ProjectCopy { .. }
        | InstructionKind::ProjectMove { .. }
        | InstructionKind::EnumTag { .. }
        | InstructionKind::Primitive { .. }
        | InstructionKind::MakeCallable { .. }
        | InstructionKind::MakeHandler { .. }
        | InstructionKind::MakeHandlerShared { .. }
        | InstructionKind::MakeBindingPack { .. } => SparseVariant::Overdefined,
        InstructionKind::EndBorrow { .. }
        | InstructionKind::DerefStore { .. }
        | InstructionKind::Deconstruct { .. }
        | InstructionKind::LabelPush { .. }
        | InstructionKind::LabelPop { .. }
        | InstructionKind::Drop { .. } => SparseVariant::Unknown,
    }
}

fn enqueue_sparse_users(
    register: Register,
    users: &[BTreeSet<usize>],
    worklist: &mut DenseWorklist,
) {
    for &index in &users[register as usize] {
        worklist.schedule(index);
    }
}

/// Delete unused chains of pure predefined-scalar primitives. Eligibility is
/// deliberately shared with local primitive CSE: every operand is a Copy, the
/// result and arguments are ownership-neutral frozen scalars, and the primitive
/// cannot trap. Registers with more than one definition are excluded because
/// compact MIR narrowly permits ABI-place reconstruction outside strict SSA.
fn eliminate_dead_nontrapping_scalar_primitives(
    function: &mut Function,
    budget: u64,
) -> (PassOutcome, u64) {
    let mut scratch = function.clone();
    let mut work = 0_u64;
    let mut definitions = vec![0_u32; scratch.register_types.len()];
    let mut locations = vec![None; scratch.register_types.len()];
    for (block_index, block) in scratch.blocks.iter().enumerate() {
        for (statement_index, statement) in block.statements.iter().enumerate() {
            work = work.saturating_add(1);
            if work > budget {
                return (PassOutcome::BudgetExhausted, work);
            }
            if let Some(destination) = statement.kind.destination() {
                let count = &mut definitions[destination as usize];
                *count = count.saturating_add(1);
                locations[destination as usize] =
                    (*count == 1).then_some((block_index, statement_index));
            }
        }
        for parameter in &block.params {
            let count = &mut definitions[parameter.register as usize];
            *count = count.saturating_add(1);
            locations[parameter.register as usize] = None;
        }
    }
    if scratch.receiver_mode.is_some() && !definitions.is_empty() {
        definitions[0] = definitions[0].saturating_add(1);
        locations[0] = None;
    }
    for register in 1..=scratch
        .params
        .len()
        .min(definitions.len().saturating_sub(1))
    {
        definitions[register] = definitions[register].saturating_add(1);
        locations[register] = None;
    }

    let mut candidate_arguments = vec![None; scratch.register_types.len()];
    for (register, location) in locations.iter().copied().enumerate() {
        if definitions[register] != 1 {
            continue;
        }
        let Some((block, statement)) = location else {
            continue;
        };
        let InstructionKind::Primitive {
            dst,
            primitive,
            args,
        } = &scratch.blocks[block].statements[statement].kind
        else {
            continue;
        };
        if primitive_cse_key(&scratch, *dst, *primitive, args).is_some() {
            candidate_arguments[register] = Some(
                args.iter()
                    .map(|argument| argument.register)
                    .collect::<Vec<_>>(),
            );
        }
    }

    let mut uses = register_uses(&scratch);
    let mut worklist = DenseWorklist::new(uses.len());
    for register in 0..uses.len() {
        if uses[register] == 0 && candidate_arguments[register].is_some() {
            worklist.schedule(register);
        }
    }
    let mut removed = scratch
        .blocks
        .iter()
        .map(|block| vec![false; block.statements.len()])
        .collect::<Vec<_>>();
    let mut changed = false;
    while let Some(register) = worklist.pop() {
        work = work.saturating_add(1);
        if work > budget {
            return (PassOutcome::BudgetExhausted, work);
        }
        if uses[register] != 0 {
            continue;
        }
        let Some(arguments) = candidate_arguments[register].take() else {
            continue;
        };
        let Some((block, statement)) = locations[register] else {
            continue;
        };
        removed[block][statement] = true;
        changed = true;
        for argument in arguments {
            uses[argument as usize] = uses[argument as usize].saturating_sub(1);
            if uses[argument as usize] == 0 && candidate_arguments[argument as usize].is_some() {
                worklist.schedule(argument as usize);
            }
        }
    }

    if !changed {
        return (PassOutcome::Unchanged, work);
    }
    for (block, removed) in scratch.blocks.iter_mut().zip(removed) {
        let mut statement_index = 0_usize;
        block.statements.retain(|_| {
            let keep = !removed[statement_index];
            statement_index += 1;
            keep
        });
    }
    scratch.features = infer_feature_bits(&scratch);
    *function = scratch;
    (PassOutcome::Changed, work)
}

fn sparse_simplify(function: &mut Function, types: &[Type], budget: u64) -> (PassOutcome, u64) {
    // DEREF_STORE is an in-place definition of the referenced owner rather
    // than an SSA-register definition.  Until SCCP carries exact place/alias
    // kills, retaining a pre-store constant or enum fact for that owner would
    // be unsound.  DEREF_MOVE is paired with the same transient hole state, so
    // keep the whole pair outside this value-only analysis.
    if function.blocks.iter().any(|block| {
        block.statements.iter().any(|statement| {
            matches!(
                statement.kind,
                InstructionKind::DerefMove { .. } | InstructionKind::DerefStore { .. }
            )
        })
    }) {
        return (PassOutcome::Unchanged, 0);
    }
    if !function.features.contains(FeatureBits::SWITCHES)
        && !function.blocks.iter().any(|block| {
            block.statements.iter().any(|statement| {
                matches!(
                    statement.kind,
                    InstructionKind::Const { .. }
                        | InstructionKind::Copy { .. }
                        | InstructionKind::Move { .. }
                        | InstructionKind::Construct { .. }
                        | InstructionKind::EnumTag { .. }
                        | InstructionKind::Primitive { .. }
                )
            })
        })
    {
        return (PassOutcome::Unchanged, 0);
    }
    let mut scratch = function.clone();
    let mut work = 0_u64;
    let mut changed = false;
    // Registers are SSA identities except for narrowly validated ABI-place
    // reconstruction. Mark every multiply-defined identity overdefined so SCCP
    // cannot accidentally treat such a place as an immutable value.
    let mut definitions = vec![0_u32; scratch.register_types.len()];
    if function.receiver_mode.is_some() && !definitions.is_empty() {
        definitions[0] = 1;
    }
    for definition in definitions
        .iter_mut()
        .take(scratch.params.len() + 1)
        .skip(1)
    {
        *definition = definition.saturating_add(1);
    }
    for block in &scratch.blocks {
        for parameter in &block.params {
            definitions[parameter.register as usize] =
                definitions[parameter.register as usize].saturating_add(1);
        }
        for statement in &block.statements {
            if let Some(destination) = statement.kind.destination() {
                definitions[destination as usize] =
                    definitions[destination as usize].saturating_add(1);
            }
        }
    }

    let mut facts = definitions
        .iter()
        .map(|count| {
            if *count > 1 {
                SparseConstant::Overdefined
            } else {
                SparseConstant::Unknown
            }
        })
        .collect::<Vec<_>>();
    let mut variants = definitions
        .iter()
        .map(|count| {
            if *count > 1 {
                SparseVariant::Overdefined
            } else {
                SparseVariant::Unknown
            }
        })
        .collect::<Vec<_>>();
    if function.receiver_mode.is_some() && !facts.is_empty() {
        facts[0] = SparseConstant::Overdefined;
        variants[0] = SparseVariant::Overdefined;
    }
    for (fact, variant) in facts
        .iter_mut()
        .zip(&mut variants)
        .take(scratch.params.len() + 1)
        .skip(1)
    {
        *fact = SparseConstant::Overdefined;
        *variant = SparseVariant::Overdefined;
    }

    let block_indices = scratch
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| (block.id, index))
        .collect::<BTreeMap<_, _>>();
    // SCCP reasons about the currently executable predecessor subset. Some
    // protected-control and cleanup predecessors deliberately remain in MIR
    // even when that subset excludes them, so a fact derived through a
    // multi-predecessor parameter cannot be baked into the retained code.
    // Propagate that structural join dependency through values and use it as
    // a fail-closed barrier for branch and instruction folding.
    let mut predecessor_counts = BTreeMap::<u32, usize>::new();
    for block in &scratch.blocks {
        for_each_edge(&block.terminator, |edge| {
            *predecessor_counts.entry(edge.target).or_default() += 1;
        });
    }
    let mut join_dependencies = vec![Vec::<Register>::new(); scratch.register_types.len()];
    let mut structurally_joined = vec![false; scratch.register_types.len()];
    for block in &scratch.blocks {
        if predecessor_counts.get(&block.id).copied().unwrap_or(0) > 1 {
            for parameter in &block.params {
                structurally_joined[parameter.register as usize] = true;
            }
        }
        for statement in &block.statements {
            if let Some(destination) = statement.kind.destination() {
                statement.kind.for_each_register_use(|source, _| {
                    join_dependencies[source as usize].push(destination);
                });
            }
        }
        for_each_edge(&block.terminator, |edge| {
            let parameters = &scratch.blocks[block_indices[&edge.target]].params;
            let implicit = parameters.len().saturating_sub(edge.args.len());
            for (parameter, argument) in parameters[implicit..].iter().zip(&edge.args) {
                join_dependencies[argument.register as usize].push(parameter.register);
            }
        });
    }
    let mut joined_work = std::collections::VecDeque::new();
    for (register, joined) in structurally_joined.iter().copied().enumerate() {
        if joined {
            joined_work.push_back(register as Register);
        }
    }
    while let Some(source) = joined_work.pop_front() {
        for &destination in &join_dependencies[source as usize] {
            if !structurally_joined[destination as usize] {
                structurally_joined[destination as usize] = true;
                joined_work.push_back(destination);
            }
        }
    }
    let mut reachable = vec![false; scratch.blocks.len()];
    let mut users = vec![BTreeSet::<usize>::new(); scratch.register_types.len()];
    for (block_index, block) in scratch.blocks.iter().enumerate() {
        for register in used_registers(block) {
            users[register as usize].insert(block_index);
        }
    }
    let mut worklist = DenseWorklist::new(scratch.blocks.len());
    let entry_index = block_indices[&scratch.entry];
    reachable[entry_index] = true;
    worklist.schedule(entry_index);

    while let Some(block_index) = worklist.pop() {
        if !reachable[block_index] {
            continue;
        }
        let block = &scratch.blocks[block_index];
        work = work.saturating_add(block.statements.len() as u64 + 1);
        if work > budget {
            return (PassOutcome::BudgetExhausted, work);
        }
        for statement in &block.statements {
            let Some(destination) = statement.kind.destination() else {
                continue;
            };
            if definitions[destination as usize] != 1 {
                continue;
            }
            let incoming =
                sparse_statement_value(&statement.kind, &facts, &variants, &scratch.register_types);
            let constant_changed =
                merge_sparse_constant(&mut facts[destination as usize], incoming);
            let incoming_variant = sparse_statement_variant(&statement.kind, &variants);
            let variant_changed =
                merge_sparse_variant(&mut variants[destination as usize], incoming_variant);
            if constant_changed || variant_changed {
                enqueue_sparse_users(destination, &users, &mut worklist);
            }
        }

        let executable_edges = match &block.terminator {
            Terminator::Switch {
                discr,
                cases,
                otherwise,
            } => match if structurally_joined[discr.register as usize] {
                SparseConstant::Overdefined
            } else {
                sparse_operand(&facts, discr)
            } {
                SparseConstant::Constant(value) => vec![
                    cases
                        .iter()
                        .find_map(|(candidate, edge)| {
                            frozen_constant_eq(candidate, &value).then(|| edge.clone())
                        })
                        .unwrap_or_else(|| otherwise.clone()),
                ],
                SparseConstant::Overdefined => cases
                    .iter()
                    .map(|(_, edge)| edge.clone())
                    .chain(std::iter::once(otherwise.clone()))
                    .collect(),
                // An undefined discriminator may still become a constant. SCCP
                // waits rather than prematurely making every successor live.
                SparseConstant::Unknown => Vec::new(),
            },
            terminator => {
                let mut edges = Vec::new();
                for_each_edge(terminator, |edge| edges.push(edge.clone()));
                edges
            }
        };

        for edge in executable_edges {
            let target_index = block_indices[&edge.target];
            if !reachable[target_index] {
                reachable[target_index] = true;
                worklist.schedule(target_index);
            }
            let parameters = &scratch.blocks[target_index].params;
            let implicit = parameters.len().saturating_sub(edge.args.len());
            for parameter in &parameters[..implicit] {
                if merge_sparse_constant(
                    &mut facts[parameter.register as usize],
                    SparseConstant::Overdefined,
                ) | merge_sparse_variant(
                    &mut variants[parameter.register as usize],
                    SparseVariant::Overdefined,
                ) {
                    enqueue_sparse_users(parameter.register, &users, &mut worklist);
                }
            }
            for (parameter, argument) in parameters[implicit..].iter().zip(edge.args.iter()) {
                let incoming = sparse_operand(&facts, argument);
                let incoming_variant = variants[argument.register as usize];
                if merge_sparse_constant(&mut facts[parameter.register as usize], incoming)
                    | merge_sparse_variant(
                        &mut variants[parameter.register as usize],
                        incoming_variant,
                    )
                {
                    enqueue_sparse_users(parameter.register, &users, &mut worklist);
                }
            }
        }
    }

    for block in &mut scratch.blocks {
        for statement in &mut block.statements {
            let destination_is_joined = statement
                .kind
                .destination()
                .is_some_and(|destination| structurally_joined[destination as usize]);
            let replacement = match &statement.kind {
                InstructionKind::Primitive {
                    dst,
                    primitive,
                    args,
                } if !destination_is_joined => match &facts[*dst as usize] {
                    SparseConstant::Constant(value) => Some(InstructionKind::Const {
                        dst: *dst,
                        value: value.clone(),
                    }),
                    SparseConstant::Unknown | SparseConstant::Overdefined => {
                        simplify_integer_identity(
                            *dst,
                            scratch.register_types[*dst as usize],
                            *primitive,
                            args,
                            &facts,
                            &scratch.register_types,
                        )
                    }
                },
                InstructionKind::EnumTag { dst, .. } if !destination_is_joined => {
                    if let SparseConstant::Constant(value) = &facts[*dst as usize] {
                        Some(InstructionKind::Const {
                            dst: *dst,
                            value: value.clone(),
                        })
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(replacement) = replacement {
                statement.kind = replacement;
                changed = true;
            }
        }
        if let Terminator::Switch {
            discr,
            cases,
            otherwise,
        } = &block.terminator
            && types[scratch.register_types[discr.register as usize] as usize]
                .claimed_zero_use_allowed()
            && !structurally_joined[discr.register as usize]
            && let SparseConstant::Constant(value) = &facts[discr.register as usize]
        {
            let selected = cases
                .iter()
                .find_map(|(candidate, edge)| {
                    frozen_constant_eq(candidate, value).then(|| edge.clone())
                })
                .unwrap_or_else(|| otherwise.clone());
            block.terminator = Terminator::Goto(selected);
            changed = true;
        }
    }
    let (dead_primitives, dead_primitive_work) =
        eliminate_dead_nontrapping_scalar_primitives(&mut scratch, budget.saturating_sub(work));
    work = work.saturating_add(dead_primitive_work);
    if dead_primitives == PassOutcome::BudgetExhausted {
        return (PassOutcome::BudgetExhausted, work);
    }
    changed |= dead_primitives == PassOutcome::Changed;

    let uses = register_uses(&scratch);
    for block in &mut scratch.blocks {
        block.statements.retain(|statement| {
            let InstructionKind::Const { dst, .. } = statement.kind else {
                return true;
            };
            // Explicit Drop and return-cleanup dispositions count as uses.
            // They are never erased merely because the produced structural
            // value is otherwise dead (mir-design.md section 7.2).
            let dead = uses[dst as usize] == 0
                && types[scratch.register_types[dst as usize] as usize].claimed_zero_use_allowed();
            changed |= dead;
            !dead
        });
    }
    let (forwarding, forwarding_work) =
        local_forward_moves(&mut scratch, budget.saturating_sub(work));
    work = work.saturating_add(forwarding_work);
    if forwarding == PassOutcome::BudgetExhausted {
        return (PassOutcome::BudgetExhausted, work);
    }
    changed |= forwarding == PassOutcome::Changed;
    scratch.features = infer_feature_bits(&scratch);
    *function = scratch;
    (
        if changed {
            PassOutcome::Changed
        } else {
            PassOutcome::Unchanged
        },
        work,
    )
}

fn instruction_register_use_count(instruction: &InstructionKind, register: Register) -> usize {
    let mut count = 0;
    instruction.for_each_register_use(|used, _| count += usize::from(used == register));
    count
}

fn terminator_register_use_count(terminator: &Terminator, register: Register) -> usize {
    let mut count = 0;
    terminator.for_each_register_use(|used, _| count += usize::from(used == register));
    count
}

fn predefined_no_drop_scalar(ty: TypeId) -> bool {
    matches!(
        ty,
        UNIT | U8
            | U16
            | U32
            | U64
            | U128
            | USIZE
            | I8
            | I16
            | I32
            | I64
            | I128
            | ISIZE
            | F32
            | F64
            | CHAR
    )
}

fn local_forwarding_use_is_safe(instruction: &InstructionKind, register: Register) -> bool {
    match instruction {
        InstructionKind::Copy { src, .. } | InstructionKind::Move { src, .. } => {
            src.register == register
        }
        InstructionKind::Primitive { args, .. } => {
            args.iter().any(|operand| operand.register == register)
        }
        InstructionKind::Drop { owner } => owner.register == register,
        _ => instruction_register_use_count(instruction, register) == 0,
    }
}

/// Remove a same-block scalar Move used only as an ownership-neutral register
/// rename. The moved source takes the destination's exact later uses, so the
/// dynamic owned disposition and every later operand mode remain unchanged.
///
/// Copy is intentionally not handled: erasing a Copy changes the dynamic copy
/// and owner count even for a predefined scalar. Aggregate/custom-drop values,
/// loans, handlers, resumptions, captures, edge arguments, and cross-block uses
/// likewise stay untouched until richer ownership and cleanup facts exist.
fn local_forward_moves(function: &mut Function, budget: u64) -> (PassOutcome, u64) {
    if function.features.contains(FeatureBits::LOANS)
        || function.features.contains(FeatureBits::HANDLERS)
        || function.features.contains(FeatureBits::RESUMPTIONS)
    {
        return (PassOutcome::Unchanged, 0);
    }
    let mut scratch = function.clone();
    let mut work = 0_u64;
    let mut changed = false;
    loop {
        let uses = register_uses(&scratch);
        let mut candidate = None;
        'blocks: for (block_index, block) in scratch.blocks.iter().enumerate() {
            for (statement_index, statement) in block.statements.iter().enumerate() {
                work = work.saturating_add(block.statements.len() as u64 + 1);
                if work > budget {
                    return (PassOutcome::BudgetExhausted, work);
                }
                let InstructionKind::Move {
                    dst,
                    src:
                        Operand {
                            register: source,
                            mode: UseMode::Move,
                        },
                } = statement.kind
                else {
                    continue;
                };
                if dst == source
                    || scratch.register_types.get(dst as usize)
                        != scratch.register_types.get(source as usize)
                    || !scratch
                        .register_types
                        .get(dst as usize)
                        .copied()
                        .is_some_and(predefined_no_drop_scalar)
                    || scratch.return_cleanup.contains(&dst)
                    || scratch.return_cleanup.contains(&source)
                {
                    continue;
                }
                let before = &block.statements[..statement_index];
                let after = &block.statements[statement_index + 1..];
                let source_before = before
                    .iter()
                    .map(|prior| instruction_register_use_count(&prior.kind, source))
                    .sum::<usize>();
                let destination_after = after
                    .iter()
                    .map(|later| instruction_register_use_count(&later.kind, dst))
                    .sum::<usize>()
                    + terminator_register_use_count(&block.terminator, dst);
                if destination_after == 0
                    || before
                        .iter()
                        .any(|prior| instruction_register_use_count(&prior.kind, dst) != 0)
                    || after.iter().any(|later| {
                        instruction_register_use_count(&later.kind, source) != 0
                            || !local_forwarding_use_is_safe(&later.kind, dst)
                            || later.kind.destination() == Some(source)
                    })
                    || terminator_register_use_count(&block.terminator, source) != 0
                    || !matches!(
                        &block.terminator,
                        Terminator::Return { value: Some(value) }
                            if value.register == dst
                    ) && terminator_register_use_count(&block.terminator, dst) != 0
                    || uses[source as usize] != (source_before + 1) as u32
                    || uses[dst as usize] != destination_after as u32
                {
                    continue;
                }
                candidate = Some((block_index, statement_index, dst, source));
                break 'blocks;
            }
        }
        let Some((block_index, statement_index, destination, source)) = candidate else {
            break;
        };
        let block_id = super::BlockId(scratch.blocks[block_index].id);
        let mut editor = CheckedCfg::new(&scratch, ResourceLimits::default())
            .expect("validated MIR must open in the checked CFG editor");
        editor
            .remove_statement(block_id, statement_index)
            .expect("selected statement exists");
        debug_assert_eq!(editor.invalidated() & analysis::CFG, 0);
        editor
            .commit(&mut scratch)
            .expect("statement removal cannot invalidate CFG targets");
        let block = scratch
            .blocks
            .iter_mut()
            .find(|block| block.id == block_id.0)
            .expect("checked editor preserves the containing block identity");
        replace_block_uses(block, destination, source);
        changed = true;
    }
    scratch.features = infer_feature_bits(&scratch);
    *function = scratch;
    (
        if changed {
            PassOutcome::Changed
        } else {
            PassOutcome::Unchanged
        },
        work,
    )
}

/// Remove cleanup operations whose exported facts prove that they have neither
/// a custom hook nor structural work. This is the first drop-flag SCCP slice:
/// a `DestroyIf` for a cleanup-free owner is constant no-op, and an all-false
/// residual bitmap has no initialized field to visit. The source `Drop` is
/// erased only when zero use is admitted, so optimization cannot discharge a
/// must-move obligation or make malformed ownership flow acceptable.
///
/// Control-bearing bodies and protected block parameters remain hard barriers.
/// Removing an operation never permutes its neighbors, preserving reverse
/// destruction order. Cleanup actions and now-dead flag facts are updated in
/// the same transaction so the mandatory cleanup checkpoint can rederive the
/// exact result.
fn structurally_empty_drop_type(
    types: &[Type],
    direct_custom_drop_types: &BTreeSet<TypeId>,
    ty: TypeId,
) -> bool {
    fn descriptor(
        types: &[Type],
        direct_custom_drop_types: &BTreeSet<TypeId>,
        ty: &Type,
        visiting: &mut BTreeSet<TypeId>,
    ) -> bool {
        match ty {
            Type::Restricted { base, .. } => {
                descriptor(types, direct_custom_drop_types, base, visiting)
            }
            Type::Unit
            | Type::Never
            | Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::U128
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::I128
            | Type::Usize
            | Type::Isize
            | Type::F32
            | Type::F64
            | Type::Char => true,
            Type::Tuple { fields, .. } => fields
                .iter()
                .all(|field| by_id(types, direct_custom_drop_types, *field, visiting)),
            Type::Struct { fields, .. } => fields
                .iter()
                .all(|field| by_id(types, direct_custom_drop_types, field.ty, visiting)),
            Type::Enum { variants, .. } => variants.iter().all(|variant| {
                variant
                    .fields
                    .iter()
                    .all(|field| by_id(types, direct_custom_drop_types, field.ty, visiting))
            }),
            Type::Text
            | Type::Bytes
            | Type::Array { .. }
            | Type::RefShared { .. }
            | Type::RefUnique { .. }
            | Type::Callable { .. }
            | Type::Handler { .. }
            | Type::Resumption { .. }
            | Type::BindingPack { .. }
            | Type::Available { .. } => false,
        }
    }
    fn by_id(
        types: &[Type],
        direct_custom_drop_types: &BTreeSet<TypeId>,
        ty: TypeId,
        visiting: &mut BTreeSet<TypeId>,
    ) -> bool {
        if direct_custom_drop_types.contains(&ty) {
            return false;
        }
        let Some(value) = types.get(ty as usize) else {
            return false;
        };
        if !visiting.insert(ty) {
            return false;
        }
        let empty = descriptor(types, direct_custom_drop_types, value, visiting);
        visiting.remove(&ty);
        empty
    }
    by_id(types, direct_custom_drop_types, ty, &mut BTreeSet::new())
}

fn remove_proven_empty_drops(
    function: &mut Function,
    types: &[Type],
    direct_custom_drop_types: &BTreeSet<TypeId>,
    budget: u64,
) -> (bool, u64, bool) {
    if function.flow.provenance != FlowProvenance::Exported
        || !function.flow.labels.is_empty()
        || !function.flow.handlers.is_empty()
        || !function.flow.performs.is_empty()
        || !function.flow.resumptions.is_empty()
        // Explicit scalar drops may be the proof that old ABI parameters are
        // dead before a later self-tail backedge rewrite. Keep them until tail
        // formation learns cleanup-free overwrite facts directly.
        || function.features.contains(FeatureBits::TAIL_CALLS)
        || function.blocks.iter().any(|block| {
            block
                .params
                .iter()
                .any(|param| param.role == BlockParamRole::ProtectedExitValue)
        })
    {
        return (false, 0, false);
    }

    let protected = function
        .flow
        .cleanup_plans
        .iter()
        .flat_map(|plan| plan.protected.iter().copied())
        .collect::<BTreeSet<_>>();
    let empty_residuals = function
        .flow
        .cleanup_plans
        .iter()
        .flat_map(|plan| &plan.actions)
        .filter_map(|action| match action {
            CleanupAction::DestroyResidual {
                local,
                initialized_fields,
            } if initialized_fields.iter().all(|initialized| !initialized) => Some(*local),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let drop_owners = function
        .blocks
        .iter()
        .flat_map(|block| &block.statements)
        .filter_map(|statement| match &statement.kind {
            InstructionKind::Drop { owner } => Some(owner.register),
            _ => None,
        })
        .chain(function.return_cleanup.iter().copied())
        .collect::<BTreeSet<_>>();
    let removable = function
        .flow
        .locals
        .iter()
        .enumerate()
        .filter_map(|(register, fact)| {
            let register = register as Register;
            (drop_owners.contains(&register)
                && !protected.contains(&register)
                && fact.use_interval.admits_zero_use()
                && (fact.drop_glue == DropGlueKind::None
                    || (fact.drop_glue != DropGlueKind::Custom
                        && structurally_empty_drop_type(types, direct_custom_drop_types, fact.ty))
                    || (fact.drop_glue != DropGlueKind::Custom
                        && empty_residuals.contains(&register))))
            .then_some(register)
        })
        .collect::<BTreeSet<_>>();
    if removable.is_empty() {
        return (false, 0, false);
    }

    let mut work = 0_u64;
    let mut changed = false;
    for block in &mut function.blocks {
        let before = block.statements.len();
        block.statements.retain(|statement| {
            work = work.saturating_add(1);
            !matches!(
                statement.kind,
                InstructionKind::Drop { ref owner } if removable.contains(&owner.register)
            )
        });
        changed |= block.statements.len() != before;
        if work > budget {
            return (false, work, true);
        }
    }
    let cleanup_len = function.return_cleanup.len();
    function
        .return_cleanup
        .retain(|register| !removable.contains(register));
    changed |= cleanup_len != function.return_cleanup.len();
    if !changed {
        return (false, work, false);
    }

    for plan in &mut function.flow.cleanup_plans {
        plan.actions.retain(|action| match action {
            CleanupAction::Destroy(local)
            | CleanupAction::DestroyIf { local, .. }
            | CleanupAction::DestroyResidual { local, .. } => !removable.contains(local),
            CleanupAction::EndBorrow(_) => true,
        });
    }
    function
        .flow
        .drop_flags
        .retain(|fact| !removable.contains(&fact.owner));
    (true, work, false)
}

/// Share byte-for-byte equivalent cleanup tails without changing the dynamic
/// cleanup sequence on any edge. Drops not proven empty above remain exact: an
/// apparently redundant operation can still encode a custom hook, structural
/// destruction, or an ownership error which validation must reject rather than
/// optimization making acceptable.
///
/// Parameter-free tails are the only ones shared here.  This excludes protected
/// exit values and implicit call/handler/resumption results until cleanup-place
/// identities and drop-flag facts are represented directly in MIR.  Exact
/// register operands, action order, source information, and terminators must
/// match. The normative cleanup graph may share actions from different source
/// locations only while retaining each incoming operation's source info; this
/// compact MIR cannot encode that per-edge provenance yet.
fn simplify_cleanup(
    function: &mut Function,
    types: &[Type],
    direct_custom_drop_types: &BTreeSet<TypeId>,
    budget: u64,
) -> (PassOutcome, u64) {
    if !function.features.contains(FeatureBits::DROPS) {
        return (PassOutcome::Unchanged, 0);
    }

    let mut scratch = function.clone();
    let mut work = 0_u64;
    let mut changed = false;

    let (removed_empty, empty_work, exhausted) =
        remove_proven_empty_drops(&mut scratch, types, direct_custom_drop_types, budget);
    work = work.saturating_add(empty_work);
    if exhausted {
        return (PassOutcome::BudgetExhausted, work);
    }
    changed |= removed_empty;

    loop {
        let mut cleanup_blocks = scratch
            .blocks
            .iter()
            .filter(|block| {
                block.id != scratch.entry
                    && block.params.is_empty()
                    && !block.statements.is_empty()
                    && block
                        .statements
                        .iter()
                        .all(|statement| matches!(statement.kind, InstructionKind::Drop { .. }))
            })
            .map(|block| block.id)
            .collect::<Vec<_>>();
        cleanup_blocks.sort_unstable();

        let mut duplicate = None;
        'search: for (left_index, &canonical_id) in cleanup_blocks.iter().enumerate() {
            let canonical = scratch
                .blocks
                .iter()
                .find(|block| block.id == canonical_id)
                .expect("selected cleanup block exists");
            for &candidate_id in &cleanup_blocks[left_index + 1..] {
                work = work.saturating_add(canonical.statements.len() as u64 + 1);
                if work > budget {
                    return (PassOutcome::BudgetExhausted, work);
                }
                let candidate = scratch
                    .blocks
                    .iter()
                    .find(|block| block.id == candidate_id)
                    .expect("selected cleanup block exists");
                let same_actions = canonical.statements == candidate.statements;
                let cyclic_pair = successors(&canonical.terminator)
                    .into_iter()
                    .any(|target| target == canonical_id || target == candidate_id);
                if same_actions && canonical.terminator == candidate.terminator && !cyclic_pair {
                    duplicate = Some((canonical_id, candidate_id));
                    break 'search;
                }
            }
        }

        let Some((canonical, removed)) = duplicate else {
            break;
        };
        for block in &mut scratch.blocks {
            for_each_edge_mut(&mut block.terminator, |edge| {
                if edge.target == removed {
                    edge.target = canonical;
                }
            });
        }
        scratch.blocks.retain(|block| block.id != removed);
        changed = true;
    }

    scratch.features = infer_feature_bits(&scratch);
    *function = scratch;
    (
        if changed {
            PassOutcome::Changed
        } else {
            PassOutcome::Unchanged
        },
        work,
    )
}

/// Factor a common, byte-for-byte cleanup suffix after control and callable
/// specialization have exposed it.  This first O2 slice never removes or
/// reorders a `Drop`; it only gives two parameter-free cleanup paths one shared
/// execution site.  Equal spans are required until MIR can retain per-origin
/// cleanup source information on a shared action.
fn specialize_cleanup(function: &mut Function, types: &[Type], budget: u64) -> (PassOutcome, u64) {
    if !function.features.contains(FeatureBits::DROPS) {
        return (PassOutcome::Unchanged, 0);
    }

    fn reaches_either(function: &Function, starts: Vec<u32>, left: u32, right: u32) -> bool {
        let mut seen = BTreeSet::new();
        let mut queue = VecDeque::from(starts);
        while let Some(block_id) = queue.pop_front() {
            if block_id == left || block_id == right {
                return true;
            }
            if !seen.insert(block_id) {
                continue;
            }
            let Some(block) = function.blocks.iter().find(|block| block.id == block_id) else {
                continue;
            };
            queue.extend(successors(&block.terminator));
        }
        false
    }

    #[derive(Clone, Copy)]
    struct Candidate {
        left: u32,
        right: u32,
        suffix: usize,
    }

    let mut scratch = function.clone();
    let mut work = 0_u64;
    let mut changed = false;
    loop {
        let mut cleanup_blocks = scratch
            .blocks
            .iter()
            .filter(|block| {
                block.id != scratch.entry
                    && block.params.is_empty()
                    && !block.statements.is_empty()
                    && block
                        .statements
                        .iter()
                        .all(|statement| matches!(statement.kind, InstructionKind::Drop { .. }))
            })
            .map(|block| block.id)
            .collect::<Vec<_>>();
        cleanup_blocks.sort_unstable();

        let mut best = None::<Candidate>;
        for (left_index, &left_id) in cleanup_blocks.iter().enumerate() {
            let left = scratch
                .blocks
                .iter()
                .find(|block| block.id == left_id)
                .expect("selected cleanup block exists");
            for &right_id in &cleanup_blocks[left_index + 1..] {
                let right = scratch
                    .blocks
                    .iter()
                    .find(|block| block.id == right_id)
                    .expect("selected cleanup block exists");
                let comparison_work = left.statements.len().min(right.statements.len()) as u64 + 1;
                work = work.saturating_add(comparison_work);
                if work > budget {
                    return (PassOutcome::BudgetExhausted, work);
                }
                if left.terminator != right.terminator
                    || reaches_either(&scratch, successors(&left.terminator), left_id, right_id)
                {
                    continue;
                }
                let suffix = left
                    .statements
                    .iter()
                    .rev()
                    .zip(right.statements.iter().rev())
                    // Instruction equality deliberately includes Span.
                    .take_while(|(left, right)| left == right)
                    .count();
                if suffix == 0
                    || (suffix == left.statements.len() && suffix == right.statements.len())
                {
                    continue;
                }
                let candidate = Candidate {
                    left: left_id,
                    right: right_id,
                    suffix,
                };
                if best.is_none_or(|current| {
                    (
                        candidate.suffix,
                        std::cmp::Reverse(candidate.left),
                        std::cmp::Reverse(candidate.right),
                    ) > (
                        current.suffix,
                        std::cmp::Reverse(current.left),
                        std::cmp::Reverse(current.right),
                    )
                }) {
                    best = Some(candidate);
                }
            }
        }

        let Some(candidate) = best else {
            break;
        };
        let rewrite_work = candidate.suffix as u64 + 2;
        work = work.saturating_add(rewrite_work);
        if work > budget {
            return (PassOutcome::BudgetExhausted, work);
        }

        let left_index = scratch
            .blocks
            .iter()
            .position(|block| block.id == candidate.left)
            .expect("selected cleanup block exists");
        let right_index = scratch
            .blocks
            .iter()
            .position(|block| block.id == candidate.right)
            .expect("selected cleanup block exists");
        let left_len = scratch.blocks[left_index].statements.len();
        let right_len = scratch.blocks[right_index].statements.len();
        let shared = if candidate.suffix == left_len {
            candidate.left
        } else if candidate.suffix == right_len {
            candidate.right
        } else {
            let Some(id) = scratch
                .blocks
                .iter()
                .map(|block| block.id)
                .max()
                .unwrap_or(0)
                .checked_add(1)
            else {
                return (PassOutcome::BudgetExhausted, work);
            };
            let statements =
                scratch.blocks[left_index].statements[left_len - candidate.suffix..].to_vec();
            let terminator = scratch.blocks[left_index].terminator.clone();
            scratch.blocks.push(BasicBlock {
                id,
                params: vec![],
                statements,
                terminator,
            });
            id
        };

        for (index, len) in [(left_index, left_len), (right_index, right_len)] {
            if scratch.blocks[index].id == shared {
                continue;
            }
            scratch.blocks[index]
                .statements
                .truncate(len - candidate.suffix);
            scratch.blocks[index].terminator = Terminator::Goto(Edge {
                target: shared,
                args: vec![],
            });
        }
        changed = true;
    }

    let remaining = budget.saturating_sub(work);
    let direct_custom_drop_types = scratch
        .flow
        .locals
        .iter()
        .filter_map(|fact| (fact.drop_glue == DropGlueKind::Custom).then_some(fact.ty))
        .collect::<BTreeSet<_>>();
    let (merge_outcome, merge_work) =
        simplify_cleanup(&mut scratch, types, &direct_custom_drop_types, remaining);
    work = work.saturating_add(merge_work);
    if merge_outcome == PassOutcome::BudgetExhausted {
        return (PassOutcome::BudgetExhausted, work);
    }
    changed |= merge_outcome == PassOutcome::Changed;
    scratch.features = infer_feature_bits(&scratch);
    *function = scratch;
    (
        if changed {
            PassOutcome::Changed
        } else {
            PassOutcome::Unchanged
        },
        work,
    )
}

/// Erase reference values whose only dynamic use is ending the loan they
/// represent. Ownership and loan validity have already been proved before the
/// optimizer runs, so such a borrow/`EndBorrow` pair is proof-only. Any runtime
/// observation, edge transfer, cleanup disposition, or continuation capture is
/// counted as an additional use and is therefore a hard barrier.
///
/// The loop is intentional: removing a proof-only reborrow can expose its
/// parent reference as proof-only in the next round.
fn erase_loan_proofs(function: &mut Function, budget: u64) -> (PassOutcome, u64) {
    if !function.features.contains(FeatureBits::LOANS) {
        return (PassOutcome::Unchanged, 0);
    }
    let mut scratch = function.clone();
    let mut changed = false;
    let mut work = 0_u64;

    loop {
        work = work.saturating_add(
            scratch
                .blocks
                .iter()
                .map(|block| block.statements.len() as u64 + 1)
                .sum::<u64>(),
        );
        if work > budget {
            return (PassOutcome::BudgetExhausted, work);
        }
        let uses = register_uses(&scratch);
        let mut proof_definitions = BTreeSet::new();
        let mut end_counts = BTreeMap::<Register, u32>::new();
        for block in &scratch.blocks {
            for statement in &block.statements {
                match statement.kind {
                    InstructionKind::Borrow { dst, .. }
                    | InstructionKind::ProjectBorrow { dst, .. }
                    | InstructionKind::Reborrow { dst, .. }
                        if uses.get(dst as usize).copied() == Some(1) =>
                    {
                        proof_definitions.insert(dst);
                    }
                    InstructionKind::EndBorrow { reference } => {
                        *end_counts.entry(reference).or_default() += 1;
                    }
                    _ => {}
                }
            }
        }
        proof_definitions.retain(|register| end_counts.get(register).copied() == Some(1));
        if proof_definitions.is_empty() {
            break;
        }

        for block in &mut scratch.blocks {
            block.statements.retain(|statement| {
                let erase = match statement.kind {
                    InstructionKind::Borrow { dst, .. }
                    | InstructionKind::ProjectBorrow { dst, .. }
                    | InstructionKind::Reborrow { dst, .. } => proof_definitions.contains(&dst),
                    InstructionKind::EndBorrow { reference } => {
                        proof_definitions.contains(&reference)
                    }
                    _ => false,
                };
                !erase
            });
        }
        changed = true;
    }

    scratch.features = infer_feature_bits(&scratch);
    *function = scratch;
    (
        if changed {
            PassOutcome::Changed
        } else {
            PassOutcome::Unchanged
        },
        work,
    )
}

/// Compute initialized-register state immediately before each reachable block
/// terminator for a deliberately small ownership-transparent CFG subset.
/// Returning `None` is a conservative barrier for both tail discovery and the
/// self-tail backedge rewrite.
fn simple_block_exit_states(function: &Function) -> Option<BTreeMap<u32, Vec<bool>>> {
    fn read(state: &[bool], register: Register) -> Option<()> {
        state.get(register as usize).copied()?.then_some(())
    }

    fn consume(state: &mut [bool], register: Register) -> Option<()> {
        read(state, register)?;
        state[register as usize] = false;
        Some(())
    }

    fn write(state: &mut [bool], register: Register) -> Option<()> {
        let initialized = state.get_mut(register as usize)?;
        if *initialized {
            return None;
        }
        *initialized = true;
        Some(())
    }

    fn transfer_edge(
        function: &Function,
        state: &mut [bool],
        edge: &Edge,
        implicit_params: usize,
    ) -> Option<()> {
        let target = function
            .blocks
            .iter()
            .find(|block| block.id == edge.target)?;
        if target.params.len() != edge.args.len() + implicit_params {
            return None;
        }
        // Bytecode lowering snapshots all sources before assigning any block
        // parameter. Model that parallel ownership transfer without exposing
        // lowering-only temporary registers.
        for argument in &edge.args {
            read(state, argument.register)?;
        }
        let mut moved = BTreeSet::new();
        for argument in &edge.args {
            if argument.mode == UseMode::Move {
                if !moved.insert(argument.register) {
                    return None;
                }
                consume(state, argument.register)?;
            }
        }
        for parameter in target.params.iter().skip(implicit_params) {
            write(state, parameter.register)?;
        }
        Some(())
    }

    let mut initial = vec![false; function.register_types.len()];
    if function.receiver_mode.is_some() {
        *initial.get_mut(0)? = true;
    }
    initial.get_mut(1..1 + function.params.len())?.fill(true);
    let mut entries = BTreeMap::from([(function.entry, initial)]);
    let mut exits = BTreeMap::new();
    let mut queue = VecDeque::from([function.entry]);
    while let Some(block_id) = queue.pop_front() {
        let block = function
            .blocks
            .iter()
            .find(|candidate| candidate.id == block_id)?;
        let mut state = entries.get(&block_id)?.clone();
        for statement in &block.statements {
            match &statement.kind {
                InstructionKind::Const { dst, .. } => write(&mut state, *dst)?,
                InstructionKind::Copy { dst, src } => {
                    read(&state, src.register)?;
                    write(&mut state, *dst)?;
                }
                InstructionKind::Move { dst, src } => {
                    consume(&mut state, src.register)?;
                    write(&mut state, *dst)?;
                }
                InstructionKind::Primitive { dst, args, .. } => {
                    for argument in args {
                        match argument.mode {
                            UseMode::Copy => read(&state, argument.register)?,
                            UseMode::Move => consume(&mut state, argument.register)?,
                        }
                    }
                    write(&mut state, *dst)?;
                }
                InstructionKind::Drop { owner } => consume(&mut state, owner.register)?,
                InstructionKind::Borrow { dst, src, .. }
                | InstructionKind::ProjectBorrow { dst, src, .. }
                | InstructionKind::Reborrow { dst, src, .. }
                | InstructionKind::DerefCopy { dst, src }
                | InstructionKind::DerefReborrow { dst, src, .. }
                | InstructionKind::DerefMove { dst, src }
                | InstructionKind::EnumTag { dst, src } => {
                    read(&state, *src)?;
                    write(&mut state, *dst)?;
                }
                InstructionKind::DerefStore { dst, src } => {
                    read(&state, *dst)?;
                    match src.mode {
                        UseMode::Copy => read(&state, src.register)?,
                        UseMode::Move => consume(&mut state, src.register)?,
                    }
                }
                InstructionKind::EndBorrow { reference }
                | InstructionKind::Deconstruct { src: reference } => {
                    consume(&mut state, *reference)?;
                }
                InstructionKind::Construct { dst, fields, .. }
                | InstructionKind::MakeCallable {
                    dst,
                    captures: fields,
                    ..
                }
                | InstructionKind::MakeHandlerShared {
                    dst,
                    captures: fields,
                    ..
                }
                | InstructionKind::MakeBindingPack {
                    dst,
                    payloads: fields,
                    ..
                }
                | InstructionKind::MakeHandler {
                    dst,
                    clauses: fields,
                    ..
                } => {
                    for field in fields {
                        match field.mode {
                            UseMode::Copy => read(&state, field.register)?,
                            UseMode::Move => consume(&mut state, field.register)?,
                        }
                    }
                    write(&mut state, *dst)?;
                }
                InstructionKind::ProjectCopy { dst, src, .. } => {
                    read(&state, src.register)?;
                    write(&mut state, *dst)?;
                }
                // Moving a field initializes the projection result but leaves
                // a residual aggregate shell in the source register.
                InstructionKind::ProjectMove { dst, src, .. } => {
                    read(&state, src.register)?;
                    write(&mut state, *dst)?;
                }
                // Label activation changes dynamic control state rather than
                // register initialization. It still needs label-arena cloning
                // before an enclosing CFG may be inlined.
                InstructionKind::LabelPush { result, .. } => read(&state, *result)?,
                InstructionKind::LabelPop { .. } => {}
            }
        }

        let mut propagate = |edge: &Edge, mut successor: Vec<bool>| -> Option<()> {
            transfer_edge(function, &mut successor, edge, 0)?;
            match entries.get(&edge.target) {
                Some(existing) if existing != &successor => None,
                Some(_) => Some(()),
                None => {
                    entries.insert(edge.target, successor);
                    queue.push_back(edge.target);
                    Some(())
                }
            }
        };
        exits.insert(block.id, state.clone());
        match &block.terminator {
            Terminator::Goto(edge) => propagate(edge, state)?,
            Terminator::Switch {
                discr,
                cases,
                otherwise,
            } => {
                read(&state, discr.register)?;
                for (_, edge) in cases {
                    propagate(edge, state.clone())?;
                }
                propagate(otherwise, state)?;
            }
            Terminator::Call {
                result,
                args,
                normal,
                ..
            } => {
                for argument in args {
                    consume(&mut state, argument.register)?;
                }
                if let Some(result) = result {
                    write(&mut state, *result)?;
                }
                transfer_edge(function, &mut state, normal, usize::from(result.is_some()))?;
                match entries.get(&normal.target) {
                    Some(existing) if existing != &state => return None,
                    Some(_) => {}
                    None => {
                        entries.insert(normal.target, state);
                        queue.push_back(normal.target);
                    }
                }
            }
            Terminator::CallSelf {
                result,
                args,
                normal,
            } => {
                read(&state, 0)?;
                for argument in args {
                    consume(&mut state, argument.register)?;
                }
                if let Some(result) = result {
                    write(&mut state, *result)?;
                }
                transfer_edge(function, &mut state, normal, usize::from(result.is_some()))?;
                match entries.get(&normal.target) {
                    Some(existing) if existing != &state => return None,
                    Some(_) => {}
                    None => {
                        entries.insert(normal.target, state);
                        queue.push_back(normal.target);
                    }
                }
            }
            Terminator::CallKnownReceiver {
                result,
                receiver,
                args,
                normal,
                ..
            } => {
                read(&state, receiver.register)?;
                for argument in args {
                    consume(&mut state, argument.register)?;
                }
                if let Some(result) = result {
                    write(&mut state, *result)?;
                }
                transfer_edge(function, &mut state, normal, usize::from(result.is_some()))?;
                match entries.get(&normal.target) {
                    Some(existing) if existing != &state => return None,
                    Some(_) => {}
                    None => {
                        entries.insert(normal.target, state);
                        queue.push_back(normal.target);
                    }
                }
            }
            Terminator::HostCall {
                result,
                args,
                normal,
                ..
            } => {
                for argument in args {
                    consume(&mut state, argument.register)?;
                }
                if let Some(result) = result {
                    write(&mut state, *result)?;
                }
                transfer_edge(function, &mut state, normal, usize::from(result.is_some()))?;
                match entries.get(&normal.target) {
                    Some(existing) if existing != &state => return None,
                    Some(_) => {}
                    None => {
                        entries.insert(normal.target, state);
                        queue.push_back(normal.target);
                    }
                }
            }
            Terminator::TailCall { .. } => {}
            Terminator::TailCallSelf { .. } => {
                consume(&mut state, 0)?;
            }
            Terminator::TailCallKnownReceiver { receiver, .. } => {
                read(&state, receiver.register)?;
            }
            Terminator::Leave { .. } => return None,
            Terminator::Return { .. } | Terminator::Abort { .. } | Terminator::Unreachable => {}
            // Preserve states at an indirect call itself so conservative tail
            // discovery can inspect it. Do not propagate through indirect
            // control until receiver-aware call effects are modeled here.
            Terminator::CallIndirect { .. } => {}
            Terminator::Resume {
                result,
                resumption,
                receiver_mode,
                value,
                normal,
            } => {
                if *receiver_mode == 2 {
                    consume(&mut state, resumption.register)?;
                } else {
                    read(&state, resumption.register)?;
                }
                match value.mode {
                    UseMode::Copy => read(&state, value.register)?,
                    UseMode::Move => consume(&mut state, value.register)?,
                }
                write(&mut state, *result)?;
                transfer_edge(function, &mut state, normal, 1)?;
                match entries.get(&normal.target) {
                    Some(existing) if existing != &state => return None,
                    Some(_) => {}
                    None => {
                        entries.insert(normal.target, state);
                        queue.push_back(normal.target);
                    }
                }
            }
            Terminator::TailResume { .. } => {}
            Terminator::Handle { .. }
            | Terminator::Perform { .. }
            | Terminator::Cancel { .. }
            | Terminator::TailCallIndirect { .. } => return None,
        }
    }
    Some(exits)
}

/// Discover the exact call/continuation shape whose ordinary call frame is
/// observationally equivalent to immediate frame replacement. The ownership
/// proof is intentionally strict: after protecting moved call operands, no
/// initialized receiver, local, capture, or other owner may remain in the
/// caller frame. This prevents custom destruction from moving from after the
/// callee to before it.
fn discover_tail_calls(
    function: &mut Function,
    types: &[Type],
    direct_custom_drop_types: &BTreeSet<TypeId>,
    budget: u64,
) -> (PassOutcome, u64) {
    let trace = std::env::var("G1_TAIL_CALL_TRACE")
        .is_ok_and(|fragment| !fragment.is_empty() && function.name.contains(&fragment));
    let work = body_size(function)
        .saturating_add(function.blocks.len() as u64 * function.register_types.len() as u64);
    if work > budget {
        return (PassOutcome::BudgetExhausted, work);
    }
    let exit_states = simple_block_exit_states(function).or_else(|| {
        // Complex valid joins may carry different cleanup-free temporaries and
        // exceed the deliberately exact compact analysis above. Fall back to
        // the normative ownership interpreter's per-terminator live-owner
        // lists rather than weakening initialization rules.
        let analysis =
            derive_cleanup_state_analysis_with_array_calls(function, types, &BTreeMap::new())
                .ok()?;
        Some(
            analysis
                .lists
                .into_iter()
                .filter_map(|(block, points)| {
                    let live = points.last()?;
                    let mut state = vec![false; function.register_types.len()];
                    for register in live {
                        *state.get_mut(*register as usize)? = true;
                    }
                    Some((block, state))
                })
                .collect::<BTreeMap<_, _>>(),
        )
    });
    let Some(exit_states) = exit_states else {
        return (PassOutcome::Unchanged, work);
    };

    let mut incoming = BTreeMap::<u32, u32>::new();
    for block in &function.blocks {
        for_each_edge(&block.terminator, |edge| {
            *incoming.entry(edge.target).or_default() += 1;
        });
    }

    let cleanup_free_drop = |register: Register| {
        function
            .flow
            .locals
            .get(register as usize)
            .is_some_and(|fact| {
                fact.drop_glue != DropGlueKind::Custom
                    && structurally_empty_drop_type(types, direct_custom_drop_types, fact.ty)
            })
    };
    let tail_discardable = |register: Register| {
        function
            .flow
            .locals
            .get(register as usize)
            .is_some_and(|fact| {
                fact.use_interval.admits_zero_use()
                    && types
                        .get(fact.ty as usize)
                        .is_some_and(Type::claimed_zero_use_allowed)
                    && cleanup_free_drop(register)
            })
    };

    let exact_return_continuation = |normal: &Edge,
                                     result: Option<Register>,
                                     role: BlockParamRole|
     -> Option<Vec<Instruction>> {
        let Some(mut result) = result else {
            return None;
        };
        if !normal.args.is_empty()
            || normal.target == function.entry
            || incoming.get(&normal.target) != Some(&1)
        {
            return None;
        }
        let mut target = normal.target;
        let mut expected_role = role;
        let mut visited = BTreeSet::new();
        let mut origins = BTreeMap::<Register, Register>::new();
        let mut passthrough = BTreeSet::new();
        let mut dropped = BTreeSet::new();
        let mut cleanup = Vec::new();
        loop {
            if !visited.insert(target) {
                return None;
            }
            let Some(continuation) = function.blocks.iter().find(|block| block.id == target) else {
                return None;
            };
            let Some(result_parameter) = continuation
                .params
                .iter()
                .find(|parameter| parameter.register == result)
            else {
                return None;
            };
            if result_parameter.ty != function.register_types[result as usize]
                || result_parameter.role != expected_role
            {
                return None;
            }
            for parameter in &continuation.params {
                if parameter.register != result {
                    passthrough.insert(
                        origins
                            .get(&parameter.register)
                            .copied()
                            .unwrap_or(parameter.register),
                    );
                }
            }
            for statement in &continuation.statements {
                match statement.kind {
                    InstructionKind::Drop { owner } => {
                        let origin = origins
                            .get(&owner.register)
                            .copied()
                            .unwrap_or(owner.register);
                        if owner.mode != UseMode::Move
                            || owner.register == result
                            || !cleanup_free_drop(owner.register)
                            || !dropped.insert(origin)
                        {
                            return None;
                        }
                        cleanup.push(Instruction {
                            span: statement.span,
                            kind: InstructionKind::Drop {
                                owner: Operand {
                                    register: origin,
                                    mode: UseMode::Move,
                                },
                            },
                        });
                    }
                    // A local label cannot escape in a verified program. Pop
                    // it before replacing the complete caller frame just as
                    // the ordinary return continuation would have done.
                    InstructionKind::LabelPop { .. } => cleanup.push(statement.clone()),
                    _ => return None,
                }
            }
            match &continuation.terminator {
                Terminator::Return {
                    value:
                        Some(Operand {
                            register,
                            mode: UseMode::Move,
                        }),
                } if *register == result => {
                    return passthrough
                        .iter()
                        .all(|register| dropped.contains(register) || tail_discardable(*register))
                        .then_some(cleanup);
                }
                Terminator::Goto(edge) if edge.target != function.entry => {
                    let Some(next_block) =
                        function.blocks.iter().find(|block| block.id == edge.target)
                    else {
                        return None;
                    };
                    if edge.args.len() != next_block.params.len() {
                        return None;
                    }
                    let mut result_positions =
                        edge.args
                            .iter()
                            .enumerate()
                            .filter_map(|(position, argument)| {
                                (argument.register == result && argument.mode == UseMode::Move)
                                    .then_some(position)
                            });
                    let Some(result_position) = result_positions.next() else {
                        return None;
                    };
                    if result_positions.next().is_some() {
                        return None;
                    }
                    let mut next_origins = BTreeMap::new();
                    let mut edge_origins = BTreeSet::new();
                    for (position, (argument, parameter)) in
                        edge.args.iter().zip(&next_block.params).enumerate()
                    {
                        let origin = origins
                            .get(&argument.register)
                            .copied()
                            .unwrap_or(argument.register);
                        if (position == result_position && argument.mode != UseMode::Move)
                            || function.register_types.get(argument.register as usize)
                                != Some(&parameter.ty)
                            || !edge_origins.insert(origin)
                        {
                            return None;
                        }
                        next_origins.insert(parameter.register, origin);
                        if position != result_position {
                            passthrough.insert(origin);
                        }
                    }
                    let next = &next_block.params[result_position];
                    // Shared cleanup blocks are safe to specialize along this
                    // incoming edge. The traversal below accepts only exact
                    // origin-preserving forwarding, cleanup, and an eventual
                    // return, and `visited` rejects cycles.
                    // MIR registers are single-assignment. Keep mappings for
                    // values that stay live through a block without being
                    // repeated as that block's parameters, while adding the
                    // newly introduced parameter identities.
                    origins.extend(next_origins);
                    result = next.register;
                    expected_role = next.role;
                    if !matches!(
                        expected_role,
                        BlockParamRole::Ordinary | BlockParamRole::ProtectedExitValue
                    ) {
                        return None;
                    }
                    target = edge.target;
                }
                _ => return None,
            }
        }
    };

    let consumes_complete_frame =
        |state: &[bool], operands: &[Operand], cleanup: &[Instruction]| -> bool {
            if !function.flow.loans.is_empty()
                && operands.iter().any(|operand| {
                    function
                        .register_types
                        .get(operand.register as usize)
                        .is_none_or(|ty| type_carries_reference(types, *ty))
                })
            {
                // A reference formed in this frame may point into a caller-owned
                // stack slot. PlaceFlow does not yet attach the exact surviving
                // loan to aggregate tail operands, so retain the caller frame
                // unless no local loans exist.
                return false;
            }
            let mut state = state.to_vec();
            let mut moved = BTreeSet::new();
            for operand in operands {
                if operand.mode != UseMode::Move
                    || !moved.insert(operand.register)
                    || !state
                        .get(operand.register as usize)
                        .copied()
                        .unwrap_or(false)
                {
                    return false;
                }
                state[operand.register as usize] = false;
            }
            for statement in cleanup {
                match statement.kind {
                    InstructionKind::Drop { owner } => {
                        if owner.mode != UseMode::Move
                            || !moved.insert(owner.register)
                            || !state.get(owner.register as usize).copied().unwrap_or(false)
                        {
                            return false;
                        }
                        state[owner.register as usize] = false;
                    }
                    InstructionKind::LabelPop { .. } => {}
                    _ => return false,
                }
            }
            state.iter().enumerate().all(|(register, initialized)| {
                !*initialized
                    || tail_discardable(register as Register)
                    || (register == 0
                        && function.receiver_mode == Some(2)
                        && function.receiver_type == UNIT)
            })
        };

    // A self call borrows the already-installed receiver rather than taking it
    // as an explicit operand.  Tail replacement keeps that receiver installed
    // for the replacement frame, so require every other live register to be
    // transferred exactly once while deliberately retaining register zero.
    let consumes_complete_self_frame = |state: &[bool],
                                        operands: &[Operand],
                                        cleanup: &[Instruction]|
     -> bool {
        if function.receiver_mode.is_none() || !state.first().copied().unwrap_or(false) {
            return false;
        }
        if !function.flow.loans.is_empty()
            && operands.iter().any(|operand| {
                function
                    .register_types
                    .get(operand.register as usize)
                    .is_none_or(|ty| type_carries_reference(types, *ty))
            })
        {
            return false;
        }
        let mut state = state.to_vec();
        state[0] = false;
        let mut moved = BTreeSet::new();
        for operand in operands {
            if operand.mode != UseMode::Move
                || operand.register == 0
                || !moved.insert(operand.register)
                || !state
                    .get(operand.register as usize)
                    .copied()
                    .unwrap_or(false)
            {
                return false;
            }
            state[operand.register as usize] = false;
        }
        for statement in cleanup {
            match statement.kind {
                InstructionKind::Drop { owner } => {
                    if owner.mode != UseMode::Move
                        || owner.register == 0
                        || !moved.insert(owner.register)
                        || !state.get(owner.register as usize).copied().unwrap_or(false)
                    {
                        return false;
                    }
                    state[owner.register as usize] = false;
                }
                InstructionKind::LabelPop { .. } => {}
                _ => return false,
            }
        }
        state
            .into_iter()
            .enumerate()
            .all(|(register, initialized)| !initialized || tail_discardable(register as Register))
    };

    let mut scratch = function.clone();
    let mut changed = false;
    for block in &mut scratch.blocks {
        let Some(state) = exit_states.get(&block.id) else {
            continue;
        };
        let replacement = match block.terminator.clone() {
            Terminator::Call {
                result,
                function: target,
                args,
                normal,
            } => {
                let continuation =
                    exact_return_continuation(&normal, result, BlockParamRole::CallResult);
                let exact = continuation.is_some();
                let complete = continuation
                    .as_ref()
                    .is_some_and(|cleanup| consumes_complete_frame(state, &args, cleanup));
                if trace {
                    eprintln!(
                        "g1-tail-call function={:?} block={} target={} exact_return={} complete_frame={}",
                        function.name, block.id, target, exact, complete,
                    );
                }
                continuation.and_then(|cleanup| {
                    complete.then_some((
                        Terminator::TailCall {
                            function: target,
                            args,
                        },
                        cleanup,
                    ))
                })
            }
            Terminator::CallSelf {
                result,
                args,
                normal,
            } => exact_return_continuation(&normal, result, BlockParamRole::CallResult).and_then(
                |cleanup| {
                    consumes_complete_self_frame(state, &args, &cleanup)
                        .then_some((Terminator::TailCallSelf { args }, cleanup))
                },
            ),
            Terminator::CallIndirect {
                result,
                callable,
                known_function,
                receiver_mode: 2,
                cleanup_callable: false,
                args,
                normal,
            } if callable.mode == UseMode::Move => {
                exact_return_continuation(&normal, result, BlockParamRole::CallResult).and_then(
                    |cleanup| {
                        let mut operands = Vec::with_capacity(args.len() + 1);
                        operands.push(callable);
                        operands.extend(args.iter().copied());
                        consumes_complete_frame(state, &operands, &cleanup).then_some((
                            Terminator::TailCallIndirect {
                                callable,
                                known_function,
                                receiver_mode: 2,
                                args,
                            },
                            cleanup,
                        ))
                    },
                )
            }
            Terminator::Resume {
                result,
                resumption,
                receiver_mode: 2,
                value,
                normal,
            } if resumption.mode == UseMode::Move => {
                exact_return_continuation(&normal, Some(result), BlockParamRole::ResumeResult)
                    .and_then(|cleanup| {
                        consumes_complete_frame(state, &[resumption, value], &cleanup).then_some((
                            Terminator::TailResume {
                                resumption,
                                receiver_mode: 2,
                                value,
                            },
                            cleanup,
                        ))
                    })
            }
            _ => None,
        };
        if let Some((replacement, cleanup)) = replacement {
            block.statements.extend(cleanup);
            block.terminator = replacement;
            changed = true;
        }
    }
    if changed {
        scratch.features = infer_feature_bits(&scratch);
        *function = scratch;
        (PassOutcome::Changed, work)
    } else {
        (PassOutcome::Unchanged, work)
    }
}

/// Replace safe direct self tail calls with an in-frame backedge. Arguments
/// are first moved into fresh typed temporaries, then moved into input
/// registers, which gives true parallel-assignment behavior for swaps/cycles.
fn form_self_tail_backedges(function: &mut Function, budget: u64) -> (PassOutcome, u64) {
    if function.receiver_mode.is_some()
        || function.features.contains(FeatureBits::LOANS)
        || !function.features.contains(FeatureBits::TAIL_CALLS)
        || function
            .blocks
            .iter()
            .find(|block| block.id == function.entry)
            .is_none_or(|entry| !entry.params.is_empty())
    {
        return (PassOutcome::Unchanged, 0);
    }
    let work = body_size(function)
        .saturating_add(function.blocks.len() as u64 * function.register_types.len() as u64);
    if work > budget {
        return (PassOutcome::BudgetExhausted, work);
    }
    let Some(exit_states) = simple_block_exit_states(function) else {
        return (PassOutcome::Unchanged, work);
    };
    let mut scratch = function.clone();
    let initial_len = scratch.register_types.len();
    let mut changed = false;
    for block in &mut scratch.blocks {
        let Terminator::TailCall {
            function: target,
            args,
        } = &block.terminator
        else {
            continue;
        };
        if *target != scratch.declaration
            || args.len() != scratch.params.len()
            || args.iter().any(|argument| argument.mode != UseMode::Move)
            || args
                .iter()
                .zip(&scratch.params)
                .any(|(argument, expected)| {
                    scratch.register_types.get(argument.register as usize) != Some(expected)
                })
        {
            continue;
        }
        let mut distinct = BTreeSet::new();
        if !args
            .iter()
            .all(|argument| distinct.insert(argument.register))
        {
            continue;
        }
        let Some(mut state) = exit_states.get(&block.id).cloned() else {
            continue;
        };
        let mut safe = true;
        for argument in args {
            if !state
                .get(argument.register as usize)
                .copied()
                .unwrap_or(false)
            {
                safe = false;
                break;
            }
            state[argument.register as usize] = false;
        }
        for parameter in state.iter_mut().take(scratch.params.len() + 1).skip(1) {
            if *parameter {
                safe = false;
                break;
            }
            *parameter = true;
        }
        if state
            != (0..initial_len)
                .map(|register| (1..=scratch.params.len()).contains(&register))
                .collect::<Vec<_>>()
        {
            safe = false;
        }
        if !safe {
            continue;
        }

        let span = block
            .statements
            .last()
            .map(|statement| statement.span)
            .unwrap_or_default();
        let arguments = args.clone();
        let mut temporaries = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let ty = scratch.register_types[argument.register as usize];
            let temporary = scratch.register_types.len() as Register;
            scratch.register_types.push(ty);
            block.statements.push(Instruction {
                span,
                kind: InstructionKind::Move {
                    dst: temporary,
                    src: argument,
                },
            });
            temporaries.push(temporary);
        }
        for (index, temporary) in temporaries.into_iter().enumerate() {
            block.statements.push(Instruction {
                span,
                kind: InstructionKind::Move {
                    dst: index as Register + 1,
                    src: Operand {
                        register: temporary,
                        mode: UseMode::Move,
                    },
                },
            });
        }
        block.terminator = Terminator::Goto(Edge {
            target: scratch.entry,
            args: vec![],
        });
        changed = true;
    }
    scratch.features = infer_feature_bits(&scratch);
    *function = scratch;
    (
        if changed {
            PassOutcome::Changed
        } else {
            PassOutcome::Unchanged
        },
        work,
    )
}

/// Hoist loop-invariant predefined-scalar calculations from natural loops.
///
/// This intentionally starts with the strongest cheap legality proof: a
/// unique empty-argument preheader, no special control/loan/drop operations in
/// the function, a nontrapping primitive with Copy-only no-drop operands, and
/// every operand defined outside the loop and dominating its preheader. Such a
/// computation has no ownership, cleanup, alias, effect, or trap observation,
/// including when hoisting makes it execute on a zero-trip body path.
fn hoist_loop_invariant_primitives(function: &mut Function, budget: u64) -> (PassOutcome, u64) {
    if function.features.contains(FeatureBits::LOANS)
        || function.features.contains(FeatureBits::DROPS)
        || function.features.contains(FeatureBits::HANDLERS)
        || function.features.contains(FeatureBits::RESUMPTIONS)
        || function.blocks.iter().any(|block| {
            block.statements.iter().any(|statement| {
                matches!(
                    statement.kind,
                    InstructionKind::LabelPush { .. } | InstructionKind::LabelPop { .. }
                )
            }) || matches!(block.terminator, Terminator::Leave { .. })
        })
    {
        return (PassOutcome::Unchanged, 0);
    }

    let mut work = body_size(function);
    if work > budget {
        return (PassOutcome::BudgetExhausted, work);
    }
    let cfg = match ControlFlowAnalysis::compute(function, budget.saturating_sub(work)) {
        Ok(cfg) => cfg,
        Err(error) => match error.kind {
            AnalysisErrorKind::BudgetExceeded { attempted, .. } => {
                return (PassOutcome::BudgetExhausted, work.saturating_add(attempted));
            }
            _ => panic!("validated MIR rejected by control-flow analysis: {error}"),
        },
    };
    debug_assert!(!ControlFlowAnalysis::invalidated_by(analysis::USES));
    work = work.saturating_add(cfg.work());
    if cfg.rpo().len() < 2 {
        return (PassOutcome::Unchanged, work);
    }

    let mut definitions = BTreeMap::<Register, Option<u32>>::new();
    let abi_end = function.params.len() as Register;
    for register in 0..=abi_end {
        definitions.insert(register, None);
    }
    let mut multiply_defined = BTreeSet::new();
    for block in &function.blocks {
        for parameter in &block.params {
            if definitions
                .insert(parameter.register, Some(block.id))
                .is_some()
            {
                multiply_defined.insert(parameter.register);
            }
        }
        for statement in &block.statements {
            if let Some(destination) = statement.kind.destination()
                && definitions.insert(destination, Some(block.id)).is_some()
            {
                multiply_defined.insert(destination);
            }
        }
        if let Some(result) = terminator_result(&block.terminator)
            && definitions.insert(result, Some(block.id)).is_some()
        {
            multiply_defined.insert(result);
        }
    }

    let mut scratch = function.clone();
    let mut changed = false;
    for natural_loop in cfg.loops() {
        if natural_loop.latches.is_empty()
            || natural_loop
                .blocks
                .iter()
                .any(|block| cfg.irreducible().contains(block))
        {
            continue;
        }
        let header = natural_loop.header.0;
        let loop_blocks = natural_loop
            .blocks
            .iter()
            .map(|block| block.0)
            .collect::<BTreeSet<_>>();
        let Some(header_block) = scratch.blocks.iter().find(|block| block.id == header) else {
            continue;
        };
        if !header_block.params.is_empty() {
            continue;
        }
        // NormalizeCfg can legally merge a trivial function-entry preheader
        // into the loop header. Recreate that structural edge only if LICM
        // actually finds work; ABI inputs are already live before the entry.
        let (existing_preheader, synthesize_entry_preheader) = match natural_loop.preheader {
            Some(preheader) => (Some(preheader.0), false),
            None if header == scratch.entry => (None, true),
            _ => continue,
        };
        debug_assert_eq!(
            natural_loop.preheader.is_some(),
            cfg.predecessors(natural_loop.header)
                .is_some_and(|incoming| incoming
                    .iter()
                    .any(|block| !natural_loop.blocks.contains(block)))
        );
        if let Some(preheader) = existing_preheader {
            let Some(preheader_index) = scratch
                .blocks
                .iter()
                .position(|block| block.id == preheader)
            else {
                continue;
            };
            if !matches!(
                scratch.blocks[preheader_index].terminator,
                Terminator::Goto(Edge { target, ref args }) if target == header && args.is_empty()
            ) {
                continue;
            }
        }

        let mut candidates = Vec::<(u32, usize)>::new();
        for block_id in &loop_blocks {
            let Some(block) = scratch.blocks.iter().find(|block| block.id == *block_id) else {
                continue;
            };
            for (statement_index, statement) in block.statements.iter().enumerate() {
                let InstructionKind::Primitive {
                    dst,
                    primitive,
                    args,
                } = &statement.kind
                else {
                    continue;
                };
                if multiply_defined.contains(dst)
                    || primitive_cse_key(&scratch, *dst, *primitive, args).is_none()
                    || args.iter().any(|argument| {
                        multiply_defined.contains(&argument.register)
                            || match definitions.get(&argument.register) {
                                Some(None) => false,
                                Some(Some(definition)) => {
                                    loop_blocks.contains(definition)
                                        || existing_preheader.is_none_or(|preheader| {
                                            !cfg.dominates(
                                                super::BlockId(*definition),
                                                super::BlockId(preheader),
                                            )
                                        })
                                }
                                None => true,
                            }
                    })
                {
                    continue;
                }
                candidates.push((*block_id, statement_index));
            }
        }
        candidates.sort_unstable();
        // Remove in reverse source order so indices stay stable, then restore
        // deterministic block/statement order in the preheader.
        let mut hoisted = Vec::with_capacity(candidates.len());
        for (block_id, statement_index) in candidates.into_iter().rev() {
            work = work.saturating_add(1);
            if work > budget {
                return (PassOutcome::BudgetExhausted, work);
            }
            let block_index = scratch
                .blocks
                .iter()
                .position(|block| block.id == block_id)
                .expect("selected loop block exists");
            hoisted.push((
                block_id,
                statement_index,
                scratch.blocks[block_index]
                    .statements
                    .remove(statement_index),
            ));
        }
        if hoisted.is_empty() {
            continue;
        }
        hoisted.sort_by_key(|(block, statement, _)| (*block, *statement));
        let preheader_index = if synthesize_entry_preheader {
            let Some(preheader) = scratch
                .blocks
                .iter()
                .map(|block| block.id)
                .max()
                .unwrap_or(0)
                .checked_add(1)
            else {
                return (PassOutcome::BudgetExhausted, work);
            };
            scratch.entry = preheader;
            scratch.blocks.push(BasicBlock {
                id: preheader,
                params: vec![],
                statements: vec![],
                terminator: Terminator::Goto(Edge {
                    target: header,
                    args: vec![],
                }),
            });
            scratch.blocks.len() - 1
        } else {
            scratch
                .blocks
                .iter()
                .position(|block| Some(block.id) == existing_preheader)
                .expect("validated preheader exists")
        };
        scratch.blocks[preheader_index]
            .statements
            .extend(hoisted.into_iter().map(|(_, _, instruction)| instruction));
        changed = true;
    }

    if changed {
        scratch.features = infer_feature_bits(&scratch);
        *function = scratch;
        (PassOutcome::Changed, work)
    } else {
        (PassOutcome::Unchanged, work)
    }
}

fn form_tail_calls_and_hoist(
    function: &mut Function,
    types: &[Type],
    direct_custom_drop_types: &BTreeSet<TypeId>,
    budget: u64,
) -> (PassOutcome, u64) {
    let mut scratch = function.clone();
    let (discovery, discovery_work) =
        discover_tail_calls(&mut scratch, types, direct_custom_drop_types, budget);
    if discovery == PassOutcome::BudgetExhausted {
        return (discovery, discovery_work);
    }
    let (backedges, backedge_work) = form_self_tail_backedges(
        &mut scratch,
        budget.saturating_sub(discovery_work.min(budget)),
    );
    let work = discovery_work.saturating_add(backedge_work);
    if backedges == PassOutcome::BudgetExhausted {
        return (backedges, work);
    }
    let (hoisting, hoist_work) =
        hoist_loop_invariant_primitives(&mut scratch, budget.saturating_sub(work.min(budget)));
    let work = work.saturating_add(hoist_work);
    if hoisting == PassOutcome::BudgetExhausted {
        return (hoisting, work);
    }
    let outcome = if discovery == PassOutcome::Changed
        || backedges == PassOutcome::Changed
        || hoisting == PassOutcome::Changed
    {
        PassOutcome::Changed
    } else {
        PassOutcome::Unchanged
    };
    *function = scratch;
    (outcome, work)
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ScalarConstantKey {
    Unit,
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    Usize(u64),
    Isize(i64),
    F32(u32),
    F64(u64),
    Char(char),
    Text(String),
    Bytes(Vec<u8>),
}

impl ScalarConstantKey {
    fn from_constant(value: &Constant) -> Self {
        match value {
            Constant::Unit => Self::Unit,
            Constant::U8(value) => Self::U8(*value),
            Constant::U16(value) => Self::U16(*value),
            Constant::U32(value) => Self::U32(*value),
            Constant::U64(value) => Self::U64(*value),
            Constant::U128(value) => Self::U128(*value),
            Constant::I8(value) => Self::I8(*value),
            Constant::I16(value) => Self::I16(*value),
            Constant::I32(value) => Self::I32(*value),
            Constant::I64(value) => Self::I64(*value),
            Constant::I128(value) => Self::I128(*value),
            Constant::Usize(value) => Self::Usize(*value),
            Constant::Isize(value) => Self::Isize(*value),
            Constant::F32(value) => Self::F32(value.to_bits()),
            Constant::F64(value) => Self::F64(value.to_bits()),
            Constant::Char(value) => Self::Char(*value),
            Constant::Text(value) => Self::Text(value.clone()),
            Constant::Bytes(value) => Self::Bytes(value.clone()),
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct GlobalFacts {
    callables: BTreeMap<Register, u32>,
    scalars: BTreeMap<Register, ScalarConstantKey>,
    /// Exact, nontrapping scalar computations available on every path to the
    /// current point. The stored result remains initialized and copyable.
    primitives: BTreeMap<PrimitiveCseKey, Register>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct PrimitiveCseKey {
    primitive: u32,
    result_type: TypeId,
    arguments: Vec<(Register, TypeId)>,
}

fn nontrapping_scalar_cse_primitive(primitive: Primitive) -> bool {
    use Primitive::*;

    matches!(
        primitive,
        IntWrappingAdd
            | IntWrappingSub
            | IntWrappingMul
            | IntBitAnd
            | IntBitOr
            | IntBitXor
            | IntBitNot
            | IntEq
            | IntNe
            | IntLt
            | IntLe
            | IntGt
            | IntGe
            | IntConvertWrapping
            | IntWrappingNeg
            | FloatAdd
            | FloatSub
            | FloatMul
            | FloatDiv
            | FloatRem
            | FloatEq
            | FloatNe
            | FloatLt
            | FloatLe
            | FloatGt
            | FloatGe
            | FloatConvert
            | FloatNeg
            | IntToFloat
            | CharToU32
    )
}

fn primitive_cse_key(
    function: &Function,
    destination: Register,
    primitive: Primitive,
    arguments: &[Operand],
) -> Option<PrimitiveCseKey> {
    let result_type = *function.register_types.get(destination as usize)?;
    if !predefined_no_drop_scalar(result_type) {
        return None;
    }
    let arguments = arguments
        .iter()
        .map(|argument| {
            let ty = *function.register_types.get(argument.register as usize)?;
            (argument.mode == UseMode::Copy && predefined_no_drop_scalar(ty))
                .then_some((argument.register, ty))
        })
        .collect::<Option<Vec<_>>>()?;
    nontrapping_scalar_cse_primitive(primitive).then_some(PrimitiveCseKey {
        primitive: primitive as u32,
        result_type,
        arguments,
    })
}

fn invalidate_primitive_cse_register(
    available: &mut BTreeMap<PrimitiveCseKey, Register>,
    register: Register,
) {
    available.retain(|key, result| {
        *result != register
            && key
                .arguments
                .iter()
                .all(|(argument, _)| *argument != register)
    });
}

impl GlobalFacts {
    fn retain_equal(&mut self, other: &Self) {
        self.callables
            .retain(|register, target| other.callables.get(register) == Some(target));
        self.scalars
            .retain(|register, value| other.scalars.get(register) == Some(value));
        self.primitives
            .retain(|key, result| other.primitives.get(key) == Some(result));
    }

    fn remove(&mut self, register: Register) {
        self.callables.remove(&register);
        self.scalars.remove(&register);
        invalidate_primitive_cse_register(&mut self.primitives, register);
    }

    fn move_register(&mut self, destination: Register, source: &Operand) {
        let callable = self.callables.get(&source.register).copied();
        let scalar = self.scalars.get(&source.register).cloned();
        if source.mode == UseMode::Move {
            self.remove(source.register);
        }
        self.remove(destination);
        if let Some(target) = callable {
            self.callables.insert(destination, target);
        }
        if let Some(value) = scalar {
            self.scalars.insert(destination, value);
        }
    }

    fn consume(&mut self, operand: &Operand) {
        if operand.mode == UseMode::Move {
            self.remove(operand.register);
        }
    }

    fn barrier(&mut self) {
        self.callables.clear();
        self.scalars.clear();
        self.primitives.clear();
    }
}

/// Deterministic global simplification over exact forward must-facts. Facts at
/// a join are intersection facts, which is equivalent to requiring each value
/// definition to dominate the use and remain unconsumed on every incoming
/// path. This first global slice propagates callable identities across blocks,
/// reuses exact predefined scalar constants, and resolves switches from a
/// dominating constant. Within one basic block it also reuses exact,
/// nontrapping predefined-scalar primitive results. That deliberately narrow
/// CSE slice requires copy-mode operands. Its availability is propagated over
/// ordinary CFG edges, intersected at joins, and killed whenever an operand or
/// result register is moved/redefined or a loan, memory, handler, effect, or
/// destruction barrier is crossed.
fn global_simplify_exact_callables(
    function: &mut Function,
    types: &[Type],
    budget: u64,
) -> (PassOutcome, u64) {
    let mut work = 0_u64;

    fn transfer_statement(
        function: &Function,
        facts: &mut GlobalFacts,
        statement: &InstructionKind,
    ) {
        match statement {
            InstructionKind::MakeCallable {
                dst,
                function: target,
                captures,
                ..
            } => {
                for capture in captures {
                    facts.consume(capture);
                }
                facts.remove(*dst);
                facts.callables.insert(*dst, *target);
            }
            InstructionKind::Const { dst, value } => {
                facts.remove(*dst);
                facts
                    .scalars
                    .insert(*dst, ScalarConstantKey::from_constant(value));
            }
            InstructionKind::Copy { dst, src } | InstructionKind::Move { dst, src } => {
                facts.move_register(*dst, src);
            }
            // Loan, handler, resumption, and destruction operations are hard
            // barriers in this slice. No fact is floated through them.
            InstructionKind::Borrow { .. }
            | InstructionKind::ProjectBorrow { .. }
            | InstructionKind::Reborrow { .. }
            | InstructionKind::DerefCopy { .. }
            | InstructionKind::DerefReborrow { .. }
            | InstructionKind::DerefMove { .. }
            | InstructionKind::DerefStore { .. }
            | InstructionKind::EndBorrow { .. }
            | InstructionKind::MakeHandler { .. }
            | InstructionKind::MakeHandlerShared { .. }
            | InstructionKind::LabelPush { .. }
            | InstructionKind::LabelPop { .. }
            | InstructionKind::Drop { .. } => facts.barrier(),
            InstructionKind::Construct { dst, fields, .. } => {
                for field in fields {
                    facts.consume(field);
                }
                facts.remove(*dst);
            }
            InstructionKind::MakeBindingPack { dst, payloads, .. } => {
                for payload in payloads {
                    facts.consume(payload);
                }
                facts.remove(*dst);
            }
            InstructionKind::ProjectCopy { dst, src, .. }
            | InstructionKind::ProjectMove { dst, src, .. } => {
                facts.consume(src);
                facts.remove(*dst);
            }
            InstructionKind::Deconstruct { src } => facts.remove(*src),
            InstructionKind::EnumTag { dst, .. } => facts.remove(*dst),
            InstructionKind::Primitive {
                dst,
                primitive,
                args,
            } => {
                let key = primitive_cse_key(function, *dst, *primitive, args);
                for argument in args {
                    facts.consume(argument);
                }
                facts.remove(*dst);
                if let Some(key) = key {
                    facts.primitives.insert(key, *dst);
                }
            }
        }
    }

    fn transfer_edge(
        function: &Function,
        facts: &GlobalFacts,
        edge: &Edge,
        implicit: usize,
    ) -> Option<GlobalFacts> {
        let target = function
            .blocks
            .iter()
            .find(|block| block.id == edge.target)?;
        if target.params.len() != edge.args.len() + implicit {
            return None;
        }
        let snapshots = target
            .params
            .iter()
            .skip(implicit)
            .zip(&edge.args)
            .map(|(parameter, argument)| {
                (
                    parameter.register,
                    facts.callables.get(&argument.register).copied(),
                    facts.scalars.get(&argument.register).cloned(),
                    *argument,
                )
            })
            .collect::<Vec<_>>();
        let mut result = facts.clone();
        for (_, _, _, argument) in &snapshots {
            result.consume(argument);
        }
        for (destination, callable, scalar, _) in snapshots {
            result.remove(destination);
            if let Some(callable) = callable {
                result.callables.insert(destination, callable);
            }
            if let Some(scalar) = scalar {
                result.scalars.insert(destination, scalar);
            }
        }
        Some(result)
    }

    fn block_successors(
        function: &Function,
        block: &BasicBlock,
        mut facts: GlobalFacts,
    ) -> Vec<(u32, GlobalFacts)> {
        match &block.terminator {
            Terminator::Goto(edge) => transfer_edge(function, &facts, edge, 0)
                .map(|facts| vec![(edge.target, facts)])
                .unwrap_or_default(),
            Terminator::Switch {
                cases, otherwise, ..
            } => cases
                .iter()
                .map(|(_, edge)| edge)
                .chain(std::iter::once(otherwise))
                .filter_map(|edge| {
                    transfer_edge(function, &facts, edge, 0).map(|facts| (edge.target, facts))
                })
                .collect(),
            Terminator::Call {
                result,
                args,
                normal,
                ..
            }
            | Terminator::CallSelf {
                result,
                args,
                normal,
            }
            | Terminator::CallKnownReceiver {
                result,
                args,
                normal,
                ..
            } => {
                for argument in args {
                    facts.consume(argument);
                }
                if let Some(result) = result {
                    facts.remove(*result);
                }
                transfer_edge(function, &facts, normal, usize::from(result.is_some()))
                    .map(|facts| vec![(normal.target, facts)])
                    .unwrap_or_default()
            }
            Terminator::HostCall {
                result,
                args,
                normal,
                ..
            } => {
                facts.barrier();
                for argument in args {
                    facts.consume(argument);
                }
                if let Some(result) = result {
                    facts.remove(*result);
                }
                transfer_edge(function, &facts, normal, usize::from(result.is_some()))
                    .map(|facts| vec![(normal.target, facts)])
                    .unwrap_or_default()
            }
            Terminator::CallIndirect {
                callable,
                args,
                normal,
                result,
                ..
            } => {
                facts.consume(callable);
                for argument in args {
                    facts.consume(argument);
                }
                if let Some(result) = result {
                    facts.remove(*result);
                }
                transfer_edge(function, &facts, normal, usize::from(result.is_some()))
                    .map(|facts| vec![(normal.target, facts)])
                    .unwrap_or_default()
            }
            Terminator::Handle { .. }
            | Terminator::Perform { .. }
            | Terminator::Resume { .. }
            | Terminator::TailResume { .. }
            | Terminator::Cancel { .. } => vec![],
            Terminator::Leave { target, .. } => {
                facts.barrier();
                transfer_edge(function, &facts, target, 0)
                    .map(|facts| vec![(target.target, facts)])
                    .unwrap_or_default()
            }
            Terminator::Return { .. }
            | Terminator::TailCall { .. }
            | Terminator::TailCallSelf { .. }
            | Terminator::TailCallKnownReceiver { .. }
            | Terminator::TailCallIndirect { .. }
            | Terminator::Abort { .. }
            | Terminator::Unreachable => vec![],
        }
    }

    // Solve exact incoming must-facts before rewriting. Starting a newly seen
    // block from its first predecessor and then intersecting can only remove
    // facts, so loops and joins converge deterministically.
    let block_indices = function
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| (block.id, index))
        .collect::<BTreeMap<_, _>>();
    let mut incoming = BTreeMap::from([(function.entry, GlobalFacts::default())]);
    let mut worklist = DenseWorklist::new(function.blocks.len());
    worklist.schedule(block_indices[&function.entry]);
    while let Some(block_index) = worklist.pop() {
        let block = &function.blocks[block_index];
        let block_id = block.id;
        work = work.saturating_add(block.statements.len() as u64 + 1);
        if work > budget {
            return (PassOutcome::BudgetExhausted, work);
        }
        let mut facts = incoming[&block_id].clone();
        for statement in &block.statements {
            transfer_statement(function, &mut facts, &statement.kind);
        }
        let successors = block_successors(function, block, facts);
        work = work.saturating_add(successors.len() as u64);
        if work > budget {
            return (PassOutcome::BudgetExhausted, work);
        }
        for (target, candidate) in successors {
            let changed = match incoming.get_mut(&target) {
                Some(existing) => {
                    let before = existing.clone();
                    existing.retain_equal(&candidate);
                    *existing != before
                }
                None => {
                    incoming.insert(target, candidate);
                    true
                }
            };
            if changed {
                worklist.schedule(block_indices[&target]);
            }
        }
    }

    let mut scratch = function.clone();
    let mut changed = false;
    let mut flow_changed = false;
    for block in &mut scratch.blocks {
        let Some(mut facts) = incoming.get(&block.id).cloned() else {
            continue;
        };
        work = work.saturating_add(block.statements.len() as u64 + 1);
        if work > budget {
            return (PassOutcome::BudgetExhausted, work);
        }
        for statement in &mut block.statements {
            if let InstructionKind::Primitive {
                dst,
                primitive,
                args,
            } = &statement.kind
                && let Some(key) = primitive_cse_key(function, *dst, *primitive, args)
                && let Some(source) = facts.primitives.get(&key).copied()
            {
                statement.kind = InstructionKind::Copy {
                    dst: *dst,
                    src: Operand {
                        register: source,
                        mode: UseMode::Copy,
                    },
                };
                changed = true;
                flow_changed = true;
            }
            match &statement.kind {
                InstructionKind::Const { dst, value }
                    if types
                        .get(function.register_types[*dst as usize] as usize)
                        .is_some_and(|ty| ty.is_predefined() && ty.claimed_duplicable()) =>
                {
                    let key = ScalarConstantKey::from_constant(value);
                    let source = facts.scalars.iter().find_map(|(register, candidate)| {
                        (*candidate == key
                            && function.register_types[*register as usize]
                                == function.register_types[*dst as usize])
                            .then_some(*register)
                    });
                    if let Some(source) = source {
                        statement.kind = InstructionKind::Copy {
                            dst: *dst,
                            src: Operand {
                                register: source,
                                mode: UseMode::Copy,
                            },
                        };
                        changed = true;
                        flow_changed = true;
                    }
                }
                _ => {}
            }
            transfer_statement(function, &mut facts, &statement.kind);
        }
        let known_callable = match &block.terminator {
            Terminator::CallIndirect { callable, .. }
            | Terminator::TailCallIndirect { callable, .. } => {
                facts.callables.get(&callable.register).copied()
            }
            _ => None,
        };
        match &mut block.terminator {
            Terminator::CallIndirect { known_function, .. }
            | Terminator::TailCallIndirect { known_function, .. } => {
                changed |= *known_function != known_callable;
                *known_function = known_callable;
            }
            Terminator::Switch {
                discr,
                cases,
                otherwise,
            } => {
                if let Some(value) = facts.scalars.get(&discr.register) {
                    let selected = cases
                        .iter()
                        .find(|(constant, _)| ScalarConstantKey::from_constant(constant) == *value)
                        .map(|(_, edge)| edge)
                        .unwrap_or(otherwise)
                        .clone();
                    block.terminator = Terminator::Goto(selected);
                    changed = true;
                    flow_changed = true;
                }
            }
            _ => {}
        }
    }
    if changed {
        scratch.features = infer_feature_bits(&scratch);
        scratch.invalid_analyses |= if flow_changed {
            analysis::ALL
        } else {
            // Updating an exact target annotation changes neither the CFG nor
            // operands/ownership. Keep imported PlaceFlow trusted while
            // invalidating only consumers of call semantics and cost.
            analysis::EFFECTS | analysis::VALUES | analysis::COST
        };
        *function = scratch;
        (PassOutcome::Changed, work)
    } else {
        (PassOutcome::Unchanged, work)
    }
}

#[derive(Clone)]
enum DirectCallSpecialization {
    Unit,
    Forward(u32),
    Constant(Constant),
    Primitive {
        primitive: Primitive,
        arguments: Vec<DirectPrimitiveArgument>,
        argument_types: Vec<TypeId>,
        result_type: TypeId,
    },
}

/// A scalar operand of a tiny direct callee.  Keeping callee literals in the
/// summary lets call specialization partially evaluate functions such as
/// `add_one(x)` without cloning their body into every caller.
#[derive(Clone)]
enum DirectPrimitiveArgument {
    Parameter(u32),
    Constant(Constant),
}

fn scalar_constant_type(ty: TypeId) -> bool {
    int_spec(ty).is_some() || matches!(ty, F32 | F64 | CHAR)
}

/// Resolve direct calls to tiny receiverless functions which either forward a
/// parameter, return unit, or return one literal constant. This is narrower
/// than inlining: it does not clone a body or consume its budget. A forwarding
/// argument (or a fresh caller-side constant) becomes the continuation's
/// implicit call-result edge argument, preserving ownership transfer exactly.
fn specialize_forwarding_direct_calls(program: &mut Program, budget: u64) -> (PassOutcome, u64) {
    let scan_work = operation_count(program);
    if scan_work > budget {
        return (PassOutcome::BudgetExhausted, scan_work);
    }
    let forwarding = program
        .functions
        .iter()
        .filter_map(|function| {
            let entry = function.blocks.iter().find(|block| block.id == function.entry)?;
            if function.receiver_mode.is_some()
                || function.blocks.len() != 1
                || !function.return_cleanup.is_empty()
                || !function.outward_protocols.is_empty()
                || function.no_return
            {
                return None;
            }
            let specialization = match (&entry.statements[..], &entry.terminator) {
                ([], Terminator::Return { value: None }) if function.result == UNIT => {
                    DirectCallSpecialization::Unit
                }
                (
                    [],
                    Terminator::Return {
                        value:
                            Some(Operand {
                                register,
                                mode: UseMode::Move,
                            }),
                    },
                ) => register
                    .checked_sub(1)
                    .filter(|index| {
                        function
                            .params
                            .get(*index as usize)
                            .is_some_and(|ty| *ty == function.result)
                    })
                    .map(DirectCallSpecialization::Forward)?,
                (
                    [Instruction {
                        kind: InstructionKind::Const { dst, value },
                        ..
                    }],
                    Terminator::Return {
                        value:
                            Some(Operand {
                                register,
                                mode: UseMode::Move,
                            }),
                    },
                ) if dst == register => DirectCallSpecialization::Constant(value.clone()),
                (
                    statements,
                    Terminator::Return {
                        value:
                            Some(Operand {
                                register,
                                mode: UseMode::Move,
                            }),
                    },
                ) => {
                    let (primitive_statement, prefix) = statements.split_last()?;
                    let InstructionKind::Primitive {
                        dst,
                        primitive,
                        args,
                    } = &primitive_statement.kind else {
                        return None;
                    };
                    if *dst != *register || !prefix.iter().all(|statement| matches!(
                        statement.kind,
                        InstructionKind::Const { .. }
                    )) {
                        return None;
                    }
                    let constants = prefix.iter().filter_map(|statement| match &statement.kind {
                        InstructionKind::Const { dst, value } => Some((*dst, value)),
                        _ => None,
                    }).collect::<BTreeMap<_, _>>();
                    let arguments = args
                        .iter()
                        .map(|argument| {
                            if argument.mode != UseMode::Copy {
                                return None;
                            }
                            if let Some(index) = argument.register.checked_sub(1)
                                && function.params.get(index as usize).is_some()
                            {
                                Some(DirectPrimitiveArgument::Parameter(index))
                            } else {
                                constants.get(&argument.register).cloned().cloned().map(
                                    DirectPrimitiveArgument::Constant,
                                )
                            }
                        })
                        .collect::<Option<Vec<_>>>()?;
                    let argument_types = arguments
                        .iter()
                        .zip(args)
                        .map(|(argument, operand)| match argument {
                            DirectPrimitiveArgument::Parameter(index) => {
                                function.params.get(*index as usize).copied()
                            }
                            DirectPrimitiveArgument::Constant(_) => function
                                .register_types
                                .get(operand.register as usize)
                                .copied(),
                        })
                        .collect::<Option<Vec<_>>>()?;
                    if !argument_types.iter().copied().all(scalar_constant_type)
                        || function.register_types.get(*dst as usize) != Some(&function.result)
                    {
                        return None;
                    }
                    DirectCallSpecialization::Primitive {
                        primitive: *primitive,
                        arguments,
                        argument_types,
                        result_type: function.result,
                    }
                }
                _ => return None,
            };
            Some((function.declaration, specialization))
        })
        .collect::<BTreeMap<_, _>>();
    if forwarding.is_empty() {
        return (PassOutcome::Unchanged, scan_work);
    }

    let mut changed = false;
    for caller in &mut program.functions {
        let mut caller_changed = false;
        for block_index in 0..caller.blocks.len() {
            if let Terminator::TailCall { function, args } =
                caller.blocks[block_index].terminator.clone()
            {
                if matches!(
                    forwarding.get(&function),
                    Some(DirectCallSpecialization::Forward(0))
                ) && args.len() == 1
                {
                    caller.blocks[block_index].terminator = Terminator::Return {
                        value: Some(args[0]),
                    };
                    caller_changed = true;
                }
                continue;
            }
            let Terminator::Call {
                result,
                function,
                args,
                normal,
            } = caller.blocks[block_index].terminator.clone()
            else {
                continue;
            };
            let Some(specialization) = forwarding.get(&function) else {
                continue;
            };
            let replacement = match (specialization, result) {
                (DirectCallSpecialization::Unit, None) => normal,
                (DirectCallSpecialization::Forward(index), Some(_)) => {
                    let Some(value) = args.get(*index as usize).copied() else {
                        continue;
                    };
                    let mut edge_args = Vec::with_capacity(normal.args.len() + 1);
                    edge_args.push(value);
                    edge_args.extend(normal.args);
                    Edge {
                        target: normal.target,
                        args: edge_args,
                    }
                }
                (DirectCallSpecialization::Constant(value), Some(result)) => {
                    let Some(result_type) = caller.register_types.get(result as usize).copied() else {
                        continue;
                    };
                    let constant_register = caller.register_types.len() as Register;
                    caller.register_types.push(result_type);
                    let span = caller.blocks[block_index]
                        .statements
                        .last()
                        .map(|statement| statement.span)
                        .unwrap_or_default();
                    caller.blocks[block_index].statements.push(Instruction {
                        span,
                        kind: InstructionKind::Const {
                            dst: constant_register,
                            value: value.clone(),
                        },
                    });
                    let mut edge_args = Vec::with_capacity(normal.args.len() + 1);
                    edge_args.push(Operand {
                        register: constant_register,
                        mode: UseMode::Move,
                    });
                    edge_args.extend(normal.args);
                    Edge {
                        target: normal.target,
                        args: edge_args,
                    }
                }
                (
                    DirectCallSpecialization::Primitive {
                        primitive,
                        arguments,
                        argument_types,
                        result_type,
                    },
                    Some(result),
                ) => {
                    let values = caller.blocks[block_index]
                        .statements
                        .iter()
                        .filter_map(|statement| match &statement.kind {
                            InstructionKind::Const { dst, value } => Some((*dst, value.clone())),
                            _ => None,
                        })
                        .collect::<BTreeMap<_, _>>();
                    let constants = arguments
                        .iter()
                        .map(|argument| match argument {
                            DirectPrimitiveArgument::Parameter(index) => args
                                .get(*index as usize)
                                .and_then(|argument| values.get(&argument.register))
                                .cloned(),
                            DirectPrimitiveArgument::Constant(value) => Some(value.clone()),
                        })
                        .collect::<Option<Vec<_>>>();
                    let Some(constants) = constants else {
                        continue;
                    };
                    let Some(value) = fold_primitive(*result_type, *primitive, argument_types, &constants) else {
                        continue;
                    };
                    let Some(result_type) = caller.register_types.get(result as usize).copied() else {
                        continue;
                    };
                    let constant_register = caller.register_types.len() as Register;
                    caller.register_types.push(result_type);
                    let span = caller.blocks[block_index]
                        .statements
                        .last()
                        .map(|statement| statement.span)
                        .unwrap_or_default();
                    caller.blocks[block_index].statements.push(Instruction {
                        span,
                        kind: InstructionKind::Const {
                            dst: constant_register,
                            value,
                        },
                    });
                    let mut edge_args = Vec::with_capacity(normal.args.len() + 1);
                    edge_args.push(Operand {
                        register: constant_register,
                        mode: UseMode::Move,
                    });
                    edge_args.extend(normal.args);
                    Edge {
                        target: normal.target,
                        args: edge_args,
                    }
                }
                _ => continue,
            };
            caller.blocks[block_index].terminator = Terminator::Goto(replacement);
            caller_changed = true;
        }
        if caller_changed {
            caller.invalid_analyses |= pass_contract(PassId::SpecializeDirectCalls).invalidates;
            caller.features = infer_feature_bits(caller);
            changed = true;
        }
    }
    (
        if changed {
            PassOutcome::Changed
        } else {
            PassOutcome::Unchanged
        },
        scan_work,
    )
}

const MAX_SCALARIZED_CALLABLE_OPERATIONS: u64 = 4096;

#[derive(Clone)]
struct CallableScalarization {
    caller: usize,
    block: usize,
    statement_start: usize,
    target: usize,
    captures: Vec<Operand>,
    args: Vec<Operand>,
    result: Option<Register>,
    normal: Option<Edge>,
    tail: bool,
}

fn remap_register(register: Register, registers: &[Option<Register>]) -> Option<Register> {
    registers.get(register as usize).copied().flatten()
}

fn remap_operand(operand: &mut Operand, registers: &[Option<Register>]) -> Option<()> {
    operand.register = remap_register(operand.register, registers)?;
    Some(())
}

fn remap_edge(edge: &mut Edge, registers: &[Option<Register>]) -> Option<()> {
    for argument in &mut edge.args {
        remap_operand(argument, registers)?;
    }
    Some(())
}

fn remap_instruction(kind: &mut InstructionKind, registers: &[Option<Register>]) -> Option<()> {
    if let Some(destination) = kind.destination_mut() {
        *destination = remap_register(*destination, registers)?;
    }
    match kind {
        InstructionKind::Copy { src, .. } | InstructionKind::Move { src, .. } => {
            remap_operand(src, registers)?
        }
        InstructionKind::Borrow { src, .. }
        | InstructionKind::ProjectBorrow { src, .. }
        | InstructionKind::Reborrow { src, .. }
        | InstructionKind::DerefCopy { src, .. }
        | InstructionKind::DerefReborrow { src, .. }
        | InstructionKind::DerefMove { src, .. }
        | InstructionKind::EndBorrow { reference: src }
        | InstructionKind::Deconstruct { src }
        | InstructionKind::EnumTag { src, .. } => {
            *src = remap_register(*src, registers)?;
        }
        InstructionKind::DerefStore { dst, src } => {
            *dst = remap_register(*dst, registers)?;
            remap_operand(src, registers)?;
        }
        InstructionKind::Construct { fields, .. } => {
            for field in fields {
                remap_operand(field, registers)?;
            }
        }
        InstructionKind::ProjectCopy { src, .. }
        | InstructionKind::ProjectMove { src, .. }
        | InstructionKind::Drop { owner: src } => remap_operand(src, registers)?,
        InstructionKind::Primitive { args, .. } => {
            for argument in args {
                remap_operand(argument, registers)?;
            }
        }
        InstructionKind::MakeCallable { captures, .. }
        | InstructionKind::MakeHandlerShared { captures, .. } => {
            for capture in captures {
                remap_operand(capture, registers)?;
            }
        }
        InstructionKind::MakeHandler { clauses, .. } => {
            for clause in clauses {
                remap_operand(clause, registers)?;
            }
        }
        InstructionKind::MakeBindingPack { payloads, .. } => {
            for payload in payloads {
                remap_operand(payload, registers)?;
            }
        }
        InstructionKind::LabelPush { result, .. } => {
            *result = remap_register(*result, registers)?;
        }
        InstructionKind::Const { .. } | InstructionKind::LabelPop { .. } => {}
    }
    Some(())
}

fn remap_terminator(terminator: &mut Terminator, registers: &[Option<Register>]) -> Option<()> {
    match terminator {
        Terminator::Goto(edge) => remap_edge(edge, registers)?,
        Terminator::Switch {
            discr,
            cases,
            otherwise,
        } => {
            remap_operand(discr, registers)?;
            for (_, edge) in cases {
                remap_edge(edge, registers)?;
            }
            remap_edge(otherwise, registers)?;
        }
        Terminator::Return { value } => {
            if let Some(value) = value {
                remap_operand(value, registers)?;
            }
        }
        Terminator::Call {
            result,
            args,
            normal,
            ..
        }
        | Terminator::CallSelf {
            result,
            args,
            normal,
        } => {
            if let Some(result) = result {
                *result = remap_register(*result, registers)?;
            }
            for argument in args {
                remap_operand(argument, registers)?;
            }
            remap_edge(normal, registers)?;
        }
        Terminator::CallKnownReceiver {
            result,
            receiver,
            args,
            normal,
            ..
        } => {
            if let Some(result) = result {
                *result = remap_register(*result, registers)?;
            }
            remap_operand(receiver, registers)?;
            for argument in args {
                remap_operand(argument, registers)?;
            }
            remap_edge(normal, registers)?;
        }
        Terminator::HostCall {
            result,
            args,
            normal,
            ..
        } => {
            if let Some(result) = result {
                *result = remap_register(*result, registers)?;
            }
            for argument in args {
                remap_operand(argument, registers)?;
            }
            remap_edge(normal, registers)?;
        }
        Terminator::CallIndirect {
            result,
            callable,
            args,
            normal,
            ..
        } => {
            if let Some(result) = result {
                *result = remap_register(*result, registers)?;
            }
            remap_operand(callable, registers)?;
            for argument in args {
                remap_operand(argument, registers)?;
            }
            remap_edge(normal, registers)?;
        }
        Terminator::Handle {
            result,
            handler,
            body,
            normal,
        } => {
            *result = remap_register(*result, registers)?;
            remap_operand(handler, registers)?;
            remap_operand(body, registers)?;
            remap_edge(normal, registers)?;
        }
        Terminator::Perform {
            result,
            payloads,
            capture,
            resume,
            ..
        } => {
            if let Some(result) = result {
                *result = remap_register(*result, registers)?;
            }
            for payload in payloads {
                remap_operand(payload, registers)?;
            }
            for register in &mut capture.captured_owners {
                *register = remap_register(*register, registers)?;
            }
            for register in &mut capture.captured_references {
                *register = remap_register(*register, registers)?;
            }
            for residual in &mut capture.captured_residuals {
                residual.register = remap_register(residual.register, registers)?;
            }
            capture.captured_owners.sort_unstable();
            capture.captured_references.sort_unstable();
            capture
                .captured_residuals
                .sort_by_key(|residual| residual.register);
            if let Some(resume) = resume {
                remap_edge(resume, registers)?;
            }
        }
        Terminator::Resume {
            result,
            resumption,
            value,
            normal,
            ..
        } => {
            *result = remap_register(*result, registers)?;
            remap_operand(resumption, registers)?;
            remap_operand(value, registers)?;
            remap_edge(normal, registers)?;
        }
        Terminator::TailResume {
            resumption, value, ..
        } => {
            remap_operand(resumption, registers)?;
            remap_operand(value, registers)?;
        }
        Terminator::Cancel {
            result,
            resumption,
            normal,
        } => {
            *result = remap_register(*result, registers)?;
            remap_operand(resumption, registers)?;
            remap_edge(normal, registers)?;
        }
        Terminator::TailCall { args, .. } | Terminator::TailCallSelf { args } => {
            for argument in args {
                remap_operand(argument, registers)?;
            }
        }
        Terminator::TailCallIndirect { callable, args, .. } => {
            remap_operand(callable, registers)?;
            for argument in args {
                remap_operand(argument, registers)?;
            }
        }
        Terminator::TailCallKnownReceiver { receiver, args, .. } => {
            remap_operand(receiver, registers)?;
            for argument in args {
                remap_operand(argument, registers)?;
            }
        }
        Terminator::Leave { target, .. } => remap_edge(target, registers)?,
        Terminator::Abort { .. } | Terminator::Unreachable => {}
    }
    Some(())
}

fn terminator_result(terminator: &Terminator) -> Option<Register> {
    match terminator {
        Terminator::Call { result, .. }
        | Terminator::CallSelf { result, .. }
        | Terminator::CallKnownReceiver { result, .. }
        | Terminator::CallIndirect { result, .. }
        | Terminator::HostCall { result, .. }
        | Terminator::Perform { result, .. } => *result,
        Terminator::Handle { result, .. }
        | Terminator::Resume { result, .. }
        | Terminator::Cancel { result, .. } => Some(*result),
        Terminator::Goto(_)
        | Terminator::Switch { .. }
        | Terminator::Return { .. }
        | Terminator::TailResume { .. }
        | Terminator::TailCall { .. }
        | Terminator::TailCallSelf { .. }
        | Terminator::TailCallKnownReceiver { .. }
        | Terminator::TailCallIndirect { .. }
        | Terminator::Leave { .. }
        | Terminator::Abort { .. }
        | Terminator::Unreachable => None,
    }
}

/// Whether the final activity of a block-local virtual register empties it.
/// Earlier reads are harmless; the strict interval inequality ensures the
/// replacement definition is a later instruction. Partial projections and
/// continuation captures do not empty their base and therefore fail closed.
fn register_emptied_at_last_local_activity(
    function: &Function,
    register: Register,
    block_id: super::BlockId,
) -> bool {
    let Some(block) = function.blocks.iter().find(|block| block.id == block_id.0) else {
        return false;
    };
    let mut last = None;
    for statement in &block.statements {
        let mut used = false;
        let mut consuming = true;
        statement.kind.for_each_register_use(|candidate, kind| {
            if candidate == register {
                used = true;
                consuming &= kind == RegisterUseKind::Consume;
            }
        });
        if used {
            last = Some(consuming);
        }
    }

    let mut used = false;
    let mut consuming = true;
    block.terminator.for_each_register_use(|candidate, kind| {
        if candidate == register {
            used = true;
            consuming &= kind == RegisterUseKind::Consume;
        }
    });
    if used {
        last = Some(consuming);
    }
    last == Some(true)
}

/// Compact the register namespace used by bytecode emission.
///
/// The receiver and source parameter ABI prefix (`r0`, then `r1..`) is frozen.
/// Every other referenced or defined register is assigned densely in old-ID
/// order.  The monotone map is important: besides making output reproducible,
/// it preserves the canonical ordering of continuation capture sets.  This is
/// mandatory correctness lowering at every optimization level, and is kept out
/// of the MIR optimization report because bytecode edge lowering owns the rest
/// of `LowerRegistersAndEdges`.
pub(crate) fn compact_live_registers_for_emission(
    program: &mut Program,
    types: &[Type],
) -> Result<bool, ValidationError> {
    if program
        .functions
        .iter()
        .all(|function| function.phase == MirPhase::Lowered)
    {
        validate_program(program, types, MirPhase::Lowered)?;
        return Ok(false);
    }
    validate_program(program, types, MirPhase::Optimized)?;
    let mut changed = false;
    for function in &mut program.functions {
        changed |= layout_checked_blocks_for_emission(function)?;
        let old_len = function.register_types.len();
        if old_len == 0 {
            function.phase = MirPhase::Lowered;
            continue;
        }

        let abi_len = function.params.len().saturating_add(1);
        if abi_len > old_len {
            return Err(error(
                function,
                None,
                "register compaction found a truncated receiver/parameter ABI prefix",
            ));
        }
        let intervals =
            RegisterIntervals::compute(function, types, u64::MAX).map_err(|failure| {
                error(
                    function,
                    None,
                    format!("register interval construction failed: {failure}"),
                )
            })?;
        debug_assert!(!RegisterIntervals::invalidated_by(analysis::COST));
        let _analysis_work = intervals.work();
        let mut emptied = BTreeSet::new();
        for interval in intervals.intervals() {
            debug_assert!(interval.start <= interval.end);
            debug_assert_eq!(
                function.register_types[interval.register as usize],
                interval.ty
            );
            debug_assert!(!interval.addressable || interval.class != RegisterClass::Erased);
            // In a multi-block body, an unrestricted SSA value can remain an
            // ambient physical owner at a successor even when every explicit
            // definition/use belongs to one block. Until interval construction
            // incorporates ownership cleanup-state liveness, only straight-line
            // bodies may reuse an emptied slot.
            if function.blocks.len() == 1
                && !interval.addressable
                && interval.local_block.is_some_and(|block| {
                    register_emptied_at_last_local_activity(function, interval.register, block)
                })
            {
                emptied.insert(interval.register);
            }
        }
        let allocation = PhysicalRegisterAllocation::exact(
            &intervals,
            &function.register_types,
            abi_len,
            &emptied,
        );
        let registers = allocation.map();
        let register_types = allocation.register_types().to_vec();
        let identity = register_types.len() == old_len
            && registers
                .iter()
                .enumerate()
                .all(|(old, physical)| *physical == Some(old as Register));
        if identity {
            continue;
        }

        let mut scratch = function.clone();
        for block in &mut scratch.blocks {
            for parameter in &mut block.params {
                parameter.register =
                    remap_register(parameter.register, registers).ok_or_else(|| {
                        error(
                            function,
                            Some(block.id),
                            "register compaction lost a block parameter",
                        )
                    })?;
            }
            for statement in &mut block.statements {
                remap_instruction(&mut statement.kind, registers).ok_or_else(|| {
                    error(
                        function,
                        Some(block.id),
                        "register compaction lost an instruction register",
                    )
                })?;
            }
            remap_terminator(&mut block.terminator, registers).ok_or_else(|| {
                error(
                    function,
                    Some(block.id),
                    "register compaction lost a terminator register",
                )
            })?;
        }
        for register in &mut scratch.return_cleanup {
            *register = remap_register(*register, registers).ok_or_else(|| {
                error(
                    function,
                    None,
                    "register compaction lost a return-cleanup owner",
                )
            })?;
        }
        // Remap the exported per-register facts to the compacted numbering and
        // remap register-bearing derived facts. Physical reuse is legal only
        // across disjoint intervals, so exact cleanup actions retain their
        // meaning under the allocation map.
        let bridged = bridged_locals(function, types);
        let mut physical_sources = vec![Vec::new(); register_types.len()];
        for (old, physical) in registers.iter().copied().enumerate() {
            if let Some(physical) = physical {
                physical_sources[physical as usize].push(old);
            }
        }
        scratch.flow.locals = physical_sources
            .iter()
            .enumerate()
            .map(|(physical, sources)| {
                if sources.len() == 1 && !allocation.reused().contains(&(physical as Register)) {
                    bridged[sources[0]].clone()
                } else {
                    let ty = register_types[physical];
                    LocalFact::conservative(ty, &types[ty as usize])
                }
            })
            .collect();
        // Proof-only borrow/end pairs may already have been erased. Their
        // exported loan facts are historical provenance rather than live
        // lowered identities, so compact the loan arena alongside registers
        // and repair every LoanId consumer. A loan with either endpoint still
        // present must retain both endpoints; losing only one side would hide
        // a live reference-origin bug.
        let old_loans = std::mem::take(&mut scratch.flow.loans);
        let mut loan_ids = vec![None; old_loans.len()];
        for (old_id, loan) in old_loans.iter().enumerate() {
            let reference = remap_register(loan.reference, registers);
            let borrowed = remap_register(loan.borrowed.base, registers);
            match (reference, borrowed) {
                (None, None) => {}
                (Some(_), None) => {
                    return Err(error(
                        function,
                        Some(loan.issued_block),
                        "register compaction lost a live exported borrowed place",
                    ));
                }
                (None, Some(_)) => {
                    // The owner can outlive a proof-only reference. The erased
                    // loan has no runtime or cleanup identity after this point.
                }
                (Some(reference), Some(_)) => {
                    let new_id = LoanId(scratch.flow.loans.len() as u32);
                    loan_ids[old_id] = Some(new_id);
                    let mut remapped = loan.clone();
                    remapped.reference = reference;
                    scratch.flow.loans.push(remapped);
                }
            }
        }
        for loan in &mut scratch.flow.loans {
            loan.borrowed.base =
                remap_register(loan.borrowed.base, registers).ok_or_else(|| {
                    error(
                        function,
                        Some(loan.issued_block),
                        "register compaction lost a live exported borrowed place",
                    )
                })?;
            loan.parent = match loan.parent {
                Some(parent) => Some(loan_ids.get(parent.index()).copied().flatten().ok_or_else(
                    || {
                        error(
                            function,
                            Some(loan.issued_block),
                            "register compaction lost a live parent-loan identity",
                        )
                    },
                )?),
                None => None,
            };
            loan.region = RegionId(
                loan_ids[loan.region.index()]
                    .expect("retained loan has a compacted one-to-one region identity")
                    .0,
            );
        }
        for scope in &mut scratch.flow.scopes {
            scope.owners.retain_mut(|owner| {
                if let Some(mapped) = remap_register(*owner, registers) {
                    *owner = mapped;
                    true
                } else {
                    false
                }
            });
        }
        for site in &mut scratch.flow.indirect_calls {
            for register in site
                .capture
                .captured_owners
                .iter_mut()
                .chain(&mut site.capture.captured_references)
            {
                *register = remap_register(*register, registers).ok_or_else(|| {
                    error(
                        function,
                        Some(site.block),
                        "register compaction lost an indirect-call capture",
                    )
                })?;
            }
            for residual in &mut site.capture.captured_residuals {
                residual.register =
                    remap_register(residual.register, registers).ok_or_else(|| {
                        error(
                            function,
                            Some(site.block),
                            "register compaction lost an indirect-call residual capture",
                        )
                    })?;
            }
            site.capture.captured_owners.sort_unstable();
            site.capture.captured_references.sort_unstable();
            site.capture
                .captured_residuals
                .sort_by_key(|residual| residual.register);
        }
        for plan in &mut scratch.flow.cleanup_plans {
            let mut actions = Vec::with_capacity(plan.actions.len());
            for mut action in std::mem::take(&mut plan.actions) {
                match &mut action {
                    CleanupAction::Destroy(register) => {
                        *register = remap_register(*register, registers).ok_or_else(|| {
                            error(function, None, "register compaction lost a cleanup owner")
                        })?;
                    }
                    CleanupAction::DestroyIf { local, flag } => {
                        *local = remap_register(*local, registers).ok_or_else(|| {
                            error(
                                function,
                                None,
                                "register compaction lost a conditional cleanup owner",
                            )
                        })?;
                        *flag = remap_register(*flag, registers).ok_or_else(|| {
                            error(function, None, "register compaction lost a cleanup flag")
                        })?;
                    }
                    CleanupAction::DestroyResidual { local, .. } => {
                        *local = remap_register(*local, registers).ok_or_else(|| {
                            error(
                                function,
                                None,
                                "register compaction lost a residual cleanup owner",
                            )
                        })?;
                    }
                    CleanupAction::EndBorrow(loan) => {
                        let Some(mapped) = loan_ids.get(loan.index()).copied().flatten() else {
                            continue;
                        };
                        *loan = mapped;
                    }
                }
                actions.push(action);
            }
            plan.actions = actions;
            for register in &mut plan.protected {
                *register = remap_register(*register, registers).ok_or_else(|| {
                    error(
                        function,
                        None,
                        "register compaction lost a cleanup-protected value",
                    )
                })?;
            }
        }
        scratch.flow.drop_flags.retain_mut(|fact| {
            match (
                remap_register(fact.flag, registers),
                remap_register(fact.owner, registers),
            ) {
                (Some(flag), Some(owner)) => {
                    fact.flag = flag;
                    fact.owner = owner;
                    true
                }
                _ => false,
            }
        });
        scratch
            .flow
            .drop_flags
            .sort_by_key(|fact| (fact.flag, fact.owner, fact.field));
        scratch
            .flow
            .drop_flags
            .dedup_by_key(|fact| (fact.flag, fact.owner, fact.field));
        rebuild_site_facts(&mut scratch);
        scratch.flow.move_paths = derive_move_paths(&scratch);
        scratch.invalid_analyses = 0;
        scratch.register_types = register_types;
        scratch.phase = MirPhase::Lowered;
        *function = scratch;
        changed = true;
    }
    for function in &mut program.functions {
        function.phase = MirPhase::Lowered;
        function.features = infer_feature_bits(function);
    }
    validate_program(program, types, MirPhase::Lowered)?;
    Ok(changed)
}

/// Order compact MIR by typed control region while retaining stable BlockIds.
/// Reachable order is the checked CFG's deterministic RPO; unreachable ties use
/// the original identity. The earlier bytecode layout pass is consequently
/// idempotent for ordinary bodies while cleanup/label/handler/resumption seeds
/// retain explicit, contiguous cold regions.
fn layout_checked_blocks_for_emission(function: &mut Function) -> Result<bool, ValidationError> {
    if function.blocks.len() < 2 {
        return Ok(false);
    }
    let editor = CheckedCfg::new(function, ResourceLimits::default()).map_err(|failure| {
        error(
            function,
            failure.block.map(|block| block.0),
            format!("checked block layout rejected its input: {failure}"),
        )
    })?;
    let cfg = ControlFlowAnalysis::compute(function, u64::MAX).map_err(|failure| {
        error(
            function,
            None,
            format!("checked block layout analysis failed: {failure}"),
        )
    })?;
    let rpo = cfg
        .rpo()
        .iter()
        .enumerate()
        .map(|(position, block)| (*block, position))
        .collect::<BTreeMap<_, _>>();
    let mut order = function
        .blocks
        .iter()
        .map(|block| {
            let id = super::BlockId(block.id);
            let kind = editor
                .block_kind(id)
                .expect("checked editor retains every live block");
            let region = match kind {
                BlockKind::Entry => 0,
                BlockKind::Normal => 1,
                BlockKind::Label => 2,
                BlockKind::Cleanup => 3,
                BlockKind::Handler => 4,
                BlockKind::Resumption => 5,
            };
            (region, rpo.get(&id).copied().unwrap_or(usize::MAX), id)
        })
        .collect::<Vec<_>>();
    order.sort_unstable();
    let ids = order
        .into_iter()
        .map(|(_, _, block)| block.0)
        .collect::<Vec<_>>();
    if ids
        == function
            .blocks
            .iter()
            .map(|block| block.id)
            .collect::<Vec<_>>()
    {
        return Ok(false);
    }
    let mut blocks = std::mem::take(&mut function.blocks)
        .into_iter()
        .map(|block| (block.id, block))
        .collect::<BTreeMap<_, _>>();
    function.blocks = ids
        .into_iter()
        .map(|id| {
            blocks
                .remove(&id)
                .expect("layout retains every checked block")
        })
        .collect();
    Ok(true)
}

/// Clone an owned callable target without its receiver shell. This only
/// accepts the canonical lowering prologue, so moving captures into leading
/// ABI parameters preserves their identity and cleanup order exactly.
fn receiverless_callable_clone(
    target: &Function,
    capture_types: &[TypeId],
    declaration: u32,
) -> Option<Function> {
    if target.receiver_mode != Some(2)
        || target.features.contains(FeatureBits::LOANS)
        || target.features.contains(FeatureBits::RESUMPTIONS)
        || target.blocks.iter().any(|block| {
            block.statements.iter().any(|statement| {
                matches!(
                    statement.kind,
                    InstructionKind::MakeHandler { .. } | InstructionKind::MakeHandlerShared { .. }
                )
            }) || matches!(
                block.terminator,
                Terminator::Handle { .. }
                    | Terminator::Resume { .. }
                    | Terminator::TailResume { .. }
                    | Terminator::Cancel { .. }
                    | Terminator::Perform {
                        resume: Some(_),
                        ..
                    }
            )
        })
    {
        return None;
    }
    let entry_index = target
        .blocks
        .iter()
        .position(|block| block.id == target.entry)?;
    let entry = &target.blocks[entry_index];
    if entry.statements.len() < capture_types.len() + 1 {
        return None;
    }
    let mut capture_destinations = Vec::with_capacity(capture_types.len());
    for (field, statement) in entry
        .statements
        .iter()
        .take(capture_types.len())
        .enumerate()
    {
        let InstructionKind::ProjectMove {
            dst,
            src:
                Operand {
                    register: 0,
                    mode: UseMode::Move,
                },
            field: actual_field,
        } = statement.kind
        else {
            return None;
        };
        if actual_field != field as u32
            || target.register_types.get(dst as usize) != capture_types.get(field)
        {
            return None;
        }
        capture_destinations.push(dst);
    }
    if !matches!(
        entry.statements[capture_types.len()].kind,
        InstructionKind::Deconstruct { src: 0 }
    ) || register_uses(target).first().copied() != Some(capture_types.len() as u32 + 1)
    {
        return None;
    }
    // A clone referring directly to its receiver-taking source would have an
    // incompatible ABI. Recursive callable dispatch remains indirect and is
    // outside this deliberately narrow first slice.
    if target.blocks.iter().any(|block| {
        matches!(
            block.terminator,
            Terminator::Call { function, .. } | Terminator::TailCall { function, .. }
                if function == target.declaration
        )
    }) {
        return None;
    }

    let mut registers = vec![None; target.register_types.len()];
    let mut register_types = vec![UNIT];
    let mut params = capture_types.to_vec();
    params.extend_from_slice(&target.params);
    register_types.extend_from_slice(&params);
    for (index, destination) in capture_destinations.into_iter().enumerate() {
        if registers[destination as usize]
            .replace(index as Register + 1)
            .is_some()
        {
            return None;
        }
    }
    for (index, _) in target.params.iter().enumerate() {
        let old = index + 1;
        let new = capture_types.len() + index + 1;
        if registers[old].replace(new as Register).is_some() {
            return None;
        }
    }
    for (mapped, ty) in registers.iter_mut().zip(&target.register_types).skip(1) {
        if mapped.is_none() {
            let new = register_types.len() as Register;
            *mapped = Some(new);
            register_types.push(*ty);
        }
    }

    let mut clone = target.clone();
    clone.declaration = declaration;
    clone.name = format!("$scalarized${}${declaration}", target.declaration);
    clone.params = params;
    clone.receiver_mode = None;
    clone.receiver_type = UNIT;
    clone.register_types = register_types;
    clone.blocks[entry_index]
        .statements
        .drain(..capture_types.len() + 1);
    for block in &mut clone.blocks {
        for parameter in &mut block.params {
            parameter.register = remap_register(parameter.register, &registers)?;
        }
        for statement in &mut block.statements {
            remap_instruction(&mut statement.kind, &registers)?;
        }
        remap_terminator(&mut block.terminator, &registers)?;
    }
    for register in &mut clone.return_cleanup {
        *register = remap_register(*register, &registers)?;
    }
    clone.features = infer_feature_bits(&clone);
    Some(clone)
}

/// Scalarize the smallest ownership-safe closure-call shape into a direct call
/// of a receiverless clone. Discovery and clone construction finish before any
/// mutation, making budget exhaustion and rejected candidates transactional.
fn scalarize_callables(program: &mut Program, types: &[Type], budget: u64) -> (PassOutcome, u64) {
    let scan_work = operation_count(program);
    if scan_work > budget {
        return (PassOutcome::BudgetExhausted, scan_work);
    }
    // Bytecode currently uses declaration IDs as function-table indices after
    // sorting. Do not synthesize a direct target unless the input namespace is
    // the canonical dense range and the appended declaration will therefore
    // be its exact artifact index.
    let declarations = program
        .functions
        .iter()
        .map(|function| function.declaration)
        .collect::<BTreeSet<_>>();
    if declarations.len() != program.functions.len()
        || declarations
            .iter()
            .copied()
            .ne(0..program.functions.len() as u32)
    {
        return (PassOutcome::Unchanged, scan_work);
    }
    let mut candidates = Vec::new();
    for (caller_index, caller) in program.functions.iter().enumerate() {
        if caller.features.contains(FeatureBits::LOANS)
            || caller.features.contains(FeatureBits::HANDLERS)
            || caller.features.contains(FeatureBits::RESUMPTIONS)
        {
            continue;
        }
        let uses = register_uses(caller);
        for (block_index, block) in caller.blocks.iter().enumerate() {
            let Some(statement_start) = block.statements.iter().rposition(|statement| {
                matches!(statement.kind, InstructionKind::MakeCallable { .. })
            }) else {
                continue;
            };
            let InstructionKind::MakeCallable {
                dst,
                callable_type,
                function: made_target,
                captures,
            } = &block.statements[statement_start].kind
            else {
                unreachable!()
            };
            let mut final_callable = *dst;
            let mut alias_chain_safe = uses.get(*dst as usize).copied() == Some(1);
            for statement in &block.statements[statement_start + 1..] {
                let InstructionKind::Move {
                    dst: alias,
                    src:
                        Operand {
                            register: source,
                            mode: UseMode::Move,
                        },
                } = statement.kind
                else {
                    alias_chain_safe = false;
                    break;
                };
                if source != final_callable
                    || uses.get(alias as usize).copied() != Some(1)
                    || caller.register_types.get(source as usize)
                        != caller.register_types.get(alias as usize)
                {
                    alias_chain_safe = false;
                    break;
                }
                final_callable = alias;
            }
            let (result, callable, known_target, args, normal, tail) = match &block.terminator {
                Terminator::CallIndirect {
                    result,
                    callable,
                    known_function: Some(known_target),
                    receiver_mode: 2,
                    cleanup_callable: false,
                    args,
                    normal,
                } => (*result, callable, *known_target, args, Some(normal.clone()), false),
                Terminator::TailCallIndirect {
                    callable,
                    known_function: Some(known_target),
                    receiver_mode: 2,
                    args,
                } => (None, callable, *known_target, args, None, true),
                _ => continue,
            };
            if !alias_chain_safe
                || callable.register != final_callable
                || callable.mode != UseMode::Move
                || captures.iter().any(|capture| capture.mode != UseMode::Move)
                || *made_target != known_target
            {
                continue;
            }
            let Some(target_index) = program
                .functions
                .iter()
                .position(|function| function.declaration == known_target)
            else {
                continue;
            };
            let target = &program.functions[target_index];
            let Some(Type::Callable {
                capture_type,
                receiver_mode: 2,
                ..
            }) = types.get(*callable_type as usize).map(Type::representation)
            else {
                continue;
            };
            // Tuple is the only receiver shell known here to have no custom
            // destruction authority of its own. Field cleanup remains in the
            // cloned body and is not approximated by this pass.
            let Some(Type::Tuple {
                fields: capture_types,
                ..
            }) = types.get(*capture_type as usize).map(Type::representation)
            else {
                continue;
            };
            if capture_types.len() != captures.len()
                || captures.iter().zip(capture_types).any(|(capture, ty)| {
                    caller.register_types.get(capture.register as usize) != Some(ty)
                })
                || target.receiver_type != *capture_type
            {
                continue;
            }
            candidates.push(CallableScalarization {
                caller: caller_index,
                block: block_index,
                statement_start,
                target: target_index,
                captures: captures.clone(),
                args: args.clone(),
                result,
                normal,
                tail,
            });
        }
    }
    if candidates.is_empty() {
        return (PassOutcome::Unchanged, scan_work);
    }

    let mut next_declaration = program.functions.len() as u32;
    let mut clones = Vec::new();
    let mut accepted = Vec::new();
    let mut clone_work = 0_u64;
    for candidate in candidates {
        let target = &program.functions[candidate.target];
        let capture_types = candidate
            .captures
            .iter()
            .map(|capture| {
                program.functions[candidate.caller].register_types[capture.register as usize]
            })
            .collect::<Vec<_>>();
        let Some(clone) = receiverless_callable_clone(target, &capture_types, next_declaration)
        else {
            continue;
        };
        clone_work = clone_work.saturating_add(body_size(&clone));
        if clone_work > MAX_SCALARIZED_CALLABLE_OPERATIONS
            || scan_work.saturating_add(clone_work) > budget
        {
            return (
                PassOutcome::BudgetExhausted,
                scan_work.saturating_add(clone_work),
            );
        }
        accepted.push((candidate, next_declaration));
        clones.push(clone);
        let Some(next) = next_declaration.checked_add(1) else {
            return (
                PassOutcome::BudgetExhausted,
                scan_work.saturating_add(clone_work),
            );
        };
        next_declaration = next;
    }
    if accepted.is_empty() {
        return (PassOutcome::Unchanged, scan_work.saturating_add(clone_work));
    }
    for (candidate, declaration) in accepted {
        let caller = &mut program.functions[candidate.caller];
        caller.invalid_analyses |= pass_contract(PassId::ScalarizeCallables).invalidates;
        let block = &mut caller.blocks[candidate.block];
        block.statements.truncate(candidate.statement_start);
        let mut direct_args = candidate.captures;
        direct_args.extend(candidate.args);
        block.terminator = if candidate.tail {
            Terminator::TailCall {
                function: declaration,
                args: direct_args,
            }
        } else {
            Terminator::Call {
                result: candidate.result,
                function: declaration,
                args: direct_args,
                normal: candidate.normal.expect("non-tail call has a normal edge"),
            }
        };
    }
    for clone in &mut clones {
        clone.invalid_analyses |= pass_contract(PassId::ScalarizeCallables).invalidates;
    }
    program.functions.extend(clones);
    for function in &mut program.functions {
        function.features = infer_feature_bits(function);
    }
    (PassOutcome::Changed, scan_work.saturating_add(clone_work))
}

/// Resolve one statically known cleanup-empty terminal performance to the first
/// matching clause of an immediately constructed handler. Multiple operation
/// groups and partial handlers are legal: the selected synthetic pattern-matrix
/// callable retains source first-match/fallback behavior outside the delimiter.
/// Richer control and resumptive specialization waits until compact MIR carries
/// ordered cleanup plans and lexical handler/resumption site IDs.
#[derive(Clone)]
struct TerminalHandlerFusion {
    caller: usize,
    block: usize,
    statement_start: usize,
    clause_statement: Instruction,
    clause_register: Register,
    clause_function: u32,
    result: Register,
    normal: Edge,
    capture_setup_statements: Vec<Instruction>,
    body_register_types: Vec<TypeId>,
    body_capture_bindings: Vec<(Register, Register)>,
    body_statements: Vec<Instruction>,
    body_cleanup_owners: Vec<Register>,
    payloads: Vec<Operand>,
}

/// A statically delimited, single-performance nonterminal handler.  Unlike
/// terminal fusion, this rewrite composes the clause's `Resume`/`Cancel` edge
/// with the suspended body directly.  The deliberately small shape proof is
/// important: it eliminates a real runtime resumption without manufacturing a
/// fake resumption value, and rejects every case whose cancellation cleanup or
/// deep reinstatement would not be represented by the transplanted CFG.
#[derive(Clone)]
struct DirectResumptiveHandlerFusion {
    caller: usize,
    block: usize,
    statement_start: usize,
    result: Register,
    normal: Edge,
    body: Function,
    clause: Function,
    clause_resumption: Register,
}

fn append_transplanted_statements(
    source: &Function,
    statements: &[Instruction],
    registers: &mut [Option<Register>],
    omitted: &mut BTreeSet<Register>,
    destination_types: &mut Vec<TypeId>,
    destination: &mut Vec<Instruction>,
) -> Option<()> {
    for statement in statements {
        match &statement.kind {
            InstructionKind::Move { dst, src } if omitted.contains(&src.register) => {
                if registers.get(*dst as usize)?.is_some() || !omitted.insert(*dst) {
                    return None;
                }
                continue;
            }
            InstructionKind::Drop { owner } if omitted.contains(&owner.register) => continue,
            InstructionKind::EndBorrow { reference } if omitted.contains(reference) => continue,
            InstructionKind::Deconstruct { src } if omitted.contains(src) => continue,
            _ => {}
        }

        let old_destination = statement.kind.destination();
        if let Some(old_destination) = old_destination {
            if registers.get(old_destination as usize)?.is_some()
                || omitted.contains(&old_destination)
            {
                return None;
            }
            let new_destination = destination_types.len() as Register;
            destination_types.push(*source.register_types.get(old_destination as usize)?);
            registers[old_destination as usize] = Some(new_destination);
        }
        let mut transplanted = statement.clone();
        remap_instruction(&mut transplanted.kind, registers)?;
        destination.push(transplanted);
    }
    Some(())
}

fn bind_transplanted_edge(
    source: &Function,
    edge: &Edge,
    registers: &mut [Option<Register>],
) -> Option<u32> {
    let target = source.blocks.iter().find(|block| block.id == edge.target)?;
    let mut arguments = edge.args.iter();
    for parameter in &target.params {
        if matches!(
            parameter.role,
            BlockParamRole::CallResult | BlockParamRole::ResumeResult
        ) && registers.get(parameter.register as usize)?.is_some()
        {
            continue;
        }
        let argument = arguments.next()?;
        if argument.mode != UseMode::Move {
            return None;
        }
        let mapped = remap_register(argument.register, registers)?;
        let slot = registers.get_mut(parameter.register as usize)?;
        if slot.is_some_and(|existing| existing != mapped) {
            return None;
        }
        *slot = Some(mapped);
    }
    if arguments.next().is_some() {
        return None;
    }
    Some(edge.target)
}

/// Transplant a straight-line CFG suffix made only from `Goto` edges and one
/// `Return`.  This includes the protected-exit blocks emitted for handler
/// clauses while refusing switches, calls, effects, labels, or cycles.
fn append_transplanted_linear_suffix(
    source: &Function,
    first_edge: &Edge,
    registers: &mut [Option<Register>],
    omitted: &mut BTreeSet<Register>,
    destination_types: &mut Vec<TypeId>,
    destination: &mut Vec<Instruction>,
) -> Option<Option<Operand>> {
    let mut block_id = bind_transplanted_edge(source, first_edge, registers)?;
    let mut visited = BTreeSet::new();
    loop {
        if !visited.insert(block_id) {
            return None;
        }
        let block = source.blocks.iter().find(|block| block.id == block_id)?;
        append_transplanted_statements(
            source,
            &block.statements,
            registers,
            omitted,
            destination_types,
            destination,
        )?;
        match &block.terminator {
            Terminator::Goto(edge) => {
                block_id = bind_transplanted_edge(source, edge, registers)?;
            }
            Terminator::Return { value } => {
                let mut value = *value;
                if let Some(value) = &mut value {
                    remap_operand(value, registers)?;
                }
                return Some(value);
            }
            _ => return None,
        }
    }
}

/// Expose a terminal `Perform` hidden behind one exact, no-return direct call.
/// This is the forwarding shape emitted for `handle forward(payload)`: the
/// body computes arguments, transfers them to a leaf, and its normal edge is
/// unreachable.  Cleanup is remapped from the leaf rather than discarded.
fn resolve_forwarded_terminal_body(
    program: &Program,
    body: &Function,
    types: &[Type],
) -> Option<Function> {
    if body.blocks.len() == 1
        && body.blocks[0].id == body.entry
        && matches!(
            body.blocks[0].terminator,
            Terminator::Perform {
                result: None,
                resume: None,
                ..
            }
        )
    {
        return Some(body.clone());
    }
    if body.blocks.len() != 2 || !body.params.is_empty() {
        return None;
    }
    let entry = body.blocks.iter().find(|block| block.id == body.entry)?;
    let Terminator::Call {
        result: None,
        function,
        args,
        normal,
    } = &entry.terminator
    else {
        return None;
    };
    let unreachable = body.blocks.iter().find(|block| block.id == normal.target)?;
    if !normal.args.is_empty()
        || !unreachable.params.is_empty()
        || !unreachable.statements.is_empty()
        || !matches!(unreachable.terminator, Terminator::Unreachable)
    {
        return None;
    }
    let forwarded = direct_target(program, *function)?;
    if forwarded.receiver_mode.is_some()
        || forwarded.params.len() != args.len()
        || !forwarded.no_return
        || !forwarded.return_cleanup.is_empty()
        || forwarded.blocks.len() != 1
        || forwarded.blocks[0].id != forwarded.entry
        || !forwarded.blocks[0].params.is_empty()
    {
        return None;
    }
    let forwarded_block = &forwarded.blocks[0];
    if !matches!(
        forwarded_block.terminator,
        Terminator::Perform {
            result: None,
            resume: None,
            ..
        }
    ) {
        return None;
    }

    let mut flattened = body.clone();
    flattened.blocks = vec![entry.clone()];
    let flattened_entry = &mut flattened.blocks[0];
    let mut registers = vec![None; forwarded.register_types.len()];
    for (index, argument) in args.iter().enumerate() {
        if argument.mode != UseMode::Move
            || forwarded.params.get(index) != body.register_types.get(argument.register as usize)
        {
            return None;
        }
        registers[index + 1] = Some(argument.register);
    }
    for statement in &forwarded_block.statements {
        let old_destination = statement.kind.destination()?;
        let new_destination = flattened.register_types.len() as Register;
        flattened
            .register_types
            .push(*forwarded.register_types.get(old_destination as usize)?);
        registers[old_destination as usize] = Some(new_destination);
        let mut statement = statement.clone();
        remap_instruction(&mut statement.kind, &registers)?;
        flattened_entry.statements.push(statement);
    }
    let mut terminator = forwarded_block.terminator.clone();
    remap_terminator(&mut terminator, &registers)?;
    flattened_entry.terminator = terminator;

    let (_, cleanup) = forwarded.flow.plan_for(&CleanupEdge::TerminalPerform {
        block: forwarded_block.id,
    })?;
    let mut actions = Vec::with_capacity(cleanup.actions.len());
    for action in &cleanup.actions {
        let CleanupAction::Destroy(owner) = action else {
            return None;
        };
        if forwarded
            .flow
            .locals
            .get(*owner as usize)
            .is_some_and(|fact| fact.drop_glue == DropGlueKind::Custom)
        {
            return None;
        }
        actions.push(CleanupAction::Destroy(remap_register(*owner, &registers)?));
    }
    let protected = cleanup
        .protected
        .iter()
        .map(|register| remap_register(*register, &registers))
        .collect::<Option<Vec<_>>>()?;
    flattened.flow.cleanup_plans = vec![CleanupPlanFact {
        edge: CleanupEdge::TerminalPerform {
            block: flattened_entry.id,
        },
        source_scope: cleanup.source_scope,
        target_scope: cleanup.target_scope,
        actions,
        protected,
    }];
    flattened.no_return = true;
    flattened.features = infer_feature_bits(&flattened);
    // The later checked pass rebuilds all derived flow facts.  We nevertheless
    // retain conservative local descriptors for newly transplanted registers
    // because terminal fusion consults their custom-drop classification.
    while flattened.flow.locals.len() < flattened.register_types.len() {
        let register = flattened.flow.locals.len();
        let ty = flattened.register_types[register];
        flattened
            .flow
            .locals
            .push(LocalFact::conservative(ty, &types[ty as usize]));
    }
    Some(flattened)
}

fn specialize_terminal_handlers(
    program: &mut Program,
    types: &[Type],
    protocols: &[Protocol],
    handler_defs: &[HandlerDef],
    budget: u64,
) -> (PassOutcome, u64) {
    let mut work = 0_u64;
    let mut candidates = Vec::new();

    for (caller_index, caller) in program.functions.iter().enumerate() {
        let mut use_counts = BTreeMap::<Register, u32>::new();
        for block in &caller.blocks {
            for register in used_registers(block) {
                *use_counts.entry(register).or_default() += 1;
            }
        }
        for (block_index, block) in caller.blocks.iter().enumerate() {
            work = work.saturating_add(block.statements.len() as u64 + 1);
            let Terminator::Handle {
                result,
                handler,
                body,
                normal,
            } = &block.terminator
            else {
                continue;
            };
            if block.statements.len() < 3
                || handler.mode != UseMode::Move
                || body.mode != UseMode::Move
            {
                continue;
            }
            let body_statement = &block.statements[block.statements.len() - 1];
            let InstructionKind::MakeCallable {
                dst: body_register,
                callable_type: body_type,
                function: body_declaration,
                captures: body_captures,
            } = &body_statement.kind
            else {
                continue;
            };
            let Some(handler_statement_index) = block.statements[..block.statements.len() - 1]
                .iter()
                .rposition(|statement| {
                    matches!(
                        statement.kind,
                        InstructionKind::MakeHandler { dst, .. } if dst == handler.register
                    )
                })
            else {
                continue;
            };
            let handler_statement = &block.statements[handler_statement_index];
            let InstructionKind::MakeHandler {
                dst: handler_register,
                handler_def,
                clauses,
            } = &handler_statement.kind
            else {
                unreachable!("the matching statement was selected by variant");
            };
            let Some(definition) = handler_defs.get(*handler_def as usize) else {
                continue;
            };
            if definition.clauses.is_empty()
                || clauses.len() != definition.clauses.len()
                || handler_statement_index < definition.clauses.len()
            {
                continue;
            }
            let statement_start = handler_statement_index - definition.clauses.len();
            let clause_statements = &block.statements[statement_start..handler_statement_index];
            let capture_setup_statements =
                &block.statements[handler_statement_index + 1..block.statements.len() - 1];
            let mut clause_values = Vec::with_capacity(definition.clauses.len());
            let mut clauses_safe = true;
            for (index, statement) in clause_statements.iter().enumerate() {
                let InstructionKind::MakeCallable {
                    dst,
                    callable_type,
                    function,
                    captures,
                } = &statement.kind
                else {
                    clauses_safe = false;
                    break;
                };
                let Some(Type::Callable { capture_type, .. }) =
                    types.get(*callable_type as usize).map(Type::representation)
                else {
                    clauses_safe = false;
                    break;
                };
                if clauses.get(index)
                    != Some(&Operand {
                        register: *dst,
                        mode: UseMode::Move,
                    })
                    || use_counts.get(dst).copied() != Some(1)
                {
                    clauses_safe = false;
                    break;
                }
                clause_values.push((
                    statement.clone(),
                    *dst,
                    *callable_type,
                    *function,
                    captures.is_empty(),
                    *capture_type,
                    types[*callable_type as usize].claimed_zero_use_allowed(),
                ));
            }
            if !clauses_safe
                || clause_values.len() != definition.clauses.len()
                || *handler_register != handler.register
                || *body_register != body.register
                || use_counts.get(handler_register).copied() != Some(1)
                || use_counts.get(body_register).copied() != Some(1)
            {
                continue;
            }
            if capture_setup_statements.iter().any(|statement| {
                let Some(dst) = statement.kind.destination() else {
                    return true;
                };
                let dst_ty = caller.register_types[dst as usize];
                let unique_reference = matches!(
                    types[dst_ty as usize].representation(),
                    Type::RefUnique { .. }
                );
                if unique_reference {
                    !matches!(
                        statement.kind,
                        InstructionKind::Move { .. }
                            | InstructionKind::Reborrow { unique: true, .. }
                    )
                } else {
                    !types[dst_ty as usize].claimed_duplicable()
                        || !types[dst_ty as usize].claimed_zero_use_allowed()
                        || !matches!(
                            statement.kind,
                            InstructionKind::Const { .. }
                                | InstructionKind::Copy { .. }
                                | InstructionKind::Primitive { .. }
                        )
                }
            }) {
                continue;
            }

            let handler_ty = caller.register_types[*handler_register as usize];
            let Some(Type::Handler {
                handler_def: value_definition,
                ..
            }) = types.get(handler_ty as usize).map(Type::representation)
            else {
                continue;
            };
            let Some(Type::Callable {
                capture_type: body_capture,
                receiver_mode: body_mode,
                ..
            }) = types.get(*body_type as usize).map(Type::representation)
            else {
                continue;
            };
            if value_definition != handler_def || *body_mode != 2 {
                continue;
            }

            let Some(raw_body_function) = direct_target(program, *body_declaration) else {
                continue;
            };
            let Some(resolved_body_function) =
                resolve_forwarded_terminal_body(program, raw_body_function, types)
            else {
                continue;
            };
            let body_function = &resolved_body_function;
            if !body_function.params.is_empty()
                || body_function.receiver_mode != Some(2)
                || body_function.receiver_type != *body_capture
                || !body_function.return_cleanup.is_empty()
                || body_function.blocks.len() != 1
                || body_function.blocks[0].id != body_function.entry
                || !body_function.blocks[0].params.is_empty()
            {
                continue;
            }
            let body_block = &body_function.blocks[0];
            let Terminator::Perform {
                result: None,
                protocol,
                operation,
                payloads,
                capture,
                resume: None,
            } = &body_block.terminator
            else {
                continue;
            };
            let Some(selected_index) = definition
                .clauses
                .iter()
                .position(|clause| clause.protocol == *protocol && clause.operation == *operation)
            else {
                continue;
            };
            let descriptor = &definition.clauses[selected_index];
            let Some(operation_definition) = protocols
                .get(descriptor.protocol as usize)
                .and_then(|protocol| protocol.operations.get(descriptor.operation as usize))
            else {
                continue;
            };
            if clause_values.iter().enumerate().any(
                |(index, (_, _, _, _, capture_free, capture_type, zero_use_allowed))| {
                    index != selected_index
                        && (!capture_free || *capture_type != UNIT || !zero_use_allowed)
                },
            ) {
                continue;
            }
            let (clause_statement, clause_register, clause_type, clause_function, _, _, _) =
                &clause_values[selected_index];
            let Some(Type::Callable {
                signature: clause_signature,
                receiver_mode: clause_mode,
                ..
            }) = types.get(*clause_type as usize).map(Type::representation)
            else {
                continue;
            };
            if !operation_definition.terminal
                || operation_definition.resumption_lower != 0
                || operation_definition.resumption_upper != Some(0)
                || descriptor.resumption_type.is_some()
                || *clause_mode != 2
                || clause_signature != &descriptor.callable_signature
                || clause_signature.result != caller.register_types[*result as usize]
                || !capture.captured_residuals.is_empty()
                || !capture.cancellation_safe
            {
                continue;
            }

            // Peel the canonical owned-callable receiver shell when every
            // capture is a freely disposable scalar. This lets terminal
            // fusion preserve actual computed payloads, rather than only
            // payloads which happened to constant-fold before this pass.
            let mut body_capture_bindings = Vec::new();
            let mut body_statement_start = 0;
            let mut available = BTreeSet::new();
            if body_captures.is_empty() {
                if *body_capture != UNIT {
                    continue;
                }
            } else {
                if body_block.statements.len() < body_captures.len() + 1 {
                    continue;
                }
                let mut canonical = true;
                for (field, (capture_operand, statement)) in
                    body_captures.iter().zip(&body_block.statements).enumerate()
                {
                    let InstructionKind::ProjectMove {
                        dst,
                        src:
                            Operand {
                                register: 0,
                                mode: UseMode::Move,
                            },
                        field: actual_field,
                    } = statement.kind
                    else {
                        canonical = false;
                        break;
                    };
                    let capture_ty = caller.register_types[capture_operand.register as usize];
                    let capture_is_unique_reference = matches!(
                        types[capture_ty as usize].representation(),
                        Type::RefUnique { .. }
                    );
                    if capture_operand.mode != UseMode::Move
                        || actual_field != field as u32
                        || body_function.register_types[dst as usize] != capture_ty
                        || (!types[capture_ty as usize].claimed_duplicable()
                            && !capture_is_unique_reference)
                        || (!types[capture_ty as usize].claimed_zero_use_allowed()
                            && !capture_is_unique_reference)
                    {
                        canonical = false;
                        break;
                    }
                    canonical &= available.insert(dst);
                    body_capture_bindings.push((dst, capture_operand.register));
                }
                if !canonical
                    || !matches!(
                        body_block.statements[body_captures.len()].kind,
                        InstructionKind::Deconstruct { src: 0 }
                    )
                {
                    continue;
                }
                body_statement_start = body_captures.len() + 1;
            }

            // Scalar computations are safe to transplant verbatim: they do
            // not carry ownership or control, and trapping primitives retain
            // their original order before the terminal performance.
            let mut safe = true;
            for statement in &body_block.statements[body_statement_start..] {
                match &statement.kind {
                    InstructionKind::Const { dst, .. } => safe &= available.insert(*dst),
                    InstructionKind::Copy { dst, src } if available.contains(&src.register) => {
                        safe &= available.insert(*dst);
                    }
                    InstructionKind::Move { dst, src } if available.contains(&src.register) => {
                        safe &= available.insert(*dst);
                    }
                    InstructionKind::Construct { dst, fields, .. }
                        if fields
                            .iter()
                            .all(|field| available.contains(&field.register)) =>
                    {
                        safe &= available.insert(*dst);
                    }
                    InstructionKind::Primitive { dst, args, .. }
                        if args
                            .iter()
                            .all(|argument| available.contains(&argument.register))
                            && types[body_function.register_types[*dst as usize] as usize]
                                .claimed_duplicable()
                            && types[body_function.register_types[*dst as usize] as usize]
                                .claimed_zero_use_allowed() =>
                    {
                        safe &= available.insert(*dst);
                    }
                    _ => safe = false,
                }
            }
            safe &= payloads
                .iter()
                .all(|payload| available.contains(&payload.register));
            let Some((_, cleanup_plan)) =
                body_function
                    .flow
                    .plan_for(&crate::compiler_mir::CleanupEdge::TerminalPerform {
                        block: body_block.id,
                    })
            else {
                continue;
            };
            let shared_capture_cleanup = body_capture_bindings
                .iter()
                .map(|(body_register, _)| *body_register)
                .filter(|body_register| {
                    matches!(
                        types[body_function.register_types[*body_register as usize] as usize]
                            .representation(),
                        Type::RefShared { .. }
                    ) && !cleanup_plan.protected.contains(body_register)
                })
                .collect::<Vec<_>>();
            let mut next_shared_capture = 0;
            let mut body_cleanup_owners = Vec::new();
            for action in &cleanup_plan.actions {
                let owner = match action {
                    CleanupAction::Destroy(owner) => *owner,
                    CleanupAction::EndBorrow(_) => {
                        let Some(owner) = shared_capture_cleanup.get(next_shared_capture).copied()
                        else {
                            safe = false;
                            break;
                        };
                        next_shared_capture += 1;
                        owner
                    }
                    CleanupAction::DestroyResidual { .. } | CleanupAction::DestroyIf { .. } => {
                        safe = false;
                        break;
                    }
                };
                if owner == 0 && body_function.receiver_type == UNIT {
                    continue;
                }
                // Custom hooks have already been elaborated at this point in
                // the pipeline. Reintroducing a plain Drop while transplanting
                // the terminal body would silently turn that hook into
                // structural cleanup, so leave the handler boundary intact.
                if body_function
                    .flow
                    .locals
                    .get(owner as usize)
                    .is_some_and(|fact| fact.drop_glue == DropGlueKind::Custom)
                {
                    safe = false;
                    break;
                }
                if !available.contains(&owner) {
                    safe = false;
                    break;
                }
                body_cleanup_owners.push(owner);
            }
            safe &= next_shared_capture == shared_capture_cleanup.len();
            // A unique loan can cross this rewrite only when ownership of the
            // reference itself is transferred as an operation payload. Any
            // abandoned unique capture still needs the original handler/
            // continuation boundary to end its loan in the proven order.
            safe &= capture.captured_references.iter().all(|reference| {
                !matches!(
                    types[body_function.register_types[*reference as usize] as usize]
                        .representation(),
                    Type::RefUnique { .. }
                ) || cleanup_plan.protected.contains(reference)
            });
            safe &= capture.captured_owners.iter().all(|owner| {
                (*owner == 0 && body_function.receiver_type == UNIT)
                    || body_cleanup_owners.contains(owner)
                    || cleanup_plan.protected.contains(owner)
            });
            if !safe {
                continue;
            }

            candidates.push(TerminalHandlerFusion {
                caller: caller_index,
                block: block_index,
                statement_start,
                clause_statement: clause_statement.clone(),
                clause_register: *clause_register,
                clause_function: *clause_function,
                result: *result,
                normal: normal.clone(),
                capture_setup_statements: capture_setup_statements.to_vec(),
                body_register_types: body_function.register_types.clone(),
                body_capture_bindings,
                body_statements: body_block.statements[body_statement_start..].to_vec(),
                body_cleanup_owners,
                payloads: payloads.clone(),
            });
        }
    }

    let rewrite_work = candidates
        .iter()
        .map(|candidate| candidate.body_statements.len() as u64 + 4)
        .sum::<u64>();
    let total_work = work.saturating_add(rewrite_work);
    if total_work > budget {
        return (PassOutcome::BudgetExhausted, work.min(budget));
    }
    if candidates.is_empty() {
        return (PassOutcome::Unchanged, work);
    }

    for candidate in candidates {
        let function = &mut program.functions[candidate.caller];
        let block = &mut function.blocks[candidate.block];
        block.statements.truncate(candidate.statement_start);
        let cleanup_span = candidate.clause_statement.span;
        block.statements.push(candidate.clause_statement);
        block.statements.extend(candidate.capture_setup_statements);
        let mut registers = vec![None; candidate.body_register_types.len()];
        for (body_register, caller_register) in candidate.body_capture_bindings {
            registers[body_register as usize] = Some(caller_register);
        }
        for mut statement in candidate.body_statements {
            let old_destination = statement
                .kind
                .destination()
                .expect("terminal-fusion statements always define registers");
            let new_destination = function.register_types.len() as Register;
            function
                .register_types
                .push(candidate.body_register_types[old_destination as usize]);
            registers[old_destination as usize] = Some(new_destination);
            remap_instruction(&mut statement.kind, &registers)
                .expect("terminal-fusion operands were proven locally available");
            block.statements.push(statement);
        }
        for owner in candidate.body_cleanup_owners {
            let owner = registers[owner as usize]
                .expect("terminal-fusion cleanup owners were proven locally available");
            block.statements.push(Instruction {
                span: cleanup_span,
                kind: InstructionKind::Drop {
                    owner: Operand {
                        register: owner,
                        mode: UseMode::Move,
                    },
                },
            });
        }
        let mut payloads = candidate.payloads;
        for payload in &mut payloads {
            remap_operand(payload, &registers)
                .expect("terminal-fusion payloads were proven locally available");
        }
        block.terminator = Terminator::CallIndirect {
            result: Some(candidate.result),
            callable: Operand {
                register: candidate.clause_register,
                mode: UseMode::Move,
            },
            known_function: Some(candidate.clause_function),
            receiver_mode: 2,
            cleanup_callable: false,
            args: payloads,
            normal: candidate.normal,
        };
    }
    for function in &mut program.functions {
        function.features = infer_feature_bits(function);
    }
    (PassOutcome::Changed, total_work)
}

fn rewrite_direct_resumptive_handler(
    function: &mut Function,
    candidate: &DirectResumptiveHandlerFusion,
) -> Option<()> {
    let body_entry = candidate
        .body
        .blocks
        .iter()
        .find(|block| block.id == candidate.body.entry)?;
    let Terminator::Perform {
        result: Some(body_perform_result),
        payloads,
        resume: Some(body_resume),
        ..
    } = &body_entry.terminator
    else {
        return None;
    };
    let clause_entry = candidate
        .clause
        .blocks
        .iter()
        .find(|block| block.id == candidate.clause.entry)?;

    let block = function.blocks.get_mut(candidate.block)?;
    block.statements.truncate(candidate.statement_start);

    let mut body_registers = vec![None; candidate.body.register_types.len()];
    let mut body_omitted = BTreeSet::from([0]);
    append_transplanted_statements(
        &candidate.body,
        &body_entry.statements,
        &mut body_registers,
        &mut body_omitted,
        &mut function.register_types,
        &mut block.statements,
    )?;
    let mut mapped_payloads = payloads.clone();
    for payload in &mut mapped_payloads {
        remap_operand(payload, &body_registers)?;
        if payload.mode != UseMode::Move {
            return None;
        }
    }
    if mapped_payloads.len() + 1 != candidate.clause.params.len() {
        return None;
    }

    let mut clause_registers = vec![None; candidate.clause.register_types.len()];
    let mut clause_omitted = BTreeSet::from([0, candidate.clause_resumption]);
    for (index, payload) in mapped_payloads.iter().enumerate() {
        let parameter = (index + 1) as Register;
        if candidate.clause.register_types.get(parameter as usize)
            != function.register_types.get(payload.register as usize)
        {
            return None;
        }
        clause_registers[parameter as usize] = Some(payload.register);
    }
    append_transplanted_statements(
        &candidate.clause,
        &clause_entry.statements,
        &mut clause_registers,
        &mut clause_omitted,
        &mut function.register_types,
        &mut block.statements,
    )?;

    let clause_result = match &clause_entry.terminator {
        Terminator::Resume {
            result,
            resumption,
            value,
            normal,
            ..
        } => {
            if !clause_omitted.contains(&resumption.register) || value.mode != UseMode::Move {
                return None;
            }
            let mut value = *value;
            remap_operand(&mut value, &clause_registers)?;
            body_registers[*body_perform_result as usize] = Some(value.register);
            let body_result = append_transplanted_linear_suffix(
                &candidate.body,
                body_resume,
                &mut body_registers,
                &mut body_omitted,
                &mut function.register_types,
                &mut block.statements,
            )??;
            if body_result.mode != UseMode::Move
                || candidate.clause.register_types.get(*result as usize)
                    != function.register_types.get(body_result.register as usize)
            {
                return None;
            }
            clause_registers[*result as usize] = Some(body_result.register);
            append_transplanted_linear_suffix(
                &candidate.clause,
                normal,
                &mut clause_registers,
                &mut clause_omitted,
                &mut function.register_types,
                &mut block.statements,
            )??
        }
        Terminator::Cancel {
            result,
            resumption,
            normal,
        } => {
            if !clause_omitted.contains(&resumption.register)
                || candidate
                    .clause
                    .register_types
                    .get(*result as usize)
                    .copied()
                    != Some(UNIT)
            {
                return None;
            }
            let unit = function.register_types.len() as Register;
            function.register_types.push(UNIT);
            block.statements.push(Instruction {
                span: clause_entry
                    .statements
                    .last()
                    .map_or(Span::default(), |statement| statement.span),
                kind: InstructionKind::Const {
                    dst: unit,
                    value: Constant::Unit,
                },
            });
            clause_registers[*result as usize] = Some(unit);
            append_transplanted_linear_suffix(
                &candidate.clause,
                normal,
                &mut clause_registers,
                &mut clause_omitted,
                &mut function.register_types,
                &mut block.statements,
            )??
        }
        _ => return None,
    };
    if clause_result.mode != UseMode::Move
        || function.register_types.get(clause_result.register as usize)
            != function.register_types.get(candidate.result as usize)
    {
        return None;
    }
    let mut normal = candidate.normal.clone();
    normal.args.insert(0, clause_result);
    block.terminator = Terminator::Goto(normal);
    Some(())
}

/// Eliminate a canonical one-shot nonterminal handler by statically composing
/// its clause with the suspended continuation.  This handles both `resume` and
/// `cancel`, selected clauses in multi-operation definitions, and known hits in
/// partial handlers.  Captured continuation state, multiple resumptions, and a
/// continued body which can perform again remain explicit barriers.
fn specialize_direct_resumptive_handlers(
    program: &mut Program,
    types: &[Type],
    protocols: &[Protocol],
    handler_defs: &[HandlerDef],
    budget: u64,
) -> (PassOutcome, u64) {
    let mut scan_work = 0_u64;
    let mut candidates = Vec::new();
    for (caller_index, caller) in program.functions.iter().enumerate() {
        let mut use_counts = BTreeMap::<Register, u32>::new();
        for block in &caller.blocks {
            for register in used_registers(block) {
                *use_counts.entry(register).or_default() += 1;
            }
        }
        for (block_index, block) in caller.blocks.iter().enumerate() {
            scan_work = scan_work.saturating_add(block.statements.len() as u64 + 1);
            let Terminator::Handle {
                result,
                handler,
                body,
                normal,
            } = &block.terminator
            else {
                continue;
            };
            if handler.mode != UseMode::Move || body.mode != UseMode::Move {
                continue;
            }
            let Some(body_statement) = block.statements.last() else {
                continue;
            };
            let InstructionKind::MakeCallable {
                dst: body_register,
                callable_type: body_type,
                function: body_declaration,
                captures: body_captures,
            } = &body_statement.kind
            else {
                continue;
            };
            if *body_register != body.register
                || !body_captures.is_empty()
                || use_counts.get(body_register).copied() != Some(1)
            {
                continue;
            }
            let Some(handler_statement_index) = block.statements[..block.statements.len() - 1]
                .iter()
                .rposition(|statement| {
                    matches!(statement.kind, InstructionKind::MakeHandler { dst, .. } if dst == handler.register)
                })
            else {
                continue;
            };
            let InstructionKind::MakeHandler {
                dst: handler_register,
                handler_def,
                clauses,
            } = &block.statements[handler_statement_index].kind
            else {
                continue;
            };
            let Some(definition) = handler_defs.get(*handler_def as usize) else {
                continue;
            };
            if *handler_register != handler.register
                || use_counts.get(handler_register).copied() != Some(1)
                || clauses.len() != definition.clauses.len()
                || definition.clauses.is_empty()
                || handler_statement_index < definition.clauses.len()
                || handler_statement_index + 1 != block.statements.len() - 1
            {
                continue;
            }
            let statement_start = handler_statement_index - definition.clauses.len();
            let clause_statements = &block.statements[statement_start..handler_statement_index];
            let mut clause_values = Vec::new();
            let mut clauses_safe = true;
            for (index, statement) in clause_statements.iter().enumerate() {
                let InstructionKind::MakeCallable {
                    dst,
                    callable_type,
                    function,
                    captures,
                } = &statement.kind
                else {
                    clauses_safe = false;
                    break;
                };
                let Some(Type::Callable {
                    capture_type,
                    receiver_mode,
                    ..
                }) = types.get(*callable_type as usize).map(Type::representation)
                else {
                    clauses_safe = false;
                    break;
                };
                if clauses.get(index)
                    != Some(&Operand {
                        register: *dst,
                        mode: UseMode::Move,
                    })
                    || use_counts.get(dst).copied() != Some(1)
                    || !captures.is_empty()
                    || *capture_type != UNIT
                    || !types[*callable_type as usize].claimed_zero_use_allowed()
                {
                    clauses_safe = false;
                    break;
                }
                clause_values.push((*function, *receiver_mode));
            }
            if !clauses_safe {
                continue;
            }
            let Some(Type::Callable {
                capture_type: body_capture,
                receiver_mode: body_mode,
                ..
            }) = types.get(*body_type as usize).map(Type::representation)
            else {
                continue;
            };
            if *body_capture != UNIT || *body_mode != 2 {
                continue;
            }
            let Some(body_function) = direct_target(program, *body_declaration) else {
                continue;
            };
            if !body_function.params.is_empty()
                || body_function.receiver_mode != Some(2)
                || body_function.blocks.len() != 2
                || body_function
                    .return_cleanup
                    .iter()
                    .any(|register| *register != 0)
            {
                continue;
            }
            let Some(body_entry) = body_function
                .blocks
                .iter()
                .find(|body_block| body_block.id == body_function.entry)
            else {
                continue;
            };
            let Terminator::Perform {
                result: Some(_),
                protocol,
                operation,
                payloads,
                capture,
                resume: Some(_),
            } = &body_entry.terminator
            else {
                continue;
            };
            let Some(selected_index) = definition
                .clauses
                .iter()
                .position(|clause| clause.protocol == *protocol && clause.operation == *operation)
            else {
                // This is the partial-handler fallback path: preserve the
                // delimiter so the operation continues outward unchanged.
                continue;
            };
            let descriptor = &definition.clauses[selected_index];
            let Some(operation_definition) = protocols
                .get(descriptor.protocol as usize)
                .and_then(|protocol| protocol.operations.get(descriptor.operation as usize))
            else {
                continue;
            };
            if operation_definition.terminal
                || operation_definition.resumption_upper != Some(1)
                || descriptor.resumption_type.is_none()
                || payloads.len() + 1 != descriptor.callable_signature.params.len()
            {
                continue;
            }
            let Some((clause_declaration, clause_mode)) = clause_values.get(selected_index) else {
                continue;
            };
            let Some(clause_function) = direct_target(program, *clause_declaration) else {
                continue;
            };
            if *clause_mode != clause_function.receiver_mode.unwrap_or(u32::MAX)
                || clause_function.blocks.is_empty()
                || clause_function.params.len() != payloads.len() + 1
                || clause_function
                    .return_cleanup
                    .iter()
                    .any(|register| *register != 0)
            {
                continue;
            }
            let clause_resumption = clause_function.params.len() as Register;
            if clause_function.params.last().copied() != descriptor.resumption_type {
                continue;
            }
            let Some(clause_entry) = clause_function
                .blocks
                .iter()
                .find(|clause_block| clause_block.id == clause_function.entry)
            else {
                continue;
            };
            if !matches!(
                clause_entry.terminator,
                Terminator::Resume { .. } | Terminator::Cancel { .. }
            ) {
                continue;
            }
            if !capture.cancellation_safe
                || !capture.captured_references.is_empty()
                || !capture.captured_residuals.is_empty()
                || capture.captured_owners.iter().any(|owner| *owner != 0)
            {
                continue;
            }
            if matches!(clause_entry.terminator, Terminator::Cancel { .. })
                && operation_definition.resumption_lower != 0
            {
                continue;
            }
            candidates.push(DirectResumptiveHandlerFusion {
                caller: caller_index,
                block: block_index,
                statement_start,
                result: *result,
                normal: normal.clone(),
                body: body_function.clone(),
                clause: clause_function.clone(),
                clause_resumption,
            });
        }
    }
    let rewrite_work = candidates
        .iter()
        .map(|candidate| {
            body_size(&candidate.body)
                .saturating_add(body_size(&candidate.clause))
                .saturating_add(4)
        })
        .sum::<u64>();
    let total_work = scan_work.saturating_add(rewrite_work);
    if total_work > budget {
        return (PassOutcome::BudgetExhausted, scan_work.min(budget));
    }
    if candidates.is_empty() {
        return (PassOutcome::Unchanged, scan_work);
    }

    let mut scratch = program.clone();
    let mut changed = false;
    for candidate in &candidates {
        let Some(function) = scratch.functions.get_mut(candidate.caller) else {
            continue;
        };
        let mut rewritten = function.clone();
        if rewrite_direct_resumptive_handler(&mut rewritten, candidate).is_some() {
            *function = rewritten;
            changed = true;
        }
    }
    if !changed {
        return (PassOutcome::Unchanged, total_work);
    }
    for function in &mut scratch.functions {
        function.features = infer_feature_bits(function);
    }
    *program = scratch;
    (PassOutcome::Changed, total_work)
}

fn specialize_static_handlers(
    program: &mut Program,
    types: &[Type],
    protocols: &[Protocol],
    handler_defs: &[HandlerDef],
    budget: u64,
) -> (PassOutcome, u64) {
    let mut scratch = program.clone();
    let (terminal, terminal_work) =
        specialize_terminal_handlers(&mut scratch, types, protocols, handler_defs, budget);
    if terminal == PassOutcome::BudgetExhausted {
        return (terminal, terminal_work);
    }
    let remaining = budget.saturating_sub(terminal_work);
    let (resumptive, resumptive_work) = specialize_direct_resumptive_handlers(
        &mut scratch,
        types,
        protocols,
        handler_defs,
        remaining,
    );
    let work = terminal_work.saturating_add(resumptive_work);
    if resumptive == PassOutcome::BudgetExhausted {
        return (resumptive, work);
    }
    let outcome = if terminal == PassOutcome::Changed || resumptive == PassOutcome::Changed {
        *program = scratch;
        PassOutcome::Changed
    } else {
        PassOutcome::Unchanged
    };
    (outcome, work)
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct InlineCandidate {
    caller: u32,
    block: u32,
    target: u32,
}

const MAX_PROGRAM_CLONED_BODIES: u32 = 4_096;

#[derive(Clone, Debug, Eq, PartialEq)]
struct InlinePolicyState {
    cloned_bodies_remaining: u32,
    source_clones: BTreeMap<u32, u32>,
    depths: BTreeMap<u32, u8>,
}

impl Default for InlinePolicyState {
    fn default() -> Self {
        Self {
            cloned_bodies_remaining: MAX_PROGRAM_CLONED_BODIES,
            source_clones: BTreeMap::new(),
            depths: BTreeMap::new(),
        }
    }
}

/// Compute deterministic call-graph SCCs from the pre-inline program. Known
/// indirect targets participate because devirtualization has made those graph
/// edges just as exact as direct calls.
fn inline_call_graph_sccs(program: &Program) -> BTreeMap<u32, usize> {
    let declarations = program
        .functions
        .iter()
        .map(|function| function.declaration)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let indices = declarations
        .iter()
        .copied()
        .enumerate()
        .map(|(index, declaration)| (declaration, index))
        .collect::<BTreeMap<_, _>>();
    let mut edges = vec![BTreeSet::new(); declarations.len()];
    for function in &program.functions {
        let source = indices[&function.declaration];
        for block in &function.blocks {
            let target = match block.terminator {
                Terminator::Call { function, .. } | Terminator::TailCall { function, .. } => {
                    Some(function)
                }
                Terminator::CallIndirect { known_function, .. }
                | Terminator::TailCallIndirect { known_function, .. } => known_function,
                _ => None,
            };
            if let Some(target) = target.and_then(|target| indices.get(&target).copied()) {
                edges[source].insert(target);
            }
        }
    }
    let edges = edges
        .into_iter()
        .map(|targets| targets.into_iter().collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let mut reverse = vec![Vec::new(); declarations.len()];
    for (source, targets) in edges.iter().enumerate() {
        for &target in targets {
            reverse[target].push(source);
        }
    }

    let mut visited = vec![false; declarations.len()];
    let mut finish = Vec::with_capacity(declarations.len());
    for start in 0..declarations.len() {
        if visited[start] {
            continue;
        }
        visited[start] = true;
        let mut stack = vec![(start, 0_usize)];
        while let Some((node, next)) = stack.last_mut() {
            if *next < edges[*node].len() {
                let successor = edges[*node][*next];
                *next += 1;
                if !visited[successor] {
                    visited[successor] = true;
                    stack.push((successor, 0));
                }
            } else {
                finish.push(*node);
                stack.pop();
            }
        }
    }

    let mut components = vec![usize::MAX; declarations.len()];
    let mut component = 0_usize;
    for &start in finish.iter().rev() {
        if components[start] != usize::MAX {
            continue;
        }
        components[start] = component;
        let mut stack = vec![start];
        while let Some(node) = stack.pop() {
            for &predecessor in reverse[node].iter().rev() {
                if components[predecessor] == usize::MAX {
                    components[predecessor] = component;
                    stack.push(predecessor);
                }
            }
        }
        component += 1;
    }
    declarations.into_iter().zip(components).collect()
}

fn inline_weight(function: &Function) -> u64 {
    function
        .blocks
        .iter()
        .map(|block| {
            let statements = block
                .statements
                .iter()
                .map(|statement| match statement.kind {
                    // The compact optimizer does not yet receive the drop-glue
                    // table, so use the custom-cleanup weight conservatively.
                    InstructionKind::Drop { .. } => 12,
                    InstructionKind::MakeHandler { .. }
                    | InstructionKind::MakeHandlerShared { .. } => 20,
                    _ => 1,
                })
                .sum::<u64>();
            statements
                + match block.terminator {
                    Terminator::Goto(_) | Terminator::Switch { .. } => 2,
                    Terminator::Call { .. }
                    | Terminator::CallSelf { .. }
                    | Terminator::CallKnownReceiver { .. }
                    | Terminator::HostCall { .. }
                    | Terminator::TailCall { .. }
                    | Terminator::TailCallSelf { .. }
                    | Terminator::TailCallKnownReceiver { .. } => 5,
                    Terminator::CallIndirect { .. } | Terminator::TailCallIndirect { .. } => 8,
                    Terminator::Handle { .. }
                    | Terminator::Perform { .. }
                    | Terminator::Resume { .. }
                    | Terminator::TailResume { .. }
                    | Terminator::Cancel { .. }
                    | Terminator::Leave { .. }
                    | Terminator::Abort { .. } => 20,
                    Terminator::Return { .. } | Terminator::Unreachable => 1,
                }
        })
        .sum()
}

fn type_carries_reference(types: &[Type], ty: TypeId) -> bool {
    fn visit(types: &[Type], ty: TypeId, visiting: &mut BTreeSet<TypeId>) -> bool {
        if !visiting.insert(ty) {
            return false;
        }
        let carries = match types.get(ty as usize).map(Type::representation) {
            Some(Type::RefShared { .. } | Type::RefUnique { .. }) => true,
            Some(Type::Array { element }) => visit(types, *element, visiting),
            Some(Type::Callable { capture_type, .. } | Type::Handler { capture_type, .. }) => {
                visit(types, *capture_type, visiting)
            }
            Some(Type::BindingPack { payload_type, .. }) => visit(types, *payload_type, visiting),
            Some(Type::Tuple { fields, .. }) => {
                fields.iter().any(|field| visit(types, *field, visiting))
            }
            Some(Type::Struct { fields, .. }) => {
                fields.iter().any(|field| visit(types, field.ty, visiting))
            }
            Some(Type::Enum { variants, .. }) => variants.iter().any(|variant| {
                variant
                    .fields
                    .iter()
                    .any(|field| visit(types, field.ty, visiting))
            }),
            // An invalid type is rejected by MIR validation. Refuse to use it
            // as proof for an ownership-sensitive inline in the meantime.
            None => true,
            _ => false,
        };
        visiting.remove(&ty);
        carries
    }

    visit(types, ty, &mut BTreeSet::new())
}

fn inline_leaf_legal(target: &Function, types: &[Type]) -> bool {
    if target.receiver_mode.is_some()
        || target.no_return
        || !target.outward_protocols.is_empty()
        // A reference-returning call is an ownership boundary: its return
        // contract transfers a loan rooted in one argument. Compact MIR does
        // not yet encode that route on Primitive instructions, so cloning a
        // trusted reference leaf would manufacture a result without
        // transplanting its owner dependency.
        || type_carries_reference(types, target.result)
        || target.features.contains(FeatureBits::LOANS)
        || target.features.contains(FeatureBits::HANDLERS)
        || target.features.contains(FeatureBits::RESUMPTIONS)
        || target.blocks.len() != 1
    {
        return false;
    }
    let block = &target.blocks[0];
    if block.id != target.entry
        || !block.params.is_empty()
        || !matches!(block.terminator, Terminator::Return { .. })
    {
        return false;
    }
    let abi_end = target.params.len() as Register;
    if target.return_cleanup.contains(&0)
        || used_registers(block).contains(&0)
        || block.statements.iter().any(|statement| {
            statement
                .kind
                .destination()
                .is_some_and(|register| register <= abi_end)
        })
    {
        return false;
    }

    inline_leaf_exit_survivors(target).is_some()
}

/// Return registers still initialized after a leaf's returned value has moved
/// out. Cleanup-owned survivors make the leaf unsafe to clone because the
/// caller does not inherit the callee's return-cleanup table. Cleanup-free
/// survivors are permitted only at a single-predecessor continuation; the
/// caller-side candidate check enforces that CFG condition.
fn inline_leaf_exit_survivors(target: &Function) -> Option<BTreeSet<Register>> {
    let block = target.blocks.first()?;
    let mut exit =
        simple_block_exit_states(target).and_then(|states| states.get(&block.id).cloned())?;
    if let Terminator::Return { value: Some(value) } = &block.terminator {
        if value.mode != UseMode::Move
            || !exit.get(value.register as usize).copied().unwrap_or(false)
        {
            return None;
        }
        exit[value.register as usize] = false;
    }
    let survivors = exit
        .into_iter()
        .enumerate()
        .filter_map(|(register, initialized)| initialized.then_some(register as Register))
        .collect::<BTreeSet<_>>();
    survivors
        .iter()
        .all(|register| !target.return_cleanup.contains(register))
        .then_some(survivors)
}

fn inline_candidate_depth(depths: &BTreeMap<u32, u8>, target: u32, depth_cap: u8) -> Option<u8> {
    let depth = depths.get(&target).copied().unwrap_or(0).saturating_add(1);
    (depth <= depth_cap).then_some(depth)
}

/// Whether the call's normal continuation is a closed forward region. A fresh
/// live callee register is present on the source edge and throughout this
/// region; an edge entering it from anywhere else would create a mismatched
/// initialization state at that join.
fn inline_survivor_region_is_closed(
    caller: &Function,
    source_block: u32,
    continuation: u32,
) -> bool {
    let mut reachable = BTreeSet::new();
    let mut queue = VecDeque::from([continuation]);
    while let Some(block) = queue.pop_front() {
        if !reachable.insert(block) {
            continue;
        }
        let Some(body) = caller.blocks.iter().find(|candidate| candidate.id == block) else {
            return false;
        };
        queue.extend(successors(&body.terminator));
    }
    caller.blocks.iter().all(|predecessor| {
        reachable.contains(&predecessor.id)
            || predecessor.id == source_block
            || successors(&predecessor.terminator)
                .into_iter()
                .all(|successor| !reachable.contains(&successor))
    })
}

/// Prove a multi-block callee can be cloned without transplanting any of the
/// ownership/control arenas. Every reachable exit must consume all callee
/// state except the value moved into the caller continuation. This admits pure
/// branching/forwarding CFGs while keeping cleanup, loans, labels, handlers,
/// resumptions, and callee-owned survivors as hard barriers.
fn inline_multiblock_exit_survivors(
    target: &Function,
    types: &[Type],
) -> Option<BTreeSet<Register>> {
    if target.receiver_mode.is_some()
        || target.no_return
        || !target.outward_protocols.is_empty()
        || type_carries_reference(types, target.result)
        || target.blocks.len() < 2
        || !target.return_cleanup.is_empty()
        || target.features.contains(FeatureBits::HANDLERS)
        || target.features.contains(FeatureBits::RESUMPTIONS)
    {
        return None;
    }
    let entry = target
        .blocks
        .iter()
        .find(|block| block.id == target.entry)?;
    if !entry.params.is_empty()
        || target.blocks.iter().any(|block| {
            block
                .params
                .iter()
                .any(|parameter| !matches!(parameter.role, BlockParamRole::Ordinary))
                || !matches!(
                    block.terminator,
                    Terminator::Goto(_) | Terminator::Switch { .. } | Terminator::Return { .. }
                )
        })
    {
        return None;
    }
    let abi_end = target.params.len() as Register;
    if target.blocks.iter().any(|block| {
        used_registers(block).contains(&0)
            || block.statements.iter().any(|statement| {
                statement
                    .kind
                    .destination()
                    .is_some_and(|register| register <= abi_end)
            })
    }) {
        return None;
    }
    let exits = simple_block_exit_states(target)?;
    let mut saw_return = false;
    let mut common_survivors = None;
    for block in &target.blocks {
        let Terminator::Return { value } = &block.terminator else {
            continue;
        };
        saw_return = true;
        if value.is_some() != (target.result != grandiose_vm::UNIT) {
            return None;
        }
        let mut state = exits.get(&block.id).cloned()?;
        if let Some(value) = value {
            if value.mode != UseMode::Move
                || !state.get(value.register as usize).copied().unwrap_or(false)
            {
                return None;
            }
            state[value.register as usize] = false;
        }
        let survivors = state
            .into_iter()
            .enumerate()
            .filter_map(|(register, initialized)| initialized.then_some(register as Register))
            .collect::<BTreeSet<_>>();
        if survivors
            .iter()
            .any(|register| target.return_cleanup.contains(register))
        {
            return None;
        }
        match &common_survivors {
            Some(common) if common != &survivors => return None,
            Some(_) => {}
            None => common_survivors = Some(survivors),
        }
    }
    saw_return.then(|| common_survivors.unwrap_or_default())
}

fn inline_multiblock_legal(target: &Function, types: &[Type]) -> bool {
    inline_multiblock_exit_survivors(target, types).is_some()
}

#[derive(Clone, Debug)]
struct InlineArenaMap {
    labels: BTreeMap<LabelId, LabelId>,
}

/// Transplant the callee's persistent ownership/control arenas into the
/// caller. Every identity is fresh and all cross-arena references are remapped
/// in one transaction. The caller clone is discarded if any ID space or
/// referential mapping cannot be represented.
fn append_inline_arenas(
    caller: &mut Function,
    target: &Function,
    registers: &[Option<Register>],
    blocks: &BTreeMap<u32, u32>,
) -> Option<InlineArenaMap> {
    let add = |base: usize, old: u32| u32::try_from(base).ok()?.checked_add(old);
    let register = |old| remap_register(old, registers);
    let block = |old| blocks.get(&old).copied();

    // Per-local facts are positional. Refuse to manufacture provenance when a
    // preexisting pass already left a sparse bridge; ImportPlaceFlow will
    // conservatively rebuild that shape on a later phase boundary.
    let append_locals = caller.flow.locals.len()
        == caller.register_types.len() - (registers.len() - 1)
        && target.flow.locals.len() == target.register_types.len();

    let source_base = caller.flow.sources.len();
    let source = |old: SourceInfoId| {
        if target.flow.sources.is_empty() {
            Some(SourceInfoId(0))
        } else {
            add(source_base, old.0).map(SourceInfoId)
        }
    };
    caller
        .flow
        .sources
        .extend(target.flow.sources.iter().copied());

    let scope_base = caller.flow.scopes.len();
    let scope = |old: ScopeId| add(scope_base, old.0).map(ScopeId);
    for mut fact in target.flow.scopes.clone() {
        fact.parent = match fact.parent {
            Some(parent) => Some(scope(parent)?),
            None => None,
        };
        for owner in &mut fact.owners {
            *owner = register(*owner)?;
        }
        caller.flow.scopes.push(fact);
    }

    if append_locals {
        for mut fact in target.flow.locals.iter().skip(1).cloned() {
            fact.scope = scope(fact.scope)?;
            fact.source = source(fact.source)?;
            caller.flow.locals.push(fact);
        }
    }

    let path_base = caller.flow.move_paths.facts.len();
    let path = |old: MovePathId| add(path_base, old.0).map(MovePathId);
    for mut fact in target.flow.move_paths.facts.clone() {
        fact.parent = match fact.parent {
            Some(parent) => Some(path(parent)?),
            None => None,
        };
        fact.base = register(fact.base)?;
        for child in &mut fact.children {
            *child = path(*child)?;
        }
        caller.flow.move_paths.facts.push(fact);
    }

    let loan_base = caller.flow.loans.len();
    let loan = |old: LoanId| add(loan_base, old.0).map(LoanId);
    for mut fact in target.flow.loans.clone() {
        fact.reference = register(fact.reference)?;
        fact.borrowed.base = register(fact.borrowed.base)?;
        fact.parent = match fact.parent {
            Some(parent) => Some(loan(parent)?),
            None => None,
        };
        fact.region = RegionId(add(loan_base, fact.region.0)?);
        fact.issued_block = block(fact.issued_block)?;
        fact.source = source(fact.source)?;
        caller.flow.loans.push(fact);
    }

    let label_base = caller.flow.labels.len();
    let label = |old: LabelId| add(label_base, old.0).map(LabelId);
    let labels = (0..target.flow.labels.len())
        .map(|old| {
            let old = LabelId(u32::try_from(old).ok()?);
            Some((old, label(old)?))
        })
        .collect::<Option<BTreeMap<_, _>>>()?;
    for mut fact in target.flow.labels.clone() {
        fact.scope = scope(fact.scope)?;
        fact.destination = block(fact.destination)?;
        caller.flow.labels.push(fact);
    }

    let cleanup_base = caller.flow.cleanup_plans.len();
    let cleanup = |old: CleanupPlanId| add(cleanup_base, old.0).map(CleanupPlanId);
    for mut fact in target.flow.handlers.clone() {
        fact.block = block(fact.block)?;
        fact.scope = scope(fact.scope)?;
        caller.flow.handlers.push(fact);
    }
    for mut fact in target.flow.performs.clone() {
        fact.block = block(fact.block)?;
        fact.frame_cleanup = match fact.frame_cleanup {
            Some(plan) => Some(cleanup(plan)?),
            None => None,
        };
        caller.flow.performs.push(fact);
    }
    for mut fact in target.flow.resumptions.clone() {
        fact.block = block(fact.block)?;
        fact.cancellation_cleanup = match fact.cancellation_cleanup {
            Some(plan) => Some(cleanup(plan)?),
            None => None,
        };
        caller.flow.resumptions.push(fact);
    }
    for mut fact in target.flow.indirect_calls.clone() {
        fact.block = block(fact.block)?;
        for owner in fact
            .capture
            .captured_owners
            .iter_mut()
            .chain(&mut fact.capture.captured_references)
        {
            *owner = register(*owner)?;
        }
        for residual in &mut fact.capture.captured_residuals {
            residual.register = register(residual.register)?;
        }
        caller.flow.indirect_calls.push(fact);
    }
    for mut fact in target.flow.joins.clone() {
        fact.block = block(fact.block)?;
        for incoming in &mut fact.incoming {
            *incoming = block(*incoming)?;
        }
        caller.flow.joins.push(fact);
    }
    for mut fact in target.flow.drop_flags.clone() {
        fact.flag = register(fact.flag)?;
        fact.owner = register(fact.owner)?;
        caller.flow.drop_flags.push(fact);
    }
    for mut plan in target.flow.cleanup_plans.clone() {
        plan.edge = match plan.edge {
            CleanupEdge::Return { block: at } => CleanupEdge::Return { block: block(at)? },
            CleanupEdge::TailCall { block: at } => CleanupEdge::TailCall { block: block(at)? },
            CleanupEdge::TerminalPerform { block: at } => {
                CleanupEdge::TerminalPerform { block: block(at)? }
            }
            CleanupEdge::Cancel { block: at } => CleanupEdge::Cancel { block: block(at)? },
            CleanupEdge::Leave {
                block: at,
                label: id,
            } => CleanupEdge::Leave {
                block: block(at)?,
                label: label(id)?,
            },
        };
        plan.source_scope = scope(plan.source_scope)?;
        plan.target_scope = scope(plan.target_scope)?;
        for action in &mut plan.actions {
            match action {
                CleanupAction::EndBorrow(id) => *id = loan(*id)?,
                CleanupAction::Destroy(local) | CleanupAction::DestroyResidual { local, .. } => {
                    *local = register(*local)?
                }
                CleanupAction::DestroyIf { local, flag } => {
                    *local = register(*local)?;
                    *flag = register(*flag)?;
                }
            }
        }
        for protected in &mut plan.protected {
            *protected = register(*protected)?;
        }
        caller.flow.cleanup_plans.push(plan);
    }
    Some(InlineArenaMap { labels })
}

fn remap_cloned_control_identities(
    instruction: &mut InstructionKind,
    arenas: &InlineArenaMap,
    blocks: &BTreeMap<u32, u32>,
) -> Option<()> {
    match instruction {
        InstructionKind::LabelPush { label, target, .. } => {
            *label = *arenas.labels.get(label)?;
            *target = *blocks.get(target)?;
        }
        InstructionKind::LabelPop { label } => *label = *arenas.labels.get(label)?,
        _ => {}
    }
    Some(())
}

fn remap_cloned_terminator_identities(
    terminator: &mut Terminator,
    arenas: &InlineArenaMap,
) -> Option<()> {
    if let Terminator::Leave { label, .. } = terminator {
        *label = *arenas.labels.get(label)?;
    }
    Some(())
}

fn remap_cloned_cfg_targets(
    terminator: &mut Terminator,
    blocks: &BTreeMap<u32, u32>,
) -> Option<()> {
    let remap = |edge: &mut Edge| {
        edge.target = *blocks.get(&edge.target)?;
        Some(())
    };
    match terminator {
        Terminator::Goto(edge) => remap(edge),
        Terminator::Switch {
            cases, otherwise, ..
        } => {
            for (_, edge) in cases {
                remap(edge)?;
            }
            remap(otherwise)
        }
        Terminator::Return { .. } => Some(()),
        _ => None,
    }
}

/// Inline a deliberately narrow, ownership-transparent leaf shape. Bodies
/// carrying loans or control sites wait for the full MIR arenas needed to give
/// those identities fresh IDs. The entire pass is transactional under its work
/// budget.
#[cfg(test)]
fn inline_by_cost(
    program: &mut Program,
    level: OptimizationLevel,
    budget: u64,
) -> (PassOutcome, u64) {
    inline_by_cost_with_policy(
        program,
        &Type::predefined(),
        level,
        budget,
        &mut InlinePolicyState::default(),
    )
}

fn inline_by_cost_with_policy(
    program: &mut Program,
    types: &[Type],
    level: OptimizationLevel,
    budget: u64,
    policy: &mut InlinePolicyState,
) -> (PassOutcome, u64) {
    let scan_work = operation_count(program);
    if scan_work > budget {
        return (PassOutcome::BudgetExhausted, scan_work);
    }
    let threshold = match level {
        OptimizationLevel::O0 | OptimizationLevel::O1 => {
            return (PassOutcome::SkippedUnavailable, 0);
        }
        OptimizationLevel::O2 => 60,
        OptimizationLevel::O3 => 120,
    };
    let growth_factor = if level == OptimizationLevel::O3 { 4 } else { 2 };
    let growth_slack = if level == OptimizationLevel::O3 {
        1_024
    } else {
        256
    };
    let depth_cap = if level == OptimizationLevel::O3 {
        16
    } else {
        8
    };
    let source_clone_cap = if level == OptimizationLevel::O3 {
        16
    } else {
        8
    };
    let originals = program
        .functions
        .iter()
        .map(|function| (function.declaration, inline_weight(function)))
        .collect::<BTreeMap<_, _>>();
    let components = inline_call_graph_sccs(program);
    let mut scratch = program.clone();
    let mut scratch_policy = policy.clone();
    let mut work = scan_work;
    let mut changed = false;
    for declaration in originals.keys().copied() {
        scratch_policy.depths.entry(declaration).or_insert(0);
    }

    loop {
        let targets = scratch
            .functions
            .iter()
            .filter(|function| {
                inline_leaf_legal(function, types) && inline_weight(function) <= threshold
            })
            .map(|function| function.declaration)
            .collect::<BTreeSet<_>>();
        let exit_survivors = scratch
            .functions
            .iter()
            .filter(|function| targets.contains(&function.declaration))
            .map(|function| {
                (
                    function.declaration,
                    inline_leaf_exit_survivors(function)
                        .expect("inline-legal leaf has a proven exit state"),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut candidates = Vec::new();
        for caller in &scratch.functions {
            for block in &caller.blocks {
                let Terminator::Call {
                    function: target,
                    args,
                    normal,
                    ..
                } = &block.terminator
                else {
                    continue;
                };
                if *target != caller.declaration
                    && targets.contains(target)
                    && components.get(&caller.declaration) != components.get(target)
                    && args.iter().all(|argument| argument.mode == UseMode::Move)
                    && args
                        .iter()
                        .map(|argument| argument.register)
                        .collect::<BTreeSet<_>>()
                        .len()
                        == args.len()
                    && (exit_survivors[target].is_empty()
                        || inline_survivor_region_is_closed(caller, block.id, normal.target))
                {
                    candidates.push(InlineCandidate {
                        caller: caller.declaration,
                        block: block.id,
                        target: *target,
                    });
                }
            }
        }
        candidates.sort_unstable();
        let mut changed_this_round = false;
        for candidate in candidates {
            let Some(next_depth) =
                inline_candidate_depth(&scratch_policy.depths, candidate.target, depth_cap)
            else {
                continue;
            };
            if scratch_policy
                .source_clones
                .get(&candidate.target)
                .copied()
                .unwrap_or(0)
                >= source_clone_cap
                || scratch_policy.cloned_bodies_remaining == 0
            {
                continue;
            }
            let Some(target) = scratch
                .functions
                .iter()
                .find(|function| function.declaration == candidate.target)
                .cloned()
            else {
                continue;
            };
            let target_block = &target.blocks[0];
            let Terminator::Return { value: returned } = &target_block.terminator else {
                continue;
            };
            let Some(caller_index) = scratch
                .functions
                .iter()
                .position(|function| function.declaration == candidate.caller)
            else {
                continue;
            };
            let Some(block_index) = scratch.functions[caller_index]
                .blocks
                .iter()
                .position(|block| block.id == candidate.block)
            else {
                continue;
            };
            let Terminator::Call {
                result,
                function,
                args,
                normal,
            } = scratch.functions[caller_index].blocks[block_index]
                .terminator
                .clone()
            else {
                continue;
            };
            if function != candidate.target
                || args.len() != target.params.len()
                || result.is_some() != returned.is_some()
            {
                continue;
            }

            let added_work =
                2_u64.saturating_mul(args.len() as u64 + target_block.statements.len() as u64 + 1);
            work = work.saturating_add(added_work);
            if work > budget {
                return (PassOutcome::BudgetExhausted, work);
            }

            let old_caller = scratch.functions[caller_index].clone();
            let caller = &mut scratch.functions[caller_index];
            let mut registers = vec![None; target.register_types.len()];
            for (old, ty) in target.register_types.iter().copied().enumerate().skip(1) {
                let new = caller.register_types.len() as Register;
                caller.register_types.push(ty);
                registers[old] = Some(new);
            }
            let block = &mut caller.blocks[block_index];
            let span = block
                .statements
                .last()
                .map(|statement| statement.span)
                .unwrap_or_default();
            for (index, argument) in args.into_iter().enumerate() {
                block.statements.push(Instruction {
                    span,
                    kind: InstructionKind::Move {
                        dst: registers[index + 1].expect("callee ABI register was mapped"),
                        src: argument,
                    },
                });
            }
            for mut statement in target_block.statements.clone() {
                remap_instruction(&mut statement.kind, &registers)
                    .expect("legal leaf has a complete non-receiver register map");
                block.statements.push(statement);
            }
            let mut edge_args =
                Vec::with_capacity(normal.args.len() + usize::from(result.is_some()));
            if let Some(mut value) = *returned {
                remap_operand(&mut value, &registers)
                    .expect("legal leaf return does not reference receiver r0");
                edge_args.push(value);
            }
            edge_args.extend(normal.args);
            block.terminator = Terminator::Goto(Edge {
                target: normal.target,
                args: edge_args,
            });
            caller.features = infer_feature_bits(caller);

            let original = originals[&candidate.caller];
            let cap = growth_factor * original + growth_slack;
            if inline_weight(caller) > cap {
                scratch.functions[caller_index] = old_caller;
                continue;
            }
            caller.invalid_analyses |= pass_contract(PassId::InlineByCost).invalidates;
            scratch_policy
                .depths
                .entry(candidate.caller)
                .and_modify(|depth| *depth = (*depth).max(next_depth));
            *scratch_policy
                .source_clones
                .entry(candidate.target)
                .or_default() += 1;
            scratch_policy.cloned_bodies_remaining -= 1;
            changed = true;
            changed_this_round = true;
        }
        if !changed_this_round {
            break;
        }
    }

    // Clone ownership-transparent multi-block CFGs after leaf saturation. A
    // separate loop keeps the proven leaf rewrite small and lets newly
    // simplified callers become candidates without mixing block- and
    // statement-level remapping.
    loop {
        let targets = scratch
            .functions
            .iter()
            .filter(|function| {
                inline_multiblock_legal(function, types) && inline_weight(function) <= threshold
            })
            .map(|function| function.declaration)
            .collect::<BTreeSet<_>>();
        let exit_survivors = scratch
            .functions
            .iter()
            .filter(|function| targets.contains(&function.declaration))
            .map(|function| {
                (
                    function.declaration,
                    inline_multiblock_exit_survivors(function, types)
                        .expect("inline-legal multi-block body has proven exits"),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut candidates = Vec::new();
        for caller in &scratch.functions {
            for block in &caller.blocks {
                let Terminator::Call {
                    function: target,
                    args,
                    normal,
                    ..
                } = &block.terminator
                else {
                    continue;
                };
                if *target != caller.declaration
                    && targets.contains(target)
                    && components.get(&caller.declaration) != components.get(target)
                    && args.iter().all(|argument| argument.mode == UseMode::Move)
                    && args
                        .iter()
                        .map(|argument| argument.register)
                        .collect::<BTreeSet<_>>()
                        .len()
                        == args.len()
                    && (exit_survivors[target].is_empty()
                        || inline_survivor_region_is_closed(caller, block.id, normal.target))
                {
                    candidates.push(InlineCandidate {
                        caller: caller.declaration,
                        block: block.id,
                        target: *target,
                    });
                }
            }
        }
        candidates.sort_unstable();
        let mut changed_this_round = false;
        for candidate in candidates {
            let Some(next_depth) =
                inline_candidate_depth(&scratch_policy.depths, candidate.target, depth_cap)
            else {
                continue;
            };
            if scratch_policy
                .source_clones
                .get(&candidate.target)
                .copied()
                .unwrap_or(0)
                >= source_clone_cap
                || scratch_policy.cloned_bodies_remaining == 0
            {
                continue;
            }
            let Some(target) = scratch
                .functions
                .iter()
                .find(|function| function.declaration == candidate.target)
                .cloned()
            else {
                continue;
            };
            let Some(caller_index) = scratch
                .functions
                .iter()
                .position(|function| function.declaration == candidate.caller)
            else {
                continue;
            };
            let Some(block_index) = scratch.functions[caller_index]
                .blocks
                .iter()
                .position(|block| block.id == candidate.block)
            else {
                continue;
            };
            let Terminator::Call {
                result,
                function,
                args,
                normal,
            } = scratch.functions[caller_index].blocks[block_index]
                .terminator
                .clone()
            else {
                continue;
            };
            if function != candidate.target
                || args.len() != target.params.len()
                || result.is_some() != (target.result != grandiose_vm::UNIT)
            {
                continue;
            }

            let added_work = 2_u64.saturating_mul(
                args.len() as u64
                    + target
                        .blocks
                        .iter()
                        .map(|block| block.statements.len() as u64 + 1)
                        .sum::<u64>(),
            );
            work = work.saturating_add(added_work);
            if work > budget {
                return (PassOutcome::BudgetExhausted, work);
            }

            let old_caller = scratch.functions[caller_index].clone();
            let caller = &mut scratch.functions[caller_index];
            let mut registers = vec![None; target.register_types.len()];
            for (old, ty) in target.register_types.iter().copied().enumerate().skip(1) {
                let new = caller.register_types.len() as Register;
                caller.register_types.push(ty);
                registers[old] = Some(new);
            }
            let Some(block_count) = u32::try_from(target.blocks.len()).ok() else {
                scratch.functions[caller_index] = old_caller;
                continue;
            };
            let caller_max_block = caller
                .blocks
                .iter()
                .map(|block| block.id)
                .max()
                .unwrap_or(0);
            if caller_max_block.checked_add(block_count).is_none() {
                scratch.functions[caller_index] = old_caller;
                continue;
            }
            let mut blocks = BTreeMap::new();
            for (offset, block) in target.blocks.iter().enumerate() {
                blocks.insert(block.id, caller_max_block + 1 + offset as u32);
            }
            let Some(&cloned_entry) = blocks.get(&target.entry) else {
                scratch.functions[caller_index] = old_caller;
                continue;
            };
            let Some(arenas) = append_inline_arenas(caller, &target, &registers, &blocks) else {
                scratch.functions[caller_index] = old_caller;
                continue;
            };

            let span = caller.blocks[block_index]
                .statements
                .last()
                .map(|statement| statement.span)
                .unwrap_or_default();
            for (index, argument) in args.into_iter().enumerate() {
                caller.blocks[block_index].statements.push(Instruction {
                    span,
                    kind: InstructionKind::Move {
                        dst: registers[index + 1].expect("callee ABI register was mapped"),
                        src: argument,
                    },
                });
            }
            caller.blocks[block_index].terminator = Terminator::Goto(Edge {
                target: cloned_entry,
                args: vec![],
            });

            let mut cloned = Vec::with_capacity(target.blocks.len());
            let mut remap_failed = false;
            for mut block in target.blocks.clone() {
                block.id = blocks[&block.id];
                for parameter in &mut block.params {
                    let Some(mapped) = remap_register(parameter.register, &registers) else {
                        remap_failed = true;
                        break;
                    };
                    parameter.register = mapped;
                }
                if remap_failed {
                    break;
                }
                for statement in &mut block.statements {
                    if remap_instruction(&mut statement.kind, &registers).is_none() {
                        remap_failed = true;
                        break;
                    }
                    if remap_cloned_control_identities(&mut statement.kind, &arenas, &blocks)
                        .is_none()
                    {
                        remap_failed = true;
                        break;
                    }
                }
                if remap_failed || remap_terminator(&mut block.terminator, &registers).is_none() {
                    remap_failed = true;
                    break;
                }
                if remap_cloned_terminator_identities(&mut block.terminator, &arenas).is_none() {
                    remap_failed = true;
                    break;
                }
                match block.terminator.clone() {
                    Terminator::Return { value } => {
                        let mut edge_args =
                            Vec::with_capacity(normal.args.len() + usize::from(value.is_some()));
                        if let Some(value) = value {
                            edge_args.push(value);
                        }
                        edge_args.extend(normal.args.clone());
                        block.terminator = Terminator::Goto(Edge {
                            target: normal.target,
                            args: edge_args,
                        });
                    }
                    _ => {
                        if remap_cloned_cfg_targets(&mut block.terminator, &blocks).is_none() {
                            remap_failed = true;
                            break;
                        }
                    }
                }
                cloned.push(block);
            }
            if remap_failed {
                scratch.functions[caller_index] = old_caller;
                continue;
            }
            caller.blocks.extend(cloned);
            caller.features = infer_feature_bits(caller);
            caller.invalid_analyses |= pass_contract(PassId::InlineByCost).invalidates;

            let original = originals[&candidate.caller];
            let cap = growth_factor * original + growth_slack;
            if inline_weight(caller) > cap {
                scratch.functions[caller_index] = old_caller;
                continue;
            }
            scratch_policy
                .depths
                .entry(candidate.caller)
                .and_modify(|depth| *depth = (*depth).max(next_depth));
            *scratch_policy
                .source_clones
                .entry(candidate.target)
                .or_default() += 1;
            scratch_policy.cloned_bodies_remaining -= 1;
            changed = true;
            changed_this_round = true;
        }
        if !changed_this_round {
            break;
        }
    }
    if changed {
        *program = scratch;
        *policy = scratch_policy;
        (PassOutcome::Changed, work)
    } else {
        (PassOutcome::Unchanged, work)
    }
}

fn run_transactional_pass(
    program: &mut Program,
    pass: PassId,
    types: &[Type],
    global_remaining: &mut u64,
) -> PassReport {
    // Direct custom-hook identity is distinct from structural destruction,
    // but cleanup simplification must still see those hooks recursively when
    // deciding whether an otherwise scalar-only container is observable.
    let direct_custom_drop_types = program
        .functions
        .iter()
        .flat_map(|function| &function.flow.locals)
        .filter_map(|fact| (fact.drop_glue == DropGlueKind::Custom).then_some(fact.ty))
        .collect::<BTreeSet<_>>();
    let mut outcome = PassOutcome::Unchanged;
    let mut total_work = 0_u64;
    // Tail formation is the final stack-safety opportunity after proof
    // erasure. Give every body its deterministic local cap instead of letting
    // earlier declarations consume a shared FIFO budget and make recursion
    // safety depend on declaration order.
    let fair_per_function_budget = pass == PassId::FormTailCallsAndHoist;
    for function in &mut program.functions {
        let local_limit = (100_000_u64).max(32 * body_size(function));
        let limit = if fair_per_function_budget {
            local_limit
        } else {
            local_limit.min(*global_remaining)
        };
        let invalidated_before = function.invalid_analyses;
        let (body_outcome, work) = match pass {
            PassId::NormalizeCfg => normalize_cfg(function, limit),
            PassId::SparseSimplify => sparse_simplify(function, types, limit),
            PassId::ScalarizeLocals => scalarize_locals(function, types, limit),
            PassId::SimplifyCleanup => {
                simplify_cleanup(function, types, &direct_custom_drop_types, limit)
            }
            PassId::GlobalSimplify => global_simplify_exact_callables(function, types, limit),
            PassId::SpecializeCleanup => specialize_cleanup(function, types, limit),
            PassId::EraseLoanProofsAndScalarizedReferences => erase_loan_proofs(function, limit),
            PassId::FormTailCallsAndHoist => {
                form_tail_calls_and_hoist(function, types, &direct_custom_drop_types, limit)
            }
            _ => (PassOutcome::SkippedUnavailable, 0),
        };
        if body_outcome == PassOutcome::Changed {
            // Passes may publish a narrower, mutation-specific mask. Fall
            // back to the conservative contract for older transformations.
            if function.invalid_analyses == invalidated_before {
                function.invalid_analyses |= pass_contract(pass).invalidates;
            }
        }
        total_work = total_work.saturating_add(work);
        if !fair_per_function_budget {
            *global_remaining = global_remaining.saturating_sub(work.min(*global_remaining));
        }
        outcome = match (outcome, body_outcome) {
            (_, PassOutcome::BudgetExhausted) => PassOutcome::BudgetExhausted,
            (PassOutcome::BudgetExhausted, _) => PassOutcome::BudgetExhausted,
            (_, PassOutcome::Changed) => PassOutcome::Changed,
            (PassOutcome::Changed, _) => PassOutcome::Changed,
            (_, PassOutcome::SkippedUnavailable) => PassOutcome::SkippedUnavailable,
            (current, PassOutcome::Unchanged) => current,
        };
        if !fair_per_function_budget && *global_remaining == 0 {
            outcome = PassOutcome::BudgetExhausted;
            break;
        }
    }
    PassReport {
        pass,
        outcome,
        work_units: total_work,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum InvalidationScope {
    ChangedBodies,
    WholeProgram,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PassContract {
    invalidates: u8,
    scope: InvalidationScope,
}

fn pass_contract(pass: PassId) -> PassContract {
    let changed = |invalidates| PassContract {
        invalidates,
        scope: InvalidationScope::ChangedBodies,
    };
    match pass {
        PassId::NormalizeCfg
        | PassId::SparseSimplify
        | PassId::SimplifyCleanup
        | PassId::GlobalSimplify
        | PassId::SpecializeDirectCalls
        | PassId::SpecializeCleanup
        | PassId::FormTailCallsAndHoist => changed(analysis::ALL),
        // These preserve the block graph while rewriting definitions and
        // ownership events, so existing CFG topology remains valid.
        PassId::ScalarizeLocals | PassId::EraseLoanProofsAndScalarizedReferences => changed(
            analysis::USES | analysis::FLOW | analysis::EFFECTS | analysis::VALUES | analysis::COST,
        ),
        // Callable scalarization and inlining mark each rewritten/new body as
        // they commit it. Handler specialization currently rewrites through a
        // whole-program scratch transaction, so it retains the conservative
        // program-wide checkpoint contract.
        PassId::ScalarizeCallables | PassId::InlineByCost => changed(analysis::ALL),
        PassId::SpecializeControl => PassContract {
            invalidates: analysis::ALL,
            scope: InvalidationScope::WholeProgram,
        },
        PassId::ValidateRawMir
        | PassId::ImportAndValidatePlaceFlow
        | PassId::ElaborateCleanup
        | PassId::ValidateCleanupMir
        | PassId::LowerRegistersAndEdges
        | PassId::LayoutAndPeephole
        | PassId::ValidateBytecodeInput
        | PassId::ValidateFinalArtifact => changed(0),
    }
}

#[derive(Clone, Copy)]
struct WholeProgramPassTables<'a> {
    types: &'a [Type],
    protocols: &'a [Protocol],
    handler_defs: &'a [HandlerDef],
}

fn run_transactional_whole_program_pass(
    program: &mut Program,
    pass: PassId,
    tables: WholeProgramPassTables<'_>,
    level: OptimizationLevel,
    global_remaining: &mut u64,
    inline_policy: &mut InlinePolicyState,
) -> PassReport {
    let (outcome, work_units) = match pass {
        PassId::SpecializeDirectCalls => specialize_forwarding_direct_calls(program, *global_remaining),
        PassId::ScalarizeCallables => scalarize_callables(program, tables.types, *global_remaining),
        PassId::SpecializeControl => specialize_static_handlers(
            program,
            tables.types,
            tables.protocols,
            tables.handler_defs,
            *global_remaining,
        ),
        PassId::InlineByCost => inline_by_cost_with_policy(
            program,
            tables.types,
            level,
            *global_remaining,
            inline_policy,
        ),
        _ => (PassOutcome::SkippedUnavailable, 0),
    };
    if outcome == PassOutcome::Changed {
        let contract = pass_contract(pass);
        match contract.scope {
            InvalidationScope::WholeProgram => {
                for function in &mut program.functions {
                    function.invalid_analyses |= contract.invalidates;
                }
            }
            InvalidationScope::ChangedBodies => {
                debug_assert!(
                    program
                        .functions
                        .iter()
                        .any(|function| function.invalid_analyses & contract.invalidates != 0),
                    "{pass:?} changed MIR without publishing its body invalidation"
                );
            }
        }
    }
    *global_remaining = global_remaining.saturating_sub(work_units.min(*global_remaining));
    PassReport {
        pass,
        outcome,
        work_units,
    }
}

fn run_mandatory_normalize(program: &mut Program) -> PassReport {
    let mut outcome = PassOutcome::Unchanged;
    let mut work_units = 0_u64;
    for function in &mut program.functions {
        let (body_outcome, work) = normalize_cfg(function, u64::MAX);
        work_units += work;
        if body_outcome == PassOutcome::Changed {
            function.invalid_analyses |= pass_contract(PassId::NormalizeCfg).invalidates;
            outcome = PassOutcome::Changed;
        }
    }
    PassReport {
        pass: PassId::NormalizeCfg,
        outcome,
        work_units,
    }
}

fn run_mandatory_loan_erasure(program: &mut Program) -> PassReport {
    let mut outcome = PassOutcome::Unchanged;
    let mut work_units = 0_u64;
    for function in &mut program.functions {
        let (body_outcome, work) = erase_loan_proofs(function, u64::MAX);
        work_units = work_units.saturating_add(work);
        if body_outcome == PassOutcome::Changed {
            function.invalid_analyses |=
                pass_contract(PassId::EraseLoanProofsAndScalarizedReferences).invalidates;
            outcome = PassOutcome::Changed;
        }
    }
    PassReport {
        pass: PassId::EraseLoanProofsAndScalarizedReferences,
        outcome,
        work_units,
    }
}

fn strict_flow(function: &Function) -> bool {
    function.flow.provenance == FlowProvenance::Exported
}

fn flow_to_validation(function: &Function, error: regions::FlowError) -> ValidationError {
    ValidationError {
        function: function.name.clone(),
        block: error.block,
        message: error.message,
    }
}

/// One local fact per register: the exported prefix where it agrees with the
/// register table, conservative temporary facts for the remainder. This is
/// the documented import bridge for registers allocated after export.
fn bridged_locals(function: &Function, types: &[Type]) -> Vec<LocalFact> {
    let mut locals = function.flow.locals.clone();
    locals.truncate(function.register_types.len());
    for (register, fact) in locals.iter_mut().enumerate() {
        let ty = function.register_types[register];
        if fact.ty != ty {
            *fact = LocalFact::conservative(ty, &types[ty as usize]);
        }
    }
    for &ty in &function.register_types[locals.len()..] {
        locals.push(LocalFact::conservative(ty, &types[ty as usize]));
    }
    locals
}

/// Derive the move-path tree from the instruction stream, deterministically
/// in block-ID/statement order.
fn derive_move_paths(function: &Function) -> MovePaths {
    let mut paths = MovePaths::default();
    let mut ordered = function.blocks.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|block| block.id);
    for block in ordered {
        for statement in &block.statements {
            let (base, field) = match &statement.kind {
                InstructionKind::ProjectMove { src, field, .. }
                | InstructionKind::ProjectCopy { src, field, .. } => (src.register, *field),
                InstructionKind::ProjectBorrow { src, field, .. } => (*src, *field),
                _ => continue,
            };
            let root = paths.root(base);
            paths.child(
                root,
                Projection::Field {
                    variant: None,
                    field,
                },
            );
        }
    }
    paths
}

/// Validate that the frontend-exported facts name the actual MIR locals,
/// loans, and control sites without loss. Mismatches are internal errors.
fn validate_exported_facts(function: &Function, types: &[Type]) -> Result<(), ValidationError> {
    if function.flow.locals.len() > function.register_types.len() {
        return Err(error(
            function,
            None,
            format!(
                "imported PlaceFlow exports {} local facts for {} registers",
                function.flow.locals.len(),
                function.register_types.len()
            ),
        ));
    }
    for (register, fact) in function.flow.locals.iter().enumerate() {
        let ty = function.register_types[register];
        if fact.ty != ty {
            return Err(error(
                function,
                None,
                format!(
                    "imported PlaceFlow local fact for r{register} names type t{}, but the register has type t{ty}",
                    fact.ty
                ),
            ));
        }
        if fact.ty as usize >= types.len() {
            return Err(error(
                function,
                None,
                format!("imported PlaceFlow local fact for r{register} is out of type range"),
            ));
        }
    }
    let mut instruction_loans = Vec::new();
    let mut ordered = function.blocks.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|block| block.id);
    for block in &ordered {
        for statement in &block.statements {
            match &statement.kind {
                InstructionKind::Borrow { dst, unique, .. }
                | InstructionKind::ProjectBorrow { dst, unique, .. }
                | InstructionKind::Reborrow { dst, unique, .. } => {
                    instruction_loans.push((*dst, *unique));
                }
                InstructionKind::Primitive {
                    dst,
                    primitive:
                        primitive @ (Primitive::ArrayGetBorrowShared | Primitive::ArrayGetBorrowUnique),
                    ..
                } => {
                    instruction_loans.push((*dst, *primitive == Primitive::ArrayGetBorrowUnique));
                }
                _ => {}
            }
        }
    }
    instruction_loans.sort_unstable();
    let mut fact_loans = function
        .flow
        .loans
        .iter()
        .map(|loan| {
            (
                loan.reference,
                loan.kind == crate::compiler_mir::LoanKind::Unique,
            )
        })
        .collect::<Vec<_>>();
    fact_loans.sort_unstable();
    if instruction_loans != fact_loans {
        return Err(error(
            function,
            None,
            format!(
                "imported PlaceFlow loan facts {fact_loans:?} do not match the borrow instructions {instruction_loans:?}"
            ),
        ));
    }
    let site_blocks = |predicate: fn(&Terminator) -> bool| {
        ordered
            .iter()
            .filter(|block| predicate(&block.terminator))
            .map(|block| block.id)
            .collect::<Vec<_>>()
    };
    let perform_blocks = site_blocks(|terminator| matches!(terminator, Terminator::Perform { .. }));
    let handle_blocks = site_blocks(|terminator| matches!(terminator, Terminator::Handle { .. }));
    let resume_blocks = site_blocks(|terminator| {
        matches!(
            terminator,
            Terminator::Resume { .. } | Terminator::TailResume { .. } | Terminator::Cancel { .. }
        )
    });
    let indirect_calls = ordered
        .iter()
        .filter_map(|block| match &block.terminator {
            Terminator::CallIndirect { callable, .. } => {
                let outward = match types
                    .get(function.register_types[callable.register as usize] as usize)
                    .map(Type::representation)
                {
                    Some(Type::Callable { signature, .. }) => signature.outward_protocols.clone(),
                    _ => return None,
                };
                Some((block.id, outward))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let fact_indirect_calls = function
        .flow
        .indirect_calls
        .iter()
        .map(|site| (site.block, site.outward_protocols.clone()))
        .collect::<Vec<_>>();
    if fact_indirect_calls != indirect_calls {
        return Err(error(
            function,
            None,
            format!(
                "imported PlaceFlow indirect-call sites {fact_indirect_calls:?} do not match callable terminators {indirect_calls:?}"
            ),
        ));
    }
    let mut incoming = BTreeMap::<u32, Vec<u32>>::new();
    for block in &ordered {
        for target in successors(&block.terminator) {
            incoming.entry(target).or_default().push(block.id);
        }
    }
    let actual_joins = incoming
        .into_iter()
        .filter_map(|(block, mut incoming)| {
            incoming.sort_unstable();
            incoming.dedup();
            (incoming.len() > 1).then_some((block, incoming))
        })
        .collect::<Vec<_>>();
    let fact_joins = function
        .flow
        .joins
        .iter()
        .map(|site| (site.block, site.incoming.clone()))
        .collect::<Vec<_>>();
    if fact_joins != actual_joins {
        return Err(error(
            function,
            None,
            format!(
                "imported PlaceFlow join sites {fact_joins:?} do not match CFG joins {actual_joins:?}"
            ),
        ));
    }
    let mut fact_performs = function
        .flow
        .performs
        .iter()
        .map(|site| site.block)
        .collect::<Vec<_>>();
    fact_performs.sort_unstable();
    let mut fact_handlers = function
        .flow
        .handlers
        .iter()
        .map(|site| site.block)
        .collect::<Vec<_>>();
    fact_handlers.sort_unstable();
    let mut fact_resumptions = function
        .flow
        .resumptions
        .iter()
        .map(|site| site.block)
        .collect::<Vec<_>>();
    fact_resumptions.sort_unstable();
    for (label, facts, actual) in [
        ("perform", fact_performs, perform_blocks),
        ("handler", fact_handlers, handle_blocks),
        ("resumption", fact_resumptions, resume_blocks),
    ] {
        if facts != actual {
            return Err(error(
                function,
                None,
                format!(
                    "imported PlaceFlow {label} sites {facts:?} do not match the terminators at {actual:?}"
                ),
            ));
        }
    }
    Ok(())
}

/// Rebuild the derived per-block site facts from the current terminators.
fn rebuild_site_facts(function: &mut Function) {
    let mut handlers = Vec::new();
    let mut performs = Vec::new();
    let mut resumptions = Vec::new();
    let mut incoming = BTreeMap::<u32, Vec<u32>>::new();
    let mut ordered = function.blocks.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|block| block.id);
    for block in &ordered {
        for target in successors(&block.terminator) {
            incoming.entry(target).or_default().push(block.id);
        }
        match &block.terminator {
            Terminator::Handle { .. } => handlers.push(HandlerSiteFact {
                block: block.id,
                scope: ScopeId(0),
            }),
            Terminator::Perform { resume, .. } => performs.push(PerformSiteFact {
                block: block.id,
                resumptive: resume.is_some(),
                frame_cleanup: None,
            }),
            Terminator::Resume { .. } | Terminator::TailResume { .. } => {
                resumptions.push(ResumptionSiteFact {
                    block: block.id,
                    cancel: false,
                    cancellation_cleanup: None,
                })
            }
            Terminator::Cancel { .. } => resumptions.push(ResumptionSiteFact {
                block: block.id,
                cancel: true,
                cancellation_cleanup: None,
            }),
            _ => {}
        }
    }
    let joins = incoming
        .into_iter()
        .filter_map(|(block, mut incoming)| {
            incoming.sort_unstable();
            incoming.dedup();
            (incoming.len() > 1).then_some(JoinSiteFact { block, incoming })
        })
        .collect();
    function.flow.handlers = handlers;
    function.flow.performs = performs;
    function.flow.resumptions = resumptions;
    function.flow.joins = joins;
}

/// The elaborated cleanup plans of one body plus their site attachments.
#[derive(Debug, Eq, PartialEq)]
struct CleanupElaboration {
    plans: Vec<CleanupPlanFact>,
    perform_plans: BTreeMap<u32, CleanupPlanId>,
    cancel_plans: BTreeMap<u32, CleanupPlanId>,
}

/// Classify one trailing destruction statement into a cleanup action using
/// the ownership state in force just before it executes.
fn cleanup_action(
    function: &Function,
    kind: &InstructionKind,
    state: &regions::OwnState,
) -> Option<CleanupAction> {
    match kind {
        InstructionKind::Drop { owner } => {
            let register = owner.register;
            Some(match &state.regs[register as usize] {
                regions::RegState::Partial(bitmap) => CleanupAction::DestroyResidual {
                    local: register,
                    initialized_fields: bitmap.clone(),
                },
                regions::RegState::MaybeLive => CleanupAction::DestroyIf {
                    local: register,
                    flag: function
                        .flow
                        .drop_flags
                        .iter()
                        .find(|fact| fact.owner == register && fact.field.is_none())
                        .map(|fact| fact.flag)
                        .unwrap_or(register),
                },
                _ => CleanupAction::Destroy(register),
            })
        }
        InstructionKind::EndBorrow { reference } => Some(CleanupAction::EndBorrow(LoanId(
            state
                .loans
                .get(reference)
                .map(|loan| loan.id)
                .unwrap_or(u32::MAX),
        ))),
        _ => None,
    }
}

/// Classify an owner abandoned implicitly by a nonlocal edge rather than by
/// an explicit trailing MIR statement.
fn abandoned_cleanup_action(
    function: &Function,
    state: &regions::OwnState,
    register: Register,
) -> CleanupAction {
    if let Some(loan) = state.loans.get(&register) {
        return CleanupAction::EndBorrow(LoanId(loan.id));
    }
    match &state.regs[register as usize] {
        regions::RegState::Partial(initialized_fields) => CleanupAction::DestroyResidual {
            local: register,
            initialized_fields: initialized_fields.clone(),
        },
        regions::RegState::MaybeLive => CleanupAction::DestroyIf {
            local: register,
            flag: function
                .flow
                .drop_flags
                .iter()
                .find(|fact| fact.owner == register && fact.field.is_none())
                .map(|fact| fact.flag)
                .unwrap_or(register),
        },
        regions::RegState::Undefined | regions::RegState::Live | regions::RegState::Consumed => {
            CleanupAction::Destroy(register)
        }
    }
}

fn implicit_abandonment_actions(
    function: &Function,
    state: &regions::OwnState,
    protected: &BTreeSet<Register>,
) -> Vec<CleanupAction> {
    state
        .order
        .iter()
        .rev()
        .copied()
        .filter(|register| {
            !protected.contains(register)
                && (*register != 0 || function.receiver_mode.is_some())
                && function
                    .flow
                    .locals
                    .get(*register as usize)
                    .is_none_or(|fact| fact.drop_glue != DropGlueKind::None)
        })
        .map(|register| abandoned_cleanup_action(function, state, register))
        .collect()
}

/// Compute the exact cleanup plans for every scope-exiting or abandoning
/// edge: normal return, tail call, terminal perform frame abandonment, and
/// continuation cancellation. Deterministic in block order.
#[cfg(test)]
fn derive_cleanup_elaboration(
    function: &Function,
    types: &[Type],
) -> Result<CleanupElaboration, ValidationError> {
    derive_cleanup_elaboration_with_array_calls(function, types, &BTreeMap::new())
}

fn derive_cleanup_elaboration_with_array_calls(
    function: &Function,
    types: &[Type],
    array_calls: &BTreeMap<u32, regions::ArrayCallSummary>,
) -> Result<CleanupElaboration, ValidationError> {
    let locals = bridged_locals(function, types);
    let context = regions::FlowContext {
        function,
        types,
        locals: &locals,
        loans: regions::loan_table(function, types),
        array_calls,
        strict: strict_flow(function),
        refine_enum_switches: true,
    };
    let solution = regions::solve(&context).map_err(|flow_error| {
        if std::env::var_os("GRANDIOSE_DEBUG_FLOW").is_some() {
            let program = Program {
                functions: vec![function.clone()],
            };
            eprintln!("{}", program.canonical_text());
        }
        flow_to_validation(function, flow_error)
    })?;
    let mut elaboration = CleanupElaboration {
        plans: Vec::new(),
        perform_plans: BTreeMap::new(),
        cancel_plans: BTreeMap::new(),
    };
    let mut ordered = function.blocks.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|block| block.id);
    for block in ordered {
        let Some(entry) = solution.entries.get(&block.id) else {
            // A generated terminal handler body can reach its terminal
            // perform only through a call-return edge that the conservative
            // ownership solver has classified as non-returning.  The
            // terminator's continuation capture is the exact lowering-time
            // ownership snapshot, so retain its abandonment plan rather than
            // silently losing residual-field cleanup with the missing entry.
            if let Terminator::Perform {
                resume: None,
                payloads,
                capture,
                ..
            } = &block.terminator
            {
                let protected = payloads
                    .iter()
                    .map(|operand| operand.register)
                    .collect::<BTreeSet<_>>();
                let actions = capture
                    .captured_owners
                    .iter()
                    .rev()
                    .copied()
                    .filter(|register| {
                        !protected.contains(register)
                            && function
                                .flow
                                .locals
                                .get(*register as usize)
                                .is_none_or(|fact| fact.drop_glue != DropGlueKind::None)
                    })
                    .map(|register| {
                        capture
                            .captured_residuals
                            .iter()
                            .find(|residual| residual.register == register)
                            .map_or(CleanupAction::Destroy(register), |residual| {
                                CleanupAction::DestroyResidual {
                                    local: register,
                                    initialized_fields: residual.initialized_fields.clone(),
                                }
                            })
                    })
                    .collect();
                let id = CleanupPlanId(elaboration.plans.len() as u32);
                elaboration.perform_plans.insert(block.id, id);
                elaboration.plans.push(CleanupPlanFact {
                    edge: CleanupEdge::TerminalPerform { block: block.id },
                    source_scope: ScopeId(0),
                    target_scope: ScopeId(0),
                    actions,
                    protected: protected.into_iter().collect(),
                });
            }
            // Other unreachable blocks have no ownership state and exit
            // nothing.
            continue;
        };
        let states = regions::block_states(&context, block, entry)
            .map_err(|error| flow_to_validation(function, error))?;
        let exit = states.last().expect("block states include the terminator");
        let (edge, protected, target_scope, implicit_actions) = match &block.terminator {
            Terminator::Return { value } => {
                let protected = value
                    .iter()
                    .map(|operand| operand.register)
                    .collect::<BTreeSet<_>>();
                (
                    CleanupEdge::Return { block: block.id },
                    protected.iter().copied().collect(),
                    ScopeId(0),
                    implicit_abandonment_actions(function, exit, &protected),
                )
            }
            Terminator::TailCall { args, .. } => {
                let protected = args
                    .iter()
                    .map(|operand| operand.register)
                    .collect::<BTreeSet<_>>();
                (
                    CleanupEdge::TailCall { block: block.id },
                    protected.iter().copied().collect(),
                    ScopeId(0),
                    implicit_abandonment_actions(function, exit, &protected),
                )
            }
            Terminator::TailResume {
                resumption,
                receiver_mode,
                value,
            } => {
                let protected = (*receiver_mode == 2)
                    .then_some(resumption.register)
                    .into_iter()
                    .chain(std::iter::once(value.register))
                    .collect::<BTreeSet<_>>();
                (
                    CleanupEdge::TailCall { block: block.id },
                    protected.iter().copied().collect(),
                    ScopeId(0),
                    implicit_abandonment_actions(function, exit, &protected),
                )
            }
            Terminator::TailCallSelf { args } => {
                let protected = std::iter::once(0)
                    .chain(args.iter().map(|operand| operand.register))
                    .collect::<BTreeSet<_>>();
                (
                    CleanupEdge::TailCall { block: block.id },
                    protected.iter().copied().collect(),
                    ScopeId(0),
                    implicit_abandonment_actions(function, exit, &protected),
                )
            }
            Terminator::TailCallKnownReceiver { args, .. } => {
                let protected = args
                    .iter()
                    .map(|operand| operand.register)
                    .collect::<BTreeSet<_>>();
                (
                    CleanupEdge::TailCall { block: block.id },
                    protected.iter().copied().collect(),
                    ScopeId(0),
                    implicit_abandonment_actions(function, exit, &protected),
                )
            }
            Terminator::TailCallIndirect {
                callable,
                receiver_mode,
                args,
                ..
            } => {
                let protected = (*receiver_mode == 2)
                    .then_some(callable.register)
                    .into_iter()
                    .chain(args.iter().map(|operand| operand.register))
                    .collect::<BTreeSet<_>>();
                (
                    CleanupEdge::TailCall { block: block.id },
                    protected.iter().copied().collect(),
                    ScopeId(0),
                    implicit_abandonment_actions(function, exit, &protected),
                )
            }
            Terminator::Leave { label, target } => {
                let label_fact = function.flow.labels.get(label.index()).ok_or_else(|| {
                    error(function, Some(block.id), "Leave label is out of range")
                })?;
                let label_entry = exit
                    .labels
                    .iter()
                    .rposition(|entry| entry.label == *label)
                    .map(|index| &exit.labels[index])
                    .ok_or_else(|| error(function, Some(block.id), "Leave label is not active"))?;
                let outer = label_entry.owners.iter().copied().collect::<BTreeSet<_>>();
                let protected = target
                    .args
                    .iter()
                    .map(|operand| operand.register)
                    .collect::<BTreeSet<_>>();
                let retained = outer.union(&protected).copied().collect::<BTreeSet<_>>();
                let implicit_actions = implicit_abandonment_actions(function, exit, &retained);
                (
                    CleanupEdge::Leave {
                        block: block.id,
                        label: *label,
                    },
                    protected.into_iter().collect(),
                    label_fact.scope,
                    implicit_actions,
                )
            }
            Terminator::Perform {
                resume: None,
                payloads,
                ..
            } => {
                let payload_registers = payloads
                    .iter()
                    .map(|operand| operand.register)
                    .collect::<BTreeSet<_>>();
                let mut actions = Vec::new();
                for register in exit.order.iter().rev() {
                    if payload_registers.contains(register) {
                        continue;
                    }
                    if *register == 0 && function.receiver_mode.is_none() {
                        continue;
                    }
                    if function
                        .flow
                        .locals
                        .get(*register as usize)
                        .is_some_and(|fact| fact.drop_glue == DropGlueKind::None)
                    {
                        continue;
                    }
                    actions.push(abandoned_cleanup_action(function, exit, *register));
                }
                let id = CleanupPlanId(elaboration.plans.len() as u32);
                elaboration.perform_plans.insert(block.id, id);
                elaboration.plans.push(CleanupPlanFact {
                    edge: CleanupEdge::TerminalPerform { block: block.id },
                    source_scope: ScopeId(0),
                    target_scope: ScopeId(0),
                    actions,
                    protected: payload_registers.into_iter().collect(),
                });
                continue;
            }
            Terminator::Cancel { resumption, .. } => {
                let id = CleanupPlanId(elaboration.plans.len() as u32);
                elaboration.cancel_plans.insert(block.id, id);
                elaboration.plans.push(CleanupPlanFact {
                    edge: CleanupEdge::Cancel { block: block.id },
                    source_scope: ScopeId(0),
                    target_scope: ScopeId(0),
                    actions: vec![CleanupAction::Destroy(resumption.register)],
                    protected: Vec::new(),
                });
                continue;
            }
            _ => continue,
        };
        let mut start = block.statements.len();
        while start > 0
            && matches!(
                block.statements[start - 1].kind,
                InstructionKind::Drop { .. } | InstructionKind::EndBorrow { .. }
            )
        {
            start -= 1;
        }
        let mut actions = (start..block.statements.len())
            .filter_map(|index| {
                cleanup_action(function, &block.statements[index].kind, &states[index])
            })
            .collect::<Vec<_>>();
        actions.extend(implicit_actions);
        elaboration.plans.push(CleanupPlanFact {
            edge,
            source_scope: ScopeId(0),
            target_scope,
            actions,
            protected,
        });
    }
    Ok(elaboration)
}

/// Apply one elaboration to a body; true when anything changed.
fn apply_cleanup_elaboration(function: &mut Function, elaboration: CleanupElaboration) -> bool {
    let mut changed = false;
    if function.flow.cleanup_plans != elaboration.plans {
        function.flow.cleanup_plans = elaboration.plans;
        changed = true;
    }
    for site in &mut function.flow.performs {
        let plan = (!site.resumptive)
            .then(|| elaboration.perform_plans.get(&site.block).copied())
            .flatten();
        if site.frame_cleanup != plan {
            site.frame_cleanup = plan;
            changed = true;
        }
    }
    for site in &mut function.flow.resumptions {
        let plan = site
            .cancel
            .then(|| elaboration.cancel_plans.get(&site.block).copied())
            .flatten();
        if site.cancellation_cleanup != plan {
            site.cancellation_cleanup = plan;
            changed = true;
        }
    }
    changed
}

/// `ImportAndValidatePlaceFlow`: validate the exported frontend facts against
/// the instruction stream, materialize bridged facts and move paths, and run
/// the ownership fixed point. Advances `Raw -> Owned`.
fn import_and_validate_place_flow(
    program: &mut Program,
    types: &[Type],
) -> Result<PassReport, ValidationError> {
    let mut work = 0_u64;
    let mut changed = false;
    let array_calls = regions::array_call_summaries(program, types);
    for function in &mut program.functions {
        work = work.saturating_add(body_size(function));
        if strict_flow(function) {
            validate_exported_facts(function, types)?;
        } else {
            // Synthesized-fact bodies have no exported sites; derive them.
            let before = (
                function.flow.handlers.clone(),
                function.flow.performs.clone(),
                function.flow.resumptions.clone(),
            );
            rebuild_site_facts(function);
            changed |= before
                != (
                    function.flow.handlers.clone(),
                    function.flow.performs.clone(),
                    function.flow.resumptions.clone(),
                );
        }
        let locals = bridged_locals(function, types);
        if locals != function.flow.locals {
            function.flow.locals = locals;
            changed = true;
        }
        let move_paths = derive_move_paths(function);
        if move_paths != function.flow.move_paths {
            function.flow.move_paths = move_paths;
            changed = true;
        }
        let context = regions::FlowContext {
            function,
            types,
            locals: &function.flow.locals,
            loans: regions::loan_table(function, types),
            array_calls: &array_calls,
            strict: strict_flow(function),
            refine_enum_switches: true,
        };
        regions::solve(&context).map_err(|error| {
            if std::env::var_os("GRANDIOSE_DEBUG_FLOW").is_some() {
                let program = Program {
                    functions: vec![function.clone()],
                };
                eprintln!("{}", program.canonical_text());
            }
            flow_to_validation(function, error)
        })?;
        function.phase = MirPhase::Owned;
        function.features = infer_feature_bits(function);
    }
    Ok(PassReport {
        pass: PassId::ImportAndValidatePlaceFlow,
        outcome: if changed {
            PassOutcome::Changed
        } else {
            PassOutcome::Unchanged
        },
        work_units: work,
    })
}

/// `ElaborateCleanup`: build the explicit cleanup plans for every abandoning
/// or scope-exiting edge and attach them to their sites. Advances
/// `Owned -> Cleanup`.
fn elaborate_cleanup(program: &mut Program, types: &[Type]) -> Result<PassReport, ValidationError> {
    let mut work = 0_u64;
    let mut changed = false;
    let array_calls = regions::array_call_summaries(program, types);
    for function in &mut program.functions {
        work = work.saturating_add(body_size(function));
        let elaboration =
            derive_cleanup_elaboration_with_array_calls(function, types, &array_calls)?;
        changed |= apply_cleanup_elaboration(function, elaboration);
        function.phase = MirPhase::Cleanup;
        function.features = infer_feature_bits(function);
    }
    Ok(PassReport {
        pass: PassId::ElaborateCleanup,
        outcome: if changed {
            PassOutcome::Changed
        } else {
            PassOutcome::Unchanged
        },
        work_units: work,
    })
}

/// The full `ValidateCleanupMir`/`ValidateOptimizedMir` flow contract: rerun
/// the ownership fixed point, require the recorded cleanup plans to match a
/// fresh elaboration exactly, and require protected values to survive their
/// own cleanup chains.
fn validate_flow_and_cleanup(program: &Program, types: &[Type]) -> Result<(), ValidationError> {
    let array_calls = regions::array_call_summaries(program, types);
    for function in &program.functions {
        let elaboration =
            derive_cleanup_elaboration_with_array_calls(function, types, &array_calls)?;
        if elaboration.plans != function.flow.cleanup_plans {
            return Err(error(
                function,
                None,
                "cleanup plans are stale: a pass mutated ownership-relevant MIR without \
                 re-elaborating its cleanup facts",
            ));
        }
        for site in &function.flow.performs {
            if !site.resumptive
                && site.frame_cleanup != elaboration.perform_plans.get(&site.block).copied()
            {
                return Err(error(
                    function,
                    Some(site.block),
                    "terminal perform site lacks its frame cleanup plan",
                ));
            }
        }
        for site in &function.flow.resumptions {
            if site.cancel
                && site.cancellation_cleanup != elaboration.cancel_plans.get(&site.block).copied()
            {
                return Err(error(
                    function,
                    Some(site.block),
                    "cancellation site lacks its cleanup plan",
                ));
            }
        }
        for plan in &function.flow.cleanup_plans {
            for action in &plan.actions {
                let destroyed = match action {
                    CleanupAction::Destroy(local)
                    | CleanupAction::DestroyResidual { local, .. }
                    | CleanupAction::DestroyIf { local, .. } => Some(*local),
                    CleanupAction::EndBorrow(_) => None,
                };
                if let Some(local) = destroyed
                    && plan.protected.contains(&local)
                {
                    return Err(error(
                        function,
                        None,
                        format!("cleanup plan destroys r{local}, which is protected on its edge"),
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Solve the ownership fixed point for one body and return, per block, the
/// cleanup list (live registers newest first) before each statement plus one
/// before the terminator. Used by bytecode emission to cross-validate the
/// serialized cleanup maps against MIR facts.
#[cfg(test)]
pub(crate) fn derive_cleanup_lists(
    function: &Function,
    types: &[Type],
) -> Result<BTreeMap<u32, Vec<Vec<Register>>>, ValidationError> {
    Ok(derive_cleanup_state_analysis(function, types)?.lists)
}

/// Turn an edge copy into a transfer when the original SSA register is not
/// independently live at the destination. MIR edges snapshot arguments into
/// temporaries before committing target parameters, so the final occurrence
/// of one dead source can consume it after any earlier copies have taken
/// their snapshots.
///
/// Keeping such an argument as `Copy` is semantically harmless in the
/// ownership fixed point, which discards conditional unrestricted aliases at
/// joins, but it is not a faithful physical lowering: the bytecode `COPY`
/// leaves an extra initialized source register that is absent from the
/// destination's cleanup state. Canonicalizing before emission makes the MIR
/// ownership facts and the verifier-visible transfer agree.
pub(crate) fn canonicalize_dead_edge_copies_for_emission(
    program: &mut Program,
    types: &[Type],
) -> Result<u64, ValidationError> {
    let mir_snapshot_path = std::env::var_os("G1_PRE_EDGE_MIR");
    if let Some(path) = &mir_snapshot_path {
        std::fs::write(&path, program.canonical_text()).map_err(|write_error| ValidationError {
            function: "<program>".into(),
            block: None,
            message: format!(
                "could not write pre-edge MIR snapshot `{}`: {write_error}",
                std::path::Path::new(&path).display()
            ),
        })?;
    }
    let mut changed = 0_u64;
    for function in &mut program.functions {
        let changed_before = changed;
        let trace_edge_copies = std::env::var_os("G1_EDGE_COPY_TRACE")
            .is_some_and(|filter| function.name.contains(&filter.to_string_lossy().as_ref()));
        let trace_register = std::env::var("G1_EDGE_COPY_REGISTER")
            .ok()
            .and_then(|register| register.parse::<Register>().ok());
        // This is ordinary backwards liveness, independent of the current
        // edge transfer modes. In particular, a Copy argument cannot make its
        // own source appear live at the destination and thereby defeat
        // final-use transfer inference.
        let liveness = EdgeLiveness::compute(function, u64::MAX)
            .map_err(|analysis| error(function, None, analysis.to_string()))?;
        let params_by_block = function
            .blocks
            .iter()
            .map(|block| (block.id, block.params.clone()))
            .collect::<BTreeMap<_, _>>();
        for block in &mut function.blocks {
            for_each_edge_with_implicit_mut(&mut block.terminator, |edge, implicit| {
                let independently_live = liveness
                    .live_in(super::BlockId(edge.target))
                    .cloned()
                    .unwrap_or_default();
                let overwritten = params_by_block
                    .get(&edge.target)
                    .into_iter()
                    .flat_map(|params| params.iter().skip(implicit))
                    .map(|parameter| parameter.register)
                    .collect::<BTreeSet<_>>();
                let already_moved = edge
                    .args
                    .iter()
                    .filter(|argument| argument.mode == UseMode::Move)
                    .map(|argument| argument.register)
                    .collect::<BTreeSet<_>>();
                let mut final_dead_copy = BTreeMap::<Register, usize>::new();
                for (index, argument) in edge.args.iter().enumerate() {
                    if argument.mode == UseMode::Copy
                        && !already_moved.contains(&argument.register)
                        && (!independently_live.contains(&argument.register)
                            || overwritten.contains(&argument.register))
                    {
                        final_dead_copy.insert(argument.register, index);
                    }
                }
                for index in final_dead_copy.into_values() {
                    let argument = edge.args[index];
                    if trace_edge_copies
                        && trace_register.is_none_or(|register| register == argument.register)
                    {
                        eprintln!(
                            "edge-copy canonicalization (liveness): {} b{} -> b{} r{}: live={}, overwritten={}",
                            function.name,
                            block.id,
                            edge.target,
                            argument.register,
                            independently_live.contains(&argument.register),
                            overwritten.contains(&argument.register),
                        );
                    }
                    edge.args[index].mode = UseMode::Move;
                    changed += 1;
                }
            });
        }
        if changed != changed_before {
            function.invalid_analyses |= analysis::ALL;
        }
    }

    // Re-solve after transfer canonicalization, then materialize the other
    // half of physical join normalization: unrestricted ambient owners which
    // exist on only one ordinary or switch predecessor and are not carried by
    // an edge.
    // Keeping this as an ordinary MIR cleanup block means every later phase,
    // including move-path and loan verification, observes the retirement.
    let cleanup_lists = derive_program_serialization_cleanup_lists(program, types)?;
    for (function, lists) in program.functions.iter_mut().zip(cleanup_lists) {
        let function_name = function.name.clone();
        let trace_edge_copies = std::env::var_os("G1_EDGE_COPY_TRACE")
            .is_some_and(|filter| function_name.contains(filter.to_string_lossy().as_ref()));
        let trace_register = std::env::var("G1_EDGE_COPY_REGISTER")
            .ok()
            .and_then(|register| register.parse::<Register>().ok());
        // Cleanup states are path-sensitive ownership facts, whereas emitted
        // bytecode must remain valid along every structurally reachable
        // successor. A conditionally present handle can therefore be absent
        // from the merged cleanup state while still having a later use on
        // the path which introduced it. Recompute structural liveness after
        // the first transfer rewrite and never let cleanup reconciliation
        // consume such a handle.
        let liveness = EdgeLiveness::compute(function, u64::MAX)
            .map_err(|analysis| error(function, None, analysis.to_string()))?;
        let mut next_block = function
            .blocks
            .iter()
            .map(|block| block.id)
            .max()
            .unwrap_or(0)
            .saturating_add(1);
        let mut cleanup_blocks = Vec::new();
        let ownerships = function
            .flow
            .locals
            .iter()
            .map(|fact| fact.ownership)
            .collect::<Vec<_>>();
        let cfg = ControlFlowAnalysis::compute(function, u64::MAX)
            .map_err(|analysis| error(function, None, analysis.to_string()))?;
        let uses = register_uses(function);
        let mut edge_uses = vec![0_u32; function.register_types.len()];
        let mut end_blocks = vec![Vec::<super::BlockId>::new(); function.register_types.len()];
        for block in &function.blocks {
            for statement in &block.statements {
                if let InstructionKind::EndBorrow { reference } = statement.kind {
                    end_blocks[reference as usize].push(super::BlockId(block.id));
                }
            }
            for_each_edge_with_implicit(&block.terminator, |edge, _| {
                for argument in &edge.args {
                    edge_uses[argument.register as usize] =
                        edge_uses[argument.register as usize].saturating_add(1);
                }
            });
        }
        let cleanup_references = function
            .flow
            .cleanup_plans
            .iter()
            .flat_map(|plan| &plan.actions)
            .filter_map(|action| match action {
                CleanupAction::EndBorrow(loan) => function
                    .flow
                    .loans
                    .get(loan.index())
                    .map(|loan| loan.reference),
                _ => None,
            })
            .chain(function.return_cleanup.iter().copied())
            .collect::<BTreeSet<_>>();
        // A predecessor-local shared handle whose sole dynamic transport is
        // one edge and whose remaining uses are proof-only EndBorrow markers
        // can be transferred into the join parameter. Keeping both aliases
        // would make the old handle conditionally initialized after a merge;
        // bytecode state is intentionally structural and does not retain the
        // predecessor/tag correlation needed to validate that hole.
        let transferable_proof_aliases = uses
            .iter()
            .enumerate()
            .filter_map(|(register, &use_count)| {
                let end_count = end_blocks[register].len() as u32;
                (ownerships.get(register) == Some(&OwnershipCategory::SharedRef)
                    && edge_uses[register] == 1
                    && end_count != 0
                    && use_count == edge_uses[register].saturating_add(end_count)
                    && !cleanup_references.contains(&(register as Register)))
                .then_some(register as Register)
            })
            .collect::<BTreeSet<_>>();
        let mut transferred_proof_aliases = BTreeSet::<Register>::new();
        let params_by_block = function
            .blocks
            .iter()
            .map(|block| (block.id, block.params.clone()))
            .collect::<BTreeMap<_, _>>();
        for block in &mut function.blocks {
            let Some(source) = lists.get(&block.id).and_then(|points| points.last()) else {
                continue;
            };
            let block_id = block.id;
            let mut reconcile = |edge: &mut Edge| -> Result<(), ValidationError> {
                let Some(destination) = lists.get(&edge.target).and_then(|points| points.first())
                else {
                    return Ok(());
                };
                let destination = destination.iter().copied().collect::<BTreeSet<_>>();
                let structurally_live = liveness
                    .live_in(super::BlockId(edge.target))
                    .cloned()
                    .unwrap_or_default();
                let overwritten = params_by_block
                    .get(&edge.target)
                    .into_iter()
                    .flatten()
                    .map(|parameter| parameter.register)
                    .collect::<BTreeSet<_>>();
                let already_moved = edge
                    .args
                    .iter()
                    .filter(|argument| argument.mode == UseMode::Move)
                    .map(|argument| argument.register)
                    .collect::<BTreeSet<_>>();
                let mut final_dead_copy = BTreeMap::<Register, usize>::new();
                for (index, argument) in edge.args.iter().enumerate() {
                    let transferable_proof_alias = transferable_proof_aliases
                        .contains(&argument.register)
                        && end_blocks[argument.register as usize]
                            .iter()
                            .all(|block| cfg.dominates(super::BlockId(edge.target), *block));
                    if argument.mode == UseMode::Copy
                        && !already_moved.contains(&argument.register)
                        && (overwritten.contains(&argument.register)
                            || (!destination.contains(&argument.register)
                                && (!structurally_live.contains(&argument.register)
                                    || transferable_proof_alias)))
                    {
                        final_dead_copy.insert(argument.register, index);
                    }
                }
                for index in final_dead_copy.into_values() {
                    let argument = edge.args[index];
                    if trace_edge_copies
                        && trace_register.is_none_or(|register| register == argument.register)
                    {
                        eprintln!(
                            "edge-copy canonicalization (cleanup): {} b{} -> b{} r{}: live={}, destination={}, overwritten={}",
                            function_name,
                            block_id,
                            edge.target,
                            argument.register,
                            structurally_live.contains(&argument.register),
                            destination.contains(&argument.register),
                            overwritten.contains(&argument.register),
                        );
                    }
                    edge.args[index].mode = UseMode::Move;
                    if transferable_proof_aliases.contains(&argument.register) {
                        transferred_proof_aliases.insert(argument.register);
                    }
                    changed += 1;
                }
                // Cleanup executes before the forwarded edge. Every operand
                // must remain initialized until the edge snapshots it. A
                // dead copied source was converted to a final Move above;
                // any remaining Copy is independently live at the target and
                // therefore cannot be retired in this predecessor block.
                let carried = edge
                    .args
                    .iter()
                    .map(|argument| argument.register)
                    .collect::<BTreeSet<_>>();
                let retire = source
                    .iter()
                    .copied()
                    .filter(|register| {
                        (!destination.contains(register) || overwritten.contains(register))
                            && !carried.contains(register)
                    })
                    .filter(|register| {
                        ownerships.get(*register as usize).is_some_and(|ownership| {
                            matches!(
                                ownership,
                                OwnershipCategory::SharedRef
                                    | OwnershipCategory::CopyValue
                                    | OwnershipCategory::ZstErased
                            )
                        })
                    })
                    .collect::<Vec<_>>();
                if retire.is_empty() {
                    return Ok(());
                }
                let original = edge.clone();
                let cleanup = next_block;
                next_block = next_block.checked_add(1).ok_or_else(|| ValidationError {
                    function: function_name.clone(),
                    block: Some(block_id),
                    message: "MIR block space exhausted".into(),
                })?;
                edge.target = cleanup;
                edge.args.clear();
                let statements = retire
                    .into_iter()
                    .map(|register| Instruction {
                        span: Span::default(),
                        kind: match ownerships[register as usize] {
                            OwnershipCategory::SharedRef => InstructionKind::EndBorrow {
                                reference: register,
                            },
                            OwnershipCategory::CopyValue | OwnershipCategory::ZstErased => {
                                InstructionKind::Drop {
                                    owner: Operand {
                                        register,
                                        mode: UseMode::Move,
                                    },
                                }
                            }
                            OwnershipCategory::Owned | OwnershipCategory::UniqueRef => {
                                unreachable!("restricted owners are never normalized at joins")
                            }
                        },
                    })
                    .collect();
                cleanup_blocks.push(BasicBlock {
                    id: cleanup,
                    params: Vec::new(),
                    statements,
                    terminator: Terminator::Goto(original),
                });
                changed += 1;
                Ok(())
            };
            match &mut block.terminator {
                Terminator::Goto(edge) => reconcile(edge)?,
                Terminator::Switch {
                    cases, otherwise, ..
                } => {
                    for (_, edge) in cases {
                        reconcile(edge)?;
                    }
                    reconcile(otherwise)?;
                }
                _ => {}
            }

            // A normal call/control edge may define an implicit result
            // parameter. Forward every destination parameter through fresh
            // cleanup-block parameters, retire predecessor-only ambient
            // owners after the operation, then move the forwarded values into
            // the original destination.
            let mut consumed = BTreeSet::new();
            block.terminator.for_each_register_use(|register, kind| {
                if kind == RegisterUseKind::Consume {
                    consumed.insert(register);
                }
            });
            let normal = match &mut block.terminator {
                Terminator::Call { normal, .. }
                | Terminator::CallSelf { normal, .. }
                | Terminator::CallKnownReceiver { normal, .. }
                | Terminator::HostCall { normal, .. }
                | Terminator::CallIndirect { normal, .. }
                | Terminator::Handle { normal, .. }
                | Terminator::Resume { normal, .. }
                | Terminator::Cancel { normal, .. } => Some(normal),
                Terminator::Perform {
                    resume: Some(resume),
                    ..
                } => Some(resume),
                _ => None,
            };
            if let Some(normal) = normal
                && let Some(destination) =
                    lists.get(&normal.target).and_then(|points| points.first())
            {
                let destination = destination.iter().copied().collect::<BTreeSet<_>>();
                let retire = source
                    .iter()
                    .copied()
                    .filter(|register| {
                        !destination.contains(register) && !consumed.contains(register)
                    })
                    .filter(|register| {
                        ownerships.get(*register as usize).is_some_and(|ownership| {
                            matches!(
                                ownership,
                                OwnershipCategory::SharedRef
                                    | OwnershipCategory::CopyValue
                                    | OwnershipCategory::ZstErased
                            )
                        })
                    })
                    .collect::<Vec<_>>();
                if !retire.is_empty() {
                    let original = normal.clone();
                    let target_params =
                        params_by_block
                            .get(&original.target)
                            .ok_or_else(|| ValidationError {
                                function: function_name.clone(),
                                block: Some(block_id),
                                message: format!(
                                    "normal edge targets missing block {}",
                                    original.target
                                ),
                            })?;
                    let cleanup = next_block;
                    next_block = next_block.checked_add(1).ok_or_else(|| ValidationError {
                        function: function_name.clone(),
                        block: Some(block_id),
                        message: "MIR block space exhausted".into(),
                    })?;
                    let mut forwarded_params = Vec::with_capacity(target_params.len());
                    let mut forwarded_args = Vec::with_capacity(target_params.len());
                    for parameter in target_params {
                        let register = function.register_types.len() as Register;
                        function.register_types.push(parameter.ty);
                        forwarded_params.push(BlockParam {
                            register,
                            ty: parameter.ty,
                            role: parameter.role,
                        });
                        forwarded_args.push(Operand {
                            register,
                            mode: UseMode::Move,
                        });
                    }
                    normal.target = cleanup;
                    let statements = retire
                        .into_iter()
                        .map(|register| Instruction {
                            span: Span::default(),
                            kind: match ownerships[register as usize] {
                                OwnershipCategory::SharedRef => InstructionKind::EndBorrow {
                                    reference: register,
                                },
                                OwnershipCategory::CopyValue | OwnershipCategory::ZstErased => {
                                    InstructionKind::Drop {
                                        owner: Operand {
                                            register,
                                            mode: UseMode::Move,
                                        },
                                    }
                                }
                                OwnershipCategory::Owned | OwnershipCategory::UniqueRef => {
                                    unreachable!("restricted owners are never normalized at joins")
                                }
                            },
                        })
                        .collect();
                    cleanup_blocks.push(BasicBlock {
                        id: cleanup,
                        params: forwarded_params,
                        statements,
                        terminator: Terminator::Goto(Edge {
                            target: original.target,
                            args: forwarded_args,
                        }),
                    });
                    changed += 1;
                    function.invalid_analyses |= analysis::ALL;
                }
            }
        }
        if !transferred_proof_aliases.is_empty() {
            for block in &mut function.blocks {
                let before = block.statements.len();
                block.statements.retain(|statement| {
                    !matches!(
                        statement.kind,
                        InstructionKind::EndBorrow { reference }
                            if transferred_proof_aliases.contains(&reference)
                    )
                });
                changed += (before - block.statements.len()) as u64;
            }
            function.invalid_analyses |= analysis::ALL;
        }
        if !cleanup_blocks.is_empty() {
            function.blocks.extend(cleanup_blocks);
            function.invalid_analyses |= analysis::ALL;
        }
    }
    refresh_invalidated_flow(program, types)?;
    // No emission-only assumption bypasses the ordinary ownership, loan, or
    // physical-switch checks.
    derive_program_serialization_cleanup_lists(program, types)?;
    if let Some(path) = mir_snapshot_path {
        let mut post_path = path;
        post_path.push(".post");
        std::fs::write(&post_path, program.canonical_text()).map_err(|write_error| {
            ValidationError {
                function: "<program>".into(),
                block: None,
                message: format!(
                    "could not write post-edge MIR snapshot `{}`: {write_error}",
                    std::path::Path::new(&post_path).display()
                ),
            }
        })?;
    }
    Ok(changed)
}

/// Derive physical cleanup states for final bytecode serialization. Semantic
/// ownership validation may prune a statically impossible enum-switch arm;
/// the bytecode verifier still structurally checks that encoded target, so
/// serialization follows every arm without applying tag refinement.
pub(crate) fn derive_program_serialization_cleanup_lists(
    program: &Program,
    types: &[Type],
) -> Result<Vec<BTreeMap<u32, Vec<Vec<Register>>>>, ValidationError> {
    let array_calls = regions::array_call_summaries(program, types);
    program
        .functions
        .iter()
        .map(|function| {
            let locals = bridged_locals(function, types);
            let context = regions::FlowContext {
                function,
                types,
                locals: &locals,
                loans: regions::loan_table(function, types),
                array_calls: &array_calls,
                strict: strict_flow(function),
                refine_enum_switches: false,
            };
            Ok(regions::solve(&context)
                .map_err(|error| flow_to_validation(function, error))?
                .cleanup_lists)
        })
        .collect()
}

struct CleanupStateAnalysis {
    lists: BTreeMap<u32, Vec<Vec<Register>>>,
    /// Blocks reached by the ownership interpreter after enum/tag and other
    /// path refinements. Structural CFG reachability intentionally
    /// over-approximates this set for compiled pattern decision trees.
    reachable: BTreeSet<u32>,
}

#[cfg(test)]
fn derive_cleanup_state_analysis(
    function: &Function,
    types: &[Type],
) -> Result<CleanupStateAnalysis, ValidationError> {
    derive_cleanup_state_analysis_with_array_calls(function, types, &BTreeMap::new())
}

fn derive_cleanup_state_analysis_with_array_calls(
    function: &Function,
    types: &[Type],
    array_calls: &BTreeMap<u32, regions::ArrayCallSummary>,
) -> Result<CleanupStateAnalysis, ValidationError> {
    let locals = bridged_locals(function, types);
    let context = regions::FlowContext {
        function,
        types,
        locals: &locals,
        loans: regions::loan_table(function, types),
        array_calls,
        strict: strict_flow(function),
        refine_enum_switches: true,
    };
    let solution = regions::solve(&context).map_err(|error| flow_to_validation(function, error))?;
    let reachable = solution.entries.keys().copied().collect();
    Ok(CleanupStateAnalysis {
        lists: solution.cleanup_lists,
        reachable,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LeaveCleanupBoundary {
    source: Vec<Register>,
    target: Vec<Register>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LeaveCleanupAnchors {
    pub(crate) source: Vec<Register>,
    pub(crate) target: Vec<Register>,
}

/// Infer `LEAVE` cleanup boundaries solely from MIR ownership states. Public
/// labels therefore do not need compiler-seeded bytecode cleanup anchors to
/// establish the source/target relationship: after protected transfer values
/// are removed, the target owner order must be a suffix of the source order.
fn derive_leave_cleanup_boundaries(
    function: &Function,
    lists: &BTreeMap<u32, Vec<Vec<Register>>>,
) -> Result<BTreeMap<u32, LeaveCleanupBoundary>, ValidationError> {
    let mut result = BTreeMap::new();
    for block in &function.blocks {
        let Terminator::Leave { target, .. } = &block.terminator else {
            continue;
        };
        let (Some(source_points), Some(target_points)) =
            (lists.get(&block.id), lists.get(&target.target))
        else {
            continue;
        };
        let protected_sources = target
            .args
            .iter()
            .filter(|operand| operand.mode == UseMode::Move)
            .map(|operand| operand.register)
            .collect::<BTreeSet<_>>();
        let target_block = function
            .blocks
            .iter()
            .find(|candidate| candidate.id == target.target)
            .ok_or_else(|| error(function, Some(block.id), "Leave target block is missing"))?;
        // Every moved LEAVE argument is atomically transferred to the matching
        // destination parameter before cleanup. A copied argument also
        // initializes its parameter, but its source identity remains live
        // and therefore still belongs to the cleanup suffix.
        let protected_targets = target_block
            .params
            .iter()
            .map(|parameter| parameter.register)
            .collect::<BTreeSet<_>>();
        let mut source = source_points
            .last()
            .into_iter()
            .flatten()
            .filter(|register| !protected_sources.contains(register))
            .copied()
            .collect::<Vec<_>>();
        let target = target_points
            .first()
            .into_iter()
            .flatten()
            .filter(|register| !protected_targets.contains(register))
            .copied()
            .collect::<Vec<_>>();
        if !source.ends_with(&target) {
            let target_set = target.iter().copied().collect::<BTreeSet<_>>();
            let target_is_copy_only = target.iter().all(|register| {
                function
                    .flow
                    .locals
                    .get(*register as usize)
                    .is_some_and(|fact| {
                        matches!(
                            fact.ownership,
                            OwnershipCategory::CopyValue | OwnershipCategory::ZstErased
                        ) && fact.drop_glue != DropGlueKind::Custom
                    })
            });
            let target_is_commutable = target.iter().all(|register| {
                function
                    .flow
                    .locals
                    .get(*register as usize)
                    .is_some_and(|fact| {
                        matches!(
                            fact.ownership,
                            OwnershipCategory::CopyValue
                                | OwnershipCategory::ZstErased
                                | OwnershipCategory::SharedRef
                        ) && fact.drop_glue != DropGlueKind::Custom
                    })
            });
            let reordered = source
                .iter()
                .enumerate()
                .filter(|(_, register)| target.first() == Some(register))
                .filter_map(|(start, _)| {
                    let candidate = &source[start..];
                    let retained = candidate
                        .iter()
                        .filter(|register| target_set.contains(register))
                        .copied()
                        .collect::<Vec<_>>();
                    if retained != target
                        || !candidate.iter().all(|register| {
                            target_set.contains(register)
                                || function.flow.locals.get(*register as usize).is_some_and(
                                    |fact| {
                                        (matches!(
                                            fact.ownership,
                                            OwnershipCategory::CopyValue
                                                | OwnershipCategory::ZstErased
                                        ) || (target_is_commutable
                                            && fact.ownership == OwnershipCategory::SharedRef)
                                            || (target_is_copy_only
                                                && matches!(
                                                    fact.ownership,
                                                    OwnershipCategory::UniqueRef
                                                )))
                                            && fact.drop_glue != DropGlueKind::Custom
                                    },
                                )
                        })
                    {
                        return None;
                    }
                    let mut reordered = source[..start].to_vec();
                    reordered.extend(
                        candidate
                            .iter()
                            .filter(|register| !target_set.contains(register))
                            .copied(),
                    );
                    reordered.extend(target.iter().copied());
                    Some(reordered)
                })
                .next();
            let Some(reordered) = reordered else {
                if std::env::var_os("GRANDIOSE_DEBUG_FLOW").is_some() {
                    let program = Program {
                        functions: vec![function.clone()],
                    };
                    eprintln!("{}", program.canonical_text());
                }
                return Err(error(
                    function,
                    Some(block.id),
                    format!(
                        "Leave cleanup target {target:?} is not a suffix of source {source:?} after protected transfer"
                    ),
                ));
            };
            source = reordered;
        }
        result.insert(block.id, LeaveCleanupBoundary { source, target });
    }
    Ok(result)
}

/// Produce the exact bytecode cleanup lists for each public `LEAVE` source and
/// destination after proving the normalized MIR owner suffix relation. The
/// VM atomically transfers the protected value before running the cleanup
/// prefix, so the source anchor substitutes the destination protected slot for
/// the moved source identity. This makes the serialized source and target
/// suffixes describe the post-transfer frame exactly.
pub(crate) fn derive_leave_cleanup_anchors(
    function: &Function,
    lists: &BTreeMap<u32, Vec<Vec<Register>>>,
) -> Result<BTreeMap<u32, LeaveCleanupAnchors>, ValidationError> {
    let boundaries = derive_leave_cleanup_boundaries(function, lists)?;
    let mut result = BTreeMap::new();
    for block in &function.blocks {
        let Terminator::Leave { target, .. } = &block.terminator else {
            continue;
        };
        let (Some(source_points), Some(target_points)) =
            (lists.get(&block.id), lists.get(&target.target))
        else {
            continue;
        };
        let destination = target_points.first().cloned().unwrap_or_default();
        let boundary = &boundaries[&block.id];
        debug_assert_eq!(
            destination
                .iter()
                .copied()
                .filter(|register| boundary.target.contains(register))
                .collect::<Vec<_>>(),
            boundary.target,
        );
        let destination_registers = destination.iter().copied().collect::<BTreeSet<_>>();
        let transferred_sources = target
            .args
            .iter()
            .filter(|argument| argument.mode == UseMode::Move)
            .map(|argument| argument.register)
            .collect::<BTreeSet<_>>();
        let mut source = source_points
            .last()
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .filter(|register| {
                !destination_registers.contains(register) && !transferred_sources.contains(register)
            })
            .collect::<Vec<_>>();
        source.extend(destination.iter().copied());
        result.insert(
            block.id,
            LeaveCleanupAnchors {
                source,
                target: destination,
            },
        );
    }
    Ok(result)
}

/// Distinct optimized-MIR checkpoint immediately before representation
/// lowering. It revalidates structural MIR and cleanup elaboration, derives the
/// exact owner list at every statement/terminator point, proves every recorded
/// destruction refers to a live source-block owner, validates conditional-drop
/// evidence, and infers every public `LEAVE` boundary from MIR alone.
fn validate_bytecode_input_checkpoint(
    program: &Program,
    types: &[Type],
) -> Result<PassReport, ValidationError> {
    validate_program(program, types, MirPhase::Optimized)?;
    validate_flow_and_cleanup(program, types)?;
    let array_calls = regions::array_call_summaries(program, types);
    let mut work = 0_u64;
    for function in &program.functions {
        let cleanup =
            derive_cleanup_state_analysis_with_array_calls(function, types, &array_calls)?;
        let lists = &cleanup.lists;
        for block in &function.blocks {
            let Some(points) = lists.get(&block.id) else {
                if !cleanup.reachable.contains(&block.id) {
                    continue;
                }
                return Err(error(
                    function,
                    Some(block.id),
                    "bytecode-input validation lacks MIR-derived cleanup states",
                ));
            };
            if points.len() != block.statements.len() + 1 {
                return Err(error(
                    function,
                    Some(block.id),
                    format!(
                        "MIR-derived cleanup states have {} points, expected {}",
                        points.len(),
                        block.statements.len() + 1
                    ),
                ));
            }
            for point in points {
                work = work.saturating_add(point.len() as u64 + 1);
                let mut unique = BTreeSet::new();
                for &register in point {
                    if register as usize >= function.register_types.len() {
                        return Err(error(
                            function,
                            Some(block.id),
                            format!("cleanup state references out-of-range register r{register}"),
                        ));
                    }
                    if !unique.insert(register) {
                        return Err(error(
                            function,
                            Some(block.id),
                            format!("cleanup state contains duplicate owner r{register}"),
                        ));
                    }
                }
            }
        }
        for plan in &function.flow.cleanup_plans {
            let source_block = match plan.edge {
                CleanupEdge::Return { block }
                | CleanupEdge::TailCall { block }
                | CleanupEdge::TerminalPerform { block }
                | CleanupEdge::Cancel { block }
                | CleanupEdge::Leave { block, .. } => block,
            };
            let Some(points) = lists.get(&source_block) else {
                if !cleanup.reachable.contains(&source_block) {
                    continue;
                }
                return Err(error(
                    function,
                    Some(source_block),
                    "cleanup plan source lacks MIR-derived ownership states",
                ));
            };
            let mut destroyed = BTreeSet::new();
            for action in &plan.actions {
                work = work.saturating_add(1);
                let local = match action {
                    CleanupAction::Destroy(local)
                    | CleanupAction::DestroyResidual { local, .. }
                    | CleanupAction::DestroyIf { local, .. } => Some(*local),
                    CleanupAction::EndBorrow(_) => None,
                };
                let Some(local) = local else { continue };
                if !destroyed.insert(local) {
                    return Err(error(
                        function,
                        Some(source_block),
                        format!("cleanup plan destroys r{local} more than once"),
                    ));
                }
                if !points.iter().any(|point| point.contains(&local)) {
                    return Err(error(
                        function,
                        Some(source_block),
                        format!(
                            "cleanup plan destroys r{local}, which is never live in its source block"
                        ),
                    ));
                }
                if let CleanupAction::DestroyIf { flag, .. } = action
                    && *flag as usize >= function.register_types.len()
                {
                    return Err(error(
                        function,
                        Some(source_block),
                        format!("conditional cleanup of r{local} uses out-of-range flag r{flag}"),
                    ));
                }
            }
        }
        let boundaries = derive_leave_cleanup_boundaries(function, lists)?;
        work = work.saturating_add(boundaries.len() as u64);
    }
    Ok(PassReport {
        pass: PassId::ValidateBytecodeInput,
        outcome: PassOutcome::Unchanged,
        work_units: work,
    })
}

/// Recompute derived ownership facts for bodies whose analyses were
/// invalidated by a mutation. Passes never silently keep stale facts: any
/// change ORs the invalidation mask, and this refresh is the only way the
/// facts become trusted again.
fn refresh_invalidated_flow(program: &mut Program, types: &[Type]) -> Result<(), ValidationError> {
    let array_calls = regions::array_call_summaries(program, types);
    for function in &mut program.functions {
        let invalidated = function.invalid_analyses;
        if invalidated == 0 {
            continue;
        }
        if invalidated & (analysis::CFG | analysis::USES | analysis::FLOW) == 0 {
            // EFFECTS, VALUES, and COST are ephemeral/on-demand analyses; no
            // stored ownership fact depends on them. Clearing those bits at a
            // checkpoint avoids a complete PlaceFlow rebuild for metadata-only
            // mutations such as attaching an exact indirect-call target.
            function.invalid_analyses = 0;
            continue;
        }
        rebuild_site_facts(function);
        let locals = bridged_locals(function, types);
        function.flow.locals = locals;
        function.flow.move_paths = derive_move_paths(function);
        let elaboration =
            derive_cleanup_elaboration_with_array_calls(function, types, &array_calls)?;
        apply_cleanup_elaboration(function, elaboration);
        function.invalid_analyses = 0;
    }
    Ok(())
}

fn record(passes: &mut Vec<PassReport>, pass: PassId, outcome: PassOutcome, work: u64) {
    passes.push(PassReport {
        pass,
        outcome,
        work_units: work,
    });
}

fn validate_cleanup_checkpoint(
    program: &mut Program,
    types: &[Type],
) -> Result<(), ValidationError> {
    refresh_invalidated_flow(program, types)?;
    if cfg!(debug_assertions) {
        validate_program(program, types, MirPhase::Cleanup)?;
        validate_flow_and_cleanup(program, types)?;
    }
    Ok(())
}

/// Validate a checked-builder product through the complete ownership import
/// and cleanup-elaboration boundary without retaining any transformed state.
/// Test generators and future frontend builders use this as their commit
/// predicate: a structurally well-formed CFG is not accepted unless PlaceFlow
/// can derive and validate its ownership and cleanup obligations as well.
#[allow(dead_code)] // Used by the checked MIR builder during frontend migration.
pub(crate) fn validate_generated_function(
    function: &Function,
    types: &[Type],
) -> Result<(), ValidationError> {
    let mut program = Program {
        functions: vec![function.clone()],
    };
    validate_program(&program, types, MirPhase::Raw)?;
    import_and_validate_place_flow(&mut program, types)?;
    validate_program(&program, types, MirPhase::Owned)?;
    elaborate_cleanup(&mut program, types)?;
    validate_program(&program, types, MirPhase::Cleanup)?;
    validate_flow_and_cleanup(&program, types)
}

fn push_checked(
    passes: &mut Vec<PassReport>,
    report: PassReport,
    program: &mut Program,
    types: &[Type],
) -> Result<(), ValidationError> {
    let pass = report.pass;
    passes.push(report);
    validate_cleanup_checkpoint(program, types).map_err(|mut error| {
        if std::env::var_os("GRANDIOSE_DEBUG_FLOW").is_some() {
            eprintln!(
                "optimizer checkpoint after {pass:?}:\n{}",
                program.canonical_text()
            );
        }
        error.message = format!("after {pass:?}: {}", error.message);
        error
    })
}

const FIXED_POINT_ROUNDS: usize = 3;

#[cfg(test)]
fn bounded_fixed_point(mut run: impl FnMut() -> Option<PassReport>) -> Vec<PassReport> {
    let mut reports = Vec::with_capacity(FIXED_POINT_ROUNDS);
    for _ in 0..FIXED_POINT_ROUNDS {
        let Some(report) = run() else {
            break;
        };
        let stop = matches!(
            report.outcome,
            PassOutcome::Unchanged | PassOutcome::BudgetExhausted
        );
        reports.push(report);
        if stop {
            break;
        }
    }
    reports
}

/// Run one MIR pass to the bounded fixed point required by the frozen schedule.
/// Reports retain every actual round, which makes both early stabilization and
/// cap hits observable without introducing timing-dependent diagnostics.
fn run_fixed_point(
    passes: &mut Vec<PassReport>,
    program: &mut Program,
    pass: PassId,
    types: &[Type],
    global_remaining: &mut u64,
) -> Result<(), ValidationError> {
    for _ in 0..FIXED_POINT_ROUNDS {
        if *global_remaining == 0 {
            break;
        }
        let report = run_transactional_pass(program, pass, types, global_remaining);
        let stop = matches!(
            report.outcome,
            PassOutcome::Unchanged | PassOutcome::BudgetExhausted
        );
        push_checked(passes, report, program, types)?;
        if stop {
            break;
        }
    }
    Ok(())
}

/// Run a whole-program transform to the same bounded fixed point as local
/// passes. Direct-call specialization discovers candidates across function
/// bodies, so it must use the whole-program dispatcher rather than the local
/// pass entry point.
fn run_whole_program_fixed_point(
    passes: &mut Vec<PassReport>,
    program: &mut Program,
    pass: PassId,
    tables: WholeProgramPassTables<'_>,
    level: OptimizationLevel,
    types: &[Type],
    global_remaining: &mut u64,
    inline_policy: &mut InlinePolicyState,
) -> Result<(), ValidationError> {
    for _ in 0..FIXED_POINT_ROUNDS {
        if *global_remaining == 0 {
            break;
        }
        let report = run_transactional_whole_program_pass(
            program,
            pass,
            tables,
            level,
            global_remaining,
            inline_policy,
        );
        let stop = matches!(
            report.outcome,
            PassOutcome::Unchanged | PassOutcome::BudgetExhausted,
        );
        push_checked(passes, report, program, types)?;
        if stop {
            break;
        }
    }
    Ok(())
}

/// Complete the post-inline cleanup cycle. Sparse simplification performs
/// propagation and local DCE; CFG normalization then deletes the newly dead
/// arms and trivial joins. Either rewrite can expose work for the other, so
/// alternate them under the same deterministic cap and global work budget.
fn run_post_inline_cleanup_fixed_point(
    passes: &mut Vec<PassReport>,
    program: &mut Program,
    types: &[Type],
    global_remaining: &mut u64,
) -> Result<(), ValidationError> {
    for _ in 0..FIXED_POINT_ROUNDS {
        if *global_remaining == 0 {
            break;
        }
        let normalize = run_transactional_pass(
            program,
            PassId::NormalizeCfg,
            types,
            global_remaining,
        );
        let normalize_stop = matches!(normalize.outcome, PassOutcome::Unchanged);
        let normalize_exhausted = matches!(normalize.outcome, PassOutcome::BudgetExhausted);
        push_checked(passes, normalize, program, types)?;
        if *global_remaining == 0 || normalize_exhausted {
            break;
        }
        let sparse = run_transactional_pass(
            program,
            PassId::SparseSimplify,
            types,
            global_remaining,
        );
        let sparse_stop = matches!(sparse.outcome, PassOutcome::Unchanged);
        let sparse_exhausted = matches!(sparse.outcome, PassOutcome::BudgetExhausted);
        push_checked(passes, sparse, program, types)?;
        if sparse_exhausted || (normalize_stop && sparse_stop) {
            break;
        }
    }
    Ok(())
}

/// Run the fixed generation-1 MIR pass schedule. Unimplemented optional MIR
/// passes are reported explicitly rather than silently approximated. Frontend
/// ownership/cleanup construction and bytecode lowering occur in their owning
/// pipelines and are deliberately not claimed by this report.
#[cfg(test)]
pub(crate) fn optimize_program(
    program: &mut Program,
    types: &[Type],
    level: OptimizationLevel,
) -> Result<OptimizationReport, ValidationError> {
    optimize_program_with_control_tables(program, types, &[], &[], level)
}

pub(crate) fn optimize_program_with_control_tables(
    program: &mut Program,
    types: &[Type],
    protocols: &[Protocol],
    handler_defs: &[HandlerDef],
    level: OptimizationLevel,
) -> Result<OptimizationReport, ValidationError> {
    validate_program(program, types, MirPhase::Raw)?;
    let initial_operations = operation_count(program);
    let mut passes = Vec::new();
    record(
        &mut passes,
        PassId::ValidateRawMir,
        PassOutcome::Unchanged,
        initial_operations,
    );
    let import = import_and_validate_place_flow(program, types)?;
    passes.push(import);
    validate_program(program, types, MirPhase::Owned)?;
    let cleanup = elaborate_cleanup(program, types)?;
    passes.push(cleanup);
    validate_program(program, types, MirPhase::Cleanup)?;
    validate_flow_and_cleanup(program, types)?;
    record(
        &mut passes,
        PassId::ValidateCleanupMir,
        PassOutcome::Unchanged,
        initial_operations,
    );

    let normalize = run_mandatory_normalize(program);
    push_checked(&mut passes, normalize, program, types)?;
    let mut global_remaining = 64_u64.saturating_mul(initial_operations);
    let mut inline_policy = InlinePolicyState::default();
    let whole_program_tables = WholeProgramPassTables {
        types,
        protocols,
        handler_defs,
    };

    if level.at_least(OptimizationLevel::O1) {
        run_fixed_point(
            &mut passes,
            program,
            PassId::SparseSimplify,
            types,
            &mut global_remaining,
        )?;
        if global_remaining != 0 {
            let report = run_transactional_pass(
                program,
                PassId::ScalarizeLocals,
                types,
                &mut global_remaining,
            );
            push_checked(&mut passes, report, program, types)?;
        }
        if global_remaining != 0 {
            let report = run_transactional_pass(
                program,
                PassId::SimplifyCleanup,
                types,
                &mut global_remaining,
            );
            push_checked(&mut passes, report, program, types)?;
        }
        if global_remaining != 0 {
            let report = run_transactional_whole_program_pass(
                program,
                PassId::SpecializeDirectCalls,
                whole_program_tables,
                level,
                &mut global_remaining,
                &mut inline_policy,
            );
            push_checked(&mut passes, report, program, types)?;
        }
    }
    if level.at_least(OptimizationLevel::O2) {
        if global_remaining != 0 {
            let report = run_transactional_pass(
                program,
                PassId::GlobalSimplify,
                types,
                &mut global_remaining,
            );
            push_checked(&mut passes, report, program, types)?;
        }
        if global_remaining != 0 {
            let report = run_transactional_whole_program_pass(
                program,
                PassId::ScalarizeCallables,
                whole_program_tables,
                level,
                &mut global_remaining,
                &mut inline_policy,
            );
            push_checked(&mut passes, report, program, types)?;
        }
        if global_remaining != 0 {
            let report = run_transactional_whole_program_pass(
                program,
                PassId::SpecializeControl,
                whole_program_tables,
                level,
                &mut global_remaining,
                &mut inline_policy,
            );
            push_checked(&mut passes, report, program, types)?;
        }
        if global_remaining != 0 {
            let report = run_transactional_pass(
                program,
                PassId::SpecializeCleanup,
                types,
                &mut global_remaining,
            );
            push_checked(&mut passes, report, program, types)?;
        }
        if global_remaining != 0 {
            let report = run_transactional_whole_program_pass(
                program,
                PassId::InlineByCost,
                whole_program_tables,
                level,
                &mut global_remaining,
                &mut inline_policy,
            );
            push_checked(&mut passes, report, program, types)?;
        }
        run_fixed_point(
            &mut passes,
            program,
            PassId::SparseSimplify,
            types,
            &mut global_remaining,
        )?;
        // O3 repeats the devirtualization/control/inlining family, then gives
        // its newly exposed local facts a distinct bounded fixed point. This
        // must happen before proof erasure and tail formation.
        if level == OptimizationLevel::O3 {
            if global_remaining != 0 {
                let report = run_transactional_pass(
                    program,
                    PassId::GlobalSimplify,
                    types,
                    &mut global_remaining,
                );
                push_checked(&mut passes, report, program, types)?;
            }
            if global_remaining != 0 {
                let report = run_transactional_whole_program_pass(
                    program,
                    PassId::SpecializeControl,
                    whole_program_tables,
                    level,
                    &mut global_remaining,
                    &mut inline_policy,
                );
                push_checked(&mut passes, report, program, types)?;
            }
            if global_remaining != 0 {
                let report = run_transactional_whole_program_pass(
                    program,
                    PassId::InlineByCost,
                    whole_program_tables,
                    level,
                    &mut global_remaining,
                    &mut inline_policy,
                );
                push_checked(&mut passes, report, program, types)?;
            }
            run_fixed_point(
                &mut passes,
                program,
                PassId::SparseSimplify,
                types,
                &mut global_remaining,
            )?;
        }
    }

    // Sparse/global simplification and inlining can turn a Switch into a
    // Goto or expose an unreachable continuation after the mandatory early
    // normalization has run. Alternate propagation/DCE with checked CFG
    // cleanup before representation lowering.
    if level.at_least(OptimizationLevel::O1) {
        run_post_inline_cleanup_fixed_point(
            &mut passes,
            program,
            types,
            &mut global_remaining,
        )?;
        if level.at_least(OptimizationLevel::O2) {
            // The first direct-call pass can turn an ordinary wrapper into a
            // forwarding function only after its call continuation has been
            // normalized away. Inlining can expose the same shape in a caller.
            // Revisit direct-call specialization after that cleanup so callers do
            // not retain a dynamic VM call merely because their target became
            // trivial during this optimization run. The bounded pass fixed point
            // also handles short chains of such newly-forwarding wrappers.
            run_whole_program_fixed_point(
                &mut passes,
                program,
                PassId::SpecializeDirectCalls,
                whole_program_tables,
                level,
                types,
                &mut global_remaining,
                &mut inline_policy,
            )?;
            // Re-specialization produces Gotos and can expose another trivial
            // join, so give its result the same checked CFG/local cleanup cycle.
            run_post_inline_cleanup_fixed_point(
                &mut passes,
                program,
                types,
                &mut global_remaining,
            )?;
        }
    }

    // Proof-only references are a mandatory representation lowering at every
    // optimization level, not an optional O2 profitability transform.
    let erasure = run_mandatory_loan_erasure(program);
    push_checked(&mut passes, erasure, program, types)?;
    if level.at_least(OptimizationLevel::O2) {
        let report = run_transactional_pass(
            program,
            PassId::FormTailCallsAndHoist,
            types,
            &mut global_remaining,
        );
        push_checked(&mut passes, report, program, types)?;
    }

    refresh_invalidated_flow(program, types)?;
    for function in &mut program.functions {
        function.phase = MirPhase::Optimized;
        function.features = infer_feature_bits(function);
    }
    validate_program(program, types, MirPhase::Optimized)?;
    validate_flow_and_cleanup(program, types)?;
    passes.push(validate_bytecode_input_checkpoint(program, types)?);
    Ok(OptimizationReport {
        level,
        initial_operations,
        final_operations: operation_count(program),
        passes,
    })
}

#[cfg(test)]
mod tests {
    use grandiose_vm::bytecode::{EnumVariant, Field, Signature};
    use grandiose_vm::{I64, Type, UNIT};

    use crate::span::Span;

    use super::*;
    use crate::compiler_mir::{
        BasicBlock, BlockParam, ContinuationCapture, Instruction, ResidualCapture, UseMode,
    };

    fn operand(register: u32) -> Operand {
        Operand {
            register,
            mode: UseMode::Copy,
        }
    }

    fn function(blocks: Vec<BasicBlock>, registers: Vec<TypeId>) -> Function {
        Function {
            declaration: 0,
            name: "test".into(),
            params: vec![],
            result: UNIT,
            receiver_mode: None,
            receiver_type: UNIT,
            no_return: false,
            outward_protocols: vec![],
            register_types: registers,
            entry: 0,
            blocks,
            phase: MirPhase::Raw,
            features: FeatureBits::empty(),
            return_cleanup: vec![],
            flow: crate::compiler_mir::PlaceFlow::default(),
            invalid_analyses: 0,
        }
    }

    fn block(id: u32, terminator: Terminator) -> BasicBlock {
        BasicBlock {
            id,
            params: vec![],
            statements: vec![],
            terminator,
        }
    }

    fn program(function: Function) -> Program {
        Program {
            functions: vec![function],
        }
    }

    #[test]
    fn structural_use_facts_count_leave_arguments_once() {
        let body = function(
            vec![
                block(
                    0,
                    Terminator::Leave {
                        label: LabelId(0),
                        target: Edge {
                            target: 1,
                            args: vec![operand(1)],
                        },
                    },
                ),
                block(1, Terminator::Return { value: None }),
            ],
            vec![UNIT, UNIT],
        );

        assert_eq!(register_uses(&body), vec![0, 1]);
        assert_eq!(
            terminator_register_use_count(&body.blocks[0].terminator, 1),
            1
        );
    }

    #[test]
    fn emission_keeps_a_copied_reference_handle_live_for_later_end_borrow() {
        let mut types = Type::predefined();
        let shared = types.len() as TypeId;
        types.push(Type::RefShared { referent: I64 });

        let mut entry = block(
            0,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![operand(2)],
            }),
        );
        entry.statements.push(instruction(InstructionKind::Borrow {
            dst: 2,
            src: 1,
            unique: false,
        }));
        let mut target = block(1, Terminator::Return { value: None });
        target.params.push(BlockParam {
            register: 3,
            ty: shared,
            role: BlockParamRole::Ordinary,
        });
        target.statements.extend([
            instruction(InstructionKind::EndBorrow { reference: 2 }),
            instruction(InstructionKind::EndBorrow { reference: 3 }),
        ]);
        let mut body = function(vec![entry, target], vec![UNIT, I64, shared, shared]);
        body.params = vec![I64];
        body.features = infer_feature_bits(&body);
        let mut candidate = program(body);

        optimize_program(&mut candidate, &types, OptimizationLevel::O0).unwrap();
        canonicalize_dead_edge_copies_for_emission(&mut candidate, &types).unwrap();

        let Terminator::Goto(edge) = &candidate.functions[0].blocks[0].terminator else {
            panic!("reference transport must remain an ordinary edge");
        };
        assert_eq!(edge.args, vec![operand(2)]);
    }

    #[test]
    fn validator_rejects_phase_duplicate_missing_target_and_bad_register() {
        let types = Type::predefined();
        let mut wrong_phase = program(function(
            vec![block(0, Terminator::Return { value: None })],
            vec![],
        ));
        wrong_phase.functions[0].phase = MirPhase::Cleanup;
        assert!(
            validate_program(&wrong_phase, &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("phase")
        );

        let duplicate = program(function(
            vec![
                block(0, Terminator::Unreachable),
                block(0, Terminator::Unreachable),
            ],
            vec![],
        ));
        assert!(
            validate_program(&duplicate, &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("duplicate")
        );

        let missing = program(function(
            vec![block(
                0,
                Terminator::Goto(Edge {
                    target: 9,
                    args: vec![],
                }),
            )],
            vec![],
        ));
        assert!(
            validate_program(&missing, &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("missing block")
        );

        let bad_register = program(function(
            vec![block(
                0,
                Terminator::Return {
                    value: Some(operand(4)),
                },
            )],
            vec![],
        ));
        assert!(
            validate_program(&bad_register, &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("out of range")
        );
    }

    #[test]
    fn validator_rejects_an_edge_that_moves_one_source_twice() {
        let types = Type::predefined();
        let mut entry = block(
            0,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![
                    Operand {
                        register: 1,
                        mode: UseMode::Move,
                    },
                    Operand {
                        register: 1,
                        mode: UseMode::Move,
                    },
                ],
            }),
        );
        entry.statements.push(instruction(InstructionKind::Const {
            dst: 1,
            value: Constant::I64(1),
        }));
        let target = BasicBlock {
            id: 1,
            params: vec![
                BlockParam {
                    register: 2,
                    ty: I64,
                    role: BlockParamRole::Ordinary,
                },
                BlockParam {
                    register: 3,
                    ty: I64,
                    role: BlockParamRole::Ordinary,
                },
            ],
            statements: vec![],
            terminator: Terminator::Return { value: None },
        };
        let duplicate_move = program(function(vec![entry, target], vec![UNIT, I64, I64, I64]));
        assert!(
            validate_program(&duplicate_move, &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("moves r1 more than once")
        );
    }

    #[test]
    fn validator_checks_edge_parameter_count_and_type() {
        let types = Type::predefined();
        let mut target = block(1, Terminator::Return { value: None });
        target.params.push(BlockParam {
            register: 0,
            ty: I64,
            role: BlockParamRole::Ordinary,
        });
        let mismatch = program(function(
            vec![
                block(
                    0,
                    Terminator::Goto(Edge {
                        target: 1,
                        args: vec![],
                    }),
                ),
                target,
            ],
            vec![I64],
        ));
        assert!(
            validate_program(&mismatch, &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("arguments")
        );
    }

    #[test]
    fn validator_rejects_duplicate_declarations_and_index_fallback_targets() {
        let types = Type::predefined();
        let mut duplicate = function(vec![block(0, Terminator::Return { value: None })], vec![]);
        duplicate.declaration = 4;
        let duplicate_program = Program {
            functions: vec![duplicate.clone(), duplicate],
        };
        assert!(
            validate_program(&duplicate_program, &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("duplicate function declaration")
        );

        let mut missing = function(
            vec![block(
                0,
                Terminator::TailCall {
                    function: 0,
                    args: vec![],
                },
            )],
            vec![],
        );
        missing.declaration = 9;
        assert!(
            validate_program(&program(missing), &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("target 0 is missing")
        );
    }

    #[test]
    fn validator_rejects_redefined_registers_and_mismatched_call_result_parameters() {
        let types = Type::predefined();
        let mut entry = block(0, Terminator::Return { value: None });
        entry.statements = vec![
            instruction(InstructionKind::Const {
                dst: 0,
                value: Constant::I64(1),
            }),
            instruction(InstructionKind::Const {
                dst: 0,
                value: Constant::I64(2),
            }),
        ];
        let duplicate = program(function(vec![entry], vec![I64]));
        assert!(
            validate_program(&duplicate, &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("defined by both")
        );

        let mut caller = function(
            vec![
                block(
                    0,
                    Terminator::Call {
                        result: Some(0),
                        function: 1,
                        args: vec![],
                        normal: Edge {
                            target: 1,
                            args: vec![],
                        },
                    },
                ),
                BasicBlock {
                    id: 1,
                    params: vec![BlockParam {
                        register: 1,
                        ty: I64,
                        role: BlockParamRole::CallResult,
                    }],
                    statements: vec![],
                    terminator: Terminator::Unreachable,
                },
            ],
            vec![I64, I64],
        );
        caller.declaration = 0;
        let mut callee = function(vec![block(0, Terminator::Unreachable)], vec![]);
        callee.declaration = 1;
        callee.result = I64;
        let mismatch = Program {
            functions: vec![caller, callee],
        };
        assert!(
            validate_program(&mismatch, &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("carries result r0")
        );
    }

    #[test]
    fn validator_allows_consumed_temporary_aggregate_reconstruction() {
        let mut types = Type::predefined();
        let tuple = types.len() as TypeId;
        types.push(Type::Tuple {
            fields: vec![I64],
            copy: true,
        });
        let mut entry = block(
            0,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![],
            }),
        );
        entry.statements = vec![
            instruction(InstructionKind::Const {
                dst: 0,
                value: Constant::I64(1),
            }),
            instruction(InstructionKind::Construct {
                dst: 1,
                ty: tuple,
                variant: None,
                fields: vec![Operand {
                    register: 0,
                    mode: UseMode::Move,
                }],
            }),
        ];
        let mut rebuild = block(1, Terminator::Return { value: None });
        rebuild.statements = vec![
            instruction(InstructionKind::ProjectMove {
                dst: 2,
                src: Operand {
                    register: 1,
                    mode: UseMode::Move,
                },
                field: 0,
            }),
            instruction(InstructionKind::Deconstruct { src: 1 }),
            instruction(InstructionKind::Construct {
                dst: 1,
                ty: tuple,
                variant: None,
                fields: vec![Operand {
                    register: 2,
                    mode: UseMode::Move,
                }],
            }),
        ];

        let candidate = program(function(vec![entry, rebuild], vec![I64, tuple, I64]));
        validate_program(&candidate, &types, MirPhase::Raw).unwrap();
    }

    #[test]
    fn validator_checks_callable_descriptors_and_indirect_results() {
        let mut types = Type::predefined();
        let callable = types.len() as TypeId;
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            capture_type: UNIT,
            receiver_mode: 2,
            identity_name: "bad-target".into(),
            copy: false,
            zero_use_allowed: true,
        });
        let mut maker = function(
            vec![block(0, Terminator::Return { value: None })],
            vec![UNIT, callable],
        );
        maker.blocks[0]
            .statements
            .push(instruction(InstructionKind::MakeCallable {
                dst: 1,
                callable_type: callable,
                function: 7,
                captures: vec![],
            }));
        let mut target = function(
            vec![block(0, Terminator::Return { value: None })],
            vec![UNIT],
        );
        target.declaration = 7;
        target.receiver_mode = Some(2);
        let malformed = Program {
            functions: vec![maker, target],
        };
        assert!(
            validate_program(&malformed, &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("descriptor does not match target signature")
        );

        let indirect = program(function(
            vec![
                block(
                    0,
                    Terminator::CallIndirect {
                        result: None,
                        callable: Operand {
                            register: 0,
                            mode: UseMode::Move,
                        },
                        known_function: None,
                        receiver_mode: 2,
                        cleanup_callable: false,
                        args: vec![],
                        normal: Edge {
                            target: 1,
                            args: vec![],
                        },
                    },
                ),
                block(1, Terminator::Return { value: None }),
            ],
            vec![callable],
        ));
        assert!(
            validate_program(&indirect, &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("has no result register")
        );
    }

    #[test]
    fn validator_checks_callable_receiver_and_capture_layout() {
        let mut types = Type::predefined();
        let capture = types.len() as TypeId;
        types.push(Type::Tuple {
            fields: vec![I64],
            copy: true,
        });
        let shared_capture = types.len() as TypeId;
        types.push(Type::RefShared { referent: capture });
        let callable = types.len() as TypeId;
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            capture_type: capture,
            receiver_mode: 0,
            identity_name: "capture-check".into(),
            copy: true,
            zero_use_allowed: true,
        });

        let make_program = |captures: Vec<Operand>, receiver_type: TypeId| {
            let mut maker = function(
                vec![block(0, Terminator::Return { value: None })],
                vec![UNIT, callable, I64],
            );
            maker.blocks[0]
                .statements
                .push(instruction(InstructionKind::Const {
                    dst: 2,
                    value: Constant::I64(1),
                }));
            maker.blocks[0]
                .statements
                .push(instruction(InstructionKind::MakeCallable {
                    dst: 1,
                    callable_type: callable,
                    function: 7,
                    captures,
                }));
            let mut target = function(
                vec![block(0, Terminator::Return { value: None })],
                vec![receiver_type],
            );
            target.declaration = 7;
            target.receiver_mode = Some(0);
            target.receiver_type = receiver_type;
            Program {
                functions: vec![maker, target],
            }
        };

        let bad_receiver = make_program(vec![operand(2)], UNIT);
        assert!(
            validate_program(&bad_receiver, &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("receiver type is inconsistent")
        );

        let bad_layout = make_program(vec![], shared_capture);
        assert!(
            validate_program(&bad_layout, &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("capture count does not match")
        );
    }

    #[test]
    fn validator_limits_indirect_modes_and_self_tail_place_assignments() {
        let mut types = Type::predefined();
        let callable = types.len() as TypeId;
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            capture_type: UNIT,
            receiver_mode: 0,
            identity_name: "mode-check".into(),
            copy: true,
            zero_use_allowed: true,
        });
        let bad_mode = program(function(
            vec![
                block(
                    0,
                    Terminator::CallIndirect {
                        result: None,
                        callable: operand(0),
                        known_function: None,
                        receiver_mode: 3,
                        cleanup_callable: false,
                        args: vec![],
                        normal: Edge {
                            target: 1,
                            args: vec![],
                        },
                    },
                ),
                block(1, Terminator::Return { value: None }),
            ],
            vec![callable],
        ));
        assert!(
            validate_program(&bad_mode, &types, MirPhase::Raw)
                .unwrap_err()
                .message
                .contains("invalid indirect receiver mode")
        );

        let self_tail = |assignment_mode| {
            let mut body = function(
                vec![BasicBlock {
                    id: 0,
                    params: vec![],
                    statements: vec![
                        instruction(InstructionKind::Move {
                            dst: 2,
                            src: Operand {
                                register: 1,
                                mode: UseMode::Move,
                            },
                        }),
                        instruction(InstructionKind::Move {
                            dst: 1,
                            src: Operand {
                                register: 2,
                                mode: assignment_mode,
                            },
                        }),
                    ],
                    terminator: Terminator::Goto(Edge {
                        target: 0,
                        args: vec![],
                    }),
                }],
                vec![UNIT, I64, I64],
            );
            body.params = vec![I64];
            body.phase = MirPhase::Optimized;
            body.features = infer_feature_bits(&body);
            program(body)
        };
        assert!(validate_program(&self_tail(UseMode::Move), &types, MirPhase::Optimized).is_ok());
        assert!(
            validate_program(&self_tail(UseMode::Copy), &types, MirPhase::Optimized)
                .unwrap_err()
                .message
                .contains("defined by both")
        );
    }

    #[test]
    fn feature_inference_is_stable_and_finds_barriers() {
        let mut body = function(
            vec![block(
                0,
                Terminator::TailCallIndirect {
                    callable: operand(0),
                    known_function: None,
                    receiver_mode: 2,
                    args: vec![],
                },
            )],
            vec![UNIT],
        );
        body.blocks[0].statements.push(Instruction {
            span: Span::new(0, 0),
            kind: InstructionKind::Drop { owner: operand(0) },
        });
        let first = infer_feature_bits(&body);
        assert!(first.contains(FeatureBits::INDIRECT_CALLS));
        assert!(first.contains(FeatureBits::TAIL_CALLS));
        assert!(first.contains(FeatureBits::DROPS));
        assert_eq!(first, infer_feature_bits(&body));
    }

    #[test]
    fn normalize_cfg_removes_unreachable_and_empty_forwarders_only() {
        let types = Type::predefined();
        let mut body = function(
            vec![
                block(
                    0,
                    Terminator::Goto(Edge {
                        target: 1,
                        args: vec![],
                    }),
                ),
                block(
                    1,
                    Terminator::Goto(Edge {
                        target: 2,
                        args: vec![],
                    }),
                ),
                block(2, Terminator::Return { value: None }),
                block(9, Terminator::Unreachable),
            ],
            vec![],
        );
        // A drop makes block 2 a barrier and therefore nontrivial.
        body.blocks[2].statements.push(Instruction {
            span: Span::new(0, 0),
            kind: InstructionKind::Drop { owner: operand(0) },
        });
        // Ownership barriers in an unreachable component are unobservable and
        // are removed with that component, never floated onto a live path.
        body.blocks[3].statements.push(Instruction {
            span: Span::new(0, 0),
            kind: InstructionKind::Drop { owner: operand(0) },
        });
        body.register_types.push(UNIT);
        // r0 is an initialized receiver at entry; scratch registers are no
        // longer implicitly live in lenient hand-assembled MIR.
        body.receiver_mode = Some(2);
        body.receiver_type = UNIT;
        let mut program = program(body);
        optimize_program(&mut program, &types, OptimizationLevel::O0).unwrap();
        assert_eq!(program.functions[0].blocks.len(), 1);
        assert_eq!(program.functions[0].entry, 2);
        assert!(matches!(
            program.functions[0].blocks[0].statements[0].kind,
            InstructionKind::Drop { .. }
        ));
    }

    #[test]
    fn normalize_cfg_merges_unique_straight_line_blocks_in_order() {
        let types = Type::predefined();
        let mut entry = block(
            0,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![],
            }),
        );
        entry.statements.push(Instruction {
            span: Span::new(1, 2),
            kind: InstructionKind::Const {
                dst: 0,
                value: Constant::U32(1),
            },
        });
        let mut target = block(1, Terminator::Return { value: None });
        target.statements.push(Instruction {
            span: Span::new(3, 4),
            kind: InstructionKind::Drop { owner: operand(0) },
        });
        let mut program = program(function(vec![target, entry], vec![U32]));

        optimize_program(&mut program, &types, OptimizationLevel::O0).unwrap();

        let body = &program.functions[0];
        assert_eq!(body.entry, 0);
        assert_eq!(body.blocks.len(), 1);
        assert_eq!(body.blocks[0].id, 0);
        assert!(matches!(
            body.blocks[0].statements.as_slice(),
            [
                Instruction {
                    kind: InstructionKind::Const { .. },
                    ..
                },
                Instruction {
                    kind: InstructionKind::Drop { .. },
                    ..
                }
            ]
        ));
        assert!(matches!(
            body.blocks[0].terminator,
            Terminator::Return { .. }
        ));
    }

    #[test]
    fn normalize_cfg_preserves_block_parameter_transfers() {
        let types = Type::predefined();
        let mut entry = block(
            0,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![operand(0)],
            }),
        );
        entry.statements.push(Instruction {
            span: Span::new(0, 0),
            kind: InstructionKind::Const {
                dst: 0,
                value: Constant::U32(7),
            },
        });
        let mut target = block(1, Terminator::Return { value: None });
        target.params.push(BlockParam {
            register: 1,
            ty: U32,
            role: BlockParamRole::Ordinary,
        });
        target.statements.push(Instruction {
            span: Span::new(0, 0),
            kind: InstructionKind::Drop { owner: operand(1) },
        });
        let mut program = program(function(vec![entry, target], vec![U32, U32]));

        optimize_program(&mut program, &types, OptimizationLevel::O0).unwrap();

        let body = &program.functions[0];
        assert_eq!(body.blocks.len(), 2);
        assert!(matches!(
            body.blocks[0].terminator,
            Terminator::Goto(Edge { target: 1, .. })
        ));
        assert_eq!(body.blocks[1].params[0].role, BlockParamRole::Ordinary);
    }

    fn constant_switch_parameter_diamond(second_is_constant: bool) -> Function {
        let entry = block(
            0,
            Terminator::Switch {
                discr: operand(1),
                cases: vec![(
                    Constant::U32(1),
                    Edge {
                        target: 1,
                        args: vec![],
                    },
                )],
                otherwise: Edge {
                    target: 2,
                    args: vec![],
                },
            },
        );
        let mut truthy = block(
            1,
            Terminator::Goto(Edge {
                target: 3,
                args: vec![move_operand(2)],
            }),
        );
        truthy.statements.push(instruction(InstructionKind::Const {
            dst: 2,
            value: Constant::U32(1),
        }));
        let mut falsy = block(
            2,
            Terminator::Goto(Edge {
                target: 3,
                args: vec![move_operand(3)],
            }),
        );
        if second_is_constant {
            falsy.statements.push(instruction(InstructionKind::Const {
                dst: 3,
                value: Constant::U32(0),
            }));
        }
        let mut dispatcher = block(
            3,
            Terminator::Switch {
                discr: operand(4),
                cases: vec![(
                    Constant::U32(1),
                    Edge {
                        target: 4,
                        args: vec![],
                    },
                )],
                otherwise: Edge {
                    target: 5,
                    args: vec![],
                },
            },
        );
        dispatcher.params.push(BlockParam {
            register: 4,
            ty: U32,
            role: BlockParamRole::ProtectedExitValue,
        });
        let mut yes = block(4, Terminator::Return { value: None });
        yes.statements.push(instruction(InstructionKind::Drop {
            owner: move_operand(4),
        }));
        let mut no = block(5, Terminator::Return { value: None });
        no.statements.push(instruction(InstructionKind::Drop {
            owner: move_operand(4),
        }));
        let mut body = function(
            vec![entry, truthy, falsy, dispatcher, yes, no],
            vec![UNIT, U32, U32, U32, U32],
        );
        body.params = vec![U32];
        body
    }

    #[test]
    fn normalize_cfg_threads_constant_switch_parameter_diamonds_with_exact_ownership() {
        let types = Type::predefined();
        let mut optimized = program(constant_switch_parameter_diamond(true));
        optimize_program(&mut optimized, &types, OptimizationLevel::O0).unwrap();
        assert!(
            optimized.functions[0]
                .blocks
                .iter()
                .all(|block| block.id != 3),
            "mandatory O0 normalization must remove the dispatcher"
        );

        let mut body = constant_switch_parameter_diamond(true);
        let mut work = 0;

        assert!(
            thread_one_constant_switch_parameter_diamond(&mut body, u64::MAX, &mut work).unwrap()
        );
        assert!(body.blocks.iter().all(|block| block.id != 3));
        assert_eq!(body.register_types.len(), 7);

        let truthy = body.blocks.iter().find(|block| block.id == 1).unwrap();
        let falsy = body.blocks.iter().find(|block| block.id == 2).unwrap();
        assert!(matches!(
            &truthy.terminator,
            Terminator::Goto(Edge { target: 4, args })
                if args == &vec![move_operand(2)]
        ));
        assert!(matches!(
            &falsy.terminator,
            Terminator::Goto(Edge { target: 5, args })
                if args == &vec![move_operand(3)]
        ));
        for (target, fresh) in [(4, 5), (5, 6)] {
            let arm = body.blocks.iter().find(|block| block.id == target).unwrap();
            assert_eq!(
                arm.params,
                [BlockParam {
                    register: fresh,
                    ty: U32,
                    role: BlockParamRole::Ordinary,
                }]
            );
            assert!(matches!(
                arm.statements[0].kind,
                InstructionKind::Drop {
                    owner: Operand {
                        register,
                        mode: UseMode::Move
                    }
                } if register == fresh
            ));
        }
        assert_eq!(register_uses(&body)[4], 0);
    }

    #[test]
    fn normalize_cfg_does_not_thread_a_diamond_across_a_live_reference() {
        let types = Type::predefined();
        let mut body = constant_switch_parameter_diamond(true);
        body.register_types.push(UNIT);
        for target in [4, 5] {
            body.blocks
                .iter_mut()
                .find(|block| block.id == target)
                .unwrap()
                .terminator = Terminator::Return {
                value: Some(move_operand(5)),
            };
        }
        body.flow.locals = body
            .register_types
            .iter()
            .map(|ty| LocalFact::conservative(*ty, &types[*ty as usize]))
            .collect();
        body.flow.locals[5].ownership = crate::compiler_mir::OwnershipCategory::SharedRef;
        let original = body.clone();
        let mut work = 0;

        assert!(
            !thread_one_constant_switch_parameter_diamond(&mut body, u64::MAX, &mut work).unwrap()
        );
        assert_eq!(body, original);
    }

    #[test]
    fn normalize_cfg_does_not_partially_thread_a_nonconstant_diamond() {
        let mut body = constant_switch_parameter_diamond(false);
        let original = body.clone();
        let mut work = 0;

        assert!(
            !thread_one_constant_switch_parameter_diamond(&mut body, u64::MAX, &mut work).unwrap()
        );
        assert_eq!(body, original);
    }

    #[test]
    fn normalize_cfg_does_not_thread_a_diamond_with_existing_arm_arguments() {
        let mut body = constant_switch_parameter_diamond(true);
        let dispatcher = body.blocks.iter_mut().find(|block| block.id == 3).unwrap();
        let Terminator::Switch { cases, .. } = &mut dispatcher.terminator else {
            unreachable!();
        };
        cases[0].1.args.push(move_operand(2));
        let original = body.clone();
        let mut work = 0;

        assert!(
            !thread_one_constant_switch_parameter_diamond(&mut body, u64::MAX, &mut work).unwrap()
        );
        assert_eq!(body, original);
    }

    #[test]
    fn normalize_cfg_preserves_handler_and_resumption_continuation_edges() {
        let types = Type::predefined();
        let mut handler_continuation = block(
            1,
            Terminator::Goto(Edge {
                target: 2,
                args: vec![],
            }),
        );
        handler_continuation.params.push(BlockParam {
            register: 0,
            ty: UNIT,
            role: BlockParamRole::CallResult,
        });
        let handler = function(
            vec![
                block(
                    0,
                    Terminator::Handle {
                        result: 0,
                        handler: operand(1),
                        body: operand(2),
                        normal: Edge {
                            target: 1,
                            args: vec![],
                        },
                    },
                ),
                handler_continuation,
                block(2, Terminator::Return { value: None }),
            ],
            vec![UNIT, UNIT, UNIT],
        );

        let mut resume_continuation = block(
            1,
            Terminator::Goto(Edge {
                target: 2,
                args: vec![],
            }),
        );
        resume_continuation.params.push(BlockParam {
            register: 0,
            ty: UNIT,
            role: BlockParamRole::ResumeResult,
        });
        let resumption = function(
            vec![
                block(
                    0,
                    Terminator::Perform {
                        result: Some(0),
                        protocol: 0,
                        operation: 0,
                        payloads: vec![],
                        capture: crate::compiler_mir::ContinuationCapture {
                            captured_owners: vec![],
                            captured_references: vec![],
                            captured_residuals: vec![],
                            cancellation_safe: true,
                        },
                        resume: Some(Edge {
                            target: 1,
                            args: vec![],
                        }),
                    },
                ),
                resume_continuation,
                block(2, Terminator::Return { value: None }),
            ],
            vec![UNIT],
        );

        for body in [handler, resumption] {
            let mut program = program(body);
            optimize_program(&mut program, &types, OptimizationLevel::O0).unwrap();
            let body = &program.functions[0];
            // The ordinary tail after the continuation may merge into it, but
            // the implicit-result continuation itself must remain intact.
            assert_eq!(body.blocks.len(), 2);
            assert_eq!(body.blocks[1].id, 1);
            assert_eq!(body.blocks[1].params.len(), 1);
        }
    }

    #[test]
    fn normalize_cfg_eliminates_only_a_same_move_identity_ordinary_parameter() {
        let mut target = block(
            3,
            Terminator::Return {
                value: Some(move_operand(3)),
            },
        );
        target.params.push(BlockParam {
            register: 3,
            ty: I64,
            role: BlockParamRole::Ordinary,
        });
        let entry = block(
            0,
            Terminator::Switch {
                discr: operand(2),
                cases: vec![(
                    Constant::U32(0),
                    Edge {
                        target: 3,
                        args: vec![move_operand(1)],
                    },
                )],
                otherwise: Edge {
                    target: 3,
                    args: vec![move_operand(1)],
                },
            },
        );
        let mut body = function(vec![entry, target], vec![UNIT, I64, U32, I64]);
        body.params = vec![I64, U32];
        body.result = I64;

        let liveness = EdgeLiveness::compute(&body, u64::MAX).unwrap();
        assert!(simplify_identity_block_parameter(&mut body, &liveness, 3));
        let target = body.blocks.iter().find(|block| block.id == 3).unwrap();
        assert!(target.params.is_empty());
        assert!(matches!(
            target.terminator,
            Terminator::Return {
                value: Some(Operand {
                    register: 1,
                    mode: UseMode::Move
                })
            }
        ));
        let Terminator::Switch {
            cases, otherwise, ..
        } = &body.blocks[0].terminator
        else {
            unreachable!()
        };
        assert!(cases[0].1.args.is_empty());
        assert!(otherwise.args.is_empty());
    }

    #[test]
    fn normalize_cfg_parameter_elimination_keeps_copy_distinct_loop_and_special_barriers() {
        let make = |left: Operand, right: Operand, role: BlockParamRole, loop_back: bool| {
            let otherwise_target = if loop_back { 0 } else { 1 };
            let entry = block(
                0,
                Terminator::Switch {
                    discr: operand(2),
                    cases: vec![(
                        Constant::U32(0),
                        Edge {
                            target: 1,
                            args: vec![left],
                        },
                    )],
                    otherwise: Edge {
                        target: otherwise_target,
                        args: if loop_back { vec![] } else { vec![right] },
                    },
                },
            );
            let mut target = block(
                1,
                if loop_back {
                    Terminator::Goto(Edge {
                        target: 1,
                        args: vec![move_operand(1)],
                    })
                } else {
                    Terminator::Return {
                        value: Some(move_operand(4)),
                    }
                },
            );
            target.params.push(BlockParam {
                register: 4,
                ty: I64,
                role,
            });
            let mut body = function(vec![entry, target], vec![UNIT, I64, U32, I64, I64]);
            body.params = vec![I64, U32, I64];
            body.result = I64;
            body
        };

        let copy = make(operand(1), operand(1), BlockParamRole::Ordinary, false);
        let distinct = make(
            move_operand(1),
            move_operand(3),
            BlockParamRole::Ordinary,
            false,
        );
        let protected = make(
            move_operand(1),
            move_operand(1),
            BlockParamRole::ProtectedExitValue,
            false,
        );
        let loop_phi = make(
            move_operand(1),
            move_operand(1),
            BlockParamRole::Ordinary,
            true,
        );
        for mut body in [copy, distinct, protected, loop_phi] {
            let liveness = EdgeLiveness::compute(&body, u64::MAX).unwrap();
            assert!(!simplify_identity_block_parameter(&mut body, &liveness, 1));
            assert_eq!(body.blocks[1].params.len(), 1);
        }
    }

    #[test]
    fn normalize_cfg_recomputes_liveness_after_each_parameter_mutation() {
        let mut target = block(
            1,
            Terminator::Return {
                value: Some(move_operand(5)),
            },
        );
        target.params = vec![
            BlockParam {
                register: 3,
                ty: I64,
                role: BlockParamRole::Ordinary,
            },
            BlockParam {
                register: 4,
                ty: I64,
                role: BlockParamRole::Ordinary,
            },
        ];
        target
            .statements
            .push(instruction(InstructionKind::Primitive {
                dst: 5,
                primitive: Primitive::IntCheckedAdd,
                args: vec![move_operand(3), move_operand(4)],
            }));
        let entry = block(
            0,
            Terminator::Switch {
                discr: operand(2),
                cases: vec![(
                    Constant::U32(0),
                    Edge {
                        target: 1,
                        args: vec![move_operand(1), move_operand(6)],
                    },
                )],
                otherwise: Edge {
                    target: 1,
                    args: vec![move_operand(1), move_operand(6)],
                },
            },
        );
        let mut body = function(
            vec![entry, target],
            vec![UNIT, I64, U32, I64, I64, I64, I64],
        );
        body.params = vec![I64, U32, I64, I64, I64, I64];
        body.result = I64;

        let (outcome, _) = normalize_cfg(&mut body, u64::MAX);

        assert_eq!(outcome, PassOutcome::Changed);
        let target = body.blocks.iter().find(|block| block.id == 1).unwrap();
        assert!(target.params.is_empty());
        let InstructionKind::Primitive { args, .. } = &target.statements[0].kind else {
            unreachable!()
        };
        assert_eq!(args, &vec![move_operand(1), move_operand(6)]);
    }

    #[test]
    fn normalize_cfg_splits_switch_critical_edge_but_not_call_normal_edge() {
        let types = Type::predefined();
        let entry = block(
            0,
            Terminator::Switch {
                discr: operand(1),
                cases: vec![(
                    Constant::U32(0),
                    Edge {
                        target: 3,
                        args: vec![operand(2)],
                    },
                )],
                otherwise: Edge {
                    target: 2,
                    args: vec![],
                },
            },
        );
        let call = block(
            2,
            Terminator::Call {
                result: None,
                function: 1,
                args: vec![],
                normal: Edge {
                    target: 3,
                    args: vec![move_operand(2)],
                },
            },
        );
        let mut join = block(3, Terminator::Return { value: None });
        join.params.push(BlockParam {
            register: 3,
            ty: I64,
            role: BlockParamRole::Ordinary,
        });
        join.statements.push(instruction(InstructionKind::Drop {
            owner: move_operand(3),
        }));
        let mut caller = function(
            vec![join, block(9, Terminator::Unreachable), call, entry],
            vec![UNIT, U32, I64, I64],
        );
        caller.declaration = 0;
        caller.params = vec![U32, I64];
        let mut callee = function(
            vec![block(0, Terminator::Return { value: None })],
            vec![UNIT],
        );
        callee.declaration = 1;
        let mut program = Program {
            functions: vec![caller, callee],
        };

        optimize_program(&mut program, &types, OptimizationLevel::O0).unwrap();

        let caller = &program.functions[0];
        let split = caller.blocks.iter().find(|block| block.id == 10).expect(
            "fresh ID follows even a deleted prior maximum, independently of storage order",
        );
        assert_eq!(split.params.len(), 1);
        assert_eq!(split.params[0].register, 4);
        assert_eq!(split.params[0].role, BlockParamRole::Ordinary);
        assert!(matches!(
            split.terminator,
            Terminator::Goto(Edge {
                target: 3,
                ref args
            }) if args == &[move_operand(4)]
        ));
        let switch = caller.blocks.iter().find(|block| block.id == 0).unwrap();
        let Terminator::Switch { cases, .. } = &switch.terminator else {
            unreachable!()
        };
        assert_eq!(cases[0].1.target, 10);
        assert_eq!(cases[0].1.args, [operand(2)]);
        let call = caller.blocks.iter().find(|block| block.id == 2).unwrap();
        assert!(matches!(
            call.terminator,
            Terminator::Call {
                normal: Edge { target: 3, .. },
                ..
            }
        ));
    }

    #[test]
    fn normalize_cfg_budget_exhaustion_is_transactional() {
        let original = function(
            vec![
                block(
                    0,
                    Terminator::Goto(Edge {
                        target: 1,
                        args: vec![],
                    }),
                ),
                block(1, Terminator::Return { value: None }),
                block(9, Terminator::Unreachable),
            ],
            vec![],
        );
        let mut candidate = original.clone();
        let (outcome, _) = normalize_cfg(&mut candidate, 0);
        assert_eq!(outcome, PassOutcome::BudgetExhausted);
        assert_eq!(candidate, original);
    }

    #[test]
    fn sparse_simplify_folds_constant_switch_and_dead_safe_const() {
        let types = Type::predefined();
        let mut entry = block(
            0,
            Terminator::Switch {
                discr: operand(0),
                cases: vec![(
                    Constant::U32(1),
                    Edge {
                        target: 1,
                        args: vec![],
                    },
                )],
                otherwise: Edge {
                    target: 2,
                    args: vec![],
                },
            },
        );
        entry.statements.push(Instruction {
            span: Span::new(0, 0),
            kind: InstructionKind::Const {
                dst: 0,
                value: Constant::U32(1),
            },
        });
        let mut program = program(function(
            vec![
                entry,
                block(1, Terminator::Return { value: None }),
                block(2, Terminator::Return { value: None }),
            ],
            vec![U32],
        ));
        let report = optimize_program(&mut program, &types, OptimizationLevel::O1).unwrap();
        let body = &program.functions[0];
        assert!(!body.features.contains(FeatureBits::SWITCHES));
        assert_eq!(
            body.blocks.len(),
            1,
            "dead switch arm and trivial surviving join must be removed"
        );
        assert!(body.blocks.iter().all(|block| block.statements.is_empty()));
        assert!(report.passes.iter().any(
            |pass| pass.pass == PassId::SparseSimplify && pass.outcome == PassOutcome::Changed
        ));
        assert!(report.passes.iter().any(
            |pass| pass.pass == PassId::NormalizeCfg && pass.outcome == PassOutcome::Changed
        ));
    }

    #[test]
    fn sparse_simplify_preserves_restricted_must_use_constants_and_barriers() {
        let mut types = Type::predefined();
        let restricted = types.len() as TypeId;
        types.push(Type::U32.restricted(true, false));
        let mut entry = block(0, Terminator::Return { value: None });
        entry.statements.push(Instruction {
            span: Span::new(0, 0),
            kind: InstructionKind::Const {
                dst: 0,
                value: Constant::U32(1),
            },
        });
        // Constant values use their frozen representation ID, so a restricted
        // destination is rejected instead of being silently optimized.
        let invalid = program(function(vec![entry], vec![restricted]));
        assert!(validate_program(&invalid, &types, MirPhase::Raw).is_err());
    }

    fn instruction(kind: InstructionKind) -> Instruction {
        Instruction {
            span: Span::new(0, 0),
            kind,
        }
    }

    fn optimize_expression(
        register_types: Vec<TypeId>,
        result: TypeId,
        statements: Vec<Instruction>,
        return_register: Register,
    ) -> Function {
        optimize_expression_at_level(
            register_types,
            result,
            statements,
            return_register,
            OptimizationLevel::O1,
        )
    }

    fn optimize_expression_at_level(
        register_types: Vec<TypeId>,
        result: TypeId,
        statements: Vec<Instruction>,
        return_register: Register,
        level: OptimizationLevel,
    ) -> Function {
        let types = Type::predefined();
        let mut body = function(
            vec![BasicBlock {
                id: 0,
                params: vec![],
                statements,
                terminator: Terminator::Return {
                    value: Some(operand(return_register)),
                },
            }],
            register_types,
        );
        body.result = result;
        let mut program = program(body);
        optimize_program(&mut program, &types, level).unwrap();
        program.functions.pop().unwrap()
    }

    #[test]
    fn deref_move_store_remain_ordered_memory_barriers_at_every_level() {
        let mut types = Type::predefined();
        let unique_i64 = types.len() as TypeId;
        types.push(Type::RefUnique { referent: I64 });

        for level in [
            OptimizationLevel::O0,
            OptimizationLevel::O1,
            OptimizationLevel::O2,
            OptimizationLevel::O3,
        ] {
            let mut body = function(
                vec![BasicBlock {
                    id: 0,
                    params: vec![],
                    statements: vec![
                        instruction(InstructionKind::DerefMove { dst: 3, src: 1 }),
                        instruction(InstructionKind::DerefStore {
                            dst: 1,
                            src: Operand {
                                register: 2,
                                mode: UseMode::Move,
                            },
                        }),
                    ],
                    terminator: Terminator::Return {
                        value: Some(Operand {
                            register: 3,
                            mode: UseMode::Move,
                        }),
                    },
                }],
                vec![UNIT, unique_i64, I64, I64],
            );
            body.params = vec![unique_i64, I64];
            body.result = I64;
            let mut candidate = program(body);
            let report = optimize_program(&mut candidate, &types, level).unwrap();
            let statements = &candidate.functions[0].blocks[0].statements;
            assert_eq!(statements.len(), 2, "{level:?}: {statements:?}");
            assert!(matches!(
                statements[0].kind,
                InstructionKind::DerefMove { .. }
            ));
            assert!(matches!(
                statements[1].kind,
                InstructionKind::DerefStore { .. }
            ));
            if level.at_least(OptimizationLevel::O1) {
                assert!(report.passes.iter().any(|pass| {
                    pass.pass == PassId::SparseSimplify && pass.outcome == PassOutcome::Unchanged
                }));
            }
        }
    }

    #[test]
    fn sparse_simplify_propagates_copy_facts_and_folds_checked_arithmetic() {
        let body = optimize_expression(
            vec![I64, I64, I64, I64],
            I64,
            vec![
                instruction(InstructionKind::Const {
                    dst: 0,
                    value: Constant::I64(40),
                }),
                instruction(InstructionKind::Copy {
                    dst: 1,
                    src: operand(0),
                }),
                instruction(InstructionKind::Const {
                    dst: 2,
                    value: Constant::I64(2),
                }),
                instruction(InstructionKind::Primitive {
                    dst: 3,
                    primitive: Primitive::IntCheckedAdd,
                    args: vec![operand(1), operand(2)],
                }),
            ],
            3,
        );
        assert!(body.blocks[0].statements.iter().any(|statement| matches!(
            statement.kind,
            InstructionKind::Const {
                dst: 3,
                value: Constant::I64(42)
            }
        )));
        // The ownership event remains even though its value fact propagated.
        assert!(
            body.blocks[0]
                .statements
                .iter()
                .any(|statement| matches!(statement.kind, InstructionKind::Copy { dst: 1, .. }))
        );
    }

    #[test]
    fn sparse_simplify_removes_dead_nontrapping_scalar_primitive_chain() {
        let types = Type::predefined();
        let mut body = function(
            vec![BasicBlock {
                id: 0,
                params: vec![],
                statements: vec![
                    instruction(InstructionKind::Primitive {
                        dst: 3,
                        primitive: Primitive::IntBitXor,
                        args: vec![operand(1), operand(2)],
                    }),
                    instruction(InstructionKind::Primitive {
                        dst: 4,
                        primitive: Primitive::IntWrappingAdd,
                        args: vec![operand(3), operand(1)],
                    }),
                    instruction(InstructionKind::Primitive {
                        dst: 5,
                        primitive: Primitive::IntWrappingMul,
                        args: vec![operand(4), operand(2)],
                    }),
                    instruction(InstructionKind::Primitive {
                        dst: 6,
                        primitive: Primitive::IntWrappingNeg,
                        args: vec![operand(5)],
                    }),
                ],
                terminator: Terminator::Return { value: None },
            }],
            vec![UNIT, I64, I64, I64, I64, I64, I64],
        );
        body.params = vec![I64, I64];
        body.features = infer_feature_bits(&body);

        let (outcome, _) = sparse_simplify(&mut body, &types, u64::MAX);

        assert_eq!(outcome, PassOutcome::Changed);
        assert!(body.blocks[0].statements.is_empty());
    }

    #[test]
    fn dead_scalar_primitive_elimination_is_transactional_and_keeps_unsafe_cases() {
        let mut body = function(
            vec![BasicBlock {
                id: 0,
                params: vec![],
                statements: vec![
                    instruction(InstructionKind::Primitive {
                        dst: 3,
                        primitive: Primitive::IntCheckedDiv,
                        args: vec![operand(1), operand(2)],
                    }),
                    instruction(InstructionKind::Primitive {
                        dst: 4,
                        primitive: Primitive::IntBitXor,
                        args: vec![
                            Operand {
                                register: 1,
                                mode: UseMode::Move,
                            },
                            operand(2),
                        ],
                    }),
                    instruction(InstructionKind::Primitive {
                        dst: 5,
                        primitive: Primitive::FloatToIntChecked,
                        args: vec![operand(6)],
                    }),
                ],
                terminator: Terminator::Return { value: None },
            }],
            vec![UNIT, I64, I64, I64, I64, I64, F64],
        );
        body.params = vec![I64, I64];
        let before = body.clone();

        let (outcome, _) = eliminate_dead_nontrapping_scalar_primitives(&mut body, u64::MAX);
        assert_eq!(outcome, PassOutcome::Unchanged);
        assert_eq!(body, before);

        let (outcome, work) = eliminate_dead_nontrapping_scalar_primitives(&mut body, 0);
        assert_eq!(outcome, PassOutcome::BudgetExhausted);
        assert!(work > 0);
        assert_eq!(body, before);
    }

    #[test]
    fn sparse_simplify_applies_proven_integer_identities() {
        #[derive(Clone, Copy)]
        enum Expected {
            Forward,
            Zero,
        }
        let types = Type::predefined();
        let cases = [
            (
                Primitive::IntCheckedAdd,
                Constant::I64(0),
                false,
                Expected::Forward,
            ),
            (
                Primitive::IntCheckedMul,
                Constant::I64(0),
                true,
                Expected::Zero,
            ),
            (
                Primitive::IntCheckedDiv,
                Constant::I64(1),
                false,
                Expected::Forward,
            ),
            (
                Primitive::IntCheckedRem,
                Constant::I64(1),
                false,
                Expected::Zero,
            ),
            (
                Primitive::IntBitAnd,
                Constant::I64(-1),
                false,
                Expected::Forward,
            ),
        ];
        for (primitive, identity, constant_first, expected) in cases {
            let arguments = if constant_first {
                vec![operand(2), operand(1)]
            } else {
                vec![operand(1), operand(2)]
            };
            let mut body = function(
                vec![BasicBlock {
                    id: 0,
                    params: vec![],
                    statements: vec![
                        instruction(InstructionKind::Const {
                            dst: 2,
                            value: identity,
                        }),
                        instruction(InstructionKind::Primitive {
                            dst: 3,
                            primitive,
                            args: arguments,
                        }),
                    ],
                    terminator: Terminator::Return {
                        value: Some(operand(3)),
                    },
                }],
                vec![UNIT, I64, I64, I64],
            );
            body.params = vec![I64];
            body.result = I64;
            body.features = infer_feature_bits(&body);

            let (outcome, _) = sparse_simplify(&mut body, &types, u64::MAX);

            assert_eq!(outcome, PassOutcome::Changed, "{primitive:?}");
            assert!(
                body.blocks[0]
                    .statements
                    .iter()
                    .all(|statement| !matches!(statement.kind, InstructionKind::Primitive { .. }))
            );
            assert!(
                body.blocks[0]
                    .statements
                    .iter()
                    .any(|statement| match expected {
                        Expected::Forward => matches!(
                            statement.kind,
                            InstructionKind::Copy {
                                dst: 3,
                                src: Operand {
                                    register: 1,
                                    mode: UseMode::Copy,
                                },
                            }
                        ),
                        Expected::Zero => matches!(
                            statement.kind,
                            InstructionKind::Const {
                                dst: 3,
                                value: Constant::I64(0),
                            }
                        ),
                    })
            );
        }

        let mut shifted = function(
            vec![BasicBlock {
                id: 0,
                params: vec![],
                statements: vec![
                    instruction(InstructionKind::Const {
                        dst: 2,
                        value: Constant::U32(0),
                    }),
                    instruction(InstructionKind::Primitive {
                        dst: 3,
                        primitive: Primitive::IntShl,
                        args: vec![operand(1), operand(2)],
                    }),
                ],
                terminator: Terminator::Return {
                    value: Some(operand(3)),
                },
            }],
            vec![UNIT, I64, U32, I64],
        );
        shifted.params = vec![I64];
        shifted.result = I64;
        shifted.features = infer_feature_bits(&shifted);
        sparse_simplify(&mut shifted, &types, u64::MAX);
        assert!(matches!(
            shifted.blocks[0].statements.last().unwrap().kind,
            InstructionKind::Copy {
                dst: 3,
                src: Operand { register: 1, .. },
            }
        ));
    }

    #[test]
    fn integer_identity_simplification_keeps_near_traps_and_float_operations() {
        let types = Type::predefined();
        for (primitive, identity) in [
            (Primitive::IntCheckedAdd, Constant::I64(1)),
            (Primitive::IntCheckedDiv, Constant::I64(-1)),
            (Primitive::IntCheckedRem, Constant::I64(-1)),
        ] {
            let mut body = function(
                vec![BasicBlock {
                    id: 0,
                    params: vec![],
                    statements: vec![
                        instruction(InstructionKind::Const {
                            dst: 2,
                            value: identity,
                        }),
                        instruction(InstructionKind::Primitive {
                            dst: 3,
                            primitive,
                            args: vec![operand(1), operand(2)],
                        }),
                    ],
                    terminator: Terminator::Return {
                        value: Some(operand(3)),
                    },
                }],
                vec![UNIT, I64, I64, I64],
            );
            body.params = vec![I64];
            body.result = I64;
            body.features = infer_feature_bits(&body);
            sparse_simplify(&mut body, &types, u64::MAX);
            assert!(body.blocks[0].statements.iter().any(|statement| matches!(
                statement.kind,
                InstructionKind::Primitive { primitive: found, .. } if found == primitive
            )));
        }

        let facts = vec![
            SparseConstant::Unknown,
            SparseConstant::Overdefined,
            SparseConstant::Constant(Constant::I64(0)),
            SparseConstant::Unknown,
        ];
        let moved = simplify_integer_identity(
            3,
            I64,
            Primitive::IntCheckedAdd,
            &[move_operand(1), operand(2)],
            &facts,
            &[UNIT, I64, I64, I64],
        );
        assert!(matches!(
            moved,
            Some(InstructionKind::Move {
                dst: 3,
                src: Operand {
                    register: 1,
                    mode: UseMode::Move,
                },
            })
        ));

        assert!(
            simplify_integer_identity(
                3,
                F64,
                Primitive::FloatAdd,
                &[operand(1), operand(2)],
                &[
                    SparseConstant::Unknown,
                    SparseConstant::Overdefined,
                    SparseConstant::Constant(Constant::F64(0.0)),
                    SparseConstant::Unknown,
                ],
                &[UNIT, F64, F64, F64],
            )
            .is_none()
        );
    }

    #[test]
    fn integer_identity_simplification_covers_every_frozen_width() {
        for ty in [I8, U8, I64, U64, I128, U128, ISIZE, USIZE] {
            let spec = int_spec(ty).unwrap();
            let facts = vec![
                SparseConstant::Unknown,
                SparseConstant::Overdefined,
                SparseConstant::Constant(make_int_constant(ty, int_mask(spec.bits)).unwrap()),
                SparseConstant::Unknown,
            ];
            let rewritten = simplify_integer_identity(
                3,
                ty,
                Primitive::IntBitAnd,
                &[operand(1), operand(2)],
                &facts,
                &[UNIT, ty, ty, ty],
            );
            assert!(
                matches!(
                    rewritten,
                    Some(InstructionKind::Copy {
                        dst: 3,
                        src: Operand { register: 1, .. },
                    })
                ),
                "{ty}"
            );
        }
    }

    #[test]
    fn reflexive_integer_comparisons_fold_without_float_or_ownership_leakage() {
        for ty in [I8, U8, I128, U128, ISIZE, USIZE] {
            for (primitive, expected) in [
                (Primitive::IntEq, 1),
                (Primitive::IntNe, 0),
                (Primitive::IntLt, 0),
                (Primitive::IntLe, 1),
                (Primitive::IntGt, 0),
                (Primitive::IntGe, 1),
            ] {
                let rewritten = simplify_integer_identity(
                    2,
                    U32,
                    primitive,
                    &[operand(1), operand(1)],
                    &[
                        SparseConstant::Unknown,
                        SparseConstant::Overdefined,
                        SparseConstant::Unknown,
                    ],
                    &[UNIT, ty, U32],
                );
                assert!(
                    matches!(
                        rewritten,
                        Some(InstructionKind::Const {
                            dst: 2,
                            value: Constant::U32(value),
                        }) if value == expected
                    ),
                    "{ty} {primitive:?}"
                );
            }
        }

        for (ty, arguments) in [
            (F64, vec![operand(1), operand(1)]),
            (I64, vec![move_operand(1), operand(1)]),
            (I64, vec![operand(1), operand(2)]),
        ] {
            assert!(
                simplify_integer_identity(
                    3,
                    U32,
                    Primitive::IntEq,
                    &arguments,
                    &[
                        SparseConstant::Unknown,
                        SparseConstant::Overdefined,
                        SparseConstant::Overdefined,
                        SparseConstant::Unknown,
                    ],
                    &[UNIT, ty, ty, U32],
                )
                .is_none()
            );
        }
    }

    #[test]
    fn reflexive_integer_comparison_collapses_its_switch_at_o1() {
        let types = Type::predefined();
        let mut body = function(
            vec![
                BasicBlock {
                    id: 0,
                    params: vec![],
                    statements: vec![instruction(InstructionKind::Primitive {
                        dst: 2,
                        primitive: Primitive::IntEq,
                        args: vec![operand(1), operand(1)],
                    })],
                    terminator: Terminator::Switch {
                        discr: operand(2),
                        cases: vec![(
                            Constant::U32(1),
                            Edge {
                                target: 1,
                                args: vec![],
                            },
                        )],
                        otherwise: Edge {
                            target: 2,
                            args: vec![],
                        },
                    },
                },
                block(1, Terminator::Return { value: None }),
                block(2, Terminator::Unreachable),
            ],
            vec![UNIT, I64, U32],
        );
        body.params = vec![I64];
        body.features = infer_feature_bits(&body);
        let raw = program(body);
        let mut o0 = raw.clone();
        optimize_program(&mut o0, &types, OptimizationLevel::O0).unwrap();
        assert!(
            o0.functions[0]
                .blocks
                .iter()
                .any(|block| matches!(block.terminator, Terminator::Switch { .. }))
        );

        let mut o1 = raw;
        optimize_program(&mut o1, &types, OptimizationLevel::O1).unwrap();
        assert!(o1.functions[0].blocks.iter().all(|block| {
            !matches!(block.terminator, Terminator::Switch { .. })
                && block.statements.iter().all(|statement| {
                    !matches!(
                        statement.kind,
                        InstructionKind::Primitive {
                            primitive: Primitive::IntEq,
                            ..
                        }
                    )
                })
        }));
    }

    #[test]
    fn sparse_simplify_propagates_constants_through_block_parameters() {
        let types = Type::predefined();
        let mut entry = block(
            0,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![operand(0)],
            }),
        );
        entry.statements.push(instruction(InstructionKind::Const {
            dst: 0,
            value: Constant::I64(40),
        }));
        let continuation = BasicBlock {
            id: 1,
            params: vec![BlockParam {
                register: 1,
                ty: I64,
                role: BlockParamRole::Ordinary,
            }],
            statements: vec![
                instruction(InstructionKind::Const {
                    dst: 2,
                    value: Constant::I64(2),
                }),
                instruction(InstructionKind::Primitive {
                    dst: 3,
                    primitive: Primitive::IntCheckedAdd,
                    args: vec![operand(1), operand(2)],
                }),
            ],
            terminator: Terminator::Return {
                value: Some(operand(3)),
            },
        };
        let mut body = function(vec![entry, continuation], vec![I64, I64, I64, I64]);
        body.result = I64;
        let mut program = program(body);
        optimize_program(&mut program, &types, OptimizationLevel::O1).unwrap();

        assert!(program.functions[0].blocks.iter().any(|block| {
            block.statements.iter().any(|statement| {
                matches!(
                    statement.kind,
                    InstructionKind::Const {
                        dst: 3,
                        value: Constant::I64(42)
                    }
                )
            })
        }));
    }

    #[test]
    fn sparse_simplify_folds_enum_tags_through_block_parameters() {
        let mut types = Type::predefined();
        let choice = types.len() as TypeId;
        types.push(Type::Enum {
            name: "Choice".into(),
            variants: vec![
                EnumVariant {
                    name: "Left".into(),
                    fields: vec![],
                },
                EnumVariant {
                    name: "Right".into(),
                    fields: vec![],
                },
            ],
            copy: true,
        });
        let mut entry = block(
            0,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![Operand {
                    register: 0,
                    mode: UseMode::Move,
                }],
            }),
        );
        entry
            .statements
            .push(instruction(InstructionKind::Construct {
                dst: 0,
                ty: choice,
                variant: Some(1),
                fields: vec![],
            }));
        let continuation = BasicBlock {
            id: 1,
            params: vec![BlockParam {
                register: 1,
                ty: choice,
                role: BlockParamRole::Ordinary,
            }],
            statements: vec![instruction(InstructionKind::EnumTag { dst: 2, src: 1 })],
            terminator: Terminator::Return {
                value: Some(Operand {
                    register: 2,
                    mode: UseMode::Move,
                }),
            },
        };
        let mut body = function(vec![entry, continuation], vec![choice, choice, U32]);
        body.result = U32;
        let mut program = program(body);
        optimize_program(&mut program, &types, OptimizationLevel::O1).unwrap();

        assert!(program.functions[0].blocks.iter().any(|block| {
            block.statements.iter().any(|statement| {
                matches!(
                    statement.kind,
                    InstructionKind::Const {
                        dst: 2,
                        value: Constant::U32(1)
                    }
                )
            })
        }));
    }

    #[test]
    fn sparse_simplify_does_not_fold_across_a_retained_structural_predecessor() {
        let mut types = Type::predefined();
        let choice = types.len() as TypeId;
        types.push(Type::Enum {
            name: "Choice".into(),
            variants: vec![
                EnumVariant {
                    name: "Left".into(),
                    fields: vec![],
                },
                EnumVariant {
                    name: "Right".into(),
                    fields: vec![],
                },
            ],
            copy: true,
        });
        let predecessor = |id, register, variant| {
            let mut predecessor = block(
                id,
                Terminator::Goto(Edge {
                    target: 2,
                    args: vec![Operand {
                        register,
                        mode: UseMode::Move,
                    }],
                }),
            );
            predecessor
                .statements
                .push(instruction(InstructionKind::Construct {
                    dst: register,
                    ty: choice,
                    variant: Some(variant),
                    fields: vec![],
                }));
            predecessor
        };
        let join = BasicBlock {
            id: 2,
            params: vec![BlockParam {
                register: 2,
                ty: choice,
                role: BlockParamRole::ProtectedExitValue,
            }],
            statements: vec![instruction(InstructionKind::EnumTag { dst: 3, src: 2 })],
            terminator: Terminator::Return {
                value: Some(Operand {
                    register: 3,
                    mode: UseMode::Move,
                }),
            },
        };
        let mut body = function(
            vec![predecessor(0, 0, 0), predecessor(1, 1, 1), join],
            vec![choice, choice, choice, U32],
        );
        body.result = U32;

        let _ = sparse_simplify(&mut body, &types, u64::MAX);

        assert!(body.blocks.iter().any(|block| {
            block.statements.iter().any(|statement| {
                matches!(statement.kind, InstructionKind::EnumTag { dst: 3, src: 2 })
            })
        }));
    }

    #[test]
    fn sparse_simplify_folds_narrow_wrapping_arithmetic() {
        let body = optimize_expression(
            vec![I8, I8, I8],
            I8,
            vec![
                instruction(InstructionKind::Const {
                    dst: 0,
                    value: Constant::I8(127),
                }),
                instruction(InstructionKind::Const {
                    dst: 1,
                    value: Constant::I8(1),
                }),
                instruction(InstructionKind::Primitive {
                    dst: 2,
                    primitive: Primitive::IntWrappingAdd,
                    args: vec![operand(0), operand(1)],
                }),
            ],
            2,
        );
        assert!(body.blocks[0].statements.iter().any(|statement| matches!(
            statement.kind,
            InstructionKind::Const {
                dst: 2,
                value: Constant::I8(-128)
            }
        )));
    }

    #[test]
    fn sparse_simplify_keeps_division_by_zero_and_checked_overflow_traps() {
        for (left, right, primitive) in [
            (1_i8, 0_i8, Primitive::IntCheckedDiv),
            (127_i8, 1_i8, Primitive::IntCheckedAdd),
        ] {
            let body = optimize_expression(
                vec![I8, I8, I8],
                I8,
                vec![
                    instruction(InstructionKind::Const {
                        dst: 0,
                        value: Constant::I8(left),
                    }),
                    instruction(InstructionKind::Const {
                        dst: 1,
                        value: Constant::I8(right),
                    }),
                    instruction(InstructionKind::Primitive {
                        dst: 2,
                        primitive,
                        args: vec![operand(0), operand(1)],
                    }),
                ],
                2,
            );
            assert!(body.blocks[0].statements.iter().any(|statement| matches!(
                statement.kind,
                InstructionKind::Primitive {
                    dst: 2,
                    primitive: retained,
                    ..
                } if retained == primitive
            )));
        }
    }

    #[test]
    fn sparse_simplify_keeps_unsupported_float_conversions() {
        for (source, result, value, primitive) in [
            (F64, F32, Constant::F64(1.25), Primitive::FloatConvert),
            (I64, F64, Constant::I64(7), Primitive::IntToFloat),
            (F64, I64, Constant::F64(7.0), Primitive::FloatToIntChecked),
        ] {
            let body = optimize_expression(
                vec![source, result],
                result,
                vec![
                    instruction(InstructionKind::Const { dst: 0, value }),
                    instruction(InstructionKind::Primitive {
                        dst: 1,
                        primitive,
                        args: vec![operand(0)],
                    }),
                ],
                1,
            );
            assert!(body.blocks[0].statements.iter().any(|statement| matches!(
                statement.kind,
                InstructionKind::Primitive {
                    dst: 1,
                    primitive: retained,
                    ..
                } if retained == primitive
            )));
        }
    }

    #[test]
    fn sparse_float_folding_matches_frozen_ieee_semantics() {
        use Primitive::*;

        for (primitive, expected) in [
            (FloatAdd, 7.5_f32),
            (FloatSub, 3.5_f32),
            (FloatMul, 11.0_f32),
            (FloatDiv, 2.75_f32),
            (FloatRem, 1.5_f32),
        ] {
            assert_eq!(
                fold_primitive(
                    F32,
                    primitive,
                    &[F32, F32],
                    &[Constant::F32(5.5), Constant::F32(2.0)],
                ),
                Some(Constant::F32(expected)),
                "{primitive:?}",
            );
        }
        for (primitive, expected) in [
            (FloatAdd, 7.5_f64),
            (FloatSub, 3.5_f64),
            (FloatMul, 11.0_f64),
            (FloatDiv, 2.75_f64),
            (FloatRem, 1.5_f64),
        ] {
            assert_eq!(
                fold_primitive(
                    F64,
                    primitive,
                    &[F64, F64],
                    &[Constant::F64(5.5), Constant::F64(2.0)],
                ),
                Some(Constant::F64(expected)),
                "{primitive:?}",
            );
        }

        let Some(Constant::F32(negative_zero)) =
            fold_primitive(F32, FloatNeg, &[F32], &[Constant::F32(0.0)])
        else {
            panic!("float negation did not fold")
        };
        assert_eq!(negative_zero.to_bits(), (-0.0_f32).to_bits());
        let Some(Constant::F64(negative_zero)) =
            fold_primitive(F64, FloatNeg, &[F64], &[Constant::F64(0.0)])
        else {
            panic!("f64 negation did not fold")
        };
        assert_eq!(negative_zero.to_bits(), (-0.0_f64).to_bits());

        let Some(Constant::F32(nan32)) = fold_primitive(
            F32,
            FloatDiv,
            &[F32, F32],
            &[Constant::F32(0.0), Constant::F32(0.0)],
        ) else {
            panic!("f32 NaN-producing division did not fold")
        };
        assert_eq!(nan32.to_bits(), 0x7fc0_0000);

        let Some(Constant::F64(nan)) = fold_primitive(
            F64,
            FloatDiv,
            &[F64, F64],
            &[Constant::F64(0.0), Constant::F64(0.0)],
        ) else {
            panic!("NaN-producing division did not fold")
        };
        assert_eq!(nan.to_bits(), 0x7ff8_0000_0000_0000);

        for (ty, args, negative) in [
            (F32, vec![Constant::F32(1.0), Constant::F32(0.0)], false),
            (F64, vec![Constant::F64(-1.0), Constant::F64(0.0)], true),
        ] {
            let folded = fold_primitive(ty, FloatDiv, &[ty, ty], &args);
            match folded {
                Some(Constant::F32(value)) => {
                    assert!(value.is_infinite());
                    assert_eq!(value.is_sign_negative(), negative);
                }
                Some(Constant::F64(value)) => {
                    assert!(value.is_infinite());
                    assert_eq!(value.is_sign_negative(), negative);
                }
                other => panic!("division by zero did not fold: {other:?}"),
            }
        }

        let nan = Constant::F64(f64::from_bits(0x7ff8_0000_0000_0000));
        for (primitive, expected) in [
            (FloatEq, 0),
            (FloatNe, 1),
            (FloatLt, 0),
            (FloatLe, 0),
            (FloatGt, 0),
            (FloatGe, 0),
        ] {
            assert_eq!(
                fold_primitive(
                    U32,
                    primitive,
                    &[F64, F64],
                    &[nan.clone(), Constant::F64(1.0)],
                ),
                Some(Constant::U32(expected)),
                "{primitive:?}",
            );
        }
        let nan32 = Constant::F32(f32::from_bits(0x7fc0_0000));
        for (primitive, expected) in [
            (FloatEq, 0),
            (FloatNe, 1),
            (FloatLt, 0),
            (FloatLe, 0),
            (FloatGt, 0),
            (FloatGe, 0),
        ] {
            assert_eq!(
                fold_primitive(
                    U32,
                    primitive,
                    &[F32, F32],
                    &[nan32.clone(), Constant::F32(1.0)],
                ),
                Some(Constant::U32(expected)),
                "{primitive:?}",
            );
        }
        assert_eq!(
            fold_primitive(
                U32,
                FloatEq,
                &[F32, F32],
                &[Constant::F32(0.0), Constant::F32(-0.0)],
            ),
            Some(Constant::U32(1)),
        );

        assert!(frozen_constant_eq(&nan, &nan));
        assert!(!frozen_constant_eq(
            &Constant::F64(-0.0),
            &Constant::F64(0.0),
        ));
        assert_eq!(
            fold_primitive(F32, FloatConvert, &[F64], &[Constant::F64(1.0)],),
            None,
        );
        assert_eq!(
            fold_primitive(F64, IntToFloat, &[I64], &[Constant::I64(1)],),
            None,
        );
        assert_eq!(
            fold_primitive(I64, FloatToIntChecked, &[F64], &[Constant::F64(1.0)],),
            None,
        );
    }

    #[test]
    fn sparse_folds_allocation_free_text_and_byte_literals() {
        use Primitive::*;

        assert_eq!(
            fold_primitive(
                USIZE,
                TextByteLen,
                &[TEXT],
                &[Constant::Text("grandiose".into())],
            ),
            Some(Constant::Usize(9)),
        );
        assert_eq!(
            fold_primitive(
                U32,
                TextEq,
                &[TEXT, TEXT],
                &[Constant::Text("same".into()), Constant::Text("same".into())],
            ),
            Some(Constant::U32(1)),
        );
        assert_eq!(
            fold_primitive(
                USIZE,
                BytesLen,
                &[BYTES],
                &[Constant::Bytes(vec![0, 1, 2])],
            ),
            Some(Constant::Usize(3)),
        );
        assert_eq!(
            fold_primitive(
                USIZE,
                BytesUtf8ValidUpTo,
                &[BYTES],
                &[Constant::Bytes(b"a\xc2".to_vec())],
            ),
            Some(Constant::Usize(1)),
        );
    }

    #[test]
    fn sparse_simplify_rewrites_float_primitives_to_canonical_constants() {
        for level in [
            OptimizationLevel::O1,
            OptimizationLevel::O2,
            OptimizationLevel::O3,
        ] {
            let folded = optimize_expression_at_level(
                vec![F64, F64, F64],
                F64,
                vec![
                    instruction(InstructionKind::Const {
                        dst: 0,
                        value: Constant::F64(1.25),
                    }),
                    instruction(InstructionKind::Const {
                        dst: 1,
                        value: Constant::F64(2.5),
                    }),
                    instruction(InstructionKind::Primitive {
                        dst: 2,
                        primitive: Primitive::FloatAdd,
                        args: vec![operand(0), operand(1)],
                    }),
                ],
                2,
                level,
            );
            assert!(folded.blocks[0].statements.iter().any(|statement| matches!(
                statement.kind,
                InstructionKind::Const {
                    dst: 2,
                    value: Constant::F64(3.75),
                }
            )));
            assert!(
                folded.blocks[0]
                    .statements
                    .iter()
                    .all(|statement| !matches!(
                        statement.kind,
                        InstructionKind::Primitive {
                            primitive: Primitive::FloatAdd,
                            ..
                        }
                    ))
            );
        }

        let nan = optimize_expression(
            vec![F32, F32, F32],
            F32,
            vec![
                instruction(InstructionKind::Const {
                    dst: 0,
                    value: Constant::F32(0.0),
                }),
                instruction(InstructionKind::Const {
                    dst: 1,
                    value: Constant::F32(0.0),
                }),
                instruction(InstructionKind::Primitive {
                    dst: 2,
                    primitive: Primitive::FloatDiv,
                    args: vec![operand(0), operand(1)],
                }),
            ],
            2,
        );
        let Some(Constant::F32(value)) =
            nan.blocks[0]
                .statements
                .iter()
                .find_map(|statement| match &statement.kind {
                    InstructionKind::Const { dst: 2, value } => Some(value.clone()),
                    _ => None,
                })
        else {
            panic!("NaN-producing primitive was not replaced with a constant")
        };
        assert_eq!(value.to_bits(), 0x7fc0_0000);
    }

    #[test]
    fn sparse_switch_selection_uses_frozen_float_bits() {
        let mut entry = block(
            0,
            Terminator::Switch {
                discr: operand(0),
                cases: vec![
                    (
                        Constant::F64(0.0),
                        Edge {
                            target: 1,
                            args: vec![],
                        },
                    ),
                    (
                        Constant::F64(-0.0),
                        Edge {
                            target: 2,
                            args: vec![],
                        },
                    ),
                ],
                otherwise: Edge {
                    target: 3,
                    args: vec![],
                },
            },
        );
        entry.statements.push(instruction(InstructionKind::Const {
            dst: 0,
            value: Constant::F64(-0.0),
        }));
        let mut body = function(
            vec![
                entry,
                block(1, Terminator::Return { value: None }),
                block(2, Terminator::Return { value: None }),
                block(3, Terminator::Return { value: None }),
            ],
            vec![F64],
        );
        body.features = infer_feature_bits(&body);
        let types = Type::predefined();
        assert_eq!(
            sparse_simplify(&mut body, &types, u64::MAX).0,
            PassOutcome::Changed,
        );
        assert!(matches!(
            body.blocks[0].terminator,
            Terminator::Goto(Edge { target: 2, .. })
        ));
    }

    #[test]
    fn local_forwarding_collapses_same_block_scalar_move_aliases_and_keeps_drop() {
        let mut body = function(
            vec![BasicBlock {
                id: 0,
                params: vec![],
                statements: vec![
                    instruction(InstructionKind::Move {
                        dst: 2,
                        src: move_operand(1),
                    }),
                    instruction(InstructionKind::Move {
                        dst: 3,
                        src: move_operand(2),
                    }),
                    instruction(InstructionKind::Drop {
                        owner: move_operand(3),
                    }),
                ],
                terminator: Terminator::Return { value: None },
            }],
            vec![UNIT, I64, I64, I64],
        );
        body.params = vec![I64];
        body.features = infer_feature_bits(&body);

        let (outcome, _) = local_forward_moves(&mut body, u64::MAX);

        assert_eq!(outcome, PassOutcome::Changed);
        assert!(matches!(
            body.blocks[0].statements.as_slice(),
            [Instruction {
                kind: InstructionKind::Drop {
                    owner: Operand {
                        register: 1,
                        mode: UseMode::Move
                    }
                },
                ..
            }]
        ));

        let types = Type::predefined();
        let mut scheduled = function(
            vec![BasicBlock {
                id: 0,
                params: vec![],
                statements: vec![
                    instruction(InstructionKind::Move {
                        dst: 2,
                        src: move_operand(1),
                    }),
                    instruction(InstructionKind::Drop {
                        owner: move_operand(2),
                    }),
                ],
                terminator: Terminator::Return { value: None },
            }],
            vec![UNIT, I64, I64],
        );
        scheduled.params = vec![I64];
        let mut program = program(scheduled);
        optimize_program(&mut program, &types, OptimizationLevel::O1).unwrap();
        assert!(matches!(
            program.functions[0].blocks[0].statements.as_slice(),
            [Instruction {
                kind: InstructionKind::Drop {
                    owner: Operand { register: 1, .. }
                },
                ..
            }]
        ));
    }

    #[test]
    fn local_forwarding_keeps_copy_cleanup_capture_cross_block_and_redefinition_barriers() {
        let make_local = |statements: Vec<Instruction>| {
            let mut body = function(
                vec![BasicBlock {
                    id: 0,
                    params: vec![],
                    statements,
                    terminator: Terminator::Return { value: None },
                }],
                vec![UNIT, I64, I64, I64],
            );
            body.params = vec![I64];
            body.features = infer_feature_bits(&body);
            body
        };

        let copy = make_local(vec![
            instruction(InstructionKind::Copy {
                dst: 2,
                src: operand(1),
            }),
            instruction(InstructionKind::Drop {
                owner: move_operand(2),
            }),
        ]);

        let mut cleanup = make_local(vec![instruction(InstructionKind::Move {
            dst: 2,
            src: move_operand(1),
        })]);
        cleanup.return_cleanup.push(2);

        let capture = make_local(vec![
            instruction(InstructionKind::Move {
                dst: 2,
                src: move_operand(1),
            }),
            instruction(InstructionKind::MakeCallable {
                dst: 3,
                callable_type: UNIT,
                function: 0,
                captures: vec![move_operand(2)],
            }),
        ]);

        let mut cross_block = function(
            vec![
                BasicBlock {
                    id: 0,
                    params: vec![],
                    statements: vec![instruction(InstructionKind::Move {
                        dst: 2,
                        src: move_operand(1),
                    })],
                    terminator: Terminator::Goto(Edge {
                        target: 1,
                        args: vec![],
                    }),
                },
                BasicBlock {
                    id: 1,
                    params: vec![],
                    statements: vec![instruction(InstructionKind::Drop {
                        owner: move_operand(2),
                    })],
                    terminator: Terminator::Return { value: None },
                },
            ],
            vec![UNIT, I64, I64],
        );
        cross_block.params = vec![I64];
        cross_block.features = infer_feature_bits(&cross_block);

        let redefinition = make_local(vec![
            instruction(InstructionKind::Move {
                dst: 2,
                src: move_operand(1),
            }),
            instruction(InstructionKind::Const {
                dst: 1,
                value: Constant::I64(7),
            }),
            instruction(InstructionKind::Drop {
                owner: move_operand(2),
            }),
        ]);

        for mut body in [copy, cleanup, capture, cross_block, redefinition] {
            let original = body.clone();
            assert_eq!(
                local_forward_moves(&mut body, u64::MAX).0,
                PassOutcome::Unchanged
            );
            assert_eq!(body, original);
        }
    }

    #[test]
    fn local_forwarding_keeps_custom_type_and_loan_barriers() {
        let custom = Type::predefined().len() as TypeId;
        let mut custom_body = function(
            vec![BasicBlock {
                id: 0,
                params: vec![],
                statements: vec![
                    instruction(InstructionKind::Move {
                        dst: 2,
                        src: move_operand(1),
                    }),
                    instruction(InstructionKind::Drop {
                        owner: move_operand(2),
                    }),
                ],
                terminator: Terminator::Return { value: None },
            }],
            vec![UNIT, custom, custom],
        );
        custom_body.params = vec![custom];
        custom_body.features = infer_feature_bits(&custom_body);

        let mut loan_body = function(
            vec![BasicBlock {
                id: 0,
                params: vec![],
                statements: vec![
                    instruction(InstructionKind::Move {
                        dst: 2,
                        src: move_operand(1),
                    }),
                    instruction(InstructionKind::Borrow {
                        dst: 3,
                        src: 2,
                        unique: false,
                    }),
                    instruction(InstructionKind::EndBorrow { reference: 3 }),
                    instruction(InstructionKind::Drop {
                        owner: move_operand(2),
                    }),
                ],
                terminator: Terminator::Return { value: None },
            }],
            vec![UNIT, I64, I64, UNIT],
        );
        loan_body.params = vec![I64];
        loan_body.features = infer_feature_bits(&loan_body);

        for mut body in [custom_body, loan_body] {
            let original = body.clone();
            assert_eq!(
                local_forward_moves(&mut body, u64::MAX).0,
                PassOutcome::Unchanged
            );
            assert_eq!(body, original);
        }
    }

    #[test]
    fn o2_self_tail_backedge_uses_fresh_temporaries_for_parallel_swaps() {
        let types = Type::predefined();
        let mut body = function(
            vec![block(
                0,
                Terminator::TailCall {
                    function: 0,
                    args: vec![
                        Operand {
                            register: 2,
                            mode: UseMode::Move,
                        },
                        Operand {
                            register: 1,
                            mode: UseMode::Move,
                        },
                    ],
                },
            )],
            vec![UNIT, I64, I64],
        );
        body.params = vec![I64, I64];
        body.features = infer_feature_bits(&body);
        let mut program = program(body);
        let report = optimize_program(&mut program, &types, OptimizationLevel::O2).unwrap();
        let body = &program.functions[0];
        assert_eq!(body.register_types, [UNIT, I64, I64, I64, I64]);
        assert_eq!(body.blocks[0].statements.len(), 4);
        assert!(matches!(
            body.blocks[0].statements[0].kind,
            InstructionKind::Move {
                dst: 3,
                src: Operand { register: 2, .. }
            }
        ));
        assert!(matches!(
            body.blocks[0].statements[1].kind,
            InstructionKind::Move {
                dst: 4,
                src: Operand { register: 1, .. }
            }
        ));
        assert!(matches!(
            body.blocks[0].statements[2].kind,
            InstructionKind::Move {
                dst: 1,
                src: Operand { register: 3, .. }
            }
        ));
        assert!(matches!(
            body.blocks[0].statements[3].kind,
            InstructionKind::Move {
                dst: 2,
                src: Operand { register: 4, .. }
            }
        ));
        assert!(matches!(
            body.blocks[0].terminator,
            Terminator::Goto(Edge {
                target: 0,
                ref args
            }) if args.is_empty()
        ));
        assert!(
            report.passes.iter().any(|pass| {
                pass.pass == PassId::FormTailCallsAndHoist && pass.outcome == PassOutcome::Changed
            }),
            "{:#?}",
            report.passes
        );
    }

    fn direct_tail_discovery_fixture() -> Function {
        let mut entry = block(
            0,
            Terminator::Call {
                result: Some(2),
                function: 1,
                args: vec![move_operand(1)],
                normal: Edge {
                    target: 1,
                    args: vec![],
                },
            },
        );
        entry.params = vec![];
        let continuation = BasicBlock {
            id: 1,
            params: vec![BlockParam {
                register: 2,
                ty: I64,
                role: BlockParamRole::CallResult,
            }],
            statements: vec![],
            terminator: Terminator::Return {
                value: Some(move_operand(2)),
            },
        };
        let mut body = function(vec![entry, continuation], vec![UNIT, I64, I64]);
        body.params = vec![I64];
        body.result = I64;
        body.features = infer_feature_bits(&body);
        body
    }

    #[test]
    fn o2_discovers_exact_direct_tail_continuations_and_keeps_nonself_calls() {
        let mut body = direct_tail_discovery_fixture();
        let (outcome, _) =
            form_tail_calls_and_hoist(&mut body, &Type::predefined(), &BTreeSet::new(), u64::MAX);
        assert_eq!(outcome, PassOutcome::Changed);
        assert!(matches!(
            body.blocks[0].terminator,
            Terminator::TailCall {
                function: 1,
                ref args,
            } if args == &[move_operand(1)]
        ));
    }

    #[test]
    fn tail_discovery_retains_an_installed_self_receiver() {
        let entry = block(
            0,
            Terminator::CallSelf {
                result: Some(2),
                args: vec![move_operand(1)],
                normal: Edge {
                    target: 1,
                    args: vec![],
                },
            },
        );
        let continuation = BasicBlock {
            id: 1,
            params: vec![BlockParam {
                register: 2,
                ty: I64,
                role: BlockParamRole::CallResult,
            }],
            statements: vec![],
            terminator: Terminator::Return {
                value: Some(move_operand(2)),
            },
        };
        let mut body = function(vec![entry, continuation], vec![UNIT, I64, I64]);
        body.receiver_mode = Some(0);
        body.receiver_type = UNIT;
        body.params = vec![I64];
        body.result = I64;
        body.features = infer_feature_bits(&body);

        assert_eq!(
            discover_tail_calls(&mut body, &Type::predefined(), &BTreeSet::new(), u64::MAX,).0,
            PassOutcome::Changed
        );
        assert!(matches!(
            body.blocks[0].terminator,
            Terminator::TailCallSelf { ref args } if args == &[move_operand(1)]
        ));
    }

    #[test]
    fn tail_discovery_follows_a_unique_cleanup_free_forwarding_chain() {
        let mut body = direct_tail_discovery_fixture();
        body.register_types.push(I64);
        body.blocks[1].terminator = Terminator::Goto(Edge {
            target: 2,
            args: vec![move_operand(2)],
        });
        body.blocks.push(BasicBlock {
            id: 2,
            params: vec![BlockParam {
                register: 3,
                ty: I64,
                role: BlockParamRole::Ordinary,
            }],
            statements: vec![],
            terminator: Terminator::Return {
                value: Some(move_operand(3)),
            },
        });

        assert_eq!(
            discover_tail_calls(&mut body, &Type::predefined(), &BTreeSet::new(), u64::MAX,).0,
            PassOutcome::Changed
        );
        assert!(matches!(
            body.blocks[0].terminator,
            Terminator::TailCall { function: 1, .. }
        ));

        let mut shared_join = direct_tail_discovery_fixture();
        shared_join.register_types.push(I64);
        shared_join.blocks[1].terminator = Terminator::Goto(Edge {
            target: 2,
            args: vec![move_operand(2)],
        });
        shared_join.blocks.push(BasicBlock {
            id: 2,
            params: vec![BlockParam {
                register: 3,
                ty: I64,
                role: BlockParamRole::Ordinary,
            }],
            statements: vec![],
            terminator: Terminator::Return {
                value: Some(move_operand(3)),
            },
        });
        shared_join.blocks.push(block(
            3,
            Terminator::Goto(Edge {
                target: 2,
                args: vec![move_operand(1)],
            }),
        ));
        assert_eq!(
            discover_tail_calls(
                &mut shared_join,
                &Type::predefined(),
                &BTreeSet::new(),
                u64::MAX,
            )
            .0,
            PassOutcome::Changed,
            "a shared terminal return does not keep the caller frame alive"
        );
    }

    #[test]
    fn tail_discovery_discards_cleanup_free_values_through_a_shared_return() {
        let types = Type::predefined();
        let mut body = direct_tail_discovery_fixture();
        body.register_types
            .extend([I64, U32, I64, I64, U32, I64, I64]);
        body.blocks[0]
            .statements
            .push(instruction(InstructionKind::Const {
                dst: 3,
                value: Constant::I64(9),
            }));
        body.blocks[0]
            .statements
            .push(instruction(InstructionKind::Const {
                dst: 4,
                value: Constant::U32(7),
            }));
        body.blocks[1].terminator = Terminator::Goto(Edge {
            target: 2,
            args: vec![move_operand(2), operand(3), operand(4)],
        });
        body.blocks.push(BasicBlock {
            id: 2,
            params: vec![
                BlockParam {
                    register: 5,
                    ty: I64,
                    role: BlockParamRole::ProtectedExitValue,
                },
                BlockParam {
                    register: 6,
                    ty: I64,
                    role: BlockParamRole::Ordinary,
                },
                BlockParam {
                    register: 7,
                    ty: U32,
                    role: BlockParamRole::Ordinary,
                },
            ],
            statements: vec![],
            terminator: Terminator::Goto(Edge {
                target: 5,
                args: vec![move_operand(5)],
            }),
        });
        body.blocks.push(block(
            3,
            Terminator::Goto(Edge {
                target: 2,
                args: vec![move_operand(1), move_operand(3), move_operand(4)],
            }),
        ));
        body.blocks.push(BasicBlock {
            id: 4,
            params: vec![BlockParam {
                register: 8,
                ty: I64,
                role: BlockParamRole::ProtectedExitValue,
            }],
            statements: vec![],
            terminator: Terminator::Return {
                value: Some(move_operand(8)),
            },
        });
        body.blocks.push(BasicBlock {
            id: 5,
            params: vec![BlockParam {
                register: 9,
                ty: I64,
                role: BlockParamRole::ProtectedExitValue,
            }],
            statements: vec![
                instruction(InstructionKind::Drop {
                    owner: move_operand(7),
                }),
                instruction(InstructionKind::Drop {
                    owner: move_operand(6),
                }),
                instruction(InstructionKind::LabelPop { label: LabelId(0) }),
            ],
            terminator: Terminator::Goto(Edge {
                target: 4,
                args: vec![move_operand(9)],
            }),
        });
        body.flow.locals = body
            .register_types
            .iter()
            .map(|ty| crate::compiler_mir::LocalFact::conservative(*ty, &types[*ty as usize]))
            .collect();

        assert_eq!(
            discover_tail_calls(&mut body, &types, &BTreeSet::new(), u64::MAX).0,
            PassOutcome::Changed
        );
        assert!(matches!(
            body.blocks[0].terminator,
            Terminator::TailCall { function: 1, .. }
        ));
        assert!(matches!(
            body.blocks[0].statements.as_slice(),
            [
                _,
                _,
                Instruction {
                    kind: InstructionKind::Drop {
                        owner: Operand { register: 4, .. },
                    },
                    ..
                },
                Instruction {
                    kind: InstructionKind::Drop {
                        owner: Operand { register: 3, .. },
                    },
                    ..
                },
                Instruction {
                    kind: InstructionKind::LabelPop { label: LabelId(0) },
                    ..
                },
            ]
        ));
    }

    #[test]
    fn o2_hoists_nontrapping_scalar_loop_invariants_to_a_unique_preheader() {
        let mut body = function(
            vec![
                block(
                    0,
                    Terminator::Goto(Edge {
                        target: 1,
                        args: vec![],
                    }),
                ),
                block(
                    1,
                    Terminator::Switch {
                        discr: operand(1),
                        cases: vec![(
                            Constant::U32(0),
                            Edge {
                                target: 3,
                                args: vec![],
                            },
                        )],
                        otherwise: Edge {
                            target: 2,
                            args: vec![],
                        },
                    },
                ),
                BasicBlock {
                    id: 2,
                    params: vec![],
                    statements: vec![instruction(InstructionKind::Primitive {
                        dst: 3,
                        primitive: Primitive::IntBitXor,
                        args: vec![operand(2), operand(2)],
                    })],
                    terminator: Terminator::Goto(Edge {
                        target: 1,
                        args: vec![],
                    }),
                },
                block(3, Terminator::Return { value: None }),
            ],
            vec![UNIT, U32, I64, I64],
        );
        body.params = vec![U32, I64];
        body.features = infer_feature_bits(&body);

        let (outcome, _) =
            form_tail_calls_and_hoist(&mut body, &Type::predefined(), &BTreeSet::new(), u64::MAX);

        assert_eq!(outcome, PassOutcome::Changed);
        assert!(matches!(
            body.blocks[0].statements.as_slice(),
            [Instruction {
                kind: InstructionKind::Primitive {
                    dst: 3,
                    primitive: Primitive::IntBitXor,
                    ..
                },
                ..
            }]
        ));
        assert!(body.blocks[2].statements.is_empty());
    }

    #[test]
    fn scheduled_o2_licm_preserves_validated_ownership_and_cleanup_flow() {
        let types = Type::predefined();
        let mut body = function(
            vec![
                block(
                    0,
                    Terminator::Goto(Edge {
                        target: 1,
                        args: vec![],
                    }),
                ),
                block(
                    1,
                    Terminator::Switch {
                        discr: operand(1),
                        cases: vec![(
                            Constant::U32(0),
                            Edge {
                                target: 3,
                                args: vec![],
                            },
                        )],
                        otherwise: Edge {
                            target: 2,
                            args: vec![],
                        },
                    },
                ),
                BasicBlock {
                    id: 2,
                    params: vec![],
                    statements: vec![instruction(InstructionKind::Primitive {
                        dst: 3,
                        primitive: Primitive::IntWrappingAdd,
                        args: vec![operand(2), operand(2)],
                    })],
                    terminator: Terminator::Switch {
                        discr: operand(3),
                        cases: vec![(
                            Constant::I64(0),
                            Edge {
                                target: 1,
                                args: vec![],
                            },
                        )],
                        otherwise: Edge {
                            target: 3,
                            args: vec![],
                        },
                    },
                },
                block(3, Terminator::Return { value: None }),
            ],
            vec![UNIT, U32, I64, I64],
        );
        body.params = vec![U32, I64];
        body.features = infer_feature_bits(&body);
        let mut program = program(body);

        let report = optimize_program(&mut program, &types, OptimizationLevel::O2).unwrap();
        assert!(
            report.passes.iter().any(|pass| {
                pass.pass == PassId::FormTailCallsAndHoist && pass.outcome == PassOutcome::Changed
            }),
            "{:#?}",
            report.passes
        );
        let body = &program.functions[0];
        let entry = body
            .blocks
            .iter()
            .find(|block| block.id == body.entry)
            .expect("LICM entry preheader exists");
        assert!(entry.statements.iter().any(|statement| matches!(
            statement.kind,
            InstructionKind::Primitive {
                dst: 3,
                primitive: Primitive::IntWrappingAdd,
                ..
            }
        )));
        assert!(body.blocks[2].statements.is_empty());
        validate_program(&program, &types, MirPhase::Optimized).unwrap();
    }

    #[test]
    fn loop_hoisting_keeps_traps_and_loop_defined_inputs_in_place() {
        let fixture = |primitive, args| {
            let mut body = function(
                vec![
                    block(
                        0,
                        Terminator::Goto(Edge {
                            target: 1,
                            args: vec![],
                        }),
                    ),
                    block(
                        1,
                        Terminator::Goto(Edge {
                            target: 2,
                            args: vec![],
                        }),
                    ),
                    BasicBlock {
                        id: 2,
                        params: vec![],
                        statements: vec![
                            instruction(InstructionKind::Primitive {
                                dst: 3,
                                primitive: Primitive::IntBitXor,
                                args: vec![operand(2), operand(2)],
                            }),
                            instruction(InstructionKind::Primitive {
                                dst: 4,
                                primitive,
                                args,
                            }),
                        ],
                        terminator: Terminator::Goto(Edge {
                            target: 1,
                            args: vec![],
                        }),
                    },
                ],
                vec![UNIT, U32, I64, I64, I64],
            );
            body.params = vec![U32, I64];
            body.features = infer_feature_bits(&body);
            body
        };

        let mut trapping = fixture(Primitive::IntCheckedAdd, vec![operand(2), operand(2)]);
        assert_eq!(
            hoist_loop_invariant_primitives(&mut trapping, u64::MAX).0,
            PassOutcome::Changed,
            "the independent xor still hoists"
        );
        assert!(matches!(
            trapping.blocks[2].statements.as_slice(),
            [Instruction {
                kind: InstructionKind::Primitive {
                    primitive: Primitive::IntCheckedAdd,
                    ..
                },
                ..
            }]
        ));

        let mut dependent = fixture(Primitive::IntBitXor, vec![operand(3), operand(2)]);
        assert_eq!(
            hoist_loop_invariant_primitives(&mut dependent, u64::MAX).0,
            PassOutcome::Changed,
            "the independent xor still hoists"
        );
        assert!(matches!(
            dependent.blocks[2].statements.as_slice(),
            [Instruction {
                kind: InstructionKind::Primitive { dst: 4, .. },
                ..
            }]
        ));
    }

    #[test]
    fn tail_discovery_rejects_live_owners_cleanup_multi_pred_and_explicit_edges() {
        let mut live = direct_tail_discovery_fixture();
        live.register_types.push(I64);
        live.blocks[0]
            .statements
            .push(instruction(InstructionKind::Const {
                dst: 3,
                value: Constant::I64(9),
            }));
        assert_eq!(
            discover_tail_calls(&mut live, &Type::predefined(), &BTreeSet::new(), u64::MAX,).0,
            PassOutcome::Unchanged
        );

        let mut cleanup = direct_tail_discovery_fixture();
        cleanup.blocks[1]
            .statements
            .push(instruction(InstructionKind::Drop {
                owner: move_operand(0),
            }));
        assert_eq!(
            discover_tail_calls(
                &mut cleanup,
                &Type::predefined(),
                &BTreeSet::new(),
                u64::MAX,
            )
            .0,
            PassOutcome::Unchanged
        );

        let mut multi_pred = direct_tail_discovery_fixture();
        multi_pred.blocks.push(block(
            2,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![],
            }),
        ));
        assert_eq!(
            discover_tail_calls(
                &mut multi_pred,
                &Type::predefined(),
                &BTreeSet::new(),
                u64::MAX,
            )
            .0,
            PassOutcome::Unchanged
        );

        let mut explicit = direct_tail_discovery_fixture();
        explicit.register_types.push(I64);
        let Terminator::Call { normal, .. } = &mut explicit.blocks[0].terminator else {
            unreachable!()
        };
        normal.args.push(move_operand(1));
        explicit.blocks[1].params.push(BlockParam {
            register: 3,
            ty: I64,
            role: BlockParamRole::Ordinary,
        });
        assert_eq!(
            discover_tail_calls(
                &mut explicit,
                &Type::predefined(),
                &BTreeSet::new(),
                u64::MAX,
            )
            .0,
            PassOutcome::Unchanged
        );
    }

    #[test]
    fn indirect_tail_discovery_requires_an_owned_consumed_receiver() {
        let fixture = |receiver_mode, callable_mode, cleanup_callable| {
            let entry = block(
                0,
                Terminator::CallIndirect {
                    result: Some(2),
                    callable: Operand {
                        register: 1,
                        mode: callable_mode,
                    },
                    known_function: Some(7),
                    receiver_mode,
                    cleanup_callable,
                    args: vec![],
                    normal: Edge {
                        target: 1,
                        args: vec![],
                    },
                },
            );
            let continuation = BasicBlock {
                id: 1,
                params: vec![BlockParam {
                    register: 2,
                    ty: I64,
                    role: BlockParamRole::CallResult,
                }],
                statements: vec![],
                terminator: Terminator::Return {
                    value: Some(move_operand(2)),
                },
            };
            let mut body = function(vec![entry, continuation], vec![UNIT, UNIT, I64]);
            body.params = vec![UNIT];
            body.result = I64;
            body.features = infer_feature_bits(&body);
            body
        };

        let mut owned = fixture(2, UseMode::Move, false);
        assert_eq!(
            discover_tail_calls(&mut owned, &Type::predefined(), &BTreeSet::new(), u64::MAX,).0,
            PassOutcome::Changed
        );
        assert!(matches!(
            owned.blocks[0].terminator,
            Terminator::TailCallIndirect {
                receiver_mode: 2,
                callable: Operand {
                    mode: UseMode::Move,
                    ..
                },
                ..
            }
        ));

        for mut barrier in [
            fixture(0, UseMode::Copy, true),
            fixture(1, UseMode::Copy, true),
            fixture(2, UseMode::Move, true),
        ] {
            assert_eq!(
                discover_tail_calls(
                    &mut barrier,
                    &Type::predefined(),
                    &BTreeSet::new(),
                    u64::MAX,
                )
                .0,
                PassOutcome::Unchanged
            );
        }
    }

    #[test]
    fn tail_discovery_forms_an_exact_owned_resume_edge() {
        let entry = block(
            0,
            Terminator::Resume {
                result: 3,
                resumption: move_operand(1),
                receiver_mode: 2,
                value: move_operand(2),
                normal: Edge {
                    target: 1,
                    args: vec![],
                },
            },
        );
        let continuation = BasicBlock {
            id: 1,
            params: vec![BlockParam {
                register: 3,
                ty: I64,
                role: BlockParamRole::ResumeResult,
            }],
            statements: vec![],
            terminator: Terminator::Return {
                value: Some(move_operand(3)),
            },
        };
        let mut body = function(vec![entry, continuation], vec![UNIT, UNIT, I64, I64]);
        body.params = vec![UNIT, I64];
        body.result = I64;
        body.receiver_mode = Some(2);
        body.receiver_type = UNIT;
        body.features = infer_feature_bits(&body);

        assert_eq!(
            discover_tail_calls(&mut body, &Type::predefined(), &BTreeSet::new(), u64::MAX,).0,
            PassOutcome::Changed
        );
        assert!(matches!(
            body.blocks[0].terminator,
            Terminator::TailResume {
                receiver_mode: 2,
                resumption: Operand {
                    register: 1,
                    mode: UseMode::Move,
                },
                value: Operand {
                    register: 2,
                    mode: UseMode::Move,
                },
            }
        ));

        let mut with_live_owner = body;
        with_live_owner.blocks[0].terminator = Terminator::Resume {
            result: 3,
            resumption: move_operand(1),
            receiver_mode: 2,
            value: move_operand(2),
            normal: Edge {
                target: 1,
                args: vec![],
            },
        };
        with_live_owner.register_types.push(I64);
        with_live_owner.blocks[0]
            .statements
            .push(instruction(InstructionKind::Const {
                dst: 4,
                value: Constant::I64(9),
            }));
        assert_eq!(
            discover_tail_calls(
                &mut with_live_owner,
                &Type::predefined(),
                &BTreeSet::new(),
                u64::MAX,
            )
            .0,
            PassOutcome::Unchanged
        );
    }

    #[test]
    fn mandatory_lowering_erases_nested_proof_only_loans_at_o0() {
        let mut types = Type::predefined();
        let shared_i64 = types.len() as TypeId;
        types.push(Type::RefShared { referent: I64 });
        let mut entry = block(0, Terminator::Return { value: None });
        entry.statements = vec![
            instruction(InstructionKind::Const {
                dst: 0,
                value: Constant::I64(7),
            }),
            instruction(InstructionKind::Borrow {
                dst: 1,
                src: 0,
                unique: false,
            }),
            instruction(InstructionKind::Reborrow {
                dst: 2,
                src: 1,
                unique: false,
            }),
            instruction(InstructionKind::EndBorrow { reference: 2 }),
            instruction(InstructionKind::EndBorrow { reference: 1 }),
        ];
        let mut program = program(function(vec![entry], vec![I64, shared_i64, shared_i64]));
        let report = optimize_program(&mut program, &types, OptimizationLevel::O0).unwrap();

        assert!(!program.functions[0].features.contains(FeatureBits::LOANS));
        assert!(
            program.functions[0].blocks[0]
                .statements
                .iter()
                .all(|statement| !matches!(
                    statement.kind,
                    InstructionKind::Borrow { .. }
                        | InstructionKind::ProjectBorrow { .. }
                        | InstructionKind::Reborrow { .. }
                        | InstructionKind::EndBorrow { .. }
                ))
        );
        assert!(report.passes.iter().any(|pass| {
            pass.pass == PassId::EraseLoanProofsAndScalarizedReferences
                && pass.outcome == PassOutcome::Changed
        }));

        // Exported provenance intentionally survives the proof-erasure pass.
        // Mandatory physical lowering must compact those historical facts
        // rather than trying to allocate their now-dead reference registers.
        use crate::compiler_mir::{LoanFact, LoanKind, Place, SourceInfoId};
        program.functions[0].flow.loans = vec![
            LoanFact {
                kind: LoanKind::Shared,
                reference: 1,
                borrowed: Place {
                    base: 0,
                    projection: vec![],
                },
                parent: None,
                region: RegionId(0),
                issued_block: 0,
                source: SourceInfoId(0),
            },
            LoanFact {
                kind: LoanKind::Shared,
                reference: 2,
                borrowed: Place {
                    base: 1,
                    projection: vec![],
                },
                parent: Some(LoanId(0)),
                region: RegionId(1),
                issued_block: 0,
                source: SourceInfoId(0),
            },
        ];
        compact_live_registers_for_emission(&mut program, &types).unwrap();
        assert!(program.functions[0].flow.loans.is_empty());
    }

    #[test]
    fn loan_erasure_preserves_every_continuation_capture_kind() {
        let capture_variants = [
            ContinuationCapture {
                captured_owners: vec![1],
                captured_references: vec![],
                captured_residuals: vec![],
                cancellation_safe: true,
            },
            ContinuationCapture {
                captured_owners: vec![],
                captured_references: vec![1],
                captured_residuals: vec![],
                cancellation_safe: true,
            },
            ContinuationCapture {
                captured_owners: vec![],
                captured_references: vec![],
                captured_residuals: vec![ResidualCapture {
                    register: 1,
                    initialized_fields: vec![true],
                }],
                cancellation_safe: true,
            },
        ];
        for capture in capture_variants {
            let mut entry = block(
                0,
                Terminator::Perform {
                    result: None,
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                    capture,
                    resume: None,
                },
            );
            entry.statements = vec![
                instruction(InstructionKind::Borrow {
                    dst: 1,
                    src: 0,
                    unique: false,
                }),
                instruction(InstructionKind::EndBorrow { reference: 1 }),
            ];
            let mut body = function(vec![entry], vec![I64, I64]);
            body.features = infer_feature_bits(&body);

            let (outcome, _) = erase_loan_proofs(&mut body, u64::MAX);
            assert_eq!(outcome, PassOutcome::Unchanged);
            assert!(matches!(
                body.blocks[0].statements[0].kind,
                InstructionKind::Borrow { dst: 1, .. }
            ));
        }
    }

    #[test]
    fn o2_self_tail_backedge_keeps_frame_replacement_across_loan_barriers() {
        let mut types = Type::predefined();
        let shared_i64 = types.len() as TypeId;
        types.push(Type::RefShared { referent: I64 });
        let mut body = function(
            vec![BasicBlock {
                id: 0,
                params: vec![],
                statements: vec![
                    Instruction {
                        span: Span::new(0, 0),
                        kind: InstructionKind::Borrow {
                            dst: 2,
                            src: 1,
                            unique: false,
                        },
                    },
                    Instruction {
                        span: Span::new(0, 0),
                        kind: InstructionKind::Copy {
                            dst: 3,
                            src: Operand {
                                register: 2,
                                mode: UseMode::Copy,
                            },
                        },
                    },
                    Instruction {
                        span: Span::new(0, 0),
                        kind: InstructionKind::EndBorrow { reference: 3 },
                    },
                    Instruction {
                        span: Span::new(0, 0),
                        kind: InstructionKind::EndBorrow { reference: 2 },
                    },
                ],
                terminator: Terminator::TailCall {
                    function: 0,
                    args: vec![Operand {
                        register: 1,
                        mode: UseMode::Move,
                    }],
                },
            }],
            vec![UNIT, I64, shared_i64, shared_i64],
        );
        body.params = vec![I64];
        body.features = infer_feature_bits(&body);
        let mut program = program(body);
        optimize_program(&mut program, &types, OptimizationLevel::O2).unwrap();
        assert!(matches!(
            program.functions[0].blocks[0].terminator,
            Terminator::TailCall { function: 0, .. }
        ));
    }

    #[test]
    fn fixed_schedule_reports_control_pass_and_is_deterministic() {
        let types = Type::predefined();
        let original = program(function(
            vec![block(0, Terminator::Return { value: None })],
            vec![],
        ));
        let mut first = original.clone();
        let mut second = original;
        let a = optimize_program(&mut first, &types, OptimizationLevel::O2).unwrap();
        let b = optimize_program(&mut second, &types, OptimizationLevel::O2).unwrap();
        assert_eq!(a, b);
        assert_eq!(first, second);
        assert_eq!(first.functions[0].phase, MirPhase::Optimized);
        assert!(
            a.passes
                .iter()
                .any(|pass| pass.pass == PassId::SpecializeControl
                    && pass.outcome == PassOutcome::Unchanged)
        );
    }

    #[test]
    fn static_handler_specialization_budget_exhaustion_is_transactional() {
        let types = Type::predefined();
        let mut candidate = program(function(
            vec![block(0, Terminator::Return { value: None })],
            vec![],
        ));
        let original = candidate.clone();
        assert_eq!(
            specialize_static_handlers(&mut candidate, &types, &[], &[], 0),
            (PassOutcome::BudgetExhausted, 0)
        );
        assert_eq!(candidate, original);
    }

    #[test]
    fn scheduler_accepts_compiler_produced_tail_and_ownership_mir() {
        let source = r#"
            struct Scratch { marker: i64 }
            impl Use<[0,1]> for Scratch {}
            leaf() -> i64 { 42 }
            forward(value: Scratch) -> i64 { leaf() }
            main() -> { () }
        "#;
        let phases = crate::compile_source_to_phases_with_options(
            "optimizer-input.glorious",
            source,
            crate::CompileOptions {
                optimization_level: OptimizationLevel::O0,
            },
        )
        .unwrap();
        let mut program = phases.mir;
        for function in &mut program.functions {
            function.phase = MirPhase::Raw;
            function.features = FeatureBits::empty();
        }
        let report =
            optimize_program(&mut program, &phases.artifact.types, OptimizationLevel::O1).unwrap();
        assert!(
            program
                .functions
                .iter()
                .all(|body| body.phase == MirPhase::Optimized)
        );
        assert!(report.final_operations <= report.initial_operations);
    }

    fn move_operand(register: Register) -> Operand {
        Operand {
            register,
            mode: UseMode::Move,
        }
    }

    fn scalarizable_tuple_body(tuple: TypeId) -> Function {
        let mut entry = block(
            0,
            Terminator::Return {
                value: Some(operand(3)),
            },
        );
        entry.statements = vec![
            instruction(InstructionKind::Const {
                dst: 0,
                value: Constant::I64(20),
            }),
            instruction(InstructionKind::Const {
                dst: 1,
                value: Constant::I64(22),
            }),
            instruction(InstructionKind::Construct {
                dst: 2,
                ty: tuple,
                variant: None,
                fields: vec![move_operand(0), move_operand(1)],
            }),
            instruction(InstructionKind::ProjectCopy {
                dst: 3,
                src: operand(2),
                field: 0,
            }),
            instruction(InstructionKind::ProjectMove {
                dst: 4,
                src: move_operand(2),
                field: 1,
            }),
            instruction(InstructionKind::ProjectMove {
                dst: 5,
                src: move_operand(2),
                field: 0,
            }),
            instruction(InstructionKind::Deconstruct { src: 2 }),
        ];
        let mut body = function(vec![entry], vec![I64, I64, tuple, I64, I64, I64]);
        body.result = I64;
        body
    }

    #[test]
    fn o1_scalarizes_complete_nonescaping_tuple_and_preserves_partial_move_order() {
        let mut types = Type::predefined();
        let tuple = types.len() as TypeId;
        types.push(Type::Tuple {
            fields: vec![I64, I64],
            copy: true,
        });
        let mut program = program(scalarizable_tuple_body(tuple));

        let report = optimize_program(&mut program, &types, OptimizationLevel::O1).unwrap();
        let body = &program.functions[0];
        assert!(report.passes.iter().any(|pass| {
            pass.pass == PassId::ScalarizeLocals && pass.outcome == PassOutcome::Changed
        }));
        assert!(!body.blocks[0].statements.iter().any(|statement| matches!(
            statement.kind,
            InstructionKind::Construct { .. }
                | InstructionKind::ProjectCopy { .. }
                | InstructionKind::ProjectMove { .. }
                | InstructionKind::Deconstruct { .. }
        )));
        let scalar_zero = 6;
        let scalar_one = 7;
        assert!(matches!(
            body.blocks[0].statements[2].kind,
            InstructionKind::Move {
                dst,
                src: Operand { register: 0, mode: UseMode::Move }
            } if dst == scalar_zero
        ));
        assert!(matches!(
            body.blocks[0].statements[3].kind,
            InstructionKind::Move {
                dst,
                src: Operand { register: 1, mode: UseMode::Move }
            } if dst == scalar_one
        ));
        assert!(matches!(
            body.blocks[0].statements[4].kind,
            InstructionKind::Copy {
                dst: 3,
                src: Operand { register, mode: UseMode::Copy }
            } if register == scalar_zero
        ));
        assert!(matches!(
            body.blocks[0].statements[5].kind,
            InstructionKind::Move {
                dst: 4,
                src: Operand { register, mode: UseMode::Move }
            } if register == scalar_one
        ));
        assert!(matches!(
            body.blocks[0].statements[6].kind,
            InstructionKind::Move {
                dst: 5,
                src: Operand { register, mode: UseMode::Move }
            } if register == scalar_zero
        ));
    }

    #[test]
    fn scalarize_locals_keeps_incomplete_post_move_and_loan_drop_escape_barriers() {
        let mut types = Type::predefined();
        let tuple = types.len() as TypeId;
        types.push(Type::Tuple {
            fields: vec![I64, I64],
            copy: true,
        });
        let shared_tuple = types.len() as TypeId;
        types.push(Type::RefShared { referent: tuple });

        let mut incomplete = scalarizable_tuple_body(tuple);
        incomplete.blocks[0].statements.remove(4); // field 1 is never transferred

        let mut post_move = scalarizable_tuple_body(tuple);
        post_move.blocks[0].statements.swap(3, 5); // copy field 0 after its move

        let mut loan = scalarizable_tuple_body(tuple);
        loan.register_types.push(shared_tuple);
        loan.blocks[0].statements.insert(
            3,
            instruction(InstructionKind::Borrow {
                dst: 6,
                src: 2,
                unique: false,
            }),
        );
        loan.blocks[0]
            .statements
            .insert(4, instruction(InstructionKind::EndBorrow { reference: 6 }));

        let mut drop_exposed = scalarizable_tuple_body(tuple);
        drop_exposed.blocks[0].statements.insert(
            3,
            instruction(InstructionKind::Drop {
                owner: move_operand(2),
            }),
        );

        for body in [incomplete, post_move, loan, drop_exposed] {
            let mut candidate = program(body);
            let report = optimize_program(&mut candidate, &types, OptimizationLevel::O1).unwrap();
            assert!(
                candidate.functions[0].blocks[0]
                    .statements
                    .iter()
                    .any(|statement| matches!(statement.kind, InstructionKind::Construct { .. }))
            );
            assert!(report.passes.iter().any(|pass| {
                pass.pass == PassId::ScalarizeLocals && pass.outcome == PassOutcome::Unchanged
            }));
        }
    }

    #[test]
    fn simplify_cleanup_shares_exact_tails_without_erasing_dynamic_drop() {
        let types = Type::predefined();
        let mut entry = block(
            0,
            Terminator::Switch {
                discr: operand(2),
                cases: vec![(
                    Constant::U32(0),
                    Edge {
                        target: 1,
                        args: vec![],
                    },
                )],
                otherwise: Edge {
                    target: 2,
                    args: vec![],
                },
            },
        );
        // Keep the switch discriminator live and unknown to SparseSimplify.
        entry.statements.clear();
        let mut first = block(1, Terminator::Return { value: None });
        first.statements.push(Instruction {
            span: Span::new(1, 2),
            kind: InstructionKind::Drop {
                owner: move_operand(1),
            },
        });
        let mut second = block(2, Terminator::Return { value: None });
        second.statements.push(Instruction {
            // This compact MIR can share only when the retained operation's
            // source information is identical on every incoming path.
            span: Span::new(1, 2),
            kind: InstructionKind::Drop {
                owner: move_operand(1),
            },
        });
        let mut body = function(vec![entry, first, second], vec![UNIT, I64, U32]);
        body.params = vec![I64, U32];
        let mut program = program(body);

        let report = optimize_program(&mut program, &types, OptimizationLevel::O1).unwrap();
        let body = &program.functions[0];
        assert_eq!(body.blocks.len(), 2);
        assert_eq!(
            body.blocks
                .iter()
                .flat_map(|block| &block.statements)
                .filter(|statement| matches!(statement.kind, InstructionKind::Drop { .. }))
                .count(),
            1,
            "one statically shared tail still executes one Drop on either path"
        );
        let Terminator::Switch {
            cases, otherwise, ..
        } = &body.blocks[0].terminator
        else {
            panic!("unknown discriminator must retain the switch");
        };
        assert_eq!(cases[0].1.target, otherwise.target);
        assert!(report.passes.iter().any(|pass| {
            pass.pass == PassId::SimplifyCleanup && pass.outcome == PassOutcome::Changed
        }));
    }

    fn empty_drop_fixture(drop_glue: DropGlueKind) -> Program {
        let types = Type::predefined();
        let mut entry = block(0, Terminator::Return { value: None });
        entry.statements.push(instruction(InstructionKind::Drop {
            owner: move_operand(1),
        }));
        let mut body = function(vec![entry], vec![UNIT, UNIT]);
        body.params = vec![UNIT];
        body.flow.provenance = FlowProvenance::Exported;
        let receiver = LocalFact::conservative(UNIT, &types[UNIT as usize]);
        let mut parameter = LocalFact::conservative(UNIT, &types[UNIT as usize]);
        parameter.kind = crate::compiler_mir::LocalKind::Parameter(0);
        parameter.initial = crate::compiler_mir::InitAtEntry::Initialized;
        parameter.drop_glue = drop_glue;
        parameter.use_interval = crate::compiler_mir::UseInterval::UNRESTRICTED;
        body.flow.locals = vec![receiver, parameter];
        program(body)
    }

    #[test]
    fn simplify_cleanup_erases_only_proven_empty_zero_use_drops_and_dead_flags() {
        let types = Type::predefined();
        let mut candidate = empty_drop_fixture(DropGlueKind::None);
        candidate.functions[0]
            .flow
            .drop_flags
            .push(crate::compiler_mir::DropFlagFact {
                flag: 0,
                owner: 1,
                field: None,
            });
        candidate.functions[0].return_cleanup.push(1);

        let report = optimize_program(&mut candidate, &types, OptimizationLevel::O2).unwrap();
        let body = &candidate.functions[0];
        assert!(body.blocks[0].statements.is_empty());
        assert!(body.return_cleanup.is_empty());
        assert!(body.flow.drop_flags.is_empty());
        assert!(
            body.flow
                .cleanup_plans
                .iter()
                .all(|plan| plan.actions.is_empty())
        );
        assert!(report.passes.iter().any(|pass| {
            pass.pass == PassId::SimplifyCleanup && pass.outcome == PassOutcome::Changed
        }));

        let mut custom = empty_drop_fixture(DropGlueKind::Custom);
        optimize_program(&mut custom, &types, OptimizationLevel::O2).unwrap();
        assert!(matches!(
            custom.functions[0].blocks[0].statements[0].kind,
            InstructionKind::Drop { .. }
        ));
    }

    #[test]
    fn cleanup_simplification_preserves_structural_containers_with_custom_children() {
        let mut types = Type::predefined();
        let child = types.len() as TypeId;
        types.push(Type::Struct {
            name: "CustomChild".into(),
            fields: vec![Field {
                name: "marker".into(),
                ty: I64,
            }],
            copy: true,
        });
        let parent = types.len() as TypeId;
        types.push(Type::Struct {
            name: "StructuralParent".into(),
            fields: vec![Field {
                name: "child".into(),
                ty: child,
            }],
            copy: true,
        });
        let mut entry = block(0, Terminator::Return { value: None });
        entry.statements.push(instruction(InstructionKind::Drop {
            owner: move_operand(1),
        }));
        let mut body = function(vec![entry], vec![UNIT, parent, child]);
        body.params = vec![parent];
        body.flow.provenance = FlowProvenance::Exported;
        let receiver = LocalFact::conservative(UNIT, &types[UNIT as usize]);
        let mut parent_fact = LocalFact::conservative(parent, &types[parent as usize]);
        parent_fact.kind = crate::compiler_mir::LocalKind::Parameter(0);
        parent_fact.initial = crate::compiler_mir::InitAtEntry::Initialized;
        parent_fact.drop_glue = DropGlueKind::Structural;
        parent_fact.use_interval = crate::compiler_mir::UseInterval::UNRESTRICTED;
        let mut child_fact = LocalFact::conservative(child, &types[child as usize]);
        child_fact.drop_glue = DropGlueKind::Custom;
        body.flow.locals = vec![receiver, parent_fact, child_fact];
        let mut candidate = program(body);

        optimize_program(&mut candidate, &types, OptimizationLevel::O2).unwrap();
        assert!(matches!(
            candidate.functions[0].blocks[0].statements[0].kind,
            InstructionKind::Drop { .. }
        ));
        assert_eq!(
            candidate.functions[0].flow.locals[1].drop_glue,
            DropGlueKind::Structural,
            "the container remains structurally destructible rather than becoming a direct hook"
        );
    }

    #[test]
    fn cleanup_optimization_does_not_mask_drop_after_move_malformed_flow() {
        let types = Type::predefined();
        let mut candidate = empty_drop_fixture(DropGlueKind::None);
        candidate.functions[0].register_types.push(UNIT);
        let mut temporary = LocalFact::conservative(UNIT, &types[UNIT as usize]);
        temporary.drop_glue = DropGlueKind::None;
        candidate.functions[0].flow.locals.push(temporary);
        candidate.functions[0].blocks[0].statements.insert(
            0,
            instruction(InstructionKind::Move {
                dst: 2,
                src: move_operand(1),
            }),
        );

        let error = optimize_program(&mut candidate, &types, OptimizationLevel::O2).unwrap_err();
        assert!(
            error.message.contains("unavailable")
                || error.message.contains("moved")
                || error.message.contains("uninitialized"),
            "{error}"
        );
    }

    #[test]
    fn simplify_cleanup_keeps_ordered_and_protected_cleanup_tails_distinct() {
        let mut ordered_left = block(1, Terminator::Return { value: None });
        ordered_left.statements.extend([
            instruction(InstructionKind::Drop {
                owner: move_operand(1),
            }),
            instruction(InstructionKind::Drop {
                owner: move_operand(2),
            }),
        ]);
        let mut ordered_right = block(2, Terminator::Return { value: None });
        ordered_right.statements.extend([
            instruction(InstructionKind::Drop {
                owner: move_operand(2),
            }),
            instruction(InstructionKind::Drop {
                owner: move_operand(1),
            }),
        ]);
        let mut protected_left = ordered_left.clone();
        protected_left.id = 3;
        protected_left.params.push(BlockParam {
            register: 3,
            ty: I64,
            role: BlockParamRole::ProtectedExitValue,
        });
        let mut protected_right = protected_left.clone();
        protected_right.id = 4;

        let mut body = function(
            vec![ordered_left, ordered_right, protected_left, protected_right],
            vec![UNIT, I64, I64, I64],
        );
        body.entry = 1;
        body.features = infer_feature_bits(&body);
        let (outcome, _) =
            simplify_cleanup(&mut body, &Type::predefined(), &BTreeSet::new(), u64::MAX);

        assert_eq!(outcome, PassOutcome::Unchanged);
        assert_eq!(body.blocks.len(), 4);
        assert_eq!(
            body.blocks[0].statements[0].kind,
            InstructionKind::Drop {
                owner: move_operand(1)
            }
        );
        assert_eq!(
            body.blocks[1].statements[0].kind,
            InstructionKind::Drop {
                owner: move_operand(2)
            }
        );
    }

    #[test]
    fn simplify_cleanup_preserves_distinct_destroy_source_information() {
        let mut first = block(1, Terminator::Return { value: None });
        first.statements.push(Instruction {
            span: Span::new(1, 2),
            kind: InstructionKind::Drop {
                owner: move_operand(1),
            },
        });
        let mut second = block(2, Terminator::Return { value: None });
        second.statements.push(Instruction {
            span: Span::new(10, 20),
            kind: InstructionKind::Drop {
                owner: move_operand(1),
            },
        });
        let mut body = function(vec![first, second], vec![UNIT, I64]);
        body.entry = 1;
        body.features = infer_feature_bits(&body);

        let (outcome, _) =
            simplify_cleanup(&mut body, &Type::predefined(), &BTreeSet::new(), u64::MAX);

        assert_eq!(outcome, PassOutcome::Unchanged);
        assert_eq!(body.blocks.len(), 2);
        assert_eq!(body.blocks[0].statements[0].span, Span::new(1, 2));
        assert_eq!(body.blocks[1].statements[0].span, Span::new(10, 20));
    }

    fn cleanup_suffix_fixture() -> Function {
        let mut entry = block(
            0,
            Terminator::Switch {
                discr: operand(4),
                cases: vec![(
                    Constant::U32(0),
                    Edge {
                        target: 1,
                        args: vec![],
                    },
                )],
                otherwise: Edge {
                    target: 2,
                    args: vec![],
                },
            },
        );
        entry.statements.clear();
        let mut left = block(1, Terminator::Return { value: None });
        left.statements.extend([
            instruction(InstructionKind::Drop {
                owner: move_operand(1),
            }),
            instruction(InstructionKind::Drop {
                owner: move_operand(2),
            }),
        ]);
        let mut right = block(2, Terminator::Return { value: None });
        right.statements.extend([
            instruction(InstructionKind::Drop {
                owner: move_operand(3),
            }),
            instruction(InstructionKind::Drop {
                owner: move_operand(2),
            }),
        ]);
        let mut body = function(vec![entry, left, right], vec![UNIT, I64, I64, I64, U32]);
        body.params = vec![I64, I64, I64, U32];
        body.features = infer_feature_bits(&body);
        body
    }

    fn cleanup_trace(function: &Function, first_case: bool) -> Vec<Register> {
        let entry = function
            .blocks
            .iter()
            .find(|block| block.id == function.entry)
            .unwrap();
        let Terminator::Switch {
            cases, otherwise, ..
        } = &entry.terminator
        else {
            panic!("fixture entry must remain a Switch")
        };
        let mut current = if first_case {
            cases[0].1.target
        } else {
            otherwise.target
        };
        let mut trace = Vec::new();
        let mut visited = BTreeSet::new();
        loop {
            assert!(visited.insert(current), "cleanup trace must be acyclic");
            let block = function
                .blocks
                .iter()
                .find(|block| block.id == current)
                .unwrap();
            trace.extend(block.statements.iter().map(|statement| {
                let InstructionKind::Drop { owner } = statement.kind else {
                    panic!("cleanup fixture contains only Drop statements")
                };
                owner.register
            }));
            match &block.terminator {
                Terminator::Goto(edge) => current = edge.target,
                Terminator::Return { .. } => return trace,
                other => panic!("unexpected cleanup terminator {other:?}"),
            }
        }
    }

    #[test]
    fn o2_specialize_cleanup_factors_longest_suffix_without_erasing_drop() {
        let types = Type::predefined();
        let original = cleanup_suffix_fixture();
        let expected = [
            cleanup_trace(&original, true),
            cleanup_trace(&original, false),
        ];
        let mut candidate = program(original);

        let report = optimize_program(&mut candidate, &types, OptimizationLevel::O2).unwrap();
        let optimized = &candidate.functions[0];

        assert_eq!(cleanup_trace(optimized, true), expected[0]);
        assert_eq!(cleanup_trace(optimized, false), expected[1]);
        assert_eq!(
            optimized
                .blocks
                .iter()
                .flat_map(|block| &block.statements)
                .filter(|statement| matches!(statement.kind, InstructionKind::Drop { .. }))
                .count(),
            3,
            "four path-local Drops become three static instructions, not fewer dynamic Drops"
        );
        assert_eq!(
            optimized
                .blocks
                .iter()
                .filter(|block| {
                    block.statements.as_slice()
                        == [instruction(InstructionKind::Drop {
                            owner: move_operand(2),
                        })]
                })
                .count(),
            1
        );
        assert!(report.passes.iter().any(|pass| {
            pass.pass == PassId::SpecializeCleanup && pass.outcome == PassOutcome::Changed
        }));
    }

    #[test]
    fn specialize_cleanup_is_transactional_deterministic_and_keeps_barriers() {
        let base = cleanup_suffix_fixture();
        let mut first = base.clone();
        let mut second = base.clone();
        let types = Type::predefined();
        let first_result = specialize_cleanup(&mut first, &types, u64::MAX);
        let second_result = specialize_cleanup(&mut second, &types, u64::MAX);
        assert_eq!(first, second);
        assert_eq!(first_result, second_result);

        let mut exhausted = base.clone();
        let before = exhausted.clone();
        assert_eq!(
            specialize_cleanup(&mut exhausted, &types, 0).0,
            PassOutcome::BudgetExhausted
        );
        assert_eq!(exhausted, before);

        let mut different_span = base.clone();
        different_span.blocks[2].statements[1].span = Span::new(10, 20);
        assert_eq!(
            specialize_cleanup(&mut different_span, &types, u64::MAX).0,
            PassOutcome::Unchanged
        );

        let mut protected = base.clone();
        protected.blocks[2].params.push(BlockParam {
            register: 5,
            ty: I64,
            role: BlockParamRole::ProtectedExitValue,
        });
        protected.register_types.push(I64);
        assert_eq!(
            specialize_cleanup(&mut protected, &types, u64::MAX).0,
            PassOutcome::Unchanged
        );

        let mut different_order = base.clone();
        different_order.blocks[2].statements.reverse();
        assert_eq!(
            specialize_cleanup(&mut different_order, &types, u64::MAX).0,
            PassOutcome::Unchanged
        );

        let mut cyclic = base;
        cyclic.blocks[1].terminator = Terminator::Goto(Edge {
            target: 1,
            args: vec![],
        });
        cyclic.blocks[2].terminator = cyclic.blocks[1].terminator.clone();
        assert_eq!(
            specialize_cleanup(&mut cyclic, &types, u64::MAX).0,
            PassOutcome::Unchanged
        );
    }

    fn inline_leaf_fixture() -> (Program, Vec<Type>) {
        let types = Type::predefined();
        let mut entry = block(
            0,
            Terminator::Call {
                result: Some(3),
                function: 1,
                args: vec![move_operand(1), move_operand(2)],
                normal: Edge {
                    target: 1,
                    args: vec![move_operand(4)],
                },
            },
        );
        entry.statements = vec![
            instruction(InstructionKind::Const {
                dst: 1,
                value: Constant::I64(40),
            }),
            instruction(InstructionKind::Const {
                dst: 2,
                value: Constant::I64(2),
            }),
            instruction(InstructionKind::Const {
                dst: 4,
                value: Constant::I64(9),
            }),
        ];
        let continuation = BasicBlock {
            id: 1,
            params: vec![
                BlockParam {
                    register: 3,
                    ty: I64,
                    role: BlockParamRole::CallResult,
                },
                BlockParam {
                    register: 5,
                    ty: I64,
                    role: BlockParamRole::Ordinary,
                },
            ],
            statements: vec![],
            terminator: Terminator::Return {
                value: Some(move_operand(3)),
            },
        };
        let mut caller = function(
            vec![entry, continuation],
            vec![UNIT, I64, I64, I64, I64, I64],
        );
        caller.declaration = 0;
        caller.name = "inline-caller".into();
        caller.result = I64;
        caller.features = infer_feature_bits(&caller);

        let mut leaf = block(
            0,
            Terminator::Return {
                value: Some(move_operand(3)),
            },
        );
        leaf.statements.push(Instruction {
            span: Span::new(10, 20),
            kind: InstructionKind::Primitive {
                dst: 3,
                primitive: Primitive::IntCheckedAdd,
                args: vec![operand(1), operand(2)],
            },
        });
        let mut callee = function(vec![leaf], vec![UNIT, I64, I64, I64]);
        callee.declaration = 1;
        callee.name = "inline-leaf".into();
        callee.params = vec![I64, I64];
        callee.result = I64;
        callee.features = infer_feature_bits(&callee);
        (
            Program {
                functions: vec![caller, callee],
            },
            types,
        )
    }

    #[test]
    fn inline_by_cost_remaps_leaf_and_prepends_implicit_call_result() {
        let (mut candidate, types) = inline_leaf_fixture();
        let (outcome, work) = inline_by_cost(&mut candidate, OptimizationLevel::O2, u64::MAX);
        assert_eq!(outcome, PassOutcome::Changed);
        assert!(work > operation_count(&candidate));
        let caller = &candidate.functions[0];
        assert_eq!(&caller.register_types[6..], &[I64, I64, I64]);
        assert!(matches!(
            caller.blocks[0].statements[3].kind,
            InstructionKind::Move {
                dst: 6,
                src: Operand {
                    register: 1,
                    mode: UseMode::Move
                }
            }
        ));
        assert!(matches!(
            caller.blocks[0].statements[4].kind,
            InstructionKind::Move { dst: 7, .. }
        ));
        assert_eq!(caller.blocks[0].statements[5].span, Span::new(10, 20));
        assert!(matches!(
            caller.blocks[0].statements[5].kind,
            InstructionKind::Primitive { dst: 8, .. }
        ));
        assert_eq!(
            caller.blocks[0].terminator,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![move_operand(8), move_operand(4)],
            })
        );
        validate_program(&candidate, &types, MirPhase::Raw).unwrap();
    }

    #[test]
    fn forwarding_direct_call_specialization_reuses_the_moved_argument() {
        let (mut candidate, types) = inline_leaf_fixture();
        let callee = &mut candidate.functions[1];
        callee.blocks[0].statements.clear();
        callee.blocks[0].terminator = Terminator::Return {
            value: Some(move_operand(1)),
        };

        assert_eq!(
            specialize_forwarding_direct_calls(&mut candidate, u64::MAX).0,
            PassOutcome::Changed
        );
        let caller = &candidate.functions[0];
        assert_eq!(caller.blocks[0].statements.len(), 3);
        assert_eq!(
            caller.blocks[0].terminator,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![move_operand(1), move_operand(4)],
            })
        );
        validate_program(&candidate, &types, MirPhase::Raw).unwrap();
    }

    #[test]
    fn o1_specializes_forwarding_direct_calls_without_inlining() {
        let (mut candidate, types) = inline_leaf_fixture();
        let callee = &mut candidate.functions[1];
        callee.blocks[0].statements.clear();
        callee.blocks[0].terminator = Terminator::Return {
            value: Some(move_operand(1)),
        };

        let report = optimize_program(&mut candidate, &types, OptimizationLevel::O1).unwrap();
        assert!(matches!(
            candidate.functions[0].blocks[0].terminator,
            Terminator::Goto(_)
        ));
        assert!(report.passes.iter().any(|pass| {
            pass.pass == PassId::SpecializeDirectCalls && pass.outcome == PassOutcome::Changed
        }));
    }

    #[test]
    fn o1_specializes_constant_returning_direct_calls() {
        let (mut candidate, types) = inline_leaf_fixture();
        let callee = &mut candidate.functions[1];
        callee.params.clear();
        callee.register_types = vec![UNIT, I64];
        callee.blocks[0].statements = vec![instruction(InstructionKind::Const {
            dst: 1,
            value: Constant::I64(42),
        })];
        callee.blocks[0].terminator = Terminator::Return {
            value: Some(move_operand(1)),
        };
        let Terminator::Call { args, .. } = &mut candidate.functions[0].blocks[0].terminator else {
            unreachable!()
        };
        args.clear();

        let report = optimize_program(&mut candidate, &types, OptimizationLevel::O1).unwrap();
        let caller = &candidate.functions[0];
        assert!(matches!(
            caller.blocks[0].statements.last().map(|statement| &statement.kind),
            Some(InstructionKind::Const {
                dst: 6,
                value: Constant::I64(42),
            })
        ));
        assert_eq!(
            caller.blocks[0].terminator,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![move_operand(6), move_operand(4)],
            })
        );
        assert!(report.passes.iter().any(|pass| {
            pass.pass == PassId::SpecializeDirectCalls && pass.outcome == PassOutcome::Changed
        }));
    }

    #[test]
    fn specializes_constant_arguments_through_direct_primitive_call() {
        let (mut candidate, types) = inline_leaf_fixture();
        let callee = &mut candidate.functions[1];
        callee.blocks[0].statements = vec![instruction(InstructionKind::Primitive {
            dst: 3,
            primitive: Primitive::IntCheckedAdd,
            args: vec![operand(1), operand(2)],
        })];
        callee.blocks[0].terminator = Terminator::Return {
            value: Some(move_operand(3)),
        };

        assert_eq!(
            specialize_forwarding_direct_calls(&mut candidate, u64::MAX).0,
            PassOutcome::Changed
        );
        let caller = &candidate.functions[0];
        assert!(matches!(
            caller.blocks[0].statements.last().map(|statement| &statement.kind),
            Some(InstructionKind::Const {
                dst: 6,
                value: Constant::I64(42),
            })
        ));
        assert_eq!(
            caller.blocks[0].terminator,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![move_operand(6), move_operand(4)],
            })
        );
        validate_program(&candidate, &types, MirPhase::Raw).unwrap();
    }

    #[test]
    fn specializes_constant_argument_through_direct_primitive_with_callee_literal() {
        let (mut candidate, types) = inline_leaf_fixture();
        let callee = &mut candidate.functions[1];
        callee.params = vec![I64];
        callee.register_types = vec![UNIT, I64, I64, I64];
        callee.blocks[0].statements = vec![
            instruction(InstructionKind::Const {
                dst: 2,
                value: Constant::I64(1),
            }),
            instruction(InstructionKind::Primitive {
                dst: 3,
                primitive: Primitive::IntCheckedAdd,
                args: vec![operand(1), operand(2)],
            }),
        ];
        callee.blocks[0].terminator = Terminator::Return {
            value: Some(move_operand(3)),
        };
        let Terminator::Call { args, .. } = &mut candidate.functions[0].blocks[0].terminator else {
            unreachable!()
        };
        args.truncate(1);

        assert_eq!(
            specialize_forwarding_direct_calls(&mut candidate, u64::MAX).0,
            PassOutcome::Changed
        );
        let caller = &candidate.functions[0];
        assert!(matches!(
            caller.blocks[0].statements.last().map(|statement| &statement.kind),
            Some(InstructionKind::Const {
                dst: 6,
                value: Constant::I64(41),
            })
        ));
        assert!(matches!(caller.blocks[0].terminator, Terminator::Goto(_)));
        validate_program(&candidate, &types, MirPhase::Raw).unwrap();
    }

    #[test]
    fn specializes_single_argument_forwarding_tail_call() {
        let (mut candidate, types) = inline_leaf_fixture();
        let caller = &mut candidate.functions[0];
        caller.blocks.truncate(1);
        caller.blocks[0].terminator = Terminator::TailCall {
            function: 1,
            args: vec![move_operand(1)],
        };
        let callee = &mut candidate.functions[1];
        callee.params = vec![I64];
        callee.register_types = vec![UNIT, I64];
        callee.blocks[0].statements.clear();
        callee.blocks[0].terminator = Terminator::Return {
            value: Some(move_operand(1)),
        };

        assert_eq!(
            specialize_forwarding_direct_calls(&mut candidate, u64::MAX).0,
            PassOutcome::Changed
        );
        assert_eq!(
            candidate.functions[0].blocks[0].terminator,
            Terminator::Return {
                value: Some(move_operand(1)),
            }
        );
        validate_program(&candidate, &types, MirPhase::Raw).unwrap();
    }

    #[test]
    fn whole_program_inlining_only_invalidates_rewritten_bodies() {
        let (mut candidate, types) = inline_leaf_fixture();
        let mut remaining = u64::MAX;
        let mut policy = InlinePolicyState::default();
        let report = run_transactional_whole_program_pass(
            &mut candidate,
            PassId::InlineByCost,
            WholeProgramPassTables {
                types: &types,
                protocols: &[],
                handler_defs: &[],
            },
            OptimizationLevel::O2,
            &mut remaining,
            &mut policy,
        );

        assert_eq!(report.outcome, PassOutcome::Changed);
        assert_eq!(candidate.functions[0].invalid_analyses, analysis::ALL);
        assert_eq!(candidate.functions[1].invalid_analyses, 0);
    }

    #[test]
    fn pass_contract_preserves_cfg_for_body_only_rewrites() {
        let body_only =
            analysis::USES | analysis::FLOW | analysis::EFFECTS | analysis::VALUES | analysis::COST;
        for pass in [
            PassId::ScalarizeLocals,
            PassId::EraseLoanProofsAndScalarizedReferences,
        ] {
            assert_eq!(pass_contract(pass).invalidates, body_only);
            assert_eq!(pass_contract(pass).scope, InvalidationScope::ChangedBodies);
        }
        assert_eq!(
            pass_contract(PassId::InlineByCost).scope,
            InvalidationScope::ChangedBodies
        );
        assert_eq!(
            pass_contract(PassId::SpecializeControl).scope,
            InvalidationScope::WholeProgram
        );
    }

    #[test]
    fn inline_by_cost_preserves_reference_return_call_boundaries() {
        fn set_result_type(program: &mut Program, ty: TypeId) {
            let caller = &mut program.functions[0];
            caller.result = ty;
            caller.register_types[3] = ty;
            caller.blocks[1].params[0].ty = ty;
            let callee = &mut program.functions[1];
            callee.result = ty;
            callee.register_types[3] = ty;
        }

        let (mut scalar, scalar_types) = inline_leaf_fixture();
        assert_eq!(
            inline_by_cost_with_policy(
                &mut scalar,
                &scalar_types,
                OptimizationLevel::O2,
                u64::MAX,
                &mut InlinePolicyState::default(),
            )
            .0,
            PassOutcome::Changed,
            "a reference-free leaf must remain inlineable",
        );

        let (mut direct, mut direct_types) = inline_leaf_fixture();
        let direct_reference = direct_types.len() as TypeId;
        direct_types.push(Type::RefShared { referent: I64 });
        set_result_type(&mut direct, direct_reference);
        assert_eq!(
            inline_by_cost_with_policy(
                &mut direct,
                &direct_types,
                OptimizationLevel::O2,
                u64::MAX,
                &mut InlinePolicyState::default(),
            )
            .0,
            PassOutcome::Unchanged,
            "a direct reference result carries a call-boundary loan route",
        );

        let (mut nested, mut nested_types) = inline_leaf_fixture();
        let nested_reference = nested_types.len() as TypeId;
        nested_types.push(Type::RefUnique { referent: I64 });
        let tuple = nested_types.len() as TypeId;
        nested_types.push(Type::Tuple {
            fields: vec![I64, nested_reference],
            copy: false,
        });
        let structure = nested_types.len() as TypeId;
        nested_types.push(Type::Struct {
            name: "ReferenceCarrier".into(),
            fields: vec![Field {
                name: "tuple".into(),
                ty: tuple,
            }],
            copy: false,
        });
        let restricted_enum = nested_types.len() as TypeId;
        nested_types.push(
            Type::Enum {
                name: "MaybeReferenceCarrier".into(),
                variants: vec![EnumVariant {
                    name: "Some".into(),
                    fields: vec![Field {
                        name: "value".into(),
                        ty: structure,
                    }],
                }],
                copy: false,
            }
            .restricted(false, false),
        );
        set_result_type(&mut nested, restricted_enum);
        assert_eq!(
            inline_by_cost_with_policy(
                &mut nested,
                &nested_types,
                OptimizationLevel::O2,
                u64::MAX,
                &mut InlinePolicyState::default(),
            )
            .0,
            PassOutcome::Unchanged,
            "nested references remain visible through restricted aggregates",
        );
    }

    #[test]
    fn inline_by_cost_clones_a_branching_cfg_with_a_closed_cleanup_free_survivor() {
        let types = Type::predefined();
        let mut entry = block(
            0,
            Terminator::Call {
                result: Some(2),
                function: 1,
                args: vec![move_operand(1)],
                normal: Edge {
                    target: 1,
                    args: vec![],
                },
            },
        );
        entry.statements.push(instruction(InstructionKind::Const {
            dst: 1,
            value: Constant::I64(42),
        }));
        let continuation = BasicBlock {
            id: 1,
            params: vec![BlockParam {
                register: 2,
                ty: I64,
                role: BlockParamRole::CallResult,
            }],
            statements: vec![],
            terminator: Terminator::Return {
                value: Some(move_operand(2)),
            },
        };
        let mut caller = function(vec![entry, continuation], vec![UNIT, I64, I64]);
        caller.declaration = 0;
        caller.name = "branching-caller".into();
        caller.result = I64;
        caller.features = infer_feature_bits(&caller);

        let mut dispatch = block(
            0,
            Terminator::Switch {
                discr: operand(1),
                cases: vec![(
                    Constant::I64(0),
                    Edge {
                        target: 1,
                        args: vec![],
                    },
                )],
                otherwise: Edge {
                    target: 2,
                    args: vec![],
                },
            },
        );
        dispatch
            .statements
            .push(instruction(InstructionKind::Const {
                dst: 3,
                value: Constant::I64(7),
            }));
        let yes = block(
            1,
            Terminator::Goto(Edge {
                target: 3,
                args: vec![move_operand(1)],
            }),
        );
        let no = block(
            2,
            Terminator::Goto(Edge {
                target: 3,
                args: vec![move_operand(1)],
            }),
        );
        let merged = BasicBlock {
            id: 3,
            params: vec![BlockParam {
                register: 2,
                ty: I64,
                role: BlockParamRole::Ordinary,
            }],
            statements: vec![],
            terminator: Terminator::Return {
                value: Some(move_operand(2)),
            },
        };
        let mut callee = function(vec![dispatch, yes, no, merged], vec![UNIT, I64, I64, I64]);
        callee.declaration = 1;
        callee.name = "branching-callee".into();
        callee.params = vec![I64];
        callee.result = I64;
        callee.features = infer_feature_bits(&callee);

        let mut candidate = Program {
            functions: vec![caller, callee],
        };
        let original = candidate.clone();
        let (outcome, _) = inline_by_cost(&mut candidate, OptimizationLevel::O2, u64::MAX);
        assert_eq!(outcome, PassOutcome::Changed);
        let caller = &candidate.functions[0];
        assert!(
            caller
                .blocks
                .iter()
                .all(|block| { !matches!(block.terminator, Terminator::Call { function: 1, .. }) })
        );
        assert!(
            caller
                .blocks
                .iter()
                .any(|block| matches!(block.terminator, Terminator::Switch { .. }))
        );
        validate_program(&candidate, &types, MirPhase::Raw).unwrap();

        let mut exhausted_ids = original.clone();
        exhausted_ids.functions[0].blocks[1].id = u32::MAX;
        let Terminator::Call { normal, .. } = &mut exhausted_ids.functions[0].blocks[0].terminator
        else {
            unreachable!()
        };
        normal.target = u32::MAX;
        exhausted_ids.functions[1].blocks[0].statements.clear();
        let before_exhaustion = exhausted_ids.clone();
        assert_eq!(
            inline_by_cost(&mut exhausted_ids, OptimizationLevel::O2, u64::MAX).0,
            PassOutcome::Unchanged,
            "CFG cloning must not wrap or alias exhausted block identities"
        );
        assert_eq!(exhausted_ids, before_exhaustion);

        let mut open = original;
        let alternate_register = open.functions[0].register_types.len() as Register;
        open.functions[0].register_types.push(I64);
        let mut alternate = block(
            2,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![move_operand(alternate_register)],
            }),
        );
        alternate
            .statements
            .push(instruction(InstructionKind::Const {
                dst: alternate_register,
                value: Constant::I64(0),
            }));
        open.functions[0].blocks.push(alternate);
        assert_eq!(
            inline_by_cost(&mut open, OptimizationLevel::O2, u64::MAX).0,
            PassOutcome::Unchanged,
            "an alternate continuation predecessor cannot join a cloned live survivor"
        );
    }

    #[test]
    fn inline_arena_clone_freshens_move_paths_loans_scopes_and_sources() {
        use crate::compiler_mir::{LoanFact, LoanKind, Place, ScopeFact, SourceInfoId};

        let mut caller = function(vec![block(0, Terminator::Unreachable)], vec![UNIT; 5]);
        caller.flow.sources.push(Span::new(1, 2));
        caller.flow.scopes.push(ScopeFact {
            parent: None,
            owners: vec![],
        });
        caller.flow.move_paths.root(4);
        let mut target = function(vec![block(7, Terminator::Unreachable)], vec![UNIT; 3]);
        target.flow.sources.push(Span::new(10, 20));
        target.flow.scopes.push(ScopeFact {
            parent: None,
            owners: vec![1],
        });
        let root = target.flow.move_paths.root(1);
        target.flow.move_paths.child(
            root,
            Projection::Field {
                variant: None,
                field: 0,
            },
        );
        target.flow.loans.push(LoanFact {
            kind: LoanKind::Shared,
            reference: 2,
            borrowed: Place {
                base: 1,
                projection: vec![],
            },
            parent: None,
            region: RegionId(0),
            issued_block: 7,
            source: SourceInfoId(0),
        });

        let registers = vec![None, Some(5), Some(6)];
        let blocks = BTreeMap::from([(7, 11)]);
        let arenas = append_inline_arenas(&mut caller, &target, &registers, &blocks).unwrap();

        assert!(arenas.labels.is_empty());
        assert_eq!(
            caller.flow.sources,
            vec![Span::new(1, 2), Span::new(10, 20)]
        );
        assert_eq!(caller.flow.scopes[1].owners, vec![5]);
        assert_eq!(caller.flow.move_paths.facts[1].base, 5);
        assert_eq!(
            caller.flow.move_paths.facts[1].children,
            vec![MovePathId(2)]
        );
        assert_eq!(caller.flow.move_paths.facts[2].parent, Some(MovePathId(1)));
        assert_eq!(caller.flow.loans[0].reference, 6);
        assert_eq!(caller.flow.loans[0].borrowed.base, 5);
        assert_eq!(caller.flow.loans[0].issued_block, 11);
        assert_eq!(caller.flow.loans[0].source, SourceInfoId(1));
    }

    #[test]
    fn tail_discovery_tracks_ended_loans_and_aggregate_environments() {
        let mut call = block(
            0,
            Terminator::Call {
                result: Some(5),
                function: 9,
                args: vec![move_operand(4)],
                normal: Edge {
                    target: 1,
                    args: vec![],
                },
            },
        );
        call.statements = vec![
            instruction(InstructionKind::Const {
                dst: 1,
                value: Constant::I64(1),
            }),
            instruction(InstructionKind::Borrow {
                dst: 2,
                src: 1,
                unique: false,
            }),
            instruction(InstructionKind::EndBorrow { reference: 2 }),
            instruction(InstructionKind::Construct {
                dst: 4,
                ty: I64,
                variant: None,
                fields: vec![move_operand(1)],
            }),
        ];
        let continuation = BasicBlock {
            id: 1,
            params: vec![BlockParam {
                register: 5,
                ty: I64,
                role: BlockParamRole::CallResult,
            }],
            statements: vec![],
            terminator: Terminator::Return {
                value: Some(move_operand(5)),
            },
        };
        let mut body = function(
            vec![call, continuation],
            vec![UNIT, I64, I64, I64, I64, I64],
        );
        body.result = I64;

        assert_eq!(
            discover_tail_calls(&mut body, &Type::predefined(), &BTreeSet::new(), u64::MAX,).0,
            PassOutcome::Changed
        );
        assert!(matches!(
            body.blocks[0].terminator,
            Terminator::TailCall {
                function: 9,
                ref args,
            } if args == &[move_operand(4)]
        ));
    }

    #[test]
    fn inline_by_cost_is_transactional_and_keeps_identity_barriers() {
        let (raw, _) = inline_leaf_fixture();
        let mut first = raw.clone();
        let mut second = raw.clone();
        let first_report = inline_by_cost(&mut first, OptimizationLevel::O2, u64::MAX);
        let second_report = inline_by_cost(&mut second, OptimizationLevel::O2, u64::MAX);
        assert_eq!(first, second);
        assert_eq!(first_report, second_report);

        let mut budgeted = raw.clone();
        let scan = operation_count(&budgeted);
        let mut policy = InlinePolicyState::default();
        let before_policy = policy.clone();
        let types = Type::predefined();
        assert_eq!(
            inline_by_cost_with_policy(
                &mut budgeted,
                &types,
                OptimizationLevel::O2,
                scan,
                &mut policy,
            )
            .0,
            PassOutcome::BudgetExhausted
        );
        assert_eq!(budgeted, raw);
        assert_eq!(policy, before_policy);

        for barrier in 0..5 {
            let (mut candidate, _) = inline_leaf_fixture();
            let target = &mut candidate.functions[1];
            match barrier {
                0 => target.receiver_mode = Some(0),
                1 => target.outward_protocols.push(0),
                2 => target.features = FeatureBits::LOANS,
                3 => {
                    target.blocks[0].statements = vec![instruction(InstructionKind::Copy {
                        dst: 3,
                        src: operand(1),
                    })];
                    target.return_cleanup.push(2);
                }
                _ => target.blocks[0]
                    .statements
                    .push(instruction(InstructionKind::Copy {
                        dst: 1,
                        src: operand(1),
                    })),
            }
            assert_eq!(
                inline_by_cost(&mut candidate, OptimizationLevel::O2, u64::MAX).0,
                PassOutcome::Unchanged
            );
        }
    }

    #[test]
    fn inline_survivors_require_a_closed_downstream_region() {
        let (mut candidate, _) = inline_leaf_fixture();
        let caller = &mut candidate.functions[0];
        assert!(inline_survivor_region_is_closed(caller, 0, 1));

        caller.blocks.push(block(
            2,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![move_operand(4)],
            }),
        ));
        assert!(!inline_survivor_region_is_closed(caller, 0, 1));
    }

    fn inline_many_callers(count: u32) -> Program {
        let (template, _) = inline_leaf_fixture();
        let mut leaf = template.functions[1].clone();
        leaf.declaration = 10_000;
        let mut functions = Vec::new();
        for declaration in 0..count {
            let mut caller = template.functions[0].clone();
            caller.declaration = declaration;
            let Terminator::Call { function, .. } = &mut caller.blocks[0].terminator else {
                unreachable!()
            };
            *function = leaf.declaration;
            functions.push(caller);
        }
        functions.push(leaf);
        Program { functions }
    }

    fn inlined_callers(program: &Program) -> BTreeSet<u32> {
        program
            .functions
            .iter()
            .filter(|function| function.declaration != 10_000)
            .filter(|function| matches!(function.blocks[0].terminator, Terminator::Goto(_)))
            .map(|function| function.declaration)
            .collect()
    }

    #[test]
    fn inline_call_graph_sccs_are_deterministic_for_mutual_recursion() {
        let recursive = |declaration, target| {
            let mut body = function(
                vec![block(
                    0,
                    Terminator::TailCall {
                        function: target,
                        args: vec![],
                    },
                )],
                vec![UNIT],
            );
            body.declaration = declaration;
            body
        };
        let mut leaf = function(
            vec![block(0, Terminator::Return { value: None })],
            vec![UNIT],
        );
        leaf.declaration = 2;
        let first = Program {
            functions: vec![recursive(0, 1), recursive(1, 0), leaf.clone()],
        };
        let second = Program {
            functions: vec![leaf, recursive(1, 0), recursive(0, 1)],
        };

        let first_sccs = inline_call_graph_sccs(&first);
        let second_sccs = inline_call_graph_sccs(&second);
        assert_eq!(first_sccs, second_sccs);
        assert_eq!(first_sccs[&0], first_sccs[&1]);
        assert_ne!(first_sccs[&0], first_sccs[&2]);
    }

    #[test]
    fn inline_depth_caps_are_explicit_for_o2_and_o3_chains() {
        for cap in [8_u8, 16] {
            let mut depths = (0..=u32::from(cap))
                .map(|function| (function, 0_u8))
                .collect::<BTreeMap<_, _>>();
            for caller in (0..u32::from(cap)).rev() {
                let depth = inline_candidate_depth(&depths, caller + 1, cap).unwrap();
                depths.insert(caller, depth);
            }
            assert_eq!(depths[&0], cap);
            assert_eq!(inline_candidate_depth(&depths, 0, cap), None);
        }
    }

    #[test]
    fn inline_source_and_program_clone_caps_are_deterministic() {
        for (level, cap) in [(OptimizationLevel::O2, 8), (OptimizationLevel::O3, 16)] {
            let mut ordered = inline_many_callers(20);
            let mut reversed = ordered.clone();
            reversed.functions.reverse();
            assert_eq!(
                inline_by_cost(&mut ordered, level, u64::MAX).0,
                PassOutcome::Changed
            );
            assert_eq!(
                inline_by_cost(&mut reversed, level, u64::MAX).0,
                PassOutcome::Changed
            );
            assert_eq!(inlined_callers(&ordered).len(), cap);
            assert_eq!(inlined_callers(&ordered), inlined_callers(&reversed));
        }

        let mut persistent = inline_many_callers(20);
        let mut persistent_policy = InlinePolicyState::default();
        let types = Type::predefined();
        assert_eq!(
            inline_by_cost_with_policy(
                &mut persistent,
                &types,
                OptimizationLevel::O2,
                u64::MAX,
                &mut persistent_policy,
            )
            .0,
            PassOutcome::Changed
        );
        assert_eq!(
            inline_by_cost_with_policy(
                &mut persistent,
                &types,
                OptimizationLevel::O2,
                u64::MAX,
                &mut persistent_policy,
            )
            .0,
            PassOutcome::Unchanged
        );
        assert_eq!(persistent_policy.source_clones[&10_000], 8);

        let mut limited = inline_many_callers(5);
        let mut policy = InlinePolicyState {
            cloned_bodies_remaining: 2,
            ..InlinePolicyState::default()
        };
        assert_eq!(
            inline_by_cost_with_policy(
                &mut limited,
                &types,
                OptimizationLevel::O2,
                u64::MAX,
                &mut policy,
            )
            .0,
            PassOutcome::Changed
        );
        assert_eq!(policy.cloned_bodies_remaining, 0);
        assert_eq!(inlined_callers(&limited).len(), 2);
    }

    #[test]
    fn validator_rejects_copy_mode_direct_call_arguments() {
        let (mut candidate, types) = inline_leaf_fixture();
        let Terminator::Call { args, .. } = &mut candidate.functions[0].blocks[0].terminator else {
            unreachable!()
        };
        args[0].mode = UseMode::Copy;
        let error = validate_program(&candidate, &types, MirPhase::Raw).unwrap_err();
        assert!(
            error
                .message
                .contains("must transfer every argument by move")
        );
    }

    fn schedule_for(level: OptimizationLevel) -> OptimizationReport {
        let types = Type::predefined();
        let mut candidate = program(function(
            vec![block(0, Terminator::Return { value: None })],
            vec![],
        ));
        optimize_program(&mut candidate, &types, level).unwrap()
    }

    fn exact_callable_fixture(tail: bool) -> (Program, Vec<Type>, TypeId) {
        let mut types = Type::predefined();
        let receiver = types.len() as TypeId;
        types.push(Type::RefShared { referent: UNIT });
        let callable = types.len() as TypeId;
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            capture_type: UNIT,
            receiver_mode: 0,
            identity_name: "exact-target".into(),
            copy: true,
            zero_use_allowed: true,
        });

        let terminator = if tail {
            Terminator::TailCallIndirect {
                callable: operand(2),
                known_function: None,
                receiver_mode: 0,
                args: vec![],
            }
        } else {
            Terminator::CallIndirect {
                result: None,
                callable: operand(2),
                known_function: None,
                receiver_mode: 0,
                cleanup_callable: false,
                args: vec![],
                normal: Edge {
                    target: 1,
                    args: vec![],
                },
            }
        };
        let mut entry = block(0, terminator);
        entry
            .statements
            .push(instruction(InstructionKind::MakeCallable {
                dst: 0,
                callable_type: callable,
                function: 7,
                captures: vec![],
            }));
        entry.statements.push(instruction(InstructionKind::Copy {
            dst: 1,
            src: operand(0),
        }));
        entry.statements.push(instruction(InstructionKind::Move {
            dst: 2,
            src: Operand {
                register: 1,
                mode: UseMode::Move,
            },
        }));
        let blocks = if tail {
            vec![entry]
        } else {
            vec![entry, block(1, Terminator::Return { value: None })]
        };
        let mut caller = function(blocks, vec![callable, callable, callable]);
        caller.declaration = 3;
        let mut target = function(
            vec![block(0, Terminator::Return { value: None })],
            vec![receiver],
        );
        target.declaration = 7;
        target.receiver_mode = Some(0);
        target.receiver_type = receiver;
        (
            Program {
                functions: vec![caller, target],
            },
            types,
            callable,
        )
    }

    fn owned_callable_scalarization_fixture(alias: bool) -> (Program, Vec<Type>) {
        let mut types = Type::predefined();
        let capture = types.len() as TypeId;
        types.push(Type::Tuple {
            fields: vec![I64],
            copy: false,
        });
        let callable = types.len() as TypeId;
        types.push(Type::Callable {
            signature: Signature {
                params: vec![I64],
                result: I64,
                outward_protocols: vec![],
            },
            capture_type: capture,
            receiver_mode: 2,
            identity_name: "owned-scalarization-target".into(),
            copy: false,
            zero_use_allowed: false,
        });

        let callable_register = if alias { 4 } else { 3 };
        let mut entry = block(
            0,
            Terminator::CallIndirect {
                result: Some(5),
                callable: Operand {
                    register: callable_register,
                    mode: UseMode::Move,
                },
                known_function: Some(1),
                receiver_mode: 2,
                cleanup_callable: false,
                args: vec![move_operand(2)],
                normal: Edge {
                    target: 1,
                    args: vec![],
                },
            },
        );
        entry.statements = vec![
            instruction(InstructionKind::Const {
                dst: 1,
                value: Constant::I64(40),
            }),
            instruction(InstructionKind::Const {
                dst: 2,
                value: Constant::I64(2),
            }),
            instruction(InstructionKind::MakeCallable {
                dst: 3,
                callable_type: callable,
                function: 1,
                captures: vec![move_operand(1)],
            }),
        ];
        if alias {
            entry.statements.push(instruction(InstructionKind::Move {
                dst: 4,
                src: move_operand(3),
            }));
        }
        let mut caller = function(
            vec![
                entry,
                BasicBlock {
                    id: 1,
                    params: vec![BlockParam {
                        register: 5,
                        ty: I64,
                        role: BlockParamRole::CallResult,
                    }],
                    statements: vec![],
                    terminator: Terminator::Return {
                        value: Some(move_operand(5)),
                    },
                },
            ],
            vec![UNIT, I64, I64, callable, callable, I64],
        );
        caller.declaration = 0;
        caller.name = "caller".into();
        caller.result = I64;

        let mut target_entry = block(
            0,
            Terminator::Return {
                value: Some(move_operand(3)),
            },
        );
        target_entry.statements = vec![
            instruction(InstructionKind::ProjectMove {
                dst: 2,
                src: move_operand(0),
                field: 0,
            }),
            instruction(InstructionKind::Deconstruct { src: 0 }),
            instruction(InstructionKind::Primitive {
                dst: 3,
                primitive: Primitive::IntCheckedAdd,
                args: vec![operand(2), operand(1)],
            }),
            instruction(InstructionKind::Drop {
                owner: move_operand(1),
            }),
            instruction(InstructionKind::Drop {
                owner: move_operand(2),
            }),
        ];
        let mut target = function(vec![target_entry], vec![capture, I64, I64, I64]);
        target.declaration = 1;
        target.name = "$closure$1".into();
        target.params = vec![I64];
        target.result = I64;
        target.receiver_mode = Some(2);
        target.receiver_type = capture;
        target.return_cleanup = vec![1, 2];
        (
            Program {
                functions: vec![caller, target],
            },
            types,
        )
    }

    #[test]
    fn o2_scalarizes_immediate_owned_callable_and_move_only_alias() {
        for alias in [false, true] {
            let (raw, types) = owned_callable_scalarization_fixture(alias);
            let mut o0 = raw.clone();
            optimize_program(&mut o0, &types, OptimizationLevel::O0).unwrap();
            let mut o2 = raw;
            let report = optimize_program(&mut o2, &types, OptimizationLevel::O2).unwrap();

            assert_eq!(o0.functions.len(), 2);
            assert_eq!(o2.functions.len(), 3);
            let caller = &o2.functions[0];
            assert!(
                caller.blocks[0]
                    .statements
                    .iter()
                    .all(|statement| !matches!(
                        statement.kind,
                        InstructionKind::MakeCallable { .. } | InstructionKind::Move { dst: 4, .. }
                    ))
            );
            let Terminator::Goto(Edge { target, args }) = &caller.blocks[0].terminator else {
                panic!(
                    "scalarized receiverless leaf was not subsequently inlined: {:?}",
                    caller.blocks[0].terminator
                )
            };
            assert_eq!(*target, 1);
            assert_eq!(args.len(), 1);

            let clone = &o2.functions[2];
            assert_eq!(clone.declaration, 2);
            assert_eq!(clone.name, "$scalarized$1$2");
            assert_eq!(clone.receiver_mode, None);
            assert_eq!(clone.receiver_type, UNIT);
            assert_eq!(clone.params, vec![I64, I64]);
            assert_eq!(&clone.register_types[..3], &[UNIT, I64, I64]);
            assert_eq!(clone.return_cleanup, vec![2, 1]);
            let drops = clone.blocks[0]
                .statements
                .iter()
                .filter_map(|statement| match statement.kind {
                    InstructionKind::Drop { owner } => Some(owner.register),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(drops, vec![2, 1], "arguments must drop before captures");
            assert!(clone.blocks[0].statements.iter().all(|statement| !matches!(
                statement.kind,
                InstructionKind::ProjectMove {
                    src: Operand { register: 0, .. },
                    ..
                } | InstructionKind::Deconstruct { src: 0 }
            )));
            assert!(report.passes.iter().any(|pass| {
                pass.pass == PassId::ScalarizeCallables && pass.outcome == PassOutcome::Changed
            }));
            assert!(report.passes.iter().any(|pass| {
                pass.pass == PassId::InlineByCost && pass.outcome == PassOutcome::Changed
            }));
            validate_program(&o2, &types, MirPhase::Optimized).unwrap();
        }
    }

    #[test]
    fn scalarizes_immediate_owned_callable_tail_call() {
        let (mut program, types) = owned_callable_scalarization_fixture(true);
        let caller = &mut program.functions[0];
        caller.blocks.truncate(1);
        caller.blocks[0].terminator = Terminator::TailCallIndirect {
            callable: move_operand(4),
            known_function: Some(1),
            receiver_mode: 2,
            args: vec![move_operand(2)],
        };

        assert_eq!(
            scalarize_callables(&mut program, &types, u64::MAX).0,
            PassOutcome::Changed
        );
        let caller = &program.functions[0];
        assert!(caller.blocks[0].statements.iter().all(|statement| !matches!(
            statement.kind,
            InstructionKind::MakeCallable { .. } | InstructionKind::Move { dst: 4, .. }
        )));
        assert!(matches!(
            caller.blocks[0].terminator,
            Terminator::TailCall {
                function: 2,
                ref args,
            } if args == &vec![move_operand(1), move_operand(2)]
        ));
        validate_program(&program, &types, MirPhase::Raw).unwrap();
    }

    #[test]
    fn callable_scalarization_is_deterministic_and_keeps_barriers() {
        let (raw, types) = owned_callable_scalarization_fixture(true);
        let mut first = raw.clone();
        let mut second = raw.clone();
        let first_report = optimize_program(&mut first, &types, OptimizationLevel::O2).unwrap();
        let second_report = optimize_program(&mut second, &types, OptimizationLevel::O2).unwrap();
        assert_eq!(first, second);
        assert_eq!(first_report, second_report);

        let mut copy_alias = raw.clone();
        copy_alias.functions[0].blocks[0].statements[3].kind = InstructionKind::Copy {
            dst: 4,
            src: operand(3),
        };
        copy_alias.functions[0].blocks[0].terminator = Terminator::CallIndirect {
            result: Some(5),
            callable: Operand {
                register: 4,
                mode: UseMode::Move,
            },
            known_function: Some(1),
            receiver_mode: 2,
            cleanup_callable: false,
            args: vec![move_operand(2)],
            normal: Edge {
                target: 1,
                args: vec![],
            },
        };
        let (outcome, _) = scalarize_callables(&mut copy_alias, &types, u64::MAX);
        assert_eq!(outcome, PassOutcome::Unchanged);
        assert_eq!(copy_alias.functions.len(), 2);

        let mut nonfinal = raw;
        nonfinal.functions[0].blocks[0]
            .statements
            .push(instruction(InstructionKind::Const {
                dst: 6,
                value: Constant::I64(9),
            }));
        nonfinal.functions[0].register_types.push(I64);
        let (outcome, _) = scalarize_callables(&mut nonfinal, &types, u64::MAX);
        assert_eq!(outcome, PassOutcome::Unchanged);
    }

    #[test]
    fn o2_global_simplify_tracks_exact_callable_through_copy_and_move() {
        for tail in [false, true] {
            let (raw, types, _) = exact_callable_fixture(tail);
            let mut o0 = raw.clone();
            optimize_program(&mut o0, &types, OptimizationLevel::O0).unwrap();
            let mut o2 = raw;
            let report = optimize_program(&mut o2, &types, OptimizationLevel::O2).unwrap();

            let known = match &o2.functions[0].blocks[0].terminator {
                Terminator::CallIndirect { known_function, .. }
                | Terminator::TailCallIndirect { known_function, .. } => *known_function,
                other => panic!("unexpected optimized terminator: {other:?}"),
            };
            let o0_known = match &o0.functions[0].blocks[0].terminator {
                Terminator::CallIndirect { known_function, .. }
                | Terminator::TailCallIndirect { known_function, .. } => *known_function,
                other => panic!("unexpected O0 terminator: {other:?}"),
            };
            assert_eq!(o0_known, None);
            assert_eq!(known, Some(7));
            assert!(report.passes.iter().any(|pass| {
                pass.pass == PassId::GlobalSimplify && pass.outcome == PassOutcome::Changed
            }));
        }
    }

    #[test]
    fn exact_callable_annotation_skips_place_flow_rebuild() {
        let (mut candidate, types, _) = exact_callable_fixture(true);
        let flow_before = candidate.functions[0].flow.clone();

        let (outcome, _) =
            global_simplify_exact_callables(&mut candidate.functions[0], &types, u64::MAX);

        assert_eq!(outcome, PassOutcome::Changed);
        assert_eq!(
            candidate.functions[0].invalid_analyses,
            analysis::EFFECTS | analysis::VALUES | analysis::COST
        );
        refresh_invalidated_flow(&mut candidate, &types).unwrap();
        assert_eq!(candidate.functions[0].invalid_analyses, 0);
        assert_eq!(candidate.functions[0].flow, flow_before);
    }

    #[test]
    fn global_simplify_reuses_dominating_scalar_constants_and_resolves_switches() {
        let types = Type::predefined();
        let mut body = function(
            vec![
                BasicBlock {
                    id: 0,
                    params: vec![],
                    statements: vec![instruction(InstructionKind::Const {
                        dst: 1,
                        value: Constant::U32(7),
                    })],
                    terminator: Terminator::Goto(Edge {
                        target: 1,
                        args: vec![],
                    }),
                },
                BasicBlock {
                    id: 1,
                    params: vec![],
                    statements: vec![instruction(InstructionKind::Const {
                        dst: 2,
                        value: Constant::U32(7),
                    })],
                    terminator: Terminator::Switch {
                        discr: operand(1),
                        cases: vec![(
                            Constant::U32(7),
                            Edge {
                                target: 2,
                                args: vec![],
                            },
                        )],
                        otherwise: Edge {
                            target: 3,
                            args: vec![],
                        },
                    },
                },
                block(2, Terminator::Return { value: None }),
                block(3, Terminator::Unreachable),
            ],
            vec![UNIT, U32, U32],
        );
        body.features = infer_feature_bits(&body);
        let (outcome, _) = global_simplify_exact_callables(&mut body, &types, u64::MAX);
        assert_eq!(outcome, PassOutcome::Changed);
        assert!(matches!(
            body.blocks[1].statements[0].kind,
            InstructionKind::Copy {
                dst: 2,
                src: Operand {
                    register: 1,
                    mode: UseMode::Copy,
                },
            }
        ));
        assert!(matches!(
            body.blocks[1].terminator,
            Terminator::Goto(Edge { target: 2, .. })
        ));
    }

    #[test]
    fn global_simplify_cses_nontrapping_scalar_primitives_in_one_block() {
        let types = Type::predefined();
        for (primitive, ty) in [(Primitive::IntBitXor, I64), (Primitive::FloatAdd, F64)] {
            let mut body = function(
                vec![BasicBlock {
                    id: 0,
                    params: vec![],
                    statements: vec![
                        instruction(InstructionKind::Primitive {
                            dst: 2,
                            primitive,
                            args: vec![operand(0), operand(1)],
                        }),
                        instruction(InstructionKind::Primitive {
                            dst: 3,
                            primitive,
                            args: vec![operand(0), operand(1)],
                        }),
                    ],
                    terminator: Terminator::Return { value: None },
                }],
                vec![ty, ty, ty, ty],
            );

            let (outcome, _) = global_simplify_exact_callables(&mut body, &types, u64::MAX);

            assert_eq!(outcome, PassOutcome::Changed, "{primitive:?}");
            assert!(matches!(
                body.blocks[0].statements[0].kind,
                InstructionKind::Primitive { dst: 2, .. }
            ));
            assert!(matches!(
                body.blocks[0].statements[1].kind,
                InstructionKind::Copy {
                    dst: 3,
                    src: Operand {
                        register: 2,
                        mode: UseMode::Copy,
                    },
                }
            ));
        }
    }

    #[test]
    fn global_simplify_cses_nontrapping_scalar_primitives_across_blocks_and_joins() {
        let types = Type::predefined();
        let expression = |dst| {
            instruction(InstructionKind::Primitive {
                dst,
                primitive: Primitive::IntBitXor,
                args: vec![operand(0), operand(1)],
            })
        };
        let mut body = function(
            vec![
                BasicBlock {
                    id: 0,
                    params: vec![],
                    statements: vec![expression(2)],
                    terminator: Terminator::Switch {
                        discr: operand(4),
                        cases: vec![(
                            Constant::U32(0),
                            Edge {
                                target: 1,
                                args: vec![],
                            },
                        )],
                        otherwise: Edge {
                            target: 2,
                            args: vec![],
                        },
                    },
                },
                block(
                    1,
                    Terminator::Goto(Edge {
                        target: 3,
                        args: vec![],
                    }),
                ),
                block(
                    2,
                    Terminator::Goto(Edge {
                        target: 3,
                        args: vec![],
                    }),
                ),
                BasicBlock {
                    id: 3,
                    params: vec![],
                    statements: vec![expression(3)],
                    terminator: Terminator::Return { value: None },
                },
            ],
            vec![I64, I64, I64, I64, U32],
        );

        let (outcome, _) = global_simplify_exact_callables(&mut body, &types, u64::MAX);

        assert_eq!(outcome, PassOutcome::Changed);
        assert!(matches!(
            body.blocks[3].statements[0].kind,
            InstructionKind::Copy {
                dst: 3,
                src: Operand {
                    register: 2,
                    mode: UseMode::Copy,
                },
            }
        ));
    }

    #[test]
    fn cross_block_primitive_cse_intersects_moves_and_control_barriers() {
        let types = Type::predefined();
        let expression = |dst| {
            instruction(InstructionKind::Primitive {
                dst,
                primitive: Primitive::IntBitXor,
                args: vec![operand(0), operand(1)],
            })
        };
        let mut body = function(
            vec![
                BasicBlock {
                    id: 0,
                    params: vec![],
                    statements: vec![expression(2)],
                    terminator: Terminator::Switch {
                        discr: operand(4),
                        cases: vec![(
                            Constant::U32(0),
                            Edge {
                                target: 1,
                                args: vec![],
                            },
                        )],
                        otherwise: Edge {
                            target: 2,
                            args: vec![],
                        },
                    },
                },
                BasicBlock {
                    id: 1,
                    params: vec![],
                    statements: vec![instruction(InstructionKind::Drop {
                        owner: move_operand(2),
                    })],
                    terminator: Terminator::Goto(Edge {
                        target: 3,
                        args: vec![],
                    }),
                },
                block(
                    2,
                    Terminator::Goto(Edge {
                        target: 3,
                        args: vec![],
                    }),
                ),
                BasicBlock {
                    id: 3,
                    params: vec![],
                    statements: vec![expression(3)],
                    terminator: Terminator::Return { value: None },
                },
            ],
            vec![I64, I64, I64, I64, U32],
        );

        let (outcome, _) = global_simplify_exact_callables(&mut body, &types, u64::MAX);

        assert_eq!(outcome, PassOutcome::Unchanged);
        assert!(matches!(
            body.blocks[3].statements[0].kind,
            InstructionKind::Primitive { dst: 3, .. }
        ));
    }

    #[test]
    fn global_scalar_cse_respects_ownership_barriers_and_argument_order() {
        let types = Type::predefined();
        let duplicate = |args| {
            instruction(InstructionKind::Primitive {
                dst: 3,
                primitive: Primitive::IntWrappingSub,
                args,
            })
        };
        let mut blocked = function(
            vec![BasicBlock {
                id: 0,
                params: vec![],
                statements: vec![
                    instruction(InstructionKind::Primitive {
                        dst: 2,
                        primitive: Primitive::IntWrappingSub,
                        args: vec![operand(0), operand(1)],
                    }),
                    instruction(InstructionKind::Drop {
                        owner: move_operand(2),
                    }),
                    duplicate(vec![operand(0), operand(1)]),
                ],
                terminator: Terminator::Return { value: None },
            }],
            vec![I64, I64, I64, I64],
        );
        let (outcome, _) = global_simplify_exact_callables(&mut blocked, &types, u64::MAX);
        assert_eq!(outcome, PassOutcome::Unchanged);
        assert!(matches!(
            blocked.blocks[0].statements[2].kind,
            InstructionKind::Primitive { .. }
        ));

        let mut reordered = function(
            vec![BasicBlock {
                id: 0,
                params: vec![],
                statements: vec![
                    instruction(InstructionKind::Primitive {
                        dst: 2,
                        primitive: Primitive::IntWrappingSub,
                        args: vec![operand(0), operand(1)],
                    }),
                    duplicate(vec![operand(1), operand(0)]),
                ],
                terminator: Terminator::Return { value: None },
            }],
            vec![I64, I64, I64, I64],
        );
        let (outcome, _) = global_simplify_exact_callables(&mut reordered, &types, u64::MAX);
        assert_eq!(outcome, PassOutcome::Unchanged);
        assert!(matches!(
            reordered.blocks[0].statements[1].kind,
            InstructionKind::Primitive { .. }
        ));
    }

    #[test]
    fn global_scalar_facts_intersect_at_joins_and_stop_at_ownership_barriers() {
        let types = Type::predefined();
        let mut joined = function(
            vec![
                block(
                    0,
                    Terminator::Switch {
                        discr: operand(1),
                        cases: vec![(
                            Constant::U32(0),
                            Edge {
                                target: 1,
                                args: vec![],
                            },
                        )],
                        otherwise: Edge {
                            target: 2,
                            args: vec![],
                        },
                    },
                ),
                BasicBlock {
                    id: 1,
                    params: vec![],
                    statements: vec![instruction(InstructionKind::Const {
                        dst: 2,
                        value: Constant::U32(7),
                    })],
                    terminator: Terminator::Goto(Edge {
                        target: 3,
                        args: vec![],
                    }),
                },
                BasicBlock {
                    id: 2,
                    params: vec![],
                    statements: vec![instruction(InstructionKind::Const {
                        dst: 3,
                        value: Constant::U32(7),
                    })],
                    terminator: Terminator::Goto(Edge {
                        target: 3,
                        args: vec![],
                    }),
                },
                BasicBlock {
                    id: 3,
                    params: vec![],
                    statements: vec![instruction(InstructionKind::Const {
                        dst: 4,
                        value: Constant::U32(7),
                    })],
                    terminator: Terminator::Return { value: None },
                },
            ],
            vec![UNIT, U32, U32, U32, U32],
        );
        joined.params = vec![U32];
        let (outcome, _) = global_simplify_exact_callables(&mut joined, &types, u64::MAX);
        assert_eq!(outcome, PassOutcome::Unchanged);
        assert!(matches!(
            joined.blocks[3].statements[0].kind,
            InstructionKind::Const { dst: 4, .. }
        ));

        let mut dropped = function(
            vec![BasicBlock {
                id: 0,
                params: vec![],
                statements: vec![
                    instruction(InstructionKind::Const {
                        dst: 1,
                        value: Constant::U32(7),
                    }),
                    instruction(InstructionKind::Drop {
                        owner: move_operand(1),
                    }),
                    instruction(InstructionKind::Const {
                        dst: 2,
                        value: Constant::U32(7),
                    }),
                ],
                terminator: Terminator::Return { value: None },
            }],
            vec![UNIT, U32, U32],
        );
        let (outcome, _) = global_simplify_exact_callables(&mut dropped, &types, u64::MAX);
        assert_eq!(outcome, PassOutcome::Unchanged);
        assert!(matches!(
            dropped.blocks[0].statements[2].kind,
            InstructionKind::Const { dst: 2, .. }
        ));
    }

    #[test]
    fn global_simplify_budget_is_transactional_on_cycles() {
        let types = Type::predefined();
        let mut body = function(
            vec![
                BasicBlock {
                    id: 0,
                    params: vec![],
                    statements: vec![instruction(InstructionKind::Const {
                        dst: 1,
                        value: Constant::U32(7),
                    })],
                    terminator: Terminator::Goto(Edge {
                        target: 1,
                        args: vec![],
                    }),
                },
                block(
                    1,
                    Terminator::Goto(Edge {
                        target: 0,
                        args: vec![],
                    }),
                ),
            ],
            vec![UNIT, U32],
        );
        let before = body.clone();

        let (outcome, work) = global_simplify_exact_callables(&mut body, &types, 3);

        assert_eq!(outcome, PassOutcome::BudgetExhausted);
        assert!(work > 3);
        assert_eq!(body, before);
    }

    #[test]
    fn global_simplify_never_cses_trapping_primitives() {
        let types = Type::predefined();
        let mut body = function(
            vec![BasicBlock {
                id: 0,
                params: vec![],
                statements: vec![
                    instruction(InstructionKind::Const {
                        dst: 1,
                        value: Constant::I64(1),
                    }),
                    instruction(InstructionKind::Const {
                        dst: 2,
                        value: Constant::I64(0),
                    }),
                    instruction(InstructionKind::Primitive {
                        dst: 3,
                        primitive: Primitive::IntCheckedDiv,
                        args: vec![move_operand(1), move_operand(2)],
                    }),
                    instruction(InstructionKind::Const {
                        dst: 4,
                        value: Constant::I64(1),
                    }),
                    instruction(InstructionKind::Const {
                        dst: 5,
                        value: Constant::I64(0),
                    }),
                    instruction(InstructionKind::Primitive {
                        dst: 6,
                        primitive: Primitive::IntCheckedDiv,
                        args: vec![move_operand(4), move_operand(5)],
                    }),
                ],
                terminator: Terminator::Return { value: None },
            }],
            vec![UNIT, I64, I64, I64, I64, I64, I64],
        );
        let (outcome, _) = global_simplify_exact_callables(&mut body, &types, u64::MAX);
        assert_eq!(outcome, PassOutcome::Unchanged);
        assert_eq!(
            body.blocks[0]
                .statements
                .iter()
                .filter(|statement| matches!(
                    statement.kind,
                    InstructionKind::Primitive {
                        primitive: Primitive::IntCheckedDiv,
                        ..
                    }
                ))
                .count(),
            2
        );
    }

    #[test]
    fn exact_callable_fact_crosses_an_ordinary_cfg_parameter() {
        let (mut across_cfg, types, callable) = exact_callable_fixture(false);
        let caller = &mut across_cfg.functions[0];
        caller.blocks[0].terminator = Terminator::Goto(Edge {
            target: 1,
            args: vec![operand(2)],
        });
        caller.blocks[1].params.push(BlockParam {
            register: 3,
            ty: callable,
            role: BlockParamRole::Ordinary,
        });
        caller.register_types.push(callable);
        caller.blocks[1].terminator = Terminator::TailCallIndirect {
            callable: operand(3),
            known_function: None,
            receiver_mode: 0,
            args: vec![],
        };
        optimize_program(&mut across_cfg, &types, OptimizationLevel::O2).unwrap();
        let call = &across_cfg.functions[0]
            .blocks
            .iter()
            .find(|block| block.id == 1)
            .unwrap()
            .terminator;
        assert!(matches!(
            call,
            Terminator::TailCallIndirect {
                known_function: Some(7),
                ..
            }
        ));
    }

    #[test]
    fn exact_callable_fact_stops_at_a_drop_barrier() {
        let (mut candidate, types, _) = exact_callable_fixture(true);
        let caller = &mut candidate.functions[0];
        caller.blocks[0]
            .statements
            .push(instruction(InstructionKind::Drop {
                owner: move_operand(0),
            }));
        caller.features = infer_feature_bits(caller);
        let (outcome, _) = global_simplify_exact_callables(caller, &types, u64::MAX);
        assert_eq!(outcome, PassOutcome::Unchanged);
        assert!(matches!(
            caller.blocks[0].terminator,
            Terminator::TailCallIndirect {
                known_function: None,
                ..
            }
        ));
    }

    #[test]
    fn exact_callable_fact_does_not_follow_aggregate_escape_and_projection() {
        let (mut program, mut types, callable) = exact_callable_fixture(false);
        let tuple = types.len() as TypeId;
        types.push(Type::Tuple {
            fields: vec![callable],
            copy: true,
        });
        let caller = &mut program.functions[0];
        caller.register_types.extend([tuple, callable]);
        caller.blocks[0]
            .statements
            .push(instruction(InstructionKind::Construct {
                dst: 3,
                ty: tuple,
                variant: None,
                fields: vec![Operand {
                    register: 2,
                    mode: UseMode::Move,
                }],
            }));
        caller.blocks[0]
            .statements
            .push(instruction(InstructionKind::ProjectMove {
                dst: 4,
                src: Operand {
                    register: 3,
                    mode: UseMode::Move,
                },
                field: 0,
            }));
        let Terminator::CallIndirect {
            callable,
            known_function,
            ..
        } = &mut caller.blocks[0].terminator
        else {
            unreachable!()
        };
        callable.register = 4;
        *known_function = None;
        caller.features = infer_feature_bits(caller);

        let (outcome, _) = global_simplify_exact_callables(caller, &types, u64::MAX);
        assert_eq!(outcome, PassOutcome::Unchanged);
        assert!(matches!(
            caller.blocks[0].terminator,
            Terminator::CallIndirect {
                known_function: None,
                ..
            }
        ));
    }

    #[test]
    fn known_callable_validation_rejects_target_descriptor_conflicts() {
        let (mut program, types, _) = exact_callable_fixture(true);
        let Terminator::TailCallIndirect { known_function, .. } =
            &mut program.functions[0].blocks[0].terminator
        else {
            unreachable!()
        };
        *known_function = Some(3);
        let error = validate_program(&program, &types, MirPhase::Raw).unwrap_err();
        assert!(error.message.contains("no receiver ABI"));
    }

    #[test]
    fn known_receiver_validation_requires_an_exact_shared_target_and_observed_receiver() {
        let mut types = Type::predefined();
        let shared = types.len() as TypeId;
        types.push(Type::RefShared { referent: UNIT });

        let mut caller = function(
            vec![
                block(
                    0,
                    Terminator::CallKnownReceiver {
                        result: Some(3),
                        function: 1,
                        receiver: Operand {
                            register: 1,
                            mode: UseMode::Copy,
                        },
                        args: vec![move_operand(2)],
                        normal: Edge {
                            target: 1,
                            args: vec![],
                        },
                    },
                ),
                BasicBlock {
                    id: 1,
                    params: vec![BlockParam {
                        register: 3,
                        ty: I64,
                        role: BlockParamRole::CallResult,
                    }],
                    statements: vec![],
                    terminator: Terminator::Return {
                        value: Some(move_operand(3)),
                    },
                },
            ],
            vec![UNIT, shared, I64, I64],
        );
        caller.params = vec![shared, I64];
        caller.result = I64;
        caller.features = infer_feature_bits(&caller);

        let mut target = function(
            vec![block(
                0,
                Terminator::Return {
                    value: Some(move_operand(1)),
                },
            )],
            vec![shared, I64],
        );
        target.declaration = 1;
        target.params = vec![I64];
        target.result = I64;
        target.receiver_mode = Some(0);
        target.receiver_type = shared;
        target.features = infer_feature_bits(&target);

        let valid = Program {
            functions: vec![caller.clone(), target.clone()],
        };
        validate_program(&valid, &types, MirPhase::Raw).unwrap();

        let Terminator::CallKnownReceiver { receiver, .. } = &mut caller.blocks[0].terminator
        else {
            unreachable!()
        };
        receiver.mode = UseMode::Move;
        let invalid = Program {
            functions: vec![caller, target],
        };
        let error = validate_program(&invalid, &types, MirPhase::Raw).unwrap_err();
        assert!(error.message.contains("exact mode-0 target"), "{error}");
    }

    #[test]
    fn tail_resume_validates_as_a_terminal_resumption_and_protects_transfers() {
        let mut types = Type::predefined();
        let resumption = types.len() as TypeId;
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: 1,
            upper_uses: Some(1),
            identity_name: "tail-resume".into(),
            copy: false,
        });
        let mut body = function(
            vec![block(
                0,
                Terminator::TailResume {
                    resumption: move_operand(1),
                    receiver_mode: 2,
                    value: move_operand(2),
                },
            )],
            vec![UNIT, resumption, I64],
        );
        body.params = vec![resumption, I64];
        body.result = I64;

        let valid = program(body.clone());
        validate_program(&valid, &types, MirPhase::Raw).unwrap();
        let features = infer_feature_bits(&body);
        assert!(features.contains(FeatureBits::RESUMPTIONS));
        assert!(features.contains(FeatureBits::TAIL_CALLS));

        let mut borrowed_one_shot = body.clone();
        let Terminator::TailResume {
            resumption,
            receiver_mode,
            ..
        } = &mut borrowed_one_shot.blocks[0].terminator
        else {
            unreachable!()
        };
        resumption.mode = UseMode::Copy;
        *receiver_mode = 0;
        let error =
            validate_program(&program(borrowed_one_shot), &types, MirPhase::Raw).unwrap_err();
        assert!(error.message.contains("tail resume"), "{error}");

        let mut wrong_output = body.clone();
        wrong_output.result = UNIT;
        let error = validate_program(&program(wrong_output), &types, MirPhase::Raw).unwrap_err();
        assert!(error.message.contains("tail resume"), "{error}");

        let mut elaborated = program(body);
        import_and_validate_place_flow(&mut elaborated, &types).unwrap();
        elaborate_cleanup(&mut elaborated, &types).unwrap();
        let flow = &elaborated.functions[0].flow;
        assert_eq!(flow.resumptions.len(), 1);
        assert!(!flow.resumptions[0].cancel);
        let (_, plan) = flow
            .plan_for(&CleanupEdge::TailCall { block: 0 })
            .expect("tail resume has an abandoning-edge cleanup plan");
        assert_eq!(plan.protected, vec![1, 2]);
    }

    #[test]
    fn exact_callable_global_simplify_is_deterministic() {
        let (program, types, _) = exact_callable_fixture(false);
        let mut first = program.clone();
        let mut second = program;
        let first_report = optimize_program(&mut first, &types, OptimizationLevel::O2).unwrap();
        let second_report = optimize_program(&mut second, &types, OptimizationLevel::O2).unwrap();
        assert_eq!(first, second);
        assert_eq!(first_report, second_report);
    }

    #[test]
    fn scheduler_uses_the_exact_level_sequences_and_distinct_fixed_points() {
        use PassId::*;

        let mandatory = [
            ValidateRawMir,
            ImportAndValidatePlaceFlow,
            ElaborateCleanup,
            ValidateCleanupMir,
            NormalizeCfg,
        ];
        let o1 = [
            SparseSimplify,
            ScalarizeLocals,
            SimplifyCleanup,
            SpecializeDirectCalls,
        ];
        let post_simplify = [NormalizeCfg, SparseSimplify];
        let post_specialization = [SpecializeDirectCalls];
        let o2 = [
            GlobalSimplify,
            ScalarizeCallables,
            SpecializeControl,
            SpecializeCleanup,
            InlineByCost,
            SparseSimplify,
        ];
        let proof_erasure = [EraseLoanProofsAndScalarizedReferences];
        let bytecode_input = [ValidateBytecodeInput];
        let tail = [FormTailCallsAndHoist];
        let o3_second = [
            GlobalSimplify,
            SpecializeControl,
            InlineByCost,
            SparseSimplify,
        ];

        let ids = |level| {
            schedule_for(level)
                .passes
                .into_iter()
                .map(|report| report.pass)
                .collect::<Vec<_>>()
        };
        assert_eq!(
            ids(OptimizationLevel::O0),
            mandatory
                .into_iter()
                .chain(proof_erasure)
                .chain(bytecode_input)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            ids(OptimizationLevel::O1),
            mandatory
                .into_iter()
                .chain(o1)
                .chain(post_simplify)
                .chain(proof_erasure)
                .chain(bytecode_input)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            ids(OptimizationLevel::O2),
            mandatory
                .into_iter()
                .chain(o1)
                .chain(o2)
                .chain(post_simplify)
                .chain(post_specialization)
                .chain(post_simplify)
                .chain(proof_erasure)
                .chain(tail)
                .chain(bytecode_input)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            ids(OptimizationLevel::O3),
            mandatory
                .into_iter()
                .chain(o1)
                .chain(o2)
                .chain(o3_second)
                .chain(post_simplify)
                .chain(post_specialization)
                .chain(post_simplify)
                .chain(proof_erasure)
                .chain(tail)
                .chain(bytecode_input)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn fixed_points_stop_on_unchanged_and_budget_exhaustion_and_cap_at_three() {
        let report = |outcome| PassReport {
            pass: PassId::SparseSimplify,
            outcome,
            work_units: 1,
        };

        let mut unchanged_calls = 0;
        let unchanged = bounded_fixed_point(|| {
            unchanged_calls += 1;
            Some(report(PassOutcome::Unchanged))
        });
        assert_eq!(unchanged_calls, 1);
        assert_eq!(unchanged.len(), 1);

        let mut budget_calls = 0;
        let exhausted = bounded_fixed_point(|| {
            budget_calls += 1;
            Some(report(PassOutcome::BudgetExhausted))
        });
        assert_eq!(budget_calls, 1);
        assert_eq!(exhausted.len(), 1);

        let mut changed_calls = 0;
        let capped = bounded_fixed_point(|| {
            changed_calls += 1;
            Some(report(PassOutcome::Changed))
        });
        assert_eq!(changed_calls, FIXED_POINT_ROUNDS);
        assert_eq!(capped.len(), FIXED_POINT_ROUNDS);
    }

    #[test]
    fn o1_sparse_fixed_point_stops_immediately_after_actual_stabilization() {
        let types = Type::predefined();
        let mut entry = block(
            0,
            Terminator::Switch {
                discr: operand(0),
                cases: vec![(
                    Constant::U32(7),
                    Edge {
                        target: 1,
                        args: vec![],
                    },
                )],
                otherwise: Edge {
                    target: 2,
                    args: vec![],
                },
            },
        );
        entry.statements.push(instruction(InstructionKind::Const {
            dst: 0,
            value: Constant::U32(7),
        }));
        let mut candidate = program(function(
            vec![
                entry,
                block(1, Terminator::Return { value: None }),
                block(2, Terminator::Return { value: None }),
            ],
            vec![U32],
        ));

        let report = optimize_program(&mut candidate, &types, OptimizationLevel::O1).unwrap();
        let sparse = report
            .passes
            .iter()
            .filter(|entry| entry.pass == PassId::SparseSimplify)
            .map(|entry| entry.outcome)
            .collect::<Vec<_>>();
        assert_eq!(sparse, [PassOutcome::Changed, PassOutcome::Unchanged]);
        assert!(candidate.functions[0].blocks[0].statements.is_empty());
        assert!(matches!(
            candidate.functions[0].blocks[0].terminator,
            Terminator::Goto(Edge { target: 1, .. })
        ));
    }

    #[test]
    fn dense_register_compaction_rewrites_blocks_continuations_captures_and_cleanup() {
        let types = Type::predefined();
        let mut entry = block(
            0,
            Terminator::Perform {
                result: Some(10),
                protocol: 0,
                operation: 0,
                payloads: vec![Operand {
                    register: 4,
                    mode: UseMode::Move,
                }],
                capture: crate::compiler_mir::ContinuationCapture {
                    captured_owners: vec![7, 9],
                    captured_references: vec![9],
                    captured_residuals: vec![crate::compiler_mir::ResidualCapture {
                        register: 7,
                        initialized_fields: vec![true, false],
                    }],
                    cancellation_safe: false,
                },
                resume: Some(Edge {
                    target: 1,
                    args: vec![operand(4)],
                }),
            },
        );
        entry.statements.extend([
            instruction(InstructionKind::Const {
                dst: 4,
                value: Constant::I64(4),
            }),
            instruction(InstructionKind::Const {
                dst: 7,
                value: Constant::I64(7),
            }),
            instruction(InstructionKind::Const {
                dst: 9,
                value: Constant::I64(9),
            }),
        ]);
        let mut resumed = block(
            1,
            Terminator::Return {
                value: Some(operand(11)),
            },
        );
        resumed.params = vec![
            BlockParam {
                register: 10,
                ty: I64,
                role: BlockParamRole::ResumeResult,
            },
            BlockParam {
                register: 11,
                ty: I64,
                role: BlockParamRole::Ordinary,
            },
        ];
        let mut candidate = program(function(
            vec![entry, resumed],
            vec![UNIT, I64, U8, U16, I64, U32, U64, I64, I128, I64, I64, I64],
        ));
        candidate.functions[0].params = vec![I64];
        candidate.functions[0].result = I64;
        candidate.functions[0].return_cleanup = vec![9, 7];
        candidate.functions[0].flow.drop_flags.extend([
            crate::compiler_mir::DropFlagFact {
                flag: 4,
                owner: 7,
                field: Some(0),
            },
            crate::compiler_mir::DropFlagFact {
                flag: 4,
                owner: 7,
                field: Some(1),
            },
        ]);
        candidate.functions[0].phase = MirPhase::Optimized;
        candidate.functions[0].features = infer_feature_bits(&candidate.functions[0]);

        assert!(compact_live_registers_for_emission(&mut candidate, &types).unwrap());
        let compact = &candidate.functions[0];
        assert_eq!(
            compact.register_types,
            vec![UNIT, I64, I64, I64, I64, I64, I64]
        );
        assert_eq!(compact.return_cleanup, vec![4, 3]);
        assert_eq!(
            compact.flow.drop_flags,
            vec![
                crate::compiler_mir::DropFlagFact {
                    flag: 2,
                    owner: 3,
                    field: Some(0),
                },
                crate::compiler_mir::DropFlagFact {
                    flag: 2,
                    owner: 3,
                    field: Some(1),
                },
            ],
            "register compaction must retain distinct per-field drop flags",
        );
        assert_eq!(compact.blocks[1].params[0].register, 5);
        assert_eq!(compact.blocks[1].params[1].register, 6);
        assert!(matches!(
            &compact.blocks[0].terminator,
            Terminator::Perform {
                result: Some(5),
                payloads,
                capture,
                resume: Some(Edge { args, .. }),
                ..
            } if payloads[0].register == 2
                && capture.captured_owners == [3, 4]
                && capture.captured_references == [4]
                && capture.captured_residuals[0].register == 3
                && args[0].register == 2
        ));
        assert!(matches!(
            compact.blocks[1].terminator,
            Terminator::Return {
                value: Some(Operand { register: 6, .. })
            }
        ));

        let once = candidate.clone();
        assert!(!compact_live_registers_for_emission(&mut candidate, &types).unwrap());
        assert_eq!(candidate, once, "register compaction must be idempotent");
    }

    #[test]
    fn dense_register_compaction_is_deterministic_and_mandatory_level_independent() {
        let types = Type::predefined();
        let fixture = || {
            let mut entry = block(
                0,
                Terminator::Return {
                    value: Some(operand(2)),
                },
            );
            entry.statements.push(instruction(InstructionKind::Const {
                dst: 2,
                value: Constant::U32(41),
            }));
            let mut function = function(vec![entry], vec![UNIT, I64, U32]);
            function.result = U32;
            program(function)
        };

        let mut outputs = Vec::new();
        for level in [
            OptimizationLevel::O0,
            OptimizationLevel::O1,
            OptimizationLevel::O2,
            OptimizationLevel::O3,
        ] {
            let mut first = fixture();
            let mut second = fixture();
            optimize_program(&mut first, &types, level).unwrap();
            optimize_program(&mut second, &types, level).unwrap();
            assert!(compact_live_registers_for_emission(&mut first, &types).unwrap());
            assert!(compact_live_registers_for_emission(&mut second, &types).unwrap());
            assert_eq!(first, second);
            assert_eq!(first.functions[0].register_types, vec![UNIT, U32]);
            assert!(matches!(
                first.functions[0].blocks[0].statements[0].kind,
                InstructionKind::Const { dst: 1, .. }
            ));
            assert!(matches!(
                first.functions[0].blocks[0].terminator,
                Terminator::Return {
                    value: Some(Operand { register: 1, .. })
                }
            ));
            outputs.push(first);
        }
        assert!(outputs.windows(2).all(|pair| pair[0] == pair[1]));
    }

    #[test]
    fn physical_register_reuse_requires_a_proven_empty_slot() {
        let types = Type::predefined();
        let mut entry = block(
            0,
            Terminator::Return {
                value: Some(move_operand(2)),
            },
        );
        entry.statements.extend([
            instruction(InstructionKind::Const {
                dst: 1,
                value: Constant::I64(10),
            }),
            instruction(InstructionKind::Drop {
                owner: move_operand(1),
            }),
            instruction(InstructionKind::Const {
                dst: 2,
                value: Constant::I64(20),
            }),
        ]);
        let mut body = function(vec![entry], vec![UNIT, I64, I64]);
        body.result = I64;
        body.phase = MirPhase::Optimized;
        body.features = infer_feature_bits(&body);
        let mut candidate = program(body);

        assert!(compact_live_registers_for_emission(&mut candidate, &types).unwrap());
        let lowered = &candidate.functions[0];
        assert_eq!(lowered.register_types, vec![UNIT, I64]);
        assert!(matches!(
            lowered.blocks[0].statements.as_slice(),
            [
                Instruction {
                    kind: InstructionKind::Const { dst: 1, .. },
                    ..
                },
                Instruction {
                    kind: InstructionKind::Drop {
                        owner: Operand { register: 1, .. }
                    },
                    ..
                },
                Instruction {
                    kind: InstructionKind::Const { dst: 1, .. },
                    ..
                },
            ]
        ));

        let mut not_empty = candidate.clone();
        not_empty.functions[0].phase = MirPhase::Optimized;
        not_empty.functions[0].register_types = vec![UNIT, I64, I64];
        not_empty.functions[0].blocks[0].statements.remove(1);
        not_empty.functions[0].blocks[0].statements[1] = instruction(InstructionKind::Const {
            dst: 2,
            value: Constant::I64(20),
        });
        if let Terminator::Return { value: Some(value) } =
            &mut not_empty.functions[0].blocks[0].terminator
        {
            value.register = 2;
        }
        not_empty.functions[0].flow.locals = vec![];
        not_empty.functions[0].features = infer_feature_bits(&not_empty.functions[0]);
        compact_live_registers_for_emission(&mut not_empty, &types).unwrap();
        assert_eq!(not_empty.functions[0].register_types, vec![UNIT, I64, I64]);
    }

    #[test]
    fn ended_reference_slots_reuse_but_referent_places_remain_pinned() {
        let mut types = Type::predefined();
        let shared = types.len() as TypeId;
        types.push(Type::RefShared { referent: I64 });
        let mut entry = block(0, Terminator::Return { value: None });
        entry.statements.extend([
            instruction(InstructionKind::Borrow {
                dst: 2,
                src: 1,
                unique: false,
            }),
            instruction(InstructionKind::EndBorrow { reference: 2 }),
            instruction(InstructionKind::Borrow {
                dst: 3,
                src: 1,
                unique: false,
            }),
            instruction(InstructionKind::EndBorrow { reference: 3 }),
        ]);
        let mut body = function(vec![entry], vec![UNIT, I64, shared, shared]);
        body.params = vec![I64];
        body.phase = MirPhase::Optimized;
        body.flow.locals = body
            .register_types
            .iter()
            .map(|&ty| LocalFact::conservative(ty, &types[ty as usize]))
            .collect();
        body.flow.locals[1].storage = crate::compiler_mir::StorageClass::Place;
        body.flow.loans = vec![
            crate::compiler_mir::LoanFact {
                kind: crate::compiler_mir::LoanKind::Shared,
                reference: 2,
                borrowed: crate::compiler_mir::Place {
                    base: 1,
                    projection: vec![],
                },
                parent: None,
                region: RegionId(0),
                issued_block: 0,
                source: SourceInfoId(0),
            },
            crate::compiler_mir::LoanFact {
                kind: crate::compiler_mir::LoanKind::Shared,
                reference: 3,
                borrowed: crate::compiler_mir::Place {
                    base: 1,
                    projection: vec![],
                },
                parent: None,
                region: RegionId(1),
                issued_block: 0,
                source: SourceInfoId(0),
            },
        ];
        body.features = infer_feature_bits(&body);
        let mut candidate = program(body);

        compact_live_registers_for_emission(&mut candidate, &types).unwrap();
        let lowered = &candidate.functions[0];
        assert_eq!(lowered.register_types, vec![UNIT, I64, shared]);
        assert_eq!(
            lowered
                .flow
                .loans
                .iter()
                .map(|loan| (loan.reference, loan.borrowed.base, loan.region))
                .collect::<Vec<_>>(),
            vec![(2, 1, RegionId(0)), (2, 1, RegionId(1))]
        );
        assert!(matches!(
            lowered.blocks[0].statements.as_slice(),
            [
                Instruction {
                    kind: InstructionKind::Borrow { dst: 2, src: 1, .. },
                    ..
                },
                Instruction {
                    kind: InstructionKind::EndBorrow { reference: 2 },
                    ..
                },
                Instruction {
                    kind: InstructionKind::Borrow { dst: 2, src: 1, .. },
                    ..
                },
                Instruction {
                    kind: InstructionKind::EndBorrow { reference: 2 },
                    ..
                },
            ]
        ));
    }

    #[test]
    fn hostile_lowered_register_overwrite_without_emptying_is_rejected() {
        let types = Type::predefined();
        let mut entry = block(0, Terminator::Return { value: None });
        entry.statements.extend([
            instruction(InstructionKind::Const {
                dst: 1,
                value: Constant::I64(1),
            }),
            instruction(InstructionKind::Const {
                dst: 1,
                value: Constant::I64(2),
            }),
        ]);
        let mut body = function(vec![entry], vec![UNIT, I64]);
        body.phase = MirPhase::Lowered;
        body.features = infer_feature_bits(&body);
        let mut hostile = program(body);

        let failure = compact_live_registers_for_emission(&mut hostile, &types).unwrap_err();
        assert!(failure.message.contains("defined by both"), "{failure}");
    }

    #[test]
    fn abi_register_order_is_pinned_independent_of_last_use_order() {
        let types = Type::predefined();
        let mut entry = block(
            0,
            Terminator::Return {
                value: Some(move_operand(3)),
            },
        );
        entry.statements.extend([
            instruction(InstructionKind::Drop {
                owner: Operand {
                    register: 2,
                    mode: UseMode::Move,
                },
            }),
            instruction(InstructionKind::Move {
                dst: 3,
                src: move_operand(1),
            }),
        ]);
        let mut body = function(vec![entry], vec![UNIT, I64, U32, I64]);
        body.params = vec![I64, U32];
        body.result = I64;
        body.phase = MirPhase::Optimized;
        body.features = infer_feature_bits(&body);
        let mut candidate = program(body);

        compact_live_registers_for_emission(&mut candidate, &types).unwrap();
        assert_eq!(
            &candidate.functions[0].register_types[..3],
            &[UNIT, I64, U32]
        );
    }

    #[test]
    fn non_abi_address_taken_owner_is_never_recolored() {
        let mut types = Type::predefined();
        let shared = types.len() as TypeId;
        types.push(Type::RefShared { referent: I64 });
        let mut entry = block(0, Terminator::Return { value: None });
        entry.statements.extend([
            instruction(InstructionKind::Const {
                dst: 1,
                value: Constant::I64(1),
            }),
            instruction(InstructionKind::Borrow {
                dst: 2,
                src: 1,
                unique: false,
            }),
            instruction(InstructionKind::EndBorrow { reference: 2 }),
            instruction(InstructionKind::Drop {
                owner: move_operand(1),
            }),
            instruction(InstructionKind::Const {
                dst: 3,
                value: Constant::I64(2),
            }),
            instruction(InstructionKind::Drop {
                owner: move_operand(3),
            }),
        ]);
        let mut body = function(vec![entry], vec![UNIT, I64, shared, I64]);
        body.phase = MirPhase::Optimized;
        body.features = infer_feature_bits(&body);
        let mut candidate = program(body);

        compact_live_registers_for_emission(&mut candidate, &types).unwrap();
        assert_eq!(
            candidate.functions[0].register_types,
            vec![UNIT, I64, shared, I64]
        );
        assert!(matches!(
            candidate.functions[0].blocks[0].statements[4].kind,
            InstructionKind::Const { dst: 3, .. }
        ));
    }

    #[test]
    fn checked_layout_groups_typed_control_regions_after_hot_rpo() {
        let mut entry = block(
            0,
            Terminator::Goto(Edge {
                target: 1,
                args: vec![],
            }),
        );
        entry
            .statements
            .push(instruction(InstructionKind::LabelPush {
                label: crate::compiler_mir::LabelId(0),
                result: 1,
                target: 2,
            }));
        let normal = block(1, Terminator::Return { value: None });
        let label = block(2, Terminator::Return { value: None });
        let mut cleanup = block(3, Terminator::Return { value: None });
        cleanup.params.push(BlockParam {
            register: 1,
            ty: I64,
            role: BlockParamRole::ProtectedExitValue,
        });
        let handler = block(4, Terminator::Return { value: None });
        let mut resumption = block(5, Terminator::Return { value: None });
        resumption.params.push(BlockParam {
            register: 1,
            ty: I64,
            role: BlockParamRole::ResumeResult,
        });
        let mut body = function(
            vec![resumption, handler, cleanup, label, normal, entry],
            vec![UNIT, I64],
        );
        body.flow.labels.push(crate::compiler_mir::LabelFact {
            result_type: I64,
            scope: ScopeId(0),
            destination: 2,
        });
        body.flow.handlers.push(HandlerSiteFact {
            block: 4,
            scope: ScopeId(0),
        });

        assert!(layout_checked_blocks_for_emission(&mut body).unwrap());
        assert_eq!(
            body.blocks.iter().map(|block| block.id).collect::<Vec<_>>(),
            vec![0, 1, 2, 3, 4, 5]
        );
        assert!(!layout_checked_blocks_for_emission(&mut body).unwrap());
    }

    #[test]
    fn import_rejects_exported_facts_that_mismatch_the_registers() {
        let types = Type::predefined();
        let mut body = function(
            vec![block(0, Terminator::Return { value: None })],
            vec![UNIT, I64],
        );
        body.flow.provenance = crate::compiler_mir::FlowProvenance::Exported;
        body.flow
            .locals
            .push(crate::compiler_mir::LocalFact::conservative(
                UNIT,
                &types[UNIT as usize],
            ));
        body.flow
            .locals
            .push(crate::compiler_mir::LocalFact::conservative(
                UNIT,
                &types[UNIT as usize],
            ));
        let mut program = program(body);
        let error = optimize_program(&mut program, &types, OptimizationLevel::O0).unwrap_err();
        assert!(
            error
                .message
                .contains("imported PlaceFlow local fact for r1 names type"),
            "{error}"
        );
    }

    #[test]
    fn import_rejects_a_hostile_exported_join_predecessor_set() {
        let types = Type::predefined();
        let mut entry = block(
            0,
            Terminator::Switch {
                discr: operand(1),
                cases: vec![(
                    Constant::U32(1),
                    Edge {
                        target: 1,
                        args: vec![],
                    },
                )],
                otherwise: Edge {
                    target: 2,
                    args: vec![],
                },
            },
        );
        entry.statements.push(Instruction {
            span: Span::default(),
            kind: InstructionKind::Const {
                dst: 1,
                value: Constant::U32(1),
            },
        });
        let mut body = function(
            vec![
                entry,
                block(
                    1,
                    Terminator::Goto(Edge {
                        target: 3,
                        args: vec![],
                    }),
                ),
                block(
                    2,
                    Terminator::Goto(Edge {
                        target: 3,
                        args: vec![],
                    }),
                ),
                block(3, Terminator::Return { value: None }),
            ],
            vec![UNIT, U32],
        );
        body.flow.provenance = crate::compiler_mir::FlowProvenance::Exported;
        body.flow.joins.push(crate::compiler_mir::JoinSiteFact {
            block: 3,
            incoming: vec![1],
        });
        let mut program = program(body);
        let error = optimize_program(&mut program, &types, OptimizationLevel::O0).unwrap_err();
        assert!(error.message.contains("do not match CFG joins"), "{error}");
    }

    #[test]
    fn import_rejects_a_hostile_indirect_call_outward_row() {
        let mut types = Type::predefined();
        let callable = types.len() as TypeId;
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            capture_type: UNIT,
            receiver_mode: 0,
            identity_name: "hostile-row".into(),
            copy: true,
            zero_use_allowed: true,
        });
        let mut body = function(
            vec![
                block(
                    0,
                    Terminator::CallIndirect {
                        result: None,
                        callable: operand(1),
                        known_function: None,
                        receiver_mode: 0,
                        cleanup_callable: false,
                        args: vec![],
                        normal: Edge {
                            target: 1,
                            args: vec![],
                        },
                    },
                ),
                block(1, Terminator::Return { value: None }),
            ],
            vec![UNIT, callable],
        );
        body.flow.provenance = crate::compiler_mir::FlowProvenance::Exported;
        body.flow
            .indirect_calls
            .push(crate::compiler_mir::IndirectCallSiteFact {
                block: 0,
                outward_protocols: vec![7],
                capture: ContinuationCapture {
                    captured_owners: vec![],
                    captured_references: vec![],
                    captured_residuals: vec![],
                    cancellation_safe: true,
                },
            });
        let mut program = program(body);
        let error = optimize_program(&mut program, &types, OptimizationLevel::O0).unwrap_err();
        assert!(error.message.contains("indirect-call sites"), "{error}");
    }

    #[test]
    fn elaborate_cleanup_attaches_plans_to_every_abandoning_edge() {
        let types = Type::predefined();
        let return_block = BasicBlock {
            id: 0,
            params: vec![],
            statements: vec![
                Instruction {
                    span: Span::default(),
                    kind: InstructionKind::Const {
                        dst: 1,
                        value: Constant::I64(7),
                    },
                },
                Instruction {
                    span: Span::default(),
                    kind: InstructionKind::Drop {
                        owner: Operand {
                            register: 1,
                            mode: UseMode::Move,
                        },
                    },
                },
            ],
            terminator: Terminator::Return { value: None },
        };
        let terminal = BasicBlock {
            id: 0,
            params: vec![],
            statements: vec![],
            terminator: Terminator::Perform {
                result: None,
                protocol: 0,
                operation: 0,
                payloads: vec![],
                capture: ContinuationCapture {
                    captured_owners: vec![1],
                    captured_references: vec![],
                    captured_residuals: vec![],
                    cancellation_safe: true,
                },
                resume: None,
            },
        };
        let mut returns = function(vec![return_block], vec![UNIT, I64]);
        let mut aborts = function(vec![terminal], vec![UNIT, I64]);
        aborts.declaration = 1;
        aborts.params = vec![I64];
        aborts.outward_protocols = vec![0];
        let mut program = Program {
            functions: vec![returns.clone(), aborts.clone()],
        };
        import_and_validate_place_flow(&mut program, &types).unwrap();
        elaborate_cleanup(&mut program, &types).unwrap();

        let returned = &program.functions[0].flow;
        let (_, plan) = returned
            .plan_for(&CleanupEdge::Return { block: 0 })
            .expect("return edge has a plan");
        assert_eq!(plan.actions, vec![CleanupAction::Destroy(1)]);

        let abandoned = &program.functions[1].flow;
        let site = &abandoned.performs[0];
        assert!(!site.resumptive);
        let frame = site
            .frame_cleanup
            .expect("terminal perform has frame cleanup");
        let plan = &abandoned.cleanup_plans[frame.index()];
        assert_eq!(plan.edge, CleanupEdge::TerminalPerform { block: 0 });
        assert!(
            plan.actions.contains(&CleanupAction::Destroy(1)),
            "{plan:?}"
        );
        validate_flow_and_cleanup(&program, &types).unwrap();

        // The recorded plans are exhaustively revalidated: silently mutating
        // ownership-relevant MIR without invalidation is rejected.
        returns.blocks[0].statements.pop();
        returns.blocks[0].terminator = Terminator::Return {
            value: Some(move_operand(1)),
        };
        aborts.declaration = 1;
        let stale = Program {
            functions: vec![
                Function {
                    flow: program.functions[0].flow.clone(),
                    phase: MirPhase::Cleanup,
                    ..returns
                },
                program.functions[1].clone(),
            ],
        };
        let error = validate_flow_and_cleanup(&stale, &types).unwrap_err();
        assert!(error.message.contains("cleanup plans are stale"), "{error}");
    }

    #[test]
    fn label_and_leave_cleanup_edges_have_a_stable_representation() {
        use crate::compiler_mir::{
            CleanupPlanFact, LabelFact, LabelId, LoanId, PlaceFlow, ScopeId,
        };
        // Source labels remain gated in the bootstrap frontend; the fact
        // shapes still represent their cleanup boundaries losslessly.
        let mut flow = PlaceFlow::default();
        flow.labels.push(LabelFact {
            result_type: I64,
            scope: ScopeId(0),
            destination: 4,
        });
        flow.cleanup_plans.push(CleanupPlanFact {
            edge: CleanupEdge::Leave {
                block: 2,
                label: LabelId(0),
            },
            source_scope: ScopeId(1),
            target_scope: ScopeId(0),
            actions: vec![
                CleanupAction::EndBorrow(LoanId(3)),
                CleanupAction::Destroy(7),
            ],
            protected: vec![9],
        });
        let (id, plan) = flow
            .plan_for(&CleanupEdge::Leave {
                block: 2,
                label: LabelId(0),
            })
            .expect("leave edge resolves its plan");
        assert_eq!(id.index(), 0);
        assert_eq!(plan.protected, vec![9]);
        assert!(flow.canonical_summary().contains("labels=1"));
        assert!(flow.canonical_summary().contains("plans=1"));
    }

    #[test]
    fn labels_validate_as_control_barriers_and_leave_protects_its_edge_value() {
        use crate::compiler_mir::{LabelFact, LabelId, ScopeFact, ScopeId};

        let types = Type::predefined();
        let label = LabelId(0);
        let mut entry = block(
            0,
            Terminator::Leave {
                label,
                target: Edge {
                    target: 1,
                    args: vec![move_operand(1)],
                },
            },
        );
        entry
            .statements
            .push(instruction(InstructionKind::LabelPush {
                label,
                result: 2,
                target: 1,
            }));
        let destination = BasicBlock {
            id: 1,
            params: vec![BlockParam {
                register: 2,
                ty: I64,
                role: BlockParamRole::ProtectedExitValue,
            }],
            statements: vec![],
            terminator: Terminator::Return {
                value: Some(move_operand(2)),
            },
        };
        let mut body = function(vec![entry, destination], vec![UNIT, I64, I64]);
        body.params = vec![I64];
        body.result = I64;
        body.flow.scopes.push(ScopeFact {
            parent: None,
            owners: vec![],
        });
        body.flow.labels.push(LabelFact {
            result_type: I64,
            scope: ScopeId(0),
            destination: 1,
        });
        body.features = infer_feature_bits(&body);

        assert!(body.features.contains(FeatureBits::CONTROL_FLOW));
        validate_program(&program(body.clone()), &types, MirPhase::Raw).unwrap();
        let elaboration = derive_cleanup_elaboration(&body, &types).unwrap();
        let plan = elaboration
            .plans
            .iter()
            .find(|plan| plan.edge == CleanupEdge::Leave { block: 0, label })
            .expect("Leave has a cleanup plan");
        assert_eq!(plan.protected, vec![1]);

        let mut optimized = program(body.clone());
        let report = optimize_program(&mut optimized, &types, OptimizationLevel::O0).unwrap();
        assert!(report.passes.iter().any(|entry| {
            entry.pass == PassId::ValidateBytecodeInput
                && entry.outcome == PassOutcome::Unchanged
                && entry.work_units > 0
        }));
        let lists = derive_cleanup_lists(&optimized.functions[0], &types).unwrap();
        let boundaries = derive_leave_cleanup_boundaries(&optimized.functions[0], &lists).unwrap();
        assert_eq!(
            boundaries.get(&0),
            Some(&LeaveCleanupBoundary {
                source: vec![],
                target: vec![],
            })
        );
        let anchors = derive_leave_cleanup_anchors(&optimized.functions[0], &lists).unwrap();
        assert_eq!(
            anchors.get(&0),
            Some(&LeaveCleanupAnchors {
                source: vec![2],
                target: vec![2],
            })
        );

        let hostile_lists = BTreeMap::from([(0, vec![vec![1], vec![3]]), (1, vec![vec![4]])]);
        let error = derive_leave_cleanup_boundaries(&body, &hostile_lists).unwrap_err();
        assert!(error.message.contains("not a suffix"), "{error}");

        let mut invalid = body;
        let InstructionKind::LabelPush { target, .. } = &mut invalid.blocks[0].statements[0].kind
        else {
            unreachable!()
        };
        *target = 0;
        let error = validate_program(&program(invalid), &types, MirPhase::Raw).unwrap_err();
        assert!(error.message.contains("LabelPush disagrees"), "{error}");
    }

    #[test]
    fn leave_sources_retire_distinct_copy_interlopers_before_one_common_target() {
        let types = Type::predefined();
        let label = LabelId(0);
        let destination = BasicBlock {
            id: 2,
            params: vec![BlockParam {
                register: 7,
                ty: I64,
                role: BlockParamRole::ProtectedExitValue,
            }],
            statements: vec![],
            terminator: Terminator::Return {
                value: Some(move_operand(7)),
            },
        };
        let mut body = function(
            vec![
                block(
                    0,
                    Terminator::Leave {
                        label,
                        target: Edge {
                            target: 2,
                            args: vec![move_operand(5)],
                        },
                    },
                ),
                block(
                    1,
                    Terminator::Leave {
                        label,
                        target: Edge {
                            target: 2,
                            args: vec![move_operand(6)],
                        },
                    },
                ),
                destination,
            ],
            vec![UNIT, I64, I64, I64, I64, I64, I64, I64],
        );
        body.flow.locals = bridged_locals(&body, &types);
        let lists = BTreeMap::from([
            (0, vec![vec![5, 1, 3, 2]]),
            (1, vec![vec![6, 1, 4, 2]]),
            (2, vec![vec![7, 1, 2]]),
        ]);

        let boundaries = derive_leave_cleanup_boundaries(&body, &lists).unwrap();
        assert_eq!(boundaries[&0].source, [3, 1, 2]);
        assert_eq!(boundaries[&1].source, [4, 1, 2]);
        assert_eq!(boundaries[&0].target, [1, 2]);
        assert_eq!(boundaries[&1].target, [1, 2]);

        let anchors = derive_leave_cleanup_anchors(&body, &lists).unwrap();
        assert_eq!(anchors[&0].source, [3, 7, 1, 2]);
        assert_eq!(anchors[&1].source, [4, 7, 1, 2]);
        assert_eq!(anchors[&0].target, [7, 1, 2]);
        assert_eq!(anchors[&1].target, [7, 1, 2]);

        body.flow.locals[3].ownership = OwnershipCategory::Owned;
        let error = derive_leave_cleanup_boundaries(&body, &lists).unwrap_err();
        assert!(error.message.contains("not a suffix"), "{error}");
        body.flow.locals[3].ownership = OwnershipCategory::CopyValue;
        body.flow.locals[3].drop_glue = DropGlueKind::Custom;
        let error = derive_leave_cleanup_boundaries(&body, &lists).unwrap_err();
        assert!(error.message.contains("not a suffix"), "{error}");
    }

    #[test]
    fn leave_boundary_commutes_shared_proof_handles_but_not_unique_ones() {
        let mut types = Type::predefined();
        let shared = types.len() as TypeId;
        types.push(Type::RefShared { referent: I64 });
        let unique = types.len() as TypeId;
        types.push(Type::RefUnique { referent: I64 });
        let label = LabelId(0);
        let destination = BasicBlock {
            id: 1,
            params: vec![BlockParam {
                register: 7,
                ty: I64,
                role: BlockParamRole::ProtectedExitValue,
            }],
            statements: vec![],
            terminator: Terminator::Return {
                value: Some(move_operand(7)),
            },
        };
        let mut body = function(
            vec![
                block(
                    0,
                    Terminator::Leave {
                        label,
                        target: Edge {
                            target: 1,
                            args: vec![move_operand(5)],
                        },
                    },
                ),
                destination,
            ],
            vec![UNIT, shared, shared, shared, I64, I64, I64, I64],
        );
        body.flow.locals = bridged_locals(&body, &types);
        let lists = BTreeMap::from([(0, vec![vec![5, 1, 3, 2]]), (1, vec![vec![7, 1, 2]])]);

        let boundaries = derive_leave_cleanup_boundaries(&body, &lists).unwrap();
        assert_eq!(boundaries[&0].source, [3, 1, 2]);
        assert_eq!(boundaries[&0].target, [1, 2]);

        body.register_types[3] = unique;
        body.flow.locals = bridged_locals(&body, &types);
        let error = derive_leave_cleanup_boundaries(&body, &lists).unwrap_err();
        assert!(error.message.contains("not a suffix"), "{error}");
    }

    #[test]
    fn normalize_cfg_retains_a_label_push_hidden_destination() {
        use crate::compiler_mir::{LabelFact, LabelId, ScopeId};

        let types = Type::predefined();
        let label = LabelId(0);
        let mut entry = block(0, Terminator::Return { value: None });
        entry
            .statements
            .push(instruction(InstructionKind::LabelPush {
                label,
                result: 1,
                target: 1,
            }));
        let destination = BasicBlock {
            id: 1,
            params: vec![BlockParam {
                register: 1,
                ty: I64,
                role: BlockParamRole::ProtectedExitValue,
            }],
            statements: vec![],
            terminator: Terminator::Return { value: None },
        };
        let mut body = function(vec![entry, destination], vec![UNIT, I64]);
        body.flow.labels.push(LabelFact {
            result_type: I64,
            scope: ScopeId(0),
            destination: 1,
        });
        body.features = infer_feature_bits(&body);
        validate_program(&program(body.clone()), &types, MirPhase::Raw).unwrap();

        let (outcome, _) = normalize_cfg(&mut body, u64::MAX);

        assert_eq!(outcome, PassOutcome::Unchanged);
        assert!(body.blocks.iter().any(|block| block.id == 1));
        validate_program(&program(body), &types, MirPhase::Raw).unwrap();
    }

    #[test]
    fn budget_exhaustion_leaves_mir_and_flow_facts_byte_identical() {
        let types = Type::predefined();
        let mut body = function(
            vec![
                block(
                    0,
                    Terminator::Goto(Edge {
                        target: 1,
                        args: vec![],
                    }),
                ),
                block(1, Terminator::Return { value: None }),
            ],
            vec![UNIT],
        );
        body.phase = MirPhase::Cleanup;
        body.features = infer_feature_bits(&body);
        let mut program = program(body);
        let before = program.canonical_text();
        let fingerprint = program.fingerprint();
        let mut nothing = 0_u64;
        let report =
            run_transactional_pass(&mut program, PassId::NormalizeCfg, &types, &mut nothing);
        assert_eq!(report.outcome, PassOutcome::BudgetExhausted);
        assert_eq!(program.canonical_text(), before);
        assert_eq!(program.fingerprint(), fingerprint);
        assert_eq!(program.functions[0].invalid_analyses, 0);
    }

    #[test]
    fn every_local_optimizer_pass_is_transactional_at_a_zero_budget() {
        let types = Type::predefined();
        let mut body = function(
            vec![
                block(
                    0,
                    Terminator::Goto(Edge {
                        target: 1,
                        args: vec![],
                    }),
                ),
                block(1, Terminator::Return { value: None }),
            ],
            vec![UNIT],
        );
        body.phase = MirPhase::Cleanup;
        body.features = infer_feature_bits(&body);
        let original = program(body);
        for pass in [
            PassId::NormalizeCfg,
            PassId::SparseSimplify,
            PassId::ScalarizeLocals,
            PassId::SimplifyCleanup,
            PassId::GlobalSimplify,
            PassId::SpecializeCleanup,
            PassId::EraseLoanProofsAndScalarizedReferences,
        ] {
            let mut candidate = original.clone();
            let before = candidate.canonical_text();
            let fingerprint = candidate.fingerprint();
            let mut budget = 0;
            let report = run_transactional_pass(&mut candidate, pass, &types, &mut budget);
            assert_eq!(report.pass, pass);
            assert_eq!(report.outcome, PassOutcome::BudgetExhausted, "{pass:?}");
            assert_eq!(candidate.canonical_text(), before, "{pass:?}");
            assert_eq!(candidate.fingerprint(), fingerprint, "{pass:?}");
            assert_eq!(candidate.functions[0].invalid_analyses, 0, "{pass:?}");
        }

        // The scheduling wrapper deliberately gives tail formation a fair
        // per-function cap even after the shared profitability budget is
        // depleted: this is the final stack-safety opportunity. Exercise the
        // transformation's zero local budget directly so its scratch-body
        // transaction remains covered without contradicting that scheduler
        // contract.
        let mut candidate = original.clone();
        let before = candidate.canonical_text();
        let fingerprint = candidate.fingerprint();
        let (outcome, _) =
            form_tail_calls_and_hoist(&mut candidate.functions[0], &types, &BTreeSet::new(), 0);
        assert_eq!(outcome, PassOutcome::BudgetExhausted);
        assert_eq!(candidate.canonical_text(), before);
        assert_eq!(candidate.fingerprint(), fingerprint);
        assert_eq!(candidate.functions[0].invalid_analyses, 0);
    }

    #[test]
    fn mir_report_does_not_claim_frontend_or_bytecode_lowering_ran() {
        let report = schedule_for(OptimizationLevel::O3);
        // The place-flow import and cleanup elaboration phases are real: they
        // must run (never SkippedUnavailable) and account for their work.
        for pass in [PassId::ImportAndValidatePlaceFlow, PassId::ElaborateCleanup] {
            assert!(report.passes.iter().any(|entry| {
                entry.pass == pass
                    && matches!(entry.outcome, PassOutcome::Changed | PassOutcome::Unchanged)
                    && entry.work_units > 0
            }));
        }
        assert!(report.passes.iter().any(|entry| {
            entry.pass == PassId::ValidateBytecodeInput
                && entry.outcome == PassOutcome::Unchanged
                && entry.work_units > 0
        }));
        for bytecode_pass in [PassId::LowerRegistersAndEdges, PassId::LayoutAndPeephole] {
            assert!(
                report
                    .passes
                    .iter()
                    .all(|entry| entry.pass != bytecode_pass),
                "the MIR-only report must not claim {bytecode_pass:?}"
            );
        }
    }
}
