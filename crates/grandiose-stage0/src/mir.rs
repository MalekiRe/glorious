//! Ownership-aware MIR lowered only from Typed Core and PlaceFlow.

use crate::{
    core::{
        CallableId, CaptureEnvironment, CaptureMode, ClosureCapture, CoreCompletionClause,
        CoreHandlerClause, CoreHandlerResumption, CoreId, CoreKind, CorePattern, CorePlace,
        EnvironmentBrand, ResumptionId, TypedBody,
    },
    identity::{DefKey, Digest},
    instance::InstanceKey,
    placeflow::PlaceFlow,
    types::{GenericArgument, Type},
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MirLocal(pub u32);
/// Body-local basic-block identity. It never crosses a MIR body boundary.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MirBlockId(pub u32);
/// Pattern decisions in MIR remain source-free and carry exact field types so
/// the verifier need not consult compiler interface tables to validate them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MirPattern {
    Any,
    Literal(String),
    Tuple(Vec<MirPattern>),
    Record {
        definition: DefKey,
        fields: Vec<MirPatternField>,
    },
    Enum {
        definition: DefKey,
        variant: u32,
        fields: Vec<MirPatternField>,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirPatternField {
    pub index: u32,
    pub ty: Type,
    pub pattern: MirPattern,
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
    /// IEEE-754 values are stored by bit pattern so MIR remains Eq/Hash-safe
    /// and artifact fingerprints never depend on host float formatting.
    ConstF64 {
        dst: MirLocal,
        bits: u64,
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
        effect: DefKey,
        effect_arguments: Vec<crate::GenericArgument>,
        operation: u32,
        payload_destinations: Vec<MirLocal>,
        resume_type: Type,
        continuation: MirContinuationPolicy,
        target: MirBlockId,
    },
    UninstallHandler,
    /// Materialize the identity of the innermost suspended continuation as a
    /// first-class, frame-safe callable snapshot.  The verifier binds this to
    /// an active handler frame; runtime aliases carry the same token rather
    /// than relying on a source binder spelling.
    CaptureResumption {
        dst: MirLocal,
    },
    Resume {
        value: MirLocal,
    },
    /// Resume a replayable continuation and re-enter the handler clause once
    /// that continuation completes, writing its result to `dst`.
    ResumeReturn {
        dst: MirLocal,
        value: MirLocal,
    },
    /// Consume the continuation denoted by an explicit snapshot.  This is
    /// distinct from legacy `Resume`, which consumes the innermost frame and
    /// remains useful for tail-resumption lowering.
    ResumeSnapshot {
        snapshot: MirLocal,
        value: MirLocal,
    },
    /// Decline the innermost suspended handler clause and re-perform its
    /// original operation against the next outer matching frame. The VM keeps
    /// the declined frame in the resumed continuation, which is the deep
    /// forwarding counterpart of `Resume`.
    Forward,
    /// Abandon the innermost suspended continuation. This is legal only for
    /// source continuation contracts that permit zero uses; the VM consumes
    /// the snapshot and continues the handler clause normally.
    Cancel,
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
    },
    /// Copy through a live loan without consuming it.
    DerefCopy {
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
    Call {
        dst: MirLocal,
        callee: DefKey,
        /// Preserved from Typed Core until the instance materializer replaces
        /// the declaration key with a concrete executable identity.
        generic_arguments: Vec<GenericArgument>,
        trait_instance: Option<MirTraitMethodInstance>,
        arguments: Vec<MirLocal>,
    },
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
        /// Sealed source-level environment evidence. It is intentionally
        /// proof-only at Stage 0: VM closure layout checks capture types and
        /// count independently, while this prevents a Core environment from
        /// being replayed into a different lifted callable during lowering.
        environment: Option<EnvironmentBrand>,
    },
    CallIndirect {
        dst: MirLocal,
        callee: MirLocal,
        arguments: Vec<MirLocal>,
    },
}

/// The executable use policy for a handler continuation. Typed Core remains
/// authoritative for exact lower/upper bounds; MIR preserves the distinction
/// the VM must enforce at runtime: affine continuations are consumed, whereas
/// unrestricted continuations retain a replayable snapshot.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MirContinuationPolicy {
    Consume,
    Replay,
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
    pub moved_places: Vec<crate::MoveFact>,
    pub active_loans: Vec<crate::LoanFact>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirBlock {
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
}
impl MirEditor {
    pub fn open(function: MirFunction) -> Result<Self, String> {
        function.validate()?;
        Ok(Self { function })
    }
    pub fn append_block(&mut self, block: MirBlock) -> Result<MirBlockId, String> {
        self.transaction(|function| {
            let id = MirBlockId(function.blocks.len() as u32);
            function.blocks.push(block);
            Ok(id)
        })
    }
    pub fn replace_terminator(
        &mut self,
        block: MirBlockId,
        terminator: MirTerminator,
    ) -> Result<(), String> {
        self.transaction(|function| {
            let block = function
                .blocks
                .get_mut(block.0 as usize)
                .ok_or_else(|| format!("MIR edit targets absent block {}", block.0))?;
            block.terminator = terminator;
            Ok(())
        })
    }
    pub fn replace_instructions(
        &mut self,
        block: MirBlockId,
        instructions: Vec<MirInstruction>,
    ) -> Result<(), String> {
        self.transaction(|function| {
            let block = function
                .blocks
                .get_mut(block.0 as usize)
                .ok_or_else(|| format!("MIR edit targets absent block {}", block.0))?;
            block.instructions = instructions;
            Ok(())
        })
    }
    pub fn finish(self) -> MirFunction {
        self.function
    }
    fn transaction<T>(
        &mut self,
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
        Ok(value)
    }
}
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct MirOptimizationReport {
    pub constant_folds: u32,
    pub eliminated_branches: u32,
}
/// Deterministic sparse constant propagation over validated MIR.
///
/// Arithmetic folds only use checked operations, so overflow and division by
/// zero remain explicit VM traps.  Facts cross only explicitly typed block
/// arguments, and a join retains a fact only when every incoming edge proves
/// the identical value. Transformations commit through `MirEditor`; failed
/// validation restores the unmodified graph.
pub fn optimize(function: MirFunction) -> Result<(MirFunction, MirOptimizationReport), String> {
    let mut editor = MirEditor::open(function)?;
    let mut report = MirOptimizationReport::default();
    let entry_constants = block_entry_constants(&editor.function);
    for (index, entry_constants) in entry_constants.into_iter().enumerate() {
        let block = editor.function.blocks[index].clone();
        let (instructions, constants, folds) =
            fold_block(block.instructions, entry_constants.unwrap_or_default());
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
    let function = editor.finish();
    function.validate()?;
    Ok((function, report))
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
        match instruction {
            MirInstruction::ConstI64 { dst, value } => {
                constants.insert(dst, Constant::I64(value));
            }
            MirInstruction::ConstF64 { dst, bits } => {
                constants.insert(dst, Constant::F64(bits));
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
fn constant_instruction(dst: MirLocal, value: Option<&Constant>) -> Option<MirInstruction> {
    match value {
        Some(Constant::I64(value)) => Some(MirInstruction::ConstI64 { dst, value: *value }),
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
        MirPattern::Record { fields, .. } => fields.is_empty(),
    }
}

fn literal_pattern_matches_constant(value: &Constant, pattern: &MirPattern) -> Option<bool> {
    let MirPattern::Literal(pattern) = pattern else {
        return None;
    };
    Some(match value {
        Constant::I64(value) => parse_i64_literal(pattern).is_ok_and(|pattern| pattern == *value),
        // Match the VM's IEEE equality rather than comparing bit patterns:
        // `-0.0` and `0.0` compare equal, while NaN never matches itself.
        Constant::F64(bits) => {
            parse_f64_literal(pattern).is_ok_and(|pattern| pattern == f64::from_bits(*bits))
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
        | MirInstruction::ConstF64 { dst, .. }
        | MirInstruction::ConstBool { dst, .. }
        | MirInstruction::ConstChar { dst, .. }
        | MirInstruction::ConstText { dst, .. }
        | MirInstruction::MakeTuple { dst, .. }
        | MirInstruction::MakeArray { dst, .. }
        | MirInstruction::MakeRecord { dst, .. }
        | MirInstruction::MakeEnum { dst, .. }
        | MirInstruction::ProjectRecord { dst, .. }
        | MirInstruction::ProjectTuple { dst, .. }
        | MirInstruction::UpdateRecord { dst, .. }
        | MirInstruction::PatternTest { dst, .. }
        | MirInstruction::Perform { dst, .. }
        | MirInstruction::Copy { dst, .. }
        | MirInstruction::Store { dst, .. }
        | MirInstruction::Move { dst, .. }
        | MirInstruction::Borrow { dst, .. }
        | MirInstruction::DerefCopy { dst, .. }
        | MirInstruction::NotBool { dst, .. }
        | MirInstruction::AddI64 { dst, .. }
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
        | MirInstruction::Call { dst, .. }
        | MirInstruction::MakeCallable { dst, .. }
        | MirInstruction::CallIndirect { dst, .. }
        | MirInstruction::CaptureResumption { dst } => Some(*dst),
        MirInstruction::InstallHandler { .. }
        | MirInstruction::UninstallHandler
        | MirInstruction::Resume { .. }
        | MirInstruction::ResumeReturn { .. }
        | MirInstruction::ResumeSnapshot { .. }
        | MirInstruction::Forward
        | MirInstruction::Cancel
        | MirInstruction::DerefStore { .. } => None,
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirLocalDecl {
    pub ty: Type,
    pub source: CoreId,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MirFunction {
    pub definition: DefKey,
    /// Captured environment entries occupy the prefix of `parameters`.
    pub captures: u32,
    pub parameters: Vec<MirLocal>,
    pub locals: Vec<MirLocalDecl>,
    pub result: Type,
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
    pub fn lower(definition: DefKey, body: &TypedBody, flow: &PlaceFlow) -> Self {
        Self::lower_with_bodies(definition, body, flow, &BTreeMap::new())
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
        let mut lowerer = Lowerer {
            body,
            bodies,
            definition,
            locals: vec![],
            values: BTreeMap::new(),
            named: BTreeMap::new(),
            lifted: BTreeMap::new(),
            instructions: vec![],
            diagnostics: vec![],
            leave_cleanup: MirCleanupPlan {
                moved_places: flow.moved_places.clone(),
                active_loans: flow.active_loans.clone(),
            },
            resumption_snapshots: BTreeMap::new(),
            label_rejoins: BTreeMap::new(),
            direct_resumption: None,
        };
        let parameters = body
            .parameters
            .iter()
            .map(|(name, ty)| {
                let local = lowerer.alloc(ty.clone(), CoreId(u32::MAX));
                lowerer.named.insert(name.clone(), local);
                local
            })
            .collect::<Vec<_>>();
        // Ordered refutable normal-completion clauses may leave after the
        // protected frame has been uninstalled.
        if let Some(function) =
            lowerer.lower_root_label_completion_chain(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        // An irrefutable direct normal-completion clause may leave after the
        // protected frame has been uninstalled.
        if let Some(function) =
            lowerer.lower_root_label_completion_leave(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        // A direct handler clause may itself take the lexically branded leave.
        // Claim that full frame-aware edge before generic label or handler
        // probes inspect the body as an ordinary value expression.
        if let Some(function) =
            lowerer.lower_root_label_handler_leave(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        // Labels must claim their nonlocal edge before handler-specialization
        // probes inspect the body as an ordinary value expression.
        if let Some(function) = lowerer.lower_root_label_transfer(body.root, parameters.clone()) {
            if lowerer.diagnostics.is_empty() {
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        // A closed callable effect row is an interprocedural summary, not a
        // request to inline or re-derive the callee's body.  Install the
        // caller's lexical frames around the ordinary call so the VM can
        // dispatch a later callee `Perform` through its real call stack.
        if let Some(function) = lowerer
            .lower_root_interprocedural_ordered_one_shot_handler(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) =
            lowerer.lower_root_interprocedural_one_shot_handler(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) = lowerer.lower_root_linear_resumptions(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: lowerer.diagnostics,
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) =
            lowerer.lower_root_finite_replay_safe_resumption(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) =
            lowerer.lower_root_runtime_one_shot_resumption(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) = lowerer
            .lower_root_runtime_grouped_sibling_one_shot_handler(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) = lowerer
            .lower_root_runtime_multiple_sibling_one_shot_handler(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) = lowerer
            .lower_root_runtime_ordered_nested_one_shot_handler(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) =
            lowerer.lower_root_runtime_deep_one_shot_handler(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) =
            lowerer.lower_root_runtime_nested_one_shot_handler(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) = lowerer.lower_root_let_resumption(body.root, parameters.clone()) {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) =
            lowerer.lower_root_statement_one_shot_handler(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) =
            lowerer.lower_root_statement_ordered_one_shot_handler(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) =
            lowerer.lower_root_statement_cancellation_handler(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) =
            lowerer.lower_root_runtime_one_shot_handler(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) =
            lowerer.lower_root_runtime_one_shot_indirect_handler(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) =
            lowerer.lower_root_terminal_pattern_handler(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) = lowerer.lower_root_completion_handler(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) = lowerer.lower_root_short_circuit(body.root, parameters.clone()) {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                    return Self {
                        function: None,
                        lifted: BTreeMap::new(),
                        diagnostics: vec![MirDiagnostic {
                            code: "G6002",
                            message,
                        }],
                    };
                }
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        if let Some(function) = lowerer.lower_root_label_transfer(body.root, parameters.clone()) {
            if lowerer.diagnostics.is_empty() {
                return Self {
                    function: Some(function),
                    lifted: lowerer.lifted,
                    diagnostics: vec![],
                };
            }
            return Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            };
        }
        let root = lowerer.value(body.root);
        if lowerer.diagnostics.is_empty() {
            let Some(root) = root else {
                return Self {
                    function: None,
                    lifted: BTreeMap::new(),
                    diagnostics: vec![MirDiagnostic {
                        code: "G6002",
                        message: "MIR lowering produced no root value".into(),
                    }],
                };
            };
            let function = MirFunction {
                definition,
                captures: 0,
                parameters,
                locals: lowerer.locals,
                result: body.expression(body.root).ty.clone(),
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    parameters: vec![],
                    instructions: lowerer.instructions,
                    terminator: MirTerminator::Return { value: root },
                }],
            };
            if let Err(message) = validate_lowered_handler_contracts(body, &function) {
                return Self {
                    function: None,
                    lifted: BTreeMap::new(),
                    diagnostics: vec![MirDiagnostic {
                        code: "G6002",
                        message,
                    }],
                };
            }
            Self {
                function: Some(function),
                lifted: lowerer.lifted,
                diagnostics: vec![],
            }
        } else {
            Self {
                function: None,
                lifted: BTreeMap::new(),
                diagnostics: lowerer.diagnostics,
            }
        }
    }
}
impl MirFunction {
    pub fn entry_block(&self) -> &MirBlock {
        &self.blocks[self.entry.0 as usize]
    }
    pub fn validate(&self) -> Result<(), String> {
        if self.entry.0 as usize >= self.blocks.len() {
            return Err(format!("MIR entry block {} is absent", self.entry.0));
        }
        validate_mir_type(&self.result, &mut vec![])?;
        for local in &self.locals {
            validate_mir_type(&local.ty, &mut vec![])?;
        }
        for (index, block) in self.blocks.iter().enumerate() {
            for &parameter in &block.parameters {
                self.local_type(parameter)?;
            }
            for instruction in &block.instructions {
                for local in references(instruction) {
                    self.local_type(local)?;
                }
                self.validate_instruction(instruction)?;
                validate_instruction_semantic_types(instruction)?;
            }
            self.validate_terminator(index, &block.terminator)?;
        }
        Ok(())
    }
    fn local_type(&self, local: MirLocal) -> Result<&Type, String> {
        self.locals
            .get(local.0 as usize)
            .map(|local| &local.ty)
            .ok_or_else(|| format!("MIR references invalid local {}", local.0))
    }
    fn validate_instruction(&self, instruction: &MirInstruction) -> Result<(), String> {
        if let MirInstruction::MakeArray {
            dst,
            fields,
            element_type,
        } = instruction
        {
            if self.local_type(*dst)? != &Type::Array(Box::new(element_type.clone())) {
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
            target,
            ..
        } = instruction
        {
            if target.0 as usize >= self.blocks.len() {
                return Err("MIR handler target block is absent".into());
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
                if cleanup
                    .moved_places
                    .windows(2)
                    .any(|pair| pair[0] >= pair[1])
                    || cleanup
                        .active_loans
                        .windows(2)
                        .any(|pair| pair[0] >= pair[1])
                {
                    return Err("MIR leave cleanup plan is not canonical".into());
                }
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
}

/// MIR is still permitted to carry declaration-owned generic parameters until
/// instance materialization, but it must never carry body-local inference,
/// recovery poison, or a higher-ranked lifetime whose binder is absent.  The
/// walk intentionally reaches type and effect arguments embedded in callable,
/// nominal, aggregate, pattern, and handler metadata as well as local types.
fn validate_mir_type(ty: &Type, lifetime_binders: &mut Vec<u32>) -> Result<(), String> {
    match ty {
        Type::Infer(_) => Err("MIR semantic type retains an unresolved inference variable".into()),
        Type::Error => Err("MIR semantic type retains recovered error poison".into()),
        Type::Nominal { arguments, .. } => arguments
            .iter()
            .try_for_each(|argument| validate_mir_generic_argument(argument, lifetime_binders)),
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            validate_mir_type(subject, lifetime_binders)?;
            trait_arguments
                .iter()
                .try_for_each(|argument| validate_mir_type(argument, lifetime_binders))?;
            item_arguments
                .iter()
                .try_for_each(|argument| validate_mir_type(argument, lifetime_binders))
        }
        Type::Tuple(elements) => elements
            .iter()
            .try_for_each(|element| validate_mir_type(element, lifetime_binders)),
        Type::Array(element) => validate_mir_type(element, lifetime_binders),
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
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Generic(_) => Ok(()),
    }
}

fn validate_mir_generic_argument(
    argument: &GenericArgument,
    lifetime_binders: &mut Vec<u32>,
) -> Result<(), String> {
    match argument {
        GenericArgument::Type(ty) => validate_mir_type(ty, lifetime_binders),
        GenericArgument::EffectRow(effects) => validate_mir_effect_row(effects, lifetime_binders),
        GenericArgument::Lifetime(lifetime) => validate_mir_lifetime(*lifetime, lifetime_binders),
        GenericArgument::ConstU32(_)
        | GenericArgument::ConstU32Expr(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. } => Ok(()),
    }
}

fn validate_mir_effect_row(
    effects: &crate::EffectRow,
    lifetime_binders: &mut Vec<u32>,
) -> Result<(), String> {
    if matches!(effects.tail, Some(crate::EffectTail::Infer(_))) {
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
            validate_mir_type(argument, lifetime_binders)?;
        }
        for argument in &projection.item_arguments {
            validate_mir_type(argument, lifetime_binders)?;
        }
    }
    Ok(())
}

fn validate_mir_lifetime(
    lifetime: crate::Lifetime,
    lifetime_binders: &[u32],
) -> Result<(), String> {
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

fn validate_instruction_semantic_types(instruction: &MirInstruction) -> Result<(), String> {
    let mut lifetime_binders = vec![];
    match instruction {
        MirInstruction::MakeArray { element_type, .. } => {
            validate_mir_type(element_type, &mut lifetime_binders)
        }
        MirInstruction::MakeRecord { field_types, .. }
        | MirInstruction::MakeEnum { field_types, .. } => field_types
            .iter()
            .try_for_each(|ty| validate_mir_type(ty, &mut lifetime_binders)),
        MirInstruction::ProjectRecord { field_type, .. }
        | MirInstruction::ProjectTuple { field_type, .. }
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
            Ok(())
        }
        MirInstruction::ConstUnit { .. }
        | MirInstruction::ConstI64 { .. }
        | MirInstruction::ConstF64 { .. }
        | MirInstruction::ConstBool { .. }
        | MirInstruction::ConstChar { .. }
        | MirInstruction::ConstText { .. }
        | MirInstruction::MakeTuple { .. }
        | MirInstruction::UninstallHandler
        | MirInstruction::CaptureResumption { .. }
        | MirInstruction::Resume { .. }
        | MirInstruction::ResumeReturn { .. }
        | MirInstruction::ResumeSnapshot { .. }
        | MirInstruction::Forward
        | MirInstruction::Cancel
        | MirInstruction::Copy { .. }
        | MirInstruction::Store { .. }
        | MirInstruction::Move { .. }
        | MirInstruction::Borrow { .. }
        | MirInstruction::DerefCopy { .. }
        | MirInstruction::DerefStore { .. }
        | MirInstruction::NotBool { .. }
        | MirInstruction::AddI64 { .. }
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
        | MirInstruction::CallIndirect { .. } => Ok(()),
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
        MirPattern::Record { fields, .. } | MirPattern::Enum { fields, .. } => {
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
fn validate_lowered_handler_contracts(
    body: &TypedBody,
    function: &MirFunction,
) -> Result<(), String> {
    function.validate()?;

    let clauses = body
        .expressions
        .iter()
        .flat_map(|expression| match &expression.kind {
            CoreKind::Handle { clauses, .. } => clauses.iter().collect::<Vec<_>>(),
            _ => Vec::new(),
        })
        .collect::<Vec<_>>();
    let installs = function
        .blocks
        .iter()
        .flat_map(|block| block.instructions.iter())
        .filter_map(|instruction| match instruction {
            MirInstruction::InstallHandler {
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                resume_type,
                target,
                ..
            } => Some((
                effect,
                effect_arguments,
                operation,
                payload_destinations,
                resume_type,
                target,
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    if installs.is_empty() {
        return Ok(());
    }
    if clauses.is_empty() {
        return Err("MIR installs a handler without a frozen Typed Core handler contract".into());
    }

    let uninstall_count = function
        .blocks
        .iter()
        .flat_map(|block| block.instructions.iter())
        .filter(|instruction| matches!(instruction, MirInstruction::UninstallHandler))
        .count();
    if uninstall_count < installs.len() {
        return Err(format!(
            "MIR installs {} handler frame(s) but provides only {uninstall_count} normal cleanup(s)",
            installs.len()
        ));
    }

    for (effect, arguments, operation, payload_destinations, resume_type, target) in installs {
        // Probe each source arm with independent substitutions: a refutable
        // earlier arm must not leak a partial generic match into the selected
        // arm's frozen contract.
        let Some((clause, mut substitutions)) = clauses.iter().copied().find_map(|clause| {
            let mut substitutions = BTreeMap::new();
            let matches = clause.effect.definition == *effect
                && clause.effect.arguments.len() == arguments.len()
                && clause
                    .effect
                    .arguments
                    .iter()
                    .zip(arguments)
                    .all(|(expected, actual)| {
                        generic_argument_contract_matches(expected, actual, &mut substitutions)
                    })
                && clause.operation == *operation
                && clause.payload_types.len() == payload_destinations.len()
                && clause.payload_types.iter().zip(payload_destinations).all(
                    |(expected, local)| {
                        function.local_type(*local).is_ok_and(|actual| {
                            type_contract_matches(expected, actual, &mut substitutions)
                        })
                    },
                );
            matches.then_some((clause, substitutions))
        }) else {
            return Err(
                "MIR handler frame has no matching frozen effect operation contract".into(),
            );
        };

        if clause.terminal {
            if clause.continuation.is_some()
                || !matches!(clause.resumption, CoreHandlerResumption::Terminal)
            {
                return Err("terminal handler frame retained a continuation contract".into());
            }
            continue;
        }
        let Some(contract) = clause.continuation.as_ref() else {
            return Err("nonterminal handler frame lost its frozen continuation contract".into());
        };
        let declared_quantity = match &clause.resumption {
            CoreHandlerResumption::Tail { quantity }
            | CoreHandlerResumption::Explicit { quantity, .. }
            | CoreHandlerResumption::Discard { quantity } => *quantity,
            CoreHandlerResumption::Terminal => unreachable!("terminal arms returned above"),
        };
        if contract.invocation != declared_quantity {
            return Err(
                "MIR handler resumption quantity disagrees with its frozen continuation contract"
                    .into(),
            );
        }
        // `InstallHandler::resume_type` is the value injected back into the
        // suspended `Perform`, not the outer handler result returned by the
        // continuation call.  The former is the frozen continuation
        // parameter; confusing the two would reject handlers that transform
        // an operation result before returning their final result.
        if !type_contract_matches(&contract.parameter, resume_type, &mut substitutions) {
            return Err(
                "MIR handler resume type disagrees with the frozen continuation parameter".into(),
            );
        }

        let exits = handler_region_exits(function, *target);
        match &clause.resumption {
            CoreHandlerResumption::Discard { .. } => {
                if declared_quantity.requires_positive_use() || !exits.cancel {
                    return Err(
                        "MIR cancellation does not implement the frozen discarded-continuation contract"
                            .into(),
                    );
                }
            }
            CoreHandlerResumption::Tail { .. } | CoreHandlerResumption::Explicit { .. } => {
                let replay_return =
                    exits.resume_return && declared_quantity.upper.is_some_and(|upper| upper >= 2);
                if (!declared_quantity.contains(crate::quantity::Quantity::ONCE) && !replay_return)
                    || (!exits.resume && !exits.forward && !replay_return)
                {
                    return Err(
                        "MIR handler exit does not implement the frozen resumption contract".into(),
                    );
                }
                if exits.cancel && !replay_return {
                    return Err(
                        "MIR cancellation is not permitted for a resumptive handler contract"
                            .into(),
                    );
                }
            }
            CoreHandlerResumption::Terminal => {
                return Err("nonterminal handler frame was lowered as terminal".into());
            }
        }
    }
    Ok(())
}

/// Frozen declarations can retain an operation-generic slot while the body
/// has already inferred its concrete argument.  Treat those slots as
/// unification variables *only inside this immutable contract match*, keeping
/// repeated occurrences equal without allowing MIR to conflate distinct
/// protocol instances.
fn type_contract_matches(
    expected: &Type,
    actual: &Type,
    substitutions: &mut BTreeMap<u32, Type>,
) -> bool {
    match expected {
        Type::Generic(index) => match substitutions.get(index) {
            Some(previous) => previous == actual,
            None => {
                substitutions.insert(*index, actual.clone());
                true
            }
        },
        Type::Nominal {
            definition,
            arguments,
        } => {
            matches!(actual, Type::Nominal { definition: actual_definition, arguments: actual_arguments }
            if definition == actual_definition
                && arguments.len() == actual_arguments.len()
                && arguments.iter().zip(actual_arguments).all(|(expected, actual)| {
                    generic_contract_matches(expected, actual, substitutions)
                }))
        }
        Type::Tuple(values) => matches!(actual, Type::Tuple(actual_values)
        if values.len() == actual_values.len()
            && values.iter().zip(actual_values).all(|(expected, actual)| {
                type_contract_matches(expected, actual, substitutions)
            })),
        Type::Array(value) => matches!(actual, Type::Array(actual_value)
            if type_contract_matches(value, actual_value, substitutions)),
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => matches!(actual, Type::Reference {
            mutability: actual_mutability,
            lifetime: actual_lifetime,
            referent: actual_referent,
        } if mutability == actual_mutability
            && lifetime == actual_lifetime
            && type_contract_matches(referent, actual_referent, substitutions)),
        // A frozen Core contract must not retain body inference variables, but
        // recovery products do.  They never constrain a valid MIR frame.
        Type::Infer(_) | Type::Error => true,
        _ => expected == actual,
    }
}

fn generic_argument_contract_matches(
    expected: &crate::GenericArgument,
    actual: &crate::GenericArgument,
    substitutions: &mut BTreeMap<u32, Type>,
) -> bool {
    match (expected, actual) {
        (crate::GenericArgument::Type(expected), crate::GenericArgument::Type(actual)) => {
            type_contract_matches(expected, actual, substitutions)
        }
        _ => expected == actual,
    }
}

#[derive(Default)]
struct HandlerRegionExits {
    resume: bool,
    resume_return: bool,
    forward: bool,
    cancel: bool,
}

/// The normal CFG does not encode `Perform`'s dynamic jump to a handler
/// target, but it does encode every structural decision within that target.
/// Follow those edges to discover the cleanup transfer selected by each arm.
fn handler_region_exits(function: &MirFunction, start: MirBlockId) -> HandlerRegionExits {
    let mut pending = vec![start];
    let mut visited = BTreeSet::new();
    let mut exits = HandlerRegionExits::default();
    while let Some(block) = pending.pop() {
        if !visited.insert(block) {
            continue;
        }
        let Some(block) = function.blocks.get(block.0 as usize) else {
            continue;
        };
        for instruction in &block.instructions {
            match instruction {
                MirInstruction::Resume { .. } | MirInstruction::ResumeSnapshot { .. } => {
                    exits.resume = true
                }
                MirInstruction::ResumeReturn { .. } => exits.resume_return = true,
                MirInstruction::Forward => exits.forward = true,
                MirInstruction::Cancel => exits.cancel = true,
                _ => {}
            }
        }
        match block.terminator {
            MirTerminator::Goto { target, .. } | MirTerminator::Leave { target, .. } => {
                pending.push(target)
            }
            MirTerminator::SwitchBool {
                then_target,
                else_target,
                ..
            } => {
                pending.push(then_target);
                pending.push(else_target);
            }
            MirTerminator::Return { .. } | MirTerminator::Unreachable => {}
        }
    }
    exits
}
impl MirProgram {
    pub fn validate(&self) -> Result<(), String> {
        if !self.functions.contains_key(&self.entry) {
            return Err("MIR program entry is absent".into());
        }
        for (executable, instance) in &self.instances {
            if executable != &instance.executable || !self.functions.contains_key(executable) {
                return Err("MIR instance product has no matching executable body".into());
            }
        }
        for function in self.functions.values() {
            function.validate()?;
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
                    if let MirInstruction::Call { callee, .. }
                    | MirInstruction::MakeCallable { callee, .. } = instruction
                        && !self.functions.contains_key(callee)
                    {
                        return Err(format!("MIR call targets missing function {callee:?}"));
                    }
                }
            }
        }
        Ok(())
    }
}
fn references(value: &MirInstruction) -> Vec<MirLocal> {
    match value {
        MirInstruction::ConstUnit { dst }
        | MirInstruction::ConstI64 { dst, .. }
        | MirInstruction::ConstF64 { dst, .. }
        | MirInstruction::ConstBool { dst, .. }
        | MirInstruction::ConstChar { dst, .. }
        | MirInstruction::ConstText { dst, .. } => vec![*dst],
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
        | MirInstruction::ProjectTuple { dst, base, .. } => vec![*dst, *base],
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
        MirInstruction::UninstallHandler => Vec::new(),
        MirInstruction::CaptureResumption { dst } => vec![*dst],
        MirInstruction::Resume { value } => vec![*value],
        MirInstruction::ResumeReturn { dst, value } => vec![*dst, *value],
        MirInstruction::ResumeSnapshot { snapshot, value } => vec![*snapshot, *value],
        MirInstruction::Forward => Vec::new(),
        MirInstruction::Cancel => Vec::new(),
        MirInstruction::Copy { dst, src }
        | MirInstruction::Store { dst, src }
        | MirInstruction::Move { dst, src } => vec![*dst, *src],
        MirInstruction::Borrow { dst, src, .. } => vec![*dst, *src],
        MirInstruction::DerefCopy { dst, reference } => vec![*dst, *reference],
        MirInstruction::DerefStore { reference, src } => vec![*reference, *src],
        MirInstruction::NotBool { dst, value } => vec![*dst, *value],
        MirInstruction::AddI64 { dst, left, right }
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
        MirInstruction::Call { dst, arguments, .. } => std::iter::once(*dst)
            .chain(arguments.iter().copied())
            .collect(),
        MirInstruction::MakeCallable { dst, captures, .. } => std::iter::once(*dst)
            .chain(captures.iter().copied())
            .collect(),
        MirInstruction::CallIndirect {
            dst,
            callee,
            arguments,
        } => std::iter::once(*dst)
            .chain(std::iter::once(*callee))
            .chain(arguments.iter().copied())
            .collect(),
    }
}
struct Lowerer<'a> {
    body: &'a TypedBody,
    bodies: &'a BTreeMap<DefKey, TypedBody>,
    definition: DefKey,
    locals: Vec<MirLocalDecl>,
    values: BTreeMap<CoreId, MirLocal>,
    named: BTreeMap<String, MirLocal>,
    lifted: BTreeMap<DefKey, MirFunction>,
    instructions: Vec<MirInstruction>,
    diagnostics: Vec<MirDiagnostic>,
    /// Ownership facts that survive to a nonlocal body exit. Stage 0 values
    /// need no runtime drop glue yet, but keeping this plan on `Leave` makes
    /// the erasure explicit and lets the validator reject noncanonical plans.
    leave_cleanup: MirCleanupPlan,
    /// First-class snapshots materialized in the current handler clause.
    /// Multiple aliases of the same Core identity must share this register so
    /// a stale copy cannot silently target a different frame.
    resumption_snapshots: BTreeMap<ResumptionId, MirLocal>,
    /// A label expression whose transfer has been split into a `Leave` edge
    /// and a typed rejoin block.  Re-lowering the surrounding Core
    /// continuation reads this local instead of replaying the lexical label
    /// body (and, critically, instead of encountering its `Transfer` again).
    label_rejoins: BTreeMap<CoreId, MirLocal>,
    /// Active only while lowering a statically specialized handler clause.
    /// The plan makes the captured continuation explicit even when its
    /// representation can be eliminated: either the root identity or a
    /// replay-safe residual computation cloned once per finite resumption.
    direct_resumption: Option<DirectResumptionState>,
}

#[derive(Clone, Debug)]
struct DirectResumptionState {
    name: String,
    quantity: crate::quantity::Quantity,
    calls: u64,
    plan: DirectResumptionPlan,
}

#[derive(Clone, Debug)]
enum DirectResumptionPlan {
    Identity,
    /// A real VM replay frame. Each source call transfers into a fresh
    /// continuation snapshot and returns its result to the clause callsite.
    RuntimeReplay,
    PureResidual {
        binding: String,
        prefix: Vec<CoreId>,
        result: CoreId,
    },
}

/// One runtime dispatch matrix for one operation key in a nested handler.
/// Frames select their operation before entering this matrix, so source-order
/// structural fallthrough is independent for every sibling key.
type HandlerPatternTest = (MirLocal, MirLocal, MirPattern);
type HandlerDispatchClause<'a> = (&'a CoreHandlerClause, Vec<HandlerPatternTest>);

struct SiblingHandlerDispatch<'a> {
    clauses: Vec<HandlerDispatchClause<'a>>,
    payload_destinations: Vec<MirLocal>,
    test_blocks: Vec<Vec<MirBlockId>>,
    body_blocks: Vec<MirBlockId>,
    forward_block: Option<MirBlockId>,
}

/// The selected result of a normal-completion clause in the constrained
/// direct-handler lowering.  A matching clause either exits the enclosing
/// lexical label or produces the ordinary handler result; the chain itself
/// owns the ordered pattern-dispatch edges.
enum CompletionChainArm {
    Leave {
        instructions: Vec<MirInstruction>,
        value: MirLocal,
    },
    Return {
        instructions: Vec<MirInstruction>,
        value: MirLocal,
    },
}

impl Lowerer<'_> {
    /// Lower an ordered, direct normal-completion chain under an enclosing
    /// label.  Every refutable clause receives the protected computation's
    /// result on an explicit block edge; a failed test carries that exact
    /// subject forward to the next clause.  This remains intentionally narrow
    /// (direct one-shot handler and a final irrefutable fallback) so multi-shot
    /// continuations and closure-captured control cannot acquire a synthetic
    /// CFG path here.  The final arm may itself take the enclosing label
    /// after every preceding refutable test has failed.
    fn lower_root_label_completion_chain(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (label, root_prefix) = match self.body.expression(root).kind.clone() {
            CoreKind::Label { .. } => (root, Vec::new()),
            CoreKind::Block(values) => {
                let (last, prefix) = values.split_last()?;
                matches!(self.body.expression(*last).kind, CoreKind::Label { .. })
                    .then_some((*last, prefix.to_vec()))?
            }
            _ => return None,
        };
        let CoreKind::Label { brand, body } = self.body.expression(label).kind.clone() else {
            return None;
        };
        let completion = match self.body.expression(body).kind.clone() {
            CoreKind::Completion { .. } => body,
            CoreKind::Block(values) => *values.last()?,
            _ => return None,
        };
        let CoreKind::Completion {
            computation,
            clauses: completion_clauses,
        } = self.body.expression(completion).kind.clone()
        else {
            return None;
        };
        let (fallback_clause, refutable_clauses) = completion_clauses.split_last()?;
        if refutable_clauses.is_empty()
            || !pattern_is_irrefutable(&fallback_clause.pattern)
            || !refutable_clauses
                .iter()
                .all(|clause| !pattern_is_irrefutable(&clause.pattern))
            || !(self.contains_label_transfer(fallback_clause.body, brand)
                || refutable_clauses
                    .iter()
                    .any(|clause| self.contains_label_transfer(clause.body, brand)))
        {
            return None;
        }
        let CoreKind::Handle {
            computation: protected,
            clauses: operation_clauses,
        } = self.body.expression(computation).kind.clone()
        else {
            return None;
        };
        let CoreKind::Perform {
            effect,
            operation,
            arguments: argument_ids,
            terminal: false,
        } = self.body.expression(protected).kind.clone()
        else {
            return None;
        };
        let matching = operation_clauses
            .iter()
            .filter(|clause| clause.effect == effect && clause.operation == operation)
            .collect::<Vec<_>>();
        let [operation_clause] = matching.as_slice() else {
            return None;
        };
        let quantity = match operation_clause.resumption {
            CoreHandlerResumption::Tail { quantity }
            | CoreHandlerResumption::Explicit { quantity, .. } => quantity,
            CoreHandlerResumption::Discard { .. } | CoreHandlerResumption::Terminal => return None,
        };
        if quantity != crate::quantity::Quantity::ONCE
            || operation_clause.terminal
            || operation_clause.patterns.len() != argument_ids.len()
            || !operation_clause.patterns.iter().all(pattern_is_irrefutable)
        {
            return None;
        }
        for value in root_prefix {
            self.statement(value)?;
        }
        let payloads = operation_clause
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), protected))
            .collect::<Vec<_>>();
        let performed = self.alloc(self.body.expression(protected).ty.clone(), protected);
        let arguments = argument_ids
            .iter()
            .map(|id| self.value(*id))
            .collect::<Option<Vec<_>>>()?;
        let completion_count = refutable_clauses.len();
        let test_start = 1_u32;
        let arm_start = test_start + completion_count as u32;
        let fallback_block = arm_start + completion_count as u32;
        let handler_block = fallback_block + 1;
        let join_block = handler_block + 1;
        let mut entry = std::mem::take(&mut self.instructions);
        entry.push(MirInstruction::InstallHandler {
            effect: effect.definition,
            effect_arguments: effect.arguments.clone(),
            operation,
            payload_destinations: payloads.clone(),
            resume_type: self.body.expression(protected).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target: MirBlockId(handler_block),
        });
        entry.push(MirInstruction::Perform {
            dst: performed,
            effect: effect.definition,
            effect_arguments: effect.arguments,
            operation,
            arguments,
        });
        entry.push(MirInstruction::UninstallHandler);

        let completion_subjects = (0..completion_count)
            .map(|_| self.alloc(self.body.expression(protected).ty.clone(), CoreId(u32::MAX)))
            .collect::<Vec<_>>();
        let conditions = (0..completion_count)
            .map(|_| self.alloc(Type::Scalar(crate::types::ScalarType::Bool), root))
            .collect::<Vec<_>>();
        let join = self.alloc(self.body.expression(root).ty.clone(), CoreId(u32::MAX));
        let boundary_named = self.named.clone();
        let boundary_values = self.values.clone();
        let mut arms = Vec::with_capacity(completion_count);
        for (clause, subject) in refutable_clauses.iter().zip(&completion_subjects) {
            self.instructions = Vec::new();
            self.named = boundary_named.clone();
            self.values = boundary_values.clone();
            self.bind_completion_clause(clause, *subject)?;
            let instructions;
            let value;
            if self.contains_label_transfer(clause.body, brand) {
                value = self.lower_label_transfer_path(clause.body, brand)?;
                instructions = std::mem::take(&mut self.instructions);
                arms.push(CompletionChainArm::Leave {
                    instructions,
                    value,
                });
            } else {
                value = self.value(clause.body)?;
                instructions = std::mem::take(&mut self.instructions);
                arms.push(CompletionChainArm::Return {
                    instructions,
                    value,
                });
            }
        }
        self.instructions = Vec::new();
        self.named = boundary_named.clone();
        self.values = boundary_values.clone();
        self.bind_completion_clause(fallback_clause, completion_subjects[completion_count - 1])?;
        let fallback = if self.contains_label_transfer(fallback_clause.body, brand) {
            let value = self.lower_label_transfer_path(fallback_clause.body, brand)?;
            CompletionChainArm::Leave {
                instructions: std::mem::take(&mut self.instructions),
                value,
            }
        } else {
            let value = self.value(fallback_clause.body)?;
            CompletionChainArm::Return {
                instructions: std::mem::take(&mut self.instructions),
                value,
            }
        };

        self.instructions = Vec::new();
        self.named = boundary_named;
        self.values = boundary_values;
        self.bind_handler_patterns(&operation_clause.patterns, &payloads)?;
        let resumed = self.direct_handler_clause_value(operation_clause)?;
        self.instructions
            .push(MirInstruction::Resume { value: resumed });
        let handler_instructions = std::mem::take(&mut self.instructions);

        let mut blocks = Vec::with_capacity(2 * completion_count + 3);
        blocks.push(MirBlock {
            parameters: vec![],
            instructions: entry,
            terminator: MirTerminator::Goto {
                target: MirBlockId(test_start),
                arguments: vec![performed],
            },
        });
        for index in 0..completion_count {
            let is_last = index + 1 == completion_count;
            let pattern = lower_pattern(refutable_clauses[index].pattern.clone())?;
            blocks.push(MirBlock {
                parameters: vec![completion_subjects[index]],
                instructions: vec![MirInstruction::PatternTest {
                    dst: conditions[index],
                    subject: completion_subjects[index],
                    pattern,
                }],
                terminator: MirTerminator::SwitchBool {
                    condition: conditions[index],
                    then_target: MirBlockId(arm_start + index as u32),
                    then_arguments: vec![],
                    else_target: if is_last {
                        MirBlockId(fallback_block)
                    } else {
                        MirBlockId(test_start + index as u32 + 1)
                    },
                    else_arguments: if is_last {
                        vec![]
                    } else {
                        vec![completion_subjects[index]]
                    },
                },
            });
        }
        for arm in arms {
            let (instructions, terminator) = match arm {
                CompletionChainArm::Leave {
                    instructions,
                    value,
                } => (
                    instructions,
                    MirTerminator::Leave {
                        brand,
                        target: MirBlockId(join_block),
                        arguments: vec![value],
                        cleanup: MirCleanupPlan {
                            moved_places: self.leave_cleanup.moved_places.clone(),
                            active_loans: self.leave_cleanup.active_loans.clone(),
                        },
                    },
                ),
                CompletionChainArm::Return {
                    instructions,
                    value,
                } => (instructions, MirTerminator::Return { value }),
            };
            blocks.push(MirBlock {
                parameters: vec![],
                instructions,
                terminator,
            });
        }
        let (instructions, terminator) = match fallback {
            CompletionChainArm::Leave {
                instructions,
                value,
            } => (
                instructions,
                MirTerminator::Leave {
                    brand,
                    target: MirBlockId(join_block),
                    arguments: vec![value],
                    cleanup: MirCleanupPlan {
                        moved_places: self.leave_cleanup.moved_places.clone(),
                        active_loans: self.leave_cleanup.active_loans.clone(),
                    },
                },
            ),
            CompletionChainArm::Return {
                instructions,
                value,
            } => (instructions, MirTerminator::Return { value }),
        };
        blocks.push(MirBlock {
            parameters: vec![],
            instructions,
            terminator,
        });
        blocks.push(MirBlock {
            parameters: vec![],
            instructions: handler_instructions,
            terminator: MirTerminator::Unreachable,
        });
        blocks.push(MirBlock {
            parameters: vec![join],
            instructions: vec![],
            terminator: MirTerminator::Return { value: join },
        });
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }

    /// Lower one direct normal-completion arm that leaves an enclosing label.
    /// The operation frame is resumed on its own block; the restored protected
    /// path executes `UninstallHandler` before entering the completion block,
    /// so the completion `Leave` carries only the lexical cleanup proof and
    /// cannot retain a stale continuation capability.
    fn lower_root_label_completion_leave(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (label, root_prefix) = match self.body.expression(root).kind.clone() {
            CoreKind::Label { .. } => (root, Vec::new()),
            CoreKind::Block(values) => {
                let (last, prefix) = values.split_last()?;
                matches!(self.body.expression(*last).kind, CoreKind::Label { .. })
                    .then_some((*last, prefix.to_vec()))?
            }
            _ => return None,
        };
        let CoreKind::Label { brand, body } = self.body.expression(label).kind.clone() else {
            return None;
        };
        let completion = match self.body.expression(body).kind.clone() {
            CoreKind::Completion { .. } => body,
            CoreKind::Block(values) => *values.last()?,
            _ => return None,
        };
        let CoreKind::Completion {
            computation,
            clauses: completion_clauses,
        } = self.body.expression(completion).kind.clone()
        else {
            return None;
        };
        let (completion_clause, fallback_clause) = match completion_clauses.as_slice() {
            [clause]
                if pattern_is_irrefutable(&clause.pattern)
                    && self.contains_label_transfer(clause.body, brand) =>
            {
                (clause, None)
            }
            [clause, fallback]
                if !pattern_is_irrefutable(&clause.pattern)
                    && pattern_is_irrefutable(&fallback.pattern)
                    && self.contains_label_transfer(clause.body, brand)
                    && !self.contains_label_transfer(fallback.body, brand) =>
            {
                (clause, Some(fallback))
            }
            _ => return None,
        };
        let CoreKind::Handle {
            computation: protected,
            clauses: operation_clauses,
        } = self.body.expression(computation).kind.clone()
        else {
            return None;
        };
        let CoreKind::Perform {
            effect,
            operation,
            arguments: argument_ids,
            terminal: false,
        } = self.body.expression(protected).kind.clone()
        else {
            return None;
        };
        let matching = operation_clauses
            .iter()
            .filter(|clause| clause.effect == effect && clause.operation == operation)
            .collect::<Vec<_>>();
        let [operation_clause] = matching.as_slice() else {
            return None;
        };
        let quantity = match operation_clause.resumption {
            CoreHandlerResumption::Tail { quantity }
            | CoreHandlerResumption::Explicit { quantity, .. } => quantity,
            CoreHandlerResumption::Discard { .. } | CoreHandlerResumption::Terminal => return None,
        };
        if quantity != crate::quantity::Quantity::ONCE
            || operation_clause.terminal
            || operation_clause.patterns.len() != argument_ids.len()
            || !operation_clause.patterns.iter().all(pattern_is_irrefutable)
        {
            return None;
        }
        for value in root_prefix {
            self.statement(value)?;
        }
        let payloads = operation_clause
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), protected))
            .collect::<Vec<_>>();
        let performed = self.alloc(self.body.expression(protected).ty.clone(), protected);
        let arguments = argument_ids
            .iter()
            .map(|id| self.value(*id))
            .collect::<Option<Vec<_>>>()?;
        let mut entry = std::mem::take(&mut self.instructions);
        let handler_target = if fallback_clause.is_some() { 4 } else { 2 };
        entry.push(MirInstruction::InstallHandler {
            effect: effect.definition,
            effect_arguments: effect.arguments.clone(),
            operation,
            payload_destinations: payloads.clone(),
            resume_type: self.body.expression(protected).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target: MirBlockId(handler_target),
        });
        entry.push(MirInstruction::Perform {
            dst: performed,
            effect: effect.definition,
            effect_arguments: effect.arguments,
            operation,
            arguments,
        });
        entry.push(MirInstruction::UninstallHandler);

        let completion_subject =
            self.alloc(self.body.expression(protected).ty.clone(), CoreId(u32::MAX));
        let join = self.alloc(self.body.expression(root).ty.clone(), CoreId(u32::MAX));
        let boundary_named = self.named.clone();
        let boundary_values = self.values.clone();
        self.instructions = Vec::new();
        self.named = boundary_named.clone();
        self.values = boundary_values.clone();
        self.bind_handler_patterns(
            std::slice::from_ref(&completion_clause.pattern),
            &[completion_subject],
        )?;
        let completed = self.lower_label_transfer_path(completion_clause.body, brand)?;
        let completion_instructions = std::mem::take(&mut self.instructions);

        let fallback = if let Some(fallback_clause) = fallback_clause {
            self.instructions = Vec::new();
            self.named = boundary_named.clone();
            self.values = boundary_values.clone();
            self.bind_completion_clause(fallback_clause, completion_subject)?;
            let value = self.value(fallback_clause.body)?;
            let instructions = std::mem::take(&mut self.instructions);
            let pattern = lower_pattern(completion_clause.pattern.clone())?;
            let condition = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), root);
            Some((condition, pattern, instructions, value))
        } else {
            None
        };

        self.instructions = Vec::new();
        self.named = boundary_named;
        self.values = boundary_values;
        self.bind_handler_patterns(&operation_clause.patterns, &payloads)?;
        let resumed = self.direct_handler_clause_value(operation_clause)?;
        self.instructions
            .push(MirInstruction::Resume { value: resumed });
        let handler_instructions = std::mem::take(&mut self.instructions);
        let blocks =
            if let Some((condition, pattern, fallback_instructions, fallback_value)) = fallback {
                vec![
                    MirBlock {
                        parameters: vec![],
                        instructions: entry,
                        terminator: MirTerminator::Goto {
                            target: MirBlockId(1),
                            arguments: vec![performed],
                        },
                    },
                    MirBlock {
                        parameters: vec![completion_subject],
                        instructions: vec![MirInstruction::PatternTest {
                            dst: condition,
                            subject: completion_subject,
                            pattern,
                        }],
                        terminator: MirTerminator::SwitchBool {
                            condition,
                            then_target: MirBlockId(2),
                            then_arguments: vec![],
                            else_target: MirBlockId(3),
                            else_arguments: vec![],
                        },
                    },
                    MirBlock {
                        parameters: vec![],
                        instructions: completion_instructions,
                        terminator: MirTerminator::Leave {
                            brand,
                            target: MirBlockId(5),
                            arguments: vec![completed],
                            cleanup: MirCleanupPlan {
                                moved_places: self.leave_cleanup.moved_places.clone(),
                                active_loans: self.leave_cleanup.active_loans.clone(),
                            },
                        },
                    },
                    MirBlock {
                        parameters: vec![],
                        instructions: fallback_instructions,
                        terminator: MirTerminator::Return {
                            value: fallback_value,
                        },
                    },
                    MirBlock {
                        parameters: vec![],
                        instructions: handler_instructions,
                        terminator: MirTerminator::Unreachable,
                    },
                    MirBlock {
                        parameters: vec![join],
                        instructions: vec![],
                        terminator: MirTerminator::Return { value: join },
                    },
                ]
            } else {
                vec![
                    MirBlock {
                        parameters: vec![],
                        instructions: entry,
                        terminator: MirTerminator::Goto {
                            target: MirBlockId(1),
                            arguments: vec![performed],
                        },
                    },
                    MirBlock {
                        parameters: vec![completion_subject],
                        instructions: completion_instructions,
                        terminator: MirTerminator::Leave {
                            brand,
                            target: MirBlockId(3),
                            arguments: vec![completed],
                            cleanup: MirCleanupPlan {
                                moved_places: self.leave_cleanup.moved_places.clone(),
                                active_loans: self.leave_cleanup.active_loans.clone(),
                            },
                        },
                    },
                    MirBlock {
                        parameters: vec![],
                        instructions: handler_instructions,
                        terminator: MirTerminator::Unreachable,
                    },
                    MirBlock {
                        parameters: vec![join],
                        instructions: vec![],
                        terminator: MirTerminator::Return { value: join },
                    },
                ]
            };
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }
    /// Lower the first frame-aware label boundary: one directly selected,
    /// irrefutable operation clause may leave an enclosing lexical label.
    /// The protected computation retains its ordinary uninstall path, while
    /// the clause has a real `Leave` terminator.  The VM therefore abandons
    /// the suspended one-shot continuation and all frame capabilities before
    /// entering the branded label join; it is not an emitter-only jump.
    fn lower_root_label_handler_leave(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (label, prefix) = match self.body.expression(root).kind.clone() {
            CoreKind::Label { .. } => (root, Vec::new()),
            CoreKind::Block(values) => {
                let (last, prefix) = values.split_last()?;
                matches!(self.body.expression(*last).kind, CoreKind::Label { .. })
                    .then_some((*last, prefix.to_vec()))?
            }
            _ => return None,
        };
        let CoreKind::Label { brand, body } = self.body.expression(label).kind.clone() else {
            return None;
        };
        let (computation, clauses, label_prefix) = match self.body.expression(body).kind.clone() {
            CoreKind::Handle {
                computation,
                clauses,
            } => (computation, clauses, Vec::new()),
            CoreKind::Block(values) => {
                let (last, prefix) = values.split_last()?;
                let CoreKind::Handle {
                    computation,
                    clauses,
                } = self.body.expression(*last).kind.clone()
                else {
                    return None;
                };
                (computation, clauses, prefix.to_vec())
            }
            _ => return None,
        };
        let CoreKind::Perform {
            effect,
            operation,
            arguments: argument_ids,
            terminal: false,
        } = self.body.expression(computation).kind.clone()
        else {
            return None;
        };
        let matching = clauses
            .iter()
            .filter(|clause| clause.effect == effect && clause.operation == operation)
            .collect::<Vec<_>>();
        let [clause] = matching.as_slice() else {
            return None;
        };
        if clause.terminal
            || clause.patterns.len() != argument_ids.len()
            || !clause.patterns.iter().all(pattern_is_irrefutable)
            || !self.contains_label_transfer(clause.body, brand)
        {
            return None;
        }
        for value in prefix {
            self.statement(value)?;
        }
        for value in label_prefix {
            self.statement(value)?;
        }
        let payloads = clause
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), computation))
            .collect::<Vec<_>>();
        let performed = self.alloc(self.body.expression(computation).ty.clone(), computation);
        let arguments = argument_ids
            .iter()
            .map(|id| self.value(*id))
            .collect::<Option<Vec<_>>>()?;
        let mut entry = std::mem::take(&mut self.instructions);
        entry.push(MirInstruction::InstallHandler {
            effect: effect.definition,
            effect_arguments: effect.arguments.clone(),
            operation,
            payload_destinations: payloads.clone(),
            resume_type: self.body.expression(computation).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target: MirBlockId(2),
        });
        entry.push(MirInstruction::Perform {
            dst: performed,
            effect: effect.definition,
            effect_arguments: effect.arguments,
            operation,
            arguments,
        });
        entry.push(MirInstruction::UninstallHandler);

        let join = self.alloc(self.body.expression(root).ty.clone(), CoreId(u32::MAX));
        let boundary_named = self.named.clone();
        let boundary_values = self.values.clone();
        self.instructions = Vec::new();
        self.named = boundary_named;
        self.values = boundary_values;
        self.bind_handler_patterns(&clause.patterns, &payloads)?;
        let transferred = self.lower_label_transfer_path(clause.body, brand)?;
        let clause_instructions = std::mem::take(&mut self.instructions);
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks: vec![
                MirBlock {
                    parameters: vec![],
                    instructions: entry,
                    terminator: MirTerminator::Goto {
                        target: MirBlockId(1),
                        arguments: vec![performed],
                    },
                },
                MirBlock {
                    parameters: vec![join],
                    instructions: vec![],
                    terminator: MirTerminator::Return { value: join },
                },
                MirBlock {
                    parameters: vec![],
                    instructions: clause_instructions,
                    terminator: MirTerminator::Leave {
                        brand,
                        target: MirBlockId(1),
                        arguments: vec![transferred],
                        cleanup: MirCleanupPlan {
                            moved_places: self.leave_cleanup.moved_places.clone(),
                            active_loans: self.leave_cleanup.active_loans.clone(),
                        },
                    },
                },
            ],
        })
    }
    /// Lower a lexical label transfer into its own checked CFG edge.  This is
    /// deliberately a source/Core operation rather than an emitter shortcut:
    /// the target block receives the transferred value as a typed parameter
    /// and then runs the lexical continuation after the label.  Consequently
    /// `let value = label done { transfer done 40 }; value + 2` preserves both
    /// the label result and the code that follows the label expression.
    fn lower_root_label_transfer(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let direct_site = match self.body.expression(root).kind.clone() {
            CoreKind::Label { brand, body } if self.contains_label_transfer(body, brand) => {
                Some((root, None, Vec::new(), Vec::new()))
            }
            CoreKind::Block(values) => values
                .iter()
                .enumerate()
                .find_map(|(index, id)| match self.body.expression(*id).kind.clone() {
                    CoreKind::Label { brand, body }
                        if self.contains_label_transfer(body, brand) =>
                    {
                        Some((index, *id, None))
                    }
                    CoreKind::Let { name, value }
                        if matches!(self.body.expression(value).kind, CoreKind::Label { .. }) =>
                    {
                        let CoreKind::Label { brand, body } =
                            self.body.expression(value).kind.clone()
                        else {
                            unreachable!("matched label value")
                        };
                        self.contains_label_transfer(body, brand).then_some((
                            index,
                            value,
                            Some((name, *id)),
                        ))
                    }
                    _ => None,
                })
                .map(|(index, label, binding)| {
                    (
                        label,
                        binding,
                        values[..index].to_vec(),
                        values[index + 1..].to_vec(),
                    )
                }),
            _ => None,
        };
        let (label, binding, prefix, suffix, replay_root_continuation) = match direct_site {
            Some((label, binding, prefix, suffix)) => (label, binding, prefix, suffix, false),
            None => (
                self.find_transfer_label(root)?,
                None,
                Vec::new(),
                Vec::new(),
                true,
            ),
        };
        let CoreKind::Label { brand, body } = self.body.expression(label).kind.clone() else {
            return None;
        };
        for value in prefix {
            self.statement(value)?;
        }
        if replay_root_continuation && !self.prepare_label_path(root, label) {
            return None;
        }
        let value = self.lower_label_transfer_path(body, brand)?;
        let label_result = self.body.expression(label).ty.clone();
        let join = self.alloc(label_result, CoreId(u32::MAX));
        let leave_instructions = std::mem::take(&mut self.instructions);
        if let Some((name, _let_id)) = binding {
            self.named.insert(name, join);
        }
        let result = if replay_root_continuation {
            self.label_rejoins.insert(label, join);
            self.value(root)?
        } else if suffix.is_empty() {
            join
        } else {
            for value in suffix.iter().take(suffix.len() - 1) {
                self.statement(*value)?;
            }
            self.value(*suffix.last().expect("nonempty suffix"))?
        };
        let result_type = self.body.expression(root).ty.clone();
        let continuation_instructions = std::mem::take(&mut self.instructions);
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: result_type,
            entry: MirBlockId(0),
            blocks: vec![
                MirBlock {
                    parameters: vec![],
                    instructions: leave_instructions,
                    terminator: MirTerminator::Leave {
                        brand,
                        target: MirBlockId(1),
                        arguments: vec![value],
                        cleanup: MirCleanupPlan {
                            moved_places: self.leave_cleanup.moved_places.clone(),
                            active_loans: self.leave_cleanup.active_loans.clone(),
                        },
                    },
                },
                MirBlock {
                    parameters: vec![join],
                    instructions: continuation_instructions,
                    terminator: MirTerminator::Return { value: result },
                },
            ],
        })
    }

    /// Find and lower a transfer to `target` through arbitrarily nested
    /// static label scopes.  Labels do not have a runtime object; entering a
    /// nested label only changes which brand a transfer may name.  We inspect
    /// the path first so ordinary nested labels remain on the normal value
    /// path and are not executed twice.
    fn lower_label_transfer_path(
        &mut self,
        id: CoreId,
        target: crate::LabelBrand,
    ) -> Option<MirLocal> {
        match self.body.expression(id).kind.clone() {
            CoreKind::Block(values) => {
                for value in values {
                    if self.contains_label_transfer(value, target) {
                        return self.lower_label_transfer_path(value, target);
                    }
                    self.statement(value)?;
                }
                self.error("G6012", "label scope has no transfer to its target brand");
                None
            }
            CoreKind::Label { body, .. } => self.lower_label_transfer_path(body, target),
            CoreKind::Transfer { brand, value } if brand == target => self.value(value),
            CoreKind::Transfer { .. } => {
                self.error(
                    "G6012",
                    "nested label transfer requires its own cleanup-carrying target edge",
                );
                None
            }
            _ => {
                self.error(
                    "G6012",
                    "label transfer path is not a structured lexical exit",
                );
                None
            }
        }
    }

    /// Locate an inner lexical label whose own transfer is still valid when
    /// the label is used as an operand (for example `label done { ... } + 2`).
    /// Closures are an execution boundary: Core rejects outer-label captures,
    /// and lowering must not tunnel through that proof boundary.
    fn find_transfer_label(&self, id: CoreId) -> Option<CoreId> {
        match self.body.expression(id).kind.clone() {
            CoreKind::Label { brand, body } => self
                .contains_label_transfer(body, brand)
                .then_some(id)
                .or_else(|| self.find_transfer_label(body)),
            CoreKind::Closure { .. } => None,
            CoreKind::Tuple(values) | CoreKind::Array(values) | CoreKind::Block(values) => values
                .into_iter()
                .find_map(|value| self.find_transfer_label(value)),
            CoreKind::Record { fields, .. } | CoreKind::Enum { fields, .. } => fields
                .into_iter()
                .find_map(|field| self.find_transfer_label(field)),
            CoreKind::Field { base, .. }
            | CoreKind::PatternTest { subject: base, .. }
            | CoreKind::Let { value: base, .. }
            | CoreKind::Borrow { value: base, .. }
            | CoreKind::Deref(base)
            | CoreKind::Move(base)
            | CoreKind::Unary { value: base, .. }
            | CoreKind::Transfer { value: base, .. } => self.find_transfer_label(base),
            CoreKind::Assign { place, value } => match place {
                CorePlace::Deref { reference, .. } => self
                    .find_transfer_label(reference)
                    .or_else(|| self.find_transfer_label(value)),
                _ => self.find_transfer_label(value),
            },
            CoreKind::Call { callee, arguments } => {
                self.find_transfer_label(callee).or_else(|| {
                    arguments
                        .into_iter()
                        .find_map(|value| self.find_transfer_label(value))
                })
            }
            CoreKind::Perform { arguments, .. } => arguments
                .into_iter()
                .find_map(|value| self.find_transfer_label(value)),
            CoreKind::Handle {
                computation,
                clauses,
            } => self.find_transfer_label(computation).or_else(|| {
                clauses
                    .into_iter()
                    .find_map(|clause| self.find_transfer_label(clause.body))
            }),
            CoreKind::Completion {
                computation,
                clauses,
            } => self.find_transfer_label(computation).or_else(|| {
                clauses
                    .into_iter()
                    .find_map(|clause| self.find_transfer_label(clause.body))
            }),
            CoreKind::Binary { left, right, .. } => self
                .find_transfer_label(left)
                .or_else(|| self.find_transfer_label(right)),
            CoreKind::Literal(_)
            | CoreKind::Local(_)
            | CoreKind::Resumption { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant(_)
            | CoreKind::Error => None,
        }
    }

    /// Evaluate exactly the left-to-right work that precedes `target` on its
    /// enclosing source path.  The resulting locals remain in `values` and
    /// are therefore reused by the rejoin block; this is the small CPS bridge
    /// that prevents an operand-position label transfer from dropping or
    /// replaying a preceding computation.
    fn prepare_label_path(&mut self, id: CoreId, target: CoreId) -> bool {
        if id == target {
            return true;
        }
        match self.body.expression(id).kind.clone() {
            CoreKind::Closure { .. } => false,
            CoreKind::Label { body, .. } => self.prepare_label_path(body, target),
            CoreKind::Block(values) => {
                for value in values {
                    if self.prepare_label_path(value, target) {
                        return true;
                    }
                    if self.statement(value).is_none() {
                        return false;
                    }
                }
                false
            }
            CoreKind::Tuple(values) | CoreKind::Array(values) => {
                for value in values {
                    if self.prepare_label_path(value, target) {
                        return true;
                    }
                    if self.value(value).is_none() {
                        return false;
                    }
                }
                false
            }
            CoreKind::Record { fields, .. } | CoreKind::Enum { fields, .. } => {
                for field in fields {
                    if self.prepare_label_path(field, target) {
                        return true;
                    }
                    if self.value(field).is_none() {
                        return false;
                    }
                }
                false
            }
            CoreKind::Binary { left, right, .. } => {
                if self.prepare_label_path(left, target) {
                    true
                } else {
                    self.value(left).is_some() && self.prepare_label_path(right, target)
                }
            }
            CoreKind::Call { callee, arguments } => {
                if self.prepare_label_path(callee, target) {
                    return true;
                }
                if self.value(callee).is_none() {
                    return false;
                }
                for argument in arguments {
                    if self.prepare_label_path(argument, target) {
                        return true;
                    }
                    if self.value(argument).is_none() {
                        return false;
                    }
                }
                false
            }
            CoreKind::Perform { arguments, .. } => {
                for argument in arguments {
                    if self.prepare_label_path(argument, target) {
                        return true;
                    }
                    if self.value(argument).is_none() {
                        return false;
                    }
                }
                false
            }
            CoreKind::Field { base, .. }
            | CoreKind::PatternTest { subject: base, .. }
            | CoreKind::Let { value: base, .. }
            | CoreKind::Borrow { value: base, .. }
            | CoreKind::Deref(base)
            | CoreKind::Move(base)
            | CoreKind::Unary { value: base, .. }
            | CoreKind::Transfer { value: base, .. } => self.prepare_label_path(base, target),
            CoreKind::Assign { value, .. } => self.prepare_label_path(value, target),
            // Handler/completion clauses introduce independently checked
            // continuation scopes. Their label transfers are either rejected
            // by Core or lowered by the dedicated handler paths, never by
            // this lexical expression rejoin.
            CoreKind::Handle { .. }
            | CoreKind::Completion { .. }
            | CoreKind::Literal(_)
            | CoreKind::Local(_)
            | CoreKind::Resumption { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant(_)
            | CoreKind::Error => false,
        }
    }

    fn contains_label_transfer(&self, id: CoreId, target: crate::LabelBrand) -> bool {
        match &self.body.expression(id).kind {
            CoreKind::Transfer { brand, .. } => *brand == target,
            // A closure forms a separate execution environment. Its outer
            // label transfers are rejected by Core; transfers to labels it
            // declares itself cannot become an edge in this body.
            CoreKind::Closure { .. } => false,
            CoreKind::Block(values) => values
                .iter()
                .any(|child| self.contains_label_transfer(*child, target)),
            CoreKind::Label { body, .. } | CoreKind::Let { value: body, .. } => {
                self.contains_label_transfer(*body, target)
            }
            _ => false,
        }
    }
    /// Generalize nested setup frames from a single ordered sibling operation
    /// to several independent operation-key dispatch matrices. Each matrix
    /// preserves its own source-order pattern fallthrough and forwards only
    /// after its final refutable clause fails.
    fn lower_root_runtime_grouped_sibling_one_shot_handler(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (outer_computation, outer_clauses, root_prefix) =
            match self.body.expression(root).kind.clone() {
                CoreKind::Handle {
                    computation,
                    clauses,
                } => (computation, clauses, Vec::new()),
                CoreKind::Block(values) => {
                    let (outer, prefix) = values.split_last()?;
                    let CoreKind::Handle {
                        computation,
                        clauses,
                    } = self.body.expression(*outer).kind.clone()
                    else {
                        return None;
                    };
                    (computation, clauses, prefix.to_vec())
                }
                _ => return None,
            };
        let (inner, outer_prefix) = match self.body.expression(outer_computation).kind.clone() {
            CoreKind::Handle { .. } => (outer_computation, Vec::new()),
            CoreKind::Block(values) => {
                let (inner, prefix) = values.split_last()?;
                (*inner, prefix.to_vec())
            }
            _ => return None,
        };
        let CoreKind::Handle {
            computation: inner_computation,
            clauses: inner_clauses,
        } = self.body.expression(inner).kind.clone()
        else {
            return None;
        };
        let (performed, inner_prefix) = match self.body.expression(inner_computation).kind.clone() {
            CoreKind::Perform { .. } => (inner_computation, Vec::new()),
            CoreKind::Block(values) => {
                let (performed, prefix) = values.split_last()?;
                (*performed, prefix.to_vec())
            }
            _ => return None,
        };
        let CoreKind::Perform {
            effect,
            operation,
            arguments: argument_ids,
            terminal: false,
        } = self.body.expression(performed).kind.clone()
        else {
            return None;
        };
        let outer_operation_clauses = outer_clauses
            .iter()
            .filter(|clause| !clause.terminal)
            .collect::<Vec<_>>();
        let [outer_clause] = outer_operation_clauses.as_slice() else {
            return None;
        };
        let all_inner_operation_clauses = inner_clauses
            .iter()
            .filter(|clause| !clause.terminal)
            .collect::<Vec<_>>();
        let mut direct_clauses = all_inner_operation_clauses
            .iter()
            .copied()
            .filter(|clause| clause.effect == effect && clause.operation == operation)
            .collect::<Vec<_>>();
        if direct_clauses.is_empty() {
            return None;
        }
        let mut sibling_groups = Vec::<Vec<&CoreHandlerClause>>::new();
        for clause in all_inner_operation_clauses
            .into_iter()
            .filter(|clause| clause.effect != effect || clause.operation != operation)
        {
            if let Some(group) = sibling_groups.iter_mut().find(|group| {
                group[0].effect == clause.effect && group[0].operation == clause.operation
            }) {
                group.push(clause);
            } else {
                sibling_groups.push(vec![clause]);
            }
        }
        if sibling_groups.len() < 2
            || !sibling_groups.iter().any(|group| {
                group.len() > 1 || !group[0].patterns.iter().all(pattern_is_irrefutable)
            })
        {
            return None;
        }
        for group in &mut sibling_groups {
            if let Some(fallback) = group
                .iter()
                .position(|clause| clause.patterns.iter().all(pattern_is_irrefutable))
            {
                group.truncate(fallback + 1);
            }
        }
        if let Some(fallback) = direct_clauses
            .iter()
            .position(|clause| clause.patterns.iter().all(pattern_is_irrefutable))
        {
            direct_clauses.truncate(fallback + 1);
        }
        let exact_one_shot = |clause: &CoreHandlerClause| match &clause.resumption {
            CoreHandlerResumption::Explicit { quantity, .. }
            | CoreHandlerResumption::Tail { quantity } => {
                *quantity == crate::quantity::Quantity::ONCE
            }
            CoreHandlerResumption::Discard { .. } | CoreHandlerResumption::Terminal => false,
        };
        if !exact_one_shot(outer_clause)
            || outer_clause.effect != effect
            || outer_clause.operation != operation
            || outer_clause.patterns.len() != argument_ids.len()
            || !outer_clause.patterns.iter().all(pattern_is_irrefutable)
            || direct_clauses.iter().any(|clause| {
                !exact_one_shot(clause) || clause.patterns.len() != argument_ids.len()
            })
            || sibling_groups.iter().flatten().any(|clause| {
                !exact_one_shot(clause) || clause.patterns.len() != clause.payload_types.len()
            })
        {
            return None;
        }

        for expression in root_prefix {
            self.statement(expression)?;
        }
        let outer_payload_destinations = outer_clause
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), inner_computation))
            .collect::<Vec<_>>();
        let mut dispatches = Vec::with_capacity(sibling_groups.len());
        for group in sibling_groups {
            let payload_destinations = group[0]
                .payload_types
                .iter()
                .map(|ty| self.alloc(ty.clone(), inner_computation))
                .collect::<Vec<_>>();
            let clauses = group
                .into_iter()
                .map(|clause| {
                    let tests = if clause.patterns.iter().all(pattern_is_irrefutable) {
                        Vec::new()
                    } else {
                        clause
                            .patterns
                            .iter()
                            .cloned()
                            .zip(payload_destinations.iter().copied())
                            .map(|(pattern, subject)| {
                                Some((
                                    self.alloc(
                                        Type::Scalar(crate::types::ScalarType::Bool),
                                        inner_computation,
                                    ),
                                    subject,
                                    lower_pattern(pattern)?,
                                ))
                            })
                            .collect::<Option<Vec<_>>>()?
                    };
                    Some((clause, tests))
                })
                .collect::<Option<Vec<_>>>()?;
            dispatches.push(SiblingHandlerDispatch {
                clauses,
                payload_destinations,
                test_blocks: Vec::new(),
                body_blocks: Vec::new(),
                forward_block: None,
            });
        }
        let direct_payload_destinations = direct_clauses[0]
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), inner_computation))
            .collect::<Vec<_>>();
        let direct_clauses = direct_clauses
            .into_iter()
            .map(|clause| {
                let tests = if clause.patterns.iter().all(pattern_is_irrefutable) {
                    Vec::new()
                } else {
                    clause
                        .patterns
                        .iter()
                        .cloned()
                        .zip(direct_payload_destinations.iter().copied())
                        .map(|(pattern, subject)| {
                            Some((
                                self.alloc(
                                    Type::Scalar(crate::types::ScalarType::Bool),
                                    inner_computation,
                                ),
                                subject,
                                lower_pattern(pattern)?,
                            ))
                        })
                        .collect::<Option<Vec<_>>>()?
                };
                Some((clause, tests))
            })
            .collect::<Option<Vec<_>>>()?;
        let mut direct_dispatch = SiblingHandlerDispatch {
            clauses: direct_clauses,
            payload_destinations: direct_payload_destinations.clone(),
            test_blocks: Vec::new(),
            body_blocks: Vec::new(),
            forward_block: None,
        };
        let mut next_block = 2u32;
        for dispatch in &mut dispatches {
            dispatch.test_blocks = dispatch
                .clauses
                .iter()
                .map(|(_, tests)| {
                    (0..tests.len())
                        .map(|_| {
                            let block = MirBlockId(next_block);
                            next_block += 1;
                            block
                        })
                        .collect()
                })
                .collect();
            dispatch.body_blocks = (0..dispatch.clauses.len())
                .map(|_| {
                    let block = MirBlockId(next_block);
                    next_block += 1;
                    block
                })
                .collect();
            if !dispatch
                .clauses
                .last()
                .is_some_and(|(clause, _)| clause.patterns.iter().all(pattern_is_irrefutable))
            {
                dispatch.forward_block = Some(MirBlockId(next_block));
                next_block += 1;
            }
        }
        direct_dispatch.test_blocks = direct_dispatch
            .clauses
            .iter()
            .map(|(_, tests)| {
                (0..tests.len())
                    .map(|_| {
                        let block = MirBlockId(next_block);
                        next_block += 1;
                        block
                    })
                    .collect()
            })
            .collect();
        direct_dispatch.body_blocks = (0..direct_dispatch.clauses.len())
            .map(|_| {
                let block = MirBlockId(next_block);
                next_block += 1;
                block
            })
            .collect();
        if !direct_dispatch
            .clauses
            .last()
            .is_some_and(|(clause, _)| clause.patterns.iter().all(pattern_is_irrefutable))
        {
            direct_dispatch.forward_block = Some(MirBlockId(next_block));
        }
        let direct_target = direct_dispatch
            .test_blocks
            .first()
            .and_then(|tests| tests.first())
            .copied()
            .unwrap_or(direct_dispatch.body_blocks[0]);
        let result = self.alloc(
            self.body.expression(inner_computation).ty.clone(),
            inner_computation,
        );
        let mut entry = std::mem::take(&mut self.instructions);
        entry.push(MirInstruction::InstallHandler {
            effect: outer_clause.effect.definition,
            effect_arguments: outer_clause.effect.arguments.clone(),
            operation: outer_clause.operation,
            payload_destinations: outer_payload_destinations.clone(),
            resume_type: self.body.expression(inner_computation).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target: MirBlockId(1),
        });
        self.instructions = Vec::new();
        for expression in outer_prefix {
            self.statement(expression)?;
        }
        entry.extend(std::mem::take(&mut self.instructions));
        for dispatch in &dispatches {
            let (clause, tests) = &dispatch.clauses[0];
            let target = tests
                .first()
                .and_then(|_| dispatch.test_blocks[0].first())
                .copied()
                .unwrap_or(dispatch.body_blocks[0]);
            entry.push(MirInstruction::InstallHandler {
                effect: clause.effect.definition,
                effect_arguments: clause.effect.arguments.clone(),
                operation: clause.operation,
                payload_destinations: dispatch.payload_destinations.clone(),
                resume_type: self.body.expression(inner_computation).ty.clone(),
                continuation: MirContinuationPolicy::Consume,
                target,
            });
        }
        entry.push(MirInstruction::InstallHandler {
            effect: effect.definition,
            effect_arguments: effect.arguments.clone(),
            operation,
            payload_destinations: direct_payload_destinations.clone(),
            resume_type: self.body.expression(inner_computation).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target: direct_target,
        });
        self.instructions = Vec::new();
        for expression in inner_prefix {
            self.statement(expression)?;
        }
        let arguments = argument_ids
            .iter()
            .map(|argument| self.value(*argument))
            .collect::<Option<Vec<_>>>()?;
        entry.extend(std::mem::take(&mut self.instructions));
        entry.push(MirInstruction::Perform {
            dst: result,
            effect: effect.definition,
            effect_arguments: effect.arguments,
            operation,
            arguments,
        });
        entry.push(MirInstruction::UninstallHandler);
        for _ in &dispatches {
            entry.push(MirInstruction::UninstallHandler);
        }
        entry.push(MirInstruction::UninstallHandler);

        self.instructions = Vec::new();
        let outer_named = self.named.clone();
        self.bind_handler_patterns(&outer_clause.patterns, &outer_payload_destinations)?;
        let outer_resumed = self.direct_handler_clause_value(outer_clause)?;
        self.instructions.push(MirInstruction::Resume {
            value: outer_resumed,
        });
        let outer_instructions = std::mem::take(&mut self.instructions);
        self.named = outer_named;

        let mut dispatch_instructions = Vec::with_capacity(dispatches.len());
        for dispatch in &dispatches {
            let mut bodies = Vec::with_capacity(dispatch.clauses.len());
            for (clause, _) in &dispatch.clauses {
                self.instructions = Vec::new();
                let named = self.named.clone();
                self.bind_handler_patterns(&clause.patterns, &dispatch.payload_destinations)?;
                let resumed = self.direct_handler_clause_value(clause)?;
                self.instructions
                    .push(MirInstruction::Resume { value: resumed });
                bodies.push(std::mem::take(&mut self.instructions));
                self.named = named;
            }
            dispatch_instructions.push(bodies);
        }
        let mut direct_instructions = Vec::with_capacity(direct_dispatch.clauses.len());
        for (clause, _) in &direct_dispatch.clauses {
            self.instructions = Vec::new();
            let named = self.named.clone();
            self.bind_handler_patterns(&clause.patterns, &direct_payload_destinations)?;
            let resumed = self.direct_handler_clause_value(clause)?;
            self.instructions
                .push(MirInstruction::Resume { value: resumed });
            direct_instructions.push(std::mem::take(&mut self.instructions));
            self.named = named;
        }

        let mut blocks = vec![
            MirBlock {
                parameters: vec![],
                instructions: entry,
                terminator: MirTerminator::Return { value: result },
            },
            MirBlock {
                parameters: vec![],
                instructions: outer_instructions,
                terminator: MirTerminator::Unreachable,
            },
        ];
        for (dispatch, bodies) in dispatches.iter().zip(dispatch_instructions) {
            for (clause_index, ((_, tests), test_blocks)) in dispatch
                .clauses
                .iter()
                .zip(&dispatch.test_blocks)
                .enumerate()
            {
                if tests.is_empty() {
                    continue;
                }
                let failure_target = dispatch
                    .test_blocks
                    .get(clause_index + 1)
                    .and_then(|tests| tests.first())
                    .copied()
                    .or_else(|| dispatch.body_blocks.get(clause_index + 1).copied())
                    .or(dispatch.forward_block)
                    .expect("sibling dispatch has a fallback or forward target");
                for (test_index, (condition, subject, pattern)) in tests.iter().enumerate() {
                    blocks.push(MirBlock {
                        parameters: vec![],
                        instructions: vec![MirInstruction::PatternTest {
                            dst: *condition,
                            subject: *subject,
                            pattern: pattern.clone(),
                        }],
                        terminator: MirTerminator::SwitchBool {
                            condition: *condition,
                            then_target: if test_index + 1 == tests.len() {
                                dispatch.body_blocks[clause_index]
                            } else {
                                test_blocks[test_index + 1]
                            },
                            then_arguments: vec![],
                            else_target: failure_target,
                            else_arguments: vec![],
                        },
                    });
                }
            }
            for instructions in bodies {
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions,
                    terminator: MirTerminator::Unreachable,
                });
            }
            if dispatch.forward_block.is_some() {
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions: vec![MirInstruction::Forward],
                    terminator: MirTerminator::Unreachable,
                });
            }
        }
        for (clause_index, ((_, tests), test_blocks)) in direct_dispatch
            .clauses
            .iter()
            .zip(&direct_dispatch.test_blocks)
            .enumerate()
        {
            if tests.is_empty() {
                continue;
            }
            let failure_target = direct_dispatch
                .test_blocks
                .get(clause_index + 1)
                .and_then(|tests| tests.first())
                .copied()
                .or_else(|| direct_dispatch.body_blocks.get(clause_index + 1).copied())
                .or(direct_dispatch.forward_block)
                .expect("direct dispatch has a fallback or forward target");
            for (test_index, (condition, subject, pattern)) in tests.iter().enumerate() {
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions: vec![MirInstruction::PatternTest {
                        dst: *condition,
                        subject: *subject,
                        pattern: pattern.clone(),
                    }],
                    terminator: MirTerminator::SwitchBool {
                        condition: *condition,
                        then_target: if test_index + 1 == tests.len() {
                            direct_dispatch.body_blocks[clause_index]
                        } else {
                            test_blocks[test_index + 1]
                        },
                        then_arguments: vec![],
                        else_target: failure_target,
                        else_arguments: vec![],
                    },
                });
            }
        }
        for instructions in direct_instructions {
            blocks.push(MirBlock {
                parameters: vec![],
                instructions,
                terminator: MirTerminator::Unreachable,
            });
        }
        if direct_dispatch.forward_block.is_some() {
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::Forward],
                terminator: MirTerminator::Unreachable,
            });
        }
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }
    /// Lower the root short-circuit forms with real CFG edges rather than an
    /// eager boolean instruction. The join block's sole parameter is the
    /// semantic result: one predecessor supplies the skipped constant, the
    /// other evaluates and supplies the right operand. This shape is also the
    /// minimal reusable continuation boundary for later handler lowering.
    fn lower_root_short_circuit(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let binary = match self.body.expression(root).kind.clone() {
            CoreKind::Binary {
                operator,
                left,
                right,
            } => Some((operator, left, right)),
            CoreKind::Block(values) => {
                let (last, prefix) = values.split_last()?;
                for value in prefix {
                    self.statement(*value)?;
                }
                let CoreKind::Binary {
                    operator,
                    left,
                    right,
                } = self.body.expression(*last).kind.clone()
                else {
                    return None;
                };
                Some((operator, left, right))
            }
            _ => None,
        };
        let (operator, left, right) = binary?;
        if !matches!(operator.as_str(), "and" | "or") {
            return None;
        }
        let bool_ty = Type::Scalar(crate::types::ScalarType::Bool);
        if self.body.expression(root).ty != bool_ty
            || self.body.expression(left).ty != bool_ty
            || self.body.expression(right).ty != bool_ty
        {
            self.error("G6005", "short-circuit operator lost its boolean type");
            return Some(self.invalid_function(parameters));
        }
        let condition = self.value(left)?;
        let skipped = self.alloc(bool_ty.clone(), root);
        self.instructions.push(MirInstruction::ConstBool {
            dst: skipped,
            value: operator == "or",
        });
        let entry_instructions = std::mem::take(&mut self.instructions);
        let entry_values = self.values.clone();
        let entry_named = self.named.clone();

        self.instructions = vec![];
        self.values = entry_values;
        self.named = entry_named;
        let right = self.value(right)?;
        let right_instructions = std::mem::take(&mut self.instructions);
        let joined = self.alloc(bool_ty, root);
        let (then_target, then_arguments, else_target, else_arguments) = if operator == "and" {
            (MirBlockId(1), vec![], MirBlockId(2), vec![skipped])
        } else {
            (MirBlockId(2), vec![skipped], MirBlockId(1), vec![])
        };
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks: vec![
                MirBlock {
                    parameters: vec![],
                    instructions: entry_instructions,
                    terminator: MirTerminator::SwitchBool {
                        condition,
                        then_target,
                        then_arguments,
                        else_target,
                        else_arguments,
                    },
                },
                MirBlock {
                    parameters: vec![],
                    instructions: right_instructions,
                    terminator: MirTerminator::Goto {
                        target: MirBlockId(2),
                        arguments: vec![right],
                    },
                },
                MirBlock {
                    parameters: vec![joined],
                    instructions: vec![],
                    terminator: MirTerminator::Return { value: joined },
                },
            ],
        })
    }
    /// Lower a straight-line sequence of one-shot performances under one
    /// lexical handler.  Each operation gets an explicit dispatch subgraph;
    /// every arm enters the following residual block through that operation's
    /// typed result parameter.  This is deliberately a static CFG expansion,
    /// not a substitute for the general dynamic handler stack needed for
    /// effects hidden behind calls or escaping resumptions.
    fn lower_root_linear_resumptions(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let CoreKind::Block(root_values) = self.body.expression(root).kind.clone() else {
            return None;
        };
        let (handler, root_prefix) = root_values.split_last()?;
        let CoreKind::Handle {
            computation,
            clauses,
        } = self.body.expression(*handler).kind.clone()
        else {
            return None;
        };
        let CoreKind::Block(computation_values) = self.body.expression(computation).kind.clone()
        else {
            return None;
        };
        let mut steps = Vec::new();
        for (index, binding) in computation_values.iter().copied().enumerate() {
            let CoreKind::Let { name, value } = self.body.expression(binding).kind.clone() else {
                continue;
            };
            let CoreKind::Perform {
                effect,
                operation,
                arguments,
                terminal: false,
            } = self.body.expression(value).kind.clone()
            else {
                continue;
            };
            let mut matching = clauses
                .iter()
                .filter(|clause| {
                    !clause.terminal && clause.effect == effect && clause.operation == operation
                })
                .cloned()
                .collect::<Vec<_>>();
            let has_fallback = if let Some(fallback) = matching
                .iter()
                .position(|clause| clause.patterns.iter().all(pattern_is_irrefutable))
            {
                matching.truncate(fallback + 1);
                true
            } else {
                false
            };
            if matching.iter().any(|clause| {
                clause.patterns.len() != arguments.len()
                    || !matches!(
                        clause.resumption,
                        CoreHandlerResumption::Tail { .. }
                            | CoreHandlerResumption::Explicit { .. }
                            | CoreHandlerResumption::Discard { .. }
                    )
            }) {
                return None;
            }
            steps.push((index, name, value, arguments, matching, has_fallback));
        }
        // The single-site path below emits a smaller CFG.  This one owns the
        // multi-site case so its discovery phase can fail without mutating the
        // ambient lowering state.
        if steps.len() < 2
            || steps
                .last()
                .is_some_and(|(index, ..)| *index + 1 == computation_values.len())
        {
            return None;
        }

        let continuation_parameters = steps
            .iter()
            .map(|(_, _, value, _, _, _)| {
                self.alloc(self.body.expression(*value).ty.clone(), *value)
            })
            .collect::<Vec<_>>();
        let mut blocks = (0..=steps.len())
            .map(|index| MirBlock {
                parameters: if index == 0 {
                    vec![]
                } else {
                    vec![continuation_parameters[index - 1]]
                },
                instructions: vec![],
                terminator: MirTerminator::Unreachable,
            })
            .collect::<Vec<_>>();
        let mut cursor = 0usize;
        for (step_index, (position, name, _value, argument_ids, matching, has_fallback)) in
            steps.iter().enumerate()
        {
            self.instructions = vec![];
            if step_index == 0 {
                for expression in root_prefix {
                    if self.statement(*expression).is_none() {
                        return Some(self.invalid_function(parameters));
                    }
                }
            }
            for expression in &computation_values[cursor..*position] {
                if self.statement(*expression).is_none() {
                    return Some(self.invalid_function(parameters));
                }
            }
            let mut arguments = Vec::with_capacity(argument_ids.len());
            for argument in argument_ids {
                let Some(argument) = self.value(*argument) else {
                    return Some(self.invalid_function(parameters));
                };
                arguments.push(argument);
            }
            blocks[step_index].instructions = std::mem::take(&mut self.instructions);

            let mut bodies = Vec::with_capacity(matching.len());
            for clause in matching {
                self.instructions = vec![];
                let before_clause = self.named.clone();
                // A source clause is emitted once per static performance
                // site. Its Core IDs are shared, but its payload and
                // resumption environment are not; do not let the ordinary
                // Core-value memo reuse a local produced for an earlier site.
                let before_values = self.values.clone();
                if self
                    .bind_handler_patterns(&clause.patterns, &arguments)
                    .is_none()
                {
                    self.named = before_clause;
                    self.values = before_values;
                    return Some(self.invalid_function(parameters));
                }
                let Some(resumed) = self.direct_handler_clause_value(clause) else {
                    self.named = before_clause;
                    self.values = before_values;
                    return Some(self.invalid_function(parameters));
                };
                let instructions = std::mem::take(&mut self.instructions);
                self.named = before_clause;
                self.values = before_values;
                let id = MirBlockId(blocks.len() as u32);
                let terminator =
                    if matches!(clause.resumption, CoreHandlerResumption::Discard { .. }) {
                        MirTerminator::Return { value: resumed }
                    } else {
                        MirTerminator::Goto {
                            target: MirBlockId((step_index + 1) as u32),
                            arguments: vec![resumed],
                        }
                    };
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions,
                    terminator,
                });
                bodies.push(id);
            }
            let mut next = if *has_fallback {
                *bodies.last().expect("validated handler fallback exists")
            } else {
                let id = MirBlockId(blocks.len() as u32);
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions: vec![],
                    terminator: MirTerminator::Unreachable,
                });
                id
            };
            let tested = if *has_fallback {
                matching.len().saturating_sub(1)
            } else {
                matching.len()
            };
            for arm_index in (0..tested).rev() {
                let mut selected = bodies[arm_index];
                for (pattern, argument) in matching[arm_index]
                    .patterns
                    .iter()
                    .cloned()
                    .zip(arguments.iter().copied())
                    .rev()
                {
                    let Some(pattern) = lower_pattern(pattern) else {
                        self.error(
                            "G6005",
                            "resumptive handler contains an invalid structural pattern",
                        );
                        return Some(self.invalid_function(parameters));
                    };
                    let condition = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), root);
                    blocks[step_index]
                        .instructions
                        .push(MirInstruction::PatternTest {
                            dst: condition,
                            subject: argument,
                            pattern,
                        });
                    let id = MirBlockId(blocks.len() as u32);
                    blocks.push(MirBlock {
                        parameters: vec![],
                        instructions: vec![],
                        terminator: MirTerminator::SwitchBool {
                            condition,
                            then_target: selected,
                            then_arguments: vec![],
                            else_target: next,
                            else_arguments: vec![],
                        },
                    });
                    selected = id;
                }
                next = selected;
            }
            blocks[step_index].terminator = MirTerminator::Goto {
                target: next,
                arguments: vec![],
            };
            self.named
                .insert(name.clone(), continuation_parameters[step_index]);
            cursor = *position + 1;
        }
        self.instructions = vec![];
        let Some((last, prefix)) = computation_values[cursor..].split_last() else {
            return Some(self.invalid_function(parameters));
        };
        for expression in prefix {
            if self.statement(*expression).is_none() {
                return Some(self.invalid_function(parameters));
            }
        }
        let Some(result) = self.value(*last) else {
            return Some(self.invalid_function(parameters));
        };
        blocks[steps.len()].instructions = std::mem::take(&mut self.instructions);
        blocks[steps.len()].terminator = MirTerminator::Return { value: result };
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }
    /// Install independent exact-one-shot frames for several distinct sibling
    /// operations during nested-handler setup. Repeated-key and refutable
    /// siblings remain on the ordered dispatcher below because they require
    /// source-order pattern fallthrough.
    fn lower_root_runtime_multiple_sibling_one_shot_handler(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (outer_computation, outer_clauses, root_prefix) =
            match self.body.expression(root).kind.clone() {
                CoreKind::Handle {
                    computation,
                    clauses,
                } => (computation, clauses, Vec::new()),
                CoreKind::Block(values) => {
                    let (outer, prefix) = values.split_last()?;
                    let CoreKind::Handle {
                        computation,
                        clauses,
                    } = self.body.expression(*outer).kind.clone()
                    else {
                        return None;
                    };
                    (computation, clauses, prefix.to_vec())
                }
                _ => return None,
            };
        let (inner, outer_prefix) = match self.body.expression(outer_computation).kind.clone() {
            CoreKind::Handle { .. } => (outer_computation, Vec::new()),
            CoreKind::Block(values) => {
                let (inner, prefix) = values.split_last()?;
                (*inner, prefix.to_vec())
            }
            _ => return None,
        };
        let CoreKind::Handle {
            computation: inner_computation,
            clauses: inner_clauses,
        } = self.body.expression(inner).kind.clone()
        else {
            return None;
        };
        let (performed, inner_prefix) = match self.body.expression(inner_computation).kind.clone() {
            CoreKind::Perform { .. } => (inner_computation, Vec::new()),
            CoreKind::Block(values) => {
                let (performed, prefix) = values.split_last()?;
                (*performed, prefix.to_vec())
            }
            _ => return None,
        };
        let CoreKind::Perform {
            effect,
            operation,
            arguments: argument_ids,
            terminal: false,
        } = self.body.expression(performed).kind.clone()
        else {
            return None;
        };
        let outer_operation_clauses = outer_clauses
            .iter()
            .filter(|clause| !clause.terminal)
            .collect::<Vec<_>>();
        let [outer_clause] = outer_operation_clauses.as_slice() else {
            return None;
        };
        let all_inner_operation_clauses = inner_clauses
            .iter()
            .filter(|clause| !clause.terminal)
            .collect::<Vec<_>>();
        let direct_clauses = all_inner_operation_clauses
            .iter()
            .copied()
            .filter(|clause| clause.effect == effect && clause.operation == operation)
            .collect::<Vec<_>>();
        let [direct_clause] = direct_clauses.as_slice() else {
            return None;
        };
        let mut sibling_groups = Vec::<Vec<&CoreHandlerClause>>::new();
        for clause in all_inner_operation_clauses
            .into_iter()
            .filter(|clause| clause.effect != effect || clause.operation != operation)
        {
            if let Some(group) = sibling_groups.iter_mut().find(|group| {
                group[0].effect == clause.effect && group[0].operation == clause.operation
            }) {
                group.push(clause);
            } else {
                sibling_groups.push(vec![clause]);
            }
        }
        // The existing ordered dispatcher owns repeated-key/refutable cases.
        // This adjacent path handles multiple distinct keys, each with its
        // single irrefutable exact-one-shot clause, so every setup operation
        // gets its own deep frame instead of being silently unavailable.
        if sibling_groups.len() < 2 || sibling_groups.iter().any(|group| group.len() != 1) {
            return None;
        }
        let sibling_clauses = sibling_groups
            .into_iter()
            .map(|mut group| group.remove(0))
            .collect::<Vec<_>>();
        let exact_one_shot = |clause: &CoreHandlerClause| match &clause.resumption {
            CoreHandlerResumption::Explicit { quantity, .. }
            | CoreHandlerResumption::Tail { quantity } => {
                *quantity == crate::quantity::Quantity::ONCE
            }
            CoreHandlerResumption::Discard { .. } | CoreHandlerResumption::Terminal => false,
        };
        if !exact_one_shot(outer_clause)
            || outer_clause.effect != effect
            || outer_clause.operation != operation
            || outer_clause.patterns.len() != argument_ids.len()
            || !outer_clause.patterns.iter().all(pattern_is_irrefutable)
            || !exact_one_shot(direct_clause)
            || direct_clause.patterns.len() != argument_ids.len()
            || !direct_clause.patterns.iter().all(pattern_is_irrefutable)
            || sibling_clauses.iter().any(|clause| {
                !exact_one_shot(clause)
                    || clause.patterns.len() != clause.payload_types.len()
                    || !clause.patterns.iter().all(pattern_is_irrefutable)
            })
        {
            return None;
        }

        for expression in root_prefix {
            self.statement(expression)?;
        }
        let outer_payload_destinations = outer_clause
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), inner_computation))
            .collect::<Vec<_>>();
        let sibling_payload_destinations = sibling_clauses
            .iter()
            .map(|clause| {
                clause
                    .payload_types
                    .iter()
                    .map(|ty| self.alloc(ty.clone(), inner_computation))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let direct_payload_destinations = direct_clause
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), inner_computation))
            .collect::<Vec<_>>();
        let sibling_targets = (0..sibling_clauses.len())
            .map(|index| MirBlockId(2 + index as u32))
            .collect::<Vec<_>>();
        let direct_target = MirBlockId(2 + sibling_clauses.len() as u32);
        let result = self.alloc(
            self.body.expression(inner_computation).ty.clone(),
            inner_computation,
        );

        let mut entry = std::mem::take(&mut self.instructions);
        entry.push(MirInstruction::InstallHandler {
            effect: outer_clause.effect.definition,
            effect_arguments: outer_clause.effect.arguments.clone(),
            operation: outer_clause.operation,
            payload_destinations: outer_payload_destinations.clone(),
            resume_type: self.body.expression(inner_computation).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target: MirBlockId(1),
        });
        self.instructions = Vec::new();
        for expression in outer_prefix {
            self.statement(expression)?;
        }
        entry.extend(std::mem::take(&mut self.instructions));
        for ((clause, payload_destinations), target) in sibling_clauses
            .iter()
            .zip(&sibling_payload_destinations)
            .zip(&sibling_targets)
        {
            entry.push(MirInstruction::InstallHandler {
                effect: clause.effect.definition,
                effect_arguments: clause.effect.arguments.clone(),
                operation: clause.operation,
                payload_destinations: payload_destinations.clone(),
                resume_type: self.body.expression(inner_computation).ty.clone(),
                continuation: MirContinuationPolicy::Consume,
                target: *target,
            });
        }
        entry.push(MirInstruction::InstallHandler {
            effect: effect.definition,
            effect_arguments: effect.arguments.clone(),
            operation,
            payload_destinations: direct_payload_destinations.clone(),
            resume_type: self.body.expression(inner_computation).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target: direct_target,
        });
        self.instructions = Vec::new();
        for expression in inner_prefix {
            self.statement(expression)?;
        }
        let arguments = argument_ids
            .iter()
            .map(|argument| self.value(*argument))
            .collect::<Option<Vec<_>>>()?;
        entry.extend(std::mem::take(&mut self.instructions));
        entry.push(MirInstruction::Perform {
            dst: result,
            effect: effect.definition,
            effect_arguments: effect.arguments,
            operation,
            arguments,
        });
        entry.push(MirInstruction::UninstallHandler);
        for _ in &sibling_clauses {
            entry.push(MirInstruction::UninstallHandler);
        }
        entry.push(MirInstruction::UninstallHandler);

        self.instructions = Vec::new();
        let outer_named = self.named.clone();
        self.bind_handler_patterns(&outer_clause.patterns, &outer_payload_destinations)?;
        let outer_resumed = self.direct_handler_clause_value(outer_clause)?;
        self.instructions.push(MirInstruction::Resume {
            value: outer_resumed,
        });
        let outer_instructions = std::mem::take(&mut self.instructions);
        self.named = outer_named;

        let mut sibling_bodies = Vec::with_capacity(sibling_clauses.len());
        for (clause, payload_destinations) in
            sibling_clauses.iter().zip(&sibling_payload_destinations)
        {
            self.instructions = Vec::new();
            let named = self.named.clone();
            self.bind_handler_patterns(&clause.patterns, payload_destinations)?;
            let resumed = self.direct_handler_clause_value(clause)?;
            self.instructions
                .push(MirInstruction::Resume { value: resumed });
            sibling_bodies.push(std::mem::take(&mut self.instructions));
            self.named = named;
        }
        self.instructions = Vec::new();
        let direct_named = self.named.clone();
        self.bind_handler_patterns(&direct_clause.patterns, &direct_payload_destinations)?;
        let direct_resumed = self.direct_handler_clause_value(direct_clause)?;
        self.instructions.push(MirInstruction::Resume {
            value: direct_resumed,
        });
        let direct_instructions = std::mem::take(&mut self.instructions);
        self.named = direct_named;

        let mut blocks = vec![
            MirBlock {
                parameters: vec![],
                instructions: entry,
                terminator: MirTerminator::Return { value: result },
            },
            MirBlock {
                parameters: vec![],
                instructions: outer_instructions,
                terminator: MirTerminator::Unreachable,
            },
        ];
        for instructions in sibling_bodies {
            blocks.push(MirBlock {
                parameters: vec![],
                instructions,
                terminator: MirTerminator::Unreachable,
            });
        }
        blocks.push(MirBlock {
            parameters: vec![],
            instructions: direct_instructions,
            terminator: MirTerminator::Unreachable,
        });
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }
    /// Lower ordered exact-one-shot clauses for one operation inside an outer
    /// exact-one-shot frame. Failed structural tests advance through source
    /// order and exhaust into `Forward`, so a partial inner handler preserves
    /// ordinary deep-handler outward traversal rather than choosing an arm at
    /// compile time.
    fn lower_root_runtime_ordered_nested_one_shot_handler(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (outer_computation, outer_clauses, root_prefix) =
            match self.body.expression(root).kind.clone() {
                CoreKind::Handle {
                    computation,
                    clauses,
                } => (computation, clauses, Vec::new()),
                CoreKind::Block(values) => {
                    let (outer, prefix) = values.split_last()?;
                    let CoreKind::Handle {
                        computation,
                        clauses,
                    } = self.body.expression(*outer).kind.clone()
                    else {
                        return None;
                    };
                    (computation, clauses, prefix.to_vec())
                }
                _ => return None,
            };
        let (inner, outer_prefix) = match self.body.expression(outer_computation).kind.clone() {
            CoreKind::Handle { .. } => (outer_computation, Vec::new()),
            CoreKind::Block(values) => {
                let (inner, prefix) = values.split_last()?;
                (inner.to_owned(), prefix.to_vec())
            }
            _ => return None,
        };
        let CoreKind::Handle {
            computation: inner_computation,
            clauses: inner_clauses,
        } = self.body.expression(inner).kind.clone()
        else {
            return None;
        };
        let (performed, inner_prefix) = match self.body.expression(inner_computation).kind.clone() {
            CoreKind::Perform { .. } => (inner_computation, Vec::new()),
            CoreKind::Block(values) => {
                let (performed, prefix) = values.split_last()?;
                (*performed, prefix.to_vec())
            }
            _ => return None,
        };
        let CoreKind::Perform {
            effect,
            operation,
            arguments: argument_ids,
            terminal: false,
        } = self.body.expression(performed).kind.clone()
        else {
            return None;
        };
        let outer_operation_clauses = outer_clauses
            .iter()
            .filter(|clause| !clause.terminal)
            .collect::<Vec<_>>();
        let [outer_clause] = outer_operation_clauses.as_slice() else {
            return None;
        };
        let all_inner_operation_clauses = inner_clauses
            .iter()
            .filter(|clause| !clause.terminal)
            .collect::<Vec<_>>();
        let mut inner_operation_clauses = all_inner_operation_clauses
            .iter()
            .copied()
            .filter(|clause| clause.effect == effect && clause.operation == operation)
            .collect::<Vec<_>>();
        let mut sibling_operation_clauses = all_inner_operation_clauses
            .iter()
            .copied()
            .filter(|clause| clause.effect != effect || clause.operation != operation)
            .collect::<Vec<_>>();
        if inner_operation_clauses.is_empty() {
            return None;
        }
        if sibling_operation_clauses.iter().skip(1).any(|clause| {
            clause.effect != sibling_operation_clauses[0].effect
                || clause.operation != sibling_operation_clauses[0].operation
        }) {
            return None;
        }
        if let Some(fallback) = inner_operation_clauses
            .iter()
            .position(|clause| clause.patterns.iter().all(pattern_is_irrefutable))
        {
            inner_operation_clauses.truncate(fallback + 1);
        }
        if let Some(fallback) = sibling_operation_clauses
            .iter()
            .position(|clause| clause.patterns.iter().all(pattern_is_irrefutable))
        {
            sibling_operation_clauses.truncate(fallback + 1);
        }
        let exact_one_shot = |clause: &CoreHandlerClause| match &clause.resumption {
            CoreHandlerResumption::Explicit { quantity, .. }
            | CoreHandlerResumption::Tail { quantity } => {
                *quantity == crate::quantity::Quantity::ONCE
            }
            CoreHandlerResumption::Discard { .. } | CoreHandlerResumption::Terminal => false,
        };
        if !exact_one_shot(outer_clause)
            || outer_clause.patterns.len() != argument_ids.len()
            || !outer_clause.patterns.iter().all(pattern_is_irrefutable)
            || inner_operation_clauses.iter().any(|clause| {
                !exact_one_shot(clause) || clause.patterns.len() != argument_ids.len()
            })
            || sibling_operation_clauses.iter().any(|clause| {
                !exact_one_shot(clause) || clause.patterns.len() != clause.payload_types.len()
            })
        {
            return None;
        }
        for expression in root_prefix {
            self.statement(expression)?;
        }
        let outer_payload_destinations = outer_clause
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), inner_computation))
            .collect::<Vec<_>>();
        let inner_payload_destinations = inner_operation_clauses[0]
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), inner_computation))
            .collect::<Vec<_>>();
        let mut dispatch = Vec::with_capacity(inner_operation_clauses.len());
        for clause in inner_operation_clauses {
            let tests = if clause.patterns.iter().all(pattern_is_irrefutable) {
                Vec::new()
            } else {
                clause
                    .patterns
                    .iter()
                    .cloned()
                    .zip(inner_payload_destinations.iter().copied())
                    .map(|(pattern, subject)| {
                        Some((
                            self.alloc(
                                Type::Scalar(crate::types::ScalarType::Bool),
                                inner_computation,
                            ),
                            subject,
                            lower_pattern(pattern)?,
                        ))
                    })
                    .collect::<Option<Vec<_>>>()?
            };
            dispatch.push((clause, tests));
        }
        let test_count = dispatch.iter().map(|(_, tests)| tests.len()).sum::<usize>();
        let body_start = 2 + test_count as u32;
        let has_fallback = dispatch
            .last()
            .is_some_and(|(clause, _)| clause.patterns.iter().all(pattern_is_irrefutable));
        let forward_target = MirBlockId(body_start + dispatch.len() as u32);
        let sibling_test_start = forward_target.0 + u32::from(!has_fallback);
        let mut clause_targets = Vec::with_capacity(dispatch.len());
        let mut next_test = 2u32;
        for (index, (_, tests)) in dispatch.iter().enumerate() {
            if tests.is_empty() {
                clause_targets.push(MirBlockId(body_start + index as u32));
            } else {
                clause_targets.push(MirBlockId(next_test));
                next_test += tests.len() as u32;
            }
        }
        let sibling_payload_destinations = sibling_operation_clauses.first().map(|clause| {
            clause
                .payload_types
                .iter()
                .map(|ty| self.alloc(ty.clone(), inner_computation))
                .collect::<Vec<_>>()
        });
        let mut sibling_dispatch = Vec::with_capacity(sibling_operation_clauses.len());
        for clause in sibling_operation_clauses {
            let tests = if clause.patterns.iter().all(pattern_is_irrefutable) {
                Vec::new()
            } else {
                clause
                    .patterns
                    .iter()
                    .cloned()
                    .zip(
                        sibling_payload_destinations
                            .as_ref()
                            .expect("sibling clause payload destinations exist")
                            .iter()
                            .copied(),
                    )
                    .map(|(pattern, subject)| {
                        Some((
                            self.alloc(
                                Type::Scalar(crate::types::ScalarType::Bool),
                                inner_computation,
                            ),
                            subject,
                            lower_pattern(pattern)?,
                        ))
                    })
                    .collect::<Option<Vec<_>>>()?
            };
            sibling_dispatch.push((clause, tests));
        }
        let sibling_test_count = sibling_dispatch
            .iter()
            .map(|(_, tests)| tests.len())
            .sum::<usize>();
        let sibling_body_start = sibling_test_start + sibling_test_count as u32;
        let sibling_has_fallback = sibling_dispatch
            .last()
            .is_some_and(|(clause, _)| clause.patterns.iter().all(pattern_is_irrefutable));
        let sibling_forward_target = MirBlockId(sibling_body_start + sibling_dispatch.len() as u32);
        let mut sibling_clause_targets = Vec::with_capacity(sibling_dispatch.len());
        let mut next_sibling_test = sibling_test_start;
        for (index, (_, tests)) in sibling_dispatch.iter().enumerate() {
            if tests.is_empty() {
                sibling_clause_targets.push(MirBlockId(sibling_body_start + index as u32));
            } else {
                sibling_clause_targets.push(MirBlockId(next_sibling_test));
                next_sibling_test += tests.len() as u32;
            }
        }
        let result = self.alloc(
            self.body.expression(inner_computation).ty.clone(),
            inner_computation,
        );
        let mut entry = std::mem::take(&mut self.instructions);
        entry.push(MirInstruction::InstallHandler {
            effect: outer_clause.effect.definition,
            effect_arguments: outer_clause.effect.arguments.clone(),
            operation: outer_clause.operation,
            payload_destinations: outer_payload_destinations.clone(),
            resume_type: self.body.expression(inner_computation).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target: MirBlockId(1),
        });
        self.instructions = Vec::new();
        for expression in outer_prefix {
            self.statement(expression)?;
        }
        entry.extend(std::mem::take(&mut self.instructions));
        if let (Some((clause, _)), Some(payload_destinations)) = (
            sibling_dispatch.first(),
            sibling_payload_destinations.as_ref(),
        ) {
            entry.push(MirInstruction::InstallHandler {
                effect: clause.effect.definition,
                effect_arguments: clause.effect.arguments.clone(),
                operation: clause.operation,
                payload_destinations: payload_destinations.clone(),
                resume_type: self.body.expression(inner_computation).ty.clone(),
                continuation: MirContinuationPolicy::Consume,
                target: sibling_clause_targets[0],
            });
        }
        entry.push(MirInstruction::InstallHandler {
            effect: effect.definition,
            effect_arguments: effect.arguments.clone(),
            operation,
            payload_destinations: inner_payload_destinations.clone(),
            resume_type: self.body.expression(inner_computation).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target: clause_targets[0],
        });
        self.instructions = Vec::new();
        for expression in inner_prefix {
            self.statement(expression)?;
        }
        let arguments = argument_ids
            .iter()
            .map(|argument| self.value(*argument))
            .collect::<Option<Vec<_>>>()?;
        entry.extend(std::mem::take(&mut self.instructions));
        entry.push(MirInstruction::Perform {
            dst: result,
            effect: effect.definition,
            effect_arguments: effect.arguments,
            operation,
            arguments,
        });
        entry.push(MirInstruction::UninstallHandler);
        if sibling_payload_destinations.is_some() {
            entry.push(MirInstruction::UninstallHandler);
        }
        entry.push(MirInstruction::UninstallHandler);

        self.instructions = Vec::new();
        let outer_named = self.named.clone();
        self.bind_handler_patterns(&outer_clause.patterns, &outer_payload_destinations)?;
        let outer_resumed = self.direct_handler_clause_value(outer_clause)?;
        self.instructions.push(MirInstruction::Resume {
            value: outer_resumed,
        });
        let outer_instructions = std::mem::take(&mut self.instructions);
        self.named = outer_named;

        let mut bodies = Vec::with_capacity(dispatch.len());
        for (clause, _) in &dispatch {
            self.instructions = Vec::new();
            let named = self.named.clone();
            self.bind_handler_patterns(&clause.patterns, &inner_payload_destinations)?;
            let resumed = self.direct_handler_clause_value(clause)?;
            self.instructions
                .push(MirInstruction::Resume { value: resumed });
            bodies.push(std::mem::take(&mut self.instructions));
            self.named = named;
        }
        let mut sibling_bodies = Vec::with_capacity(sibling_dispatch.len());
        for (clause, _) in &sibling_dispatch {
            self.instructions = Vec::new();
            let named = self.named.clone();
            self.bind_handler_patterns(
                &clause.patterns,
                sibling_payload_destinations
                    .as_ref()
                    .expect("sibling clause payload destinations exist"),
            )?;
            let resumed = self.direct_handler_clause_value(clause)?;
            self.instructions
                .push(MirInstruction::Resume { value: resumed });
            sibling_bodies.push(std::mem::take(&mut self.instructions));
            self.named = named;
        }

        let mut blocks = vec![
            MirBlock {
                parameters: vec![],
                instructions: entry,
                terminator: MirTerminator::Return { value: result },
            },
            MirBlock {
                parameters: vec![],
                instructions: outer_instructions,
                terminator: MirTerminator::Unreachable,
            },
        ];
        let mut test_id = 2u32;
        for (clause_index, (_, tests)) in dispatch.iter().enumerate() {
            let failure_target = clause_targets
                .get(clause_index + 1)
                .copied()
                .unwrap_or(forward_target);
            for (test_index, (condition, subject, pattern)) in tests.iter().cloned().enumerate() {
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions: vec![MirInstruction::PatternTest {
                        dst: condition,
                        subject,
                        pattern,
                    }],
                    terminator: MirTerminator::SwitchBool {
                        condition,
                        then_target: if test_index + 1 == tests.len() {
                            MirBlockId(body_start + clause_index as u32)
                        } else {
                            MirBlockId(test_id + 1)
                        },
                        then_arguments: vec![],
                        else_target: failure_target,
                        else_arguments: vec![],
                    },
                });
                test_id += 1;
            }
        }
        for instructions in bodies {
            blocks.push(MirBlock {
                parameters: vec![],
                instructions,
                terminator: MirTerminator::Unreachable,
            });
        }
        if !has_fallback {
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::Forward],
                terminator: MirTerminator::Unreachable,
            });
        }
        let mut sibling_test_id = sibling_test_start;
        for (clause_index, (_, tests)) in sibling_dispatch.iter().enumerate() {
            let failure_target = sibling_clause_targets
                .get(clause_index + 1)
                .copied()
                .unwrap_or(sibling_forward_target);
            for (test_index, (condition, subject, pattern)) in tests.iter().cloned().enumerate() {
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions: vec![MirInstruction::PatternTest {
                        dst: condition,
                        subject,
                        pattern,
                    }],
                    terminator: MirTerminator::SwitchBool {
                        condition,
                        then_target: if test_index + 1 == tests.len() {
                            MirBlockId(sibling_body_start + clause_index as u32)
                        } else {
                            MirBlockId(sibling_test_id + 1)
                        },
                        then_arguments: vec![],
                        else_target: failure_target,
                        else_arguments: vec![],
                    },
                });
                sibling_test_id += 1;
            }
        }
        for instructions in sibling_bodies {
            blocks.push(MirBlock {
                parameters: vec![],
                instructions,
                terminator: MirTerminator::Unreachable,
            });
        }
        if !sibling_has_fallback && !sibling_dispatch.is_empty() {
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::Forward],
                terminator: MirTerminator::Unreachable,
            });
        }
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }
    /// Lower an arbitrary lexical chain of three or more exact-one-shot
    /// handlers around one direct performance. Each source handler remains a
    /// real VM frame: a refutable arm runs its structural tests and explicitly
    /// forwards the suspended operation to the next outer frame. This covers
    /// deeper forwarding graphs without pretending that the continuation is a
    /// direct value substitution. Lexical setup expressions are retained at
    /// every layer and run immediately after their owning frame installs, so
    /// values they bind remain available to the enclosed frame and direct
    /// performance. Each layer may contain an ordered, refutable sequence of
    /// clauses for that direct operation: failed clauses advance locally and
    /// only the final miss forwards outward. Completion clauses, unrelated
    /// operation groups, and non-linear resumptions deliberately remain on
    /// the more general lowering paths below.
    fn lower_root_runtime_deep_one_shot_handler(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (mut current, root_prefix) = match self.body.expression(root).kind.clone() {
            CoreKind::Handle { .. } => (root, Vec::new()),
            CoreKind::Block(values) => {
                let (handler, prefix) = values.split_last()?;
                matches!(self.body.expression(*handler).kind, CoreKind::Handle { .. })
                    .then_some((*handler, prefix.to_vec()))?
            }
            _ => return None,
        };
        let mut layers = Vec::<Vec<CoreHandlerClause>>::new();
        let mut layer_setups = Vec::<Vec<CoreId>>::new();
        while let CoreKind::Handle {
            computation,
            clauses,
        } = self.body.expression(current).kind.clone()
        {
            // This direct-chain specialization has no completion behavior to
            // preserve. The operation group is checked once the protected
            // direct performance is known below.
            if clauses.is_empty() || clauses.iter().any(|clause| clause.terminal) {
                return None;
            }
            layers.push(clauses);
            current = match self.body.expression(computation).kind.clone() {
                CoreKind::Handle { .. } => {
                    layer_setups.push(Vec::new());
                    computation
                }
                CoreKind::Block(values) => {
                    let (next, setup) = values.split_last()?;
                    layer_setups.push(setup.to_vec());
                    *next
                }
                _ => {
                    layer_setups.push(Vec::new());
                    computation
                }
            };
        }
        if layers.len() < 3 {
            return None;
        }
        let CoreKind::Perform {
            effect,
            operation,
            arguments: argument_ids,
            terminal: false,
        } = self.body.expression(current).kind.clone()
        else {
            return None;
        };
        for clauses in &mut layers {
            if clauses
                .iter()
                .any(|clause| clause.effect != effect || clause.operation != operation)
            {
                return None;
            }
            if let Some(fallback) = clauses
                .iter()
                .position(|clause| clause.patterns.iter().all(pattern_is_irrefutable))
            {
                clauses.truncate(fallback + 1);
            }
            for clause in clauses {
                let quantity = match &clause.resumption {
                    CoreHandlerResumption::Explicit { quantity, .. }
                    | CoreHandlerResumption::Tail { quantity } => *quantity,
                    CoreHandlerResumption::Discard { .. } | CoreHandlerResumption::Terminal => {
                        return None;
                    }
                };
                if quantity != crate::quantity::Quantity::ONCE
                    || clause.patterns.len() != clause.payload_types.len()
                {
                    return None;
                }
            }
        }

        for expression in root_prefix {
            self.statement(expression)?;
        }
        let resume_type = self.body.expression(current).ty.clone();
        let payloads = layers
            .iter()
            .map(|clauses| {
                clauses[0]
                    .payload_types
                    .iter()
                    .map(|ty| self.alloc(ty.clone(), current))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let tests = layers
            .iter()
            .zip(&payloads)
            .map(|(clauses, payloads)| {
                clauses
                    .iter()
                    .map(|clause| {
                        if clause.patterns.iter().all(pattern_is_irrefutable) {
                            return Some(Vec::new());
                        }
                        clause
                            .patterns
                            .iter()
                            .cloned()
                            .zip(payloads.iter().copied())
                            .map(|(pattern, subject)| {
                                Some((
                                    self.alloc(
                                        Type::Scalar(crate::types::ScalarType::Bool),
                                        current,
                                    ),
                                    subject,
                                    lower_pattern(pattern)?,
                                ))
                            })
                            .collect::<Option<Vec<_>>>()
                    })
                    .collect::<Option<Vec<_>>>()
            })
            .collect::<Option<Vec<_>>>()?;

        let body_blocks = layers
            .iter()
            .map(|clauses| vec![MirBlockId(0); clauses.len()])
            .collect::<Vec<_>>();
        let mut next_block = 1u32;
        let mut body_blocks = body_blocks;
        for blocks in &mut body_blocks {
            for block in blocks {
                *block = MirBlockId(next_block);
                next_block += 1;
            }
        }
        let test_blocks = tests
            .iter()
            .map(|clauses| {
                clauses
                    .iter()
                    .map(|tests| {
                        (0..tests.len())
                            .map(|_| {
                                let block = MirBlockId(next_block);
                                next_block += 1;
                                block
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let forward_blocks = tests
            .iter()
            .map(|clauses| {
                clauses
                    .last()
                    .is_some_and(|tests| !tests.is_empty())
                    .then(|| {
                        let block = MirBlockId(next_block);
                        next_block += 1;
                        block
                    })
            })
            .collect::<Vec<_>>();

        let mut entry = std::mem::take(&mut self.instructions);
        for ((((clauses, payloads), tests), bodies), setup) in layers
            .iter()
            .zip(&payloads)
            .zip(&test_blocks)
            .zip(&body_blocks)
            .zip(&layer_setups)
        {
            let clause = &clauses[0];
            entry.push(MirInstruction::InstallHandler {
                effect: clause.effect.definition,
                effect_arguments: clause.effect.arguments.clone(),
                operation: clause.operation,
                payload_destinations: payloads.clone(),
                resume_type: resume_type.clone(),
                continuation: MirContinuationPolicy::Consume,
                target: tests[0].first().copied().unwrap_or(bodies[0]),
            });
            self.instructions = Vec::new();
            for expression in setup {
                self.statement(*expression)?;
            }
            entry.extend(std::mem::take(&mut self.instructions));
        }
        let arguments = argument_ids
            .iter()
            .map(|argument| self.value(*argument))
            .collect::<Option<Vec<_>>>()?;
        entry.extend(std::mem::take(&mut self.instructions));
        let result = self.alloc(resume_type, current);
        entry.push(MirInstruction::Perform {
            dst: result,
            effect: effect.definition,
            effect_arguments: effect.arguments,
            operation,
            arguments,
        });
        for _ in &layers {
            entry.push(MirInstruction::UninstallHandler);
        }

        let base_named = self.named.clone();
        let base_values = self.values.clone();
        let mut bodies = Vec::new();
        for (clauses, payloads) in layers.iter().zip(&payloads) {
            for clause in clauses {
                self.instructions = Vec::new();
                self.named = base_named.clone();
                self.values = base_values.clone();
                self.bind_handler_patterns(&clause.patterns, payloads)?;
                let resumed = self.direct_handler_clause_value(clause)?;
                self.instructions
                    .push(MirInstruction::Resume { value: resumed });
                bodies.push(std::mem::take(&mut self.instructions));
            }
        }
        self.named = base_named;
        self.values = base_values;

        let mut blocks = vec![MirBlock {
            parameters: vec![],
            instructions: entry,
            terminator: MirTerminator::Return { value: result },
        }];
        for instructions in bodies {
            blocks.push(MirBlock {
                parameters: vec![],
                instructions,
                terminator: MirTerminator::Unreachable,
            });
        }
        for (layer_index, (clauses, clause_test_blocks)) in
            tests.into_iter().zip(test_blocks).enumerate()
        {
            for (clause_index, clause_tests) in clauses.into_iter().enumerate() {
                let test_block_ids = &clause_test_blocks[clause_index];
                if clause_tests.is_empty() {
                    continue;
                }
                let failure_target = clause_test_blocks
                    .get(clause_index + 1)
                    .and_then(|tests| tests.first())
                    .copied()
                    .or_else(|| body_blocks[layer_index].get(clause_index + 1).copied())
                    .or(forward_blocks[layer_index])
                    .expect("ordered handler dispatch has a following clause or forward block");
                for (test_index, (condition, subject, pattern)) in
                    clause_tests.into_iter().enumerate()
                {
                    blocks.push(MirBlock {
                        parameters: vec![],
                        instructions: vec![MirInstruction::PatternTest {
                            dst: condition,
                            subject,
                            pattern,
                        }],
                        terminator: MirTerminator::SwitchBool {
                            condition,
                            then_target: test_block_ids
                                .get(test_index + 1)
                                .copied()
                                .unwrap_or(body_blocks[layer_index][clause_index]),
                            then_arguments: vec![],
                            else_target: failure_target,
                            else_arguments: vec![],
                        },
                    });
                }
            }
        }
        for forward in forward_blocks {
            if forward.is_some() {
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions: vec![MirInstruction::Forward],
                    terminator: MirTerminator::Unreachable,
                });
            }
        }
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }
    /// Lower two lexically nested handlers around one direct operation. The
    /// outer arm may be an explicit finite replay while the inner frame is
    /// one-shot. Even when that inner frame does not name the operation, it
    /// must remain on each outer continuation snapshot: every replay restores
    /// it before ordinary scope exit uninstalls it.
    fn lower_root_runtime_nested_one_shot_handler(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (outer_computation, outer_clauses, root_prefix, root_suffix) =
            match self.body.expression(root).kind.clone() {
                CoreKind::Handle {
                    computation,
                    clauses,
                } => (computation, clauses, Vec::new(), Vec::new()),
                CoreKind::Block(values) => {
                    let outer_index = values.iter().position(|value| {
                        matches!(self.body.expression(*value).kind, CoreKind::Handle { .. })
                    })?;
                    let outer = values[outer_index];
                    let CoreKind::Handle {
                        computation,
                        clauses,
                    } = self.body.expression(outer).kind.clone()
                    else {
                        return None;
                    };
                    if values[outer_index + 1..].iter().any(|value| {
                        matches!(self.body.expression(*value).kind, CoreKind::Handle { .. })
                    }) {
                        return None;
                    }
                    (
                        computation,
                        clauses,
                        values[..outer_index].to_vec(),
                        values[outer_index + 1..].to_vec(),
                    )
                }
                _ => return None,
            };
        let inner = match self.body.expression(outer_computation).kind.clone() {
            CoreKind::Handle { .. } => outer_computation,
            CoreKind::Block(values) if values.len() == 1 => values[0],
            _ => return None,
        };
        let CoreKind::Handle {
            computation: inner_computation,
            clauses: inner_clauses,
        } = self.body.expression(inner).kind.clone()
        else {
            return None;
        };
        let CoreKind::Perform {
            effect,
            operation,
            arguments: argument_ids,
            terminal: false,
        } = self.body.expression(inner_computation).kind.clone()
        else {
            return None;
        };
        let outer_operation_clauses = outer_clauses
            .iter()
            .filter(|clause| !clause.terminal)
            .collect::<Vec<_>>();
        let inner_operation_clauses = inner_clauses
            .iter()
            .filter(|clause| !clause.terminal)
            .collect::<Vec<_>>();
        let [outer_clause] = outer_operation_clauses.as_slice() else {
            return None;
        };
        let [inner_clause] = inner_operation_clauses.as_slice() else {
            return None;
        };
        let outer_policy = match &outer_clause.resumption {
            CoreHandlerResumption::Explicit { quantity, .. }
            | CoreHandlerResumption::Tail { quantity }
                if *quantity == crate::quantity::Quantity::ONCE =>
            {
                MirContinuationPolicy::Consume
            }
            CoreHandlerResumption::Explicit { quantity, .. }
                if !quantity.contains(crate::quantity::Quantity::ONCE)
                    && quantity.upper.is_some_and(|upper| upper >= 2) =>
            {
                MirContinuationPolicy::Replay
            }
            _ => return None,
        };
        let inner_is_one_shot = matches!(
            inner_clause.resumption,
            CoreHandlerResumption::Explicit {
                quantity: crate::quantity::Quantity::ONCE,
                ..
            } | CoreHandlerResumption::Tail {
                quantity: crate::quantity::Quantity::ONCE
            }
        );
        if !inner_is_one_shot
            || outer_clause.patterns.len() != argument_ids.len()
            || inner_clause.patterns.len() != argument_ids.len()
        {
            return None;
        }
        if !outer_clause.patterns.iter().all(pattern_is_irrefutable) {
            return None;
        }
        for expression in root_prefix {
            self.statement(expression)?;
        }
        let arguments = argument_ids
            .iter()
            .map(|argument| self.value(*argument))
            .collect::<Option<Vec<_>>>()?;
        let outer_payload_destinations = outer_clause
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), inner_computation))
            .collect::<Vec<_>>();
        let inner_payload_destinations = inner_clause
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), inner_computation))
            .collect::<Vec<_>>();
        // An irrefutable arm enters its body directly. A refutable arm uses
        // the shared structural pattern primitive and explicitly forwards the
        // suspended operation if any predicate fails.
        let inner_tests = if inner_clause.patterns.iter().all(pattern_is_irrefutable) {
            Vec::new()
        } else {
            inner_clause
                .patterns
                .iter()
                .cloned()
                .zip(inner_payload_destinations.iter().copied())
                .map(|(pattern, subject)| {
                    Some((
                        self.alloc(
                            Type::Scalar(crate::types::ScalarType::Bool),
                            inner_computation,
                        ),
                        subject,
                        lower_pattern(pattern)?,
                    ))
                })
                .collect::<Option<Vec<_>>>()?
        };
        let inner_test_count = inner_tests.len();
        let inner_matched_target = MirBlockId(2 + inner_test_count as u32);
        let inner_forward_target = MirBlockId(inner_matched_target.0 + 1);
        let result = self.alloc(
            self.body.expression(inner_computation).ty.clone(),
            inner_computation,
        );
        let mut entry = std::mem::take(&mut self.instructions);
        entry.push(MirInstruction::InstallHandler {
            effect: outer_clause.effect.definition,
            effect_arguments: outer_clause.effect.arguments.clone(),
            operation: outer_clause.operation,
            payload_destinations: outer_payload_destinations.clone(),
            resume_type: self.body.expression(inner_computation).ty.clone(),
            continuation: outer_policy,
            target: MirBlockId(1),
        });
        entry.push(MirInstruction::InstallHandler {
            effect: inner_clause.effect.definition,
            effect_arguments: inner_clause.effect.arguments.clone(),
            operation: inner_clause.operation,
            payload_destinations: inner_payload_destinations.clone(),
            resume_type: self.body.expression(inner_computation).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target: if inner_tests.is_empty() {
                inner_matched_target
            } else {
                MirBlockId(2)
            },
        });
        entry.push(MirInstruction::Perform {
            dst: result,
            effect: effect.definition,
            effect_arguments: effect.arguments,
            operation,
            arguments,
        });
        entry.push(MirInstruction::UninstallHandler);
        entry.push(MirInstruction::UninstallHandler);

        self.instructions = Vec::new();
        let outer_named = self.named.clone();
        self.bind_handler_patterns(&outer_clause.patterns, &outer_payload_destinations)?;
        let outer_resumed = self.direct_handler_clause_value(outer_clause)?;
        if outer_policy == MirContinuationPolicy::Consume {
            self.instructions.push(MirInstruction::Resume {
                value: outer_resumed,
            });
        } else {
            self.instructions.push(MirInstruction::Cancel);
        }
        let outer_instructions = std::mem::take(&mut self.instructions);
        self.named = outer_named;

        self.instructions = Vec::new();
        let inner_named = self.named.clone();
        self.bind_handler_patterns(&inner_clause.patterns, &inner_payload_destinations)?;
        let inner_resumed = self.direct_handler_clause_value(inner_clause)?;
        self.instructions.push(MirInstruction::Resume {
            value: inner_resumed,
        });
        let inner_instructions = std::mem::take(&mut self.instructions);
        self.named = inner_named;

        let final_result = if root_suffix.is_empty() {
            result
        } else {
            self.instructions = Vec::new();
            let (last, statements) = root_suffix.split_last()?;
            for statement in statements {
                self.statement(*statement)?;
            }
            let suffix_result = self.value(*last)?;
            entry.extend(std::mem::take(&mut self.instructions));
            suffix_result
        };

        let mut blocks = vec![
            MirBlock {
                parameters: vec![],
                instructions: entry,
                terminator: MirTerminator::Return {
                    value: final_result,
                },
            },
            MirBlock {
                parameters: vec![],
                instructions: outer_instructions,
                terminator: if outer_policy == MirContinuationPolicy::Replay {
                    MirTerminator::Return {
                        value: outer_resumed,
                    }
                } else {
                    MirTerminator::Unreachable
                },
            },
        ];
        for (index, (condition, subject, pattern)) in inner_tests.into_iter().enumerate() {
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::PatternTest {
                    dst: condition,
                    subject,
                    pattern,
                }],
                terminator: MirTerminator::SwitchBool {
                    condition,
                    then_target: if index + 1 == inner_test_count {
                        inner_matched_target
                    } else {
                        MirBlockId(3 + index as u32)
                    },
                    then_arguments: vec![],
                    else_target: inner_forward_target,
                    else_arguments: vec![],
                },
            });
        }
        blocks.push(MirBlock {
            parameters: vec![],
            instructions: inner_instructions,
            terminator: MirTerminator::Unreachable,
        });
        if inner_test_count != 0 {
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::Forward],
                terminator: MirTerminator::Unreachable,
            });
        }
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }
    /// Specialize a finite multi-shot continuation when replay is completely
    /// represented by cloning a pure residual computation. This is a real
    /// resumption replay, not an alias for the VM's one-shot `Resume`: every
    /// explicit `k(value)` evaluates the residual anew with that value bound
    /// at the suspended performance site. Effects, moves, unique borrows,
    /// mutable storage, and escaping control remain on the dynamic lowering
    /// path until their snapshots and copy glue have a verifier contract.
    fn lower_root_finite_replay_safe_resumption(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (computation, clauses, root_prefix) = match self.body.expression(root).kind.clone() {
            CoreKind::Handle {
                computation,
                clauses,
            } => (computation, clauses, Vec::new()),
            CoreKind::Block(values) => {
                let (handler, prefix) = values.split_last()?;
                let CoreKind::Handle {
                    computation,
                    clauses,
                } = self.body.expression(*handler).kind.clone()
                else {
                    return None;
                };
                (computation, clauses, prefix.to_vec())
            }
            _ => return None,
        };
        let CoreKind::Block(computation_values) = self.body.expression(computation).kind.clone()
        else {
            return None;
        };
        let first_perform = computation_values.iter().position(|candidate| {
            matches!(
                self.body.expression(*candidate).kind,
                CoreKind::Let {
                    value,
                    ..
                } if matches!(
                    self.body.expression(value).kind,
                    CoreKind::Perform { terminal: false, .. }
                )
            )
        })?;
        let (computation_prefix, operation_and_residual) =
            computation_values.split_at(first_perform);
        let (binding, residual) = operation_and_residual.split_first()?;
        let CoreKind::Let { name, value } = self.body.expression(*binding).kind.clone() else {
            return None;
        };
        let CoreKind::Perform {
            effect,
            operation,
            arguments: argument_ids,
            terminal: false,
        } = self.body.expression(value).kind.clone()
        else {
            return None;
        };
        let (residual_result, residual_prefix) = residual.split_last()?;
        if !residual
            .iter()
            .all(|expression| self.core_is_replay_safe(*expression))
        {
            return None;
        }
        let mut matching = clauses
            .iter()
            .filter(|clause| {
                !clause.terminal && clause.effect == effect && clause.operation == operation
            })
            .collect::<Vec<_>>();
        if matching.is_empty() {
            return None;
        }
        let has_fallback = if let Some(index) = matching
            .iter()
            .position(|clause| clause.patterns.iter().all(pattern_is_irrefutable))
        {
            matching.truncate(index + 1);
            true
        } else {
            false
        };
        if matching.iter().any(|clause| {
            let CoreHandlerResumption::Explicit { quantity, .. } = &clause.resumption else {
                return true;
            };
            // This static replayer is reserved for genuinely multi-shot
            // finite continuation contracts. Exact one-shot residuals use
            // the VM handler-frame lowering below.
            quantity.upper.is_none_or(|upper| upper < 2)
                || clause.patterns.len() != argument_ids.len()
        }) {
            return None;
        }
        for expression in root_prefix.iter().chain(computation_prefix.iter()) {
            self.statement(*expression)?;
        }
        let arguments = argument_ids
            .iter()
            .map(|argument| self.value(*argument))
            .collect::<Option<Vec<_>>>()?;
        let entry_instructions = std::mem::take(&mut self.instructions);
        let entry_values = self.values.clone();
        let entry_named = self.named.clone();
        let mut bodies = Vec::with_capacity(matching.len());
        for clause in &matching {
            let CoreHandlerResumption::Explicit {
                name: continuation,
                quantity,
            } = &clause.resumption
            else {
                return None;
            };
            self.instructions = Vec::new();
            self.values = entry_values.clone();
            self.named = entry_named.clone();
            self.bind_handler_patterns(&clause.patterns, &arguments)?;
            // A generated continuation shadows an outer local with the same
            // spelling. Remove the binding during clause lowering so the call
            // recognition in `value` cannot accidentally select the outer
            // local or a payload binder.
            self.named.remove(continuation);
            let previous = self.direct_resumption.replace(DirectResumptionState {
                name: continuation.clone(),
                quantity: *quantity,
                calls: 0,
                plan: DirectResumptionPlan::PureResidual {
                    binding: name.clone(),
                    prefix: residual_prefix.to_vec(),
                    result: *residual_result,
                },
            });
            let result = self.value(clause.body);
            let state = self
                .direct_resumption
                .take()
                .expect("finite resumption state must outlive its clause body");
            self.direct_resumption = previous;
            let result = result?;
            let actual = crate::quantity::Quantity::new(state.calls, Some(state.calls)).ok()?;
            if !state.quantity.contains(actual) {
                self.error(
                    "G6005",
                    "finite resumption calls do not satisfy its declared quantity",
                );
                return Some(self.invalid_function(parameters));
            }
            bodies.push((std::mem::take(&mut self.instructions), result));
        }
        self.values = entry_values;
        self.named = entry_named;

        let mut blocks = vec![MirBlock {
            parameters: vec![],
            instructions: entry_instructions,
            terminator: MirTerminator::Unreachable,
        }];
        let body_ids = bodies
            .into_iter()
            .map(|(instructions, result)| {
                let id = MirBlockId(blocks.len() as u32);
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions,
                    terminator: MirTerminator::Return { value: result },
                });
                id
            })
            .collect::<Vec<_>>();
        let mut next = if has_fallback {
            *body_ids
                .last()
                .expect("finite handler fallback body exists")
        } else {
            let id = MirBlockId(blocks.len() as u32);
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Unreachable,
            });
            id
        };
        let tested = if has_fallback {
            matching.len().saturating_sub(1)
        } else {
            matching.len()
        };
        for index in (0..tested).rev() {
            let mut selected = body_ids[index];
            for (pattern, argument) in matching[index]
                .patterns
                .iter()
                .cloned()
                .zip(arguments.iter().copied())
                .rev()
            {
                let pattern = lower_pattern(pattern)?;
                let condition = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), root);
                let id = MirBlockId(blocks.len() as u32);
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions: vec![MirInstruction::PatternTest {
                        dst: condition,
                        subject: argument,
                        pattern,
                    }],
                    terminator: MirTerminator::SwitchBool {
                        condition,
                        then_target: selected,
                        then_arguments: vec![],
                        else_target: next,
                        else_arguments: vec![],
                    },
                });
                selected = id;
            }
            next = selected;
        }
        blocks[0].terminator = MirTerminator::Goto {
            target: next,
            arguments: vec![],
        };
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }
    /// Lower a resumptive handler used as a statement in an enclosing block.
    ///
    /// The earlier root-only paths deliberately assumed that a handler was the
    /// final expression. That assumption is unsound for lexical binders: a
    /// continuation alias captured in the arm must close over the environment
    /// at the handler boundary, not over a same-spelled local introduced by a
    /// later statement.  This CFG keeps the protected `Perform`, its handler
    /// entry, and the following block suffix in separate control regions.
    ///
    /// It is the first general statement-scope frame path. More elaborate
    /// pattern matrices and multi-shot replay remain owned by their dedicated
    /// lowering paths; this one only claims the complete, exact-one-shot,
    /// irrefutable operation shape that the VM frame instruction represents.
    fn lower_root_statement_one_shot_handler(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let CoreKind::Block(values) = self.body.expression(root).kind.clone() else {
            return None;
        };
        let handler_index = values.iter().position(|value| {
            matches!(self.body.expression(*value).kind, CoreKind::Handle { .. })
        })?;
        if handler_index + 1 >= values.len()
            || values[handler_index + 1..]
                .iter()
                .any(|value| matches!(self.body.expression(*value).kind, CoreKind::Handle { .. }))
        {
            return None;
        }
        let handler = values[handler_index];
        let CoreKind::Handle {
            computation,
            clauses,
        } = self.body.expression(handler).kind.clone()
        else {
            return None;
        };
        let (computation_prefix, perform, resumed_binding, residual) =
            match self.body.expression(computation).kind.clone() {
                CoreKind::Perform {
                    terminal: false, ..
                } => (Vec::new(), computation, None, Vec::new()),
                CoreKind::Block(computation_values) => {
                    let position = computation_values.iter().position(|candidate| {
                        matches!(
                            self.body.expression(*candidate).kind,
                            CoreKind::Let {
                                value,
                                ..
                            } if matches!(
                                self.body.expression(value).kind,
                                CoreKind::Perform { terminal: false, .. }
                            )
                        )
                    })?;
                    let CoreKind::Let { name, value } = self
                        .body
                        .expression(computation_values[position])
                        .kind
                        .clone()
                    else {
                        unreachable!("the performance probe only selects let bindings");
                    };
                    (
                        computation_values[..position].to_vec(),
                        value,
                        Some(name),
                        computation_values[position + 1..].to_vec(),
                    )
                }
                _ => return None,
            };
        let CoreKind::Perform {
            effect,
            operation,
            arguments: argument_ids,
            terminal: false,
        } = self.body.expression(perform).kind.clone()
        else {
            return None;
        };
        let matching = clauses
            .iter()
            .filter(|clause| {
                !clause.terminal && clause.effect == effect && clause.operation == operation
            })
            .collect::<Vec<_>>();
        let [clause] = matching.as_slice() else {
            return None;
        };
        let exact_one_shot = matches!(
            clause.resumption,
            CoreHandlerResumption::Explicit {
                quantity: crate::quantity::Quantity {
                    lower: 1,
                    upper: Some(1)
                },
                ..
            } | CoreHandlerResumption::Tail {
                quantity: crate::quantity::Quantity {
                    lower: 1,
                    upper: Some(1)
                },
            }
        );
        if !exact_one_shot
            || clause.patterns.len() != argument_ids.len()
            || !clause.patterns.iter().all(pattern_is_irrefutable)
        {
            return None;
        }

        for expression in &values[..handler_index] {
            self.statement(*expression)?;
        }
        let payload_destinations = clause
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), perform))
            .collect::<Vec<_>>();
        let resumed = self.alloc(self.body.expression(perform).ty.clone(), perform);
        let mut entry = std::mem::take(&mut self.instructions);
        entry.push(MirInstruction::InstallHandler {
            effect: effect.definition,
            effect_arguments: effect.arguments.clone(),
            operation,
            payload_destinations: payload_destinations.clone(),
            resume_type: self.body.expression(perform).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target: MirBlockId(1),
        });
        self.instructions = Vec::new();
        for expression in &computation_prefix {
            self.statement(*expression)?;
        }
        let arguments = argument_ids
            .iter()
            .map(|argument| self.value(*argument))
            .collect::<Option<Vec<_>>>()?;
        entry.extend(std::mem::take(&mut self.instructions));
        entry.push(MirInstruction::Perform {
            dst: resumed,
            effect: effect.definition,
            effect_arguments: effect.arguments,
            operation,
            arguments,
        });

        // Preserve the exact lexical environment at the handler boundary for
        // its arm. The suffix is intentionally lowered only after that
        // snapshot, so a later `let saved = ...` cannot change which Core
        // resumption identity the arm's `saved` denotes.
        let boundary_named = self.named.clone();
        let boundary_values = self.values.clone();
        self.instructions = Vec::new();
        if let Some(binding) = resumed_binding {
            self.named.insert(binding, resumed);
        }
        if let Some((last, statements)) = residual.split_last() {
            for statement in statements {
                self.statement(*statement)?;
            }
            // A statement handler discards the protected computation's final
            // value, but its residual still has to execute before the frame
            // can leave scope.
            let _ = self.value(*last)?;
        }
        self.instructions.push(MirInstruction::UninstallHandler);
        let (last, statements) = values[handler_index + 1..].split_last()?;
        for statement in statements {
            self.statement(*statement)?;
        }
        let result = self.value(*last)?;
        entry.extend(std::mem::take(&mut self.instructions));

        self.instructions = Vec::new();
        self.named = boundary_named;
        self.values = boundary_values;
        self.bind_handler_patterns(&clause.patterns, &payload_destinations)?;
        let handler_value = self.direct_handler_clause_value(clause)?;
        self.instructions.push(MirInstruction::Resume {
            value: handler_value,
        });
        let handler_instructions = std::mem::take(&mut self.instructions);

        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks: vec![
                MirBlock {
                    parameters: vec![],
                    instructions: entry,
                    terminator: MirTerminator::Return { value: result },
                },
                MirBlock {
                    parameters: vec![],
                    instructions: handler_instructions,
                    terminator: MirTerminator::Unreachable,
                },
            ],
        })
    }
    /// Runtime ordered dispatch for a direct one-shot handler used before a
    /// later enclosing-block suffix. Unlike the compact single-arm path this
    /// keeps every refutable clause as a real CFG edge and emits `Forward`
    /// only after the final miss.
    fn lower_root_statement_ordered_one_shot_handler(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let CoreKind::Block(values) = self.body.expression(root).kind.clone() else {
            return None;
        };
        let handler_index = values
            .iter()
            .position(|id| matches!(self.body.expression(*id).kind, CoreKind::Handle { .. }))?;
        if handler_index + 1 >= values.len() {
            return None;
        }
        let CoreKind::Handle {
            computation,
            clauses,
        } = self.body.expression(values[handler_index]).kind.clone()
        else {
            return None;
        };
        let CoreKind::Perform {
            effect,
            operation,
            arguments,
            terminal: false,
        } = self.body.expression(computation).kind.clone()
        else {
            return None;
        };
        let mut matching = clauses
            .iter()
            .filter(|clause| {
                !clause.terminal && clause.effect == effect && clause.operation == operation
            })
            .collect::<Vec<_>>();
        if matching.len() < 2 {
            return None;
        }
        let fallback = matching
            .iter()
            .position(|clause| clause.patterns.iter().all(pattern_is_irrefutable));
        if let Some(index) = fallback {
            matching.truncate(index + 1);
        }
        if matching.iter().any(|clause| {
            clause.patterns.len() != arguments.len()
                || !matches!(clause.resumption,
                    CoreHandlerResumption::Explicit { quantity, .. } | CoreHandlerResumption::Tail { quantity }
                    if quantity == crate::quantity::Quantity::ONCE)
        }) { return None; }
        for expression in &values[..handler_index] {
            self.statement(*expression)?;
        }
        let payloads = matching[0]
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), computation))
            .collect::<Vec<_>>();
        let resumed = self.alloc(self.body.expression(computation).ty.clone(), computation);
        let body_blocks = (0..matching.len())
            .map(|index| MirBlockId(1 + index as u32))
            .collect::<Vec<_>>();
        let mut next = 1 + matching.len() as u32;
        let test_blocks = matching
            .iter()
            .map(|clause| {
                (0..if clause.patterns.iter().all(pattern_is_irrefutable) {
                    0
                } else {
                    clause.patterns.len()
                })
                    .map(|_| {
                        let id = MirBlockId(next);
                        next += 1;
                        id
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let forward_block = fallback.is_none().then_some(MirBlockId(next));
        let target = test_blocks[0].first().copied().unwrap_or(body_blocks[0]);
        let arguments = arguments
            .iter()
            .map(|id| self.value(*id))
            .collect::<Option<Vec<_>>>()?;
        let mut entry = std::mem::take(&mut self.instructions);
        entry.push(MirInstruction::InstallHandler {
            effect: effect.definition,
            effect_arguments: effect.arguments.clone(),
            operation,
            payload_destinations: payloads.clone(),
            resume_type: self.body.expression(computation).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target,
        });
        entry.push(MirInstruction::Perform {
            dst: resumed,
            effect: effect.definition,
            effect_arguments: effect.arguments,
            operation,
            arguments,
        });
        entry.push(MirInstruction::UninstallHandler);
        let boundary_named = self.named.clone();
        let boundary_values = self.values.clone();
        self.instructions = Vec::new();
        let (last, suffix) = values[handler_index + 1..].split_last()?;
        for statement in suffix {
            self.statement(*statement)?;
        }
        let result = self.value(*last)?;
        entry.extend(std::mem::take(&mut self.instructions));
        let mut bodies = Vec::new();
        for clause in &matching {
            self.instructions = Vec::new();
            self.named = boundary_named.clone();
            self.values = boundary_values.clone();
            self.bind_handler_patterns(&clause.patterns, &payloads)?;
            let value = self.direct_handler_clause_value(clause)?;
            self.instructions.push(MirInstruction::Resume { value });
            bodies.push(std::mem::take(&mut self.instructions));
        }
        let mut tests = Vec::new();
        for (clause, ids) in matching.iter().zip(&test_blocks) {
            let values = clause
                .patterns
                .iter()
                .cloned()
                .zip(payloads.iter().copied())
                .zip(ids.iter().copied())
                .map(|((pattern, subject), id)| {
                    Some((
                        id,
                        self.alloc(Type::Scalar(crate::types::ScalarType::Bool), root),
                        subject,
                        lower_pattern(pattern)?,
                    ))
                })
                .collect::<Option<Vec<_>>>()?;
            tests.push(values);
        }
        let mut blocks = vec![MirBlock {
            parameters: vec![],
            instructions: entry,
            terminator: MirTerminator::Return { value: result },
        }];
        blocks.extend(bodies.into_iter().map(|instructions| MirBlock {
            parameters: vec![],
            instructions,
            terminator: MirTerminator::Unreachable,
        }));
        for (index, values) in tests.into_iter().enumerate() {
            for (test_index, (id, condition, subject, pattern)) in values.into_iter().enumerate() {
                let failure = test_blocks[index]
                    .get(test_index + 1)
                    .copied()
                    .or_else(|| {
                        test_blocks
                            .get(index + 1)
                            .and_then(|ids| ids.first())
                            .copied()
                    })
                    .or_else(|| body_blocks.get(index + 1).copied())
                    .or(forward_block)
                    .expect("partial dispatch has a following clause or forwarding edge");
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions: vec![MirInstruction::PatternTest {
                        dst: condition,
                        subject,
                        pattern,
                    }],
                    terminator: MirTerminator::SwitchBool {
                        condition,
                        then_target: test_blocks[index]
                            .get(test_index + 1)
                            .copied()
                            .unwrap_or(body_blocks[index]),
                        then_arguments: vec![],
                        else_target: failure,
                        else_arguments: vec![],
                    },
                });
                debug_assert_eq!(id.0, blocks.len() as u32 - 1);
            }
        }
        if forward_block.is_some() {
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::Forward],
                terminator: MirTerminator::Unreachable,
            });
        }
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }
    /// A discarded affine continuation is a real control transfer, not an
    /// erased `Perform`. The handler target consumes its suspended frame with
    /// `Cancel` and then joins the enclosing suffix explicitly.
    fn lower_root_statement_cancellation_handler(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let CoreKind::Block(values) = self.body.expression(root).kind.clone() else {
            return None;
        };
        let handler_index = values
            .iter()
            .position(|id| matches!(self.body.expression(*id).kind, CoreKind::Handle { .. }))?;
        if handler_index + 1 >= values.len() {
            return None;
        }
        let CoreKind::Handle {
            computation: outer_computation,
            clauses: outer_clauses,
        } = self.body.expression(values[handler_index]).kind.clone()
        else {
            return None;
        };
        // The innermost direct operation is statically selected by the
        // irrefutable discarded arm below. Its cancellation body and payload
        // evaluation must be effect-free before outer operation frames can be
        // erased; otherwise an enclosing handler could be observable.
        let mut computation = outer_computation;
        let mut clauses = outer_clauses;
        let mut nested = false;
        loop {
            match self.body.expression(computation).kind.clone() {
                CoreKind::Handle {
                    computation: inner_computation,
                    clauses: inner_clauses,
                } => {
                    nested = true;
                    computation = inner_computation;
                    clauses = inner_clauses;
                }
                // Braced handler computations elaborate to a block even when
                // they contain exactly one nested handler. There is no setup
                // work to preserve in this case, so keep following the
                // syntactic wrapper to the protected direct performance.
                CoreKind::Block(values) if values.len() == 1 => {
                    computation = values[0];
                }
                _ => break,
            }
        }
        let CoreKind::Perform {
            effect,
            operation,
            arguments,
            terminal: false,
        } = self.body.expression(computation).kind.clone()
        else {
            return None;
        };
        let matching = clauses
            .iter()
            .filter(|clause| {
                !clause.terminal && clause.effect == effect && clause.operation == operation
            })
            .collect::<Vec<_>>();
        let [clause] = matching.as_slice() else {
            return None;
        };
        let CoreHandlerResumption::Discard { quantity } = clause.resumption else {
            return None;
        };
        if quantity.requires_positive_use()
            || !clause.patterns.iter().all(pattern_is_irrefutable)
            || clause.patterns.len() != arguments.len()
            || (nested
                && (!self.core_is_effect_free(clause.body)
                    || arguments
                        .iter()
                        .any(|argument| !self.core_is_effect_free(*argument))))
        {
            return None;
        }
        for expression in &values[..handler_index] {
            self.statement(*expression)?;
        }
        let payloads = clause
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), computation))
            .collect::<Vec<_>>();
        let performed = self.alloc(self.body.expression(computation).ty.clone(), computation);
        let arguments = arguments
            .iter()
            .map(|id| self.value(*id))
            .collect::<Option<Vec<_>>>()?;
        let mut entry = std::mem::take(&mut self.instructions);
        entry.push(MirInstruction::InstallHandler {
            effect: effect.definition,
            effect_arguments: effect.arguments.clone(),
            operation,
            payload_destinations: payloads.clone(),
            resume_type: self.body.expression(computation).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target: MirBlockId(2),
        });
        entry.push(MirInstruction::Perform {
            dst: performed,
            effect: effect.definition,
            effect_arguments: effect.arguments,
            operation,
            arguments,
        });
        entry.push(MirInstruction::UninstallHandler);
        let boundary_named = self.named.clone();
        let boundary_values = self.values.clone();
        self.instructions = Vec::new();
        let (last, suffix) = values[handler_index + 1..].split_last()?;
        for statement in suffix {
            self.statement(*statement)?;
        }
        let result = self.value(*last)?;
        let suffix_instructions = std::mem::take(&mut self.instructions);
        self.instructions = Vec::new();
        self.named = boundary_named;
        self.values = boundary_values;
        self.bind_handler_patterns(&clause.patterns, &payloads)?;
        let _ = self.value(clause.body)?;
        self.instructions.push(MirInstruction::Cancel);
        let handler_instructions = std::mem::take(&mut self.instructions);
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks: vec![
                MirBlock {
                    parameters: vec![],
                    instructions: entry,
                    terminator: MirTerminator::Goto {
                        target: MirBlockId(1),
                        arguments: vec![],
                    },
                },
                MirBlock {
                    parameters: vec![],
                    instructions: suffix_instructions,
                    terminator: MirTerminator::Return { value: result },
                },
                MirBlock {
                    parameters: vec![],
                    instructions: handler_instructions,
                    terminator: MirTerminator::Goto {
                        target: MirBlockId(1),
                        arguments: vec![],
                    },
                },
            ],
        })
    }
    /// Lower one nonempty, exact-one-shot continuation through the VM handler
    /// frame representation. The continuation begins immediately after the
    /// suspended `Perform`, so its `UninstallHandler` executes only after a
    /// resume restores the captured result local.
    fn lower_root_runtime_one_shot_resumption(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (computation, clauses, root_prefix) = match self.body.expression(root).kind.clone() {
            CoreKind::Handle {
                computation,
                clauses,
            } => (computation, clauses, Vec::new()),
            CoreKind::Block(values) => {
                let (handler, prefix) = values.split_last()?;
                let CoreKind::Handle {
                    computation,
                    clauses,
                } = self.body.expression(*handler).kind.clone()
                else {
                    return None;
                };
                (computation, clauses, prefix.to_vec())
            }
            _ => return None,
        };
        let CoreKind::Block(computation_values) = self.body.expression(computation).kind.clone()
        else {
            return None;
        };
        let first_perform = computation_values.iter().position(|candidate| {
            matches!(
                self.body.expression(*candidate).kind,
                CoreKind::Let {
                    value,
                    ..
                } if matches!(
                    self.body.expression(value).kind,
                    CoreKind::Perform { terminal: false, .. }
                )
            )
        })?;
        let (prefix, operation_and_residual) = computation_values.split_at(first_perform);
        let (binding, residual) = operation_and_residual.split_first()?;
        let CoreKind::Let { name, value } = self.body.expression(*binding).kind.clone() else {
            return None;
        };
        let CoreKind::Perform {
            effect,
            operation,
            arguments: argument_ids,
            terminal: false,
        } = self.body.expression(value).kind.clone()
        else {
            return None;
        };
        if residual.is_empty() {
            return None;
        }
        let matching = clauses
            .iter()
            .filter(|clause| {
                !clause.terminal && clause.effect == effect && clause.operation == operation
            })
            .collect::<Vec<_>>();
        let [clause] = matching.as_slice() else {
            return None;
        };
        let (cancellation, replay) = match &clause.resumption {
            CoreHandlerResumption::Explicit { quantity, .. }
            | CoreHandlerResumption::Tail { quantity } => {
                if *quantity == crate::quantity::Quantity::ONCE {
                    (false, false)
                } else if matches!(clause.resumption, CoreHandlerResumption::Explicit { .. })
                    && quantity.upper.is_some_and(|upper| upper >= 2)
                {
                    (false, true)
                } else {
                    return None;
                }
            }
            CoreHandlerResumption::Discard { quantity } => {
                if quantity.requires_positive_use() {
                    return None;
                }
                (true, false)
            }
            CoreHandlerResumption::Terminal => return None,
        };
        if clause.patterns.len() != argument_ids.len()
            || !clause.patterns.iter().all(pattern_is_irrefutable)
        {
            return None;
        }
        for expression in root_prefix.iter().chain(prefix.iter()) {
            self.statement(*expression)?;
        }
        let arguments = argument_ids
            .iter()
            .map(|argument| self.value(*argument))
            .collect::<Option<Vec<_>>>()?;
        let payload_destinations = argument_ids
            .iter()
            .map(|argument| self.alloc(self.body.expression(*argument).ty.clone(), *argument))
            .collect::<Vec<_>>();
        let performed = self.alloc(self.body.expression(value).ty.clone(), value);
        let mut entry = std::mem::take(&mut self.instructions);
        entry.push(MirInstruction::InstallHandler {
            effect: effect.definition,
            effect_arguments: effect.arguments.clone(),
            operation,
            payload_destinations: payload_destinations.clone(),
            resume_type: self.body.expression(value).ty.clone(),
            continuation: if replay {
                MirContinuationPolicy::Replay
            } else {
                MirContinuationPolicy::Consume
            },
            target: MirBlockId(2),
        });
        entry.push(MirInstruction::Perform {
            dst: performed,
            effect: effect.definition,
            effect_arguments: effect.arguments,
            operation,
            arguments,
        });
        entry.push(MirInstruction::UninstallHandler);

        let continuation_named = self.named.clone();
        self.named.insert(name, performed);
        self.instructions = Vec::new();
        let (last, continuation_prefix) = residual.split_last()?;
        for expression in continuation_prefix {
            self.statement(*expression)?;
        }
        let continuation_result = self.value(*last)?;
        let continuation_instructions = std::mem::take(&mut self.instructions);
        self.named = continuation_named;

        self.instructions = Vec::new();
        let handler_named = self.named.clone();
        self.bind_handler_patterns(&clause.patterns, &payload_destinations)?;
        let handler_result = self.direct_handler_clause_value(clause)?;
        self.instructions.push(if cancellation || replay {
            MirInstruction::Cancel
        } else {
            MirInstruction::Resume {
                value: handler_result,
            }
        });
        let handler_instructions = std::mem::take(&mut self.instructions);
        self.named = handler_named;

        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks: vec![
                MirBlock {
                    parameters: vec![],
                    instructions: entry,
                    terminator: MirTerminator::Goto {
                        target: MirBlockId(1),
                        arguments: vec![],
                    },
                },
                MirBlock {
                    parameters: vec![],
                    instructions: continuation_instructions,
                    terminator: MirTerminator::Return {
                        value: continuation_result,
                    },
                },
                MirBlock {
                    parameters: vec![],
                    instructions: handler_instructions,
                    terminator: if cancellation || replay {
                        MirTerminator::Return {
                            value: handler_result,
                        }
                    } else {
                        MirTerminator::Unreachable
                    },
                },
            ],
        })
    }
    /// A first non-empty delimited continuation: an operation result is bound
    /// by `let`, then enters the residual computation solely as a typed MIR
    /// block parameter. The handler arm resumes by taking the continuation
    /// edge with its produced value.
    fn lower_root_let_resumption(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let CoreKind::Block(root_values) = self.body.expression(root).kind.clone() else {
            return None;
        };
        let (handler, root_prefix) = root_values.split_last()?;
        let CoreKind::Handle {
            computation,
            clauses,
        } = self.body.expression(*handler).kind.clone()
        else {
            return None;
        };
        for expression in root_prefix {
            self.statement(*expression)?;
        }
        let CoreKind::Block(computation_values) = self.body.expression(computation).kind.clone()
        else {
            return None;
        };
        let first_perform = computation_values.iter().position(|candidate| {
            matches!(
                self.body.expression(*candidate).kind,
                CoreKind::Let {
                    value,
                    ..
                } if matches!(
                    self.body.expression(value).kind,
                    CoreKind::Perform { terminal: false, .. }
                )
            )
        })?;
        let (prefix, operation_and_residual) = computation_values.split_at(first_perform);
        let (binding, residual) = operation_and_residual.split_first()?;
        let CoreKind::Let { name, value } = self.body.expression(*binding).kind.clone() else {
            return None;
        };
        let CoreKind::Perform {
            effect,
            operation,
            arguments,
            terminal: false,
        } = self.body.expression(value).kind.clone()
        else {
            return None;
        };
        if residual.is_empty() {
            return None;
        }
        // This is still a static direct-dispatch lowering, but ordinary setup
        // may precede its first intercepted operation.  Lower it in the entry
        // so operation arguments observe the same lexical environment as the
        // source computation.
        for expression in prefix {
            self.statement(*expression)?;
        }
        let arguments = arguments
            .into_iter()
            .map(|argument| self.value(argument))
            .collect::<Option<Vec<_>>>()?;
        // A direct operation still needs the handler's ordinary first-match
        // semantics.  Keep only the operation's arms, stopping at the first
        // irrefutable arm: later rows cannot be selected and must not be
        // lowered into reachable CFG.
        let mut matching = clauses
            .into_iter()
            .filter(|clause| {
                !clause.terminal && clause.effect == effect && clause.operation == operation
            })
            .collect::<Vec<_>>();
        let has_fallback = if let Some(fallback_index) = matching
            .iter()
            .position(|clause| clause.patterns.iter().all(pattern_is_irrefutable))
        {
            matching.truncate(fallback_index + 1);
            true
        } else {
            false
        };
        if matching.iter().any(|clause| {
            clause.patterns.len() != arguments.len()
                || !matches!(
                    clause.resumption,
                    CoreHandlerResumption::Tail { .. }
                        | CoreHandlerResumption::Explicit { .. }
                        | CoreHandlerResumption::Discard { .. }
                )
        }) {
            return None;
        }

        let continuation_parameter = self.alloc(self.body.expression(value).ty.clone(), value);
        let entry_instructions = std::mem::take(&mut self.instructions);
        let before_continuation = self.named.clone();
        self.named.insert(name, continuation_parameter);
        self.instructions = vec![];
        let (last, prefix) = residual.split_last()?;
        for expression in prefix {
            self.statement(*expression)?;
        }
        let continuation_result = self.value(*last)?;
        let continuation_instructions = std::mem::take(&mut self.instructions);
        self.named = before_continuation;

        let mut blocks = vec![
            MirBlock {
                parameters: vec![],
                instructions: entry_instructions,
                terminator: MirTerminator::Unreachable,
            },
            MirBlock {
                parameters: vec![continuation_parameter],
                instructions: continuation_instructions,
                terminator: MirTerminator::Return {
                    value: continuation_result,
                },
            },
        ];
        let mut bodies = Vec::with_capacity(matching.len());
        for clause in &matching {
            self.instructions = vec![];
            let before_clause = self.named.clone();
            self.bind_handler_patterns(&clause.patterns, &arguments)?;
            let Some(resumed) = self.direct_handler_clause_value(clause) else {
                self.named = before_clause;
                return Some(self.invalid_function(parameters));
            };
            let clause_instructions = std::mem::take(&mut self.instructions);
            self.named = before_clause;
            let id = MirBlockId(blocks.len() as u32);
            let terminator = if matches!(clause.resumption, CoreHandlerResumption::Discard { .. }) {
                MirTerminator::Return { value: resumed }
            } else {
                MirTerminator::Goto {
                    target: MirBlockId(1),
                    arguments: vec![resumed],
                }
            };
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: clause_instructions,
                terminator,
            });
            bodies.push(id);
        }
        let mut next = if has_fallback {
            *bodies.last().expect("nonempty handler fallback exists")
        } else {
            let id = MirBlockId(blocks.len() as u32);
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Unreachable,
            });
            id
        };
        let tested = if has_fallback {
            matching.len().saturating_sub(1)
        } else {
            matching.len()
        };
        for index in (0..tested).rev() {
            let mut selected_arm = bodies[index];
            for (pattern, argument) in matching[index]
                .patterns
                .iter()
                .cloned()
                .zip(arguments.iter().copied())
                .rev()
            {
                let Some(pattern) = lower_pattern(pattern) else {
                    self.error(
                        "G6005",
                        "resumptive handler contains an invalid structural pattern",
                    );
                    return Some(self.invalid_function(parameters));
                };
                let condition = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), root);
                // Tests are evaluated in the entry block, before control
                // forks.  This keeps each branch's initialized-local state
                // identical while preserving source-order pattern selection.
                blocks[0].instructions.push(MirInstruction::PatternTest {
                    dst: condition,
                    subject: argument,
                    pattern,
                });
                let id = MirBlockId(blocks.len() as u32);
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions: vec![],
                    terminator: MirTerminator::SwitchBool {
                        condition,
                        then_target: selected_arm,
                        then_arguments: vec![],
                        else_target: next,
                        else_arguments: vec![],
                    },
                });
                selected_arm = id;
            }
            next = selected_arm;
        }
        blocks[0].terminator = MirTerminator::Goto {
            target: next,
            arguments: vec![],
        };
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }
    /// Lower a closed, effectful ordinary call through lexical VM frames.
    ///
    /// The callee's frozen callable effect row is the interprocedural summary
    /// used here. It authorizes only exact, closed protocol instances; open
    /// tails and delayed projections deliberately remain unsupported rather
    /// than being guessed from a callee body. This keeps calls, functions,
    /// Lower an ordered, possibly partial, one-shot handler around an
    /// ordinary call with a closed single-operation effect summary.
    ///
    /// The tests are real VM CFG blocks, so a failed refutable clause leaves
    /// the suspended performance intact for the next source clause. When the
    /// matrix is partial, the final failure explicitly `Forward`s the same
    /// suspended performance to the caller's enclosing dynamic frame. This
    /// deliberately accepts only the matrix shape the VM can represent
    /// without reordering source clauses or replaying a continuation.
    fn lower_root_interprocedural_ordered_one_shot_handler(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (computation, clauses, root_prefix) = match self.body.expression(root).kind.clone() {
            CoreKind::Handle {
                computation,
                clauses,
            } => (computation, clauses, Vec::new()),
            CoreKind::Block(values) => {
                let (handler, prefix) = values.split_last()?;
                let CoreKind::Handle {
                    computation,
                    clauses,
                } = self.body.expression(*handler).kind.clone()
                else {
                    return None;
                };
                (computation, clauses, prefix.to_vec())
            }
            _ => return None,
        };
        let CoreKind::Call { callee, arguments } = self.body.expression(computation).kind.clone()
        else {
            return None;
        };
        let Type::Callable { effects, .. } = self.body.expression(callee).ty.clone() else {
            return None;
        };
        // This is a single operation pattern matrix. A row with another
        // operation needs sibling-frame dispatch, and an open/projected row
        // cannot be soundly approximated at this boundary.
        if effects.effects.len() != 1 {
            return None;
        }
        let effect = effects
            .effects
            .iter()
            .next()
            .expect("single-element effect row has one effect");
        if effects.tail.is_some() || !effects.projections.is_empty() {
            return None;
        }
        let matching = clauses
            .iter()
            .filter(|clause| !clause.terminal && clause.effect == *effect)
            .collect::<Vec<_>>();
        if matching.is_empty()
            || matching
                .iter()
                .any(|clause| clause.operation != matching[0].operation)
            || clauses.len() != matching.len()
        {
            return None;
        }
        let fallback = matching
            .iter()
            .position(|clause| clause.patterns.iter().all(pattern_is_irrefutable));
        if let Some(index) = fallback {
            // Clauses after an irrefutable arm are unreachable; leaving this
            // form to the source-level matrix diagnostics preserves their
            // ordering rather than silently discarding them here.
            if index + 1 != matching.len() {
                return None;
            }
        }
        if matching.iter().any(|clause| {
            clause.patterns.len() != clause.payload_types.len()
                || !matches!(
                    clause.resumption,
                    CoreHandlerResumption::Tail {
                        quantity: crate::quantity::Quantity::ONCE
                    } | CoreHandlerResumption::Explicit {
                        quantity: crate::quantity::Quantity::ONCE,
                        ..
                    }
                )
                || self.handler_body_uses_snapshot_alias(clause.body)
        }) {
            return None;
        }
        for expression in root_prefix {
            self.statement(expression)?;
        }
        let arguments = arguments
            .into_iter()
            .map(|argument| self.value(argument))
            .collect::<Option<Vec<_>>>()?;
        let callee_kind = self.body.expression(callee).kind.clone();
        let indirect = match callee_kind {
            CoreKind::Function { .. } | CoreKind::TraitMethod { .. } => None,
            _ => Some(self.value(callee)?),
        };
        let result = self.alloc(self.body.expression(computation).ty.clone(), computation);
        let payloads = matching[0]
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), computation))
            .collect::<Vec<_>>();
        let body_blocks = (0..matching.len())
            .map(|index| MirBlockId(1 + index as u32))
            .collect::<Vec<_>>();
        let mut next = 1 + matching.len() as u32;
        let test_blocks = matching
            .iter()
            .map(|clause| {
                (0..if clause.patterns.iter().all(pattern_is_irrefutable) {
                    0
                } else {
                    clause.patterns.len()
                })
                    .map(|_| {
                        let id = MirBlockId(next);
                        next += 1;
                        id
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let forward_block = fallback.is_none().then_some(MirBlockId(next));
        let target = test_blocks[0].first().copied().unwrap_or(body_blocks[0]);
        let mut entry = std::mem::take(&mut self.instructions);
        entry.push(MirInstruction::InstallHandler {
            effect: effect.definition,
            effect_arguments: effect.arguments.clone(),
            operation: matching[0].operation,
            payload_destinations: payloads.clone(),
            resume_type: self.body.expression(computation).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target,
        });
        match callee_kind {
            CoreKind::Function {
                definition: callee,
                arguments: generic_arguments,
            } => entry.push(MirInstruction::Call {
                dst: result,
                callee,
                generic_arguments,
                trait_instance: None,
                arguments,
            }),
            CoreKind::TraitMethod {
                evidence,
                method: callee,
                trait_arguments,
                method_arguments,
            } => entry.push(MirInstruction::Call {
                dst: result,
                callee,
                generic_arguments: vec![],
                trait_instance: Some(MirTraitMethodInstance {
                    evidence,
                    trait_arguments,
                    method_arguments,
                }),
                arguments,
            }),
            _ => entry.push(MirInstruction::CallIndirect {
                dst: result,
                callee: indirect.expect("indirect callee was materialized"),
                arguments,
            }),
        }
        entry.push(MirInstruction::UninstallHandler);
        let boundary_named = self.named.clone();
        let boundary_values = self.values.clone();
        let mut bodies = Vec::new();
        for clause in &matching {
            self.instructions = Vec::new();
            self.named = boundary_named.clone();
            self.values = boundary_values.clone();
            self.bind_handler_patterns(&clause.patterns, &payloads)?;
            let value = self.direct_handler_clause_value(clause)?;
            self.instructions.push(MirInstruction::Resume { value });
            bodies.push(std::mem::take(&mut self.instructions));
        }
        self.named = boundary_named;
        self.values = boundary_values;
        let mut tests = Vec::new();
        for (clause, ids) in matching.iter().zip(&test_blocks) {
            let values = clause
                .patterns
                .iter()
                .cloned()
                .zip(payloads.iter().copied())
                .zip(ids.iter().copied())
                .map(|((pattern, subject), id)| {
                    Some((
                        id,
                        self.alloc(Type::Scalar(crate::types::ScalarType::Bool), root),
                        subject,
                        lower_pattern(pattern)?,
                    ))
                })
                .collect::<Option<Vec<_>>>()?;
            tests.push(values);
        }
        let mut blocks = vec![MirBlock {
            parameters: vec![],
            instructions: entry,
            terminator: MirTerminator::Return { value: result },
        }];
        blocks.extend(bodies.into_iter().map(|instructions| MirBlock {
            parameters: vec![],
            instructions,
            terminator: MirTerminator::Unreachable,
        }));
        for (index, values) in tests.into_iter().enumerate() {
            for (test_index, (id, condition, subject, pattern)) in values.into_iter().enumerate() {
                let failure = test_blocks[index]
                    .get(test_index + 1)
                    .copied()
                    .or_else(|| {
                        test_blocks
                            .get(index + 1)
                            .and_then(|ids| ids.first())
                            .copied()
                    })
                    .or_else(|| body_blocks.get(index + 1).copied())
                    .or(forward_block)
                    .expect("partial dispatch has a following clause or forwarding edge");
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions: vec![MirInstruction::PatternTest {
                        dst: condition,
                        subject,
                        pattern,
                    }],
                    terminator: MirTerminator::SwitchBool {
                        condition,
                        then_target: test_blocks[index]
                            .get(test_index + 1)
                            .copied()
                            .unwrap_or(body_blocks[index]),
                        then_arguments: vec![],
                        else_target: failure,
                        else_arguments: vec![],
                    },
                });
                debug_assert_eq!(id.0, blocks.len() as u32 - 1);
            }
        }
        if forward_block.is_some() {
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::Forward],
                terminator: MirTerminator::Unreachable,
            });
        }
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }

    /// and function values as genuine VM calls while allowing a caller's
    /// handler to intercept a callee performance dynamically.
    fn lower_root_interprocedural_one_shot_handler(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (computation, clauses, root_prefix) = match self.body.expression(root).kind.clone() {
            CoreKind::Handle {
                computation,
                clauses,
            } => (computation, clauses, Vec::new()),
            CoreKind::Block(values) => {
                let (handler, prefix) = values.split_last()?;
                let CoreKind::Handle {
                    computation,
                    clauses,
                } = self.body.expression(*handler).kind.clone()
                else {
                    return None;
                };
                (computation, clauses, prefix.to_vec())
            }
            _ => return None,
        };
        let CoreKind::Call { callee, arguments } = self.body.expression(computation).kind.clone()
        else {
            return None;
        };
        let Type::Callable { effects, .. } = self.body.expression(callee).ty.clone() else {
            return None;
        };
        // A nonempty closed row is the only summary this lowering may trust.
        // An open row can contain arbitrary protocols; an associated
        // projection requires the source solver's evidence and must not be
        // approximated by bytecode lowering.
        if effects.effects.is_empty() || effects.tail.is_some() || !effects.projections.is_empty() {
            return None;
        }
        let mut active = clauses
            .into_iter()
            .filter(|clause| !clause.terminal && effects.effects.contains(&clause.effect))
            .collect::<Vec<_>>();
        if active.is_empty()
            || active.iter().any(|clause| {
                clause.patterns.len() != clause.payload_types.len()
                    || !clause.patterns.iter().all(pattern_is_irrefutable)
                    || !matches!(
                        clause.resumption,
                        CoreHandlerResumption::Tail {
                            quantity: crate::quantity::Quantity::ONCE
                        } | CoreHandlerResumption::Explicit {
                            quantity: crate::quantity::Quantity::ONCE,
                            ..
                        }
                    )
                    || self.handler_body_uses_snapshot_alias(clause.body)
            })
        {
            return None;
        }
        active.sort_by_key(|clause| (clause.effect.clone(), clause.operation));
        if active
            .windows(2)
            .any(|pair| pair[0].effect == pair[1].effect && pair[0].operation == pair[1].operation)
        {
            // One VM frame owns one protocol operation. Refutable or sibling
            // operation dispatch needs the general handler matrix; accepting
            // it here would silently change source row ordering.
            return None;
        }
        for expression in root_prefix {
            self.statement(expression)?;
        }
        let arguments = arguments
            .into_iter()
            .map(|argument| self.value(argument))
            .collect::<Option<Vec<_>>>()?;
        let callee_kind = self.body.expression(callee).kind.clone();
        let indirect = match callee_kind {
            CoreKind::Function { .. } | CoreKind::TraitMethod { .. } => None,
            _ => Some(self.value(callee)?),
        };
        let result = self.alloc(self.body.expression(computation).ty.clone(), computation);
        let payloads = active
            .iter()
            .map(|clause| {
                clause
                    .payload_types
                    .iter()
                    .map(|ty| self.alloc(ty.clone(), computation))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut entry = std::mem::take(&mut self.instructions);
        for (index, clause) in active.iter().enumerate() {
            entry.push(MirInstruction::InstallHandler {
                effect: clause.effect.definition,
                effect_arguments: clause.effect.arguments.clone(),
                operation: clause.operation,
                payload_destinations: payloads[index].clone(),
                resume_type: self.body.expression(computation).ty.clone(),
                continuation: MirContinuationPolicy::Consume,
                target: MirBlockId((index + 1) as u32),
            });
        }
        match callee_kind {
            CoreKind::Function {
                definition: callee,
                arguments: generic_arguments,
            } => entry.push(MirInstruction::Call {
                dst: result,
                callee,
                generic_arguments,
                trait_instance: None,
                arguments,
            }),
            CoreKind::TraitMethod {
                evidence,
                method: callee,
                trait_arguments,
                method_arguments,
            } => entry.push(MirInstruction::Call {
                dst: result,
                callee,
                generic_arguments: vec![],
                trait_instance: Some(MirTraitMethodInstance {
                    evidence,
                    trait_arguments,
                    method_arguments,
                }),
                arguments,
            }),
            _ => entry.push(MirInstruction::CallIndirect {
                dst: result,
                callee: indirect.expect("indirect callee was materialized"),
                arguments,
            }),
        }
        for _ in &active {
            entry.push(MirInstruction::UninstallHandler);
        }

        let mut blocks = vec![MirBlock {
            parameters: vec![],
            instructions: entry,
            terminator: MirTerminator::Return { value: result },
        }];
        let previous_named = self.named.clone();
        for (clause, payloads) in active.iter().zip(payloads) {
            self.instructions = Vec::new();
            self.named = previous_named.clone();
            self.bind_handler_patterns(&clause.patterns, &payloads)?;
            let resumed = self.direct_handler_clause_value(clause)?;
            self.instructions
                .push(MirInstruction::Resume { value: resumed });
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: std::mem::take(&mut self.instructions),
                terminator: MirTerminator::Unreachable,
            });
        }
        self.named = previous_named;
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }
    /// Lower the smallest source form that requires the VM's real handler
    /// frame: one direct resumptive operation, one irrefutable exact-one-shot
    /// arm, and an explicit continuation call. Other shapes remain on the
    /// proven static specializers until their pattern, forwarding, and
    /// multi-shot frame contracts are represented in MIR.
    fn lower_root_runtime_one_shot_handler(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (computation, clauses, root_prefix) = match self.body.expression(root).kind.clone() {
            CoreKind::Handle {
                computation,
                clauses,
            } => (computation, clauses, Vec::new()),
            CoreKind::Block(values) => {
                let (handler, prefix) = values.split_last()?;
                let CoreKind::Handle {
                    computation,
                    clauses,
                } = self.body.expression(*handler).kind.clone()
                else {
                    return None;
                };
                (computation, clauses, prefix.to_vec())
            }
            _ => return None,
        };
        let CoreKind::Perform {
            effect,
            operation,
            arguments: argument_ids,
            terminal: false,
        } = self.body.expression(computation).kind.clone()
        else {
            return None;
        };
        let matching = clauses
            .iter()
            .filter(|clause| {
                !clause.terminal && clause.effect == effect && clause.operation == operation
            })
            .collect::<Vec<_>>();
        let [clause] = matching.as_slice() else {
            return None;
        };
        let quantity = match &clause.resumption {
            CoreHandlerResumption::Explicit { quantity, .. }
            | CoreHandlerResumption::Tail { quantity } => *quantity,
            CoreHandlerResumption::Discard { .. } | CoreHandlerResumption::Terminal => return None,
        };
        if quantity != crate::quantity::Quantity::ONCE
            || clause.patterns.len() != argument_ids.len()
            || !clause.patterns.iter().all(pattern_is_irrefutable)
        {
            return None;
        }
        for expression in root_prefix {
            self.statement(expression)?;
        }
        let arguments = argument_ids
            .iter()
            .map(|argument| self.value(*argument))
            .collect::<Option<Vec<_>>>()?;
        let payload_destinations = argument_ids
            .iter()
            .map(|argument| self.alloc(self.body.expression(*argument).ty.clone(), *argument))
            .collect::<Vec<_>>();
        let result = self.alloc(self.body.expression(computation).ty.clone(), computation);
        let mut entry = std::mem::take(&mut self.instructions);
        entry.push(MirInstruction::InstallHandler {
            effect: effect.definition,
            effect_arguments: effect.arguments.clone(),
            operation,
            payload_destinations: payload_destinations.clone(),
            resume_type: self.body.expression(computation).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target: MirBlockId(1),
        });
        entry.push(MirInstruction::Perform {
            dst: result,
            effect: effect.definition,
            effect_arguments: effect.arguments,
            operation,
            arguments,
        });
        entry.push(MirInstruction::UninstallHandler);

        self.instructions = Vec::new();
        let previous_named = self.named.clone();
        self.bind_handler_patterns(&clause.patterns, &payload_destinations)?;
        let resumed = self.direct_handler_clause_value(clause)?;
        self.instructions
            .push(MirInstruction::Resume { value: resumed });
        let handler_instructions = std::mem::take(&mut self.instructions);
        self.named = previous_named;
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks: vec![
                MirBlock {
                    parameters: vec![],
                    instructions: entry,
                    terminator: MirTerminator::Return { value: result },
                },
                MirBlock {
                    parameters: vec![],
                    instructions: handler_instructions,
                    terminator: MirTerminator::Unreachable,
                },
            ],
        })
    }
    /// Lower a named generic helper through a real VM handler frame. The
    /// helper must have the proven parameter-forwarding shape recognised by
    /// `direct_known_perform`; this preserves its Core effect identity while
    /// making the handler transition, resume, and cleanup executable rather
    /// than relying on terminal-handler lowering for a source-level call.
    fn lower_root_runtime_one_shot_indirect_handler(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (computation, clauses, root_prefix) = match self.body.expression(root).kind.clone() {
            CoreKind::Handle {
                computation,
                clauses,
            } => (computation, clauses, Vec::new()),
            CoreKind::Block(values) => {
                let (handler, prefix) = values.split_last()?;
                let CoreKind::Handle {
                    computation,
                    clauses,
                } = self.body.expression(*handler).kind.clone()
                else {
                    return None;
                };
                (computation, clauses, prefix.to_vec())
            }
            _ => return None,
        };
        let CoreKind::Call { callee, arguments } = self.body.expression(computation).kind.clone()
        else {
            return None;
        };
        let CoreKind::Function { definition, .. } = self.body.expression(callee).kind.clone()
        else {
            return None;
        };
        let (effect, operation, forwarded) =
            self.direct_known_perform(definition, arguments.clone())?;
        let matching = clauses
            .iter()
            .filter(|clause| {
                !clause.terminal && clause.effect == effect && clause.operation == operation
            })
            .collect::<Vec<_>>();
        let [clause] = matching.as_slice() else {
            return None;
        };
        let quantity = match &clause.resumption {
            CoreHandlerResumption::Explicit { quantity, .. }
            | CoreHandlerResumption::Tail { quantity } => *quantity,
            CoreHandlerResumption::Discard { .. } | CoreHandlerResumption::Terminal => return None,
        };
        if quantity != crate::quantity::Quantity::ONCE
            || clause.patterns.len() != forwarded.len()
            || !clause.patterns.iter().all(pattern_is_irrefutable)
        {
            return None;
        }
        for expression in root_prefix {
            self.statement(expression)?;
        }
        let arguments = forwarded
            .into_iter()
            .map(|argument| self.value(argument))
            .collect::<Option<Vec<_>>>()?;
        let payload_destinations = clause
            .payload_types
            .iter()
            .map(|ty| self.alloc(ty.clone(), computation))
            .collect::<Vec<_>>();
        let result = self.alloc(self.body.expression(computation).ty.clone(), computation);
        let mut entry = std::mem::take(&mut self.instructions);
        entry.push(MirInstruction::InstallHandler {
            effect: effect.definition,
            effect_arguments: effect.arguments.clone(),
            operation,
            payload_destinations: payload_destinations.clone(),
            resume_type: self.body.expression(computation).ty.clone(),
            continuation: MirContinuationPolicy::Consume,
            target: MirBlockId(1),
        });
        entry.push(MirInstruction::Perform {
            dst: result,
            effect: effect.definition,
            effect_arguments: effect.arguments,
            operation,
            arguments,
        });
        entry.push(MirInstruction::UninstallHandler);

        self.instructions = Vec::new();
        let previous_named = self.named.clone();
        self.bind_handler_patterns(&clause.patterns, &payload_destinations)?;
        let resumed = self.direct_handler_clause_value(clause)?;
        self.instructions
            .push(MirInstruction::Resume { value: resumed });
        let handler_instructions = std::mem::take(&mut self.instructions);
        self.named = previous_named;
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks: vec![
                MirBlock {
                    parameters: vec![],
                    instructions: entry,
                    terminator: MirTerminator::Return { value: result },
                },
                MirBlock {
                    parameters: vec![],
                    instructions: handler_instructions,
                    terminator: MirTerminator::Unreachable,
                },
            ],
        })
    }
    /// Lower a normal-completion handler into an ordered structural decision
    /// chain. Completion is evaluated exactly once, then every arm sees the
    /// same subject; only the selected arm gets its binder projections.
    fn lower_root_completion_handler(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (computation, clauses) = match self.body.expression(root).kind.clone() {
            CoreKind::Completion {
                computation,
                clauses,
            } => (computation, clauses),
            CoreKind::Block(values) => {
                let (last, prefix) = values.split_last()?;
                let CoreKind::Completion {
                    computation,
                    clauses,
                } = self.body.expression(*last).kind.clone()
                else {
                    return None;
                };
                for value in prefix {
                    self.statement(*value)?;
                }
                (computation, clauses)
            }
            _ => return None,
        };
        let subject = if let CoreKind::Handle {
            computation: handled_computation,
            clauses: operation_clauses,
        } = self.body.expression(computation).kind.clone()
        {
            if self.has_direct_perform(handled_computation) {
                return self.lower_root_direct_mixed_handler(
                    root,
                    computation,
                    handled_computation,
                    operation_clauses,
                    clauses,
                    parameters,
                );
            }
            // A handler with operation clauses around a statically pure
            // computation has no operation dispatch to materialize. Its
            // normal completion still remains semantically observable, and
            // lowering the inner computation directly is valid only after
            // proving that it cannot invoke an outward effectful callable.
            if !self.core_is_effect_free(handled_computation) {
                self.error(
                    "G6005",
                    "handler-stack lowering is required for an indirect handler computation",
                );
                return Some(self.invalid_function(parameters));
            }
            self.value(handled_computation)?
        } else {
            self.value(computation)?
        };

        let fallback_index = clauses
            .iter()
            .position(|clause| pattern_is_irrefutable(&clause.pattern));
        let selected = fallback_index
            .map(|index| clauses[..=index].to_vec())
            .unwrap_or(clauses);
        let has_fallback = fallback_index.is_some();
        let entry_instructions = std::mem::take(&mut self.instructions);
        let entry_values = self.values.clone();
        let mut blocks = vec![MirBlock {
            parameters: vec![],
            instructions: entry_instructions,
            terminator: MirTerminator::Unreachable,
        }];
        let mut bodies = Vec::with_capacity(selected.len());
        for clause in &selected {
            self.instructions = vec![];
            self.values = entry_values.clone();
            let previous_named = self.named.clone();
            if self.bind_completion_clause(clause, subject).is_none() {
                self.named = previous_named;
                return Some(self.invalid_function(parameters));
            }
            let Some(body) = self.value(clause.body) else {
                self.named = previous_named;
                return Some(self.invalid_function(parameters));
            };
            let instructions = std::mem::take(&mut self.instructions);
            self.named = previous_named;
            let id = MirBlockId(blocks.len() as u32);
            blocks.push(MirBlock {
                parameters: vec![],
                instructions,
                terminator: MirTerminator::Return { value: body },
            });
            bodies.push(id);
        }
        self.values = entry_values;
        let mut next = if has_fallback {
            *bodies.last().expect("completion fallback body exists")
        } else {
            let id = MirBlockId(blocks.len() as u32);
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Unreachable,
            });
            id
        };
        let tested = if has_fallback {
            selected.len().saturating_sub(1)
        } else {
            selected.len()
        };
        for index in (0..tested).rev() {
            let Some(pattern) = lower_pattern(selected[index].pattern.clone()) else {
                self.error(
                    "G6005",
                    "completion handler contains an invalid structural pattern",
                );
                return Some(self.invalid_function(parameters));
            };
            let condition = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), root);
            blocks[0].instructions.push(MirInstruction::PatternTest {
                dst: condition,
                subject,
                pattern,
            });
            let selected_arm = bodies[index];
            let id = MirBlockId(blocks.len() as u32);
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::SwitchBool {
                    condition,
                    then_target: selected_arm,
                    then_arguments: vec![],
                    else_target: next,
                    else_arguments: vec![],
                },
            });
            next = id;
        }
        blocks[0].terminator = MirTerminator::Goto {
            target: next,
            arguments: vec![],
        };
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }
    /// Direct mixed handlers use two ordered dispatch phases. A selected
    /// resumptive operation arm supplies the normal result of its resumed
    /// computation to the completion matrix; a terminal or discarded arm
    /// returns its handler result directly. The shared block parameter is the
    /// typed boundary for the normal-completion path only: operation clauses
    /// do not spuriously execute completion clauses after aborting their
    /// captured computation.
    fn lower_root_direct_mixed_handler(
        &mut self,
        root: CoreId,
        handler: CoreId,
        computation: CoreId,
        clauses: Vec<CoreHandlerClause>,
        completion: Vec<CoreCompletionClause>,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (effect, operation, argument_ids) = self.direct_operation(computation)?;
        let arguments = argument_ids
            .into_iter()
            .map(|argument| self.value(argument))
            .collect::<Option<Vec<_>>>()?;
        let mut selected = clauses
            .into_iter()
            .filter(|clause| clause.effect == effect && clause.operation == operation)
            .collect::<Vec<_>>();
        if selected.is_empty() {
            return None;
        }
        let operation_has_fallback = if let Some(fallback) = selected
            .iter()
            .position(|clause| clause.patterns.iter().all(pattern_is_irrefutable))
        {
            selected.truncate(fallback + 1);
            true
        } else {
            false
        };
        if selected
            .iter()
            .any(|clause| clause.patterns.len() != arguments.len())
        {
            return None;
        }
        let entry_instructions = std::mem::take(&mut self.instructions);
        let entry_values = self.values.clone();
        let completed = self.alloc(self.body.expression(handler).ty.clone(), handler);
        let mut blocks = vec![
            MirBlock {
                parameters: vec![],
                instructions: entry_instructions,
                terminator: MirTerminator::Unreachable,
            },
            MirBlock {
                parameters: vec![completed],
                instructions: vec![],
                terminator: MirTerminator::Unreachable,
            },
        ];

        let mut operation_bodies = Vec::with_capacity(selected.len());
        for clause in &selected {
            self.instructions = vec![];
            self.values = entry_values.clone();
            let previous_named = self.named.clone();
            self.bind_handler_patterns(&clause.patterns, &arguments)?;
            let result = self.direct_root_handler_clause_value(clause)?;
            let instructions = std::mem::take(&mut self.instructions);
            self.named = previous_named;
            let id = MirBlockId(blocks.len() as u32);
            let terminator = match clause.resumption {
                CoreHandlerResumption::Tail { .. } | CoreHandlerResumption::Explicit { .. } => {
                    MirTerminator::Goto {
                        target: MirBlockId(1),
                        arguments: vec![result],
                    }
                }
                CoreHandlerResumption::Discard { .. } | CoreHandlerResumption::Terminal => {
                    MirTerminator::Return { value: result }
                }
            };
            blocks.push(MirBlock {
                parameters: vec![],
                instructions,
                terminator,
            });
            operation_bodies.push(id);
        }

        let completion_fallback = completion
            .iter()
            .position(|clause| pattern_is_irrefutable(&clause.pattern));
        let completion = completion_fallback
            .map(|index| completion[..=index].to_vec())
            .unwrap_or(completion);
        let completion_has_fallback = completion_fallback.is_some();
        let mut completion_bodies = Vec::with_capacity(completion.len());
        for clause in &completion {
            self.instructions = vec![];
            self.values = entry_values.clone();
            let previous_named = self.named.clone();
            self.bind_completion_clause(clause, completed)?;
            let result = self.value(clause.body)?;
            let instructions = std::mem::take(&mut self.instructions);
            self.named = previous_named;
            let id = MirBlockId(blocks.len() as u32);
            blocks.push(MirBlock {
                parameters: vec![],
                instructions,
                terminator: MirTerminator::Return { value: result },
            });
            completion_bodies.push(id);
        }
        self.values = entry_values;

        let mut completion_next = if completion_has_fallback {
            *completion_bodies.last()?
        } else {
            let id = MirBlockId(blocks.len() as u32);
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Unreachable,
            });
            id
        };
        let completion_tested = if completion_has_fallback {
            completion_bodies.len().saturating_sub(1)
        } else {
            completion_bodies.len()
        };
        for index in (0..completion_tested).rev() {
            let pattern = lower_pattern(completion[index].pattern.clone())?;
            let condition = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), root);
            blocks[1].instructions.push(MirInstruction::PatternTest {
                dst: condition,
                subject: completed,
                pattern,
            });
            let id = MirBlockId(blocks.len() as u32);
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::SwitchBool {
                    condition,
                    then_target: completion_bodies[index],
                    then_arguments: vec![],
                    else_target: completion_next,
                    else_arguments: vec![],
                },
            });
            completion_next = id;
        }
        blocks[1].terminator = MirTerminator::Goto {
            target: completion_next,
            arguments: vec![],
        };

        let mut operation_next = if operation_has_fallback {
            *operation_bodies.last()?
        } else {
            let id = MirBlockId(blocks.len() as u32);
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Unreachable,
            });
            id
        };
        let operation_tested = if operation_has_fallback {
            operation_bodies.len().saturating_sub(1)
        } else {
            operation_bodies.len()
        };
        for index in (0..operation_tested).rev() {
            let mut selected_arm = operation_bodies[index];
            for (pattern, argument) in selected[index]
                .patterns
                .iter()
                .cloned()
                .zip(arguments.iter().copied())
                .rev()
            {
                let pattern = lower_pattern(pattern)?;
                let condition = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), root);
                blocks[0].instructions.push(MirInstruction::PatternTest {
                    dst: condition,
                    subject: argument,
                    pattern,
                });
                let id = MirBlockId(blocks.len() as u32);
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions: vec![],
                    terminator: MirTerminator::SwitchBool {
                        condition,
                        then_target: selected_arm,
                        then_arguments: vec![],
                        else_target: operation_next,
                        else_arguments: vec![],
                    },
                });
                selected_arm = id;
            }
            operation_next = selected_arm;
        }
        blocks[0].terminator = MirTerminator::Goto {
            target: operation_next,
            arguments: vec![],
        };
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }
    /// Construct a conventional MIR CFG for a root terminal handler. Each
    /// non-final arm receives a sequence of `PatternTest` blocks and any false
    /// edge advances to the next arm; the final
    /// irrefutable arm is the required forwarding-free fallback.  The general
    /// handler-stack lowering extends this same shape with resumptions.
    fn lower_root_terminal_pattern_handler(
        &mut self,
        root: CoreId,
        parameters: Vec<MirLocal>,
    ) -> Option<MirFunction> {
        let (computation, clauses) = match self.body.expression(root).kind.clone() {
            CoreKind::Handle {
                computation,
                clauses,
            } => (computation, clauses),
            CoreKind::Block(values) => {
                let (last, prefix) = values.split_last()?;
                let CoreKind::Handle {
                    computation,
                    clauses,
                } = self.body.expression(*last).kind.clone()
                else {
                    return None;
                };
                for value in prefix {
                    self.statement(*value)?;
                }
                (computation, clauses)
            }
            _ => return None,
        };
        // A normal direct operation still enters this fast root-handler path
        // with a resumable continuation.  Only a bottom-typed computation
        // needs the strict-context walk that finds its terminal child.
        let (effect, operation, arguments) =
            if matches!(&self.body.expression(computation).ty, Type::Never) {
                self.terminal_operation(computation)?
            } else {
                self.direct_operation(computation)?
            };
        let arguments = arguments
            .into_iter()
            .map(|argument| self.value(argument))
            .collect::<Option<Vec<_>>>()?;
        let mut selected = clauses
            .into_iter()
            .filter(|clause| clause.effect == effect && clause.operation == operation)
            .collect::<Vec<_>>();
        let fallback_index = selected
            .iter()
            .position(|clause| clause.patterns.iter().all(pattern_is_irrefutable));
        if let Some(index) = fallback_index {
            // Source-order rows after an irrefutable arm are unreachable and
            // must not be emitted as executable dispatch alternatives.
            selected.truncate(index + 1);
        }
        if selected
            .iter()
            .any(|clause| clause.patterns.len() != arguments.len())
        {
            self.error(
                "G6005",
                "terminal handler arm does not match its operation payload arity",
            );
            return Some(self.invalid_function(parameters));
        }

        let entry_instructions = std::mem::take(&mut self.instructions);
        let mut blocks = vec![MirBlock {
            parameters: vec![],
            instructions: entry_instructions,
            terminator: MirTerminator::Unreachable,
        }];
        let mut bodies = Vec::with_capacity(selected.len());
        for clause in &selected {
            let previous_named = self.named.clone();
            if self
                .bind_handler_patterns(&clause.patterns, &arguments)
                .is_none()
            {
                self.named = previous_named;
                return Some(self.invalid_function(parameters));
            }
            let body = self.direct_root_handler_clause_value(clause)?;
            let instructions = std::mem::take(&mut self.instructions);
            self.named = previous_named;
            let id = MirBlockId(blocks.len() as u32);
            blocks.push(MirBlock {
                parameters: vec![],
                instructions,
                terminator: MirTerminator::Return { value: body },
            });
            bodies.push(id);
        }
        let mut next = if fallback_index.is_some() {
            *bodies
                .last()
                .expect("terminal handler fallback body exists")
        } else {
            let id = MirBlockId(blocks.len() as u32);
            blocks.push(MirBlock {
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Unreachable,
            });
            id
        };
        let tested = if fallback_index.is_some() {
            selected.len().saturating_sub(1)
        } else {
            selected.len()
        };
        for index in (0..tested).rev() {
            let mut selected_arm = bodies[index];
            for (pattern, argument) in selected[index]
                .patterns
                .iter()
                .cloned()
                .zip(arguments.iter().copied())
                .rev()
            {
                let Some(pattern) = lower_pattern(pattern) else {
                    self.error(
                        "G6005",
                        "terminal handler contains an invalid structural pattern",
                    );
                    return Some(self.invalid_function(parameters));
                };
                let condition = self.alloc(Type::Scalar(crate::types::ScalarType::Bool), root);
                // Pattern tests are observational. Evaluate them in the entry
                // block so every later CFG edge sees the same initialized
                // register state; branches retain source-order first-match
                // selection without manufacturing phi state for test flags.
                blocks[0].instructions.push(MirInstruction::PatternTest {
                    dst: condition,
                    subject: argument,
                    pattern,
                });
                let id = MirBlockId(blocks.len() as u32);
                blocks.push(MirBlock {
                    parameters: vec![],
                    instructions: vec![],
                    terminator: MirTerminator::SwitchBool {
                        condition,
                        then_target: selected_arm,
                        then_arguments: vec![],
                        else_target: next,
                        else_arguments: vec![],
                    },
                });
                selected_arm = id;
            }
            next = selected_arm;
        }
        blocks[0].terminator = MirTerminator::Goto {
            target: next,
            arguments: vec![],
        };
        Some(MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: self.body.expression(root).ty.clone(),
            entry: MirBlockId(0),
            blocks,
        })
    }
    fn invalid_function(&self, parameters: Vec<MirLocal>) -> MirFunction {
        MirFunction {
            definition: self.definition,
            captures: 0,
            parameters,
            locals: self.locals.clone(),
            result: Type::Error,
            entry: MirBlockId(0),
            blocks: vec![MirBlock {
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Unreachable,
            }],
        }
    }
    fn direct_handler_clause_value(&mut self, clause: &CoreHandlerClause) -> Option<MirLocal> {
        match &clause.resumption {
            CoreHandlerResumption::Terminal => self.value(clause.body),
            CoreHandlerResumption::Tail { quantity } => {
                if !quantity.contains(crate::quantity::Quantity::ONCE) {
                    self.error(
                        "G6005",
                        "direct tail resumption does not satisfy its declared quantity",
                    );
                    return None;
                }
                self.value(clause.body)
            }
            CoreHandlerResumption::Explicit { name, quantity } => {
                let replay = quantity.upper.is_some_and(|upper| upper >= 2)
                    && !quantity.contains(crate::quantity::Quantity::ONCE);
                if !quantity.contains(crate::quantity::Quantity::ONCE) && !replay {
                    self.error(
                        "G6005",
                        "direct resumption does not satisfy its declared quantity",
                    );
                    return None;
                }
                if !self.handler_body_uses_snapshot_alias(clause.body) {
                    let previous = self.direct_resumption.replace(DirectResumptionState {
                        name: name.clone(),
                        quantity: *quantity,
                        calls: 0,
                        plan: if replay {
                            DirectResumptionPlan::RuntimeReplay
                        } else {
                            DirectResumptionPlan::Identity
                        },
                    });
                    let result = self.value(clause.body);
                    let state = self
                        .direct_resumption
                        .take()
                        .expect("direct resumption state must outlive its clause body");
                    self.direct_resumption = previous;
                    let result = result?;
                    let actual = crate::quantity::Quantity::new(state.calls, Some(state.calls))
                        .expect("direct resumption calls are representable");
                    if !state.quantity.contains(actual) {
                        self.error(
                            "G6005",
                            "direct resumptive handler calls do not satisfy its declared quantity",
                        );
                        return None;
                    }
                    return Some(result);
                }
                // The dynamic handler path deliberately retains a real
                // snapshot operand instead of relying on the legacy implicit
                // top-of-stack `Resume`. This is the boundary where aliasing
                // becomes executable bytecode rather than a Core-only fact.
                self.value(clause.body)
            }
            CoreHandlerResumption::Discard { quantity } => {
                if quantity.requires_positive_use() {
                    self.error(
                        "G6005",
                        "discarded continuation violates its declared quantity",
                    );
                    return None;
                }
                self.value(clause.body)
            }
        }
    }
    fn handler_body_uses_snapshot_alias(&self, id: CoreId) -> bool {
        match &self.body.expression(id).kind {
            CoreKind::Let { value, .. } => {
                matches!(
                    self.body.expression(*value).kind,
                    CoreKind::Resumption { .. }
                )
            }
            CoreKind::Block(values) => values
                .iter()
                .copied()
                .any(|value| self.handler_body_uses_snapshot_alias(value)),
            _ => false,
        }
    }
    /// Lower a clause whose captured continuation is the direct root return.
    /// Unlike a nonempty residual continuation, this identity shape can replay
    /// an exact finite number of resumes by evaluating the clause body once
    /// and replacing each `k(value)` call with that value. The use count is
    /// still checked against the frozen operation quantity; a wider interval
    /// remains a dynamic-handler concern and fails closed here.
    fn direct_root_handler_clause_value(&mut self, clause: &CoreHandlerClause) -> Option<MirLocal> {
        match &clause.resumption {
            CoreHandlerResumption::Explicit { name, quantity } => {
                // Core name resolution lets the generated continuation shadow
                // a same-spelled parameter or payload binder. Temporarily
                // remove that outer lowering binding so only a new nested
                // `let name = ...` prevents direct-resumption recognition.
                let shadowed = self.named.remove(name);
                let previous = self.direct_resumption.replace(DirectResumptionState {
                    name: name.clone(),
                    quantity: *quantity,
                    calls: 0,
                    plan: DirectResumptionPlan::Identity,
                });
                let result = self.value(clause.body);
                let state = self
                    .direct_resumption
                    .take()
                    .expect("direct resumption state must outlive its clause body");
                self.direct_resumption = previous;
                if let Some(local) = shadowed {
                    self.named.insert(name.clone(), local);
                }
                let result = result?;
                let actual = match crate::quantity::Quantity::new(state.calls, Some(state.calls)) {
                    Ok(quantity) => quantity,
                    Err(_) => {
                        self.error("G6005", "direct resumption count is not representable");
                        return None;
                    }
                };
                if !state.quantity.contains(actual) {
                    self.error(
                        "G6005",
                        "direct resumption calls do not satisfy its declared quantity",
                    );
                    return None;
                }
                Some(result)
            }
            _ => self.direct_handler_clause_value(clause),
        }
    }
    /// Bind the payload environment after a handler arm has been selected.
    /// Core retains bind nodes inside the structural pattern, so nested nominal
    /// fields are projected from their actual payload instead of being paired
    /// positionally with unrelated operation arguments.
    fn bind_completion_clause(
        &mut self,
        clause: &CoreCompletionClause,
        subject: MirLocal,
    ) -> Option<()> {
        self.bind_handler_patterns(std::slice::from_ref(&clause.pattern), &[subject])?;
        if let Some(refinement) = &clause.refinement {
            // The completion pattern proved the boolean result true. Recover
            // the cached structural subject that produced that bit and bind
            // only the positive branch's projections. This is both the
            // once-evaluation guarantee and the boundary that keeps positive
            // binders out of false/wildcard completion arms.
            let refinement_subject = self.value(refinement.subject)?;
            self.bind_handler_patterns(
                std::slice::from_ref(&refinement.pattern),
                &[refinement_subject],
            )?;
        }
        Some(())
    }

    fn bind_handler_patterns(
        &mut self,
        patterns: &[CorePattern],
        arguments: &[MirLocal],
    ) -> Option<()> {
        if patterns.len() != arguments.len() {
            self.error(
                "G6005",
                "handler arm does not match its operation payload arity",
            );
            return None;
        }
        for (pattern, argument) in patterns.iter().zip(arguments) {
            self.bind_handler_pattern(pattern, *argument)?;
        }
        Some(())
    }
    fn bind_handler_pattern(&mut self, pattern: &CorePattern, value: MirLocal) -> Option<()> {
        match pattern {
            CorePattern::Any | CorePattern::Literal(_) => Some(()),
            CorePattern::Bind { name } => {
                self.named.insert(name.clone(), value);
                Some(())
            }
            CorePattern::Record {
                field_count,
                fields,
                ..
            }
            | CorePattern::Enum {
                field_count,
                fields,
                ..
            } => {
                for field in fields {
                    let projected = self.alloc(field.ty.clone(), CoreId(u32::MAX));
                    self.instructions.push(MirInstruction::ProjectRecord {
                        dst: projected,
                        base: value,
                        index: field.index,
                        field_count: *field_count,
                        field_type: field.ty.clone(),
                    });
                    self.bind_handler_pattern(&field.pattern, projected)?;
                }
                Some(())
            }
            CorePattern::Tuple(fields) => {
                let Type::Tuple(types) = self.locals[value.0 as usize].ty.clone() else {
                    self.error("G6005", "tuple handler pattern lost its tuple payload type");
                    return None;
                };
                if fields.len() != types.len() {
                    self.error(
                        "G6005",
                        "tuple handler pattern has an invalid payload arity",
                    );
                    return None;
                }
                for (index, (pattern, ty)) in fields.iter().zip(types).enumerate() {
                    let projected = self.alloc(ty.clone(), CoreId(u32::MAX));
                    self.instructions.push(MirInstruction::ProjectTuple {
                        dst: projected,
                        base: value,
                        index: index as u32,
                        field_count: fields.len() as u32,
                        field_type: ty,
                    });
                    self.bind_handler_pattern(pattern, projected)?;
                }
                Some(())
            }
            CorePattern::Error => {
                self.error("G6005", "handler contains a recovered structural pattern");
                None
            }
        }
    }
    fn value(&mut self, id: CoreId) -> Option<MirLocal> {
        if let Some(rejoin) = self.label_rejoins.get(&id) {
            return Some(*rejoin);
        }
        if let Some(v) = self.values.get(&id) {
            return Some(*v);
        };
        let e = self.body.expression(id).clone();
        // A local binding has stable storage identity. MIR may still use
        // registers, but a `let` cannot merely alias its initializer: later
        // assignment must overwrite this same destination.
        if let CoreKind::Let { name, value } = &e.kind {
            let aliases_direct_resumption = match &self.body.expression(*value).kind {
                CoreKind::Resumption { .. } => true,
                CoreKind::Local(source) => {
                    self.direct_resumption.as_ref().is_some_and(|resumption| {
                        resumption.name == *source && !self.named.contains_key(source)
                    })
                }
                _ => false,
            };
            if aliases_direct_resumption {
                if self.direct_resumption.is_some() {
                    // Static replay owns its snapshot directly. An alias has
                    // no independent runtime storage in that specialization.
                    let unit = self.alloc(Type::Unit, id);
                    self.instructions
                        .push(MirInstruction::ConstUnit { dst: unit });
                    self.values.insert(id, unit);
                    return Some(unit);
                }
                let snapshot = self.value(*value)?;
                let local = self.alloc(self.body.expression(*value).ty.clone(), id);
                self.instructions.push(MirInstruction::Copy {
                    dst: local,
                    src: snapshot,
                });
                self.named.insert(name.clone(), local);
                let unit = self.alloc(Type::Unit, id);
                self.instructions
                    .push(MirInstruction::ConstUnit { dst: unit });
                self.values.insert(id, unit);
                return Some(unit);
            }
            let src = self.value(*value)?;
            let local = self.alloc(self.body.expression(*value).ty.clone(), id);
            self.instructions
                .push(MirInstruction::Copy { dst: local, src });
            self.named.insert(name.clone(), local);
            let unit = self.alloc(Type::Unit, id);
            self.instructions
                .push(MirInstruction::ConstUnit { dst: unit });
            self.values.insert(id, unit);
            return Some(unit);
        }
        if let CoreKind::Assign { place, value } = &e.kind {
            let src = self.value(*value)?;
            self.store_place(place, src)?;
            let unit = self.alloc(Type::Unit, id);
            self.instructions
                .push(MirInstruction::ConstUnit { dst: unit });
            self.values.insert(id, unit);
            return Some(unit);
        }
        let ty = e.ty.clone();
        let dst = self.alloc(ty.clone(), id);
        match e.kind {
            CoreKind::Literal(text) => match ty {
                Type::Scalar(crate::types::ScalarType::I64) => match parse_i64_literal(&text) {
                    Ok(value) => self
                        .instructions
                        .push(MirInstruction::ConstI64 { dst, value }),
                    Err(_) => {
                        self.error("G6003", "invalid i64 literal at MIR lowering");
                        return None;
                    }
                },
                Type::Scalar(crate::types::ScalarType::F64) => match parse_f64_literal(&text) {
                    Ok(value) => self.instructions.push(MirInstruction::ConstF64 {
                        dst,
                        bits: value.to_bits(),
                    }),
                    Err(_) => {
                        self.error("G6003", "invalid f64 literal at MIR lowering");
                        return None;
                    }
                },
                Type::Scalar(crate::types::ScalarType::Bool) => match text.as_str() {
                    "true" => self
                        .instructions
                        .push(MirInstruction::ConstBool { dst, value: true }),
                    "false" => self
                        .instructions
                        .push(MirInstruction::ConstBool { dst, value: false }),
                    _ => {
                        self.error("G6003", "invalid Bool literal at MIR lowering");
                        return None;
                    }
                },
                Type::Scalar(crate::types::ScalarType::Char) => match parse_char_literal(&text) {
                    Ok(value) => self
                        .instructions
                        .push(MirInstruction::ConstChar { dst, value }),
                    Err(_) => {
                        self.error("G6003", "invalid char literal at MIR lowering");
                        return None;
                    }
                },
                Type::Scalar(crate::types::ScalarType::Text) => match parse_text_literal(&text) {
                    Ok(value) => self
                        .instructions
                        .push(MirInstruction::ConstText { dst, value }),
                    Err(_) => {
                        self.error("G6003", "invalid Text literal at MIR lowering");
                        return None;
                    }
                },
                _ => {
                    self.error(
                        "G6003",
                        "literal type has no runtime representation in this MIR",
                    );
                    return None;
                }
            },
            CoreKind::Local(name) => {
                let src = *self.named.get(&name).or_else(|| self.values.get(&id))?;
                self.instructions.push(MirInstruction::Copy { dst, src });
            }
            CoreKind::Resumption { id, .. } => {
                if let Some(snapshot) = self.resumption_snapshots.get(&id) {
                    self.instructions.push(MirInstruction::Copy {
                        dst,
                        src: *snapshot,
                    });
                } else {
                    self.instructions
                        .push(MirInstruction::CaptureResumption { dst });
                    self.resumption_snapshots.insert(id, dst);
                }
            }
            // Named callables are first-class values just like anonymous
            // closures. Their environment is statically empty, while the
            // function identity selects the verified code target.
            CoreKind::Function {
                definition: callee,
                arguments: generic_arguments,
            } => self.instructions.push(MirInstruction::MakeCallable {
                dst,
                callee,
                captures: vec![],
                generic_arguments,
                trait_instance: None,
                environment: None,
            }),
            CoreKind::TraitMethod {
                evidence,
                method: callee,
                trait_arguments,
                method_arguments,
            } => self.instructions.push(MirInstruction::MakeCallable {
                dst,
                callee,
                captures: vec![],
                generic_arguments: vec![],
                trait_instance: Some(MirTraitMethodInstance {
                    evidence,
                    trait_arguments,
                    method_arguments,
                }),
                environment: None,
            }),
            CoreKind::Constant(callee) => {
                self.instructions.push(MirInstruction::Call {
                    dst,
                    callee,
                    generic_arguments: vec![],
                    trait_instance: None,
                    arguments: vec![],
                });
            }
            CoreKind::Tuple(fields) => {
                let fields = fields
                    .into_iter()
                    .map(|field| self.value(field))
                    .collect::<Option<Vec<_>>>()?;
                self.instructions
                    .push(MirInstruction::MakeTuple { dst, fields });
            }
            CoreKind::Array(fields) => {
                let Type::Array(element_type) = ty.clone() else {
                    self.error("G6008", "array Core expression has a non-array type");
                    return None;
                };
                let fields = fields
                    .into_iter()
                    .map(|field| self.value(field))
                    .collect::<Option<Vec<_>>>()?;
                self.instructions.push(MirInstruction::MakeArray {
                    dst,
                    fields,
                    element_type: *element_type,
                });
            }
            CoreKind::Record { definition, fields } => {
                let field_types = fields
                    .iter()
                    .map(|field| self.body.expression(*field).ty.clone())
                    .collect::<Vec<_>>();
                let fields = fields
                    .into_iter()
                    .map(|field| self.value(field))
                    .collect::<Option<Vec<_>>>()?;
                self.instructions.push(MirInstruction::MakeRecord {
                    dst,
                    definition,
                    fields,
                    field_types,
                });
            }
            CoreKind::Enum {
                definition,
                variant,
                fields,
            } => {
                let field_types = fields
                    .iter()
                    .map(|field| self.body.expression(*field).ty.clone())
                    .collect::<Vec<_>>();
                let fields = fields
                    .into_iter()
                    .map(|field| self.value(field))
                    .collect::<Option<Vec<_>>>()?;
                self.instructions.push(MirInstruction::MakeEnum {
                    dst,
                    definition,
                    variant,
                    fields,
                    field_types,
                });
            }
            CoreKind::Field {
                base,
                index,
                field_count,
            } => {
                let base = self.value(base)?;
                self.instructions.push(MirInstruction::ProjectRecord {
                    dst,
                    base,
                    index,
                    field_count,
                    field_type: ty,
                });
            }
            CoreKind::PatternTest {
                subject, pattern, ..
            } => {
                let subject = self.value(subject)?;
                let Some(pattern) = lower_pattern(pattern) else {
                    self.error("G6005", "Typed Core contains an invalid structural pattern");
                    return None;
                };
                self.instructions.push(MirInstruction::PatternTest {
                    dst,
                    subject,
                    pattern,
                });
            }
            CoreKind::Perform {
                effect,
                operation,
                arguments,
                terminal: _,
            } => {
                let arguments = arguments
                    .into_iter()
                    .map(|argument| self.value(argument))
                    .collect::<Option<Vec<_>>>()?;
                self.instructions.push(MirInstruction::Perform {
                    dst,
                    effect: effect.definition,
                    effect_arguments: effect.arguments,
                    operation,
                    arguments,
                });
            }
            CoreKind::Handle {
                computation,
                clauses,
            } => self.lower_terminal_handle(dst, computation, clauses)?,
            CoreKind::Borrow { unique, value } => {
                if let CoreKind::Deref(reference) = self.body.expression(value).kind.clone() {
                    let src = self.value(reference)?;
                    self.instructions.push(MirInstruction::Borrow {
                        dst,
                        src,
                        fields: vec![],
                        unique,
                    });
                    self.values.insert(id, dst);
                    return Some(dst);
                }
                let Some((src, fields)) = self.reference_place(value) else {
                    self.error("G6010", "borrow requires a stable local place");
                    return None;
                };
                self.instructions.push(MirInstruction::Borrow {
                    dst,
                    src,
                    fields,
                    unique,
                });
            }
            CoreKind::Deref(value) => {
                let reference = self.value(value)?;
                self.instructions
                    .push(MirInstruction::DerefCopy { dst, reference });
            }
            CoreKind::Move(value) => {
                let src = self.value(value)?;
                self.instructions.push(MirInstruction::Move { dst, src });
            }
            CoreKind::Unary { operator, value } => {
                let value = self.value(value)?;
                match (operator.as_str(), &ty) {
                    (
                        "+",
                        Type::Scalar(crate::types::ScalarType::I64 | crate::types::ScalarType::F64),
                    ) => {
                        self.instructions
                            .push(MirInstruction::Copy { dst, src: value });
                    }
                    ("-", Type::Scalar(crate::types::ScalarType::I64)) => {
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::I64), id);
                        self.instructions.push(MirInstruction::ConstI64 {
                            dst: zero,
                            value: 0,
                        });
                        self.instructions.push(MirInstruction::SubI64 {
                            dst,
                            left: zero,
                            right: value,
                        });
                    }
                    ("-", Type::Scalar(crate::types::ScalarType::F64)) => {
                        let zero = self.alloc(Type::Scalar(crate::types::ScalarType::F64), id);
                        self.instructions.push(MirInstruction::ConstF64 {
                            dst: zero,
                            bits: 0.0f64.to_bits(),
                        });
                        self.instructions.push(MirInstruction::SubF64 {
                            dst,
                            left: zero,
                            right: value,
                        });
                    }
                    ("!", Type::Scalar(crate::types::ScalarType::Bool)) => {
                        self.instructions
                            .push(MirInstruction::NotBool { dst, value });
                    }
                    _ => {
                        self.error("G6005", "prefix operator has no MIR instruction");
                        return None;
                    }
                }
            }
            CoreKind::Binary {
                operator,
                left,
                right,
            } if matches!(operator.as_str(), "+" | "-" | "*" | "/" | "%") => {
                let left = self.value(left)?;
                let right = self.value(right)?;
                let instruction = match (&ty, operator.as_str()) {
                    (Type::Scalar(crate::types::ScalarType::I64), "+") => {
                        MirInstruction::AddI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), "-") => {
                        MirInstruction::SubI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), "*") => {
                        MirInstruction::MulI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), "/") => {
                        MirInstruction::DivI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), "%") => {
                        MirInstruction::RemI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "+") => {
                        MirInstruction::AddF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Text), "+") => {
                        MirInstruction::ConcatText { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "-") => {
                        MirInstruction::SubF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "*") => {
                        MirInstruction::MulF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "/") => {
                        MirInstruction::DivF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "%") => {
                        MirInstruction::RemF64 { dst, left, right }
                    }
                    _ => {
                        self.error("G6005", "operator type has no MIR arithmetic instruction");
                        return None;
                    }
                };
                self.instructions.push(instruction);
            }
            CoreKind::Binary {
                operator,
                left,
                right,
            } if matches!(operator.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=") => {
                let operand_ty = self.body.expression(left).ty.clone();
                let left = self.value(left)?;
                let right = self.value(right)?;
                let instruction = match (&operand_ty, operator.as_str()) {
                    (Type::Scalar(crate::types::ScalarType::I64), "==") => {
                        MirInstruction::EqI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), "!=") => {
                        MirInstruction::NeI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), "<") => {
                        MirInstruction::LtI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), "<=") => {
                        MirInstruction::LeI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), ">") => {
                        MirInstruction::GtI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::I64), ">=") => {
                        MirInstruction::GeI64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "==") => {
                        MirInstruction::EqF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "!=") => {
                        MirInstruction::NeF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "<") => {
                        MirInstruction::LtF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), "<=") => {
                        MirInstruction::LeF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), ">") => {
                        MirInstruction::GtF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::F64), ">=") => {
                        MirInstruction::GeF64 { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Bool), "==") => {
                        MirInstruction::EqBool { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Bool), "!=") => {
                        MirInstruction::NeBool { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Text), "==") => {
                        MirInstruction::EqText { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Text), "!=") => {
                        MirInstruction::NeText { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Char), "==") => {
                        MirInstruction::EqChar { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Char), "!=") => {
                        MirInstruction::NeChar { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Char), "<") => {
                        MirInstruction::LtChar { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Char), "<=") => {
                        MirInstruction::LeChar { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Char), ">") => {
                        MirInstruction::GtChar { dst, left, right }
                    }
                    (Type::Scalar(crate::types::ScalarType::Char), ">=") => {
                        MirInstruction::GeChar { dst, left, right }
                    }
                    _ => {
                        self.error("G6005", "comparison type has no MIR instruction");
                        return None;
                    }
                };
                self.instructions.push(instruction);
            }
            CoreKind::Call { callee, arguments } => {
                let direct_resumption = match &self.body.expression(callee).kind {
                    // An identity-bearing Core node can only be produced for
                    // a lexical alias of the currently active continuation.
                    // The direct lowering retains that snapshot in its state
                    // rather than materializing a callable register.
                    CoreKind::Resumption { .. } => self.direct_resumption.is_some(),
                    CoreKind::Local(name) => {
                        self.direct_resumption.as_ref().is_some_and(|resumption| {
                            resumption.name == *name && !self.named.contains_key(name)
                        })
                    }
                    _ => false,
                };
                if direct_resumption {
                    let [argument] = arguments.as_slice() else {
                        self.error("G6005", "direct resumption must be invoked with one value");
                        return None;
                    };
                    let argument = self.value(*argument)?;
                    let resumption = self
                        .direct_resumption
                        .as_mut()
                        .expect("direct resumption was established above");
                    resumption.calls = match resumption.calls.checked_add(1) {
                        Some(calls) => calls,
                        None => {
                            self.error("G6005", "direct resumption call count overflowed");
                            return None;
                        }
                    };
                    let plan = resumption.plan.clone();
                    match plan {
                        DirectResumptionPlan::Identity => {
                            self.instructions
                                .push(MirInstruction::Copy { dst, src: argument });
                        }
                        DirectResumptionPlan::RuntimeReplay => {
                            self.instructions.push(MirInstruction::ResumeReturn {
                                dst,
                                value: argument,
                            });
                        }
                        DirectResumptionPlan::PureResidual {
                            binding,
                            prefix,
                            result,
                        } => {
                            // Each finite replay gets a fresh lowering of the
                            // residual. Core IDs are intentionally shared by
                            // the source tree, so restore its memoized values
                            // afterward; retaining them would turn the next
                            // `k(value)` into an unsound reuse of the first.
                            let previous_named = self.named.clone();
                            let previous_values = self.values.clone();
                            self.named.insert(binding, argument);
                            for expression in prefix {
                                self.statement(expression)?;
                            }
                            let resumed = self.value(result)?;
                            self.named = previous_named;
                            self.values = previous_values;
                            self.instructions
                                .push(MirInstruction::Copy { dst, src: resumed });
                        }
                    }
                    self.values.insert(id, dst);
                    return Some(dst);
                }
                if matches!(
                    self.body.expression(callee).kind,
                    CoreKind::Resumption { .. }
                ) {
                    let [argument] = arguments.as_slice() else {
                        self.error(
                            "G6005",
                            "resumption snapshot must be invoked with one value",
                        );
                        return None;
                    };
                    let snapshot = self.value(callee)?;
                    let value = self.value(*argument)?;
                    self.instructions
                        .push(MirInstruction::ResumeSnapshot { snapshot, value });
                    self.values.insert(id, dst);
                    return Some(dst);
                }
                let arguments = arguments
                    .into_iter()
                    .map(|argument| self.value(argument))
                    .collect::<Option<Vec<_>>>()?;
                match self.body.expression(callee).kind.clone() {
                    CoreKind::Function {
                        definition: callee,
                        arguments: generic_arguments,
                    } => self.instructions.push(MirInstruction::Call {
                        dst,
                        callee,
                        generic_arguments,
                        trait_instance: None,
                        arguments,
                    }),
                    CoreKind::TraitMethod {
                        evidence,
                        method: callee,
                        trait_arguments,
                        method_arguments,
                    } => self.instructions.push(MirInstruction::Call {
                        dst,
                        callee,
                        generic_arguments: vec![],
                        trait_instance: Some(MirTraitMethodInstance {
                            evidence,
                            trait_arguments,
                            method_arguments,
                        }),
                        arguments,
                    }),
                    _ => {
                        let callee = self.value(callee)?;
                        self.instructions.push(MirInstruction::CallIndirect {
                            dst,
                            callee,
                            arguments,
                        });
                    }
                }
            }
            CoreKind::Closure {
                callable,
                parameters,
                environment,
                body,
            } => {
                let callee = self.lift_closure(
                    callable,
                    &environment,
                    parameters,
                    environment.captures.clone(),
                    body,
                )?;
                let captures = self.capture_environment(&environment)?;
                self.instructions.push(MirInstruction::MakeCallable {
                    dst,
                    callee,
                    captures,
                    generic_arguments: vec![],
                    trait_instance: None,
                    environment: Some(environment.brand),
                });
            }
            CoreKind::Block(values) => {
                let Some(last) = values.last().copied() else {
                    self.instructions.push(MirInstruction::ConstUnit { dst });
                    self.values.insert(id, dst);
                    return Some(dst);
                };
                for value in values.into_iter().take_while(|value| *value != last) {
                    self.statement(value)?;
                }
                let src = self.value(last)?;
                self.instructions.push(MirInstruction::Copy { dst, src });
            }
            // A label with no transfer is static scope evidence only and
            // erases to its body. A transfer itself deliberately fails closed
            // until MIR gains its checked cleanup-carrying leave terminator.
            CoreKind::Label { body, .. } => {
                let src = self.value(body)?;
                self.instructions.push(MirInstruction::Copy { dst, src });
            }
            CoreKind::Transfer { .. } => {
                self.error(
                    "G6012",
                    "MIR label transfer requires a cleanup-carrying nonlocal edge",
                );
                return None;
            }
            _ => {
                self.error("G6005", "Typed Core form has no MIR lowering yet");
                return None;
            }
        };
        self.values.insert(id, dst);
        Some(dst)
    }
    /// The first executable handler lowering path. Terminal operations have no
    /// continuation, so a statically selected irrefutable arm can lower to its
    /// clause body without inventing a fake resumption or allowing the
    /// abandoned continuation to continue normally. Resumptive and refutable
    /// dispatch proceeds through the forthcoming handler-stack CFG lowering.
    fn lower_terminal_handle(
        &mut self,
        dst: MirLocal,
        computation: CoreId,
        clauses: Vec<CoreHandlerClause>,
    ) -> Option<()> {
        let (effect, operation, arguments) = self.terminal_operation(computation)?;
        let Some(clause) = clauses.iter().find(|clause| {
            clause.terminal && clause.effect == effect && clause.operation == operation
        }) else {
            self.error(
                "G6005",
                "terminal operation has no matching handler clause during MIR lowering",
            );
            return None;
        };
        if clause.patterns.len() != arguments.len()
            || !clause.patterns.iter().all(pattern_is_irrefutable)
        {
            self.error(
                "G6005",
                "refutable terminal handler dispatch requires pattern-matrix CFG lowering",
            );
            return None;
        }
        if !matches!(clause.resumption, CoreHandlerResumption::Terminal) {
            self.error(
                "G6005",
                "terminal handler clause unexpectedly carries a resumption",
            );
            return None;
        }
        let arguments = arguments
            .into_iter()
            .map(|argument| self.value(argument))
            .collect::<Option<Vec<_>>>()?;
        let previous = self.named.clone();
        self.bind_handler_patterns(&clause.patterns, &arguments)?;
        let body = self.value(clause.body)?;
        self.named = previous;
        self.instructions
            .push(MirInstruction::Copy { dst, src: body });
        Some(())
    }
    fn direct_operation(
        &mut self,
        computation: CoreId,
    ) -> Option<(crate::EffectInstance, u32, Vec<CoreId>)> {
        match self.body.expression(computation).kind.clone() {
            CoreKind::Perform {
                effect,
                operation,
                arguments,
                ..
            } => Some((effect, operation, arguments)),
            CoreKind::Block(values) => {
                let Some((last, prefix)) = values.split_last() else {
                    self.error(
                        "G6005",
                        "empty handler computation cannot select a terminal arm",
                    );
                    return None;
                };
                for value in prefix {
                    self.statement(*value)?;
                }
                self.direct_operation(*last)
            }
            CoreKind::Call { callee, arguments } => {
                let definition = match self.body.expression(callee).kind {
                    CoreKind::Function { definition, .. }
                    | CoreKind::TraitMethod {
                        method: definition, ..
                    } => definition,
                    _ => {
                        self.error(
                        "G6005",
                        "handler-stack lowering is required for an indirect handler computation",
                    );
                        return None;
                    }
                };
                self.direct_known_perform(definition, arguments)
            }
            _ => {
                self.error(
                    "G6005",
                    "handler-stack lowering is required for indirect handler computations",
                );
                None
            }
        }
    }
    /// Expand the narrow interprocedural case that is structurally identical
    /// to a direct performance: a named callee with one `Perform` root and
    /// operation arguments that resolve to its formal parameters. A block may
    /// contain local-to-local aliases before that performance, including a
    /// permutation of the parameters. Those aliases have no runtime work and
    /// do not duplicate or discard a caller value, so replacing the helper
    /// call with the performance preserves evaluation and ownership. More
    /// general setup still requires the runtime handler/continuation stack.
    fn direct_known_perform(
        &self,
        definition: DefKey,
        arguments: Vec<CoreId>,
    ) -> Option<(crate::EffectInstance, u32, Vec<CoreId>)> {
        let body = self.bodies.get(&definition)?;
        if body.parameters.len() != arguments.len() {
            return None;
        }
        let mut parameter_positions = body
            .parameters
            .iter()
            .enumerate()
            .map(|(position, (name, _))| (name.clone(), position))
            .collect::<BTreeMap<_, _>>();
        let performed_root = match body.expression(body.root).kind.clone() {
            CoreKind::Perform { .. } => body.root,
            CoreKind::Block(values) => {
                let (last, prefix) = values.split_last()?;
                for binding in prefix {
                    let CoreKind::Let { name, value } = body.expression(*binding).kind.clone()
                    else {
                        return None;
                    };
                    let CoreKind::Local(source) = body.expression(value).kind.clone() else {
                        return None;
                    };
                    let position = *parameter_positions.get(&source)?;
                    parameter_positions.insert(name, position);
                }
                *last
            }
            _ => return None,
        };
        let CoreKind::Perform {
            effect,
            operation,
            arguments: performed,
            ..
        } = body.expression(performed_root).kind.clone()
        else {
            return None;
        };
        let effect =
            instantiate_interprocedural_effect(effect, &body.parameters, self.body, &arguments)?;
        if performed.len() != arguments.len() {
            return None;
        }
        let forwarded = performed
            .into_iter()
            .map(|value| match body.expression(value).kind.clone() {
                CoreKind::Local(name) => parameter_positions.get(&name).copied(),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        // This static rewrite is only valid when every caller argument stays
        // represented exactly once. Core and PlaceFlow retain the authority
        // for more general duplication, dropping, and borrowing decisions.
        let mut covered = forwarded.clone();
        covered.sort_unstable();
        if covered != (0..arguments.len()).collect::<Vec<_>>() {
            return None;
        }
        let arguments = forwarded
            .into_iter()
            .map(|position| arguments[position])
            .collect();
        Some((effect, operation, arguments))
    }
    /// Classify the syntactically direct root shape without elaborating its
    /// prefix. The lowering path that claims the shape owns evaluation order;
    /// this probe merely distinguishes it from a provably ordinary
    /// computation wrapped by a handler literal.
    fn has_direct_perform(&self, computation: CoreId) -> bool {
        match self.body.expression(computation).kind.clone() {
            CoreKind::Perform { .. } => true,
            CoreKind::Block(values) => values
                .last()
                .is_some_and(|value| self.has_direct_perform(*value)),
            CoreKind::Call { callee, arguments } => {
                matches!(self.body.expression(callee).kind, CoreKind::Function { definition, .. }
                    | CoreKind::TraitMethod { method: definition, .. }
                    if self.direct_known_perform(definition, arguments.clone()).is_some())
            }
            _ => false,
        }
    }
    /// A finite static replay duplicates this expression once for every
    /// continuation use. Keep the proof intentionally narrower than ordinary
    /// effect-freedom: a move, unique loan, assignment, or moving closure
    /// capture would duplicate an ownership action even if it cannot perform
    /// an effect. The general VM continuation representation owns those cases
    /// once it can describe snapshot copy glue to the verifier.
    fn core_is_replay_safe(&self, id: CoreId) -> bool {
        match self.body.expression(id).kind.clone() {
            CoreKind::Literal(_)
            | CoreKind::Local(_)
            | CoreKind::Resumption { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. } => true,
            CoreKind::Constant(_)
            | CoreKind::Error
            | CoreKind::Perform { .. }
            | CoreKind::Handle { .. }
            | CoreKind::Completion { .. }
            | CoreKind::Assign { .. }
            | CoreKind::Move(_) => false,
            CoreKind::Closure { environment, .. } => environment.captures.iter().all(|capture| {
                !matches!(capture.mode, CaptureMode::Move | CaptureMode::UniqueBorrow)
            }),
            CoreKind::Borrow { unique, value } => !unique && self.core_is_replay_safe(value),
            CoreKind::Deref(value) => self.core_is_replay_safe(value),
            CoreKind::Unary { value, .. }
            | CoreKind::Field { base: value, .. }
            | CoreKind::PatternTest { subject: value, .. } => self.core_is_replay_safe(value),
            CoreKind::Let { value, .. } => self.core_is_replay_safe(value),
            CoreKind::Label { body, .. } => self.core_is_replay_safe(body),
            CoreKind::Transfer { .. } => false,
            CoreKind::Binary { left, right, .. } => {
                self.core_is_replay_safe(left) && self.core_is_replay_safe(right)
            }
            CoreKind::Tuple(values) | CoreKind::Array(values) | CoreKind::Block(values) => values
                .into_iter()
                .all(|value| self.core_is_replay_safe(value)),
            CoreKind::Record { fields, .. } | CoreKind::Enum { fields, .. } => fields
                .into_iter()
                .all(|field| self.core_is_replay_safe(field)),
            CoreKind::Call { callee, arguments } => {
                self.core_is_effect_free(id)
                    && self.core_is_replay_safe(callee)
                    && arguments
                        .into_iter()
                        .all(|argument| self.core_is_replay_safe(argument))
            }
        }
    }
    /// A deliberately conservative proof used only to erase an unexercised
    /// handler scope. It never treats a nested handler, a performance, an
    /// unknown callable, or a callable with a nonempty/open effect row as
    /// effect-free. This is not a replacement for dynamic handler lowering.
    fn core_is_effect_free(&self, id: CoreId) -> bool {
        match self.body.expression(id).kind.clone() {
            CoreKind::Literal(_)
            | CoreKind::Local(_)
            | CoreKind::Resumption { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. } => true,
            CoreKind::Constant(_)
            | CoreKind::Error
            | CoreKind::Perform { .. }
            | CoreKind::Handle { .. }
            | CoreKind::Completion { .. } => false,
            CoreKind::Tuple(values) | CoreKind::Array(values) | CoreKind::Block(values) => values
                .into_iter()
                .all(|value| self.core_is_effect_free(value)),
            CoreKind::Record { fields, .. } | CoreKind::Enum { fields, .. } => fields
                .into_iter()
                .all(|field| self.core_is_effect_free(field)),
            CoreKind::Field { base, .. }
            | CoreKind::PatternTest { subject: base, .. }
            | CoreKind::Move(base)
            | CoreKind::Borrow { value: base, .. }
            | CoreKind::Deref(base)
            | CoreKind::Unary { value: base, .. } => self.core_is_effect_free(base),
            CoreKind::Let { value, .. } | CoreKind::Assign { value, .. } => {
                self.core_is_effect_free(value)
            }
            CoreKind::Label { body, .. } => self.core_is_effect_free(body),
            CoreKind::Transfer { .. } => false,
            CoreKind::Binary { left, right, .. } => {
                self.core_is_effect_free(left) && self.core_is_effect_free(right)
            }
            CoreKind::Closure { .. } => true,
            CoreKind::Call { callee, arguments } => {
                self.core_is_effect_free(callee)
                    && arguments
                        .into_iter()
                        .all(|argument| self.core_is_effect_free(argument))
                    && matches!(
                        &self.body.expression(callee).ty,
                        Type::Callable { effects, .. }
                            if effects.effects.is_empty() && effects.tail.is_none()
                    )
            }
        }
    }
    fn terminal_operation(
        &mut self,
        computation: CoreId,
    ) -> Option<(crate::EffectInstance, u32, Vec<CoreId>)> {
        match self.body.expression(computation).kind.clone() {
            CoreKind::Perform { terminal: true, .. } => self.direct_operation(computation),
            CoreKind::Block(values) | CoreKind::Tuple(values) | CoreKind::Array(values) => self
                .terminal_in_strict_values(
                    values,
                    "terminal computation has no reachable terminal performance",
                ),
            CoreKind::Record { fields, .. } | CoreKind::Enum { fields, .. } => self
                .terminal_in_strict_values(
                    fields,
                    "terminal aggregate construction has no reachable terminal performance",
                ),
            CoreKind::Call { callee, arguments } => {
                let mut values = vec![callee];
                values.extend(arguments.clone());
                if values
                    .iter()
                    .any(|value| matches!(&self.body.expression(*value).ty, Type::Never))
                {
                    return self.terminal_in_strict_values(
                        values,
                        "terminal call has no reachable terminal operand",
                    );
                }
                let definition = match self.body.expression(callee).kind {
                    CoreKind::Function { definition, .. }
                    | CoreKind::TraitMethod {
                        method: definition, ..
                    } => definition,
                    _ => {
                        self.error("G6005", "terminal call requires handler-stack lowering");
                        return None;
                    }
                };
                self.direct_known_perform(definition, arguments)
            }
            CoreKind::Borrow { value, .. }
            | CoreKind::Deref(value)
            | CoreKind::Move(value)
            | CoreKind::Unary { value, .. }
            | CoreKind::Field { base: value, .. }
            | CoreKind::PatternTest { subject: value, .. }
            | CoreKind::Let { value, .. }
            | CoreKind::Assign { value, .. } => self.terminal_operation(value),
            _ => {
                self.error(
                    "G6005",
                    "terminal handler lowering received a resumptive operation",
                );
                None
            }
        }
    }
    /// Find the first non-returning child of a strict expression while still
    /// lowering every earlier child in source order.  The Core type has
    /// already established that this child is `Never`; later children are
    /// unreachable and must not be emitted as ordinary VM work.
    fn terminal_in_strict_values(
        &mut self,
        values: Vec<CoreId>,
        missing: &'static str,
    ) -> Option<(crate::EffectInstance, u32, Vec<CoreId>)> {
        for value in values {
            if matches!(&self.body.expression(value).ty, Type::Never) {
                return self.terminal_operation(value);
            }
            self.statement(value)?;
        }
        self.error("G6005", missing);
        None
    }
    fn alloc(&mut self, ty: Type, source: CoreId) -> MirLocal {
        let id = MirLocal(self.locals.len() as u32);
        self.locals.push(MirLocalDecl { ty, source });
        id
    }
    fn statement(&mut self, id: CoreId) -> Option<()> {
        self.value(id).map(|_| ())
    }
    /// Resolve a Typed Core value place to its stable runtime root and field
    /// path.  This refuses computed values: a borrow may never be lowered as
    /// a hidden copy of a temporary.
    fn reference_place(&mut self, id: CoreId) -> Option<(MirLocal, Vec<u32>)> {
        match self.body.expression(id).kind.clone() {
            CoreKind::Local(name) => self.named.get(&name).copied().map(|local| (local, vec![])),
            CoreKind::Field { base, index, .. } => {
                let (root, mut fields) = self.reference_place(base)?;
                fields.push(index);
                Some((root, fields))
            }
            _ => None,
        }
    }
    fn read_place(&mut self, place: &crate::CorePlace) -> Option<MirLocal> {
        match place {
            crate::CorePlace::Local { name, .. } => self.named.get(name).copied().or_else(|| {
                self.error("G6009", "MIR place refers to an unknown local");
                None
            }),
            crate::CorePlace::Field {
                base,
                index,
                field_count,
                ty,
            } => {
                let base = self.read_place(base)?;
                let dst = self.alloc(ty.clone(), CoreId(u32::MAX));
                self.instructions.push(MirInstruction::ProjectRecord {
                    dst,
                    base,
                    index: *index,
                    field_count: *field_count,
                    field_type: ty.clone(),
                });
                Some(dst)
            }
            crate::CorePlace::Deref { reference, .. } => {
                let reference = self.value(*reference)?;
                let dst = self.alloc(place.ty(), CoreId(u32::MAX));
                self.instructions
                    .push(MirInstruction::DerefCopy { dst, reference });
                Some(dst)
            }
            crate::CorePlace::Error => {
                self.error("G6009", "MIR assignment place is recovered");
                None
            }
        }
    }
    fn store_place(&mut self, place: &crate::CorePlace, value: MirLocal) -> Option<()> {
        match place {
            crate::CorePlace::Local { name, .. } => {
                let Some(dst) = self.named.get(name).copied() else {
                    self.error("G6009", "MIR assignment refers to an unknown local");
                    return None;
                };
                self.instructions
                    .push(MirInstruction::Store { dst, src: value });
                Some(())
            }
            crate::CorePlace::Field {
                base,
                index,
                field_count,
                ty,
            } => {
                let base_value = self.read_place(base)?;
                let updated = self.alloc(base.ty(), CoreId(u32::MAX));
                self.instructions.push(MirInstruction::UpdateRecord {
                    dst: updated,
                    base: base_value,
                    index: *index,
                    field_count: *field_count,
                    value,
                    field_type: ty.clone(),
                });
                self.store_place(base, updated)
            }
            crate::CorePlace::Deref {
                reference, unique, ..
            } => {
                if !unique {
                    self.error("G6010", "MIR store through shared reference");
                    return None;
                }
                let reference = self.value(*reference)?;
                self.instructions.push(MirInstruction::DerefStore {
                    reference,
                    src: value,
                });
                Some(())
            }
            crate::CorePlace::Error => {
                self.error("G6009", "MIR assignment place is recovered");
                None
            }
        }
    }
    fn capture_environment(
        &mut self,
        capture_environment: &CaptureEnvironment,
    ) -> Option<Vec<MirLocal>> {
        if !capture_environment.sealed {
            self.error(
                "G6011",
                "MIR lowering received an unsealed callable environment",
            );
            return None;
        }
        if capture_environment.post_states.len() != capture_environment.captures.len()
            || capture_environment
                .captures
                .iter()
                .zip(&capture_environment.post_states)
                .any(|(capture, state)| capture.name != state.name || capture.mode != state.mode)
        {
            self.error(
                "G6011",
                "MIR lowering received a callable environment with inconsistent capture post-states",
            );
            return None;
        }
        let mut environment = Vec::with_capacity(capture_environment.captures.len());
        for (capture, post_state) in capture_environment
            .captures
            .iter()
            .zip(&capture_environment.post_states)
        {
            let Some(local) = self.named.get(&capture.name).copied() else {
                self.error("G6007", "closure capture has no MIR local");
                return None;
            };
            // PlaceFlow owns the capture-mode decision.  Keep an actual move
            // in MIR when it selected one; shared/unique runtime references
            // have not reached Stage 0's value representation yet, and the
            // currently immutable scalar values are copied into the closure
            // environment.
            let local = if post_state.mode == CaptureMode::Move {
                let moved = self.alloc(capture.ty.clone(), CoreId(u32::MAX));
                self.instructions.push(MirInstruction::Move {
                    dst: moved,
                    src: local,
                });
                moved
            } else {
                local
            };
            environment.push(local);
        }
        Some(environment)
    }
    fn lift_closure(
        &mut self,
        callable: CallableId,
        environment: &CaptureEnvironment,
        parameters: Vec<(String, Type)>,
        captures: Vec<ClosureCapture>,
        body: CoreId,
    ) -> Option<DefKey> {
        if environment.brand.owner != self.definition || environment.brand.callable != callable {
            self.error(
                "G6011",
                "callable environment brand does not belong to the closure being lifted",
            );
            return None;
        }
        let callable_bytes = callable.0.to_le_bytes();
        let definition = DefKey(Digest::of_parts([
            b"grandiose-stage0-lifted-callable".as_slice(),
            self.definition.0.as_bytes().as_slice(),
            callable_bytes.as_slice(),
        ]));
        if self.lifted.contains_key(&definition) {
            return Some(definition);
        }
        let mut child = Lowerer {
            body: self.body,
            bodies: self.bodies,
            definition,
            locals: vec![],
            values: BTreeMap::new(),
            named: BTreeMap::new(),
            lifted: BTreeMap::new(),
            instructions: vec![],
            diagnostics: vec![],
            leave_cleanup: MirCleanupPlan {
                moved_places: vec![],
                active_loans: vec![],
            },
            resumption_snapshots: BTreeMap::new(),
            label_rejoins: BTreeMap::new(),
            direct_resumption: None,
        };
        let mut lifted_parameters = Vec::with_capacity(captures.len() + parameters.len());
        for capture in &captures {
            let local = child.alloc(capture.ty.clone(), CoreId(u32::MAX));
            child.named.insert(capture.name.clone(), local);
            lifted_parameters.push(local);
        }
        for (name, ty) in &parameters {
            let local = child.alloc(ty.clone(), CoreId(u32::MAX));
            child.named.insert(name.clone(), local);
            lifted_parameters.push(local);
        }
        let Some(root) = child.value(body) else {
            self.diagnostics.extend(child.diagnostics);
            return None;
        };
        if !child.diagnostics.is_empty() {
            self.diagnostics.extend(child.diagnostics);
            return None;
        }
        let function = MirFunction {
            definition,
            captures: captures.len() as u32,
            parameters: lifted_parameters,
            locals: child.locals,
            result: self.body.expression(body).ty.clone(),
            entry: MirBlockId(0),
            blocks: vec![MirBlock {
                parameters: vec![],
                instructions: child.instructions,
                terminator: MirTerminator::Return { value: root },
            }],
        };
        if let Err(message) = function.validate() {
            self.error("G6002", &message);
            return None;
        }
        if self.lifted.insert(definition, function).is_some() {
            self.error("G6008", "lifted callable identity collision");
            return None;
        }
        self.lifted.extend(child.lifted);
        Some(definition)
    }
    fn error(&mut self, code: &'static str, message: &str) {
        self.diagnostics.push(MirDiagnostic {
            code,
            message: message.into(),
        })
    }
}

fn pattern_is_irrefutable(pattern: &CorePattern) -> bool {
    match pattern {
        CorePattern::Any | CorePattern::Bind { .. } => true,
        CorePattern::Tuple(values) => values.iter().all(pattern_is_irrefutable),
        CorePattern::Record { fields, .. } => fields
            .iter()
            .all(|field| pattern_is_irrefutable(&field.pattern)),
        CorePattern::Literal(_) | CorePattern::Enum { .. } | CorePattern::Error => false,
    }
}

/// Instantiate a callee-owned effect identity at the direct call site. This
/// is intentionally independent of the source signature layer: MIR only sees
/// frozen Core bodies, so it proves the substitution from the callee parameter
/// types and the already-typed caller argument expressions.
fn instantiate_interprocedural_effect(
    effect: crate::EffectInstance,
    parameters: &[(String, Type)],
    caller: &TypedBody,
    arguments: &[CoreId],
) -> Option<crate::EffectInstance> {
    if parameters.len() != arguments.len() {
        return None;
    }
    let mut substitutions = BTreeMap::new();
    for ((_, template), argument) in parameters.iter().zip(arguments) {
        collect_generic_substitutions(
            template,
            &caller.expression(*argument).ty,
            &mut substitutions,
        )?;
    }
    Some(crate::EffectInstance {
        definition: effect.definition,
        arguments: effect
            .arguments
            .into_iter()
            .map(|argument| substitute_generic_argument(argument, &substitutions))
            .collect::<Option<_>>()?,
    })
}

fn collect_generic_substitutions(
    template: &Type,
    actual: &Type,
    substitutions: &mut BTreeMap<u32, Type>,
) -> Option<()> {
    match (template, actual) {
        (Type::Generic(index), actual) => match substitutions.get(index) {
            Some(previous) if previous != actual => None,
            Some(_) => Some(()),
            None => {
                substitutions.insert(*index, actual.clone());
                Some(())
            }
        },
        (
            Type::Nominal {
                definition,
                arguments,
            },
            Type::Nominal {
                definition: actual_definition,
                arguments: actual_arguments,
            },
        ) if definition == actual_definition && arguments.len() == actual_arguments.len() => {
            arguments
                .iter()
                .zip(actual_arguments)
                .try_for_each(|(template, actual)| {
                    collect_generic_argument_substitutions(template, actual, substitutions)
                        .ok_or(())
                })
                .ok()
        }
        (Type::Tuple(values), Type::Tuple(actual_values))
            if values.len() == actual_values.len() =>
        {
            values
                .iter()
                .zip(actual_values)
                .try_for_each(|(template, actual)| {
                    collect_generic_substitutions(template, actual, substitutions).ok_or(())
                })
                .ok()
        }
        (Type::Array(value), Type::Array(actual)) => {
            collect_generic_substitutions(value, actual, substitutions)
        }
        (
            Type::Reference {
                mutability,
                lifetime,
                referent,
            },
            Type::Reference {
                mutability: actual_mutability,
                lifetime: actual_lifetime,
                referent: actual_referent,
            },
        ) if mutability == actual_mutability && lifetime == actual_lifetime => {
            collect_generic_substitutions(referent, actual_referent, substitutions)
        }
        // Callable parameters can carry independent generic effect rows. They
        // are outside this direct-performance proof until their own effect
        // identity has a dedicated substitution witness.
        (Type::Callable { .. }, Type::Callable { .. }) => (template == actual).then_some(()),
        _ => (template == actual).then_some(()),
    }
}

fn substitute_generic_type(value: Type, substitutions: &BTreeMap<u32, Type>) -> Option<Type> {
    match value {
        Type::Generic(index) => substitutions.get(&index).cloned(),
        Type::Nominal {
            definition,
            arguments,
        } => Some(Type::Nominal {
            definition,
            arguments: arguments
                .into_iter()
                .map(|argument| substitute_generic_argument(argument, substitutions))
                .collect::<Option<_>>()?,
        }),
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_arguments,
        } => Some(Type::Projection {
            subject: Box::new(substitute_generic_type(*subject, substitutions)?),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|argument| substitute_generic_type(argument, substitutions))
                .collect::<Option<_>>()?,
            name,
            item_arguments: item_arguments
                .into_iter()
                .map(|argument| substitute_generic_type(argument, substitutions))
                .collect::<Option<_>>()?,
        }),
        Type::Tuple(values) => Some(Type::Tuple(
            values
                .into_iter()
                .map(|value| substitute_generic_type(value, substitutions))
                .collect::<Option<_>>()?,
        )),
        Type::Array(value) => Some(Type::Array(Box::new(substitute_generic_type(
            *value,
            substitutions,
        )?))),
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Some(Type::Reference {
            mutability,
            lifetime,
            referent: Box::new(substitute_generic_type(*referent, substitutions)?),
        }),
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Some(Type::Callable {
            lifetime_binders,
            parameters: parameters
                .into_iter()
                .map(|parameter| substitute_generic_type(parameter, substitutions))
                .collect::<Option<_>>()?,
            result: Box::new(substitute_generic_type(*result, substitutions)?),
            effects: substitute_generic_effect_row(effects, substitutions)?,
            invocation,
        }),
        value => Some(value),
    }
}

fn generic_contract_matches(
    expected: &GenericArgument,
    actual: &GenericArgument,
    substitutions: &mut BTreeMap<u32, Type>,
) -> bool {
    match (expected, actual) {
        (GenericArgument::Type(expected), GenericArgument::Type(actual)) => {
            type_contract_matches(expected, actual, substitutions)
        }
        _ => expected == actual,
    }
}

fn collect_generic_argument_substitutions(
    template: &GenericArgument,
    actual: &GenericArgument,
    substitutions: &mut BTreeMap<u32, Type>,
) -> Option<()> {
    match (template, actual) {
        (GenericArgument::Type(template), GenericArgument::Type(actual)) => {
            collect_generic_substitutions(template, actual, substitutions)
        }
        (template, actual) if template == actual => Some(()),
        _ => None,
    }
}

fn substitute_generic_argument(
    value: crate::GenericArgument,
    substitutions: &BTreeMap<u32, Type>,
) -> Option<crate::GenericArgument> {
    match value {
        crate::GenericArgument::Type(value) => {
            substitute_generic_type(value, substitutions).map(crate::GenericArgument::Type)
        }
        crate::GenericArgument::EffectRow(value) => {
            substitute_generic_effect_row(value, substitutions)
                .map(crate::GenericArgument::EffectRow)
        }
        value => Some(value),
    }
}

fn substitute_generic_effect_row(
    value: crate::EffectRow,
    substitutions: &BTreeMap<u32, Type>,
) -> Option<crate::EffectRow> {
    Some(crate::EffectRow {
        effects: value
            .effects
            .into_iter()
            .map(|effect| {
                Some(crate::EffectInstance {
                    definition: effect.definition,
                    arguments: effect
                        .arguments
                        .into_iter()
                        .map(|argument| substitute_generic_argument(argument, substitutions))
                        .collect::<Option<_>>()?,
                })
            })
            .collect::<Option<BTreeSet<_>>>()?,
        projections: value
            .projections
            .into_iter()
            .map(|projection| {
                Some(crate::EffectRowProjection {
                    subject: Box::new(substitute_generic_type(*projection.subject, substitutions)?),
                    trait_definition: projection.trait_definition,
                    trait_arguments: projection
                        .trait_arguments
                        .into_iter()
                        .map(|argument| substitute_generic_type(argument, substitutions))
                        .collect::<Option<_>>()?,
                    name: projection.name,
                    item_arguments: projection
                        .item_arguments
                        .into_iter()
                        .map(|argument| substitute_generic_type(argument, substitutions))
                        .collect::<Option<_>>()?,
                })
            })
            .collect::<Option<_>>()?,
        tail: value.tail,
    })
}

fn lower_pattern(value: CorePattern) -> Option<MirPattern> {
    match value {
        CorePattern::Any | CorePattern::Bind { .. } => Some(MirPattern::Any),
        CorePattern::Literal(value) => Some(MirPattern::Literal(value)),
        CorePattern::Tuple(values) => values
            .into_iter()
            .map(lower_pattern)
            .collect::<Option<Vec<_>>>()
            .map(MirPattern::Tuple),
        CorePattern::Record {
            definition, fields, ..
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
            .map(|fields| MirPattern::Record { definition, fields }),
        CorePattern::Enum {
            definition,
            variant,
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
                fields,
            }),
        CorePattern::Error => None,
    }
}

fn validate_pattern(pattern: &MirPattern, subject: &Type) -> Result<(), String> {
    match pattern {
        MirPattern::Any => Ok(()),
        MirPattern::Literal(value) if literal_type(value) == *subject => Ok(()),
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
        MirPattern::Record { definition, fields } => match subject {
            Type::Nominal {
                definition: actual, ..
            } if actual == definition => validate_pattern_fields(fields),
            _ => Err("MIR record pattern has an incompatible subject type".into()),
        },
        MirPattern::Enum {
            definition, fields, ..
        } => match subject {
            Type::Nominal {
                definition: actual, ..
            } if actual == definition => validate_pattern_fields(fields),
            _ => Err("MIR enum pattern has an incompatible subject type".into()),
        },
    }
}

fn validate_pattern_fields(fields: &[MirPatternField]) -> Result<(), String> {
    let mut previous = None;
    for field in fields {
        if previous.is_some_and(|previous| previous >= field.index) {
            return Err("MIR pattern fields are not strictly ordered".into());
        }
        previous = Some(field.index);
        validate_pattern(&field.pattern, &field.ty)?;
    }
    Ok(())
}

fn literal_type(text: &str) -> Type {
    if matches!(text, "true" | "false") {
        Type::Scalar(crate::types::ScalarType::Bool)
    } else if text.starts_with('"') {
        Type::Scalar(crate::types::ScalarType::Text)
    } else if text.starts_with('\'') {
        Type::Scalar(crate::types::ScalarType::Char)
    } else if text.contains('.') || text.contains('e') || text.contains('E') {
        Type::Scalar(crate::types::ScalarType::F64)
    } else {
        Type::Scalar(crate::types::ScalarType::I64)
    }
}

/// Lexing has already validated integer structure.  MIR still performs a
/// checked conversion so an out-of-range source value cannot wrap while it is
/// becoming the stage-zero VM's i64 representation.
fn parse_i64_literal(text: &str) -> Result<i64, ()> {
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
    i64::from_str_radix(digits, radix).map_err(|_| ())
}

fn parse_f64_literal(text: &str) -> Result<f64, ()> {
    text.replace('_', "").parse::<f64>().map_err(|_| ())
}

/// Source lexing validates literal escape structure. MIR decodes it again so
/// the emitted artifact contains a scalar value rather than source spelling.
fn parse_char_literal(text: &str) -> Result<u32, ()> {
    let Some(body) = text
        .strip_prefix('\'')
        .and_then(|value| value.strip_suffix('\''))
    else {
        return Err(());
    };
    let mut values = body.chars();
    let value = match values.next() {
        Some('\\') => match values.next() {
            Some('n') => '\n',
            Some('r') => '\r',
            Some('t') => '\t',
            Some('0') => '\0',
            Some('\\') => '\\',
            Some('\'') => '\'',
            Some('"') => '"',
            Some('x') => {
                let digits = values.by_ref().take(2).collect::<String>();
                let scalar = u32::from_str_radix(&digits, 16).map_err(|_| ())?;
                char::from_u32(scalar).ok_or(())?
            }
            Some('u') => {
                if values.next() != Some('{') {
                    return Err(());
                }
                let digits = values
                    .by_ref()
                    .take_while(|value| *value != '}')
                    .collect::<String>();
                char::from_u32(u32::from_str_radix(&digits, 16).map_err(|_| ())?).ok_or(())?
            }
            _ => return Err(()),
        },
        Some(value) => value,
        None => return Err(()),
    };
    if values.next().is_some() {
        return Err(());
    }
    Ok(value as u32)
}

fn parse_text_literal(text: &str) -> Result<String, ()> {
    let Some(body) = text
        .strip_prefix('"')
        .and_then(|value| value.strip_suffix('"'))
    else {
        return Err(());
    };
    let mut values = body.chars().peekable();
    let mut result = String::new();
    while let Some(value) = values.next() {
        let value = if value == '\\' {
            match values.next() {
                Some('n') => '\n',
                Some('r') => '\r',
                Some('t') => '\t',
                Some('0') => '\0',
                Some('\\') => '\\',
                Some('\'') => '\'',
                Some('"') => '"',
                Some('x') => {
                    let digits = values.by_ref().take(2).collect::<String>();
                    char::from_u32(u32::from_str_radix(&digits, 16).map_err(|_| ())?).ok_or(())?
                }
                Some('u') => {
                    if values.next() != Some('{') {
                        return Err(());
                    }
                    let digits = values
                        .by_ref()
                        .take_while(|value| *value != '}')
                        .collect::<String>();
                    char::from_u32(u32::from_str_radix(&digits, 16).map_err(|_| ())?).ok_or(())?
                }
                _ => return Err(()),
            }
        } else {
            value
        };
        result.push(value);
    }
    Ok(result)
}
