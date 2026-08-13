//! Ownership-aware MIR lowered only from Typed Core and PlaceFlow.

use crate::{
    core::{
        CallableId, CaptureMode, ClosureCapture, CoreCompletionClause, CoreHandlerClause,
        CoreHandlerResumption, CoreId, CoreKind, CorePattern, TypedBody,
    },
    identity::{DefKey, Digest},
    placeflow::PlaceFlow,
    types::Type,
};
use std::collections::{BTreeMap, BTreeSet};

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
        effect_arguments: Vec<Type>,
        operation: u32,
        arguments: Vec<MirLocal>,
    },
    /// Install a lexical one-shot handler frame. The VM stores the protected
    /// continuation at a matching `Perform` and transfers to `target`; a
    /// `Resume` re-enters that continuation with deep reinstatement.
    InstallHandler {
        effect: DefKey,
        effect_arguments: Vec<Type>,
        operation: u32,
        payload_destinations: Vec<MirLocal>,
        resume_type: Type,
        target: MirBlockId,
    },
    UninstallHandler,
    Resume {
        value: MirLocal,
    },
    /// Decline the innermost suspended handler clause and re-perform its
    /// original operation against the next outer matching frame. The VM keeps
    /// the declined frame in the resumed continuation, which is the deep
    /// forwarding counterpart of `Resume`.
    Forward,
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
        arguments: Vec<MirLocal>,
    },
    /// Materialize a lifted callable together with its ordered environment.
    /// The target's capture parameters occupy the prefix of its parameter
    /// list, before ordinary invocation parameters.
    MakeCallable {
        dst: MirLocal,
        callee: DefKey,
        captures: Vec<MirLocal>,
    },
    CallIndirect {
        dst: MirLocal,
        callee: MirLocal,
        arguments: Vec<MirLocal>,
    },
}
/// Explicit control edge for a MIR basic block. Block parameters are the only
/// phi mechanism; every edge carries an exactly typed argument list.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MirTerminator {
    Goto {
        target: MirBlockId,
        arguments: Vec<MirLocal>,
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
/// Deterministic local constant propagation over validated MIR.
///
/// Arithmetic folds only use checked operations, so overflow and division by
/// zero remain explicit VM traps. Transformations commit through `MirEditor`;
/// failed validation restores the unmodified graph.
pub fn optimize(function: MirFunction) -> Result<(MirFunction, MirOptimizationReport), String> {
    let mut editor = MirEditor::open(function)?;
    let mut report = MirOptimizationReport::default();
    let block_count = editor.function.blocks.len();
    for index in 0..block_count {
        let block = editor.function.blocks[index].clone();
        let (instructions, constants, folds) = fold_block(block.instructions);
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
#[derive(Clone, Copy, Debug)]
enum Constant {
    I64(i64),
    Bool(bool),
}
fn fold_block(
    instructions: Vec<MirInstruction>,
) -> (Vec<MirInstruction>, BTreeMap<MirLocal, Constant>, u32) {
    let mut constants = BTreeMap::new();
    let mut output = Vec::with_capacity(instructions.len());
    let mut folds = 0;
    for original in instructions {
        let folded = match original.clone() {
            MirInstruction::Copy { dst, src } => constant_instruction(dst, constants.get(&src)),
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
            MirInstruction::ConstBool { dst, value } => {
                constants.insert(dst, Constant::Bool(value));
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
        Some(Constant::Bool(value)) => Some(MirInstruction::ConstBool { dst, value: *value }),
        None => None,
    }
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
        | MirInstruction::CallIndirect { dst, .. } => Some(*dst),
        MirInstruction::InstallHandler { .. }
        | MirInstruction::UninstallHandler
        | MirInstruction::Resume { .. }
        | MirInstruction::Forward => None,
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
        if let Some(function) = lowerer.lower_root_linear_resumptions(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = function.validate() {
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
            lowerer.lower_root_runtime_one_shot_resumption(body.root, parameters.clone())
        {
            if lowerer.diagnostics.is_empty() {
                if let Err(message) = function.validate() {
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
                if let Err(message) = function.validate() {
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
                if let Err(message) = function.validate() {
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
                if let Err(message) = function.validate() {
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
                if let Err(message) = function.validate() {
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
                if let Err(message) = function.validate() {
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
                if let Err(message) = function.validate() {
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
                if let Err(message) = function.validate() {
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
            if let Err(message) = function.validate() {
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
        for (index, block) in self.blocks.iter().enumerate() {
            for &parameter in &block.parameters {
                self.local_type(parameter)?;
            }
            for instruction in &block.instructions {
                for local in references(instruction) {
                    self.local_type(local)?;
                }
                self.validate_instruction(instruction)?;
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
impl MirProgram {
    pub fn validate(&self) -> Result<(), String> {
        if !self.functions.contains_key(&self.entry) {
            return Err("MIR program entry is absent".into());
        }
        for function in self.functions.values() {
            function.validate()?;
            for block in &function.blocks {
                for instruction in &block.instructions {
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
        MirInstruction::Resume { value } => vec![*value],
        MirInstruction::Forward => Vec::new(),
        MirInstruction::Copy { dst, src }
        | MirInstruction::Store { dst, src }
        | MirInstruction::Move { dst, src } => vec![*dst, *src],
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
    /// Active only while lowering a direct root handler clause. In that
    /// special CFG shape the captured continuation returns its supplied value
    /// immediately, so exact finite resumptions can be represented without a
    /// runtime continuation object while still charging every call.
    direct_resumption: Option<DirectResumptionState>,
}

#[derive(Clone, Debug)]
struct DirectResumptionState {
    name: String,
    quantity: crate::quantity::Quantity,
    calls: u64,
}

impl Lowerer<'_> {
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
        let mut inner_operation_clauses = inner_clauses
            .iter()
            .filter(|clause| !clause.terminal)
            .collect::<Vec<_>>();
        if inner_operation_clauses.is_empty()
            || inner_operation_clauses
                .iter()
                .any(|clause| clause.effect != effect || clause.operation != operation)
        {
            return None;
        }
        if let Some(fallback) = inner_operation_clauses
            .iter()
            .position(|clause| clause.patterns.iter().all(pattern_is_irrefutable))
        {
            inner_operation_clauses.truncate(fallback + 1);
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
        {
            return None;
        }
        for expression in root_prefix {
            self.statement(expression)?;
        }
        let payload_types = argument_ids
            .iter()
            .map(|argument| self.body.expression(*argument).ty.clone())
            .collect::<Vec<_>>();
        let outer_payload_destinations = payload_types
            .iter()
            .enumerate()
            .map(|(index, ty)| self.alloc(ty.clone(), argument_ids[index]))
            .collect::<Vec<_>>();
        let inner_payload_destinations = payload_types
            .iter()
            .enumerate()
            .map(|(index, ty)| self.alloc(ty.clone(), argument_ids[index]))
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
            target: MirBlockId(1),
        });
        self.instructions = Vec::new();
        for expression in outer_prefix {
            self.statement(expression)?;
        }
        entry.extend(std::mem::take(&mut self.instructions));
        entry.push(MirInstruction::InstallHandler {
            effect: effect.definition,
            effect_arguments: effect.arguments.clone(),
            operation,
            payload_destinations: inner_payload_destinations.clone(),
            resume_type: self.body.expression(inner_computation).ty.clone(),
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
    /// Lower two lexically nested exact-one-shot handlers around one direct
    /// operation.  Even when the inner frame does not name the operation, it
    /// must remain on the continuation snapshot while the outer frame runs:
    /// resuming the outer clause restores the inner frame before normal scope
    /// exit uninstalls it.  This is the smallest source form that exercises
    /// partial-handler forwarding through the real VM stack.
    fn lower_root_runtime_nested_one_shot_handler(
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
        for clause in [*outer_clause, *inner_clause] {
            let quantity = match &clause.resumption {
                CoreHandlerResumption::Explicit { quantity, .. }
                | CoreHandlerResumption::Tail { quantity } => *quantity,
                CoreHandlerResumption::Discard { .. } | CoreHandlerResumption::Terminal => {
                    return None;
                }
            };
            if quantity != crate::quantity::Quantity::ONCE
                || clause.patterns.len() != argument_ids.len()
            {
                return None;
            }
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
        // A handler frame carries its payload register types locally. For a
        // forwarded operation these registers are not written; using the
        // direct operation's already-typed payload shape retains a concrete
        // frame contract until declaration signatures are materialized in MIR.
        let payload_types = argument_ids
            .iter()
            .map(|argument| self.body.expression(*argument).ty.clone())
            .collect::<Vec<_>>();
        let outer_payload_destinations = payload_types
            .iter()
            .enumerate()
            .map(|(index, ty)| self.alloc(ty.clone(), argument_ids[index]))
            .collect::<Vec<_>>();
        let inner_payload_destinations = payload_types
            .iter()
            .enumerate()
            .map(|(index, ty)| self.alloc(ty.clone(), argument_ids[index]))
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
            target: MirBlockId(1),
        });
        entry.push(MirInstruction::InstallHandler {
            effect: inner_clause.effect.definition,
            effect_arguments: inner_clause.effect.arguments.clone(),
            operation: inner_clause.operation,
            payload_destinations: inner_payload_destinations.clone(),
            resume_type: self.body.expression(inner_computation).ty.clone(),
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
        self.instructions.push(MirInstruction::Resume {
            value: outer_resumed,
        });
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
        let resumed = self.direct_handler_clause_value(clause)?;
        self.instructions
            .push(MirInstruction::Resume { value: resumed });
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
                    terminator: MirTerminator::Unreachable,
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
            if self
                .bind_handler_patterns(std::slice::from_ref(&clause.pattern), &[subject])
                .is_none()
            {
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
            self.bind_handler_patterns(std::slice::from_ref(&clause.pattern), &[completed])?;
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
        let (effect, operation, arguments) = self.direct_operation(computation)?;
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
                if !quantity.contains(crate::quantity::Quantity::ONCE) {
                    self.error(
                        "G6005",
                        "direct resumption does not satisfy its declared quantity",
                    );
                    return None;
                }
                let CoreKind::Call { callee, arguments } =
                    self.body.expression(clause.body).kind.clone()
                else {
                    self.error(
                        "G6005",
                        "direct resumptive handler requires an explicit call to its continuation",
                    );
                    return None;
                };
                if !matches!(self.body.expression(callee).kind, CoreKind::Local(ref local) if local == name)
                    || arguments.len() != 1
                {
                    self.error(
                        "G6005",
                        "direct resumptive handler continuation must be invoked with one value",
                    );
                    return None;
                }
                // The root operation's continuation immediately returns its
                // operation result. The upcoming deep handler-stack lowering
                // replaces this direct identity continuation for nonempty
                // residual computations.
                self.value(arguments[0])
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
        if let Some(v) = self.values.get(&id) {
            return Some(*v);
        };
        let e = self.body.expression(id).clone();
        // A local binding has stable storage identity. MIR may still use
        // registers, but a `let` cannot merely alias its initializer: later
        // assignment must overwrite this same destination.
        if let CoreKind::Let { name, value } = &e.kind {
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
            // Named callables are first-class values just like anonymous
            // closures. Their environment is statically empty, while the
            // function identity selects the verified code target.
            CoreKind::Function(callee) => self.instructions.push(MirInstruction::MakeCallable {
                dst,
                callee,
                captures: vec![],
            }),
            CoreKind::Constant(callee) => {
                self.instructions.push(MirInstruction::Call {
                    dst,
                    callee,
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
            CoreKind::PatternTest { subject, pattern } => {
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
                if let CoreKind::Local(name) = &self.body.expression(callee).kind
                    && self
                        .direct_resumption
                        .as_ref()
                        .is_some_and(|resumption| resumption.name == *name)
                    && !self.named.contains_key(name)
                {
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
                    self.instructions
                        .push(MirInstruction::Copy { dst, src: argument });
                    self.values.insert(id, dst);
                    return Some(dst);
                }
                let arguments = arguments
                    .into_iter()
                    .map(|argument| self.value(argument))
                    .collect::<Option<Vec<_>>>()?;
                match self.body.expression(callee).kind.clone() {
                    CoreKind::Function(callee) => self.instructions.push(MirInstruction::Call {
                        dst,
                        callee,
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
                captures,
                body,
            } => {
                let callee = self.lift_closure(callable, parameters, captures.clone(), body)?;
                let captures = self.capture_environment(&captures)?;
                self.instructions.push(MirInstruction::MakeCallable {
                    dst,
                    callee,
                    captures,
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
                let CoreKind::Function(definition) = self.body.expression(callee).kind else {
                    self.error(
                        "G6005",
                        "handler-stack lowering is required for an indirect handler computation",
                    );
                    return None;
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
                matches!(self.body.expression(callee).kind, CoreKind::Function(definition)
                    if self.direct_known_perform(definition, arguments).is_some())
            }
            _ => false,
        }
    }
    /// A deliberately conservative proof used only to erase an unexercised
    /// handler scope. It never treats a nested handler, a performance, an
    /// unknown callable, or a callable with a nonempty/open effect row as
    /// effect-free. This is not a replacement for dynamic handler lowering.
    fn core_is_effect_free(&self, id: CoreId) -> bool {
        match self.body.expression(id).kind.clone() {
            CoreKind::Literal(_) | CoreKind::Local(_) | CoreKind::Function(_) => true,
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
            | CoreKind::Unary { value: base, .. } => self.core_is_effect_free(base),
            CoreKind::Let { value, .. } | CoreKind::Assign { value, .. } => {
                self.core_is_effect_free(value)
            }
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
                self.terminal_operation(*last)
            }
            _ => {
                self.error(
                    "G6005",
                    "terminal handler lowering received a resumptive operation",
                );
                None
            }
        }
    }
    fn alloc(&mut self, ty: Type, source: CoreId) -> MirLocal {
        let id = MirLocal(self.locals.len() as u32);
        self.locals.push(MirLocalDecl { ty, source });
        id
    }
    fn statement(&mut self, id: CoreId) -> Option<()> {
        self.value(id).map(|_| ())
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
            crate::CorePlace::Error => {
                self.error("G6009", "MIR assignment place is recovered");
                None
            }
        }
    }
    fn capture_environment(&mut self, captures: &[ClosureCapture]) -> Option<Vec<MirLocal>> {
        let mut environment = Vec::with_capacity(captures.len());
        for capture in captures {
            let Some(local) = self.named.get(&capture.name).copied() else {
                self.error("G6007", "closure capture has no MIR local");
                return None;
            };
            // PlaceFlow owns the capture-mode decision.  Keep an actual move
            // in MIR when it selected one; shared/unique runtime references
            // have not reached Stage 0's value representation yet, and the
            // currently immutable scalar values are copied into the closure
            // environment.
            let local = if capture.mode == CaptureMode::Move {
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
        parameters: Vec<(String, Type)>,
        captures: Vec<ClosureCapture>,
        body: CoreId,
    ) -> Option<DefKey> {
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
            .map(|argument| substitute_generic_type(argument, &substitutions))
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
                    collect_generic_substitutions(template, actual, substitutions).ok_or(())
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
                referent,
            },
            Type::Reference {
                mutability: actual_mutability,
                referent: actual_referent,
            },
        ) if mutability == actual_mutability => {
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
            referent,
        } => Some(Type::Reference {
            mutability,
            referent: Box::new(substitute_generic_type(*referent, substitutions)?),
        }),
        Type::Callable {
            parameters,
            result,
            effects,
            invocation,
        } => Some(Type::Callable {
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
                        .map(|argument| substitute_generic_type(argument, substitutions))
                        .collect::<Option<_>>()?,
                })
            })
            .collect::<Option<BTreeSet<_>>>()?,
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
