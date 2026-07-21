//! Checked, typed mutation layer for compact MIR control-flow graphs.
//!
//! The compatibility `Function` remains vector-backed, but optimizer passes
//! edit through stable [`BlockId`] slots. Deleted slots become tombstones and
//! fresh IDs are never recycled during one editor transaction.

use std::{collections::BTreeMap, fmt};

use grandiose_vm::{Type, TypeId};

use super::{
    BasicBlock, BlockId, BlockKind, BlockParamRole, Function, Instruction, InstructionKind,
    Terminator, analysis,
};

pub(crate) const MAX_BLOCKS: u64 = 1_000_000;
pub(crate) const MAX_EDGES: u64 = 4_000_000;
pub(crate) const MAX_OPERATIONS: u64 = 4_000_000;
pub(crate) const MAX_LOCALS: u64 = 4_000_000;
pub(crate) const MAX_MOVE_PATHS: u64 = 8_000_000;
pub(crate) const MAX_NESTED_CONTROL: u64 = 65_535;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ResourceLimits {
    pub(crate) blocks: u64,
    pub(crate) edges: u64,
    pub(crate) operations: u64,
    pub(crate) locals: u64,
    pub(crate) move_paths: u64,
    pub(crate) nested_control: u64,
}

impl Default for ResourceLimits {
    fn default() -> Self {
        Self {
            blocks: MAX_BLOCKS,
            edges: MAX_EDGES,
            operations: MAX_OPERATIONS,
            locals: MAX_LOCALS,
            move_paths: MAX_MOVE_PATHS,
            nested_control: MAX_NESTED_CONTROL,
        }
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum MutationErrorKind {
    InvalidId,
    DuplicateBlock,
    MissingBlock,
    DeleteEntry,
    DanglingEdge {
        target: BlockId,
    },
    InvalidStatement {
        index: usize,
    },
    ResourceLimit {
        resource: &'static str,
        limit: u64,
        attempted: u64,
    },
    InvalidType {
        ty: TypeId,
    },
    InvalidRegister {
        register: u32,
    },
    OwnershipInvalid {
        message: String,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MutationError {
    pub(crate) function: String,
    pub(crate) block: Option<BlockId>,
    pub(crate) kind: MutationErrorKind,
}

impl fmt::Display for MutationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "function `{}`", self.function)?;
        if let Some(block) = self.block {
            write!(formatter, " block {}", block.0)?;
        }
        match &self.kind {
            MutationErrorKind::InvalidId => write!(formatter, ": u32::MAX is not a valid MIR ID"),
            MutationErrorKind::DuplicateBlock => write!(formatter, ": duplicate block ID"),
            MutationErrorKind::MissingBlock => write!(formatter, ": missing or tombstoned block"),
            MutationErrorKind::DeleteEntry => {
                write!(formatter, ": cannot tombstone the entry block")
            }
            MutationErrorKind::DanglingEdge { target } => {
                write!(
                    formatter,
                    ": edge targets missing or tombstoned block {}",
                    target.0
                )
            }
            MutationErrorKind::InvalidStatement { index } => {
                write!(formatter, ": statement index {index} is out of range")
            }
            MutationErrorKind::ResourceLimit {
                resource,
                limit,
                attempted,
            } => write!(
                formatter,
                ": MIR resource limit exceeded for {resource}: attempted {attempted}, limit {limit}"
            ),
            MutationErrorKind::InvalidType { ty } => {
                write!(formatter, ": unknown MIR type id {ty}")
            }
            MutationErrorKind::InvalidRegister { register } => {
                write!(formatter, ": unknown MIR register r{register}")
            }
            MutationErrorKind::OwnershipInvalid { message } => {
                write!(formatter, ": ownership-invalid MIR: {message}")
            }
        }
    }
}

impl std::error::Error for MutationError {}

#[derive(Clone, Debug)]
enum BlockSlot {
    Live {
        kind: BlockKind,
        block: Box<BasicBlock>,
    },
    Tombstone {
        kind: BlockKind,
        id: BlockId,
    },
}

/// Incremental, limit-checked MIR construction transaction. IDs are allocated
/// monotonically and never recycled; `finish` is the commit point and rejects
/// any CFG which fails the optimizer's raw-MIR, PlaceFlow ownership, or cleanup
/// validation checkpoints.
#[allow(dead_code)] // The checked frontend migration consumes this incrementally.
pub(crate) struct CheckedMirBuilder<'a> {
    function: Function,
    types: &'a [Type],
    limits: ResourceLimits,
    next_block: u32,
}

#[allow(dead_code)]
impl<'a> CheckedMirBuilder<'a> {
    pub(crate) fn new(
        function: Function,
        types: &'a [Type],
        limits: ResourceLimits,
    ) -> Result<Self, MutationError> {
        check_resource_limits(&function, limits)?;
        for &ty in function
            .register_types
            .iter()
            .chain(function.params.iter())
            .chain([&function.result, &function.receiver_type])
        {
            if ty as usize >= types.len() {
                return Err(mutation_error(
                    &function,
                    None,
                    MutationErrorKind::InvalidType { ty },
                ));
            }
        }
        let next_block = function
            .blocks
            .iter()
            .map(|block| block.id)
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .filter(|next| *next != u32::MAX)
            .ok_or_else(|| mutation_error(&function, None, MutationErrorKind::InvalidId))?;
        CheckedCfg::new(&function, limits)?;
        Ok(Self {
            function,
            types,
            limits,
            next_block,
        })
    }

    pub(crate) fn allocate_register(&mut self, ty: TypeId) -> Result<u32, MutationError> {
        if ty as usize >= self.types.len() {
            return Err(mutation_error(
                &self.function,
                None,
                MutationErrorKind::InvalidType { ty },
            ));
        }
        let attempted = self.function.register_types.len() as u64 + 1;
        limit(&self.function.name, "locals", attempted, self.limits.locals)?;
        let register = u32::try_from(self.function.register_types.len())
            .ok()
            .filter(|register| *register != u32::MAX)
            .ok_or_else(|| mutation_error(&self.function, None, MutationErrorKind::InvalidId))?;
        self.function.register_types.push(ty);
        Ok(register)
    }

    pub(crate) fn add_block(
        &mut self,
        params: Vec<super::BlockParam>,
        kind: Terminator,
    ) -> Result<BlockId, MutationError> {
        let attempted = self.function.blocks.len() as u64 + 1;
        limit(&self.function.name, "blocks", attempted, self.limits.blocks)?;
        for parameter in &params {
            self.check_register(parameter.register)?;
            if parameter.ty as usize >= self.types.len()
                || self.function.register_types[parameter.register as usize] != parameter.ty
            {
                return Err(mutation_error(
                    &self.function,
                    None,
                    MutationErrorKind::InvalidType { ty: parameter.ty },
                ));
            }
        }
        let id = BlockId(self.next_block);
        self.next_block = self
            .next_block
            .checked_add(1)
            .filter(|next| *next != u32::MAX)
            .ok_or_else(|| mutation_error(&self.function, None, MutationErrorKind::InvalidId))?;
        self.function.blocks.push(BasicBlock {
            id: id.0,
            params,
            statements: vec![],
            terminator: kind,
        });
        Ok(id)
    }

    pub(crate) fn push_statement(
        &mut self,
        block: BlockId,
        instruction: Instruction,
    ) -> Result<(), MutationError> {
        let operations = self
            .function
            .blocks
            .iter()
            .map(|block| block.statements.len() as u64 + 1)
            .sum::<u64>()
            + 1;
        limit(
            &self.function.name,
            "statements + terminators",
            operations,
            self.limits.operations,
        )?;
        let Some(target) = self
            .function
            .blocks
            .iter_mut()
            .find(|candidate| candidate.id == block.0)
        else {
            return Err(mutation_error(
                &self.function,
                Some(block),
                MutationErrorKind::MissingBlock,
            ));
        };
        target.statements.push(instruction);
        Ok(())
    }

    pub(crate) fn set_terminator(
        &mut self,
        block: BlockId,
        terminator: Terminator,
    ) -> Result<(), MutationError> {
        let Some(target) = self
            .function
            .blocks
            .iter_mut()
            .find(|candidate| candidate.id == block.0)
        else {
            return Err(mutation_error(
                &self.function,
                Some(block),
                MutationErrorKind::MissingBlock,
            ));
        };
        target.terminator = terminator;
        Ok(())
    }

    pub(crate) fn finish(self) -> Result<Function, MutationError> {
        CheckedCfg::new(&self.function, self.limits)?;
        super::optimizer::validate_generated_function(&self.function, self.types).map_err(
            |error| {
                mutation_error(
                    &self.function,
                    error.block.map(BlockId),
                    MutationErrorKind::OwnershipInvalid {
                        message: error.message,
                    },
                )
            },
        )?;
        Ok(self.function)
    }

    fn check_register(&self, register: u32) -> Result<(), MutationError> {
        if register as usize >= self.function.register_types.len() {
            Err(mutation_error(
                &self.function,
                None,
                MutationErrorKind::InvalidRegister { register },
            ))
        } else {
            Ok(())
        }
    }
}

/// Transactional checked view of one function CFG.
#[derive(Clone, Debug)]
pub(crate) struct CheckedCfg {
    function: String,
    entry: BlockId,
    slots: Vec<BlockSlot>,
    indices: BTreeMap<BlockId, usize>,
    invalidated: u8,
    limits: ResourceLimits,
}

impl CheckedCfg {
    pub(crate) fn new(function: &Function, limits: ResourceLimits) -> Result<Self, MutationError> {
        check_resource_limits(function, limits)?;
        let entry = checked_id(function, function.entry)?;
        let label_targets = function
            .flow
            .labels
            .iter()
            .map(|label| label.destination)
            .chain(function.blocks.iter().flat_map(|block| {
                block.statements.iter().filter_map(|statement| {
                    if let InstructionKind::LabelPush { target, .. } = statement.kind {
                        Some(target)
                    } else {
                        None
                    }
                })
            }))
            .collect::<Vec<_>>();
        let mut indices = BTreeMap::new();
        let mut slots = Vec::with_capacity(function.blocks.len());
        for block in &function.blocks {
            let id = checked_id(function, block.id)?;
            if indices.insert(id, slots.len()).is_some() {
                return Err(mutation_error(
                    function,
                    Some(id),
                    MutationErrorKind::DuplicateBlock,
                ));
            }
            slots.push(BlockSlot::Live {
                kind: classify_block(function, block, &label_targets),
                block: Box::new(block.clone()),
            });
        }
        if !indices.contains_key(&entry) {
            return Err(mutation_error(
                function,
                Some(entry),
                MutationErrorKind::MissingBlock,
            ));
        }
        Ok(Self {
            function: function.name.clone(),
            entry,
            slots,
            indices,
            invalidated: 0,
            limits,
        })
    }

    pub(crate) fn block_kind(&self, id: BlockId) -> Result<BlockKind, MutationError> {
        match self.slot(id)? {
            BlockSlot::Live { kind, .. } | BlockSlot::Tombstone { kind, .. } => Ok(*kind),
        }
    }

    pub(crate) fn is_tombstone(&self, id: BlockId) -> bool {
        self.slot(id)
            .is_ok_and(|slot| matches!(slot, BlockSlot::Tombstone { .. }))
    }

    pub(crate) fn invalidated(&self) -> u8 {
        self.invalidated
    }

    pub(crate) fn tombstone_many(
        &mut self,
        ids: impl IntoIterator<Item = BlockId>,
    ) -> Result<(), MutationError> {
        let mut ids = ids.into_iter().collect::<Vec<_>>();
        ids.sort_unstable();
        ids.dedup();
        for &id in &ids {
            if id == self.entry {
                return Err(self.error(Some(id), MutationErrorKind::DeleteEntry));
            }
            if !matches!(self.slot(id)?, BlockSlot::Live { .. }) {
                return Err(self.error(Some(id), MutationErrorKind::MissingBlock));
            }
        }
        for id in ids {
            let index = self.indices[&id];
            let kind = match &self.slots[index] {
                BlockSlot::Live { kind, .. } => *kind,
                BlockSlot::Tombstone { .. } => unreachable!("preflight rejected tombstone"),
            };
            self.slots[index] = BlockSlot::Tombstone { kind, id };
        }
        self.invalidated |= analysis::ALL;
        Ok(())
    }

    pub(crate) fn remove_statement(
        &mut self,
        id: BlockId,
        index: usize,
    ) -> Result<Instruction, MutationError> {
        let function_name = self.function.clone();
        let block = self.live_block_mut(id)?;
        if index >= block.statements.len() {
            return Err(MutationError {
                function: function_name,
                block: Some(id),
                kind: MutationErrorKind::InvalidStatement { index },
            });
        }
        let removed = block.statements.remove(index);
        self.invalidated |=
            analysis::USES | analysis::FLOW | analysis::EFFECTS | analysis::VALUES | analysis::COST;
        Ok(removed)
    }

    pub(crate) fn commit(self, function: &mut Function) -> Result<u8, MutationError> {
        for slot in &self.slots {
            if let BlockSlot::Live { block, .. } = slot {
                self.validate_targets(&block.terminator, Some(BlockId(block.id)))?;
                for statement in &block.statements {
                    if let InstructionKind::LabelPush { target, .. } = statement.kind {
                        self.live_block(BlockId(target))?;
                    }
                }
            }
        }
        let blocks = self
            .slots
            .into_iter()
            .filter_map(|slot| match slot {
                BlockSlot::Live { block, .. } => Some(*block),
                BlockSlot::Tombstone { id, .. } => {
                    debug_assert!(self.indices.contains_key(&id));
                    None
                }
            })
            .collect::<Vec<_>>();
        let operations = blocks
            .iter()
            .map(|block| block.statements.len() as u64 + 1)
            .sum();
        limit(
            &self.function,
            "statements + terminators",
            operations,
            self.limits.operations,
        )?;
        function.blocks = blocks;
        function.invalid_analyses |= self.invalidated;
        Ok(self.invalidated)
    }

    fn slot(&self, id: BlockId) -> Result<&BlockSlot, MutationError> {
        self.indices
            .get(&id)
            .and_then(|index| self.slots.get(*index))
            .ok_or_else(|| self.error(Some(id), MutationErrorKind::MissingBlock))
    }

    fn live_block(&self, id: BlockId) -> Result<&BasicBlock, MutationError> {
        match self.slot(id)? {
            BlockSlot::Live { block, .. } => Ok(block),
            BlockSlot::Tombstone { .. } => {
                Err(self.error(Some(id), MutationErrorKind::MissingBlock))
            }
        }
    }

    fn live_block_mut(&mut self, id: BlockId) -> Result<&mut BasicBlock, MutationError> {
        let index = self
            .indices
            .get(&id)
            .copied()
            .ok_or_else(|| self.error(Some(id), MutationErrorKind::MissingBlock))?;
        match &mut self.slots[index] {
            BlockSlot::Live { block, .. } => Ok(block),
            BlockSlot::Tombstone { .. } => Err(MutationError {
                function: self.function.clone(),
                block: Some(id),
                kind: MutationErrorKind::MissingBlock,
            }),
        }
    }

    fn validate_targets(
        &self,
        terminator: &Terminator,
        source: Option<BlockId>,
    ) -> Result<(), MutationError> {
        let mut missing = None;
        for_each_edge(terminator, |target| {
            let id = BlockId(target);
            if self.live_block(id).is_err() {
                missing = Some(id);
            }
        });
        missing.map_or(Ok(()), |target| {
            Err(self.error(source, MutationErrorKind::DanglingEdge { target }))
        })
    }

    fn error(&self, block: Option<BlockId>, kind: MutationErrorKind) -> MutationError {
        MutationError {
            function: self.function.clone(),
            block,
            kind,
        }
    }
}

pub(crate) fn check_resource_limits(
    function: &Function,
    limits: ResourceLimits,
) -> Result<(), MutationError> {
    limit(
        &function.name,
        "blocks",
        function.blocks.len() as u64,
        limits.blocks,
    )?;
    let edges = function
        .blocks
        .iter()
        .map(|block| {
            let mut count = 0_u64;
            for_each_edge(&block.terminator, |_| count += 1);
            count
        })
        .sum();
    limit(&function.name, "edges", edges, limits.edges)?;
    let operations = function
        .blocks
        .iter()
        .map(|block| block.statements.len() as u64 + 1)
        .sum();
    limit(
        &function.name,
        "statements + terminators",
        operations,
        limits.operations,
    )?;
    limit(
        &function.name,
        "locals",
        function.register_types.len() as u64,
        limits.locals,
    )?;
    limit(
        &function.name,
        "move paths",
        function.flow.move_paths.facts.len() as u64,
        limits.move_paths,
    )?;
    for (resource, attempted) in [
        ("lexical scopes", function.flow.scopes.len() as u64),
        ("loans", function.flow.loans.len() as u64),
        ("labels", function.flow.labels.len() as u64),
        ("handlers", function.flow.handlers.len() as u64),
        ("perform sites", function.flow.performs.len() as u64),
        ("resumption sites", function.flow.resumptions.len() as u64),
        ("cleanup plans", function.flow.cleanup_plans.len() as u64),
    ] {
        limit(&function.name, resource, attempted, limits.nested_control)?;
    }
    Ok(())
}

fn checked_id(function: &Function, id: u32) -> Result<BlockId, MutationError> {
    if id == u32::MAX {
        Err(mutation_error(function, None, MutationErrorKind::InvalidId))
    } else {
        Ok(BlockId(id))
    }
}

fn mutation_error(
    function: &Function,
    block: Option<BlockId>,
    kind: MutationErrorKind,
) -> MutationError {
    MutationError {
        function: function.name.clone(),
        block,
        kind,
    }
}

fn limit(
    function: &str,
    resource: &'static str,
    attempted: u64,
    maximum: u64,
) -> Result<(), MutationError> {
    if attempted > maximum {
        Err(MutationError {
            function: function.to_owned(),
            block: None,
            kind: MutationErrorKind::ResourceLimit {
                resource,
                limit: maximum,
                attempted,
            },
        })
    } else {
        Ok(())
    }
}

fn classify_block(function: &Function, block: &BasicBlock, labels: &[u32]) -> BlockKind {
    if block.id == function.entry {
        BlockKind::Entry
    } else if labels.contains(&block.id) {
        BlockKind::Label
    } else if block
        .params
        .iter()
        .any(|parameter| parameter.role == BlockParamRole::ProtectedExitValue)
        || (!block.statements.is_empty()
            && block
                .statements
                .iter()
                .all(|statement| matches!(statement.kind, InstructionKind::Drop { .. })))
    {
        BlockKind::Cleanup
    } else if block
        .params
        .iter()
        .any(|parameter| parameter.role == BlockParamRole::ResumeResult)
    {
        BlockKind::Resumption
    } else if function
        .flow
        .handlers
        .iter()
        .any(|handler| handler.block == block.id)
    {
        BlockKind::Handler
    } else {
        BlockKind::Normal
    }
}

fn for_each_edge(terminator: &Terminator, mut visit: impl FnMut(u32)) {
    for_each_edge_mut(&mut terminator.clone(), |target| visit(*target));
}

fn for_each_edge_mut(terminator: &mut Terminator, mut visit: impl FnMut(&mut u32)) {
    let mut edge = |edge: &mut super::Edge| visit(&mut edge.target);
    match terminator {
        Terminator::Goto(target) => edge(target),
        Terminator::Switch {
            cases, otherwise, ..
        } => {
            for (_, target) in cases {
                edge(target);
            }
            edge(otherwise);
        }
        Terminator::Call { normal, .. }
        | Terminator::CallSelf { normal, .. }
        | Terminator::CallKnownReceiver { normal, .. }
        | Terminator::HostCall { normal, .. }
        | Terminator::CallIndirect { normal, .. }
        | Terminator::Handle { normal, .. }
        | Terminator::Resume { normal, .. }
        | Terminator::Cancel { normal, .. } => edge(normal),
        Terminator::Perform { resume, .. } => {
            if let Some(resume) = resume {
                edge(resume);
            }
        }
        Terminator::Leave { target, .. } => edge(target),
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

#[cfg(test)]
mod tests {
    use grandiose_vm::{Constant, I64, Type, U32, UNIT};

    use super::*;
    use crate::compiler_mir::{
        BlockParam, CleanupEdge, CleanupPlanFact, Edge, FeatureBits, HandlerSiteFact, LabelFact,
        MirPhase, Operand, PlaceFlow, ScopeFact, ScopeId, UseMode,
    };
    use crate::span::Span;

    fn block(id: u32, target: Option<u32>) -> BasicBlock {
        BasicBlock {
            id,
            params: vec![],
            statements: vec![],
            terminator: target.map_or(Terminator::Return { value: None }, |target| {
                Terminator::Goto(Edge {
                    target,
                    args: vec![],
                })
            }),
        }
    }

    fn function(blocks: Vec<BasicBlock>) -> Function {
        Function {
            declaration: 0,
            name: "checked".into(),
            params: vec![],
            result: UNIT,
            receiver_mode: None,
            receiver_type: UNIT,
            no_return: false,
            outward_protocols: vec![],
            register_types: vec![UNIT],
            entry: 0,
            blocks,
            phase: MirPhase::Raw,
            features: FeatureBits::empty(),
            return_cleanup: vec![],
            flow: PlaceFlow::default(),
            invalid_analyses: 0,
        }
    }

    #[test]
    fn tombstones_retain_stable_typed_identity_until_commit() {
        let mut original = function(vec![block(0, None), block(4, None)]);
        original.return_cleanup = vec![0];
        original.flow.scopes.push(ScopeFact {
            parent: None,
            owners: vec![0],
        });
        original.flow.cleanup_plans.push(CleanupPlanFact {
            edge: CleanupEdge::Return { block: 0 },
            source_scope: ScopeId(0),
            target_scope: ScopeId(0),
            actions: vec![],
            protected: vec![],
        });
        let mut editor = CheckedCfg::new(&original, ResourceLimits::default()).unwrap();
        editor.tombstone_many([BlockId(4)]).unwrap();
        assert!(editor.is_tombstone(BlockId(4)));
        assert_eq!(editor.block_kind(BlockId(4)).unwrap(), BlockKind::Normal);
        let mut committed = original.clone();
        editor.commit(&mut committed).unwrap();
        assert_eq!(
            committed
                .blocks
                .iter()
                .map(|block| block.id)
                .collect::<Vec<_>>(),
            [0]
        );
        assert_eq!(committed.register_types, original.register_types);
        assert_eq!(committed.return_cleanup, original.return_cleanup);
        assert_eq!(committed.flow, original.flow);
    }

    #[test]
    fn mutation_masks_are_operation_specific() {
        let mut original = function(vec![block(0, None)]);
        original.blocks[0].statements.push(Instruction {
            span: Span { start: 1, end: 2 },
            kind: InstructionKind::Drop {
                owner: Operand {
                    register: 0,
                    mode: UseMode::Move,
                },
            },
        });
        let mut editor = CheckedCfg::new(&original, ResourceLimits::default()).unwrap();
        editor.remove_statement(BlockId(0), 0).unwrap();
        assert_eq!(editor.invalidated() & analysis::CFG, 0);
        assert_ne!(editor.invalidated() & analysis::USES, 0);
        let mut committed = original;
        let mask = editor.commit(&mut committed).unwrap();
        assert_eq!(committed.invalid_analyses, mask);
    }

    #[test]
    fn adversarial_deletion_edges_ids_and_limits_fail_structurally() {
        let original = function(vec![block(0, Some(1)), block(1, None)]);
        let mut editor = CheckedCfg::new(&original, ResourceLimits::default()).unwrap();
        assert_eq!(
            editor.tombstone_many([BlockId(0)]).unwrap_err().kind,
            MutationErrorKind::DeleteEntry
        );
        assert!(
            !editor.is_tombstone(BlockId(0)),
            "failed batches are atomic"
        );
        editor.tombstone_many([BlockId(1)]).unwrap();
        assert!(matches!(
            editor.commit(&mut original.clone()).unwrap_err().kind,
            MutationErrorKind::DanglingEdge { target: BlockId(1) }
        ));

        let duplicate = function(vec![block(0, None), block(0, None)]);
        assert_eq!(
            CheckedCfg::new(&duplicate, ResourceLimits::default())
                .unwrap_err()
                .kind,
            MutationErrorKind::DuplicateBlock
        );
        let invalid_id = function(vec![block(u32::MAX, None)]);
        assert_eq!(
            CheckedCfg::new(&invalid_id, ResourceLimits::default())
                .unwrap_err()
                .kind,
            MutationErrorKind::InvalidId
        );

        let limits = ResourceLimits {
            blocks: 0,
            ..ResourceLimits::default()
        };
        assert!(matches!(
            CheckedCfg::new(&function(vec![block(0, None)]), limits)
                .unwrap_err()
                .kind,
            MutationErrorKind::ResourceLimit {
                resource: "blocks",
                limit: 0,
                attempted: 1
            }
        ));

        let operation_error = CheckedCfg::new(
            &function(vec![block(0, None)]),
            ResourceLimits {
                operations: 0,
                ..ResourceLimits::default()
            },
        )
        .unwrap_err();
        assert_eq!(
            operation_error.to_string(),
            "function `checked`: MIR resource limit exceeded for statements + terminators: attempted 1, limit 0"
        );

        assert!(matches!(
            CheckedCfg::new(
                &function(vec![block(0, Some(1)), block(1, None)]),
                ResourceLimits {
                    edges: 0,
                    ..ResourceLimits::default()
                }
            )
            .unwrap_err()
            .kind,
            MutationErrorKind::ResourceLimit {
                resource: "edges",
                limit: 0,
                attempted: 1
            }
        ));

        let mut nested = function(vec![block(0, None)]);
        nested.flow.scopes.push(ScopeFact {
            parent: None,
            owners: vec![],
        });
        assert!(matches!(
            CheckedCfg::new(
                &nested,
                ResourceLimits {
                    nested_control: 0,
                    ..ResourceLimits::default()
                }
            )
            .unwrap_err()
            .kind,
            MutationErrorKind::ResourceLimit {
                resource: "lexical scopes",
                limit: 0,
                attempted: 1
            }
        ));
    }

    #[test]
    fn typed_kinds_preserve_control_boundaries() {
        let mut original = function(vec![
            block(0, Some(1)),
            block(1, None),
            block(2, None),
            block(3, None),
            block(4, None),
            block(5, None),
        ]);
        original.blocks[1].params.push(BlockParam {
            register: 0,
            ty: UNIT,
            role: BlockParamRole::ProtectedExitValue,
        });
        original.blocks[3].params.push(BlockParam {
            register: 0,
            ty: UNIT,
            role: BlockParamRole::ResumeResult,
        });
        original.flow.labels.push(LabelFact {
            result_type: UNIT,
            scope: ScopeId(0),
            destination: 4,
        });
        original.flow.handlers.push(HandlerSiteFact {
            block: 5,
            scope: ScopeId(0),
        });
        let mut editor = CheckedCfg::new(&original, ResourceLimits::default()).unwrap();
        assert_eq!(editor.block_kind(BlockId(0)).unwrap(), BlockKind::Entry);
        assert_eq!(editor.block_kind(BlockId(1)).unwrap(), BlockKind::Cleanup);
        assert_eq!(editor.block_kind(BlockId(2)).unwrap(), BlockKind::Normal);
        assert_eq!(
            editor.block_kind(BlockId(3)).unwrap(),
            BlockKind::Resumption
        );
        assert_eq!(editor.block_kind(BlockId(4)).unwrap(), BlockKind::Label);
        assert_eq!(editor.block_kind(BlockId(5)).unwrap(), BlockKind::Handler);
        editor.tombstone_many([BlockId(2)]).unwrap();
        assert_eq!(editor.invalidated(), analysis::ALL);
        editor.commit(&mut original).unwrap();
        assert!(!original.blocks.iter().any(|block| block.id == 2));
    }

    #[derive(Clone)]
    struct DeterministicMirGenerator {
        state: u64,
        remaining: u32,
    }

    impl DeterministicMirGenerator {
        fn new(seed: u64, budget: u32) -> Self {
            Self {
                state: seed,
                remaining: budget,
            }
        }

        fn next(&mut self) -> u32 {
            assert!(self.remaining != 0, "generator budget exhausted");
            self.remaining -= 1;
            self.state ^= self.state << 13;
            self.state ^= self.state >> 7;
            self.state ^= self.state << 17;
            self.state as u32
        }

        /// Produce a shrinkable four-block diamond. The seed affects only
        /// constants and branch selection; the ownership-valid CFG skeleton is
        /// fixed, which makes a failing case reducible to `(seed, budget)`.
        fn diamond(&mut self) -> Function {
            let types = Type::predefined();
            let mut seed = function(vec![block(0, None)]);
            seed.register_types.extend([I64, U32, I64]);
            seed.result = I64;
            let mut builder =
                CheckedMirBuilder::new(seed, &types, ResourceLimits::default()).unwrap();
            let left = builder.add_block(vec![], Terminator::Unreachable).unwrap();
            let right = builder.add_block(vec![], Terminator::Unreachable).unwrap();
            let join = builder
                .add_block(
                    vec![BlockParam {
                        register: 3,
                        ty: I64,
                        role: BlockParamRole::Ordinary,
                    }],
                    Terminator::Return {
                        value: Some(Operand {
                            register: 3,
                            mode: UseMode::Copy,
                        }),
                    },
                )
                .unwrap();
            for (register, value) in [
                (1, Constant::I64(self.next() as i64)),
                (2, Constant::U32(self.next() & 1)),
            ] {
                builder
                    .push_statement(
                        BlockId(0),
                        Instruction {
                            span: Span { start: 0, end: 0 },
                            kind: InstructionKind::Const {
                                dst: register,
                                value,
                            },
                        },
                    )
                    .unwrap();
            }
            builder
                .set_terminator(
                    BlockId(0),
                    Terminator::Switch {
                        discr: Operand {
                            register: 2,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            Constant::U32(0),
                            Edge {
                                target: left.0,
                                args: vec![],
                            },
                        )],
                        otherwise: Edge {
                            target: right.0,
                            args: vec![],
                        },
                    },
                )
                .unwrap();
            for arm in [left, right] {
                builder
                    .set_terminator(
                        arm,
                        Terminator::Goto(Edge {
                            target: join.0,
                            args: vec![Operand {
                                register: 1,
                                mode: UseMode::Copy,
                            }],
                        }),
                    )
                    .unwrap();
            }
            builder.finish().unwrap()
        }

        fn loop_cfg(&mut self) -> Function {
            let types = Type::predefined();
            let mut seed = function(vec![block(0, None)]);
            seed.register_types.extend([U32, I64, I64, I64]);
            seed.result = I64;
            let mut builder =
                CheckedMirBuilder::new(seed, &types, ResourceLimits::default()).unwrap();
            let header = builder
                .add_block(
                    vec![BlockParam {
                        register: 3,
                        ty: I64,
                        role: BlockParamRole::Ordinary,
                    }],
                    Terminator::Unreachable,
                )
                .unwrap();
            let exit = builder
                .add_block(
                    vec![BlockParam {
                        register: 4,
                        ty: I64,
                        role: BlockParamRole::Ordinary,
                    }],
                    Terminator::Return {
                        value: Some(Operand {
                            register: 4,
                            mode: UseMode::Copy,
                        }),
                    },
                )
                .unwrap();
            for (register, value) in [
                (1, Constant::U32(self.next() & 1)),
                (2, Constant::I64(self.next() as i64)),
            ] {
                builder
                    .push_statement(
                        BlockId(0),
                        Instruction {
                            span: Span { start: 0, end: 0 },
                            kind: InstructionKind::Const {
                                dst: register,
                                value,
                            },
                        },
                    )
                    .unwrap();
            }
            builder
                .set_terminator(
                    BlockId(0),
                    Terminator::Goto(Edge {
                        target: header.0,
                        args: vec![Operand {
                            register: 2,
                            mode: UseMode::Copy,
                        }],
                    }),
                )
                .unwrap();
            builder
                .set_terminator(
                    header,
                    Terminator::Switch {
                        discr: Operand {
                            register: 1,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            Constant::U32(0),
                            Edge {
                                target: exit.0,
                                args: vec![Operand {
                                    register: 3,
                                    mode: UseMode::Copy,
                                }],
                            },
                        )],
                        otherwise: Edge {
                            target: header.0,
                            args: vec![Operand {
                                register: 3,
                                mode: UseMode::Copy,
                            }],
                        },
                    },
                )
                .unwrap();
            builder.finish().unwrap()
        }
    }

    #[test]
    fn checked_builder_is_deterministic_budgeted_and_ownership_validated() {
        let first = DeterministicMirGenerator::new(0x5eed, 2).diamond();
        let second = DeterministicMirGenerator::new(0x5eed, 2).diamond();
        assert_eq!(first, second);
        assert_eq!(first.blocks.len(), 4);
        let generated_loop = DeterministicMirGenerator::new(7, 2).loop_cfg();
        let analysis =
            super::super::analyses::ControlFlowAnalysis::compute(&generated_loop, u64::MAX)
                .unwrap();
        assert_eq!(analysis.loops().len(), 1);

        let types = Type::predefined();
        let mut invalid = function(vec![block(0, None)]);
        let array = types.len() as u32;
        let mut owned_types = types.clone();
        owned_types.push(Type::Array { element: I64 });
        invalid.params = vec![array];
        invalid.result = array;
        invalid.register_types.push(array);
        invalid.blocks[0].statements = vec![Instruction {
            span: Span { start: 0, end: 0 },
            kind: InstructionKind::Drop {
                owner: Operand {
                    register: 1,
                    mode: UseMode::Move,
                },
            },
        }];
        invalid.blocks[0].terminator = Terminator::Return {
            value: Some(Operand {
                register: 1,
                mode: UseMode::Move,
            }),
        };
        let error = CheckedMirBuilder::new(invalid, &owned_types, ResourceLimits::default())
            .unwrap()
            .finish()
            .unwrap_err();
        assert!(matches!(
            error.kind,
            MutationErrorKind::OwnershipInvalid { .. }
        ));
    }
}
