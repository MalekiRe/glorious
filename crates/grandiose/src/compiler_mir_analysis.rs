//! Deterministic, reusable analyses over validated compact MIR.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use grandiose_vm::{Type, TypeId};

use super::{
    BasicBlock, BlockId, Function, InstructionKind, Operand, OwnershipCategory, Register,
    StorageClass, Terminator, analysis,
    mutation::{CheckedCfg, MutationError, ResourceLimits},
};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct EdgeId {
    pub(crate) source: BlockId,
    pub(crate) ordinal: u32,
    pub(crate) target: BlockId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum AnalysisErrorKind {
    InvalidCfg(String),
    MissingTarget(BlockId),
    BudgetExceeded { limit: u64, attempted: u64 },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct AnalysisError {
    pub(crate) function: String,
    pub(crate) kind: AnalysisErrorKind,
}

impl fmt::Display for AnalysisError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "function `{}`: ", self.function)?;
        match &self.kind {
            AnalysisErrorKind::InvalidCfg(message) => write!(formatter, "{message}"),
            AnalysisErrorKind::MissingTarget(target) => {
                write!(
                    formatter,
                    "analysis edge targets missing block {}",
                    target.0
                )
            }
            AnalysisErrorKind::BudgetExceeded { limit, attempted } => write!(
                formatter,
                "MIR analysis budget exceeded: attempted {attempted}, limit {limit}"
            ),
        }
    }
}

impl std::error::Error for AnalysisError {}

impl From<MutationError> for AnalysisError {
    fn from(error: MutationError) -> Self {
        Self {
            function: error.function.clone(),
            kind: AnalysisErrorKind::InvalidCfg(error.to_string()),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct NaturalLoop {
    pub(crate) header: BlockId,
    pub(crate) latches: BTreeSet<BlockId>,
    pub(crate) blocks: BTreeSet<BlockId>,
    pub(crate) preheader: Option<BlockId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ControlFlowAnalysis {
    predecessors: BTreeMap<BlockId, BTreeSet<BlockId>>,
    edges: Vec<EdgeId>,
    reachable: BTreeSet<BlockId>,
    rpo: Vec<BlockId>,
    dominators: BTreeMap<BlockId, BTreeSet<BlockId>>,
    loops: Vec<NaturalLoop>,
    irreducible: BTreeSet<BlockId>,
    work: u64,
}

impl ControlFlowAnalysis {
    pub(crate) const INVALIDATED_BY: u8 = analysis::CFG;

    pub(crate) fn compute(function: &Function, budget: u64) -> Result<Self, AnalysisError> {
        let _checked = CheckedCfg::new(function, ResourceLimits::default())?;
        let mut meter = Meter::new(&function.name, budget);
        let blocks = function
            .blocks
            .iter()
            .map(|block| (BlockId(block.id), block))
            .collect::<BTreeMap<_, _>>();
        let mut predecessors = blocks
            .keys()
            .copied()
            .map(|id| (id, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        let mut edges = Vec::new();
        for (&source, block) in &blocks {
            for (ordinal, target) in block_edges(&block.terminator).into_iter().enumerate() {
                meter.step()?;
                let target = BlockId(target);
                let Some(incoming) = predecessors.get_mut(&target) else {
                    return Err(AnalysisError {
                        function: function.name.clone(),
                        kind: AnalysisErrorKind::MissingTarget(target),
                    });
                };
                incoming.insert(source);
                edges.push(EdgeId {
                    source,
                    ordinal: ordinal as u32,
                    target,
                });
            }
        }
        edges.sort_unstable();

        let entry = BlockId(function.entry);
        let mut reachable = BTreeSet::new();
        let mut postorder = Vec::new();
        let mut stack = vec![(entry, false)];
        while let Some((block, expanded)) = stack.pop() {
            meter.step()?;
            if expanded {
                postorder.push(block);
                continue;
            }
            if !reachable.insert(block) {
                continue;
            }
            stack.push((block, true));
            let body = blocks.get(&block).ok_or_else(|| AnalysisError {
                function: function.name.clone(),
                kind: AnalysisErrorKind::MissingTarget(block),
            })?;
            let mut successors = block_edges(&body.terminator)
                .into_iter()
                .map(BlockId)
                .collect::<Vec<_>>();
            successors.sort_unstable();
            successors.dedup();
            for successor in successors.into_iter().rev() {
                if !reachable.contains(&successor) {
                    stack.push((successor, false));
                }
            }
        }
        postorder.reverse();
        let rpo = postorder;

        let mut dominators = reachable
            .iter()
            .copied()
            .map(|block| {
                let value = if block == entry {
                    BTreeSet::from([entry])
                } else {
                    reachable.clone()
                };
                (block, value)
            })
            .collect::<BTreeMap<_, _>>();
        loop {
            let mut changed = false;
            for &block in rpo.iter().filter(|block| **block != entry) {
                meter.step()?;
                let incoming = predecessors[&block]
                    .iter()
                    .filter(|source| reachable.contains(source))
                    .copied()
                    .collect::<Vec<_>>();
                let mut next = incoming
                    .first()
                    .map(|source| dominators[source].clone())
                    .unwrap_or_default();
                for source in &incoming[1..] {
                    next.retain(|candidate| dominators[source].contains(candidate));
                }
                next.insert(block);
                if next != dominators[&block] {
                    dominators.insert(block, next);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        let mut by_header = BTreeMap::<BlockId, BTreeSet<BlockId>>::new();
        for edge in &edges {
            if reachable.contains(&edge.source) && dominators[&edge.source].contains(&edge.target) {
                by_header
                    .entry(edge.target)
                    .or_default()
                    .insert(edge.source);
            }
        }
        let mut loops = Vec::new();
        for (header, latches) in by_header {
            let mut members = BTreeSet::from([header]);
            let mut pending = latches.iter().copied().collect::<Vec<_>>();
            while let Some(block) = pending.pop() {
                meter.step()?;
                if members.insert(block) {
                    pending.extend(predecessors[&block].iter().copied());
                }
            }
            let outside = predecessors[&header]
                .iter()
                .filter(|source| !members.contains(source))
                .copied()
                .collect::<Vec<_>>();
            loops.push(NaturalLoop {
                header,
                latches,
                blocks: members,
                preheader: if outside.len() == 1 {
                    Some(outside[0])
                } else {
                    None
                },
            });
        }

        // A reachable cyclic SCC without a dominating entry is irreducible.
        let components = strongly_connected(&blocks, &reachable, &mut meter)?;
        let mut irreducible = BTreeSet::new();
        for component in components {
            let cyclic = component.len() > 1
                || component.iter().any(|block| {
                    block_edges(&blocks[block].terminator)
                        .into_iter()
                        .any(|target| target == block.0)
                });
            if !cyclic {
                continue;
            }
            let mut entries = component
                .iter()
                .copied()
                .filter(|block| {
                    predecessors[block]
                        .iter()
                        .any(|source| !component.contains(source))
                })
                .collect::<Vec<_>>();
            if component.contains(&entry) {
                entries.push(entry);
                entries.sort_unstable();
                entries.dedup();
            }
            if entries.len() != 1
                || !component.iter().all(|block| {
                    dominators
                        .get(block)
                        .is_some_and(|set| set.contains(&entries[0]))
                })
            {
                irreducible.extend(component);
            }
        }

        Ok(Self {
            predecessors,
            edges,
            reachable,
            rpo,
            dominators,
            loops,
            irreducible,
            work: meter.work,
        })
    }

    pub(crate) fn predecessors(&self, block: BlockId) -> Option<&BTreeSet<BlockId>> {
        self.predecessors.get(&block)
    }
    pub(crate) fn edges(&self) -> &[EdgeId] {
        &self.edges
    }
    pub(crate) fn rpo(&self) -> &[BlockId] {
        &self.rpo
    }
    pub(crate) fn dominates(&self, dominator: BlockId, block: BlockId) -> bool {
        self.dominators
            .get(&block)
            .is_some_and(|set| set.contains(&dominator))
    }
    pub(crate) fn loops(&self) -> &[NaturalLoop] {
        &self.loops
    }
    pub(crate) fn irreducible(&self) -> &BTreeSet<BlockId> {
        &self.irreducible
    }
    pub(crate) fn work(&self) -> u64 {
        self.work
    }
    pub(crate) fn invalidated_by(mask: u8) -> bool {
        mask & Self::INVALIDATED_BY != 0
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EdgeLiveness {
    live_in: BTreeMap<BlockId, BTreeSet<Register>>,
    live_on_edge: BTreeMap<EdgeId, BTreeSet<Register>>,
    work: u64,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum RegisterClass {
    Owned,
    SharedReference,
    UniqueReference,
    CopyValue,
    Erased,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct LiveInterval {
    pub(crate) register: Register,
    pub(crate) ty: TypeId,
    pub(crate) start: u64,
    pub(crate) end: u64,
    pub(crate) class: RegisterClass,
    pub(crate) addressable: bool,
    /// Present only when every definition and use is in one basic block.
    /// Physical-slot reuse uses this as a deliberately strict control-flow
    /// proof: layout order alone is not execution order across branches.
    pub(crate) local_block: Option<BlockId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RegisterIntervals {
    intervals: Vec<LiveInterval>,
    work: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PhysicalRegisterAllocation {
    virtual_to_physical: Vec<Option<Register>>,
    register_types: Vec<TypeId>,
    reused: BTreeSet<Register>,
}

#[derive(Clone, Copy)]
struct PhysicalSlot {
    ty: TypeId,
    class: RegisterClass,
    end: u64,
    block: Option<BlockId>,
    emptied: bool,
}

impl PhysicalRegisterAllocation {
    /// Deterministically color exact-type, non-addressable intervals. ABI and
    /// addressable locals are pinned one-to-one. A slot is reusable only when
    /// its previous virtual value was proven empty and both lifetimes are
    /// wholly local to the same block; this avoids treating final layout order
    /// as execution order across branches.
    pub(crate) fn exact(
        intervals: &RegisterIntervals,
        register_types: &[TypeId],
        abi_len: usize,
        emptied: &BTreeSet<Register>,
    ) -> Self {
        let mut virtual_to_physical = vec![None; register_types.len()];
        let mut physical_types = Vec::new();
        let mut slots = Vec::<PhysicalSlot>::new();
        let mut reused = BTreeSet::new();

        let mut ordered = intervals.intervals.clone();
        ordered.sort_by_key(|interval| (interval.start, interval.end, interval.register));
        // The receiver/parameter prefix is an external calling convention,
        // not merely a set of simultaneously-live intervals. Seed it in ABI
        // order before interval coloring so differing last-use positions can
        // never permute parameter registers.
        for old in 0..abi_len {
            let interval = intervals
                .intervals
                .iter()
                .find(|interval| interval.register as usize == old)
                .expect("interval construction always materializes the ABI prefix");
            virtual_to_physical[old] = Some(old as Register);
            physical_types.push(register_types[old]);
            slots.push(PhysicalSlot {
                ty: interval.ty,
                class: interval.class,
                end: interval.end,
                block: interval.local_block,
                emptied: false,
            });
        }
        for interval in ordered {
            let old = interval.register as usize;
            if old < abi_len {
                continue;
            }
            let pinned = interval.addressable;
            let selected = (!pinned)
                .then(|| {
                    slots.iter().enumerate().find_map(|(physical, slot)| {
                        (slot.ty == interval.ty
                            && slot.class == interval.class
                            && slot.end < interval.start
                            && slot.emptied
                            && slot.block.is_some()
                            && slot.block == interval.local_block)
                            .then_some(physical as Register)
                    })
                })
                .flatten();
            let physical = selected.unwrap_or_else(|| {
                let physical = slots.len() as Register;
                slots.push(PhysicalSlot {
                    ty: interval.ty,
                    class: interval.class,
                    end: interval.end,
                    block: interval.local_block,
                    emptied: emptied.contains(&interval.register),
                });
                physical_types.push(interval.ty);
                physical
            });
            if selected.is_some() {
                reused.insert(physical);
                slots[physical as usize] = PhysicalSlot {
                    ty: interval.ty,
                    class: interval.class,
                    end: interval.end,
                    block: interval.local_block,
                    emptied: emptied.contains(&interval.register),
                };
            }
            virtual_to_physical[old] = Some(physical);
        }
        Self {
            virtual_to_physical,
            register_types: physical_types,
            reused,
        }
    }

    pub(crate) fn map(&self) -> &[Option<Register>] {
        &self.virtual_to_physical
    }

    pub(crate) fn register_types(&self) -> &[TypeId] {
        &self.register_types
    }

    pub(crate) fn reused(&self) -> &BTreeSet<Register> {
        &self.reused
    }
}

impl RegisterIntervals {
    pub(crate) const INVALIDATED_BY: u8 =
        analysis::CFG | analysis::USES | analysis::FLOW | analysis::VALUES;

    pub(crate) fn compute(
        function: &Function,
        types: &[Type],
        budget: u64,
    ) -> Result<Self, AnalysisError> {
        let _checked = CheckedCfg::new(function, ResourceLimits::default())?;
        let mut meter = Meter::new(&function.name, budget);
        let locals = &function.flow.locals;
        let mut bounds = vec![None::<(u64, u64)>; function.register_types.len()];
        let mut activity_blocks = vec![None::<Option<BlockId>>; function.register_types.len()];
        let mut addressable = vec![false; function.register_types.len()];
        let mut touch = |register: Register,
                         position: u64,
                         block: Option<BlockId>|
         -> Result<(), AnalysisError> {
            meter.step()?;
            let Some(slot) = bounds.get_mut(register as usize) else {
                return Err(AnalysisError {
                    function: function.name.clone(),
                    kind: AnalysisErrorKind::InvalidCfg(format!(
                        "live interval references out-of-range register r{register}"
                    )),
                });
            };
            match slot {
                Some((start, end)) => {
                    *start = (*start).min(position);
                    *end = (*end).max(position);
                }
                None => *slot = Some((position, position)),
            }
            let activity = &mut activity_blocks[register as usize];
            match (*activity, block) {
                (None, block) => *activity = Some(block),
                (Some(Some(previous)), Some(current)) if previous == current => {}
                _ => *activity = Some(None),
            }
            Ok(())
        };
        let abi_len = function.params.len().saturating_add(1);
        for register in 0..abi_len as Register {
            touch(register, 0, None)?;
        }
        let mut position = 1_u64;
        for block in &function.blocks {
            let block_id = BlockId(block.id);
            for parameter in &block.params {
                touch(parameter.register, position, Some(block_id))?;
            }
            position = position.saturating_add(1);
            for statement in &block.statements {
                if let Some(dst) = instruction_definition(&statement.kind) {
                    touch(dst, position, Some(block_id))?;
                }
                for register in instruction_uses(&statement.kind) {
                    touch(register, position, Some(block_id))?;
                }
                match &statement.kind {
                    InstructionKind::Borrow { src, .. }
                    | InstructionKind::ProjectBorrow { src, .. } => {
                        addressable[*src as usize] = true;
                    }
                    _ => {}
                }
                position = position.saturating_add(1);
            }
            if let Some(result) = terminator_definition(&block.terminator) {
                touch(result, position, Some(block_id))?;
            }
            for register in terminator_uses(&block.terminator) {
                touch(register, position, Some(block_id))?;
            }
            position = position.saturating_add(1);
        }
        for &register in &function.return_cleanup {
            touch(register, position, None)?;
        }
        drop(touch);

        // Loan-proof erasure can remove the instruction-level activity of a
        // borrowed place while leaving its reference value live in lowered
        // MIR. Register compaction must retain that place (and any suspended
        // parent loan) because the exported loan still names it. Compute the
        // transitive set, then pin every retained referent as addressable.
        let mut retained = bounds
            .iter()
            .enumerate()
            .filter_map(|(register, bound)| bound.is_some().then_some(register as Register))
            .collect::<BTreeSet<_>>();
        loop {
            let mut changed = false;
            for loan in &function.flow.loans {
                if !retained.contains(&loan.reference) {
                    continue;
                }
                changed |= retained.insert(loan.borrowed.base);
                if let Some(parent) = loan.parent
                    && let Some(parent) = function.flow.loans.get(parent.index())
                {
                    changed |= retained.insert(parent.reference);
                    changed |= retained.insert(parent.borrowed.base);
                }
            }
            if !changed {
                break;
            }
        }
        for loan in &function.flow.loans {
            if retained.contains(&loan.reference) {
                let Some(addressable) = addressable.get_mut(loan.borrowed.base as usize) else {
                    return Err(AnalysisError {
                        function: function.name.clone(),
                        kind: AnalysisErrorKind::InvalidCfg(format!(
                            "loan references out-of-range borrowed register r{}",
                            loan.borrowed.base
                        )),
                    });
                };
                *addressable = true;
            }
        }
        for register in retained {
            let Some(bound) = bounds.get_mut(register as usize) else {
                return Err(AnalysisError {
                    function: function.name.clone(),
                    kind: AnalysisErrorKind::InvalidCfg(format!(
                        "loan references out-of-range register r{register}"
                    )),
                });
            };
            if bound.is_none() {
                meter.step()?;
                *bound = Some((position, position));
                activity_blocks[register as usize] = Some(None);
            }
        }
        let mut intervals = Vec::new();
        for (register, bound) in bounds.into_iter().enumerate() {
            let Some((start, end)) = bound else { continue };
            let ty = function.register_types[register];
            let descriptor = types.get(ty as usize).ok_or_else(|| AnalysisError {
                function: function.name.clone(),
                kind: AnalysisErrorKind::InvalidCfg(format!(
                    "live interval r{register} has out-of-range type t{ty}"
                )),
            })?;
            let fact = locals.get(register);
            let class = if fact.is_some_and(|fact| {
                fact.storage == StorageClass::Erased
                    || fact.ownership == OwnershipCategory::ZstErased
            }) {
                RegisterClass::Erased
            } else {
                match descriptor.representation() {
                    Type::RefShared { .. } => RegisterClass::SharedReference,
                    Type::RefUnique { .. } => RegisterClass::UniqueReference,
                    _ if fact
                        .is_some_and(|fact| fact.ownership == OwnershipCategory::CopyValue)
                        || descriptor.claimed_duplicable() =>
                    {
                        RegisterClass::CopyValue
                    }
                    _ => RegisterClass::Owned,
                }
            };
            intervals.push(LiveInterval {
                register: register as Register,
                ty,
                start,
                end,
                class,
                addressable: addressable[register]
                    || fact.is_some_and(|fact| fact.storage == StorageClass::Place),
                local_block: activity_blocks[register].flatten(),
            });
        }
        intervals.sort_by_key(|interval| (interval.start, interval.end, interval.register));
        Ok(Self {
            intervals,
            work: meter.work,
        })
    }

    pub(crate) fn intervals(&self) -> &[LiveInterval] {
        &self.intervals
    }

    pub(crate) fn work(&self) -> u64 {
        self.work
    }

    pub(crate) fn invalidated_by(mask: u8) -> bool {
        mask & Self::INVALIDATED_BY != 0
    }
}

impl EdgeLiveness {
    pub(crate) const INVALIDATED_BY: u8 = analysis::CFG | analysis::USES | analysis::FLOW;

    pub(crate) fn compute(function: &Function, budget: u64) -> Result<Self, AnalysisError> {
        let cfg = ControlFlowAnalysis::compute(function, budget)?;
        let mut meter = Meter {
            function: function.name.clone(),
            limit: budget,
            work: cfg.work,
        };
        let blocks = function
            .blocks
            .iter()
            .map(|block| (BlockId(block.id), block))
            .collect::<BTreeMap<_, _>>();
        let mut live_in = blocks
            .keys()
            .copied()
            .map(|id| (id, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        let mut order = cfg.rpo().to_vec();
        let unreachable = blocks
            .keys()
            .filter(|block| !order.contains(block))
            .copied()
            .collect::<Vec<_>>();
        order.extend(unreachable);
        loop {
            let mut changed = false;
            for &id in order.iter().rev() {
                meter.step()?;
                let block = blocks[&id];
                let mut live = BTreeSet::new();
                for edge in cfg.edges().iter().filter(|edge| edge.source == id) {
                    live.extend(live_in[&edge.target].iter().copied());
                    live.extend(
                        edge_arguments(&block.terminator, edge.ordinal)
                            .iter()
                            .map(|value| value.register),
                    );
                }
                live.extend(block_local_uses(block));
                for definition in block_definitions(block) {
                    live.remove(&definition);
                }
                if live != live_in[&id] {
                    live_in.insert(id, live);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let mut live_on_edge = BTreeMap::new();
        for edge in cfg.edges() {
            meter.step()?;
            let block = blocks[&edge.source];
            let mut live = live_in[&edge.target].clone();
            live.extend(
                edge_arguments(&block.terminator, edge.ordinal)
                    .iter()
                    .map(|value| value.register),
            );
            live_on_edge.insert(*edge, live);
        }
        Ok(Self {
            live_in,
            live_on_edge,
            work: meter.work,
        })
    }

    pub(crate) fn live_in(&self, block: BlockId) -> Option<&BTreeSet<Register>> {
        self.live_in.get(&block)
    }
    pub(crate) fn live_on_any_edge(
        &self,
        source: BlockId,
        target: BlockId,
        register: Register,
    ) -> bool {
        self.live_on_edge.iter().any(|(edge, live)| {
            edge.source == source && edge.target == target && live.contains(&register)
        })
    }
    pub(crate) fn work(&self) -> u64 {
        self.work
    }
    pub(crate) fn invalidated_by(mask: u8) -> bool {
        mask & Self::INVALIDATED_BY != 0
    }
}

struct Meter {
    function: String,
    limit: u64,
    work: u64,
}
impl Meter {
    fn new(function: &str, limit: u64) -> Self {
        Self {
            function: function.to_owned(),
            limit,
            work: 0,
        }
    }
    fn step(&mut self) -> Result<(), AnalysisError> {
        self.work = self.work.saturating_add(1);
        if self.work > self.limit {
            Err(AnalysisError {
                function: self.function.clone(),
                kind: AnalysisErrorKind::BudgetExceeded {
                    limit: self.limit,
                    attempted: self.work,
                },
            })
        } else {
            Ok(())
        }
    }
}

fn block_edges(terminator: &Terminator) -> Vec<u32> {
    match terminator {
        Terminator::Goto(edge) | Terminator::Leave { target: edge, .. } => vec![edge.target],
        Terminator::Switch {
            cases, otherwise, ..
        } => cases
            .iter()
            .map(|(_, edge)| edge.target)
            .chain([otherwise.target])
            .collect(),
        Terminator::Call { normal, .. }
        | Terminator::CallSelf { normal, .. }
        | Terminator::CallKnownReceiver { normal, .. }
        | Terminator::HostCall { normal, .. }
        | Terminator::CallIndirect { normal, .. }
        | Terminator::Handle { normal, .. }
        | Terminator::Resume { normal, .. }
        | Terminator::Cancel { normal, .. } => vec![normal.target],
        Terminator::Perform { resume, .. } => resume.iter().map(|edge| edge.target).collect(),
        Terminator::Return { .. }
        | Terminator::TailResume { .. }
        | Terminator::TailCall { .. }
        | Terminator::TailCallSelf { .. }
        | Terminator::TailCallKnownReceiver { .. }
        | Terminator::TailCallIndirect { .. }
        | Terminator::Abort { .. }
        | Terminator::Unreachable => vec![],
    }
}

fn edge_arguments(terminator: &Terminator, ordinal: u32) -> &[Operand] {
    let ordinal = ordinal as usize;
    match terminator {
        Terminator::Goto(edge) | Terminator::Leave { target: edge, .. } => {
            (ordinal == 0).then_some(edge.args.as_slice())
        }
        Terminator::Switch {
            cases, otherwise, ..
        } => cases
            .get(ordinal)
            .map(|(_, edge)| edge.args.as_slice())
            .or_else(|| (ordinal == cases.len()).then_some(otherwise.args.as_slice())),
        Terminator::Call { normal, .. }
        | Terminator::CallSelf { normal, .. }
        | Terminator::CallKnownReceiver { normal, .. }
        | Terminator::HostCall { normal, .. }
        | Terminator::CallIndirect { normal, .. }
        | Terminator::Handle { normal, .. }
        | Terminator::Resume { normal, .. }
        | Terminator::Cancel { normal, .. } => (ordinal == 0).then_some(normal.args.as_slice()),
        Terminator::Perform { resume, .. } => (ordinal == 0)
            .then(|| resume.as_ref().map(|edge| edge.args.as_slice()))
            .flatten(),
        _ => None,
    }
    .unwrap_or(&[])
}

fn instruction_definition(instruction: &InstructionKind) -> Option<Register> {
    match instruction {
        InstructionKind::Const { dst, .. }
        | InstructionKind::Copy { dst, .. }
        | InstructionKind::Move { dst, .. }
        | InstructionKind::Borrow { dst, .. }
        | InstructionKind::ProjectBorrow { dst, .. }
        | InstructionKind::Reborrow { dst, .. }
        | InstructionKind::DerefCopy { dst, .. }
        | InstructionKind::DerefMove { dst, .. }
        | InstructionKind::Construct { dst, .. }
        | InstructionKind::ProjectCopy { dst, .. }
        | InstructionKind::ProjectMove { dst, .. }
        | InstructionKind::EnumTag { dst, .. }
        | InstructionKind::Primitive { dst, .. }
        | InstructionKind::MakeCallable { dst, .. }
        | InstructionKind::MakeHandler { dst, .. }
        | InstructionKind::MakeHandlerShared { dst, .. }
        | InstructionKind::MakeBindingPack { dst, .. } => Some(*dst),
        InstructionKind::EndBorrow { .. }
        | InstructionKind::DerefStore { .. }
        | InstructionKind::Deconstruct { .. }
        | InstructionKind::LabelPush { .. }
        | InstructionKind::LabelPop { .. }
        | InstructionKind::Drop { .. } => None,
    }
}

fn terminator_definition(terminator: &Terminator) -> Option<Register> {
    match terminator {
        Terminator::Call { result, .. }
        | Terminator::CallSelf { result, .. }
        | Terminator::CallKnownReceiver { result, .. }
        | Terminator::HostCall { result, .. }
        | Terminator::CallIndirect { result, .. }
        | Terminator::Perform { result, .. } => *result,
        Terminator::Handle { result, .. }
        | Terminator::Resume { result, .. }
        | Terminator::Cancel { result, .. } => Some(*result),
        _ => None,
    }
}

fn instruction_uses(instruction: &InstructionKind) -> BTreeSet<Register> {
    let mut used = BTreeSet::new();
    let mut operands = |values: &[Operand]| {
        used.extend(values.iter().map(|value| value.register));
    };
    match instruction {
        InstructionKind::Copy { src, .. } | InstructionKind::Move { src, .. } => {
            used.insert(src.register);
        }
        InstructionKind::Borrow { src, .. }
        | InstructionKind::ProjectBorrow { src, .. }
        | InstructionKind::Reborrow { src, .. }
        | InstructionKind::DerefCopy { src, .. }
        | InstructionKind::DerefMove { src, .. }
        | InstructionKind::EndBorrow { reference: src }
        | InstructionKind::Deconstruct { src }
        | InstructionKind::EnumTag { src, .. } => {
            used.insert(*src);
        }
        InstructionKind::Construct { fields, .. }
        | InstructionKind::Primitive { args: fields, .. }
        | InstructionKind::MakeCallable {
            captures: fields, ..
        }
        | InstructionKind::MakeHandler {
            clauses: fields, ..
        }
        | InstructionKind::MakeHandlerShared {
            captures: fields, ..
        }
        | InstructionKind::MakeBindingPack {
            payloads: fields, ..
        } => operands(fields),
        InstructionKind::ProjectCopy { src, .. }
        | InstructionKind::ProjectMove { src, .. }
        | InstructionKind::Drop { owner: src } => {
            used.insert(src.register);
        }
        InstructionKind::DerefStore { dst, src } => {
            used.insert(*dst);
            used.insert(src.register);
        }
        InstructionKind::Const { .. }
        | InstructionKind::LabelPush { .. }
        | InstructionKind::LabelPop { .. } => {}
    }
    used
}

fn terminator_uses(terminator: &Terminator) -> BTreeSet<Register> {
    let mut block = BasicBlock {
        id: 0,
        params: vec![],
        statements: vec![],
        terminator: terminator.clone(),
    };
    let mut used = block_local_uses(&block);
    for ordinal in 0..block_edges(&block.terminator).len() as u32 {
        used.extend(
            edge_arguments(&block.terminator, ordinal)
                .iter()
                .map(|operand| operand.register),
        );
    }
    // Make it explicit that this helper owns no MIR mutation despite using the
    // exhaustive block-use implementation.
    block.statements.clear();
    used
}

fn block_definitions(block: &BasicBlock) -> BTreeSet<Register> {
    let mut result = block
        .params
        .iter()
        .map(|param| param.register)
        .collect::<BTreeSet<_>>();
    result.extend(
        block
            .statements
            .iter()
            .filter_map(|statement| match &statement.kind {
                InstructionKind::Const { dst, .. }
                | InstructionKind::Copy { dst, .. }
                | InstructionKind::Move { dst, .. }
                | InstructionKind::Borrow { dst, .. }
                | InstructionKind::ProjectBorrow { dst, .. }
                | InstructionKind::Reborrow { dst, .. }
                | InstructionKind::DerefCopy { dst, .. }
                | InstructionKind::DerefMove { dst, .. }
                | InstructionKind::Construct { dst, .. }
                | InstructionKind::ProjectCopy { dst, .. }
                | InstructionKind::ProjectMove { dst, .. }
                | InstructionKind::EnumTag { dst, .. }
                | InstructionKind::Primitive { dst, .. }
                | InstructionKind::MakeCallable { dst, .. }
                | InstructionKind::MakeHandler { dst, .. }
                | InstructionKind::MakeHandlerShared { dst, .. }
                | InstructionKind::MakeBindingPack { dst, .. } => Some(*dst),
                _ => None,
            }),
    );
    let terminator_result = match &block.terminator {
        Terminator::Call { result, .. }
        | Terminator::CallSelf { result, .. }
        | Terminator::CallKnownReceiver { result, .. }
        | Terminator::HostCall { result, .. }
        | Terminator::CallIndirect { result, .. }
        | Terminator::Perform { result, .. } => *result,
        Terminator::Handle { result, .. }
        | Terminator::Resume { result, .. }
        | Terminator::Cancel { result, .. } => Some(*result),
        _ => None,
    };
    result.extend(terminator_result);
    result
}

fn block_local_uses(block: &BasicBlock) -> BTreeSet<Register> {
    fn operands(used: &mut BTreeSet<Register>, values: &[Operand]) {
        used.extend(values.iter().map(|value| value.register));
    }
    let mut used = BTreeSet::new();
    for statement in &block.statements {
        match &statement.kind {
            InstructionKind::Copy { src, .. } | InstructionKind::Move { src, .. } => {
                used.insert(src.register);
            }
            InstructionKind::Borrow { src, .. }
            | InstructionKind::ProjectBorrow { src, .. }
            | InstructionKind::Reborrow { src, .. }
            | InstructionKind::DerefCopy { src, .. }
            | InstructionKind::DerefMove { src, .. }
            | InstructionKind::EndBorrow { reference: src }
            | InstructionKind::Deconstruct { src }
            | InstructionKind::EnumTag { src, .. } => {
                used.insert(*src);
            }
            InstructionKind::Construct { fields, .. }
            | InstructionKind::Primitive { args: fields, .. }
            | InstructionKind::MakeCallable {
                captures: fields, ..
            }
            | InstructionKind::MakeHandler {
                clauses: fields, ..
            }
            | InstructionKind::MakeHandlerShared {
                captures: fields, ..
            }
            | InstructionKind::MakeBindingPack {
                payloads: fields, ..
            } => operands(&mut used, fields),
            InstructionKind::ProjectCopy { src, .. }
            | InstructionKind::ProjectMove { src, .. }
            | InstructionKind::Drop { owner: src } => {
                used.insert(src.register);
            }
            InstructionKind::DerefStore { dst, src } => {
                used.insert(*dst);
                used.insert(src.register);
            }
            InstructionKind::Const { .. }
            | InstructionKind::LabelPush { .. }
            | InstructionKind::LabelPop { .. } => {}
        }
    }
    match &block.terminator {
        Terminator::Switch { discr, .. } => {
            used.insert(discr.register);
        }
        Terminator::Return { value } => operands(&mut used, value.as_slice()),
        Terminator::Call { args, .. }
        | Terminator::HostCall { args, .. }
        | Terminator::TailCall { args, .. } => operands(&mut used, args),
        Terminator::CallSelf { args, .. } | Terminator::TailCallSelf { args } => {
            used.insert(0);
            operands(&mut used, args);
        }
        Terminator::CallKnownReceiver { receiver, args, .. }
        | Terminator::TailCallKnownReceiver { receiver, args, .. } => {
            used.insert(receiver.register);
            operands(&mut used, args);
        }
        Terminator::CallIndirect { callable, args, .. }
        | Terminator::TailCallIndirect { callable, args, .. } => {
            used.insert(callable.register);
            operands(&mut used, args);
        }
        Terminator::Handle { handler, body, .. } => {
            used.insert(handler.register);
            used.insert(body.register);
        }
        Terminator::Perform {
            payloads, capture, ..
        } => {
            operands(&mut used, payloads);
            used.extend(capture.captured_owners.iter().copied());
            used.extend(capture.captured_references.iter().copied());
            used.extend(capture.captured_residuals.iter().map(|fact| fact.register));
        }
        Terminator::Resume {
            resumption, value, ..
        }
        | Terminator::TailResume {
            resumption, value, ..
        } => {
            used.insert(resumption.register);
            used.insert(value.register);
        }
        Terminator::Cancel { resumption, .. } => {
            used.insert(resumption.register);
        }
        Terminator::Goto(_)
        | Terminator::Leave { .. }
        | Terminator::Abort { .. }
        | Terminator::Unreachable => {}
    }
    used
}

fn strongly_connected(
    blocks: &BTreeMap<BlockId, &BasicBlock>,
    reachable: &BTreeSet<BlockId>,
    meter: &mut Meter,
) -> Result<Vec<BTreeSet<BlockId>>, AnalysisError> {
    struct Tarjan<'a, 'm> {
        blocks: &'a BTreeMap<BlockId, &'a BasicBlock>,
        reachable: &'a BTreeSet<BlockId>,
        meter: &'m mut Meter,
        next_index: u32,
        indices: BTreeMap<BlockId, u32>,
        low: BTreeMap<BlockId, u32>,
        stack: Vec<BlockId>,
        on_stack: BTreeSet<BlockId>,
        components: Vec<BTreeSet<BlockId>>,
    }
    impl Tarjan<'_, '_> {
        fn visit(&mut self, node: BlockId) -> Result<(), AnalysisError> {
            self.meter.step()?;
            self.indices.insert(node, self.next_index);
            self.low.insert(node, self.next_index);
            self.next_index += 1;
            self.stack.push(node);
            self.on_stack.insert(node);
            let mut successors = block_edges(&self.blocks[&node].terminator)
                .into_iter()
                .map(BlockId)
                .filter(|target| self.reachable.contains(target))
                .collect::<Vec<_>>();
            successors.sort_unstable();
            successors.dedup();
            for successor in successors {
                if !self.indices.contains_key(&successor) {
                    self.visit(successor)?;
                    self.low
                        .insert(node, self.low[&node].min(self.low[&successor]));
                } else if self.on_stack.contains(&successor) {
                    self.low
                        .insert(node, self.low[&node].min(self.indices[&successor]));
                }
            }
            if self.low[&node] == self.indices[&node] {
                let mut component = BTreeSet::new();
                loop {
                    let member = self.stack.pop().expect("Tarjan root owns a stack member");
                    self.on_stack.remove(&member);
                    component.insert(member);
                    if member == node {
                        break;
                    }
                }
                self.components.push(component);
            }
            Ok(())
        }
    }
    let mut tarjan = Tarjan {
        blocks,
        reachable,
        meter,
        next_index: 0,
        indices: BTreeMap::new(),
        low: BTreeMap::new(),
        stack: Vec::new(),
        on_stack: BTreeSet::new(),
        components: Vec::new(),
    };
    for &node in reachable {
        if !tarjan.indices.contains_key(&node) {
            tarjan.visit(node)?;
        }
    }
    tarjan
        .components
        .sort_by_key(|component| component.iter().next().copied());
    Ok(tarjan.components)
}

#[cfg(test)]
mod tests {
    use grandiose_vm::{Constant, I64, UNIT};

    use super::*;
    use crate::compiler_mir::{
        BlockParam, BlockParamRole, Edge, FeatureBits, HandlerSiteFact, Instruction, LocalFact,
        MirPhase, PlaceFlow, ScopeId, UseMode,
    };
    use crate::span::Span;

    fn edge(target: u32) -> Edge {
        Edge {
            target,
            args: vec![],
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

    fn function(blocks: Vec<BasicBlock>) -> Function {
        Function {
            declaration: 0,
            name: "analysis".into(),
            params: vec![],
            result: UNIT,
            receiver_mode: None,
            receiver_type: UNIT,
            no_return: false,
            outward_protocols: vec![],
            register_types: vec![I64, I64],
            entry: 0,
            blocks,
            phase: MirPhase::Raw,
            features: FeatureBits::empty(),
            return_cleanup: vec![],
            flow: PlaceFlow::default(),
            invalid_analyses: 0,
        }
    }

    fn switch(left: u32, right: u32) -> Terminator {
        Terminator::Switch {
            discr: Operand {
                register: 0,
                mode: UseMode::Copy,
            },
            cases: vec![(Constant::I64(0), edge(left))],
            otherwise: edge(right),
        }
    }

    #[test]
    fn predecessors_rpo_dominators_and_natural_preheaders_are_canonical() {
        let body = function(vec![
            block(0, Terminator::Goto(edge(1))),
            block(1, switch(2, 3)),
            block(2, Terminator::Goto(edge(1))),
            block(3, Terminator::Return { value: None }),
        ]);
        let analysis = ControlFlowAnalysis::compute(&body, 1_000).unwrap();
        assert_eq!(
            analysis.rpo(),
            &[BlockId(0), BlockId(1), BlockId(3), BlockId(2)]
        );
        assert_eq!(
            analysis.predecessors(BlockId(1)).unwrap(),
            &BTreeSet::from([BlockId(0), BlockId(2)])
        );
        assert!(analysis.dominates(BlockId(1), BlockId(2)));
        assert!(!analysis.dominates(BlockId(2), BlockId(1)));
        assert_eq!(analysis.loops().len(), 1);
        assert_eq!(analysis.loops()[0].header, BlockId(1));
        assert_eq!(analysis.loops()[0].latches, BTreeSet::from([BlockId(2)]));
        assert_eq!(analysis.loops()[0].preheader, Some(BlockId(0)));
        assert!(analysis.irreducible().is_empty());
    }

    #[test]
    fn irreducible_two_entry_cycle_is_reported_without_a_false_natural_loop() {
        let body = function(vec![
            block(0, switch(1, 2)),
            block(1, Terminator::Goto(edge(2))),
            block(2, Terminator::Goto(edge(1))),
        ]);
        let analysis = ControlFlowAnalysis::compute(&body, 1_000).unwrap();
        assert_eq!(
            analysis.irreducible(),
            &BTreeSet::from([BlockId(1), BlockId(2)])
        );
        assert!(analysis.loops().is_empty());
    }

    #[test]
    fn cleanup_handler_edges_and_register_liveness_survive_join_analysis() {
        let mut entry = block(0, switch(1, 2));
        if let Terminator::Switch {
            cases, otherwise, ..
        } = &mut entry.terminator
        {
            cases[0].1.args.push(Operand {
                register: 0,
                mode: UseMode::Move,
            });
            otherwise.args.push(Operand {
                register: 1,
                mode: UseMode::Move,
            });
        }
        let mut cleanup = block(1, Terminator::Goto(edge(3)));
        cleanup.params.push(BlockParam {
            register: 1,
            ty: I64,
            role: BlockParamRole::ProtectedExitValue,
        });
        let mut handler = block(2, Terminator::Goto(edge(3)));
        handler.params.push(BlockParam {
            register: 1,
            ty: I64,
            role: BlockParamRole::Ordinary,
        });
        let mut body = function(vec![
            entry,
            cleanup,
            handler,
            block(3, Terminator::Return { value: None }),
        ]);
        body.flow.handlers.push(HandlerSiteFact {
            block: 2,
            scope: ScopeId(0),
        });
        let cfg = ControlFlowAnalysis::compute(&body, 1_000).unwrap();
        assert_eq!(
            cfg.predecessors(BlockId(3)).unwrap(),
            &BTreeSet::from([BlockId(1), BlockId(2)])
        );
        let live = EdgeLiveness::compute(&body, 2_000).unwrap();
        assert!(live.live_on_any_edge(BlockId(0), BlockId(1), 0));
        assert!(live.live_on_any_edge(BlockId(0), BlockId(2), 1));
        assert!(!live.live_on_any_edge(BlockId(0), BlockId(1), 1));
    }

    #[test]
    fn analysis_budgets_and_invalidation_masks_are_structured_and_precise() {
        let body = function(vec![block(0, Terminator::Return { value: None })]);
        assert!(matches!(
            ControlFlowAnalysis::compute(&body, 0).unwrap_err().kind,
            AnalysisErrorKind::BudgetExceeded {
                limit: 0,
                attempted: 1
            }
        ));
        assert!(ControlFlowAnalysis::invalidated_by(analysis::CFG));
        assert!(!ControlFlowAnalysis::invalidated_by(analysis::USES));
        assert!(EdgeLiveness::invalidated_by(analysis::USES));
        assert!(EdgeLiveness::invalidated_by(analysis::FLOW));
        assert!(!EdgeLiveness::invalidated_by(analysis::VALUES));
    }

    #[test]
    fn register_intervals_classify_ownership_references_places_and_erasure() {
        let mut types = Type::predefined();
        let owned = types.len() as TypeId;
        types.push(Type::I64.restricted(false, false));
        let shared = types.len() as TypeId;
        types.push(Type::RefShared { referent: I64 });
        let unique = types.len() as TypeId;
        types.push(Type::RefUnique { referent: I64 });
        let mut entry = block(
            0,
            Terminator::Return {
                value: Some(Operand {
                    register: 3,
                    mode: UseMode::Copy,
                }),
            },
        );
        entry.statements.extend([
            Instruction {
                span: Span::default(),
                kind: InstructionKind::Borrow {
                    dst: 1,
                    src: 0,
                    unique: false,
                },
            },
            Instruction {
                span: Span::default(),
                kind: InstructionKind::Borrow {
                    dst: 2,
                    src: 0,
                    unique: true,
                },
            },
            Instruction {
                span: Span::default(),
                kind: InstructionKind::Const {
                    dst: 3,
                    value: Constant::I64(1),
                },
            },
        ]);
        let mut body = function(vec![entry]);
        body.register_types = vec![owned, shared, unique, I64];
        body.flow.locals = body
            .register_types
            .iter()
            .map(|&ty| LocalFact::conservative(ty, &types[ty as usize]))
            .collect();
        body.flow.locals[0].storage = StorageClass::Place;
        body.flow.locals[3].storage = StorageClass::Erased;
        body.flow.locals[3].ownership = OwnershipCategory::ZstErased;

        let intervals = RegisterIntervals::compute(&body, &types, 1_000).unwrap();
        let by_register = intervals
            .intervals()
            .iter()
            .map(|interval| (interval.register, interval))
            .collect::<BTreeMap<_, _>>();
        assert_eq!(by_register[&0].class, RegisterClass::Owned);
        assert!(by_register[&0].addressable);
        assert_eq!(by_register[&1].class, RegisterClass::SharedReference);
        assert_eq!(by_register[&2].class, RegisterClass::UniqueReference);
        assert_eq!(by_register[&3].class, RegisterClass::Erased);
        assert!(
            by_register
                .values()
                .all(|interval| interval.start <= interval.end)
        );
        assert!(RegisterIntervals::invalidated_by(analysis::VALUES));
        assert!(!RegisterIntervals::invalidated_by(analysis::COST));
    }

    #[test]
    fn register_intervals_retain_exported_referents_after_borrow_proof_erasure() {
        let mut types = Type::predefined();
        let shared = types.len() as TypeId;
        types.push(Type::RefShared { referent: I64 });
        let mut entry = block(0, Terminator::Return { value: None });
        entry.statements.push(Instruction {
            span: Span::default(),
            kind: InstructionKind::EndBorrow { reference: 2 },
        });
        let mut body = function(vec![entry]);
        body.register_types = vec![I64, I64, shared];
        body.flow.loans.push(crate::compiler_mir::LoanFact {
            kind: crate::compiler_mir::LoanKind::Shared,
            reference: 2,
            borrowed: crate::compiler_mir::Place {
                base: 1,
                projection: vec![],
            },
            parent: None,
            region: crate::compiler_mir::RegionId(0),
            issued_block: 0,
            source: crate::compiler_mir::SourceInfoId(0),
        });

        let intervals = RegisterIntervals::compute(&body, &types, 1_000).unwrap();
        let by_register = intervals
            .intervals()
            .iter()
            .map(|interval| (interval.register, interval))
            .collect::<BTreeMap<_, _>>();
        assert!(by_register.contains_key(&2));
        assert!(by_register[&1].addressable);
    }
}
