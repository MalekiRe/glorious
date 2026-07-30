//! Deterministic point-set liveness used by the bootstrap region foundation,
//! plus the ownership dataflow engine backing `ImportAndValidatePlaceFlow`,
//! `ElaborateCleanup`, and the `Cleanup`-phase MIR validators.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use grandiose_vm::{Primitive, Type, TypeId};

use crate::compiler_core::PointId;
use crate::compiler_mir::{
    BasicBlock, DropGlueKind, Edge, Function, InitAtEntry, InstructionKind, LabelId, LocalFact,
    Operand, OwnershipCategory, Place, Projection, Register, Terminator, UseMode,
};

#[derive(Clone, Debug, Default)]
pub(crate) struct Point {
    pub(crate) uses: BTreeSet<String>,
    pub(crate) kills: BTreeSet<String>,
    pub(crate) successors: BTreeSet<PointId>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct PointGraph {
    pub(crate) points: BTreeMap<PointId, Point>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Solution {
    pub(crate) live_in: BTreeMap<PointId, BTreeSet<String>>,
    pub(crate) live_out: BTreeMap<PointId, BTreeSet<String>>,
}

impl PointGraph {
    pub(crate) fn solve(&self) -> Solution {
        let mut solution = Solution::default();
        for point in self.points.keys() {
            solution.live_in.insert(*point, BTreeSet::new());
            solution.live_out.insert(*point, BTreeSet::new());
        }
        loop {
            let mut changed = false;
            for (id, point) in self.points.iter().rev() {
                let live_out = point
                    .successors
                    .iter()
                    .flat_map(|successor| {
                        solution
                            .live_in
                            .get(successor)
                            .into_iter()
                            .flat_map(|live| live.iter().cloned())
                    })
                    .collect::<BTreeSet<_>>();
                let mut live_in = live_out
                    .iter()
                    .filter(|name| !point.kills.contains(*name))
                    .cloned()
                    .collect::<BTreeSet<_>>();
                live_in.extend(point.uses.iter().cloned());
                changed |= solution.live_out.get(id) != Some(&live_out)
                    || solution.live_in.get(id) != Some(&live_in);
                solution.live_out.insert(*id, live_out);
                solution.live_in.insert(*id, live_in);
            }
            if !changed {
                return solution;
            }
        }
    }
}

/// One deterministic ownership-dataflow error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct FlowError {
    pub(crate) block: Option<u32>,
    pub(crate) message: String,
}

fn flow_error(block: u32, message: impl Into<String>) -> FlowError {
    FlowError {
        block: Some(block),
        message: message.into(),
    }
}

/// Initialization state of one register at one program point.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RegState {
    /// Never defined on this path. Joins treat this as `Consumed`.
    Undefined,
    /// Holds a whole initialized value.
    Live,
    /// Aggregate shell with the per-field initialization bitmap.
    Partial(Vec<bool>),
    /// Conditionally initialized behind a drop flag; the VM `Empty` register
    /// state realizes the flag at runtime.
    MaybeLive,
    /// Moved, destroyed, deconstructed, or ended.
    Consumed,
}

impl RegState {
    fn is_live(&self) -> bool {
        matches!(self, Self::Live | Self::Partial(_) | Self::MaybeLive)
    }

    fn normalized(&self) -> &Self {
        match self {
            Self::Undefined => &Self::Consumed,
            other => other,
        }
    }
}

/// One live loan at one program point, keyed by its reference register.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LiveLoan {
    /// Stable loan identity from the deterministic per-body loan table.
    pub(crate) id: u32,
    pub(crate) unique: bool,
    /// Reference received from the caller; its referent is caller-owned and
    /// never conflicts with locally issued loans.
    pub(crate) external: bool,
    pub(crate) borrowed: Place,
    /// Reference register of the suspended parent loan, if reborrowed.
    pub(crate) parent: Option<Register>,
    /// Number of live child loans currently suspending this one.
    pub(crate) suspended: u32,
}

/// Accumulated quantitative owned-use interval for one register.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct UseCount {
    pub(crate) lower: u32,
    /// `None` is the widened unbounded upper.
    pub(crate) upper: Option<u32>,
}

/// Sparse initialization summary for one runtime array owner. Exact indices
/// are retained while the length is known; a dynamic move poisons exact reads
/// until the array is wholly consumed because one unknown slot is empty.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ArraySlotState {
    pub(crate) length: Option<u64>,
    pub(crate) empty: BTreeSet<u64>,
    pub(crate) dynamic_hole: bool,
    /// Exact reference origin installed in an initialized slot. This mirrors
    /// the VM carrier path `[ARRAY_SLOT_PATH, index, ...element_path]` without
    /// serializing the VM sentinel into MIR facts.
    pub(crate) reference_origins: BTreeMap<u64, StoredReferenceOrigin>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StoredReferenceOrigin {
    pub(crate) unique: bool,
    pub(crate) external: bool,
    pub(crate) borrowed: Place,
    /// Named parent handle from which a unique reference was reborrowed into
    /// this aggregate. The parent remains present in MIR state but is the
    /// callable environment's own suspended capability, not a competing
    /// per-call alias.
    pub(crate) parent: Option<Register>,
}

/// A bounded, ABI-independent account of the array ownership effects an
/// ordinary function applies to one of its formal arguments.  These facts are
/// inferred from MIR bodies and composed through direct calls; they are never
/// accepted from source declarations or runtime metadata.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ArrayIndexSummary {
    Constant(u64),
    Parameter(u32),
    Dynamic,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ArrayEffectKind {
    Observe,
    MoveOut,
    Restore,
    Push,
    Pop,
    Dense,
    Finish,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ArrayCallEffect {
    pub(crate) owner_parameter: u32,
    pub(crate) kind: ArrayEffectKind,
    pub(crate) index: Option<ArrayIndexSummary>,
    /// Formal parameter whose reference origin is installed by Set/Push.
    /// `None` for non-writing effects or writes of a local/opaque value.
    pub(crate) value_parameter: Option<u32>,
    /// Reference-leaf path inside that value. The current PlaceFlow engine
    /// exports the exact single-leaf root as `[]`; the path is explicit so the
    /// VM contract can extend to aggregate elements without changing shape.
    pub(crate) value_path: Vec<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ArrayResultSummary {
    Empty,
    Filled(ArrayIndexSummary),
    Parameter(u32),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ArrayCallSummary {
    pub(crate) effects: Vec<ArrayCallEffect>,
    pub(crate) result: Option<ArrayResultSummary>,
}

impl UseCount {
    const ZERO: Self = Self {
        lower: 0,
        upper: Some(0),
    };

    fn bump(&mut self) {
        self.lower = self.lower.saturating_add(1);
        self.upper = self.upper.map(|upper| upper.saturating_add(1));
    }

    fn hull(self, other: Self) -> Self {
        Self {
            lower: self.lower.min(other.lower),
            upper: match (self.upper, other.upper) {
                (Some(left), Some(right)) => Some(left.max(right)),
                _ => None,
            },
        }
    }
}

/// The abstract ownership state at one program point.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OwnState {
    pub(crate) regs: Vec<RegState>,
    /// Fields whose initialization differs across predecessor paths. A true
    /// bit is governed by a per-field drop flag and may be Empty at runtime.
    pub(crate) conditional_fields: BTreeMap<Register, Vec<bool>>,
    /// Sparse runtime-array slot summaries keyed by the owned array register.
    pub(crate) array_slots: BTreeMap<Register, ArraySlotState>,
    /// Exact origins of reference leaves stored inside aggregate registers.
    /// Paths are runtime field indices from the aggregate root.
    pub(crate) aggregate_reference_origins:
        BTreeMap<Register, BTreeMap<Vec<u32>, StoredReferenceOrigin>>,
    /// Exact integer constants used as array indices and lengths.
    pub(crate) constants: Vec<Option<u64>>,
    /// Proven active enum variant for each register. A fact is introduced by
    /// enum construction or by an `EnumTag` switch edge and is forgotten at
    /// joins that combine distinct variants. Partial enum shells may never
    /// forget this fact because their field bitmap is variant-relative.
    pub(crate) active_variants: Vec<Option<u32>>,
    /// For a live tag register, the enum register from which it was read.
    /// This lets switch edges refine the active variant without baking
    /// pattern semantics into MIR instructions.
    pub(crate) enum_tag_sources: Vec<Option<Register>>,
    /// Live registers in initialization (age) order, oldest first. This is
    /// exactly the order the bytecode verifier reconstructs; reversing it
    /// yields the cleanup list at the point.
    pub(crate) order: Vec<Register>,
    /// Remembered owner ages for deconstructed shells that may be
    /// reconstructed into the same storage place.
    pub(crate) shell_ages: Vec<Option<usize>>,
    pub(crate) loans: BTreeMap<Register, LiveLoan>,
    /// Unique references whose referent is temporarily moved out.
    pub(crate) holes: BTreeSet<Register>,
    pub(crate) uses: Vec<UseCount>,
    /// One verifier-style logical quantity group for values containing exactly
    /// one resumption leaf. Copying creates another owned view of the same
    /// group; a consuming use through any view advances the shared count.
    pub(crate) quantity_groups: Vec<Option<Register>>,
    pub(crate) quantity_uses: Vec<UseCount>,
    /// Active nonlocal destinations, outermost first. Each entry snapshots
    /// the owners that predate its `LabelPush`; `Leave` preserves precisely
    /// that baseline (plus its protected result) and abandons newer owners.
    pub(crate) labels: Vec<LabelBaseline>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LabelBaseline {
    pub(crate) label: LabelId,
    pub(crate) owners: Vec<Register>,
}

impl OwnState {
    fn cleanup_list(&self) -> Vec<Register> {
        self.order.iter().rev().copied().collect()
    }

    fn agrees_with(&self, other: &Self) -> bool {
        self.order == other.order
            && self.holes == other.holes
            && self.loans == other.loans
            && self.conditional_fields == other.conditional_fields
            && self.array_slots == other.array_slots
            && self.aggregate_reference_origins == other.aggregate_reference_origins
            && self.constants == other.constants
            && self.quantity_groups == other.quantity_groups
            && self
                .regs
                .iter()
                .zip(&other.regs)
                .all(|(left, right)| left.normalized() == right.normalized())
    }
}

/// The deterministic per-body loan identity table: external reference
/// parameters first (ascending register), then every borrow-issuing
/// instruction in block-ID/statement order.
#[derive(Clone, Debug, Default)]
pub(crate) struct LoanTable {
    pub(crate) external: BTreeMap<Register, u32>,
    pub(crate) issued: BTreeMap<(u32, usize), u32>,
    pub(crate) count: u32,
}

pub(crate) fn loan_table(function: &Function, types: &[Type]) -> LoanTable {
    let mut table = LoanTable::default();
    for (register, &ty) in function.register_types.iter().enumerate() {
        if matches!(
            types[ty as usize].representation(),
            Type::RefShared { .. } | Type::RefUnique { .. }
        ) {
            table.external.insert(register as Register, table.count);
            table.count += 1;
        }
    }
    let mut ordered = function.blocks.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|block| block.id);
    for block in ordered {
        for (index, statement) in block.statements.iter().enumerate() {
            if matches!(
                statement.kind,
                InstructionKind::Borrow { .. }
                    | InstructionKind::ProjectBorrow { .. }
                    | InstructionKind::Reborrow { .. }
                    | InstructionKind::Primitive {
                        primitive: Primitive::ArrayGetBorrowShared
                            | Primitive::ArrayGetBorrowUnique,
                        ..
                    }
            ) {
                table.issued.insert((block.id, index), table.count);
                table.count += 1;
            }
        }
    }
    table
}

#[derive(Clone, Debug)]
enum ArraySummarySymbol {
    Unknown,
    Parameter { parameter: u32, path: Vec<u32> },
    Constant(u64),
    Fresh(ArrayResultSummary),
    Callable(u32),
}

fn summary_index_of(symbol: &ArraySummarySymbol) -> ArrayIndexSummary {
    match symbol {
        ArraySummarySymbol::Constant(value) => ArrayIndexSummary::Constant(*value),
        ArraySummarySymbol::Parameter { parameter, path } if path.is_empty() => {
            ArrayIndexSummary::Parameter(*parameter)
        }
        ArraySummarySymbol::Unknown
        | ArraySummarySymbol::Parameter { .. }
        | ArraySummarySymbol::Fresh(_)
        | ArraySummarySymbol::Callable(_) => ArrayIndexSummary::Dynamic,
    }
}

fn constant_u64(value: &grandiose_vm::Constant) -> Option<u64> {
    use grandiose_vm::Constant;
    match value {
        Constant::U8(value) => Some(u64::from(*value)),
        Constant::U16(value) => Some(u64::from(*value)),
        Constant::U32(value) => Some(u64::from(*value)),
        Constant::U64(value) | Constant::Usize(value) => Some(*value),
        _ => None,
    }
}

fn translate_index(
    index: &ArrayIndexSummary,
    args: &[Operand],
    symbols: &[ArraySummarySymbol],
) -> ArrayIndexSummary {
    match index {
        ArrayIndexSummary::Constant(value) => ArrayIndexSummary::Constant(*value),
        ArrayIndexSummary::Parameter(parameter) => args
            .get(*parameter as usize)
            .map(|operand| summary_index_of(&symbols[operand.register as usize]))
            .unwrap_or(ArrayIndexSummary::Dynamic),
        ArrayIndexSummary::Dynamic => ArrayIndexSummary::Dynamic,
    }
}

fn compose_array_call_summary(
    callee: &ArrayCallSummary,
    args: &[Operand],
    symbols: &[ArraySummarySymbol],
    effects: &mut Vec<ArrayCallEffect>,
) -> Option<ArraySummarySymbol> {
    for effect in &callee.effects {
        let owner = args.get(effect.owner_parameter as usize)?;
        let ArraySummarySymbol::Parameter {
            parameter: owner_parameter,
            path: owner_path,
        } = &symbols[owner.register as usize]
        else {
            return None;
        };
        if !owner_path.is_empty() {
            return None;
        }
        let value_source = effect.value_parameter.and_then(|parameter| {
            let value = args.get(parameter as usize)?;
            match &symbols[value.register as usize] {
                ArraySummarySymbol::Parameter { parameter, path } => {
                    Some((*parameter, path.clone()))
                }
                _ => None,
            }
        });
        if effect.value_parameter.is_some() && value_source.is_none() {
            return None;
        }
        let mut value_path = value_source
            .as_ref()
            .map(|(_, path)| path.clone())
            .unwrap_or_default();
        value_path.extend(&effect.value_path);
        effects.push(ArrayCallEffect {
            owner_parameter: *owner_parameter,
            kind: effect.kind,
            index: effect
                .index
                .as_ref()
                .map(|index| translate_index(index, args, symbols)),
            value_parameter: value_source.map(|(parameter, _)| parameter),
            value_path,
        });
    }
    Some(match callee.result.as_ref() {
        Some(ArrayResultSummary::Empty) => ArraySummarySymbol::Fresh(ArrayResultSummary::Empty),
        Some(ArrayResultSummary::Filled(length)) => ArraySummarySymbol::Fresh(
            ArrayResultSummary::Filled(translate_index(length, args, symbols)),
        ),
        Some(ArrayResultSummary::Parameter(parameter)) => args
            .get(*parameter as usize)
            .map(|operand| symbols[operand.register as usize].clone())
            .unwrap_or(ArraySummarySymbol::Unknown),
        None => ArraySummarySymbol::Unknown,
    })
}

fn summary_edge_statically_diverges(
    blocks: &BTreeMap<u32, &BasicBlock>,
    edge: &Edge,
    visiting: &mut BTreeSet<u32>,
) -> bool {
    if !visiting.insert(edge.target) {
        return false;
    }
    let result = blocks
        .get(&edge.target)
        .is_some_and(|block| match &block.terminator {
            Terminator::Unreachable => true,
            Terminator::Goto(next) if block.statements.is_empty() => {
                summary_edge_statically_diverges(blocks, next, visiting)
            }
            _ => false,
        });
    visiting.remove(&edge.target);
    result
}

fn summary_edge_is_effectless_recursive_forwarder(
    blocks: &BTreeMap<u32, &BasicBlock>,
    edge: &Edge,
    function: &Function,
    recursive_group: &BTreeSet<u32>,
    types: &[Type],
    symbols: &[ArraySummarySymbol],
) -> bool {
    let Some(block) = blocks.get(&edge.target) else {
        return false;
    };
    if !block.statements.is_empty() {
        return false;
    }
    let args = match &block.terminator {
        Terminator::TailCallSelf { args } if recursive_group.contains(&function.declaration) => {
            args
        }
        Terminator::TailCall {
            function: callee,
            args,
        } if recursive_group.contains(callee) => args,
        _ => return false,
    };
    args.iter().enumerate().all(|(parameter, argument)| {
        let tracked = function.params.get(parameter).is_some_and(|ty| {
            matches!(
                types[*ty as usize].representation(),
                Type::Array { .. } | Type::RefShared { .. } | Type::RefUnique { .. }
            )
        });
        if !tracked {
            return true;
        }
        match &symbols[argument.register as usize] {
            ArraySummarySymbol::Parameter {
                parameter: source,
                path,
            } if *source == parameter as u32 && path.is_empty() => true,
            ArraySummarySymbol::Unknown
            | ArraySummarySymbol::Constant(_)
            | ArraySummarySymbol::Parameter { .. }
            | ArraySummarySymbol::Fresh(_)
            | ArraySummarySymbol::Callable(_) => false,
        }
    })
}

fn infer_array_call_summary(
    function: &Function,
    types: &[Type],
    known: &BTreeMap<u32, ArrayCallSummary>,
    recursive_group: &BTreeSet<u32>,
) -> Option<ArrayCallSummary> {
    if function.receiver_mode.is_some() {
        return None;
    }
    let blocks = function
        .blocks
        .iter()
        .map(|block| (block.id, block))
        .collect::<BTreeMap<_, _>>();
    let mut symbols = vec![ArraySummarySymbol::Unknown; function.register_types.len()];
    for parameter in 0..function.params.len() {
        let register = parameter + 1;
        if register < symbols.len() {
            symbols[register] = ArraySummarySymbol::Parameter {
                parameter: parameter as u32,
                path: Vec::new(),
            };
        }
    }
    let mut effects = Vec::new();
    let consumes_owned_array = function
        .params
        .iter()
        .any(|ty| matches!(types[*ty as usize].representation(), Type::Array { .. }));
    let mut block_id = function.entry;
    let mut visited = BTreeSet::new();
    loop {
        if !visited.insert(block_id) {
            return None;
        }
        let block = *blocks.get(&block_id)?;
        for statement in &block.statements {
            match &statement.kind {
                InstructionKind::Const { dst, value } => {
                    symbols[*dst as usize] = constant_u64(value)
                        .map(ArraySummarySymbol::Constant)
                        .unwrap_or(ArraySummarySymbol::Unknown);
                }
                InstructionKind::Copy { dst, src } | InstructionKind::Move { dst, src } => {
                    symbols[*dst as usize] = symbols[src.register as usize].clone();
                }
                InstructionKind::Borrow { dst, src, .. }
                | InstructionKind::Reborrow { dst, src, .. } => {
                    symbols[*dst as usize] = symbols[*src as usize].clone();
                }
                InstructionKind::Primitive {
                    dst,
                    primitive,
                    args,
                } => {
                    use grandiose_vm::Primitive;
                    let effect = match primitive {
                        Primitive::ArrayGetCopy
                        | Primitive::ArrayGetBorrowShared
                        | Primitive::ArrayGetBorrowUnique => {
                            Some((ArrayEffectKind::Observe, args.get(1)))
                        }
                        Primitive::ArrayLen
                        | Primitive::ArrayCapacity
                        | Primitive::ArrayReserve => Some((ArrayEffectKind::Observe, None)),
                        Primitive::ArrayGetMove => Some((ArrayEffectKind::MoveOut, args.get(1))),
                        Primitive::ArraySetMove => Some((ArrayEffectKind::Restore, args.get(1))),
                        Primitive::ArrayPushMove => Some((ArrayEffectKind::Push, None)),
                        Primitive::ArrayPopMove => Some((ArrayEffectKind::Pop, None)),
                        Primitive::ArrayFinishDrained => Some((ArrayEffectKind::Finish, None)),
                        Primitive::BytesFromArrayMove => Some((ArrayEffectKind::Dense, None)),
                        _ => None,
                    };
                    if let Some((kind, index)) = effect {
                        let owner = args.first()?;
                        let ArraySummarySymbol::Parameter {
                            parameter: owner_parameter,
                            path: owner_path,
                        } = &symbols[owner.register as usize]
                        else {
                            // Projected, aliased, or locally synthesized owners
                            // deliberately do not acquire a transport summary.
                            return None;
                        };
                        if !owner_path.is_empty() {
                            return None;
                        }
                        let value = match primitive {
                            Primitive::ArraySetMove => args.get(2),
                            Primitive::ArrayPushMove => args.get(1),
                            _ => None,
                        };
                        let value_parameter = match value {
                            Some(value) => match &symbols[value.register as usize] {
                                ArraySummarySymbol::Parameter { parameter, path }
                                    if (path.is_empty()
                                        && matches!(
                                            types[function.params[*parameter as usize] as usize]
                                                .representation(),
                                            Type::RefShared { .. } | Type::RefUnique { .. }
                                        ))
                                        || (!path.is_empty()
                                            && matches!(
                                                types[function.register_types
                                                    [value.register as usize]
                                                    as usize]
                                                    .representation(),
                                                Type::RefShared { .. } | Type::RefUnique { .. }
                                            )) =>
                                {
                                    Some((*parameter, path.clone()))
                                }
                                _ if matches!(
                                    types
                                        [function.register_types[value.register as usize] as usize]
                                        .representation(),
                                    Type::RefShared { .. } | Type::RefUnique { .. }
                                ) =>
                                {
                                    return None;
                                }
                                _ => None,
                            },
                            None => None,
                        };
                        effects.push(ArrayCallEffect {
                            owner_parameter: *owner_parameter,
                            kind,
                            index: index
                                .map(|index| summary_index_of(&symbols[index.register as usize])),
                            value_parameter: value_parameter
                                .as_ref()
                                .map(|(parameter, _)| *parameter),
                            value_path: value_parameter.map(|(_, path)| path).unwrap_or_default(),
                        });
                    }
                    symbols[*dst as usize] = match primitive {
                        Primitive::ArrayEmpty => {
                            ArraySummarySymbol::Fresh(ArrayResultSummary::Empty)
                        }
                        Primitive::ArrayNew => {
                            ArraySummarySymbol::Fresh(ArrayResultSummary::Filled(
                                args.first()
                                    .map(|operand| {
                                        summary_index_of(&symbols[operand.register as usize])
                                    })
                                    .unwrap_or(ArrayIndexSummary::Dynamic),
                            ))
                        }
                        Primitive::BytesToArray => ArraySummarySymbol::Fresh(
                            ArrayResultSummary::Filled(ArrayIndexSummary::Dynamic),
                        ),
                        _ => ArraySummarySymbol::Unknown,
                    };
                }
                InstructionKind::ProjectBorrow {
                    dst, src, field, ..
                } => {
                    symbols[*dst as usize] = match &symbols[*src as usize] {
                        ArraySummarySymbol::Parameter { parameter, path } => {
                            let mut path = path.clone();
                            path.push(*field);
                            ArraySummarySymbol::Parameter {
                                parameter: *parameter,
                                path,
                            }
                        }
                        _ => ArraySummarySymbol::Unknown,
                    };
                }
                InstructionKind::ProjectCopy { dst, src, field }
                | InstructionKind::ProjectMove { dst, src, field } => {
                    symbols[*dst as usize] = match &symbols[src.register as usize] {
                        ArraySummarySymbol::Parameter { parameter, path } => {
                            let mut path = path.clone();
                            path.push(*field);
                            ArraySummarySymbol::Parameter {
                                parameter: *parameter,
                                path,
                            }
                        }
                        _ => ArraySummarySymbol::Unknown,
                    };
                }
                InstructionKind::DerefCopy { dst, .. }
                | InstructionKind::DerefMove { dst, .. }
                | InstructionKind::Construct { dst, .. }
                | InstructionKind::MakeBindingPack { dst, .. }
                | InstructionKind::EnumTag { dst, .. }
                | InstructionKind::MakeHandler { dst, .. }
                | InstructionKind::MakeHandlerShared { dst, .. } => {
                    symbols[*dst as usize] = ArraySummarySymbol::Unknown;
                }
                InstructionKind::MakeCallable { dst, function, .. } => {
                    symbols[*dst as usize] = ArraySummarySymbol::Callable(*function);
                }
                InstructionKind::DerefStore { .. }
                | InstructionKind::EndBorrow { .. }
                | InstructionKind::Deconstruct { .. }
                | InstructionKind::LabelPush { .. }
                | InstructionKind::LabelPop { .. }
                | InstructionKind::Drop { .. } => {}
            }
        }
        match &block.terminator {
            Terminator::Goto(edge) => {
                let target = *blocks.get(&edge.target)?;
                for (argument, parameter) in edge.args.iter().zip(&target.params) {
                    symbols[parameter.register as usize] =
                        symbols[argument.register as usize].clone();
                }
                block_id = edge.target;
            }
            Terminator::Switch {
                cases, otherwise, ..
            } => {
                let continuing = cases
                    .iter()
                    .map(|(_, edge)| edge)
                    .chain(std::iter::once(otherwise))
                    .filter(|edge| {
                        !summary_edge_statically_diverges(&blocks, edge, &mut BTreeSet::new())
                            && !summary_edge_is_effectless_recursive_forwarder(
                                &blocks,
                                edge,
                                function,
                                recursive_group,
                                types,
                                &symbols,
                            )
                    })
                    .collect::<Vec<_>>();
                let edge = if let Some(first) = continuing.first()
                    && continuing.iter().all(|edge| *edge == *first)
                {
                    *first
                } else if let Some(first) = continuing.first()
                    && continuing.iter().all(|edge| {
                        let Some(first_block) = blocks.get(&first.target) else {
                            return false;
                        };
                        let Some(candidate) = blocks.get(&edge.target) else {
                            return false;
                        };
                        first_block
                            .statements
                            .iter()
                            .map(|statement| &statement.kind)
                            .eq(candidate.statements.iter().map(|statement| &statement.kind))
                            && first_block.terminator == candidate.terminator
                    })
                {
                    *first
                } else {
                    return None;
                };
                let target = *blocks.get(&edge.target)?;
                for (argument, parameter) in edge.args.iter().zip(&target.params) {
                    symbols[parameter.register as usize] =
                        symbols[argument.register as usize].clone();
                }
                block_id = edge.target;
            }
            Terminator::Call {
                result,
                function: callee,
                args,
                normal,
            } => {
                let symbolic_array_argument = args.iter().any(|argument| {
                    let ty = function.register_types[argument.register as usize];
                    let is_array = match types[ty as usize].representation() {
                        Type::Array { .. } => true,
                        Type::RefShared { referent } | Type::RefUnique { referent } => matches!(
                            types[*referent as usize].representation(),
                            Type::Array { .. }
                        ),
                        _ => false,
                    };
                    is_array
                        && matches!(
                            symbols[argument.register as usize],
                            ArraySummarySymbol::Parameter { .. } | ArraySummarySymbol::Fresh(_)
                        )
                });
                let callee = known.get(callee);
                if symbolic_array_argument && callee.is_none() {
                    return None;
                }
                let mut result_symbol = ArraySummarySymbol::Unknown;
                if let Some(callee) = callee {
                    for effect in &callee.effects {
                        let owner = args.get(effect.owner_parameter as usize)?;
                        let ArraySummarySymbol::Parameter {
                            parameter: owner_parameter,
                            path: owner_path,
                        } = &symbols[owner.register as usize]
                        else {
                            return None;
                        };
                        if !owner_path.is_empty() {
                            return None;
                        }
                        let value_source = effect.value_parameter.and_then(|parameter| {
                            let value = args.get(parameter as usize)?;
                            match &symbols[value.register as usize] {
                                ArraySummarySymbol::Parameter { parameter, path } => {
                                    Some((*parameter, path.clone()))
                                }
                                _ => None,
                            }
                        });
                        if effect.value_parameter.is_some() && value_source.is_none() {
                            return None;
                        }
                        let mut value_path = value_source
                            .as_ref()
                            .map(|(_, path)| path.clone())
                            .unwrap_or_default();
                        value_path.extend(&effect.value_path);
                        effects.push(ArrayCallEffect {
                            owner_parameter: *owner_parameter,
                            kind: effect.kind,
                            index: effect
                                .index
                                .as_ref()
                                .map(|index| translate_index(index, args, &symbols)),
                            value_parameter: value_source.map(|(parameter, _)| parameter),
                            value_path,
                        });
                    }
                    result_symbol = match callee.result.as_ref() {
                        Some(ArrayResultSummary::Empty) => {
                            ArraySummarySymbol::Fresh(ArrayResultSummary::Empty)
                        }
                        Some(ArrayResultSummary::Filled(length)) => ArraySummarySymbol::Fresh(
                            ArrayResultSummary::Filled(translate_index(length, args, &symbols)),
                        ),
                        Some(ArrayResultSummary::Parameter(parameter)) => args
                            .get(*parameter as usize)
                            .map(|operand| symbols[operand.register as usize].clone())
                            .unwrap_or(ArraySummarySymbol::Unknown),
                        None => ArraySummarySymbol::Unknown,
                    };
                }
                if let Some(result) = result {
                    symbols[*result as usize] = result_symbol;
                }
                block_id = normal.target;
            }
            Terminator::CallIndirect {
                result,
                callable,
                known_function,
                args,
                normal,
                ..
            } => {
                let target =
                    (*known_function).or_else(|| match symbols[callable.register as usize] {
                        ArraySummarySymbol::Callable(function) => Some(function),
                        _ => None,
                    });
                let symbolic_array_argument = args.iter().any(|argument| {
                    let ty = function.register_types[argument.register as usize];
                    let is_array = match types[ty as usize].representation() {
                        Type::Array { .. } => true,
                        Type::RefShared { referent } | Type::RefUnique { referent } => matches!(
                            types[*referent as usize].representation(),
                            Type::Array { .. }
                        ),
                        _ => false,
                    };
                    is_array
                        && matches!(
                            symbols[argument.register as usize],
                            ArraySummarySymbol::Parameter { .. } | ArraySummarySymbol::Fresh(_)
                        )
                });
                let callee = target.and_then(|target| known.get(&target));
                if symbolic_array_argument && callee.is_none() {
                    return None;
                }
                let result_symbol = callee
                    .and_then(|callee| {
                        compose_array_call_summary(callee, args, &symbols, &mut effects)
                    })
                    .unwrap_or(ArraySummarySymbol::Unknown);
                if let Some(result) = result {
                    symbols[*result as usize] = result_symbol;
                }
                block_id = normal.target;
            }
            Terminator::Return { value } => {
                let result = if matches!(
                    types[function.result as usize].representation(),
                    Type::Array { .. }
                ) {
                    value
                        .as_ref()
                        .and_then(|value| match &symbols[value.register as usize] {
                            ArraySummarySymbol::Fresh(result) => Some(result.clone()),
                            ArraySummarySymbol::Parameter { parameter, path }
                                if path.is_empty() =>
                            {
                                Some(ArrayResultSummary::Parameter(*parameter))
                            }
                            ArraySummarySymbol::Unknown
                            | ArraySummarySymbol::Parameter { .. }
                            | ArraySummarySymbol::Constant(_)
                            | ArraySummarySymbol::Callable(_) => None,
                        })
                } else {
                    None
                };
                return (!effects.is_empty() || result.is_some() || consumes_owned_array)
                    .then_some(ArrayCallSummary { effects, result });
            }
            Terminator::TailCall {
                function: callee,
                args,
            } => {
                let callee = known.get(callee)?;
                for effect in &callee.effects {
                    let owner = args.get(effect.owner_parameter as usize)?;
                    let ArraySummarySymbol::Parameter {
                        parameter: owner_parameter,
                        path: owner_path,
                    } = &symbols[owner.register as usize]
                    else {
                        return None;
                    };
                    if !owner_path.is_empty() {
                        return None;
                    }
                    let value_source = effect.value_parameter.and_then(|parameter| {
                        let value = args.get(parameter as usize)?;
                        match &symbols[value.register as usize] {
                            ArraySummarySymbol::Parameter { parameter, path } => {
                                Some((*parameter, path.clone()))
                            }
                            _ => None,
                        }
                    });
                    if effect.value_parameter.is_some() && value_source.is_none() {
                        return None;
                    }
                    let mut value_path = value_source
                        .as_ref()
                        .map(|(_, path)| path.clone())
                        .unwrap_or_default();
                    value_path.extend(&effect.value_path);
                    effects.push(ArrayCallEffect {
                        owner_parameter: *owner_parameter,
                        kind: effect.kind,
                        index: effect
                            .index
                            .as_ref()
                            .map(|index| translate_index(index, args, &symbols)),
                        value_parameter: value_source.map(|(parameter, _)| parameter),
                        value_path,
                    });
                }
                let result = match callee.result.as_ref() {
                    Some(ArrayResultSummary::Empty) => Some(ArrayResultSummary::Empty),
                    Some(ArrayResultSummary::Filled(length)) => Some(ArrayResultSummary::Filled(
                        translate_index(length, args, &symbols),
                    )),
                    Some(ArrayResultSummary::Parameter(parameter)) => {
                        let argument = args.get(*parameter as usize)?;
                        match &symbols[argument.register as usize] {
                            ArraySummarySymbol::Parameter { parameter, path }
                                if path.is_empty() =>
                            {
                                Some(ArrayResultSummary::Parameter(*parameter))
                            }
                            ArraySummarySymbol::Fresh(result) => Some(result.clone()),
                            ArraySummarySymbol::Unknown
                            | ArraySummarySymbol::Parameter { .. }
                            | ArraySummarySymbol::Constant(_)
                            | ArraySummarySymbol::Callable(_) => None,
                        }
                    }
                    None => None,
                };
                return (!effects.is_empty() || result.is_some())
                    .then_some(ArrayCallSummary { effects, result });
            }
            _ => return None,
        }
    }
}

fn bounded_recursive_groups(program: &crate::compiler_mir::Program) -> Vec<BTreeSet<u32>> {
    fn postorder(
        graph: &BTreeMap<u32, BTreeSet<u32>>,
        node: u32,
        visited: &mut BTreeSet<u32>,
        order: &mut Vec<u32>,
    ) {
        if !visited.insert(node) {
            return;
        }
        for &successor in &graph[&node] {
            postorder(graph, successor, visited, order);
        }
        order.push(node);
    }

    fn collect_component(
        reverse: &BTreeMap<u32, BTreeSet<u32>>,
        node: u32,
        visited: &mut BTreeSet<u32>,
        component: &mut BTreeSet<u32>,
    ) {
        if !visited.insert(node) {
            return;
        }
        component.insert(node);
        for &predecessor in &reverse[&node] {
            collect_component(reverse, predecessor, visited, component);
        }
    }

    let declarations = program
        .functions
        .iter()
        .map(|function| function.declaration)
        .collect::<BTreeSet<_>>();
    let graph = program
        .functions
        .iter()
        .map(|function| {
            let edges = function
                .blocks
                .iter()
                .filter(|block| block.statements.is_empty())
                .filter_map(|block| match block.terminator {
                    Terminator::TailCallSelf { .. } => Some(function.declaration),
                    Terminator::TailCall { function, .. } if declarations.contains(&function) => {
                        Some(function)
                    }
                    _ => None,
                })
                .collect();
            (function.declaration, edges)
        })
        .collect::<BTreeMap<_, BTreeSet<_>>>();
    let mut reverse = declarations
        .iter()
        .map(|declaration| (*declaration, BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    for (&source, targets) in &graph {
        for target in targets {
            reverse
                .get_mut(target)
                .expect("known call target")
                .insert(source);
        }
    }
    let mut visited = BTreeSet::new();
    let mut order = Vec::with_capacity(declarations.len());
    for &declaration in &declarations {
        postorder(&graph, declaration, &mut visited, &mut order);
    }
    visited.clear();
    let mut groups = Vec::new();
    for declaration in order.into_iter().rev() {
        if visited.contains(&declaration) {
            continue;
        }
        let mut group = BTreeSet::new();
        collect_component(&reverse, declaration, &mut visited, &mut group);
        let cyclic = group.len() > 1
            || graph
                .get(&declaration)
                .is_some_and(|edges| edges.contains(&declaration));
        if cyclic {
            groups.push(group);
        }
    }
    groups
}

/// Infer a least fixed point of exact bounded array effects through direct
/// calls. A recursive SCC participates only when every member has the same
/// finite normal-path summary and every recursive edge forwards tracked array
/// and reference parameters unchanged. Repeated or path-dependent recursive
/// writes, opaque calls, and ambiguous control-flow joins remain absent.
pub(crate) fn array_call_summaries(
    program: &crate::compiler_mir::Program,
    types: &[Type],
) -> BTreeMap<u32, ArrayCallSummary> {
    let mut summaries = BTreeMap::new();
    let recursive_groups = bounded_recursive_groups(program);
    for _ in 0..=program.functions.len() * 2 {
        let mut changed = false;
        for function in &program.functions {
            if summaries.contains_key(&function.declaration) {
                continue;
            }
            if let Some(summary) =
                infer_array_call_summary(function, types, &summaries, &BTreeSet::new())
            {
                summaries.insert(function.declaration, summary);
                changed = true;
            }
        }
        for group in &recursive_groups {
            if group
                .iter()
                .any(|declaration| summaries.contains_key(declaration))
            {
                continue;
            }
            let candidates = group
                .iter()
                .map(|declaration| {
                    let function = program
                        .functions
                        .iter()
                        .find(|function| function.declaration == *declaration)?;
                    infer_array_call_summary(function, types, &summaries, group)
                        .map(|summary| (*declaration, summary))
                })
                .collect::<Option<Vec<_>>>();
            let Some(candidates) = candidates else {
                continue;
            };
            let Some((_, expected)) = candidates.first() else {
                continue;
            };
            if candidates.iter().all(|(_, summary)| summary == expected) {
                summaries.extend(candidates);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    summaries
}

/// Everything the ownership engine needs to interpret one body.
pub(crate) struct FlowContext<'a> {
    pub(crate) function: &'a Function,
    pub(crate) types: &'a [Type],
    /// Bridged local facts, one per register.
    pub(crate) locals: &'a [LocalFact],
    /// Stable loan identities.
    pub(crate) loans: LoanTable,
    /// Direct-call array summaries, keyed by MIR declaration identity.
    pub(crate) array_calls: &'a BTreeMap<u32, ArrayCallSummary>,
    /// Strict mode enforces exported-fact obligations (definition discipline,
    /// duplicability, quantitative bounds, and exit cleanup completeness).
    /// Lenient mode is the documented bridge for hand-assembled MIR without
    /// exported facts: it still derives deterministic cleanup lists but only
    /// enforces structural loan discipline.
    pub(crate) strict: bool,
    /// Semantic validation may prune impossible refined enum-switch arms.
    /// Final bytecode cleanup serialization disables that pruning because the
    /// verifier structurally visits every encoded target, including the
    /// `Unreachable` arm of a proven tag switch.
    pub(crate) refine_enum_switches: bool,
}

/// The engine result: per-block entry states and per-point cleanup lists.
#[derive(Debug)]
pub(crate) struct FlowSolution {
    pub(crate) entries: BTreeMap<u32, OwnState>,
    /// Per block, one cleanup list per statement plus one for the terminator.
    pub(crate) cleanup_lists: BTreeMap<u32, Vec<Vec<Register>>>,
}

impl<'a> FlowContext<'a> {
    fn representation(&self, ty: TypeId) -> &Type {
        self.types[ty as usize].representation()
    }

    fn is_reference(&self, ty: TypeId) -> bool {
        matches!(
            self.representation(ty),
            Type::RefShared { .. } | Type::RefUnique { .. }
        )
    }

    fn is_unique_reference(&self, ty: TypeId) -> bool {
        matches!(self.representation(ty), Type::RefUnique { .. })
    }

    fn aggregate_fields(&self, ty: TypeId, variant: Option<u32>) -> Option<Vec<TypeId>> {
        let mut projected = ty;
        for _ in 0..=self.types.len() {
            projected = match self.representation(projected) {
                // MIR receiver projection addresses the capture environment,
                // although r0 itself retains its nominal callable/handler
                // type. References similarly project their referent.
                Type::RefShared { referent } | Type::RefUnique { referent } => *referent,
                Type::Callable { capture_type, .. } | Type::Handler { capture_type, .. } => {
                    *capture_type
                }
                Type::BindingPack { payload_type, .. } => *payload_type,
                _ => break,
            };
        }
        let fields = match (self.representation(projected), variant) {
            (Type::Tuple { fields, .. }, None) => Some(fields.clone()),
            (Type::Struct { fields, .. }, None) => {
                Some(fields.iter().map(|field| field.ty).collect())
            }
            (Type::Enum { variants, .. }, Some(variant)) => variants
                .get(variant as usize)
                .map(|variant| variant.fields.iter().map(|field| field.ty).collect()),
            _ => None,
        }?;
        Some(
            fields
                .into_iter()
                .filter(|field| !matches!(self.representation(*field), Type::Available { .. }))
                .collect(),
        )
    }

    fn enum_variant_count(&self, ty: TypeId) -> Option<u32> {
        let ty = match self.representation(ty) {
            Type::RefShared { referent } | Type::RefUnique { referent } => *referent,
            _ => ty,
        };
        match self.representation(ty) {
            Type::Enum { variants, .. } => u32::try_from(variants.len()).ok(),
            _ => None,
        }
    }

    fn quantity_leaf_count(&self, ty: TypeId) -> usize {
        fn collect(types: &[Type], ty: TypeId, visiting: &mut [bool]) -> usize {
            let Some(descriptor) = types.get(ty as usize) else {
                return 0;
            };
            if visiting[ty as usize] {
                return 0;
            }
            visiting[ty as usize] = true;
            let count = match descriptor.representation() {
                Type::Resumption { .. } => 1,
                Type::Tuple { fields, .. } => fields
                    .iter()
                    .map(|field| collect(types, *field, visiting))
                    .sum(),
                Type::Struct { fields, .. } => fields
                    .iter()
                    .map(|field| collect(types, field.ty, visiting))
                    .sum(),
                Type::Callable { capture_type, .. } | Type::Handler { capture_type, .. } => {
                    collect(types, *capture_type, visiting)
                }
                Type::Enum { variants, .. } => variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .map(|field| collect(types, field.ty, visiting))
                    .sum(),
                _ => 0,
            };
            visiting[ty as usize] = false;
            count
        }
        collect(self.types, ty, &mut vec![false; self.types.len()])
    }

    /// Build the exact caller-owned origins of every reference leaf carried
    /// by an aggregate ABI value.  Unlike the opaque direct-reference loan,
    /// these origins are rooted at the aggregate parameter and retain their
    /// nominal field path, so two independently lowered projections of the
    /// same parameter leaf remain identical at CFG joins.
    fn external_aggregate_reference_origins(
        &self,
        register: Register,
        ty: TypeId,
    ) -> BTreeMap<Vec<u32>, StoredReferenceOrigin> {
        fn collect(
            types: &[Type],
            ty: TypeId,
            register: Register,
            path: &mut Vec<u32>,
            visiting: &mut [bool],
            origins: &mut BTreeMap<Vec<u32>, StoredReferenceOrigin>,
        ) {
            let Some(descriptor) = types.get(ty as usize) else {
                return;
            };
            match descriptor.representation() {
                Type::RefShared { .. } | Type::RefUnique { .. } => {
                    let borrowed = Place {
                        base: register,
                        projection: path
                            .iter()
                            .map(|field| Projection::Field {
                                variant: None,
                                field: *field,
                            })
                            .collect(),
                    };
                    origins.insert(
                        path.clone(),
                        StoredReferenceOrigin {
                            unique: matches!(descriptor.representation(), Type::RefUnique { .. }),
                            external: true,
                            borrowed,
                            parent: None,
                        },
                    );
                    return;
                }
                _ => {}
            }
            if visiting.get(ty as usize).copied().unwrap_or(true) {
                return;
            }
            visiting[ty as usize] = true;
            let fields = match descriptor.representation() {
                Type::Tuple { fields, .. } => Some(fields.clone()),
                Type::Struct { fields, .. } => Some(fields.iter().map(|field| field.ty).collect()),
                Type::Callable { capture_type, .. } | Type::Handler { capture_type, .. } => {
                    match types.get(*capture_type as usize) {
                        Some(capture) => match capture.representation() {
                            Type::Tuple { fields, .. } => Some(fields.clone()),
                            Type::Struct { fields, .. } => {
                                Some(fields.iter().map(|field| field.ty).collect())
                            }
                            _ => None,
                        },
                        None => None,
                    }
                }
                Type::BindingPack { payload_type, .. } => match types.get(*payload_type as usize) {
                    Some(payload) => match payload.representation() {
                        Type::Tuple { fields, .. } => Some(fields.clone()),
                        Type::Struct { fields, .. } => {
                            Some(fields.iter().map(|field| field.ty).collect())
                        }
                        _ => None,
                    },
                    None => None,
                },
                // An enum parameter has no entry variant proof, so a numeric
                // payload field is not yet a stable nominal path.
                _ => None,
            };
            if let Some(fields) = fields {
                for (field, field_ty) in fields.into_iter().enumerate() {
                    path.push(field as u32);
                    collect(types, field_ty, register, path, visiting, origins);
                    path.pop();
                }
            }
            visiting[ty as usize] = false;
        }

        let mut origins = BTreeMap::new();
        collect(
            self.types,
            ty,
            register,
            &mut Vec::new(),
            &mut vec![false; self.types.len()],
            &mut origins,
        );
        origins
    }

    fn register_type(&self, register: Register) -> TypeId {
        self.function.register_types[register as usize]
    }

    fn admits_zero_use(&self, register: Register) -> bool {
        let fact = &self.locals[register as usize];
        fact.use_interval.admits_zero_use()
            || self.types[fact.ty as usize].claimed_zero_use_allowed()
    }

    fn type_admits_zero_use(&self, ty: TypeId) -> bool {
        let descriptor = &self.types[ty as usize];
        // `Available` is the runtime placeholder for a source type already
        // proven exactly-zero and erased from aggregate storage. It carries
        // no runtime zero-use flag because there is no value to destroy, but
        // ownership cleanup must retain the frontend proof.
        descriptor.claimed_zero_use_allowed()
            || matches!(descriptor.representation(), Type::Available { .. })
    }

    fn has_drop_flag(&self, register: Register) -> bool {
        self.function
            .flow
            .drop_flags
            .iter()
            .any(|fact| fact.owner == register && fact.field.is_none())
    }

    fn has_field_drop_flag(&self, register: Register, field: u32) -> bool {
        self.function
            .flow
            .drop_flags
            .iter()
            .any(|fact| fact.owner == register && fact.field == Some(field))
    }

    fn entry_state(&self) -> OwnState {
        let count = self.function.register_types.len();
        let mut state = OwnState {
            regs: vec![RegState::Undefined; count],
            conditional_fields: BTreeMap::new(),
            array_slots: BTreeMap::new(),
            aggregate_reference_origins: BTreeMap::new(),
            constants: vec![None; count],
            active_variants: vec![None; count],
            enum_tag_sources: vec![None; count],
            order: Vec::new(),
            shell_ages: vec![None; count],
            loans: BTreeMap::new(),
            holes: BTreeSet::new(),
            uses: vec![UseCount::ZERO; count],
            quantity_groups: vec![None; count],
            quantity_uses: vec![UseCount::ZERO; count],
            labels: Vec::new(),
        };
        let mark_live = |context: &Self, state: &mut OwnState, register: Register| {
            state.regs[register as usize] = RegState::Live;
            state.order.push(register);
            let ty = context.register_type(register);
            if context.quantity_leaf_count(ty) == 1 {
                state.quantity_groups[register as usize] = Some(register);
            }
            if matches!(context.representation(ty), Type::Array { .. }) {
                state.array_slots.insert(
                    register,
                    ArraySlotState {
                        length: None,
                        empty: BTreeSet::new(),
                        dynamic_hole: false,
                        reference_origins: BTreeMap::new(),
                    },
                );
            }
            if context.is_reference(ty) {
                state.loans.insert(
                    register,
                    LiveLoan {
                        id: context
                            .loans
                            .external
                            .get(&register)
                            .copied()
                            .unwrap_or(u32::MAX),
                        unique: context.is_unique_reference(ty),
                        external: true,
                        borrowed: Place::local(register),
                        parent: None,
                        suspended: 0,
                    },
                );
            } else if register != 0 || context.function.receiver_mode.is_none() {
                // Receiver capture environments are initialized and consumed
                // by callable-specific lowering.  Their field origins are
                // established by MakeCallable/Construct; treating r0 as an
                // ordinary caller aggregate would retain leaves that a
                // capture projection has legitimately moved out.
                let origins = context.external_aggregate_reference_origins(register, ty);
                if !origins.is_empty() {
                    state.aggregate_reference_origins.insert(register, origins);
                }
            }
        };
        if self.strict {
            // The receiver/parameter ABI prefix is initialized by contract;
            // exported facts drive the rest. The ABI rule keeps optimizer-
            // cloned bodies (scalarized callables, handler clauses) correct
            // even when their exported prefix predates the reshaping.
            if self.function.receiver_mode.is_some() {
                mark_live(self, &mut state, 0);
            }
            for register in 1..=self.function.params.len() as Register {
                mark_live(self, &mut state, register);
            }
            for (register, fact) in self.locals.iter().enumerate() {
                if fact.initial == InitAtEntry::Initialized && !state.regs[register].is_live() {
                    mark_live(self, &mut state, register as Register);
                }
            }
        } else {
            // Bridge mode relaxes definition diagnostics for hand-assembled
            // MIR, but it must still honor the bytecode entry ABI. Only a
            // receiver, explicit parameters, and locals explicitly declared
            // initialized can contain values at PC 0. Treating every scratch
            // register as live made MIR-derived cleanup metadata disagree
            // with the verifier before the first instruction.
            if self.function.receiver_mode.is_some() {
                mark_live(self, &mut state, 0);
            }
            for register in 1..=self.function.params.len() as Register {
                mark_live(self, &mut state, register);
            }
            for (register, fact) in self.locals.iter().enumerate() {
                if fact.initial == InitAtEntry::Initialized && !state.regs[register].is_live() {
                    mark_live(self, &mut state, register as Register);
                }
            }
        }
        state
    }
}

struct Interpreter<'a> {
    context: &'a FlowContext<'a>,
    block: u32,
    statement: usize,
    state: OwnState,
}

impl Interpreter<'_> {
    fn projected_aggregate_reference_origins(
        &self,
        source: Register,
        field: u32,
    ) -> BTreeMap<Vec<u32>, StoredReferenceOrigin> {
        let prefix = self.state.active_variants[source as usize]
            .map_or_else(|| vec![field], |variant| vec![u32::MAX - variant, field]);
        self.state
            .aggregate_reference_origins
            .get(&source)
            .into_iter()
            .flat_map(|origins| origins.iter())
            .filter(|(path, _)| path.starts_with(&prefix))
            .map(|(path, origin)| (path[prefix.len()..].to_vec(), origin.clone()))
            .collect()
    }

    fn install_projected_reference_origins(
        &mut self,
        destination: Register,
        origins: BTreeMap<Vec<u32>, StoredReferenceOrigin>,
    ) {
        if self
            .context
            .is_reference(self.context.register_type(destination))
        {
            if let Some(origin) = origins.get(&[] as &[u32]) {
                self.state.loans.insert(
                    destination,
                    LiveLoan {
                        id: u32::MAX,
                        unique: origin.unique,
                        external: origin.external,
                        borrowed: origin.borrowed.clone(),
                        parent: None,
                        suspended: 0,
                    },
                );
            }
        } else if !origins.is_empty() {
            self.state
                .aggregate_reference_origins
                .insert(destination, origins);
        }
    }

    fn stored_reference_origin(
        &self,
        operand: Option<&Operand>,
        value_path: &[u32],
        action: &str,
    ) -> Result<Option<StoredReferenceOrigin>, FlowError> {
        let Some(operand) = operand else {
            return Ok(None);
        };
        if !value_path.is_empty() {
            return self
                .state
                .aggregate_reference_origins
                .get(&operand.register)
                .and_then(|origins| origins.get(value_path))
                .cloned()
                .map(Some)
                .ok_or_else(|| {
                    self.error(format!(
                        "{action} cannot identify aggregate reference origin path {value_path:?} in r{}",
                        operand.register
                    ))
                });
        }
        if !self
            .context
            .is_reference(self.context.register_type(operand.register))
        {
            return Ok(None);
        }
        let loan = self.state.loans.get(&operand.register).ok_or_else(|| {
            self.error(format!(
                "{action} cannot identify the origin of reference r{}",
                operand.register
            ))
        })?;
        Ok(Some(StoredReferenceOrigin {
            unique: loan.unique,
            external: loan.external,
            borrowed: loan.borrowed.clone(),
            parent: loan.parent,
        }))
    }

    fn array_owner(
        &self,
        reference: Register,
        action: &str,
    ) -> Result<Option<Register>, FlowError> {
        let loan = self.state.loans.get(&reference).ok_or_else(|| {
            self.error(format!(
                "{action} requires an array reference with a tracked owner in r{reference}"
            ))
        })?;
        if loan.external {
            // Trusted primitive wrappers receive caller-owned arrays through
            // an external reference. Their caller retains the slot summary;
            // this body cannot name that owner and therefore performs no
            // local update.
            return Ok(None);
        }
        if !loan.borrowed.projection.is_empty() {
            if !matches!(
                self.context
                    .representation(self.context.register_type(loan.borrowed.base)),
                Type::Array { .. }
            ) {
                // The array lives inside an aggregate whose private invariant
                // is validated in the callee that owns the projection. There
                // is no direct local array-shell state to update here.
                return Ok(None);
            }
            return Err(self.error(format!(
                "{action} requires a direct local array owner; aliased or projected arrays use a conservative dynamic summary"
            )));
        }
        Ok(Some(loan.borrowed.base))
    }

    fn array_primitive(
        &mut self,
        primitive: grandiose_vm::Primitive,
        args: &[Operand],
    ) -> Result<Option<ArraySlotState>, FlowError> {
        use grandiose_vm::Primitive;

        let exact = |state: &OwnState, register: Register| state.constants[register as usize];
        let index = || {
            args.get(1)
                .and_then(|operand| exact(&self.state, operand.register))
        };
        let owner_for_reference = |this: &Self, action: &str| {
            args.first()
                .ok_or_else(|| this.error(format!("{action} lacks its array operand")))
                .and_then(|operand| this.array_owner(operand.register, action))
        };
        let check_bounds = |this: &Self,
                            action: &str,
                            slots: &ArraySlotState,
                            index: u64|
         -> Result<(), FlowError> {
            if slots.length.is_some_and(|length| index >= length) {
                return Err(this.error(format!(
                    "{action} uses out-of-bounds array index {index} for length {}",
                    slots.length.unwrap()
                )));
            }
            Ok(())
        };

        match primitive {
            Primitive::ArrayEmpty => Ok(Some(ArraySlotState {
                length: Some(0),
                empty: BTreeSet::new(),
                dynamic_hole: false,
                reference_origins: BTreeMap::new(),
            })),
            Primitive::ArrayNew => Ok(Some(ArraySlotState {
                length: args
                    .first()
                    .and_then(|operand| exact(&self.state, operand.register)),
                empty: BTreeSet::new(),
                dynamic_hole: false,
                reference_origins: BTreeMap::new(),
            })),
            Primitive::ArrayGetMove => {
                let Some(owner) = owner_for_reference(self, "ArrayGetMove")? else {
                    return Ok(None);
                };
                let mut slots =
                    self.state
                        .array_slots
                        .get(&owner)
                        .cloned()
                        .unwrap_or(ArraySlotState {
                            length: None,
                            empty: BTreeSet::new(),
                            dynamic_hole: false,
                            reference_origins: BTreeMap::new(),
                        });
                if slots.dynamic_hole {
                    return Err(self.error(
                        "ArrayGetMove cannot prove an element initialized after a dynamic-index move",
                    ));
                }
                if let Some(index) = index() {
                    check_bounds(self, "ArrayGetMove", &slots, index)?;
                    if !slots.empty.insert(index) {
                        return Err(self.error(format!(
                            "ArrayGetMove reads array index {index} after it was moved out"
                        )));
                    }
                    slots.reference_origins.remove(&index);
                } else {
                    if !slots.reference_origins.is_empty() {
                        return Err(self.error(
                            "dynamic ArrayGetMove cannot transport an exact stored reference origin",
                        ));
                    }
                    slots.dynamic_hole = true;
                }
                self.state.array_slots.insert(owner, slots);
                Ok(None)
            }
            Primitive::ArrayGetCopy
            | Primitive::ArrayGetBorrowShared
            | Primitive::ArrayGetBorrowUnique => {
                let Some(owner) = owner_for_reference(self, "array element read")? else {
                    return Ok(None);
                };
                let slots = self
                    .state
                    .array_slots
                    .get(&owner)
                    .cloned()
                    .unwrap_or(ArraySlotState {
                        length: None,
                        empty: BTreeSet::new(),
                        dynamic_hole: false,
                        reference_origins: BTreeMap::new(),
                    });
                if slots.dynamic_hole {
                    return Err(self.error(
                        "array element read cannot prove an element initialized after a dynamic-index move",
                    ));
                }
                if let Some(index) = index() {
                    check_bounds(self, "array element read", &slots, index)?;
                    if slots.empty.contains(&index) {
                        return Err(self.error(format!(
                            "array element read uses index {index} after it was moved out"
                        )));
                    }
                } else if !slots.empty.is_empty() {
                    return Err(self.error(
                        "dynamic array element read may alias an exact index that was moved out",
                    ));
                }
                Ok(None)
            }
            Primitive::ArraySetMove => {
                let origin =
                    self.stored_reference_origin(args.get(2), &[], "ArraySetMove reference write")?;
                let Some(owner) = owner_for_reference(self, "ArraySetMove")? else {
                    return Ok(None);
                };
                let mut slots =
                    self.state
                        .array_slots
                        .get(&owner)
                        .cloned()
                        .unwrap_or(ArraySlotState {
                            length: None,
                            empty: BTreeSet::new(),
                            dynamic_hole: false,
                            reference_origins: BTreeMap::new(),
                        });
                let Some(index) = index() else {
                    return Err(self.error(
                        "dynamic ArraySetMove cannot prove which moved-out slot it restores",
                    ));
                };
                check_bounds(self, "ArraySetMove", &slots, index)?;
                if !slots.empty.remove(&index) {
                    return Err(self.error(format!(
                        "ArraySetMove overwrites initialized array index {index}"
                    )));
                }
                if let Some(origin) = origin {
                    slots.reference_origins.insert(index, origin);
                }
                self.state.array_slots.insert(owner, slots);
                Ok(None)
            }
            Primitive::ArrayPushMove => {
                let origin = self.stored_reference_origin(
                    args.get(1),
                    &[],
                    "ArrayPushMove reference write",
                )?;
                let Some(owner) = owner_for_reference(self, "ArrayPushMove")? else {
                    return Ok(None);
                };
                let slots = self
                    .state
                    .array_slots
                    .entry(owner)
                    .or_insert(ArraySlotState {
                        length: None,
                        empty: BTreeSet::new(),
                        dynamic_hole: false,
                        reference_origins: BTreeMap::new(),
                    });
                let previous_length = slots.length;
                if let Some(origin) = origin {
                    let Some(index) = previous_length else {
                        return Err(self.error(
                            "ArrayPushMove cannot place a reference origin at an unknown array index",
                        ));
                    };
                    slots.reference_origins.insert(index, origin);
                }
                slots.length = previous_length.and_then(|length| length.checked_add(1));
                Ok(None)
            }
            Primitive::ArrayPopMove => {
                let Some(owner) = owner_for_reference(self, "ArrayPopMove")? else {
                    return Ok(None);
                };
                let mut slots =
                    self.state
                        .array_slots
                        .get(&owner)
                        .cloned()
                        .unwrap_or(ArraySlotState {
                            length: None,
                            empty: BTreeSet::new(),
                            dynamic_hole: false,
                            reference_origins: BTreeMap::new(),
                        });
                if slots.dynamic_hole {
                    return Err(self.error(
                        "ArrayPopMove cannot prove the final element initialized after a dynamic-index move",
                    ));
                }
                if let Some(length) = slots.length {
                    let Some(last) = length.checked_sub(1) else {
                        return Err(self.error("ArrayPopMove reads an empty array"));
                    };
                    if slots.empty.contains(&last) {
                        return Err(self
                            .error("ArrayPopMove reads the final element after it was moved out"));
                    }
                    slots.length = Some(last);
                    slots.empty.retain(|index| *index < last);
                    slots.reference_origins.remove(&last);
                }
                self.state.array_slots.insert(owner, slots);
                Ok(None)
            }
            Primitive::ArrayFinishDrained => {
                let owner = args
                    .first()
                    .ok_or_else(|| self.error("ArrayFinishDrained lacks its array operand"))?
                    .register;
                let slots = self
                    .state
                    .array_slots
                    .get(&owner)
                    .cloned()
                    .unwrap_or(ArraySlotState {
                        length: None,
                        empty: BTreeSet::new(),
                        dynamic_hole: false,
                        reference_origins: BTreeMap::new(),
                    });
                let externally_proven =
                    slots.length.is_none() && slots.empty.is_empty() && !slots.dynamic_hole;
                if externally_proven {
                    return Ok(None);
                }
                if slots.dynamic_hole
                    || !slots.reference_origins.is_empty()
                    || slots
                        .length
                        .is_none_or(|length| slots.empty.len() as u64 != length)
                {
                    return Err(self.error(
                        "ArrayFinishDrained requires an exact proof that every array slot was moved out",
                    ));
                }
                Ok(None)
            }
            Primitive::BytesFromArrayMove => {
                let owner = args
                    .first()
                    .ok_or_else(|| self.error("BytesFromArrayMove lacks its array operand"))?
                    .register;
                let slots = self
                    .state
                    .array_slots
                    .get(&owner)
                    .cloned()
                    .unwrap_or(ArraySlotState {
                        length: None,
                        empty: BTreeSet::new(),
                        dynamic_hole: false,
                        reference_origins: BTreeMap::new(),
                    });
                if slots.dynamic_hole
                    || !slots.empty.is_empty()
                    || !slots.reference_origins.is_empty()
                {
                    return Err(
                        self.error("BytesFromArrayMove requires every array slot initialized")
                    );
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    fn summary_index(&self, index: &ArrayIndexSummary, args: &[Operand]) -> Option<u64> {
        match index {
            ArrayIndexSummary::Constant(value) => Some(*value),
            ArrayIndexSummary::Parameter(parameter) => args
                .get(*parameter as usize)
                .and_then(|operand| self.state.constants[operand.register as usize]),
            ArrayIndexSummary::Dynamic => None,
        }
    }

    fn summary_owner(
        &self,
        parameter: u32,
        args: &[Operand],
        action: &str,
    ) -> Result<Option<Register>, FlowError> {
        let operand = args.get(parameter as usize).ok_or_else(|| {
            self.error(format!(
                "{action} summary names missing call argument {parameter}"
            ))
        })?;
        if self.state.loans.contains_key(&operand.register) {
            self.array_owner(operand.register, action)
        } else {
            Ok(Some(operand.register))
        }
    }

    fn apply_array_effect(
        &mut self,
        owner: Register,
        effect: &ArrayCallEffect,
        args: &[Operand],
    ) -> Result<(), FlowError> {
        let mut slots = self
            .state
            .array_slots
            .get(&owner)
            .cloned()
            .unwrap_or(ArraySlotState {
                length: None,
                empty: BTreeSet::new(),
                dynamic_hole: false,
                reference_origins: BTreeMap::new(),
            });
        let index = effect
            .index
            .as_ref()
            .and_then(|index| self.summary_index(index, args));
        let reference_origin = self.stored_reference_origin(
            effect
                .value_parameter
                .and_then(|parameter| args.get(parameter as usize)),
            &effect.value_path,
            "array call reference write",
        )?;
        let check_bounds = |this: &Self, slots: &ArraySlotState, index: u64| {
            if slots.length.is_some_and(|length| index >= length) {
                Err(this.error(format!(
                    "array call summary uses out-of-bounds index {index} for length {}",
                    slots.length.unwrap()
                )))
            } else {
                Ok(())
            }
        };
        match effect.kind {
            ArrayEffectKind::Observe => {
                if slots.dynamic_hole {
                    return Err(self.error(
                        "array call cannot prove an observed element initialized after a dynamic-index move",
                    ));
                }
                if let Some(index) = index {
                    check_bounds(self, &slots, index)?;
                    if slots.empty.contains(&index) {
                        return Err(self.error(format!(
                            "array call observes index {index} after it was moved out"
                        )));
                    }
                } else if effect.index.is_some() && !slots.empty.is_empty() {
                    return Err(self.error(
                        "dynamic array call observation may alias an exact moved-out index",
                    ));
                }
            }
            ArrayEffectKind::MoveOut => {
                if slots.dynamic_hole {
                    return Err(self.error(
                        "array call cannot prove an element initialized after a dynamic-index move",
                    ));
                }
                if let Some(index) = index {
                    check_bounds(self, &slots, index)?;
                    if !slots.empty.insert(index) {
                        return Err(self.error(format!(
                            "array call moves index {index} after it was already moved out"
                        )));
                    }
                    slots.reference_origins.remove(&index);
                } else {
                    if !slots.reference_origins.is_empty() {
                        return Err(self.error(
                            "dynamic array call move cannot transport an exact stored reference origin",
                        ));
                    }
                    slots.dynamic_hole = true;
                }
            }
            ArrayEffectKind::Restore => {
                let Some(index) = index else {
                    return Err(self.error(
                        "dynamic array call restoration cannot prove which slot it initializes",
                    ));
                };
                check_bounds(self, &slots, index)?;
                if !slots.empty.remove(&index) {
                    return Err(
                        self.error(format!("array call overwrites initialized index {index}"))
                    );
                }
                if let Some(origin) = reference_origin {
                    slots.reference_origins.insert(index, origin);
                }
            }
            ArrayEffectKind::Push => {
                let previous_length = slots.length;
                if let Some(origin) = reference_origin {
                    let Some(index) = previous_length else {
                        return Err(self.error(
                            "array call push cannot place a reference origin at an unknown array index",
                        ));
                    };
                    slots.reference_origins.insert(index, origin);
                }
                slots.length = previous_length.and_then(|length| length.checked_add(1));
            }
            ArrayEffectKind::Pop => {
                if slots.dynamic_hole {
                    return Err(
                        self.error("array call cannot pop after an unresolved dynamic-index move")
                    );
                }
                if let Some(length) = slots.length {
                    let Some(last) = length.checked_sub(1) else {
                        return Err(self.error("array call pops an empty array"));
                    };
                    if slots.empty.contains(&last) {
                        return Err(self
                            .error("array call pops a final element that was already moved out"));
                    }
                    slots.length = Some(last);
                    slots.empty.retain(|index| *index < last);
                    slots.reference_origins.remove(&last);
                }
            }
            ArrayEffectKind::Dense => {
                if slots.dynamic_hole
                    || !slots.empty.is_empty()
                    || !slots.reference_origins.is_empty()
                {
                    return Err(self.error(
                        "array call requires every slot initialized before dense conversion",
                    ));
                }
            }
            ArrayEffectKind::Finish => {
                let externally_proven =
                    slots.length.is_none() && slots.empty.is_empty() && !slots.dynamic_hole;
                if !externally_proven
                    && (slots.dynamic_hole
                        || !slots.reference_origins.is_empty()
                        || slots
                            .length
                            .is_none_or(|length| slots.empty.len() as u64 != length))
                {
                    return Err(self.error(
                        "array call finish requires exact proof that every slot was moved out",
                    ));
                }
            }
        }
        self.state.array_slots.insert(owner, slots);
        Ok(())
    }

    fn apply_array_call(
        &mut self,
        function: u32,
        args: &[Operand],
    ) -> Result<Option<ArraySlotState>, FlowError> {
        let Some(summary) = self.context.array_calls.get(&function) else {
            // Cleanup-only replays do not carry the whole-program table. The
            // importing ownership pass already validated call effects; these
            // replays need only reconstruct cleanup order.
            if self.context.array_calls.is_empty() {
                return Ok(None);
            }
            for argument in args {
                let owner = if self.state.loans.contains_key(&argument.register) {
                    self.array_owner(argument.register, "opaque array call")?
                } else {
                    Some(argument.register)
                };
                if owner.is_some_and(|owner| self.state.array_slots.contains_key(&owner)) {
                    return Err(self.error(
                        format!(
                            "opaque call to function {function} receives a tracked array but has no inferred ownership summary"
                        ),
                    ));
                }
            }
            return Ok(None);
        };
        let mut owners = BTreeMap::<Register, u32>::new();
        for effect in &summary.effects {
            let Some(owner) =
                self.summary_owner(effect.owner_parameter, args, "array ownership effect")?
            else {
                continue;
            };
            if let Some(previous) = owners.insert(owner, effect.owner_parameter)
                && previous != effect.owner_parameter
            {
                return Err(self.error(
                    "array call aliases two summarized owner parameters to the same array",
                ));
            }
            self.apply_array_effect(owner, effect, args)?;
        }
        Ok(match summary.result.as_ref() {
            Some(ArrayResultSummary::Empty) => Some(ArraySlotState {
                length: Some(0),
                empty: BTreeSet::new(),
                dynamic_hole: false,
                reference_origins: BTreeMap::new(),
            }),
            Some(ArrayResultSummary::Filled(length)) => Some(ArraySlotState {
                length: self.summary_index(length, args),
                empty: BTreeSet::new(),
                dynamic_hole: false,
                reference_origins: BTreeMap::new(),
            }),
            Some(ArrayResultSummary::Parameter(parameter)) => self
                .summary_owner(*parameter, args, "forwarded array result")?
                .and_then(|owner| self.state.array_slots.get(&owner).cloned()),
            None => None,
        })
    }

    fn error(&self, message: impl Into<String>) -> FlowError {
        flow_error(self.block, message)
    }

    fn issued_loan_id(&self) -> u32 {
        self.context
            .loans
            .issued
            .get(&(self.block, self.statement))
            .copied()
            .unwrap_or(u32::MAX)
    }

    fn expect_live(&self, register: Register, action: &str) -> Result<(), FlowError> {
        match &self.state.regs[register as usize] {
            RegState::Live | RegState::Partial(_) => Ok(()),
            RegState::MaybeLive => Err(self.error(format!(
                "{action} reads r{register}, which is only conditionally initialized"
            ))),
            RegState::Undefined | RegState::Consumed if !self.context.strict => Ok(()),
            RegState::Undefined => Err(self.error(format!(
                "{action} reads r{register}, which is never initialized on this path"
            ))),
            RegState::Consumed => Err(self.error(format!(
                "{action} reads r{register} after it was moved or destroyed"
            ))),
        }
    }

    /// Record one ordinary owned use and check the declared upper bound.
    fn count_use(&mut self, register: Register) -> Result<(), FlowError> {
        let count = if let Some(group) = self.state.quantity_groups[register as usize] {
            self.state.quantity_uses[group as usize].bump();
            self.state.quantity_uses[group as usize]
        } else {
            self.state.uses[register as usize].bump();
            self.state.uses[register as usize]
        };
        if !self.context.strict {
            return Ok(());
        }
        let interval = self.context.locals[register as usize].use_interval;
        if let Some(upper) = interval.upper
            && count.lower > upper
        {
            return Err(self.error(format!(
                "r{register} is used more than its declared Use upper bound {upper} allows"
            )));
        }
        Ok(())
    }

    fn replaceable_unrestricted(&self, register: Register) -> bool {
        let fact = &self.context.locals[register as usize];
        matches!(
            fact.ownership,
            OwnershipCategory::SharedRef
                | OwnershipCategory::CopyValue
                | OwnershipCategory::ZstErased
        ) && fact.drop_glue != DropGlueKind::Custom
    }

    fn define(&mut self, register: Register, origin: &str) -> Result<(), FlowError> {
        let replaceable_unrestricted = self.replaceable_unrestricted(register);
        let slot = &mut self.state.regs[register as usize];
        if slot.is_live() {
            if self.context.strict && !replaceable_unrestricted {
                return Err(self.error(format!(
                    "{origin} stores into r{register} while it still holds a value"
                )));
            }
            self.state.order.retain(|live| *live != register);
            if replaceable_unrestricted {
                self.state.loans.remove(&register);
            }
        }
        *slot = RegState::Live;
        self.state.conditional_fields.remove(&register);
        self.state.array_slots.remove(&register);
        self.state.aggregate_reference_origins.remove(&register);
        self.state.aggregate_reference_origins.remove(&register);
        self.state.constants[register as usize] = None;
        self.state.active_variants[register as usize] = None;
        self.state.enum_tag_sources[register as usize] = None;
        if let Some(age) = self.state.shell_ages[register as usize].take() {
            let at = age.min(self.state.order.len());
            self.state.order.insert(at, register);
        } else {
            self.state.order.push(register);
        }
        self.state.uses[register as usize] = UseCount::ZERO;
        let ty = self.context.register_type(register);
        if matches!(self.context.representation(ty), Type::Array { .. }) {
            self.state.array_slots.insert(
                register,
                ArraySlotState {
                    length: None,
                    empty: BTreeSet::new(),
                    dynamic_hole: false,
                    reference_origins: BTreeMap::new(),
                },
            );
        }
        self.state.quantity_groups[register as usize] =
            (self.context.quantity_leaf_count(ty) == 1).then_some(register);
        self.state.quantity_uses[register as usize] = UseCount::ZERO;
        // A reference produced by anything other than a borrow instruction
        // (block parameter, call result, copy of a shared reference) carries
        // an opaque loan: it is real at runtime but its borrowed place is not
        // locally analyzable, so it is conservatively treated like an
        // external loan and never proves or refutes local conflicts.
        if self.context.is_reference(ty) && !self.state.loans.contains_key(&register) {
            self.state.loans.insert(
                register,
                LiveLoan {
                    id: u32::MAX,
                    unique: self.context.is_unique_reference(ty),
                    external: true,
                    borrowed: Place::local(register),
                    parent: None,
                    suspended: 0,
                },
            );
        }
        Ok(())
    }

    /// Consume a whole register: moves, destruction, deconstruction, ends.
    fn consume(&mut self, register: Register, action: &str) -> Result<(), FlowError> {
        self.expect_live(register, action)?;
        if let Some(loan) = self.state.loans.remove(&register) {
            self.unsuspend(loan.parent);
            self.state.holes.remove(&register);
        }
        self.check_not_borrowed(register, action)?;
        self.state.regs[register as usize] = RegState::Consumed;
        self.state.conditional_fields.remove(&register);
        self.state.array_slots.remove(&register);
        self.state.aggregate_reference_origins.remove(&register);
        self.state.constants[register as usize] = None;
        self.state.quantity_groups[register as usize] = None;
        self.state.active_variants[register as usize] = None;
        self.state.enum_tag_sources[register as usize] = None;
        for source in &mut self.state.enum_tag_sources {
            if *source == Some(register) {
                *source = None;
            }
        }
        self.state.order.retain(|live| *live != register);
        for label in &mut self.state.labels {
            label.owners.retain(|owner| *owner != register);
        }
        Ok(())
    }

    fn unsuspend(&mut self, parent: Option<Register>) {
        if let Some(parent) = parent
            && let Some(loan) = self.state.loans.get_mut(&parent)
        {
            loan.suspended = loan.suspended.saturating_sub(1);
        }
    }

    /// Reject touching an owner whose subtree is still borrowed.
    fn check_not_borrowed(&self, register: Register, action: &str) -> Result<(), FlowError> {
        let root = Place::local(register);
        for (reference, loan) in &self.state.loans {
            if !loan.external && loan.borrowed.overlaps(&root) {
                return Err(self.error(format!(
                    "{action} consumes r{register} while the loan held by r{reference} is live"
                )));
            }
        }
        Ok(())
    }

    /// Reject a new loan that conflicts with a live loan of an overlapping
    /// place. Shared loans may overlap shared loans; a unique loan conflicts
    /// with every overlapping live unsuspended loan.
    fn check_loan_conflict(
        &self,
        borrowed: &Place,
        unique: bool,
        skip_parent: Option<Register>,
    ) -> Result<(), FlowError> {
        for (reference, loan) in &self.state.loans {
            if loan.external || Some(*reference) == skip_parent || loan.suspended > 0 {
                continue;
            }
            if loan.borrowed.overlaps(borrowed) && (unique || loan.unique) {
                return Err(self.error(format!(
                    "a {} loan of an overlapping place conflicts with the live {} loan held by r{reference}",
                    if unique { "unique" } else { "shared" },
                    if loan.unique { "unique" } else { "shared" },
                )));
            }
        }
        Ok(())
    }

    /// Evaluate one operand. A move transfers the whole owner and counts one
    /// quantitative use; a copy duplicates the value, which requires a
    /// structurally duplicable type (references are duplicated as loans) and,
    /// because duplicability already implies an unbounded declared upper
    /// bound, never tightens the accounted interval.
    fn operand(&mut self, operand: &Operand, action: &str) -> Result<(), FlowError> {
        match operand.mode {
            UseMode::Move => {
                self.count_use(operand.register)?;
                self.consume(operand.register, action)
            }
            UseMode::Copy => {
                self.expect_live(operand.register, action)?;
                if self.context.strict {
                    let ty = self.context.register_type(operand.register);
                    if !self.context.types[ty as usize].claimed_duplicable()
                        && !self.context.is_reference(ty)
                    {
                        return Err(self.error(format!(
                            "{action} copies r{}, whose type is not duplicable",
                            operand.register
                        )));
                    }
                }
                Ok(())
            }
        }
    }

    fn statement(&mut self, kind: &InstructionKind) -> Result<(), FlowError> {
        match kind {
            InstructionKind::Const { dst, value } => {
                self.define(*dst, "Const")?;
                self.state.constants[*dst as usize] = match value {
                    grandiose_vm::Constant::U8(value) => Some(u64::from(*value)),
                    grandiose_vm::Constant::U16(value) => Some(u64::from(*value)),
                    grandiose_vm::Constant::U32(value) => Some(u64::from(*value)),
                    grandiose_vm::Constant::U64(value) | grandiose_vm::Constant::Usize(value) => {
                        Some(*value)
                    }
                    _ => None,
                };
                Ok(())
            }
            InstructionKind::Copy { dst, src } => {
                let tag_source = self.state.enum_tag_sources[src.register as usize];
                let active_variant = self.state.active_variants[src.register as usize];
                let constant = self.state.constants[src.register as usize];
                let aggregate_origins = self
                    .state
                    .aggregate_reference_origins
                    .get(&src.register)
                    .cloned();
                let source = Operand {
                    register: src.register,
                    mode: UseMode::Copy,
                };
                self.operand(&source, "Copy")?;
                self.define(*dst, "Copy")?;
                if let Some(fresh) = self.state.quantity_groups[*dst as usize] {
                    self.state.quantity_uses[fresh as usize] = UseCount::ZERO;
                }
                self.state.quantity_groups[*dst as usize] =
                    self.state.quantity_groups[src.register as usize];
                self.state.enum_tag_sources[*dst as usize] = tag_source;
                self.state.active_variants[*dst as usize] = active_variant;
                self.state.constants[*dst as usize] = constant;
                if let Some(origins) = aggregate_origins {
                    self.state.aggregate_reference_origins.insert(*dst, origins);
                }
                let ty = self.context.register_type(src.register);
                if self.context.is_reference(ty) {
                    let loan = self
                        .state
                        .loans
                        .get(&src.register)
                        .cloned()
                        .unwrap_or(LiveLoan {
                            id: u32::MAX,
                            unique: self.context.is_unique_reference(ty),
                            external: true,
                            borrowed: Place::local(src.register),
                            parent: None,
                            suspended: 0,
                        });
                    self.state.loans.insert(
                        *dst,
                        LiveLoan {
                            id: u32::MAX,
                            borrowed: loan.borrowed,
                            parent: loan.parent,
                            unique: loan.unique,
                            external: loan.external,
                            suspended: 0,
                        },
                    );
                }
                Ok(())
            }
            InstructionKind::Move { dst, src } => {
                self.expect_live(src.register, "Move")?;
                let source = src.register as usize;
                let destination = *dst as usize;
                // Renaming: the owner, its age, loan, hole, bitmap, and use
                // account transfer to the destination register unchanged.
                let state = std::mem::replace(&mut self.state.regs[source], RegState::Consumed);
                for label in &mut self.state.labels {
                    label.owners.retain(|owner| *owner != src.register);
                }
                let replacing_unrestricted =
                    self.state.regs[destination].is_live() && self.replaceable_unrestricted(*dst);
                if self.state.regs[destination].is_live()
                    && self.context.strict
                    && !replacing_unrestricted
                {
                    return Err(self.error(format!(
                        "Move stores into r{dst} while it still holds a value"
                    )));
                }
                if replacing_unrestricted {
                    self.state.order.retain(|live| *live != *dst);
                    self.state.loans.remove(dst);
                    self.state.holes.remove(dst);
                    self.state.conditional_fields.remove(dst);
                    self.state.array_slots.remove(dst);
                    self.state.aggregate_reference_origins.remove(dst);
                    self.state.active_variants[destination] = None;
                    self.state.enum_tag_sources[destination] = None;
                    self.state.constants[destination] = None;
                    self.state.uses[destination] = UseCount::ZERO;
                    self.state.quantity_groups[destination] = None;
                }
                self.state.regs[destination] = if matches!(state, RegState::Undefined) {
                    RegState::Live
                } else {
                    state
                };
                self.state.active_variants[destination] = self.state.active_variants[source].take();
                self.state.enum_tag_sources[destination] =
                    self.state.enum_tag_sources[source].take();
                for tag_source in &mut self.state.enum_tag_sources {
                    if *tag_source == Some(src.register) {
                        *tag_source = Some(*dst);
                    }
                }
                if let Some(position) = self
                    .state
                    .order
                    .iter()
                    .position(|live| *live == src.register)
                {
                    self.state.order.retain(|live| *live != *dst);
                    let position = self
                        .state
                        .order
                        .iter()
                        .position(|live| *live == src.register)
                        .unwrap_or(position);
                    self.state.order[position] = *dst;
                } else if !self.context.strict {
                    self.state.order.push(*dst);
                }
                if let Some(mut loan) = self.state.loans.remove(&src.register) {
                    let rebases_opaque_external_root = loan.external
                        && loan.id == u32::MAX
                        && loan.parent.is_none()
                        && loan.borrowed == Place::local(src.register);
                    if rebases_opaque_external_root {
                        // Opaque caller-provided references use their current
                        // SSA register as a symbolic place. A Move is a pure
                        // rename, so keep that placeholder canonical instead
                        // of leaking an edge-transfer temporary into child
                        // reborrows observed on the next dataflow iteration.
                        loan.borrowed = Place::local(*dst);
                    }
                    self.state.loans.insert(*dst, loan);
                    // Move is a pure SSA rename for a reference loan. Any
                    // simultaneously live reborrow must follow that rename so
                    // its eventual retirement unsuspends the transferred
                    // parent rather than the now-consumed source register.
                    for child in self.state.loans.values_mut() {
                        if child.parent == Some(src.register) {
                            child.parent = Some(*dst);
                        }
                        if rebases_opaque_external_root
                            && child.external
                            && child.borrowed.base == src.register
                        {
                            child.borrowed.base = *dst;
                        }
                    }
                }
                if self.state.holes.remove(&src.register) {
                    self.state.holes.insert(*dst);
                }
                if let Some(fields) = self.state.conditional_fields.remove(&src.register) {
                    self.state.conditional_fields.insert(*dst, fields);
                }
                if let Some(slots) = self.state.array_slots.remove(&src.register) {
                    self.state.array_slots.insert(*dst, slots);
                }
                if let Some(origins) = self.state.aggregate_reference_origins.remove(&src.register)
                {
                    self.state.aggregate_reference_origins.insert(*dst, origins);
                }
                self.state.constants[destination] = self.state.constants[source].take();
                self.state.uses[destination] = self.state.uses[source];
                self.state.uses[source] = UseCount::ZERO;
                self.state.quantity_groups[destination] = self.state.quantity_groups[source].take();
                Ok(())
            }
            InstructionKind::Borrow { dst, src, unique } => {
                self.expect_live(*src, "Borrow")?;
                let borrowed = Place::local(*src);
                self.check_loan_conflict(&borrowed, *unique, None)?;
                self.define(*dst, "Borrow")?;
                self.state.loans.insert(
                    *dst,
                    LiveLoan {
                        id: self.issued_loan_id(),
                        unique: *unique,
                        external: false,
                        borrowed,
                        parent: None,
                        suspended: 0,
                    },
                );
                Ok(())
            }
            InstructionKind::ProjectBorrow {
                dst,
                src,
                field,
                unique,
            } => {
                let through_reference = self.context.is_reference(self.context.register_type(*src));
                let (borrowed, parent) = if through_reference {
                    let Some(loan) = self.state.loans.get(src) else {
                        return Err(self.error(format!(
                            "ProjectBorrow reads through r{src}, which holds no live loan"
                        )));
                    };
                    if self.state.holes.contains(src) {
                        return Err(self.error(format!(
                            "ProjectBorrow reads through r{src} while its referent is moved out"
                        )));
                    }
                    let mut borrowed = loan.borrowed.clone();
                    borrowed.projection.push(Projection::Field {
                        variant: None,
                        field: *field,
                    });
                    (borrowed, Some(*src))
                } else {
                    self.expect_live(*src, "ProjectBorrow")?;
                    self.field_access(*src, *field, "ProjectBorrow")?;
                    (
                        Place::field(*src, self.state.active_variants[*src as usize], *field),
                        None,
                    )
                };
                self.check_loan_conflict(&borrowed, *unique, parent)?;
                let external = parent
                    .and_then(|parent| self.state.loans.get(&parent))
                    .is_some_and(|loan| loan.external);
                if let Some(parent) = parent
                    && let Some(loan) = self.state.loans.get_mut(&parent)
                {
                    loan.suspended += 1;
                }
                self.define(*dst, "ProjectBorrow")?;
                self.state.loans.insert(
                    *dst,
                    LiveLoan {
                        id: self.issued_loan_id(),
                        unique: *unique,
                        // A projection through a caller-provided reference
                        // pins caller-owned memory, never a local register.
                        external,
                        borrowed,
                        parent,
                        suspended: 0,
                    },
                );
                Ok(())
            }
            InstructionKind::Reborrow { dst, src, unique } => {
                let Some(parent) = self.state.loans.get(src).cloned() else {
                    return Err(self.error(format!(
                        "Reborrow reads through r{src}, which holds no live loan"
                    )));
                };
                if self.state.holes.contains(src) {
                    return Err(self.error(format!(
                        "Reborrow reads through r{src} while its referent is moved out"
                    )));
                }
                if let Some(loan) = self.state.loans.get_mut(src) {
                    loan.suspended += 1;
                }
                self.define(*dst, "Reborrow")?;
                self.state.loans.insert(
                    *dst,
                    LiveLoan {
                        id: self.issued_loan_id(),
                        unique: *unique,
                        // Reborrowing a caller-provided reference pins the
                        // caller's referent, never a local register.
                        external: parent.external,
                        borrowed: parent.borrowed,
                        parent: Some(*src),
                        suspended: 0,
                    },
                );
                Ok(())
            }
            InstructionKind::DerefCopy { dst, src } => {
                self.expect_live(*src, "DerefCopy")?;
                if self.state.holes.contains(src) {
                    return Err(self.error(format!(
                        "DerefCopy reads through r{src} while its referent is moved out"
                    )));
                }
                if let Some(loan) = self.state.loans.get(src)
                    && loan.suspended > 0
                {
                    return Err(self.error(format!(
                        "DerefCopy reads through r{src} while its loan is suspended by a reborrow"
                    )));
                }
                self.define(*dst, "DerefCopy")
            }
            InstructionKind::DerefMove { dst, src } => {
                self.expect_live(*src, "DerefMove")?;
                if !self
                    .context
                    .is_unique_reference(self.context.register_type(*src))
                {
                    return Err(
                        self.error(format!("DerefMove requires a unique reference in r{src}"))
                    );
                }
                if !self.state.holes.insert(*src) {
                    return Err(self.error(format!(
                        "DerefMove reads through r{src}, whose referent is already moved out"
                    )));
                }
                if let Some(loan) = self.state.loans.get(src)
                    && loan.suspended > 0
                {
                    return Err(self.error(format!(
                        "DerefMove reads through r{src} while its loan is suspended by a reborrow"
                    )));
                }
                self.define(*dst, "DerefMove")
            }
            InstructionKind::DerefStore { dst, src } => {
                self.expect_live(*dst, "DerefStore")?;
                if !self.state.holes.remove(dst) {
                    return Err(self.error(format!(
                        "DerefStore writes through r{dst}, whose referent is not moved out"
                    )));
                }
                self.operand(src, "DerefStore")
            }
            InstructionKind::EndBorrow { reference } => {
                if matches!(
                    self.context.locals[*reference as usize].ownership,
                    OwnershipCategory::SharedRef
                ) && matches!(
                    self.state.regs[*reference as usize],
                    RegState::MaybeLive | RegState::Consumed
                ) {
                    // Correlated SSA paths may make a proof-only shared
                    // handle conditional at a later common cleanup. Ending
                    // that handle is safe on either path; ordinary reads of a
                    // MaybeLive reference remain rejected.
                    self.state.loans.remove(reference);
                    self.state.regs[*reference as usize] = RegState::Consumed;
                    self.state.order.retain(|live| live != reference);
                    return Ok(());
                }
                let Some(loan) = self.state.loans.get(reference) else {
                    if matches!(
                        self.context.locals[*reference as usize].ownership,
                        OwnershipCategory::SharedRef
                    ) {
                        // A copied proof-only shared handle may outlive the
                        // precise loan identity through correlated SSA joins.
                        // Retiring the handle is still a valid non-unique end.
                        return self.consume(*reference, "EndBorrow");
                    }
                    return Err(if self.context.strict {
                        self.error(format!(
                            "EndBorrow ends r{reference}, which holds no live loan"
                        ))
                    } else {
                        // Bridge mode: treat as consuming the reference value.
                        return self.consume(*reference, "EndBorrow");
                    });
                };
                if loan.suspended > 0 {
                    return Err(self.error(format!(
                        "EndBorrow ends r{reference} while a reborrow of it is still live"
                    )));
                }
                if self.state.holes.contains(reference) {
                    return Err(self.error(format!(
                        "EndBorrow ends r{reference} while its referent is moved out"
                    )));
                }
                self.consume(*reference, "EndBorrow")
            }
            InstructionKind::MakeBindingPack {
                dst,
                binding_type,
                payloads,
            } => {
                if self.context.strict && *binding_type != self.context.register_type(*dst) {
                    return Err(self.error(format!(
                        "MakeBindingPack initializes r{dst} with type {binding_type}, but the register has type {}",
                        self.context.register_type(*dst)
                    )));
                }
                if !matches!(
                    self.context.representation(*binding_type),
                    Type::BindingPack { .. }
                ) {
                    return Err(self.error(format!(
                        "MakeBindingPack initializes r{dst} with a non-binding-pack type"
                    )));
                }
                let expected = self
                    .context
                    .aggregate_fields(*binding_type, None)
                    .ok_or_else(|| self.error("binding pack payload is not an aggregate"))?;
                if self.context.strict && payloads.len() != expected.len() {
                    return Err(self.error(format!(
                        "MakeBindingPack initializes r{dst} with {} payloads, but its layout requires {}",
                        payloads.len(),
                        expected.len()
                    )));
                }
                let mut aggregate_origins = BTreeMap::new();
                for (field, (payload, expected)) in payloads.iter().zip(&expected).enumerate() {
                    if self.context.strict
                        && self.context.register_type(payload.register) != *expected
                    {
                        return Err(self.error(format!(
                            "MakeBindingPack payload {field} of r{dst} has the wrong type"
                        )));
                    }
                    let prefix = vec![field as u32];
                    if let Some(loan) = self.state.loans.get(&payload.register) {
                        aggregate_origins.insert(
                            prefix.clone(),
                            StoredReferenceOrigin {
                                unique: loan.unique,
                                external: loan.external,
                                borrowed: loan.borrowed.clone(),
                                parent: loan.parent,
                            },
                        );
                    }
                    if let Some(nested) = self
                        .state
                        .aggregate_reference_origins
                        .get(&payload.register)
                    {
                        for (path, origin) in nested {
                            let mut projected = prefix.clone();
                            projected.extend(path);
                            aggregate_origins.insert(projected, origin.clone());
                        }
                    }
                }
                for payload in payloads {
                    self.operand(payload, "MakeBindingPack")?;
                }
                self.define(*dst, "MakeBindingPack")?;
                if !aggregate_origins.is_empty() {
                    self.state
                        .aggregate_reference_origins
                        .insert(*dst, aggregate_origins);
                }
                Ok(())
            }
            InstructionKind::Construct {
                dst,
                ty,
                variant,
                fields,
            } => {
                if self.context.strict && *ty != self.context.register_type(*dst) {
                    return Err(self.error(format!(
                        "Construct initializes r{dst} with type {ty}, but the register has type {}",
                        self.context.register_type(*dst)
                    )));
                }
                let expected_fields =
                    if matches!(self.context.representation(*ty), Type::Enum { .. }) {
                        let Some(variant) = variant else {
                            return Err(self.error(format!(
                                "Construct creates enum r{dst} without an active variant"
                            )));
                        };
                        self.context
                            .aggregate_fields(*ty, Some(*variant))
                            .ok_or_else(|| {
                                self.error(format!(
                                    "Construct creates enum r{dst} with unknown variant {variant}"
                                ))
                            })?
                    } else {
                        self.context.aggregate_fields(*ty, None).ok_or_else(|| {
                            self.error(format!("Construct initializes non-aggregate r{dst}"))
                        })?
                    };
                if self.context.strict && fields.len() != expected_fields.len() {
                    return Err(self.error(format!(
                        "Construct initializes r{dst} with {} fields, but its active layout requires {}",
                        fields.len(),
                        expected_fields.len()
                    )));
                }
                if self.context.strict {
                    for (field, (operand, expected)) in
                        fields.iter().zip(&expected_fields).enumerate()
                    {
                        let actual = self.context.register_type(operand.register);
                        if actual != *expected {
                            return Err(self.error(format!(
                                "Construct field {field} of r{dst} has type {actual}, but the active layout requires {expected}"
                            )));
                        }
                    }
                }
                let mut aggregate_origins = BTreeMap::new();
                for (field, operand) in fields.iter().enumerate() {
                    let mut field_path = Vec::with_capacity(2);
                    if let Some(variant) = variant {
                        field_path.push(u32::MAX - *variant);
                    }
                    field_path.push(field as u32);
                    if let Some(loan) = self.state.loans.get(&operand.register) {
                        aggregate_origins.insert(
                            field_path.clone(),
                            StoredReferenceOrigin {
                                unique: loan.unique,
                                external: loan.external,
                                borrowed: loan.borrowed.clone(),
                                parent: loan.parent,
                            },
                        );
                    }
                    if let Some(nested) = self
                        .state
                        .aggregate_reference_origins
                        .get(&operand.register)
                    {
                        for (path, origin) in nested {
                            let mut projected = Vec::with_capacity(path.len() + field_path.len());
                            projected.extend(&field_path);
                            projected.extend(path);
                            aggregate_origins.insert(projected, origin.clone());
                        }
                    }
                }
                for field in fields {
                    self.operand(field, "Construct")?;
                }
                if self.context.strict
                    && self.state.regs[*dst as usize].is_live()
                    && self.state.shell_ages[*dst as usize].is_none()
                {
                    return Err(self.error(format!(
                        "Construct stores into r{dst} while it still holds a value"
                    )));
                }
                if self.state.regs[*dst as usize].is_live() {
                    self.state.order.retain(|live| *live != *dst);
                    self.state.regs[*dst as usize] = RegState::Consumed;
                }
                self.define(*dst, "Construct")?;
                if !aggregate_origins.is_empty() {
                    self.state
                        .aggregate_reference_origins
                        .insert(*dst, aggregate_origins);
                }
                if matches!(self.context.representation(*ty), Type::Enum { .. }) {
                    let variant = variant.expect("enum variant validated above");
                    self.state.active_variants[*dst as usize] = Some(variant);
                }
                Ok(())
            }
            InstructionKind::ProjectCopy { dst, src, field } => {
                self.field_access(src.register, *field, "ProjectCopy")?;
                let origins = self.projected_aggregate_reference_origins(src.register, *field);
                self.define(*dst, "ProjectCopy")?;
                self.install_projected_reference_origins(*dst, origins);
                Ok(())
            }
            InstructionKind::ProjectMove { dst, src, field } => {
                self.field_access(src.register, *field, "ProjectMove")?;
                let origins = self.projected_aggregate_reference_origins(src.register, *field);
                let ty = self.context.register_type(src.register);
                if self.context.strict
                    && self.context.locals[src.register as usize].drop_glue == DropGlueKind::Custom
                {
                    return Err(self.error(format!(
                        "ProjectMove moves a field out of r{}, whose type has a custom Drop hook",
                        src.register
                    )));
                }
                let variant = self.state.active_variants[src.register as usize];
                if let Some(fields) = self.context.aggregate_fields(ty, variant) {
                    let bitmap = match &mut self.state.regs[src.register as usize] {
                        RegState::Partial(bitmap) => bitmap,
                        slot @ (RegState::Live | RegState::Undefined | RegState::Consumed) => {
                            *slot = RegState::Partial(vec![true; fields.len()]);
                            let RegState::Partial(bitmap) = slot else {
                                unreachable!()
                            };
                            bitmap
                        }
                        RegState::MaybeLive => {
                            return Err(self.error(format!(
                                "ProjectMove reads r{}, which is only conditionally initialized",
                                src.register
                            )));
                        }
                    };
                    if let Some(initialized) = bitmap.get_mut(*field as usize) {
                        if !*initialized && self.context.strict {
                            return Err(self.error(format!(
                                "ProjectMove moves field {field} of r{} twice",
                                src.register
                            )));
                        }
                        *initialized = false;
                    }
                } else if matches!(self.context.representation(ty), Type::Enum { .. })
                    && self.context.strict
                {
                    return Err(self.error(format!(
                        "ProjectMove reads enum payload field {field} of r{} without an active-variant proof",
                        src.register
                    )));
                }
                if let Some(source_origins) = self
                    .state
                    .aggregate_reference_origins
                    .get_mut(&src.register)
                {
                    source_origins.retain(|path, _| path.first() != Some(field));
                    if source_origins.is_empty() {
                        self.state.aggregate_reference_origins.remove(&src.register);
                    }
                }
                self.define(*dst, "ProjectMove")?;
                self.install_projected_reference_origins(*dst, origins);
                Ok(())
            }
            InstructionKind::Deconstruct { src } => {
                self.expect_live(*src, "Deconstruct")?;
                if self.context.strict
                    && self.context.locals[*src as usize].drop_glue == DropGlueKind::Custom
                {
                    return Err(self.error(format!(
                        "Deconstruct consumes r{src}, whose type has a custom Drop hook"
                    )));
                }
                if self.context.strict {
                    let ty = self.context.register_type(*src);
                    let variant = self.state.active_variants[*src as usize];
                    if let Some(fields) = self.context.aggregate_fields(ty, variant) {
                        let initialized = match &self.state.regs[*src as usize] {
                            RegState::Live => vec![true; fields.len()],
                            RegState::Partial(bitmap) => bitmap.clone(),
                            RegState::Undefined | RegState::MaybeLive | RegState::Consumed => {
                                Vec::new()
                            }
                        };
                        for (field, (field_ty, initialized)) in
                            fields.iter().zip(&initialized).enumerate()
                        {
                            let conditional = self
                                .state
                                .conditional_fields
                                .get(src)
                                .and_then(|fields| fields.get(field))
                                .copied()
                                .unwrap_or(false);
                            if conditional && !self.context.has_field_drop_flag(*src, field as u32)
                            {
                                return Err(self.error(format!(
                                    "Deconstruct discards conditionally initialized field {field} of r{src} without a governing field drop flag"
                                )));
                            }
                            if *initialized && !self.context.type_admits_zero_use(*field_ty) {
                                return Err(self.error(format!(
                                    "Deconstruct discards still-initialized field {field} of r{src} without Use<[0,0]> evidence"
                                )));
                            }
                        }
                    }
                }
                self.state.shell_ages[*src as usize] =
                    self.state.order.iter().position(|live| live == src);
                self.consume(*src, "Deconstruct")
            }
            InstructionKind::EnumTag { dst, src } => {
                self.expect_live(*src, "EnumTag")?;
                if self.context.strict
                    && self
                        .context
                        .enum_variant_count(self.context.register_type(*src))
                        .is_none()
                {
                    return Err(
                        self.error(format!("EnumTag reads r{src}, whose type is not an enum"))
                    );
                }
                self.define(*dst, "EnumTag")?;
                if self
                    .context
                    .enum_variant_count(self.context.register_type(*src))
                    .is_some()
                {
                    self.state.enum_tag_sources[*dst as usize] = Some(*src);
                }
                Ok(())
            }
            InstructionKind::Primitive {
                dst,
                primitive,
                args,
            } => {
                let array_result = self.array_primitive(*primitive, args)?;
                let projected_loan = if matches!(
                    primitive,
                    Primitive::ArrayGetBorrowShared | Primitive::ArrayGetBorrowUnique
                ) {
                    let Some(source) = args.first().map(|argument| argument.register) else {
                        return Err(self.error("array borrow primitive has no source argument"));
                    };
                    let Some(parent) = self.state.loans.get(&source).cloned() else {
                        return Err(self.error(format!(
                            "array borrow primitive reads through r{source}, which holds no live loan"
                        )));
                    };
                    if self.state.holes.contains(&source) {
                        return Err(self.error(format!(
                            "array borrow primitive reads through r{source} while its referent is moved out"
                        )));
                    }
                    let mut borrowed = parent.borrowed.clone();
                    borrowed.projection.push(Projection::DynamicIndex);
                    let unique = *primitive == Primitive::ArrayGetBorrowUnique;
                    self.check_loan_conflict(&borrowed, unique, Some(source))?;
                    Some((parent.parent, parent.external, borrowed, unique))
                } else {
                    None
                };
                for argument in args {
                    self.operand(argument, "Primitive")?;
                }
                self.define(*dst, "Primitive")?;
                if let Some((parent, external, borrowed, unique)) = projected_loan {
                    if let Some(parent) = parent
                        && let Some(loan) = self.state.loans.get_mut(&parent)
                    {
                        // Moving the source reference temporarily removes its
                        // suspension from this ancestor. The projected result
                        // immediately inherits that same parent relationship.
                        loan.suspended += 1;
                    }
                    self.state.loans.insert(
                        *dst,
                        LiveLoan {
                            id: self.issued_loan_id(),
                            unique,
                            external,
                            borrowed,
                            parent,
                            suspended: 0,
                        },
                    );
                }
                if let Some(slots) = array_result {
                    self.state.array_slots.insert(*dst, slots);
                }
                Ok(())
            }
            InstructionKind::MakeCallable { dst, captures, .. } => {
                let mut origins = BTreeMap::new();
                for (field, capture) in captures.iter().enumerate() {
                    if let Some(origin) =
                        self.stored_reference_origin(Some(capture), &[], "MakeCallable capture")?
                    {
                        origins.insert(vec![field as u32], origin);
                    }
                    if let Some(nested) = self
                        .state
                        .aggregate_reference_origins
                        .get(&capture.register)
                    {
                        for (path, origin) in nested {
                            let mut capture_path = Vec::with_capacity(path.len() + 1);
                            capture_path.push(field as u32);
                            capture_path.extend(path);
                            origins.insert(capture_path, origin.clone());
                        }
                    }
                }
                for capture in captures {
                    self.operand(capture, "MakeCallable")?;
                }
                self.define(*dst, "MakeCallable")?;
                if !origins.is_empty() {
                    self.state.aggregate_reference_origins.insert(*dst, origins);
                }
                Ok(())
            }
            InstructionKind::MakeHandler { dst, clauses, .. } => {
                for clause in clauses {
                    self.operand(clause, "MakeHandler")?;
                }
                self.define(*dst, "MakeHandler")
            }
            InstructionKind::MakeHandlerShared { dst, captures, .. } => {
                for capture in captures {
                    self.operand(capture, "MakeHandlerShared")?;
                }
                self.define(*dst, "MakeHandlerShared")
            }
            InstructionKind::LabelPush { label, .. } => {
                if self.state.labels.iter().any(|entry| entry.label == *label) {
                    return Err(self.error(format!(
                        "LabelPush activates label slot {} more than once",
                        label.0
                    )));
                }
                self.state.labels.push(LabelBaseline {
                    label: *label,
                    owners: self.state.order.clone(),
                });
                Ok(())
            }
            InstructionKind::LabelPop { label } => {
                let Some(active) = self.state.labels.pop() else {
                    return Err(
                        self.error(format!("LabelPop removes inactive label slot {}", label.0))
                    );
                };
                if active.label != *label {
                    return Err(self.error(format!(
                        "LabelPop removes label slot {} while slot {} is innermost",
                        label.0, active.label.0
                    )));
                }
                Ok(())
            }
            InstructionKind::Drop { owner } => {
                let register = owner.register;
                if matches!(self.state.regs[register as usize], RegState::MaybeLive) {
                    // Conditional destruction through the governing drop
                    // flag; at runtime the VM Empty state skips the owner.
                    if !self.context.has_drop_flag(register) {
                        return Err(self.error(format!(
                            "Drop reads r{register}, which is only conditionally \
                             initialized and has no governing drop flag"
                        )));
                    }
                    self.state.regs[register as usize] = RegState::Consumed;
                    self.state.quantity_groups[register as usize] = None;
                    self.state.order.retain(|live| *live != register);
                    return Ok(());
                }
                self.expect_live(register, "Drop")?;
                if self.state.loans.contains_key(&register)
                    && !self
                        .context
                        .is_reference(self.context.register_type(register))
                {
                    return Err(self.error(format!(
                        "Drop destroys r{register}, which holds a live loan"
                    )));
                }
                if self.context.strict {
                    match &self.state.regs[register as usize] {
                        RegState::Partial(bitmap) => {
                            if self.context.locals[register as usize].drop_glue
                                == DropGlueKind::Custom
                            {
                                return Err(self.error(format!(
                                    "Drop destroys partially moved r{register}, whose type has a custom Drop hook"
                                )));
                            }
                            let ty = self.context.register_type(register);
                            let variant = self.state.active_variants[register as usize];
                            if let Some(fields) = self.context.aggregate_fields(ty, variant) {
                                for (field, (field_ty, initialized)) in
                                    fields.iter().zip(bitmap).enumerate()
                                {
                                    let conditional = self
                                        .state
                                        .conditional_fields
                                        .get(&register)
                                        .and_then(|fields| fields.get(field))
                                        .copied()
                                        .unwrap_or(false);
                                    if conditional
                                        && !self.context.has_field_drop_flag(register, field as u32)
                                    {
                                        return Err(self.error(format!(
                                            "Drop destroys conditionally initialized field {field} of r{register} without a governing field drop flag"
                                        )));
                                    }
                                    if *initialized && !self.context.type_admits_zero_use(*field_ty)
                                    {
                                        return Err(self.error(format!(
                                            "Drop destroys still-initialized field {field} of r{register} without Use<[0,0]> evidence"
                                        )));
                                    }
                                }
                            }
                        }
                        _ => {
                            let interval = self.context.locals[register as usize].use_interval;
                            let actual = self.state.quantity_groups[register as usize]
                                .map(|group| self.state.quantity_uses[group as usize])
                                .unwrap_or(self.state.uses[register as usize]);
                            let final_quantity_alias =
                                self.state.quantity_groups[register as usize].is_none_or(|group| {
                                    !self.state.quantity_groups.iter().enumerate().any(
                                        |(alias, candidate)| {
                                            alias != register as usize
                                                && *candidate == Some(group)
                                                && self.state.regs[alias].is_live()
                                        },
                                    )
                                });
                            if !self.context.admits_zero_use(register)
                                && final_quantity_alias
                                && actual.lower < interval.lower
                            {
                                return Err(self.error(format!(
                                    "Drop destroys r{register} before its positive Use lower bound {} is discharged; destruction cannot satisfy it",
                                    interval.lower
                                )));
                            }
                        }
                    }
                }
                self.consume(register, "Drop")
            }
        }
    }

    /// Check a field projection source: live shell with the field initialized.
    fn field_access(&self, register: Register, field: u32, action: &str) -> Result<(), FlowError> {
        self.expect_live(register, action)?;
        let ty = self.context.register_type(register);
        let variant = self.state.active_variants[register as usize];
        if self.context.strict
            && matches!(self.context.representation(ty), Type::Enum { .. })
            && variant.is_none()
        {
            return Err(self.error(format!(
                "{action} reads enum payload field {field} of r{register} without an active-variant proof"
            )));
        }
        let Some(fields) = self.context.aggregate_fields(ty, variant) else {
            if !self.context.strict {
                return Ok(());
            }
            return Err(self.error(format!(
                "{action} projects field {field} from non-aggregate r{register}"
            )));
        };
        if field as usize >= fields.len() {
            return Err(self.error(format!(
                "{action} projects out-of-bounds field {field} from r{register}"
            )));
        }
        if self
            .state
            .conditional_fields
            .get(&register)
            .and_then(|fields| fields.get(field as usize))
            .copied()
            .unwrap_or(false)
        {
            return Err(self.error(format!(
                "{action} reads conditionally initialized field {field} of r{register}"
            )));
        }
        match &self.state.regs[register as usize] {
            RegState::Partial(bitmap)
                if bitmap.get(field as usize).copied() == Some(false) && self.context.strict =>
            {
                Err(self.error(format!(
                    "{action} reads field {field} of r{register} after it was moved out"
                )))
            }
            _ => Ok(()),
        }
    }

    /// Refine an enum owner on one tag-switch edge. `false` denotes a
    /// statically unreachable edge (for example, a constructed variant sent
    /// to a different case) and keeps it out of ownership joins.
    fn refine_enum_variant(&mut self, register: Register, variant: u32) -> Result<bool, FlowError> {
        let Some(count) = self
            .context
            .enum_variant_count(self.context.register_type(register))
        else {
            return Err(self.error(format!(
                "a tag switch attempts to refine non-enum r{register}"
            )));
        };
        if variant >= count {
            return Ok(false);
        }
        if let Some(active) = self.state.active_variants[register as usize]
            && active != variant
        {
            return Ok(false);
        }
        self.state.active_variants[register as usize] = Some(variant);
        Ok(true)
    }
}

/// Solve the deterministic ownership fixed point for one body.
pub(crate) fn solve(context: &FlowContext<'_>) -> Result<FlowSolution, FlowError> {
    let mut drop_flag_keys = BTreeSet::new();
    for fact in &context.function.flow.drop_flags {
        if fact.owner as usize >= context.function.register_types.len()
            || fact.flag as usize >= context.function.register_types.len()
        {
            return Err(flow_error(
                context.function.entry,
                "drop flag names an out-of-bounds owner or flag register",
            ));
        }
        if !drop_flag_keys.insert((fact.owner, fact.field)) {
            return Err(flow_error(
                context.function.entry,
                format!(
                    "duplicate drop flag for r{} field {:?}",
                    fact.owner, fact.field
                ),
            ));
        }
        let Some(field) = fact.field else {
            continue;
        };
        if context.locals[fact.owner as usize].drop_glue == DropGlueKind::Custom {
            return Err(flow_error(
                context.function.entry,
                format!(
                    "field drop flag targets r{}, whose type has a custom Drop hook",
                    fact.owner
                ),
            ));
        }
        let Some(fields) = context.aggregate_fields(context.register_type(fact.owner), None) else {
            return Err(flow_error(
                context.function.entry,
                format!("field drop flag targets non-aggregate r{}", fact.owner),
            ));
        };
        let Some(field_ty) = fields.get(field as usize) else {
            return Err(flow_error(
                context.function.entry,
                format!(
                    "field drop flag targets out-of-bounds field {field} of r{}",
                    fact.owner
                ),
            ));
        };
        if !context.type_admits_zero_use(*field_ty) {
            return Err(flow_error(
                context.function.entry,
                format!(
                    "field drop flag conditionally disposes field {field} of r{} without Use<[0,0]> evidence",
                    fact.owner
                ),
            ));
        }
    }
    let blocks: BTreeMap<u32, &BasicBlock> = context
        .function
        .blocks
        .iter()
        .map(|block| (block.id, block))
        .collect();
    let mut entries: BTreeMap<u32, OwnState> = BTreeMap::new();
    let mut visits: BTreeMap<u32, u32> = BTreeMap::new();
    let mut cleanup_lists: BTreeMap<u32, Vec<Vec<Register>>> = BTreeMap::new();
    entries.insert(context.function.entry, context.entry_state());
    let mut work = VecDeque::from([context.function.entry]);
    while let Some(id) = work.pop_front() {
        let visit_count = {
            let counter = visits.entry(id).or_insert(0);
            *counter += 1;
            *counter
        };
        if visit_count > 64 {
            return Err(flow_error(
                id,
                "ownership dataflow failed to stabilize; widening limit exceeded",
            ));
        }
        let block = blocks
            .get(&id)
            .ok_or_else(|| flow_error(id, "edge targets a missing block"))?;
        let mut interpreter = Interpreter {
            context,
            block: id,
            statement: 0,
            state: entries[&id].clone(),
        };
        // Block parameters are definitions on the in-edge; the join already
        // applied them, so nothing to do here.
        let mut lists = Vec::with_capacity(block.statements.len() + 1);
        for (index, statement) in block.statements.iter().enumerate() {
            interpreter.statement = index;
            lists.push(interpreter.state.cleanup_list());
            interpreter.statement(&statement.kind)?;
        }
        interpreter.statement = block.statements.len();
        lists.push(interpreter.state.cleanup_list());
        cleanup_lists.insert(id, lists);
        let successors = terminator_transfer(context, &mut interpreter, block)?;
        for (target, state) in successors {
            let target_block = blocks
                .get(&target)
                .ok_or_else(|| flow_error(id, "edge targets a missing block"))?;
            let widen = visits.get(&target).copied().unwrap_or(0) >= 2;
            match entries.get_mut(&target) {
                None => {
                    entries.insert(target, state);
                    work.push_back(target);
                }
                Some(existing) => {
                    let joined = join_states(context, target_block.id, existing, &state)?;
                    let mut joined = match joined {
                        Some(joined) => joined,
                        None => continue,
                    };
                    if widen {
                        for (old, new) in existing.uses.iter().zip(&mut joined.uses) {
                            if new.upper != old.upper {
                                new.upper = None;
                            }
                        }
                        for (old, new) in
                            existing.quantity_uses.iter().zip(&mut joined.quantity_uses)
                        {
                            if new.upper != old.upper {
                                new.upper = None;
                            }
                        }
                    }
                    if joined != *existing {
                        *existing = joined;
                        if !work.contains(&target) {
                            work.push_back(target);
                        }
                    }
                }
            }
        }
    }
    Ok(FlowSolution {
        entries,
        cleanup_lists,
    })
}

/// Apply one edge: evaluate arguments left to right, then define target
/// parameters. A moved argument's register age transfers to the parameter,
/// mirroring the bytecode edge-transfer `MOVE`s the verifier will see.
fn apply_edge(
    interpreter: &mut Interpreter<'_>,
    edge: &Edge,
    params: &[crate::compiler_mir::BlockParam],
    implicit: Option<Register>,
) -> Result<OwnState, FlowError> {
    let skip = usize::from(implicit.is_some());
    if let Some(result) = implicit {
        interpreter.define(result, "terminator result")?;
    }
    let original_count = interpreter.state.regs.len();
    let mut temporaries = vec![0; edge.args.len()];

    // A consuming edge argument is an SSA rename into the target block
    // parameter, not a source-level move out of the active label scope.
    // Preserve the logical outer owner across that phi. Copy arguments create
    // an alias and deliberately leave the original baseline identity intact.
    for (parameter, argument) in params.iter().skip(skip).zip(&edge.args) {
        if argument.mode != UseMode::Move {
            continue;
        }
        for label in &mut interpreter.state.labels {
            for owner in &mut label.owners {
                if *owner == argument.register {
                    *owner = parameter.register;
                }
            }
        }
    }

    // Bytecode snapshots every edge argument before it writes any target
    // parameter. Model those physical temporaries here as well; applying the
    // renames sequentially loses values for swaps and longer cycles.
    for mode in [UseMode::Copy, UseMode::Move] {
        for (index, argument) in edge.args.iter().enumerate() {
            if argument.mode != mode {
                continue;
            }
            let temporary = interpreter.state.regs.len() as Register;
            temporaries[index] = temporary;
            interpreter.state.regs.push(RegState::Undefined);
            interpreter.state.constants.push(None);
            interpreter.state.active_variants.push(None);
            interpreter.state.enum_tag_sources.push(None);
            interpreter.state.shell_ages.push(None);
            interpreter.state.uses.push(UseCount::ZERO);
            interpreter.state.quantity_groups.push(None);
            interpreter.state.quantity_uses.push(UseCount::ZERO);

            match mode {
                UseMode::Move => {
                    // Snapshotting a move is a pure rename and therefore does
                    // not count as an ownership use.
                    interpreter.statement(&InstructionKind::Move {
                        dst: temporary,
                        src: *argument,
                    })?;
                }
                UseMode::Copy => {
                    let source = argument.register as usize;
                    let tag_source = interpreter.state.enum_tag_sources[source];
                    let active_variant = interpreter.state.active_variants[source];
                    let constant = interpreter.state.constants[source];
                    let quantity_group = interpreter.state.quantity_groups[source];
                    let aggregate_origins = interpreter
                        .state
                        .aggregate_reference_origins
                        .get(&argument.register)
                        .cloned();
                    interpreter.operand(argument, "edge argument")?;
                    interpreter.state.regs[temporary as usize] = RegState::Live;
                    interpreter.state.order.push(temporary);
                    interpreter.state.constants[temporary as usize] = constant;
                    interpreter.state.active_variants[temporary as usize] = active_variant;
                    interpreter.state.enum_tag_sources[temporary as usize] = tag_source;
                    interpreter.state.quantity_groups[temporary as usize] = quantity_group;
                    if let Some(origins) = aggregate_origins {
                        interpreter
                            .state
                            .aggregate_reference_origins
                            .insert(temporary, origins);
                    }
                    let ty = interpreter.context.register_type(argument.register);
                    if matches!(interpreter.context.representation(ty), Type::Array { .. }) {
                        interpreter.state.array_slots.insert(
                            temporary,
                            ArraySlotState {
                                length: None,
                                empty: BTreeSet::new(),
                                dynamic_hole: false,
                                reference_origins: BTreeMap::new(),
                            },
                        );
                    }
                    if interpreter.context.is_reference(ty) {
                        interpreter.state.loans.insert(
                            temporary,
                            LiveLoan {
                                id: u32::MAX,
                                unique: interpreter.context.is_unique_reference(ty),
                                external: true,
                                borrowed: Place::local(temporary),
                                parent: None,
                                suspended: 0,
                            },
                        );
                    }
                }
            }
        }
    }
    for (parameter, temporary) in params.iter().skip(skip).zip(temporaries) {
        interpreter.statement(&InstructionKind::Move {
            dst: parameter.register,
            src: Operand {
                register: temporary,
                mode: UseMode::Move,
            },
        })?;
    }

    let temporary_end = interpreter.state.regs.len();
    debug_assert!(
        interpreter
            .state
            .order
            .iter()
            .all(|register| (*register as usize) < original_count)
    );
    for temporary in original_count as Register..temporary_end as Register {
        interpreter.state.conditional_fields.remove(&temporary);
        interpreter.state.array_slots.remove(&temporary);
        interpreter
            .state
            .aggregate_reference_origins
            .remove(&temporary);
        interpreter.state.loans.remove(&temporary);
        interpreter.state.holes.remove(&temporary);
    }
    interpreter.state.regs.truncate(original_count);
    interpreter.state.constants.truncate(original_count);
    interpreter.state.active_variants.truncate(original_count);
    interpreter.state.enum_tag_sources.truncate(original_count);
    interpreter.state.shell_ages.truncate(original_count);
    interpreter.state.uses.truncate(original_count);
    interpreter.state.quantity_groups.truncate(original_count);
    interpreter.state.quantity_uses.truncate(original_count);
    Ok(interpreter.state.clone())
}

fn terminator_transfer(
    context: &FlowContext<'_>,
    interpreter: &mut Interpreter<'_>,
    block: &BasicBlock,
) -> Result<Vec<(u32, OwnState)>, FlowError> {
    let blocks: BTreeMap<u32, &BasicBlock> = context
        .function
        .blocks
        .iter()
        .map(|candidate| (candidate.id, candidate))
        .collect();
    let params_of = |target: u32| {
        blocks
            .get(&target)
            .map(|block| block.params.as_slice())
            .unwrap_or(&[])
    };
    let base = interpreter.state.clone();
    let mut successors = Vec::new();
    match &block.terminator {
        Terminator::Goto(edge) => {
            let state = apply_edge(interpreter, edge, params_of(edge.target), None)?;
            successors.push((edge.target, state));
        }
        Terminator::Switch {
            discr,
            cases,
            otherwise,
        } => {
            interpreter.expect_live(discr.register, "Switch")?;
            let after = interpreter.state.clone();
            let enum_source = after.enum_tag_sources[discr.register as usize];
            for (constant, edge) in cases {
                interpreter.state = after.clone();
                if let Some(source) = enum_source
                    && let grandiose_vm::Constant::U32(variant) = constant
                    && !interpreter.refine_enum_variant(source, *variant)?
                {
                    if context.refine_enum_switches {
                        continue;
                    }
                    // Serialization must retain every encoded arm. Force its
                    // structural tag proof after restoring the physical
                    // state: retaining a contradictory proof can poison a
                    // later fixed-point join before this switch is revisited
                    // with its converged entry state.
                    interpreter.state = after.clone();
                    if context
                        .enum_variant_count(context.register_type(source))
                        .is_some_and(|count| *variant < count)
                    {
                        interpreter.state.active_variants[source as usize] = Some(*variant);
                    }
                }
                let state = apply_edge(interpreter, edge, params_of(edge.target), None)?;
                successors.push((edge.target, state));
            }
            interpreter.state = after.clone();
            let remaining_variant = enum_source.and_then(|source| {
                let count = context.enum_variant_count(context.register_type(source))?;
                let excluded = cases
                    .iter()
                    .filter_map(|(constant, _)| match constant {
                        grandiose_vm::Constant::U32(variant) if *variant < count => Some(*variant),
                        _ => None,
                    })
                    .collect::<BTreeSet<_>>();
                (excluded.len() + 1 == count as usize)
                    .then(|| (0..count).find(|variant| !excluded.contains(variant)))
                    .flatten()
            });
            if let (Some(source), Some(variant)) = (enum_source, remaining_variant)
                && !interpreter.refine_enum_variant(source, variant)?
            {
                if context.refine_enum_switches {
                    interpreter.state = base;
                    return Ok(successors);
                }
                interpreter.state = after.clone();
                interpreter.state.active_variants[source as usize] = Some(variant);
            }
            let state = apply_edge(interpreter, otherwise, params_of(otherwise.target), None)?;
            successors.push((otherwise.target, state));
        }
        Terminator::Return { value } => {
            if let Some(value) = value {
                interpreter.operand(value, "Return")?;
            }
            check_exit_clean(context, interpreter, "return")?;
        }
        Terminator::Call {
            result,
            function,
            args,
            normal,
        } => {
            let array_result = interpreter.apply_array_call(*function, args)?;
            for argument in args {
                interpreter.operand(argument, "Call argument")?;
            }
            let mut state = apply_edge(interpreter, normal, params_of(normal.target), *result)?;
            if let (Some(result), Some(slots)) = (result, array_result) {
                state.array_slots.insert(*result, slots);
            }
            successors.push((normal.target, state));
        }
        Terminator::CallSelf {
            result,
            args,
            normal,
        }
        | Terminator::HostCall {
            result,
            args,
            normal,
            ..
        } => {
            for argument in args {
                interpreter.operand(argument, "Call argument")?;
            }
            let state = apply_edge(interpreter, normal, params_of(normal.target), *result)?;
            successors.push((normal.target, state));
        }
        Terminator::CallKnownReceiver {
            result,
            receiver,
            args,
            normal,
            ..
        } => {
            interpreter.expect_live(receiver.register, "CallKnownReceiver receiver")?;
            for argument in args {
                interpreter.operand(argument, "CallKnownReceiver argument")?;
            }
            let state = apply_edge(interpreter, normal, params_of(normal.target), *result)?;
            successors.push((normal.target, state));
        }
        Terminator::CallIndirect {
            result,
            callable,
            receiver_mode,
            args,
            normal,
            ..
        } => {
            if *receiver_mode == 2 || callable.mode == UseMode::Move {
                interpreter.operand(
                    &Operand {
                        register: callable.register,
                        mode: UseMode::Move,
                    },
                    "CallIndirect receiver",
                )?;
            } else {
                interpreter.expect_live(callable.register, "CallIndirect receiver")?;
                // A borrowed receiver creates a fresh, synchronous view of
                // every reference leaf in its sealed environment. Unique
                // leaves require exclusive access for this call; retaining
                // the exact captured place makes the check independent of
                // register allocation and catches a still-live result from a
                // preceding call.
                if *receiver_mode == 1
                    && let Some(origins) = interpreter
                        .state
                        .aggregate_reference_origins
                        .get(&callable.register)
                {
                    for origin in origins.values().filter(|origin| origin.unique) {
                        if interpreter.state.loans.iter().any(|(reference, loan)| {
                            Some(*reference) != origin.parent
                                && loan.borrowed.overlaps(&origin.borrowed)
                                && (origin.unique || loan.unique)
                        }) {
                            return Err(interpreter.error(format!(
                                "CallIndirect unique receiver r{} overlaps a live reference into its captured environment",
                                callable.register
                            )));
                        }
                    }
                }
            }
            for argument in args {
                interpreter.operand(argument, "CallIndirect argument")?;
            }
            if context.strict
                && context
                    .function
                    .flow
                    .indirect_calls
                    .iter()
                    .any(|site| site.block == interpreter.block)
            {
                let site = context
                    .function
                    .flow
                    .indirect_calls
                    .iter()
                    .find(|site| site.block == interpreter.block)
                    .expect("site existence checked above");
                let mut live = interpreter.state.order.clone();
                if let Some(result) = result {
                    live.retain(|register| register != result);
                }
                live.sort_unstable();
                if site
                    .capture
                    .captured_owners
                    .iter()
                    .any(|r| !live.contains(r))
                    || live.iter().any(|r| {
                        !site.capture.captured_owners.contains(r) && !context.admits_zero_use(*r)
                    })
                {
                    return Err(interpreter.error(format!(
                        "CallIndirect captured owners {:?} do not soundly account for live owners {live:?}",
                        site.capture.captured_owners
                    )));
                }
                let references = site
                    .capture
                    .captured_owners
                    .iter()
                    .copied()
                    .filter(|register| interpreter.state.loans.contains_key(register))
                    .collect::<Vec<_>>();
                if site.capture.captured_references != references {
                    return Err(interpreter.error(format!(
                        "CallIndirect captured references {:?} do not match live loans {references:?}",
                        site.capture.captured_references
                    )));
                }
                let residuals = site
                    .capture
                    .captured_owners
                    .iter()
                    .filter_map(
                        |register| match &interpreter.state.regs[*register as usize] {
                            RegState::Partial(initialized_fields) => {
                                Some((*register, initialized_fields))
                            }
                            _ => None,
                        },
                    )
                    .collect::<Vec<_>>();
                if residuals.len() != site.capture.captured_residuals.len()
                    || residuals.iter().zip(&site.capture.captured_residuals).any(
                        |((register, fields), recorded)| {
                            *register != recorded.register
                                || *fields != &recorded.initialized_fields
                        },
                    )
                {
                    return Err(interpreter.error(
                        "CallIndirect residual capture does not match exact partial-owner state",
                    ));
                }
                let cancellation_safe = site.capture.captured_owners.iter().all(|register| {
                    match &interpreter.state.regs[*register as usize] {
                        RegState::Partial(initialized) => {
                            let ty = context.register_type(*register);
                            let variant = interpreter.state.active_variants[*register as usize];
                            context.aggregate_fields(ty, variant).is_some_and(|fields| {
                                fields
                                    .iter()
                                    .zip(initialized)
                                    .all(|(field_ty, initialized)| {
                                        !*initialized || context.type_admits_zero_use(*field_ty)
                                    })
                            })
                        }
                        RegState::Live | RegState::MaybeLive => context.admits_zero_use(*register),
                        RegState::Undefined | RegState::Consumed => false,
                    }
                });
                if site.capture.cancellation_safe != cancellation_safe {
                    return Err(interpreter.error(format!(
                        "CallIndirect cancellation-safety fact is {}, but exact cleanup safety is {cancellation_safe}",
                        site.capture.cancellation_safe
                    )));
                }
            }
            let state = apply_edge(interpreter, normal, params_of(normal.target), *result)?;
            successors.push((normal.target, state));
        }
        Terminator::Handle {
            result,
            handler,
            body,
            normal,
        } => {
            interpreter.operand(handler, "Handle handler")?;
            interpreter.operand(body, "Handle body")?;
            let state = apply_edge(interpreter, normal, params_of(normal.target), Some(*result))?;
            successors.push((normal.target, state));
        }
        Terminator::Perform {
            result,
            payloads,
            capture,
            resume,
            ..
        } => {
            for payload in payloads {
                interpreter.operand(payload, "Perform payload")?;
            }
            if context.strict {
                let canonical =
                    |registers: &[Register]| registers.windows(2).all(|pair| pair[0] < pair[1]);
                if !canonical(&capture.captured_owners)
                    || !canonical(&capture.captured_references)
                    || !capture
                        .captured_residuals
                        .windows(2)
                        .all(|pair| pair[0].register < pair[1].register)
                {
                    return Err(interpreter.error(
                        "Perform continuation capture sets must be strictly sorted and duplicate-free",
                    ));
                }
                if capture
                    .captured_references
                    .iter()
                    .any(|reference| !capture.captured_owners.contains(reference))
                {
                    return Err(interpreter
                        .error("Perform captured references must be a subset of captured owners"));
                }
                let mut live = interpreter.state.order.clone();
                live.sort_unstable();
                for register in &capture.captured_owners {
                    if !live.contains(register) {
                        return Err(interpreter.error(format!(
                            "Perform captures r{register}, which is not live at the suspension point"
                        )));
                    }
                }
                // Live registers outside the capture accounting must be
                // trivially discardable: no accounting means cancellation
                // destroys them with zero-use evidence only.
                for register in &live {
                    if !capture.captured_owners.contains(register)
                        && !context.admits_zero_use(*register)
                    {
                        return Err(interpreter.error(format!(
                            "r{register} is live across a perform but absent from its \
                             continuation capture accounting"
                        )));
                    }
                }
                // Every reference the capture accounting names must hold a
                // live loan, and every locally issued live loan must be
                // named. Caller-provided references are caller-managed and
                // may be listed or omitted.
                for register in &capture.captured_references {
                    if !interpreter.state.loans.contains_key(register) {
                        return Err(interpreter.error(format!(
                            "Perform captures reference r{register}, which holds no live loan"
                        )));
                    }
                }
                for (register, loan) in &interpreter.state.loans {
                    if !loan.external && !capture.captured_references.contains(register) {
                        return Err(interpreter.error(format!(
                            "the live loan held by r{register} crosses a perform without \
                             capture accounting"
                        )));
                    }
                }
                for residual in &capture.captured_residuals {
                    let RegState::Partial(bitmap) =
                        &interpreter.state.regs[residual.register as usize]
                    else {
                        return Err(interpreter.error(format!(
                            "Perform records residual fields for r{}, which is not partially initialized",
                            residual.register
                        )));
                    };
                    if bitmap != &residual.initialized_fields {
                        return Err(interpreter.error(format!(
                            "Perform residual field state for r{} does not match the tracked shell",
                            residual.register
                        )));
                    }
                }
                let expected_residuals = capture
                    .captured_owners
                    .iter()
                    .filter(|register| {
                        matches!(
                            interpreter.state.regs[**register as usize],
                            RegState::Partial(_)
                        )
                    })
                    .copied()
                    .collect::<Vec<_>>();
                let recorded_residuals = capture
                    .captured_residuals
                    .iter()
                    .map(|residual| residual.register)
                    .collect::<Vec<_>>();
                if recorded_residuals != expected_residuals {
                    return Err(interpreter.error(format!(
                        "Perform residual captures {recorded_residuals:?} do not exactly describe captured partial owners {expected_residuals:?}"
                    )));
                }
                let cancellation_safe = capture.captured_owners.iter().all(|register| {
                    match &interpreter.state.regs[*register as usize] {
                        RegState::Partial(initialized) => {
                            let ty = context.register_type(*register);
                            let variant = interpreter.state.active_variants[*register as usize];
                            context.aggregate_fields(ty, variant).is_some_and(|fields| {
                                fields
                                    .iter()
                                    .zip(initialized)
                                    .all(|(field_ty, initialized)| {
                                        !*initialized || context.type_admits_zero_use(*field_ty)
                                    })
                            })
                        }
                        RegState::Live | RegState::MaybeLive => context.admits_zero_use(*register),
                        RegState::Undefined | RegState::Consumed => false,
                    }
                });
                if capture.cancellation_safe != cancellation_safe {
                    return Err(interpreter.error(format!(
                        "Perform cancellation-safety fact is {}, but exact captured-owner cleanup is {cancellation_safe}",
                        capture.cancellation_safe
                    )));
                }
            }
            if let Some(edge) = resume {
                let state = apply_edge(interpreter, edge, params_of(edge.target), *result)?;
                successors.push((edge.target, state));
            }
        }
        Terminator::Resume {
            result,
            resumption,
            value,
            normal,
            ..
        } => {
            interpreter.operand(resumption, "Resume resumption")?;
            interpreter.operand(value, "Resume value")?;
            let state = apply_edge(interpreter, normal, params_of(normal.target), Some(*result))?;
            successors.push((normal.target, state));
        }
        Terminator::TailResume {
            resumption, value, ..
        } => {
            interpreter.operand(resumption, "TailResume resumption")?;
            interpreter.operand(value, "TailResume value")?;
            check_exit_clean(context, interpreter, "tail resume")?;
        }
        Terminator::Cancel {
            result,
            resumption,
            normal,
            ..
        } => {
            interpreter.operand(resumption, "Cancel resumption")?;
            let state = apply_edge(interpreter, normal, params_of(normal.target), Some(*result))?;
            successors.push((normal.target, state));
        }
        Terminator::TailCall { function, args } => {
            interpreter.apply_array_call(*function, args)?;
            for argument in args {
                interpreter.operand(argument, "TailCall argument")?;
            }
            check_exit_clean(context, interpreter, "tail call")?;
        }
        Terminator::TailCallSelf { args } => {
            interpreter.operand(
                &Operand {
                    register: 0,
                    mode: UseMode::Move,
                },
                "TailCallSelf receiver",
            )?;
            for argument in args {
                interpreter.operand(argument, "TailCallSelf argument")?;
            }
            check_exit_clean(context, interpreter, "tail self call")?;
        }
        Terminator::TailCallKnownReceiver { receiver, args, .. } => {
            interpreter.expect_live(receiver.register, "TailCallKnownReceiver receiver")?;
            for argument in args {
                interpreter.operand(argument, "TailCallKnownReceiver argument")?;
            }
            check_exit_clean(context, interpreter, "tail known-receiver call")?;
        }
        Terminator::TailCallIndirect { callable, args, .. } => {
            interpreter.operand(callable, "TailCallIndirect receiver")?;
            for argument in args {
                interpreter.operand(argument, "TailCallIndirect argument")?;
            }
            check_exit_clean(context, interpreter, "tail call")?;
        }
        Terminator::Leave { label, target } => {
            let Some(label_index) = interpreter
                .state
                .labels
                .iter()
                .rposition(|entry| entry.label == *label)
            else {
                return Err(
                    interpreter.error(format!("Leave targets inactive label slot {}", label.0))
                );
            };
            let outer_owners = interpreter.state.labels[label_index]
                .owners
                .iter()
                .copied()
                .collect::<BTreeSet<_>>();
            let params = params_of(target.target);
            // Move the protected result first, matching the VM's atomic
            // `take(value); cleanup-prefix; put(result)` ordering.
            interpreter.state = apply_edge(interpreter, target, params, None)?;
            let protected = params
                .iter()
                .map(|parameter| parameter.register)
                .collect::<BTreeSet<_>>();
            let abandoned = interpreter
                .state
                .order
                .iter()
                .rev()
                .copied()
                .filter(|register| {
                    !outer_owners.contains(register) && !protected.contains(register)
                })
                .collect::<Vec<_>>();
            for register in abandoned {
                if context.is_reference(context.register_type(register)) {
                    interpreter.statement(&InstructionKind::EndBorrow {
                        reference: register,
                    })?;
                } else if interpreter.replaceable_unrestricted(register) {
                    // Plain copy/ZST values have no runtime cleanup. Retire
                    // the analysis slot without synthesizing a Drop action;
                    // custom-drop copies are deliberately excluded.
                    interpreter.consume(register, "Leave cleanup")?;
                } else {
                    interpreter.statement(&InstructionKind::Drop {
                        owner: Operand {
                            register,
                            mode: UseMode::Move,
                        },
                    })?;
                }
            }
            // Leaving a destination also abandons every nested destination.
            interpreter.state.labels.truncate(label_index);
            successors.push((target.target, interpreter.state.clone()));
        }
        // Abort deliberately performs no ordinary cleanup and has no
        // successor, matching the VM's immediate-termination contract.
        Terminator::Abort { .. } | Terminator::Unreachable => {}
    }
    interpreter.state = base;
    Ok(successors)
}

/// Re-interpret one block from its solved entry state, returning the state
/// before each statement plus the state before the terminator. Used by
/// cleanup elaboration to classify trailing destruction sequences.
pub(crate) fn block_states(
    context: &FlowContext<'_>,
    block: &BasicBlock,
    entry: &OwnState,
) -> Result<Vec<OwnState>, FlowError> {
    let mut interpreter = Interpreter {
        context,
        block: block.id,
        statement: 0,
        state: entry.clone(),
    };
    let mut states = Vec::with_capacity(block.statements.len() + 1);
    for (index, statement) in block.statements.iter().enumerate() {
        interpreter.statement = index;
        states.push(interpreter.state.clone());
        interpreter.statement(&statement.kind)?;
    }
    states.push(interpreter.state.clone());
    Ok(states)
}

/// Every normal exit must have transferred, deconstructed, or zero-legally
/// destroyed its owners. Registers still live at the exit are destroyed by
/// frame teardown, which is legal only with `Use<[0,0]>` evidence for every
/// initialized remainder; moved values are protected by having been consumed.
fn check_exit_clean(
    context: &FlowContext<'_>,
    interpreter: &Interpreter<'_>,
    exit: &str,
) -> Result<(), FlowError> {
    if !context.strict {
        return Ok(());
    }
    for &register in &interpreter.state.order {
        match &interpreter.state.regs[register as usize] {
            RegState::Partial(bitmap) => {
                let ty = context.register_type(register);
                let variant = interpreter.state.active_variants[register as usize];
                if let Some(fields) = context.aggregate_fields(ty, variant) {
                    for (field, (field_ty, initialized)) in fields.iter().zip(bitmap).enumerate() {
                        let conditional = interpreter
                            .state
                            .conditional_fields
                            .get(&register)
                            .and_then(|fields| fields.get(field))
                            .copied()
                            .unwrap_or(false);
                        if conditional && !context.has_field_drop_flag(register, field as u32) {
                            return Err(interpreter.error(format!(
                                "field {field} of r{register} is conditionally initialized at {exit} without a governing field drop flag"
                            )));
                        }
                        if *initialized && !context.type_admits_zero_use(*field_ty) {
                            return Err(interpreter.error(format!(
                                "field {field} of r{register} is still initialized at {exit} \
                                 without Use<[0,0]> evidence for its disposal"
                            )));
                        }
                    }
                }
            }
            _ => {
                if !context.admits_zero_use(register) {
                    return Err(interpreter.error(format!(
                        "r{register} is still live at {exit}; every owner must be transferred, \
                         deconstructed, or destroyed with Use<[0,0]> evidence before the frame exits"
                    )));
                }
            }
        }
    }
    Ok(())
}

/// Join two block-entry states. `Ok(None)` means the incoming state is
/// already covered. A live/dead initialization conflict is legal only when a
/// drop flag governs the owner; the join then records `MaybeLive`.
fn join_states(
    context: &FlowContext<'_>,
    block: u32,
    existing: &OwnState,
    incoming: &OwnState,
) -> Result<Option<OwnState>, FlowError> {
    if existing.labels.len() != incoming.labels.len() {
        return Err(flow_error(
            block,
            "block join combines differently nested active label stacks",
        ));
    }
    let mut joined_labels = Vec::with_capacity(existing.labels.len());
    for (left, right) in existing.labels.iter().zip(&incoming.labels) {
        if left.label != right.label {
            return Err(flow_error(
                block,
                "block join combines incompatible active label baselines",
            ));
        }
        let left_set = left.owners.iter().copied().collect::<BTreeSet<_>>();
        let right_set = right.owners.iter().copied().collect::<BTreeSet<_>>();
        let left_common = left
            .owners
            .iter()
            .filter(|owner| right_set.contains(owner))
            .copied()
            .collect::<Vec<_>>();
        let right_common = right
            .owners
            .iter()
            .filter(|owner| left_set.contains(owner))
            .copied()
            .collect::<Vec<_>>();
        if left_common != right_common {
            return Err(flow_error(
                block,
                "block join reorders active label-baseline owners",
            ));
        }
        joined_labels.push(LabelBaseline {
            label: left.label,
            // Label membership is a must-property: only an owner classified
            // as outer on every continuing path may survive a future Leave.
            // Ordinary register-state joining independently rejects an unsafe
            // live/dead mismatch for restricted values, so this metadata meet
            // does not weaken linear or custom-drop checking.
            owners: left_common,
        });
    }
    if existing.agrees_with(incoming) {
        let mut joined = existing.clone();
        joined.labels = joined_labels;
        let mut changed = false;
        for register in 0..joined.regs.len() {
            if joined.active_variants[register] != incoming.active_variants[register] {
                if context.strict && matches!(joined.regs[register], RegState::Partial(_)) {
                    return Err(flow_error(
                        block,
                        format!(
                            "block join combines variant-relative partial shells for r{register} with different active variants"
                        ),
                    ));
                }
                joined.active_variants[register] = None;
                changed = true;
            }
            if joined.enum_tag_sources[register] != incoming.enum_tag_sources[register] {
                joined.enum_tag_sources[register] = None;
                changed = true;
            }
        }
        for (slot, incoming_uses) in joined.uses.iter_mut().zip(&incoming.uses) {
            let hull = slot.hull(*incoming_uses);
            if hull != *slot {
                *slot = hull;
                changed = true;
            }
        }
        for (slot, incoming_uses) in joined.quantity_uses.iter_mut().zip(&incoming.quantity_uses) {
            let hull = slot.hull(*incoming_uses);
            if hull != *slot {
                *slot = hull;
                changed = true;
            }
        }
        for (slot, incoming_age) in joined.shell_ages.iter_mut().zip(&incoming.shell_ages) {
            if slot.is_some() && slot != incoming_age {
                *slot = None;
                changed = true;
            }
        }
        return Ok(changed.then_some(joined));
    }
    // Initialization conflict: allowed only through drop flags in strict
    // mode; the synthesized-fact bridge merges deterministically instead.
    let mut joined = existing.clone();
    joined.labels = joined_labels;
    for register in 0..existing.regs.len() as Register {
        let left = existing.regs[register as usize].normalized().clone();
        let right = incoming.regs[register as usize].normalized().clone();
        if left == right {
            if let Some(incoming_fields) = incoming.conditional_fields.get(&register) {
                let fields = joined
                    .conditional_fields
                    .entry(register)
                    .or_insert_with(|| vec![false; incoming_fields.len()]);
                for (field, incoming) in fields.iter_mut().zip(incoming_fields) {
                    *field |= *incoming;
                }
            }
            continue;
        }
        let partial_pair = match (&left, &right) {
            (RegState::Partial(left), RegState::Partial(right)) => {
                Some((left.clone(), right.clone()))
            }
            (RegState::Live, RegState::Partial(right)) => context
                .aggregate_fields(
                    context.register_type(register),
                    existing.active_variants[register as usize],
                )
                .map(|fields| (vec![true; fields.len()], right.clone())),
            (RegState::Partial(left), RegState::Live) => context
                .aggregate_fields(
                    context.register_type(register),
                    incoming.active_variants[register as usize],
                )
                .map(|fields| (left.clone(), vec![true; fields.len()])),
            _ => None,
        };
        if let Some((left_fields, right_fields)) = partial_pair {
            if left_fields.len() != right_fields.len() {
                return Err(flow_error(
                    block,
                    format!("block join combines differently shaped partial owners in r{register}"),
                ));
            }
            if context.strict && context.locals[register as usize].drop_glue == DropGlueKind::Custom
            {
                return Err(flow_error(
                    block,
                    format!(
                        "block join conditionally moves fields of r{register}, whose type has a custom Drop hook"
                    ),
                ));
            }
            let mut conditional = joined
                .conditional_fields
                .get(&register)
                .cloned()
                .unwrap_or_else(|| vec![false; left_fields.len()]);
            if let Some(incoming_conditional) = incoming.conditional_fields.get(&register) {
                for (slot, incoming) in conditional.iter_mut().zip(incoming_conditional) {
                    *slot |= *incoming;
                }
            }
            let mut initialized = Vec::with_capacity(left_fields.len());
            let field_types = context
                .aggregate_fields(
                    context.register_type(register),
                    existing.active_variants[register as usize]
                        .or(incoming.active_variants[register as usize]),
                )
                .ok_or_else(|| {
                    flow_error(
                        block,
                        format!(
                            "block join cannot identify the active aggregate layout of r{register}"
                        ),
                    )
                })?;
            for (field, (left_initialized, right_initialized)) in
                left_fields.iter().zip(&right_fields).enumerate()
            {
                if left_initialized != right_initialized {
                    if context.strict && !context.has_field_drop_flag(register, field as u32) {
                        return Err(flow_error(
                            block,
                            format!(
                                "block join conditionally initializes field {field} of r{register} without a governing field drop flag"
                            ),
                        ));
                    }
                    if context.strict
                        && field_types
                            .get(field)
                            .is_some_and(|ty| !context.type_admits_zero_use(*ty))
                    {
                        return Err(flow_error(
                            block,
                            format!(
                                "block join conditionally moves positive-Use field {field} of r{register}; restricted ownership post-states must agree"
                            ),
                        ));
                    }
                    conditional[field] = true;
                }
                initialized.push(*left_initialized || *right_initialized);
            }
            joined.regs[register as usize] = RegState::Partial(initialized);
            if conditional.iter().any(|field| *field) {
                joined.conditional_fields.insert(register, conditional);
            }
            continue;
        }
        let discard_conditional_value = context.strict
            && matches!(
                context.locals[register as usize].ownership,
                OwnershipCategory::SharedRef
                    | OwnershipCategory::CopyValue
                    | OwnershipCategory::ZstErased
            )
            && matches!(
                (&left, &right),
                (RegState::Live, RegState::Consumed)
                    | (RegState::Consumed, RegState::Live)
                    | (RegState::MaybeLive, RegState::Consumed)
                    | (RegState::Consumed, RegState::MaybeLive)
                    | (RegState::MaybeLive, RegState::Live)
                    | (RegState::Live, RegState::MaybeLive)
            );
        if context.strict {
            let flagged = context.has_drop_flag(register);
            let ownership = context.locals[register as usize].ownership;
            let ownership_is_unrestricted = matches!(
                ownership,
                OwnershipCategory::SharedRef
                    | OwnershipCategory::CopyValue
                    | OwnershipCategory::ZstErased
            );
            let conditional = matches!(
                (&left, &right),
                (RegState::Live, RegState::Consumed)
                    | (RegState::Consumed, RegState::Live)
                    | (RegState::MaybeLive, RegState::Consumed)
                    | (RegState::Consumed, RegState::MaybeLive)
                    | (RegState::MaybeLive, RegState::Live)
                    | (RegState::Live, RegState::MaybeLive)
            );
            if (!flagged && !ownership_is_unrestricted) || !conditional {
                return Err(flow_error(
                    block,
                    format!(
                        "block join has conflicting initialization states for r{register} \
                         ({left:?} vs {right:?}) and no drop flag governs it"
                    ),
                ));
            }
        }
        joined.regs[register as usize] = if discard_conditional_value {
            // An unrestricted SSA temporary which exists on only one
            // predecessor cannot be observed after the join. End it (and any
            // reference loan) at the edge; a later use is correctly rejected
            // as use-after-consume, while no runtime presence flag is needed.
            RegState::Consumed
        } else {
            match (&left, &right) {
                (RegState::Partial(bitmap), _) | (_, RegState::Partial(bitmap)) => {
                    RegState::Partial(bitmap.clone())
                }
                _ => RegState::MaybeLive,
            }
        };
        if !joined.regs[register as usize].is_live() {
            joined.order.retain(|live| *live != register);
        } else if !joined.order.contains(&register) {
            if let Some(position) = incoming.order.iter().position(|live| *live == register) {
                let at = position.min(joined.order.len());
                joined.order.insert(at, register);
            } else {
                joined.order.push(register);
            }
        }
    }
    if joined.order != incoming.order {
        let order_is_observable = |register: &&Register| {
            !matches!(joined.regs[**register as usize], RegState::MaybeLive)
                && !matches!(
                    context.locals[**register as usize].ownership,
                    OwnershipCategory::SharedRef
                        | OwnershipCategory::CopyValue
                        | OwnershipCategory::ZstErased
                )
        };
        let strict_conflict = joined
            .order
            .iter()
            .filter(order_is_observable)
            .ne(incoming.order.iter().filter(order_is_observable));
        if context.strict && strict_conflict {
            return Err(flow_error(
                block,
                "block join has conflicting owner cleanup orders",
            ));
        }
        for register in &incoming.order {
            if !joined.order.contains(register) && joined.regs[*register as usize].is_live() {
                joined.order.push(*register);
            }
        }
    }
    // Loan entries attached to references that are already dead on their
    // predecessor do not cross the edge.  Scratch borrows commonly end on
    // only one arm of a pattern test whose other arm does not return; keeping
    // those dead entries makes otherwise identical continuing states appear
    // incompatible at the join.
    let joined_live = joined
        .regs
        .iter()
        .map(|state| matches!(state, RegState::Live | RegState::Partial(_)))
        .collect::<Vec<_>>();
    let retain_live_loans = |loans: &mut BTreeMap<Register, LiveLoan>, live: &[bool]| {
        let removed_parents = loans
            .iter()
            .filter(|(reference, _)| !live[**reference as usize])
            .filter_map(|(_, loan)| loan.parent)
            .collect::<Vec<_>>();
        loans.retain(|reference, _| live[*reference as usize]);
        for parent in removed_parents {
            if let Some(loan) = loans.get_mut(&parent) {
                loan.suspended = loan.suspended.saturating_sub(1);
            }
        }
    };
    retain_live_loans(&mut joined.loans, &joined_live);
    for (reference, loan) in &mut joined.loans {
        if loan.external && loan.id == u32::MAX && loan.parent.is_none() {
            loan.borrowed = Place::local(*reference);
        }
    }
    let incoming_live = incoming
        .regs
        .iter()
        .zip(&joined.regs)
        .map(|(incoming, joined)| {
            incoming.is_live() && matches!(joined, RegState::Live | RegState::Partial(_))
        })
        .collect::<Vec<_>>();
    let mut incoming_loans = incoming.loans.clone();
    retain_live_loans(&mut incoming_loans, &incoming_live);
    for (reference, loan) in &mut incoming_loans {
        if loan.external && loan.id == u32::MAX && loan.parent.is_none() {
            loan.borrowed = Place::local(*reference);
        }
    }
    if joined.loans != incoming_loans {
        if context.strict {
            return Err(flow_error(
                block,
                format!(
                    "block join has conflicting live loan sets ({:?} vs {:?})",
                    joined.loans, incoming_loans
                ),
            ));
        }
        for (reference, loan) in &incoming_loans {
            joined
                .loans
                .entry(*reference)
                .or_insert_with(|| loan.clone());
        }
        let live = joined
            .regs
            .iter()
            .map(RegState::is_live)
            .collect::<Vec<_>>();
        joined
            .loans
            .retain(|reference, _| live[*reference as usize]);
    }
    if joined.holes != incoming.holes {
        if context.strict {
            return Err(flow_error(
                block,
                "block join has conflicting dereference hole states; every continuing \
                 path must restore a moved-out referent before the paths meet",
            ));
        }
        joined.holes.extend(incoming.holes.iter().copied());
    }
    for register in 0..joined.constants.len() {
        if joined.constants[register] != incoming.constants[register] {
            joined.constants[register] = None;
        }
    }
    let array_owners = joined
        .array_slots
        .keys()
        .chain(incoming.array_slots.keys())
        .copied()
        .collect::<BTreeSet<_>>();
    for owner in array_owners {
        if !joined.regs[owner as usize].is_live() {
            joined.array_slots.remove(&owner);
            continue;
        }
        let left = joined
            .array_slots
            .get(&owner)
            .cloned()
            .unwrap_or(ArraySlotState {
                length: None,
                empty: BTreeSet::new(),
                dynamic_hole: false,
                reference_origins: BTreeMap::new(),
            });
        let right = incoming
            .array_slots
            .get(&owner)
            .cloned()
            .unwrap_or(ArraySlotState {
                length: None,
                empty: BTreeSet::new(),
                dynamic_hole: false,
                reference_origins: BTreeMap::new(),
            });
        if left.reference_origins != right.reference_origins && context.strict {
            return Err(flow_error(
                block,
                format!(
                    "block join has conflicting exact reference origins in array slots of r{owner}"
                ),
            ));
        }
        let differs = left.empty != right.empty || left.dynamic_hole != right.dynamic_hole;
        if differs && context.strict {
            if context.locals[owner as usize].drop_glue == DropGlueKind::Custom {
                return Err(flow_error(
                    block,
                    format!(
                        "block join conditionally moves array slots of r{owner}, whose type has a custom Drop hook"
                    ),
                ));
            }
            let element = match context.representation(context.register_type(owner)) {
                Type::Array { element } => Some(*element),
                _ => None,
            };
            if element.is_some_and(|element| !context.type_admits_zero_use(element)) {
                return Err(flow_error(
                    block,
                    format!(
                        "block join conditionally moves a positive-Use array element of r{owner}"
                    ),
                ));
            }
        }
        joined.array_slots.insert(
            owner,
            ArraySlotState {
                length: (left.length == right.length)
                    .then_some(left.length)
                    .flatten(),
                empty: left.empty.union(&right.empty).copied().collect(),
                dynamic_hole: left.dynamic_hole || right.dynamic_hole,
                reference_origins: if left.reference_origins == right.reference_origins {
                    left.reference_origins
                } else {
                    BTreeMap::new()
                },
            },
        );
    }
    if joined.aggregate_reference_origins != incoming.aggregate_reference_origins {
        let registers = joined
            .aggregate_reference_origins
            .keys()
            .chain(incoming.aggregate_reference_origins.keys())
            .copied()
            .collect::<BTreeSet<_>>();
        for register in registers {
            if !joined.regs[register as usize].is_live() {
                // Origin facts describe only values which survive the join.
                // Unrestricted temporaries deliberately retired above must
                // not retain path-specific embedded-reference metadata.
                joined.aggregate_reference_origins.remove(&register);
                continue;
            }
            let left = joined
                .aggregate_reference_origins
                .get(&register)
                .cloned()
                .unwrap_or_default();
            let right = incoming
                .aggregate_reference_origins
                .get(&register)
                .cloned()
                .unwrap_or_default();
            if left == right {
                continue;
            }
            let variant_count = context.enum_variant_count(context.register_type(register));
            let variant_path = |path: &[u32]| {
                variant_count.is_some_and(|count| path.len() >= 2 && u32::MAX - path[0] < count)
            };
            let compatible = left
                .keys()
                .chain(right.keys())
                .all(|path| variant_path(path))
                && left
                    .iter()
                    .all(|(path, origin)| right.get(path).is_none_or(|other| other == origin));
            if !compatible {
                if context.strict {
                    return Err(flow_error(
                        block,
                        format!(
                            "block join has conflicting aggregate reference-origin paths for r{register} ({left:?} vs {right:?})"
                        ),
                    ));
                }
                joined.aggregate_reference_origins.remove(&register);
                continue;
            }
            let mut merged = left;
            merged.extend(right);
            if merged.is_empty() {
                joined.aggregate_reference_origins.remove(&register);
            } else {
                joined.aggregate_reference_origins.insert(register, merged);
            }
        }
    }
    for (slot, incoming_uses) in joined.uses.iter_mut().zip(&incoming.uses) {
        *slot = slot.hull(*incoming_uses);
    }
    for register in 0..joined.quantity_groups.len() {
        if joined.quantity_groups[register] != incoming.quantity_groups[register] {
            if context.strict
                && (joined.regs[register].is_live() || incoming.regs[register].is_live())
            {
                return Err(flow_error(
                    block,
                    format!(
                        "block join combines incompatible logical quantity aliases for r{register}"
                    ),
                ));
            }
            joined.quantity_groups[register] = None;
        }
    }
    for (slot, incoming_uses) in joined.quantity_uses.iter_mut().zip(&incoming.quantity_uses) {
        *slot = slot.hull(*incoming_uses);
    }
    for (slot, incoming_age) in joined.shell_ages.iter_mut().zip(&incoming.shell_ages) {
        if slot.is_some() && slot != incoming_age {
            *slot = None;
        }
    }
    for register in 0..joined.regs.len() {
        if joined.active_variants[register] != incoming.active_variants[register] {
            if context.strict
                && (matches!(joined.regs[register], RegState::Partial(_))
                    || matches!(incoming.regs[register], RegState::Partial(_)))
            {
                return Err(flow_error(
                    block,
                    format!(
                        "block join combines variant-relative partial shells for r{register} with different active variants"
                    ),
                ));
            }
            joined.active_variants[register] = None;
        }
        if joined.enum_tag_sources[register] != incoming.enum_tag_sources[register] {
            joined.enum_tag_sources[register] = None;
        }
    }
    Ok(Some(joined))
}

#[cfg(test)]
mod ownership_engine_tests {
    use grandiose_vm::bytecode::{EnumVariant, Field, Signature};
    use grandiose_vm::{I64, UNIT};

    use super::*;
    use crate::compiler_mir::{
        BasicBlock, BlockParam, BlockParamRole, DropFlagFact, FeatureBits, FlowProvenance,
        Instruction as MirInstruction, InstructionKind, LocalFact, MirPhase, Mutability, Operand,
        PlaceFlow, ScopeFact, StorageClass, UseInterval, UseMode,
    };
    use crate::span::Span;

    fn statement(kind: InstructionKind) -> MirInstruction {
        MirInstruction {
            span: Span::default(),
            kind,
        }
    }

    fn move_operand(register: Register) -> Operand {
        Operand {
            register,
            mode: UseMode::Move,
        }
    }

    fn block(id: u32, statements: Vec<MirInstruction>, terminator: Terminator) -> BasicBlock {
        BasicBlock {
            id,
            params: vec![],
            statements,
            terminator,
        }
    }

    /// A strict (exported-facts) function: `params` leading I64-style ABI
    /// registers after the unit receiver slot.
    fn exported_function(
        registers: Vec<grandiose_vm::TypeId>,
        params: usize,
        blocks: Vec<BasicBlock>,
        types: &[Type],
    ) -> Function {
        let mut flow = PlaceFlow {
            provenance: FlowProvenance::Exported,
            ..PlaceFlow::default()
        };
        flow.scopes.push(ScopeFact {
            parent: None,
            owners: vec![],
        });
        flow.sources.push(Span::default());
        for &ty in &registers {
            let mut fact = LocalFact::conservative(ty, &types[ty as usize]);
            // Source-level Use checking has already run; hand-built engine
            // tests start unrestricted and tighten intervals explicitly.
            fact.use_interval = UseInterval::UNRESTRICTED;
            flow.locals.push(fact);
        }
        Function {
            declaration: 0,
            name: "engine".into(),
            params: registers[1..=params].to_vec(),
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
            flow,
            invalid_analyses: 0,
        }
    }

    fn solve_function(function: &Function, types: &[Type]) -> Result<FlowSolution, FlowError> {
        let context = FlowContext {
            function,
            types,
            locals: &function.flow.locals,
            loans: loan_table(function, types),
            array_calls: &BTreeMap::new(),
            strict: true,
            refine_enum_switches: true,
        };
        solve(&context)
    }

    fn pair_types() -> (Vec<Type>, grandiose_vm::TypeId, grandiose_vm::TypeId) {
        let mut types = Type::predefined();
        let pair = types.len() as grandiose_vm::TypeId;
        types.push(Type::Tuple {
            fields: vec![I64, I64],
            copy: false,
        });
        let nested = types.len() as grandiose_vm::TypeId;
        types.push(Type::Tuple {
            fields: vec![pair, I64],
            copy: false,
        });
        (types, pair, nested)
    }

    fn reference_types() -> (Vec<Type>, grandiose_vm::TypeId, grandiose_vm::TypeId) {
        let mut types = Type::predefined();
        let shared = types.len() as grandiose_vm::TypeId;
        types.push(Type::RefShared { referent: I64 });
        let unique = types.len() as grandiose_vm::TypeId;
        types.push(Type::RefUnique { referent: I64 });
        (types, shared, unique)
    }

    #[test]
    fn equal_cfg_projections_of_an_aggregate_parameter_share_one_symbolic_origin() {
        let (mut types, shared, _) = reference_types();
        let pair = types.len() as grandiose_vm::TypeId;
        types.push(Type::Tuple {
            fields: vec![shared, shared],
            copy: true,
        });
        let projected = |block_id, destination| {
            block(
                block_id,
                vec![statement(InstructionKind::ProjectCopy {
                    dst: destination,
                    src: Operand {
                        register: 2,
                        mode: UseMode::Copy,
                    },
                    field: 0,
                })],
                Terminator::Goto(Edge {
                    target: 3,
                    args: vec![move_operand(destination)],
                }),
            )
        };
        let mut join = block(
            3,
            vec![
                statement(InstructionKind::EndBorrow { reference: 5 }),
                statement(InstructionKind::Drop {
                    owner: move_operand(2),
                }),
            ],
            Terminator::Return { value: None },
        );
        join.params.push(BlockParam {
            register: 5,
            ty: shared,
            role: BlockParamRole::Ordinary,
        });
        let function = exported_function(
            vec![UNIT, grandiose_vm::U32, pair, shared, shared, shared],
            2,
            vec![
                block(
                    0,
                    vec![],
                    Terminator::Switch {
                        discr: Operand {
                            register: 1,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            grandiose_vm::Constant::U32(0),
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
                projected(1, 3),
                projected(2, 4),
                join,
            ],
            &types,
        );

        let solution = solve_function(&function, &types).expect("equal symbolic origins join");
        let loan = &solution.entries[&3].loans[&5];
        assert!(loan.external);
        assert_eq!(loan.borrowed, Place::field(2, None, 0));
    }

    #[test]
    fn callable_environment_owns_and_releases_an_exact_unique_capture_origin() {
        let (mut types, _, unique) = reference_types();
        let environment = types.len() as grandiose_vm::TypeId;
        types.push(
            Type::Tuple {
                fields: vec![unique],
                copy: false,
            }
            .restricted(false, true),
        );
        let callable = types.len() as grandiose_vm::TypeId;
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            capture_type: environment,
            receiver_mode: 1,
            identity_name: "unique environment".into(),
            copy: false,
            zero_use_allowed: true,
        });
        let function = exported_function(
            vec![UNIT, I64, unique, callable, unique],
            1,
            vec![
                block(
                    0,
                    vec![
                        statement(InstructionKind::Borrow {
                            dst: 2,
                            src: 1,
                            unique: true,
                        }),
                        statement(InstructionKind::MakeCallable {
                            dst: 3,
                            callable_type: callable,
                            function: 1,
                            captures: vec![move_operand(2)],
                        }),
                    ],
                    Terminator::Goto(Edge {
                        target: 1,
                        args: vec![],
                    }),
                ),
                block(
                    1,
                    vec![
                        statement(InstructionKind::Drop {
                            owner: move_operand(3),
                        }),
                        statement(InstructionKind::Borrow {
                            dst: 4,
                            src: 1,
                            unique: true,
                        }),
                        statement(InstructionKind::EndBorrow { reference: 4 }),
                    ],
                    Terminator::Return { value: None },
                ),
            ],
            &types,
        );

        let solution = solve_function(&function, &types).expect("unique environment flow");
        let origin = &solution.entries[&1].aggregate_reference_origins[&3][&vec![0]];
        assert!(origin.unique);
        assert_eq!(origin.borrowed, Place::local(1));
    }

    fn enum_types() -> (Vec<Type>, grandiose_vm::TypeId) {
        let mut types = Type::predefined();
        let choice = types.len() as grandiose_vm::TypeId;
        types.push(Type::Enum {
            name: "Choice".into(),
            variants: vec![
                EnumVariant {
                    name: "Pair".into(),
                    fields: vec![
                        Field {
                            name: "0".into(),
                            ty: I64,
                        },
                        Field {
                            name: "1".into(),
                            ty: I64,
                        },
                    ],
                },
                EnumVariant {
                    name: "Single".into(),
                    fields: vec![
                        Field {
                            name: "0".into(),
                            ty: I64,
                        },
                        Field {
                            name: "1".into(),
                            ty: I64,
                        },
                    ],
                },
            ],
            copy: false,
        });
        (types, choice)
    }

    fn reusable_resumption_type() -> (Vec<Type>, grandiose_vm::TypeId) {
        let mut types = Type::predefined();
        let resumption = types.len() as grandiose_vm::TypeId;
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            lower_uses: 1,
            upper_uses: None,
            identity_name: "shared quantity".into(),
            copy: true,
        });
        (types, resumption)
    }

    #[test]
    fn copied_resumption_view_discharges_one_logical_quantity_owner() {
        let (types, resumption) = reusable_resumption_type();
        let mut function = exported_function(
            vec![UNIT, resumption, resumption, UNIT],
            1,
            vec![block(
                0,
                vec![
                    statement(InstructionKind::Copy {
                        dst: 2,
                        src: Operand {
                            register: 1,
                            mode: UseMode::Copy,
                        },
                    }),
                    statement(InstructionKind::MakeCallable {
                        dst: 3,
                        callable_type: UNIT,
                        function: 0,
                        captures: vec![move_operand(2)],
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(3),
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(1),
                    }),
                ],
                Terminator::Return { value: None },
            )],
            &types,
        );
        for register in [1, 2] {
            function.flow.locals[register].use_interval = UseInterval {
                lower: 1,
                upper: None,
            };
        }

        solve_function(&function, &types)
            .expect("a consuming use through a copied view discharges the shared quantity");
    }

    #[test]
    fn final_resumption_alias_still_enforces_lower_and_shared_upper_bounds() {
        let (types, resumption) = reusable_resumption_type();
        let make = |consume_twice| {
            let mut statements = vec![statement(InstructionKind::Copy {
                dst: 2,
                src: Operand {
                    register: 1,
                    mode: UseMode::Copy,
                },
            })];
            if consume_twice {
                statements.extend([
                    statement(InstructionKind::MakeCallable {
                        dst: 3,
                        callable_type: UNIT,
                        function: 0,
                        captures: vec![move_operand(2)],
                    }),
                    statement(InstructionKind::MakeCallable {
                        dst: 4,
                        callable_type: UNIT,
                        function: 0,
                        captures: vec![move_operand(1)],
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(3),
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(4),
                    }),
                ]);
            } else {
                statements.extend([
                    statement(InstructionKind::Drop {
                        owner: move_operand(2),
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(1),
                    }),
                ]);
            }
            let mut function = exported_function(
                vec![UNIT, resumption, resumption, UNIT, UNIT],
                1,
                vec![block(0, statements, Terminator::Return { value: None })],
                &types,
            );
            for register in [1, 2] {
                function.flow.locals[register].use_interval = UseInterval {
                    lower: 1,
                    upper: Some(1),
                };
            }
            function
        };

        let lower = solve_function(&make(false), &types).unwrap_err();
        assert!(lower.message.contains("positive Use lower bound 1"));
        let upper = solve_function(&make(true), &types).unwrap_err();
        assert!(upper.message.contains("Use upper bound 1"));
    }

    #[test]
    fn enum_tag_switch_refines_payload_moves_on_every_variant_edge() {
        let (types, choice) = enum_types();
        let function = exported_function(
            vec![UNIT, choice, grandiose_vm::U32, I64, grandiose_vm::U32],
            1,
            vec![
                block(
                    0,
                    vec![
                        statement(InstructionKind::EnumTag { dst: 2, src: 1 }),
                        statement(InstructionKind::Copy {
                            dst: 4,
                            src: Operand {
                                register: 2,
                                mode: UseMode::Copy,
                            },
                        }),
                    ],
                    Terminator::Switch {
                        discr: Operand {
                            register: 4,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            grandiose_vm::Constant::U32(0),
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
                block(
                    1,
                    vec![
                        statement(InstructionKind::ProjectMove {
                            dst: 3,
                            src: move_operand(1),
                            field: 1,
                        }),
                        statement(InstructionKind::Drop {
                            owner: move_operand(3),
                        }),
                        statement(InstructionKind::Drop {
                            owner: move_operand(1),
                        }),
                    ],
                    Terminator::Return { value: None },
                ),
                block(
                    2,
                    vec![
                        statement(InstructionKind::ProjectMove {
                            dst: 3,
                            src: move_operand(1),
                            field: 0,
                        }),
                        statement(InstructionKind::Drop {
                            owner: move_operand(3),
                        }),
                        statement(InstructionKind::Deconstruct { src: 1 }),
                    ],
                    Terminator::Return { value: None },
                ),
            ],
            &types,
        );
        solve_function(&function, &types).expect("tag edges prove active payload variants");
    }

    #[test]
    fn serialization_forces_encoded_variant_proofs_on_impossible_edges() {
        let mut types = Type::predefined();
        let choice = types.len() as grandiose_vm::TypeId;
        types.push(Type::Enum {
            name: "KnownChoice".into(),
            variants: vec![
                EnumVariant {
                    name: "First".into(),
                    fields: vec![Field {
                        name: "value".into(),
                        ty: I64,
                    }],
                },
                EnumVariant {
                    name: "Second".into(),
                    fields: vec![Field {
                        name: "value".into(),
                        ty: I64,
                    }],
                },
            ],
            copy: false,
        });
        let arm = |id| {
            block(
                id,
                vec![
                    statement(InstructionKind::Drop {
                        owner: move_operand(3),
                    }),
                    statement(InstructionKind::ProjectMove {
                        dst: 4,
                        src: move_operand(2),
                        field: 0,
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(4),
                    }),
                    statement(InstructionKind::Deconstruct { src: 2 }),
                ],
                Terminator::Return { value: None },
            )
        };
        let function = exported_function(
            vec![UNIT, I64, choice, grandiose_vm::U32, I64],
            1,
            vec![
                block(
                    0,
                    vec![
                        statement(InstructionKind::Construct {
                            dst: 2,
                            ty: choice,
                            variant: Some(1),
                            fields: vec![move_operand(1)],
                        }),
                        statement(InstructionKind::EnumTag { dst: 3, src: 2 }),
                    ],
                    Terminator::Switch {
                        discr: Operand {
                            register: 3,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            grandiose_vm::Constant::U32(0),
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
                arm(1),
                arm(2),
            ],
            &types,
        );
        let solution = solve(&FlowContext {
            function: &function,
            types: &types,
            locals: &function.flow.locals,
            loans: loan_table(&function, &types),
            array_calls: &BTreeMap::new(),
            strict: true,
            refine_enum_switches: false,
        })
        .expect("serialization follows every encoded enum edge");

        assert_eq!(solution.entries[&1].active_variants[2], Some(0));
        assert_eq!(solution.entries[&2].active_variants[2], Some(1));
    }

    #[test]
    fn enum_payload_projection_without_a_variant_proof_is_rejected() {
        let (types, choice) = enum_types();
        let function = exported_function(
            vec![UNIT, choice, I64],
            1,
            vec![block(
                0,
                vec![statement(InstructionKind::ProjectMove {
                    dst: 2,
                    src: move_operand(1),
                    field: 0,
                })],
                Terminator::Return { value: None },
            )],
            &types,
        );
        let error = solve_function(&function, &types).unwrap_err();
        assert!(
            error.message.contains("without an active-variant proof"),
            "{error:?}"
        );
    }

    #[test]
    fn partial_enum_shells_of_different_variants_cannot_join() {
        let (types, choice) = enum_types();
        let arm = |id, variant, target| {
            block(
                id,
                vec![
                    statement(InstructionKind::Copy {
                        dst: 6,
                        src: move_operand(2),
                    }),
                    statement(InstructionKind::Construct {
                        dst: 3,
                        ty: choice,
                        variant: Some(variant),
                        fields: vec![move_operand(2), move_operand(6)],
                    }),
                    statement(InstructionKind::ProjectMove {
                        dst: target,
                        src: move_operand(3),
                        field: 0,
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(target),
                    }),
                ],
                Terminator::Goto(Edge {
                    target: 3,
                    args: vec![],
                }),
            )
        };
        let function = exported_function(
            vec![UNIT, grandiose_vm::U32, I64, choice, I64, I64, I64],
            2,
            vec![
                block(
                    0,
                    vec![],
                    Terminator::Switch {
                        discr: Operand {
                            register: 1,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            grandiose_vm::Constant::U32(0),
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
                arm(1, 0, 4),
                arm(2, 1, 5),
                block(3, vec![], Terminator::Return { value: None }),
            ],
            &types,
        );
        let error = solve_function(&function, &types).unwrap_err();
        assert!(
            error.message.contains("variant-relative partial shells"),
            "{error:?}"
        );
    }

    #[test]
    fn nested_move_paths_track_disjoint_partial_moves_and_reinitialization() {
        let (types, pair, nested) = pair_types();
        // r1: nested tuple param. Project both leaves of the inner pair out
        // through fresh registers, then rebuild and reinitialize the subtree.
        let function = exported_function(
            vec![UNIT, nested, pair, I64, I64, pair],
            1,
            vec![block(
                0,
                vec![
                    // Partial move: inner pair out of the nested owner.
                    statement(InstructionKind::ProjectMove {
                        dst: 2,
                        src: move_operand(1),
                        field: 0,
                    }),
                    // Two disjoint partial moves out of the inner pair.
                    statement(InstructionKind::ProjectMove {
                        dst: 3,
                        src: move_operand(2),
                        field: 0,
                    }),
                    statement(InstructionKind::ProjectMove {
                        dst: 4,
                        src: move_operand(2),
                        field: 1,
                    }),
                    statement(InstructionKind::Deconstruct { src: 2 }),
                    // Reinitialize the subtree from the moved leaves.
                    statement(InstructionKind::Construct {
                        dst: 5,
                        ty: pair,
                        variant: None,
                        fields: vec![move_operand(3), move_operand(4)],
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(5),
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(1),
                    }),
                ],
                Terminator::Return { value: None },
            )],
            &types,
        );
        let solution = solve_function(&function, &types).expect("legal partial moves");
        // Before the inner-pair deconstruction, the shell and both leaves are
        // live, newest first.
        let lists = &solution.cleanup_lists[&0];
        assert_eq!(lists[3], vec![4, 3, 2, 1]);
        // After rebuilding, the residual nested shell and the new pair remain.
        assert_eq!(lists[5], vec![5, 1]);
    }

    #[test]
    fn double_partial_move_of_one_field_is_rejected() {
        let (types, pair, _) = pair_types();
        let function = exported_function(
            vec![UNIT, pair, I64, I64],
            1,
            vec![block(
                0,
                vec![
                    statement(InstructionKind::ProjectMove {
                        dst: 2,
                        src: move_operand(1),
                        field: 0,
                    }),
                    statement(InstructionKind::ProjectMove {
                        dst: 3,
                        src: move_operand(1),
                        field: 0,
                    }),
                ],
                Terminator::Return { value: None },
            )],
            &types,
        );
        let error = solve_function(&function, &types).unwrap_err();
        assert!(
            error
                .message
                .contains("reads field 0 of r1 after it was moved out"),
            "{error:?}"
        );
    }

    #[test]
    fn custom_drop_owners_reject_partial_moves() {
        let (types, pair, _) = pair_types();
        let mut function = exported_function(
            vec![UNIT, pair, I64],
            1,
            vec![block(
                0,
                vec![statement(InstructionKind::ProjectMove {
                    dst: 2,
                    src: move_operand(1),
                    field: 0,
                })],
                Terminator::Return { value: None },
            )],
            &types,
        );
        function.flow.locals[1].drop_glue = DropGlueKind::Custom;
        let error = solve_function(&function, &types).unwrap_err();
        assert!(error.message.contains("custom Drop hook"), "{error:?}");
    }

    #[test]
    fn branch_joins_reject_conflicting_initialization_without_a_drop_flag() {
        let (types, pair, _) = pair_types();
        let arm = |id, statements| {
            block(
                id,
                statements,
                Terminator::Goto(Edge {
                    target: 3,
                    args: vec![],
                }),
            )
        };
        let blocks = vec![
            block(
                0,
                vec![],
                Terminator::Switch {
                    discr: Operand {
                        register: 2,
                        mode: UseMode::Copy,
                    },
                    cases: vec![(
                        grandiose_vm::Constant::U32(0),
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
            arm(
                1,
                vec![statement(InstructionKind::Drop {
                    owner: move_operand(1),
                })],
            ),
            arm(2, vec![]),
            block(
                3,
                vec![statement(InstructionKind::Drop {
                    owner: move_operand(1),
                })],
                Terminator::Return { value: None },
            ),
        ];
        let mut function =
            exported_function(vec![UNIT, pair, grandiose_vm::U32], 2, blocks, &types);
        let error = solve_function(&function, &types).unwrap_err();
        assert!(
            error
                .message
                .contains("conflicting initialization states for r1"),
            "{error:?}"
        );

        // The same join is legal once a drop flag governs the owner, and the
        // owner becomes conditionally destroyed on the join path.
        function.flow.drop_flags.push(DropFlagFact {
            flag: 2,
            owner: 1,
            field: None,
        });
        let solution = solve_function(&function, &types).expect("flagged join");
        // The conditionally initialized owner stays on the cleanup list; the
        // runtime Empty state skips it when the branch already dropped it.
        assert_eq!(solution.cleanup_lists[&3][0], vec![2, 1]);

        let mut abandonment = function.clone();
        let join = abandonment
            .blocks
            .iter_mut()
            .find(|block| block.id == 3)
            .expect("join block");
        join.statements.clear();
        join.terminator = Terminator::Perform {
            result: None,
            protocol: 0,
            operation: 0,
            payloads: vec![],
            capture: crate::compiler_mir::ContinuationCapture {
                captured_owners: vec![1],
                captured_references: vec![],
                captured_residuals: vec![],
                cancellation_safe: true,
            },
            resume: None,
        };
        solve_function(&abandonment, &types)
            .expect("a whole drop flag remains cancellation-safe at terminal abandonment");
    }

    #[test]
    fn dead_conditionally_initialized_shared_reference_needs_no_drop_flag() {
        let (types, shared, _) = reference_types();
        let blocks = vec![
            block(
                0,
                vec![],
                Terminator::Switch {
                    discr: Operand {
                        register: 2,
                        mode: UseMode::Copy,
                    },
                    cases: vec![(
                        grandiose_vm::Constant::U32(0),
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
            block(
                1,
                vec![statement(InstructionKind::Reborrow {
                    dst: 3,
                    src: 1,
                    unique: false,
                })],
                Terminator::Goto(Edge {
                    target: 3,
                    args: vec![],
                }),
            ),
            block(
                2,
                vec![],
                Terminator::Goto(Edge {
                    target: 3,
                    args: vec![],
                }),
            ),
            block(3, vec![], Terminator::Return { value: None }),
        ];
        let function = exported_function(
            vec![UNIT, shared, grandiose_vm::U32, shared],
            2,
            blocks,
            &types,
        );
        solve_function(&function, &types)
            .expect("dead shared-reference temporaries require no runtime presence flag");
    }

    #[test]
    fn dead_conditionally_initialized_copy_temporary_is_consumed_at_join() {
        let types = Type::predefined();
        let blocks = vec![
            block(
                0,
                vec![],
                Terminator::Switch {
                    discr: Operand {
                        register: 1,
                        mode: UseMode::Copy,
                    },
                    cases: vec![(
                        grandiose_vm::Constant::U32(0),
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
            block(
                1,
                vec![statement(InstructionKind::Const {
                    dst: 2,
                    value: grandiose_vm::Constant::I64(1),
                })],
                Terminator::Goto(Edge {
                    target: 3,
                    args: vec![],
                }),
            ),
            block(
                2,
                vec![],
                Terminator::Goto(Edge {
                    target: 3,
                    args: vec![],
                }),
            ),
            block(3, vec![], Terminator::Return { value: None }),
        ];
        let function = exported_function(vec![UNIT, grandiose_vm::U32, I64], 1, blocks, &types);
        let solution = solve_function(&function, &types)
            .expect("dead copy temporaries require no runtime presence flag");
        assert_eq!(solution.entries[&3].regs[2], RegState::Consumed);
    }

    #[test]
    fn branch_joins_allow_conditionally_initialized_copy_temporaries() {
        let types = Type::predefined();
        let arm = |id, statements| {
            block(
                id,
                statements,
                Terminator::Goto(Edge {
                    target: 3,
                    args: vec![],
                }),
            )
        };
        let function = exported_function(
            vec![UNIT, grandiose_vm::U32, grandiose_vm::U32],
            2,
            vec![
                block(
                    0,
                    vec![],
                    Terminator::Switch {
                        discr: Operand {
                            register: 2,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            grandiose_vm::Constant::U32(0),
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
                arm(
                    1,
                    vec![statement(InstructionKind::Drop {
                        owner: move_operand(1),
                    })],
                ),
                arm(2, vec![]),
                block(3, vec![], Terminator::Return { value: None }),
            ],
            &types,
        );
        solve_function(&function, &types)
            .expect("Copy temporaries need no runtime drop flag at an unused join");
    }

    #[test]
    fn branch_joins_merge_partial_bitmaps_with_per_field_drop_flags() {
        let mut types = Type::predefined();
        let pair = types.len() as grandiose_vm::TypeId;
        types.push(Type::Tuple {
            fields: vec![UNIT, UNIT],
            copy: false,
        });
        let arm = |id, field, destination| {
            block(
                id,
                vec![
                    statement(InstructionKind::ProjectMove {
                        dst: destination,
                        src: move_operand(1),
                        field,
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(destination),
                    }),
                ],
                Terminator::Goto(Edge {
                    target: 3,
                    args: vec![],
                }),
            )
        };
        let blocks = vec![
            block(
                0,
                vec![],
                Terminator::Switch {
                    discr: Operand {
                        register: 2,
                        mode: UseMode::Copy,
                    },
                    cases: vec![(
                        grandiose_vm::Constant::U32(0),
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
            arm(1, 0, 3),
            arm(2, 1, 4),
            block(
                3,
                vec![statement(InstructionKind::Drop {
                    owner: move_operand(1),
                })],
                Terminator::Return { value: None },
            ),
        ];
        let mut function = exported_function(
            vec![UNIT, pair, grandiose_vm::U32, UNIT, UNIT],
            2,
            blocks,
            &types,
        );
        function.flow.drop_flags.extend([
            DropFlagFact {
                flag: 2,
                owner: 1,
                field: Some(0),
            },
            DropFlagFact {
                flag: 2,
                owner: 1,
                field: Some(1),
            },
        ]);
        let solution = solve_function(&function, &types).expect("field-flagged partial join");
        assert_eq!(
            solution.entries[&3].regs[1],
            RegState::Partial(vec![true, true])
        );
        assert_eq!(
            solution.entries[&3].conditional_fields[&1],
            vec![true, true]
        );
        assert_eq!(solution.cleanup_lists[&3][0], vec![2, 1]);

        let mut conditional_read = function.clone();
        conditional_read
            .blocks
            .iter_mut()
            .find(|block| block.id == 3)
            .expect("join block")
            .statements
            .insert(
                0,
                statement(InstructionKind::ProjectCopy {
                    dst: 3,
                    src: Operand {
                        register: 1,
                        mode: UseMode::Copy,
                    },
                    field: 0,
                }),
            );
        let error = solve_function(&conditional_read, &types).unwrap_err();
        assert!(
            error
                .message
                .contains("ProjectCopy reads conditionally initialized field 0 of r1"),
            "{error:?}"
        );

        function.flow.drop_flags.pop();
        let error = solve_function(&function, &types).unwrap_err();
        assert!(
            error
                .message
                .contains("field 1 of r1 without a governing field drop flag"),
            "{error:?}"
        );
    }

    #[test]
    fn loops_cannot_re_move_a_conditionally_initialized_field() {
        let mut types = Type::predefined();
        let pair = types.len() as grandiose_vm::TypeId;
        types.push(Type::Tuple {
            fields: vec![UNIT, UNIT],
            copy: false,
        });
        let blocks = vec![
            block(
                0,
                vec![
                    statement(InstructionKind::ProjectMove {
                        dst: 3,
                        src: move_operand(1),
                        field: 0,
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(3),
                    }),
                ],
                Terminator::Goto(Edge {
                    target: 1,
                    args: vec![],
                }),
            ),
            block(
                1,
                vec![],
                Terminator::Switch {
                    discr: Operand {
                        register: 2,
                        mode: UseMode::Copy,
                    },
                    cases: vec![(
                        grandiose_vm::Constant::U32(0),
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
            ),
            block(
                2,
                vec![
                    statement(InstructionKind::ProjectMove {
                        dst: 4,
                        src: move_operand(1),
                        field: 1,
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(4),
                    }),
                ],
                Terminator::Goto(Edge {
                    target: 1,
                    args: vec![],
                }),
            ),
            block(
                3,
                vec![statement(InstructionKind::Drop {
                    owner: move_operand(1),
                })],
                Terminator::Return { value: None },
            ),
        ];
        let mut function = exported_function(
            vec![UNIT, pair, grandiose_vm::U32, UNIT, UNIT],
            2,
            blocks,
            &types,
        );
        function.flow.drop_flags.push(DropFlagFact {
            flag: 2,
            owner: 1,
            field: Some(1),
        });
        let error = solve_function(&function, &types).unwrap_err();
        assert!(
            error
                .message
                .contains("ProjectMove reads conditionally initialized field 1 of r1"),
            "{error:?}"
        );

        function.flow.locals[1].drop_glue = DropGlueKind::Custom;
        let error = solve_function(&function, &types).unwrap_err();
        assert!(error.message.contains("custom Drop hook"), "{error:?}");
    }

    #[test]
    fn malformed_field_drop_flags_are_rejected_before_dataflow() {
        let (types, pair, _) = pair_types();
        let base = exported_function(
            vec![UNIT, pair, grandiose_vm::U32],
            2,
            vec![block(
                0,
                vec![statement(InstructionKind::Drop {
                    owner: move_operand(1),
                })],
                Terminator::Return { value: None },
            )],
            &types,
        );

        let mut out_of_bounds = base.clone();
        out_of_bounds.flow.drop_flags.push(DropFlagFact {
            flag: 2,
            owner: 1,
            field: Some(2),
        });
        let error = solve_function(&out_of_bounds, &types).unwrap_err();
        assert!(error.message.contains("out-of-bounds field 2"), "{error:?}");

        let mut restricted_types = types.clone();
        let restricted = restricted_types.len() as grandiose_vm::TypeId;
        restricted_types.push(Type::I64.restricted(false, false));
        let restricted_pair = restricted_types.len() as grandiose_vm::TypeId;
        restricted_types.push(Type::Tuple {
            fields: vec![restricted, UNIT],
            copy: false,
        });
        let mut positive_field = exported_function(
            vec![UNIT, restricted_pair, grandiose_vm::U32],
            2,
            vec![block(0, vec![], Terminator::Unreachable)],
            &restricted_types,
        );
        positive_field.flow.drop_flags.push(DropFlagFact {
            flag: 2,
            owner: 1,
            field: Some(0),
        });
        let error = solve_function(&positive_field, &restricted_types).unwrap_err();
        assert!(
            error.message.contains("without Use<[0,0]> evidence"),
            "{error:?}"
        );

        let mut duplicate = base;
        let fact = DropFlagFact {
            flag: 2,
            owner: 1,
            field: None,
        };
        duplicate.flow.drop_flags.extend([fact.clone(), fact]);
        let error = solve_function(&duplicate, &types).unwrap_err();
        assert!(error.message.contains("duplicate drop flag"), "{error:?}");
    }

    #[test]
    fn residual_shell_construction_requires_the_exact_register_layout() {
        let (types, pair, _) = pair_types();
        let missing_field = exported_function(
            vec![UNIT, I64, pair],
            1,
            vec![block(
                0,
                vec![statement(InstructionKind::Construct {
                    dst: 2,
                    ty: pair,
                    variant: None,
                    fields: vec![move_operand(1)],
                })],
                Terminator::Unreachable,
            )],
            &types,
        );
        let error = solve_function(&missing_field, &types).unwrap_err();
        assert!(
            error.message.contains("active layout requires 2"),
            "{error:?}"
        );

        let wrong_register_type = exported_function(
            vec![UNIT, I64, I64, pair],
            2,
            vec![block(
                0,
                vec![statement(InstructionKind::Construct {
                    dst: 3,
                    ty: UNIT,
                    variant: None,
                    fields: vec![],
                })],
                Terminator::Unreachable,
            )],
            &types,
        );
        let error = solve_function(&wrong_register_type, &types).unwrap_err();
        assert!(error.message.contains("register has type"), "{error:?}");
    }

    #[test]
    fn enum_variant_replacement_requires_payload_disposition_and_custom_drop_never_deconstructs() {
        let mut types = Type::predefined();
        let restricted = types.len() as grandiose_vm::TypeId;
        types.push(Type::I64.restricted(false, false));
        let choice = types.len() as grandiose_vm::TypeId;
        types.push(Type::Enum {
            name: "RestrictedChoice".into(),
            variants: vec![
                EnumVariant {
                    name: "Full".into(),
                    fields: vec![Field {
                        name: "value".into(),
                        ty: restricted,
                    }],
                },
                EnumVariant {
                    name: "Empty".into(),
                    fields: vec![],
                },
            ],
            copy: false,
        });
        let statements = vec![
            statement(InstructionKind::Construct {
                dst: 2,
                ty: choice,
                variant: Some(0),
                fields: vec![move_operand(1)],
            }),
            statement(InstructionKind::ProjectMove {
                dst: 3,
                src: move_operand(2),
                field: 0,
            }),
            statement(InstructionKind::Deconstruct { src: 2 }),
            statement(InstructionKind::Construct {
                dst: 2,
                ty: choice,
                variant: Some(1),
                fields: vec![],
            }),
            statement(InstructionKind::Drop {
                owner: move_operand(2),
            }),
        ];
        let mut replacement = exported_function(
            vec![UNIT, restricted, choice, restricted],
            1,
            vec![block(
                0,
                statements,
                Terminator::Return {
                    value: Some(move_operand(3)),
                },
            )],
            &types,
        );
        replacement.result = restricted;
        solve_function(&replacement, &types)
            .expect("exhaustive payload transfer permits a new enum variant");

        let mut undisposed = replacement.clone();
        undisposed.blocks[0].statements.remove(1);
        undisposed.blocks[0].statements.remove(4 - 1);
        let error = solve_function(&undisposed, &types).unwrap_err();
        assert!(
            error
                .message
                .contains("still-initialized field 0 of r2 without Use<[0,0]>"),
            "{error:?}"
        );

        let mut empty_types = Type::predefined();
        let empty = empty_types.len() as grandiose_vm::TypeId;
        empty_types.push(Type::Tuple {
            fields: vec![],
            copy: false,
        });
        let mut custom = exported_function(
            vec![UNIT, empty],
            0,
            vec![block(
                0,
                vec![
                    statement(InstructionKind::Construct {
                        dst: 1,
                        ty: empty,
                        variant: None,
                        fields: vec![],
                    }),
                    statement(InstructionKind::Deconstruct { src: 1 }),
                ],
                Terminator::Return { value: None },
            )],
            &empty_types,
        );
        custom.flow.locals[1].drop_glue = DropGlueKind::Custom;
        let error = solve_function(&custom, &empty_types).unwrap_err();
        assert!(error.message.contains("custom Drop hook"), "{error:?}");
    }

    #[test]
    fn branch_joins_reject_conditionally_moved_positive_use_fields_even_with_flags() {
        let mut types = Type::predefined();
        let restricted = types.len() as grandiose_vm::TypeId;
        types.push(Type::I64.restricted(false, false));
        let wrapper = types.len() as grandiose_vm::TypeId;
        types.push(Type::Tuple {
            fields: vec![restricted],
            copy: false,
        });
        let mut function = exported_function(
            vec![UNIT, wrapper, grandiose_vm::U32, restricted],
            2,
            vec![
                block(
                    0,
                    vec![],
                    Terminator::Switch {
                        discr: Operand {
                            register: 2,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            grandiose_vm::Constant::U32(0),
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
                block(
                    1,
                    vec![statement(InstructionKind::ProjectMove {
                        dst: 3,
                        src: move_operand(1),
                        field: 0,
                    })],
                    Terminator::Call {
                        result: None,
                        function: 999,
                        args: vec![move_operand(3)],
                        normal: Edge {
                            target: 3,
                            args: vec![],
                        },
                    },
                ),
                block(
                    2,
                    vec![],
                    Terminator::Goto(Edge {
                        target: 3,
                        args: vec![],
                    }),
                ),
                block(3, vec![], Terminator::Unreachable),
            ],
            &types,
        );
        function.flow.drop_flags.push(DropFlagFact {
            flag: 2,
            owner: 1,
            field: Some(0),
        });
        let error = solve_function(&function, &types).unwrap_err();
        assert!(
            error.message.contains("without Use<[0,0]> evidence"),
            "{error:?}"
        );
    }

    #[test]
    fn exact_array_slot_moves_restore_and_dynamic_or_invalid_indices_reject() {
        let mut types = Type::predefined();
        let array = types.len() as grandiose_vm::TypeId;
        types.push(Type::Array { element: I64 });
        let unique_array = types.len() as grandiose_vm::TypeId;
        types.push(Type::RefUnique { referent: array });
        let registers = vec![
            UNIT,
            array,
            unique_array,
            grandiose_vm::USIZE,
            I64,
            UNIT,
            I64,
            UNIT,
        ];
        let prefix = vec![
            statement(InstructionKind::Primitive {
                dst: 1,
                primitive: grandiose_vm::Primitive::ArrayEmpty,
                args: vec![],
            }),
            statement(InstructionKind::Const {
                dst: 4,
                value: grandiose_vm::Constant::I64(42),
            }),
            statement(InstructionKind::Borrow {
                dst: 2,
                src: 1,
                unique: true,
            }),
            statement(InstructionKind::Primitive {
                dst: 5,
                primitive: grandiose_vm::Primitive::ArrayPushMove,
                args: vec![move_operand(2), move_operand(4)],
            }),
            statement(InstructionKind::Const {
                dst: 3,
                value: grandiose_vm::Constant::Usize(0),
            }),
            statement(InstructionKind::Borrow {
                dst: 2,
                src: 1,
                unique: true,
            }),
            statement(InstructionKind::Primitive {
                dst: 6,
                primitive: grandiose_vm::Primitive::ArrayGetMove,
                args: vec![
                    move_operand(2),
                    Operand {
                        register: 3,
                        mode: UseMode::Copy,
                    },
                ],
            }),
        ];
        let mut positive = prefix.clone();
        positive.extend([
            statement(InstructionKind::Drop {
                owner: move_operand(6),
            }),
            statement(InstructionKind::Primitive {
                dst: 7,
                primitive: grandiose_vm::Primitive::ArrayFinishDrained,
                args: vec![move_operand(1)],
            }),
        ]);
        let function = exported_function(
            registers.clone(),
            0,
            vec![block(0, positive, Terminator::Return { value: None })],
            &types,
        );
        solve_function(&function, &types).expect("one exact slot is fully drained");

        let mut hole_to_bytes = prefix.clone();
        hole_to_bytes.push(statement(InstructionKind::Primitive {
            dst: 7,
            primitive: grandiose_vm::Primitive::BytesFromArrayMove,
            args: vec![move_operand(1)],
        }));
        let mut byte_registers = registers.clone();
        byte_registers[7] = grandiose_vm::BYTES;
        let function = exported_function(
            byte_registers,
            0,
            vec![block(0, hole_to_bytes, Terminator::Unreachable)],
            &types,
        );
        let error = solve_function(&function, &types).unwrap_err();
        assert!(
            error.message.contains("every array slot initialized"),
            "{error:?}"
        );

        let mut duplicate = prefix.clone();
        duplicate.extend([
            statement(InstructionKind::Drop {
                owner: move_operand(6),
            }),
            statement(InstructionKind::Borrow {
                dst: 2,
                src: 1,
                unique: true,
            }),
            statement(InstructionKind::Primitive {
                dst: 6,
                primitive: grandiose_vm::Primitive::ArrayGetMove,
                args: vec![
                    move_operand(2),
                    Operand {
                        register: 3,
                        mode: UseMode::Copy,
                    },
                ],
            }),
        ]);
        let function = exported_function(
            registers.clone(),
            0,
            vec![block(0, duplicate, Terminator::Unreachable)],
            &types,
        );
        let error = solve_function(&function, &types).unwrap_err();
        assert!(
            error.message.contains("after it was moved out"),
            "{error:?}"
        );

        let mut out_of_bounds = prefix;
        if let InstructionKind::Const { value, .. } = &mut out_of_bounds[4].kind {
            *value = grandiose_vm::Constant::Usize(1);
        }
        let function = exported_function(
            registers,
            0,
            vec![block(0, out_of_bounds, Terminator::Unreachable)],
            &types,
        );
        let error = solve_function(&function, &types).unwrap_err();
        assert!(
            error.message.contains("out-of-bounds array index 1"),
            "{error:?}"
        );

        let dynamic_registers = vec![
            UNIT,
            grandiose_vm::USIZE,
            array,
            unique_array,
            I64,
            UNIT,
            I64,
            grandiose_vm::USIZE,
        ];
        let dynamic = vec![
            statement(InstructionKind::Primitive {
                dst: 2,
                primitive: grandiose_vm::Primitive::ArrayEmpty,
                args: vec![],
            }),
            statement(InstructionKind::Const {
                dst: 4,
                value: grandiose_vm::Constant::I64(42),
            }),
            statement(InstructionKind::Borrow {
                dst: 3,
                src: 2,
                unique: true,
            }),
            statement(InstructionKind::Primitive {
                dst: 5,
                primitive: grandiose_vm::Primitive::ArrayPushMove,
                args: vec![move_operand(3), move_operand(4)],
            }),
            statement(InstructionKind::Borrow {
                dst: 3,
                src: 2,
                unique: true,
            }),
            statement(InstructionKind::Primitive {
                dst: 6,
                primitive: grandiose_vm::Primitive::ArrayGetMove,
                args: vec![
                    move_operand(3),
                    Operand {
                        register: 1,
                        mode: UseMode::Copy,
                    },
                ],
            }),
            statement(InstructionKind::Drop {
                owner: move_operand(6),
            }),
            statement(InstructionKind::Const {
                dst: 7,
                value: grandiose_vm::Constant::Usize(0),
            }),
            statement(InstructionKind::Borrow {
                dst: 3,
                src: 2,
                unique: true,
            }),
            statement(InstructionKind::Primitive {
                dst: 6,
                primitive: grandiose_vm::Primitive::ArrayGetMove,
                args: vec![
                    move_operand(3),
                    Operand {
                        register: 7,
                        mode: UseMode::Copy,
                    },
                ],
            }),
        ];
        let function = exported_function(
            dynamic_registers,
            1,
            vec![block(0, dynamic, Terminator::Unreachable)],
            &types,
        );
        let error = solve_function(&function, &types).unwrap_err();
        assert!(error.message.contains("dynamic-index move"), "{error:?}");
    }

    #[test]
    fn array_write_summaries_transport_exact_reference_parameters_through_wrapper_chains() {
        let mut types = Type::predefined();
        let shared_i64 = types.len() as grandiose_vm::TypeId;
        types.push(Type::RefShared { referent: I64 });
        let array = types.len() as grandiose_vm::TypeId;
        types.push(Type::Array {
            element: shared_i64,
        });
        let unique_array = types.len() as grandiose_vm::TypeId;
        types.push(Type::RefUnique { referent: array });
        let reference_pair = types.len() as grandiose_vm::TypeId;
        types.push(Type::Tuple {
            fields: vec![I64, shared_i64],
            copy: false,
        });

        let mut leaf = exported_function(
            vec![UNIT, unique_array, shared_i64, UNIT],
            2,
            vec![block(
                0,
                vec![statement(InstructionKind::Primitive {
                    dst: 3,
                    primitive: grandiose_vm::Primitive::ArrayPushMove,
                    args: vec![move_operand(1), move_operand(2)],
                })],
                Terminator::Return { value: None },
            )],
            &types,
        );
        leaf.declaration = 11;
        leaf.name = "push_reference".into();

        let mut relay = exported_function(
            vec![UNIT, unique_array, shared_i64, UNIT],
            2,
            vec![
                block(
                    0,
                    vec![],
                    Terminator::Call {
                        result: Some(3),
                        function: 11,
                        args: vec![move_operand(1), move_operand(2)],
                        normal: Edge {
                            target: 1,
                            args: vec![],
                        },
                    },
                ),
                block(1, vec![], Terminator::Return { value: None }),
            ],
            &types,
        );
        relay.declaration = 12;
        relay.name = "relay_push_reference".into();

        let mut indirect = exported_function(
            vec![UNIT, unique_array, shared_i64, UNIT, UNIT],
            2,
            vec![
                block(
                    0,
                    vec![statement(InstructionKind::MakeCallable {
                        dst: 4,
                        callable_type: UNIT,
                        function: 11,
                        captures: vec![],
                    })],
                    Terminator::CallIndirect {
                        result: Some(3),
                        callable: move_operand(4),
                        known_function: None,
                        receiver_mode: 0,
                        cleanup_callable: true,
                        args: vec![move_operand(1), move_operand(2)],
                        normal: Edge {
                            target: 1,
                            args: vec![],
                        },
                    },
                ),
                block(1, vec![], Terminator::Return { value: None }),
            ],
            &types,
        );
        indirect.declaration = 14;
        indirect.name = "indirect_push_reference".into();

        let mut aggregate_leaf = exported_function(
            vec![UNIT, unique_array, reference_pair, shared_i64, UNIT],
            2,
            vec![block(
                0,
                vec![
                    statement(InstructionKind::ProjectMove {
                        dst: 3,
                        src: move_operand(2),
                        field: 1,
                    }),
                    statement(InstructionKind::Primitive {
                        dst: 4,
                        primitive: grandiose_vm::Primitive::ArrayPushMove,
                        args: vec![move_operand(1), move_operand(3)],
                    }),
                ],
                Terminator::Return { value: None },
            )],
            &types,
        );
        aggregate_leaf.declaration = 15;
        aggregate_leaf.name = "push_aggregate_reference".into();

        let mut divergent = exported_function(
            vec![UNIT, grandiose_vm::U32, unique_array, shared_i64, UNIT],
            3,
            vec![
                block(
                    0,
                    vec![],
                    Terminator::Switch {
                        discr: Operand {
                            register: 1,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            grandiose_vm::Constant::U32(1),
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
                block(
                    1,
                    vec![statement(InstructionKind::Primitive {
                        dst: 4,
                        primitive: grandiose_vm::Primitive::ArrayPushMove,
                        args: vec![move_operand(2), move_operand(3)],
                    })],
                    Terminator::Return { value: None },
                ),
                block(2, vec![], Terminator::Unreachable),
            ],
            &types,
        );
        divergent.declaration = 16;
        divergent.name = "control_divergent_push_reference".into();

        let equal_push = || {
            vec![statement(InstructionKind::Primitive {
                dst: 4,
                primitive: grandiose_vm::Primitive::ArrayPushMove,
                args: vec![move_operand(2), move_operand(3)],
            })]
        };
        let mut equal_arms = exported_function(
            vec![UNIT, grandiose_vm::U32, unique_array, shared_i64, UNIT],
            3,
            vec![
                block(
                    0,
                    vec![],
                    Terminator::Switch {
                        discr: Operand {
                            register: 1,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            grandiose_vm::Constant::U32(1),
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
                block(
                    1,
                    equal_push(),
                    Terminator::Goto(Edge {
                        target: 3,
                        args: vec![],
                    }),
                ),
                block(
                    2,
                    equal_push(),
                    Terminator::Goto(Edge {
                        target: 3,
                        args: vec![],
                    }),
                ),
                block(3, vec![], Terminator::Return { value: None }),
            ],
            &types,
        );
        equal_arms.declaration = 17;
        equal_arms.name = "equal_arm_push_reference".into();

        let mut ambiguous_arms = exported_function(
            vec![
                UNIT,
                grandiose_vm::U32,
                unique_array,
                shared_i64,
                shared_i64,
                UNIT,
            ],
            4,
            vec![
                block(
                    0,
                    vec![],
                    Terminator::Switch {
                        discr: Operand {
                            register: 1,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            grandiose_vm::Constant::U32(1),
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
                block(
                    1,
                    vec![statement(InstructionKind::Primitive {
                        dst: 5,
                        primitive: grandiose_vm::Primitive::ArrayPushMove,
                        args: vec![move_operand(2), move_operand(3)],
                    })],
                    Terminator::Return { value: None },
                ),
                block(
                    2,
                    vec![statement(InstructionKind::Primitive {
                        dst: 5,
                        primitive: grandiose_vm::Primitive::ArrayPushMove,
                        args: vec![move_operand(2), move_operand(4)],
                    })],
                    Terminator::Return { value: None },
                ),
            ],
            &types,
        );
        ambiguous_arms.declaration = 18;
        ambiguous_arms.name = "ambiguous_arm_push_reference".into();

        let recursive_blocks = |recursive_statements| {
            vec![
                block(
                    0,
                    vec![],
                    Terminator::Switch {
                        discr: Operand {
                            register: 1,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            grandiose_vm::Constant::U32(0),
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
                block(
                    1,
                    vec![statement(InstructionKind::Primitive {
                        dst: 4,
                        primitive: grandiose_vm::Primitive::ArrayPushMove,
                        args: vec![move_operand(2), move_operand(3)],
                    })],
                    Terminator::Return { value: None },
                ),
                block(
                    2,
                    recursive_statements,
                    Terminator::TailCallSelf {
                        args: vec![
                            Operand {
                                register: 1,
                                mode: UseMode::Copy,
                            },
                            move_operand(2),
                            move_operand(3),
                        ],
                    },
                ),
            ]
        };
        let recursive_registers = vec![UNIT, grandiose_vm::U32, unique_array, shared_i64, UNIT];
        let mut bounded_recursive = exported_function(
            recursive_registers.clone(),
            3,
            recursive_blocks(vec![]),
            &types,
        );
        bounded_recursive.declaration = 19;
        bounded_recursive.name = "bounded_recursive_push_reference".into();
        let mut unbounded_recursive = exported_function(
            recursive_registers,
            3,
            recursive_blocks(vec![statement(InstructionKind::Primitive {
                dst: 4,
                primitive: grandiose_vm::Primitive::ArrayPushMove,
                args: vec![move_operand(2), move_operand(3)],
            })]),
            &types,
        );
        unbounded_recursive.declaration = 20;
        unbounded_recursive.name = "unbounded_recursive_push_reference".into();

        let mutually_recursive_blocks = |callee, value_register| {
            vec![
                block(
                    0,
                    vec![],
                    Terminator::Switch {
                        discr: Operand {
                            register: 1,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            grandiose_vm::Constant::U32(0),
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
                block(
                    1,
                    vec![statement(InstructionKind::Primitive {
                        dst: 5,
                        primitive: grandiose_vm::Primitive::ArrayPushMove,
                        args: vec![move_operand(2), move_operand(value_register)],
                    })],
                    Terminator::Return { value: None },
                ),
                block(
                    2,
                    vec![],
                    Terminator::TailCall {
                        function: callee,
                        args: vec![
                            Operand {
                                register: 1,
                                mode: UseMode::Copy,
                            },
                            move_operand(2),
                            move_operand(3),
                            move_operand(4),
                        ],
                    },
                ),
            ]
        };
        let mutual_registers = vec![
            UNIT,
            grandiose_vm::U32,
            unique_array,
            shared_i64,
            shared_i64,
            UNIT,
        ];
        let mut mutual_equal_left = exported_function(
            mutual_registers.clone(),
            4,
            mutually_recursive_blocks(22, 3),
            &types,
        );
        mutual_equal_left.declaration = 21;
        mutual_equal_left.name = "mutual_equal_left".into();
        let mut mutual_equal_right = exported_function(
            mutual_registers.clone(),
            4,
            mutually_recursive_blocks(21, 3),
            &types,
        );
        mutual_equal_right.declaration = 22;
        mutual_equal_right.name = "mutual_equal_right".into();
        let mut mutual_ambiguous_left = exported_function(
            mutual_registers.clone(),
            4,
            mutually_recursive_blocks(24, 3),
            &types,
        );
        mutual_ambiguous_left.declaration = 23;
        mutual_ambiguous_left.name = "mutual_ambiguous_left".into();
        let mut mutual_ambiguous_right = exported_function(
            mutual_registers,
            4,
            mutually_recursive_blocks(23, 4),
            &types,
        );
        mutual_ambiguous_right.declaration = 24;
        mutual_ambiguous_right.name = "mutual_ambiguous_right".into();

        // Reverse dependency order exercises the least fixed point rather
        // than accidentally relying on declaration order.
        let summaries = array_call_summaries(
            &crate::compiler_mir::Program {
                functions: vec![
                    mutual_ambiguous_right,
                    mutual_ambiguous_left,
                    mutual_equal_right,
                    mutual_equal_left,
                    ambiguous_arms,
                    unbounded_recursive,
                    bounded_recursive,
                    equal_arms,
                    divergent,
                    aggregate_leaf,
                    indirect,
                    relay,
                    leaf,
                ],
            },
            &types,
        );
        for declaration in [11, 12, 14] {
            let summary = &summaries[&declaration];
            assert_eq!(summary.effects.len(), 1);
            assert_eq!(summary.effects[0].kind, ArrayEffectKind::Push);
            assert_eq!(summary.effects[0].owner_parameter, 0);
            assert_eq!(summary.effects[0].value_parameter, Some(1));
            assert!(summary.effects[0].value_path.is_empty());
        }
        let aggregate_summary = &summaries[&15];
        assert_eq!(aggregate_summary.effects[0].value_parameter, Some(1));
        assert_eq!(aggregate_summary.effects[0].value_path, [1]);
        let divergent_summary = &summaries[&16];
        assert_eq!(divergent_summary.effects[0].owner_parameter, 1);
        assert_eq!(divergent_summary.effects[0].value_parameter, Some(2));
        let equal_summary = &summaries[&17];
        assert_eq!(equal_summary.effects[0].owner_parameter, 1);
        assert_eq!(equal_summary.effects[0].value_parameter, Some(2));
        assert!(!summaries.contains_key(&18));
        let recursive_summary = &summaries[&19];
        assert_eq!(recursive_summary.effects[0].owner_parameter, 1);
        assert_eq!(recursive_summary.effects[0].value_parameter, Some(2));
        assert!(!summaries.contains_key(&20));
        for declaration in [21, 22] {
            let summary = &summaries[&declaration];
            assert_eq!(summary.effects.len(), 1);
            assert_eq!(summary.effects[0].owner_parameter, 1);
            assert_eq!(summary.effects[0].value_parameter, Some(2));
        }
        assert!(!summaries.contains_key(&23));
        assert!(!summaries.contains_key(&24));

        let aggregate_caller = exported_function(
            vec![
                UNIT,
                shared_i64,
                I64,
                reference_pair,
                array,
                unique_array,
                UNIT,
            ],
            1,
            vec![
                block(
                    0,
                    vec![
                        statement(InstructionKind::Const {
                            dst: 2,
                            value: grandiose_vm::Constant::I64(7),
                        }),
                        statement(InstructionKind::Construct {
                            dst: 3,
                            ty: reference_pair,
                            variant: None,
                            fields: vec![move_operand(2), move_operand(1)],
                        }),
                        statement(InstructionKind::Primitive {
                            dst: 4,
                            primitive: grandiose_vm::Primitive::ArrayEmpty,
                            args: vec![],
                        }),
                        statement(InstructionKind::Borrow {
                            dst: 5,
                            src: 4,
                            unique: true,
                        }),
                    ],
                    Terminator::Call {
                        result: Some(6),
                        function: 15,
                        args: vec![move_operand(5), move_operand(3)],
                        normal: Edge {
                            target: 1,
                            args: vec![],
                        },
                    },
                ),
                block(1, vec![], Terminator::Unreachable),
            ],
            &types,
        );
        let aggregate_solution = solve(&FlowContext {
            function: &aggregate_caller,
            types: &types,
            locals: &aggregate_caller.flow.locals,
            loans: loan_table(&aggregate_caller, &types),
            array_calls: &summaries,
            strict: true,
            refine_enum_switches: true,
        })
        .expect("aggregate reference path is installed in the array slot");
        let aggregate_slots = &aggregate_solution.entries[&1].array_slots[&4];
        assert_eq!(
            aggregate_slots.reference_origins[&0].borrowed,
            Place::local(1)
        );

        let caller = exported_function(
            vec![UNIT, shared_i64, array, unique_array, UNIT],
            1,
            vec![
                block(
                    0,
                    vec![
                        statement(InstructionKind::Primitive {
                            dst: 2,
                            primitive: grandiose_vm::Primitive::ArrayEmpty,
                            args: vec![],
                        }),
                        statement(InstructionKind::Borrow {
                            dst: 3,
                            src: 2,
                            unique: true,
                        }),
                    ],
                    Terminator::Call {
                        result: Some(4),
                        function: 12,
                        args: vec![move_operand(3), move_operand(1)],
                        normal: Edge {
                            target: 1,
                            args: vec![],
                        },
                    },
                ),
                block(1, vec![], Terminator::Unreachable),
            ],
            &types,
        );
        let solution = solve(&FlowContext {
            function: &caller,
            types: &types,
            locals: &caller.flow.locals,
            loans: loan_table(&caller, &types),
            array_calls: &summaries,
            strict: true,
            refine_enum_switches: true,
        })
        .expect("wrapper call installs the transported reference origin");
        let slots = &solution.entries[&1].array_slots[&2];
        assert_eq!(slots.length, Some(1));
        assert_eq!(slots.reference_origins[&0].borrowed, Place::local(1));
        assert!(slots.reference_origins[&0].external);

        // A reference synthesized by borrowing a non-reference formal cannot
        // masquerade as a transported reference parameter.
        let mut opaque = exported_function(
            vec![UNIT, unique_array, I64, shared_i64, UNIT],
            2,
            vec![block(
                0,
                vec![
                    statement(InstructionKind::Borrow {
                        dst: 3,
                        src: 2,
                        unique: false,
                    }),
                    statement(InstructionKind::Primitive {
                        dst: 4,
                        primitive: grandiose_vm::Primitive::ArrayPushMove,
                        args: vec![move_operand(1), move_operand(3)],
                    }),
                ],
                Terminator::Return { value: None },
            )],
            &types,
        );
        opaque.declaration = 13;
        assert!(
            !array_call_summaries(
                &crate::compiler_mir::Program {
                    functions: vec![opaque]
                },
                &types
            )
            .contains_key(&13)
        );
    }

    #[test]
    fn array_slot_branch_joins_preserve_cleanup_and_enforce_barriers() {
        let mut types = Type::predefined();
        let array = types.len() as grandiose_vm::TypeId;
        types.push(Type::Array { element: UNIT });
        let unique_array = types.len() as grandiose_vm::TypeId;
        types.push(Type::RefUnique { referent: array });
        let arm = |id, statements| {
            block(
                id,
                statements,
                Terminator::Goto(Edge {
                    target: 3,
                    args: vec![],
                }),
            )
        };
        let blocks = vec![
            block(
                0,
                vec![
                    statement(InstructionKind::Primitive {
                        dst: 2,
                        primitive: grandiose_vm::Primitive::ArrayEmpty,
                        args: vec![],
                    }),
                    statement(InstructionKind::Const {
                        dst: 4,
                        value: grandiose_vm::Constant::Unit,
                    }),
                    statement(InstructionKind::Borrow {
                        dst: 3,
                        src: 2,
                        unique: true,
                    }),
                    statement(InstructionKind::Primitive {
                        dst: 5,
                        primitive: grandiose_vm::Primitive::ArrayPushMove,
                        args: vec![move_operand(3), move_operand(4)],
                    }),
                    statement(InstructionKind::Const {
                        dst: 6,
                        value: grandiose_vm::Constant::Usize(0),
                    }),
                ],
                Terminator::Switch {
                    discr: Operand {
                        register: 1,
                        mode: UseMode::Copy,
                    },
                    cases: vec![(
                        grandiose_vm::Constant::U32(0),
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
            arm(
                1,
                vec![
                    statement(InstructionKind::Borrow {
                        dst: 3,
                        src: 2,
                        unique: true,
                    }),
                    statement(InstructionKind::Primitive {
                        dst: 7,
                        primitive: grandiose_vm::Primitive::ArrayGetMove,
                        args: vec![
                            move_operand(3),
                            Operand {
                                register: 6,
                                mode: UseMode::Copy,
                            },
                        ],
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(7),
                    }),
                ],
            ),
            arm(2, vec![]),
            block(
                3,
                vec![statement(InstructionKind::Drop {
                    owner: move_operand(2),
                })],
                Terminator::Return { value: None },
            ),
        ];
        let mut function = exported_function(
            vec![
                UNIT,
                grandiose_vm::U32,
                array,
                unique_array,
                UNIT,
                UNIT,
                grandiose_vm::USIZE,
                UNIT,
            ],
            1,
            blocks,
            &types,
        );
        let solution = solve_function(&function, &types).expect("zero-use slot join");
        assert_eq!(
            solution.entries[&3].array_slots[&2].empty,
            BTreeSet::from([0])
        );

        function.flow.locals[2].drop_glue = DropGlueKind::Custom;
        let error = solve_function(&function, &types).unwrap_err();
        assert!(error.message.contains("custom Drop hook"), "{error:?}");
    }

    #[test]
    fn quantitative_use_joins_take_interval_hulls_and_lower_bounds_gate_drops() {
        let (types, pair, _) = pair_types();
        // A [1,1] owner destroyed before any use: destruction cannot
        // discharge a positive lower bound.
        let mut function = exported_function(
            vec![UNIT, pair],
            1,
            vec![block(
                0,
                vec![statement(InstructionKind::Drop {
                    owner: move_operand(1),
                })],
                Terminator::Return { value: None },
            )],
            &types,
        );
        function.flow.locals[1].use_interval = UseInterval {
            lower: 1,
            upper: Some(1),
        };
        let error = solve_function(&function, &types).unwrap_err();
        assert!(
            error
                .message
                .contains("positive Use lower bound 1 is discharged"),
            "{error:?}"
        );

        // Joining a used path with an unused path takes the interval hull;
        // dropping afterwards still cannot prove the lower bound met.
        let (types, pair, _) = pair_types();
        let arm = |id| {
            block(
                id,
                vec![],
                Terminator::Goto(Edge {
                    target: 3,
                    args: vec![],
                }),
            )
        };
        let mut joined = exported_function(
            vec![UNIT, pair, grandiose_vm::U32, pair],
            2,
            vec![
                block(
                    0,
                    vec![],
                    Terminator::Switch {
                        discr: Operand {
                            register: 2,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            grandiose_vm::Constant::U32(0),
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
                arm(1),
                arm(2),
                block(
                    3,
                    vec![statement(InstructionKind::Drop {
                        owner: move_operand(1),
                    })],
                    Terminator::Return { value: None },
                ),
            ],
            &types,
        );
        joined.flow.locals[1].use_interval = UseInterval {
            lower: 1,
            upper: None,
        };
        let error = solve_function(&joined, &types).unwrap_err();
        assert!(
            error
                .message
                .contains("positive Use lower bound 1 is discharged"),
            "{error:?}"
        );
    }

    #[test]
    fn transfers_beyond_the_declared_upper_bound_are_rejected() {
        let (mut types, pair, _) = pair_types();
        let wrapper = types.len() as grandiose_vm::TypeId;
        types.push(Type::Tuple {
            fields: vec![pair],
            copy: false,
        });
        let mut function = exported_function(
            vec![UNIT, pair, wrapper],
            1,
            vec![block(
                0,
                vec![statement(InstructionKind::Construct {
                    dst: 2,
                    ty: wrapper,
                    variant: None,
                    fields: vec![move_operand(1)],
                })],
                Terminator::Return { value: None },
            )],
            &types,
        );
        function.flow.locals[1].use_interval = UseInterval {
            lower: 0,
            upper: Some(0),
        };
        function.blocks[0]
            .statements
            .push(statement(InstructionKind::Drop {
                owner: move_operand(2),
            }));
        let error = solve_function(&function, &types).unwrap_err();
        assert!(
            error
                .message
                .contains("used more than its declared Use upper bound 0"),
            "{error:?}"
        );
    }

    #[test]
    fn shared_loans_overlap_but_unique_loans_conflict_and_expire_at_end() {
        let (types, shared, unique) = reference_types();
        // Two shared borrows of one owner are legal; both end before exit.
        let function = exported_function(
            vec![UNIT, I64, shared, shared],
            1,
            vec![block(
                0,
                vec![
                    statement(InstructionKind::Borrow {
                        dst: 2,
                        src: 1,
                        unique: false,
                    }),
                    statement(InstructionKind::Borrow {
                        dst: 3,
                        src: 1,
                        unique: false,
                    }),
                    statement(InstructionKind::EndBorrow { reference: 3 }),
                    statement(InstructionKind::EndBorrow { reference: 2 }),
                ],
                Terminator::Return { value: None },
            )],
            &types,
        );
        solve_function(&function, &types).expect("shared loans overlap legally");

        // A unique loan over a live shared loan of the same owner conflicts.
        let conflict = exported_function(
            vec![UNIT, I64, shared, unique],
            1,
            vec![block(
                0,
                vec![
                    statement(InstructionKind::Borrow {
                        dst: 2,
                        src: 1,
                        unique: false,
                    }),
                    statement(InstructionKind::Borrow {
                        dst: 3,
                        src: 1,
                        unique: true,
                    }),
                ],
                Terminator::Return { value: None },
            )],
            &types,
        );
        let error = solve_function(&conflict, &types).unwrap_err();
        assert!(
            error.message.contains("conflicts with the live"),
            "{error:?}"
        );

        // Disjoint unique loans of different owners are legal, and a loan
        // that expired at its last use frees the owner for consumption.
        let disjoint = exported_function(
            vec![UNIT, I64, I64, unique, unique],
            2,
            vec![block(
                0,
                vec![
                    statement(InstructionKind::Borrow {
                        dst: 3,
                        src: 1,
                        unique: true,
                    }),
                    statement(InstructionKind::Borrow {
                        dst: 4,
                        src: 2,
                        unique: true,
                    }),
                    statement(InstructionKind::EndBorrow { reference: 3 }),
                    statement(InstructionKind::EndBorrow { reference: 4 }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(1),
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(2),
                    }),
                ],
                Terminator::Return { value: None },
            )],
            &types,
        );
        solve_function(&disjoint, &types).expect("disjoint unique loans are legal");
    }

    #[test]
    fn array_borrow_primitive_transfers_source_loan_to_projected_result() {
        let mut types = Type::predefined();
        let array = types.len() as grandiose_vm::TypeId;
        types.push(Type::Array { element: I64 });
        let unique_array = types.len() as grandiose_vm::TypeId;
        types.push(Type::RefUnique { referent: array });
        let unique_element = types.len() as grandiose_vm::TypeId;
        types.push(Type::RefUnique { referent: I64 });
        let function = exported_function(
            vec![
                UNIT,
                array,
                unique_array,
                grandiose_vm::USIZE,
                unique_element,
            ],
            1,
            vec![block(
                0,
                vec![
                    statement(InstructionKind::Borrow {
                        dst: 2,
                        src: 1,
                        unique: true,
                    }),
                    statement(InstructionKind::Const {
                        dst: 3,
                        value: grandiose_vm::Constant::Usize(0),
                    }),
                    statement(InstructionKind::Primitive {
                        dst: 4,
                        primitive: Primitive::ArrayGetBorrowUnique,
                        args: vec![move_operand(2), move_operand(3)],
                    }),
                    statement(InstructionKind::EndBorrow { reference: 4 }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(1),
                    }),
                ],
                Terminator::Return { value: None },
            )],
            &types,
        );

        solve_function(&function, &types).unwrap();
    }

    #[test]
    fn edge_move_rebases_live_child_loan_to_transferred_parent() {
        let (types, _, unique) = reference_types();
        let function = exported_function(
            vec![
                UNIT,
                I64,
                unique,
                unique,
                grandiose_vm::U32,
                unique,
                unique,
                unique,
            ],
            1,
            vec![
                block(
                    0,
                    vec![
                        statement(InstructionKind::Borrow {
                            dst: 2,
                            src: 1,
                            unique: true,
                        }),
                        statement(InstructionKind::Reborrow {
                            dst: 3,
                            src: 2,
                            unique: true,
                        }),
                        statement(InstructionKind::Const {
                            dst: 4,
                            value: grandiose_vm::Constant::U32(0),
                        }),
                    ],
                    Terminator::Switch {
                        discr: Operand {
                            register: 4,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            grandiose_vm::Constant::U32(0),
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
                block(
                    1,
                    vec![statement(InstructionKind::EndBorrow { reference: 3 })],
                    Terminator::Goto(Edge {
                        target: 3,
                        args: vec![move_operand(2)],
                    }),
                ),
                block(
                    2,
                    vec![],
                    Terminator::Goto(Edge {
                        target: 4,
                        args: vec![move_operand(2), move_operand(3)],
                    }),
                ),
                BasicBlock {
                    id: 3,
                    params: vec![BlockParam {
                        register: 5,
                        ty: unique,
                        role: BlockParamRole::Ordinary,
                    }],
                    statements: vec![
                        statement(InstructionKind::EndBorrow { reference: 5 }),
                        statement(InstructionKind::Drop {
                            owner: move_operand(1),
                        }),
                    ],
                    terminator: Terminator::Return { value: None },
                },
                BasicBlock {
                    id: 4,
                    params: vec![
                        BlockParam {
                            register: 6,
                            ty: unique,
                            role: BlockParamRole::Ordinary,
                        },
                        BlockParam {
                            register: 7,
                            ty: unique,
                            role: BlockParamRole::Ordinary,
                        },
                    ],
                    statements: vec![statement(InstructionKind::EndBorrow { reference: 7 })],
                    terminator: Terminator::Goto(Edge {
                        target: 3,
                        args: vec![move_operand(6)],
                    }),
                },
            ],
            &types,
        );

        solve_function(&function, &types).unwrap();
    }

    #[test]
    fn consuming_a_borrowed_owner_is_rejected_until_the_loan_ends() {
        let (types, _, unique) = reference_types();
        let function = exported_function(
            vec![UNIT, I64, unique],
            1,
            vec![block(
                0,
                vec![
                    statement(InstructionKind::Borrow {
                        dst: 2,
                        src: 1,
                        unique: true,
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(1),
                    }),
                ],
                Terminator::Return { value: None },
            )],
            &types,
        );
        let error = solve_function(&function, &types).unwrap_err();
        assert!(
            error.message.contains("while the loan held by r2 is live"),
            "{error:?}"
        );
    }

    #[test]
    fn dereference_holes_must_agree_at_joins_and_close_before_end() {
        let (types, _, unique) = reference_types();
        let function = exported_function(
            vec![UNIT, unique, I64],
            1,
            vec![block(
                0,
                vec![
                    statement(InstructionKind::DerefMove { dst: 2, src: 1 }),
                    statement(InstructionKind::EndBorrow { reference: 1 }),
                ],
                Terminator::Return { value: None },
            )],
            &types,
        );
        let error = solve_function(&function, &types).unwrap_err();
        assert!(
            error.message.contains("while its referent is moved out"),
            "{error:?}"
        );

        let restored = exported_function(
            vec![UNIT, unique, I64],
            1,
            vec![block(
                0,
                vec![
                    statement(InstructionKind::DerefMove { dst: 2, src: 1 }),
                    statement(InstructionKind::DerefStore {
                        dst: 1,
                        src: move_operand(2),
                    }),
                    statement(InstructionKind::EndBorrow { reference: 1 }),
                ],
                Terminator::Return { value: None },
            )],
            &types,
        );
        solve_function(&restored, &types).expect("restored referent is legal");
    }

    #[test]
    fn perform_capture_facts_exactly_describe_residuals_and_cancellation_cleanup() {
        let (types, pair, _) = pair_types();
        let make = |capture: crate::compiler_mir::ContinuationCapture| {
            exported_function(
                vec![UNIT, pair, I64],
                1,
                vec![block(
                    0,
                    vec![statement(InstructionKind::ProjectMove {
                        dst: 2,
                        src: move_operand(1),
                        field: 0,
                    })],
                    Terminator::Perform {
                        result: None,
                        protocol: 0,
                        operation: 0,
                        payloads: vec![],
                        capture,
                        resume: None,
                    },
                )],
                &types,
            )
        };
        let exact = crate::compiler_mir::ContinuationCapture {
            captured_owners: vec![1, 2],
            captured_references: vec![],
            captured_residuals: vec![crate::compiler_mir::ResidualCapture {
                register: 1,
                initialized_fields: vec![false, true],
            }],
            cancellation_safe: true,
        };
        solve_function(&make(exact.clone()), &types)
            .expect("an exact residual capture is cancellation-safe");

        let mut missing = exact.clone();
        missing.captured_residuals.clear();
        let error = solve_function(&make(missing), &types).unwrap_err();
        assert!(error.message.contains("exactly describe"), "{error:?}");

        let mut duplicate = exact.clone();
        duplicate
            .captured_residuals
            .push(duplicate.captured_residuals[0].clone());
        let error = solve_function(&make(duplicate), &types).unwrap_err();
        assert!(
            error.message.contains("strictly sorted and duplicate-free"),
            "{error:?}"
        );

        let mut dishonest = exact;
        dishonest.cancellation_safe = false;
        let error = solve_function(&make(dishonest), &types).unwrap_err();
        assert!(error.message.contains("cancellation-safety"), "{error:?}");
    }

    #[test]
    fn cleanup_lists_destroy_owners_newest_first() {
        let mut types = Type::predefined();
        let pair = types.len() as grandiose_vm::TypeId;
        types.push(Type::Tuple {
            fields: vec![],
            copy: false,
        });
        let function = exported_function(
            vec![UNIT, pair, pair, pair],
            1,
            vec![block(
                0,
                vec![
                    statement(InstructionKind::Construct {
                        dst: 2,
                        ty: pair,
                        variant: None,
                        fields: vec![],
                    }),
                    statement(InstructionKind::Construct {
                        dst: 3,
                        ty: pair,
                        variant: None,
                        fields: vec![],
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(3),
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(2),
                    }),
                    statement(InstructionKind::Drop {
                        owner: move_operand(1),
                    }),
                ],
                Terminator::Return { value: None },
            )],
            &types,
        );
        let solution = solve_function(&function, &types).expect("ordered destruction");
        // Newest first at the fully live point.
        assert_eq!(solution.cleanup_lists[&0][2], vec![3, 2, 1]);
        // The trailing destroys consume exactly in that order.
        assert_eq!(solution.cleanup_lists[&0][3], vec![2, 1]);
        assert_eq!(solution.cleanup_lists[&0][4], vec![1]);
        assert!(solution.cleanup_lists[&0][5].is_empty());
    }

    #[test]
    fn exits_protect_transferred_arguments_and_reject_untransferred_owners() {
        let (types, pair, _) = pair_types();
        // Tail-calling with the owner moved as an argument is legal: the
        // argument is protected by having been transferred.
        let tail = exported_function(
            vec![UNIT, pair],
            1,
            vec![block(
                0,
                vec![],
                Terminator::TailCall {
                    function: 0,
                    args: vec![move_operand(1)],
                },
            )],
            &types,
        );
        solve_function(&tail, &types).expect("transferred tail argument is protected");

        // Leaving a must-use owner live across the tail call is rejected.
        let mut leftover = exported_function(
            vec![UNIT, pair],
            1,
            vec![block(
                0,
                vec![],
                Terminator::TailCall {
                    function: 0,
                    args: vec![],
                },
            )],
            &types,
        );
        leftover.flow.locals[1].use_interval = UseInterval {
            lower: 1,
            upper: None,
        };
        let error = solve_function(&leftover, &types).unwrap_err();
        assert!(
            error.message.contains("still live at tail call"),
            "{error:?}"
        );
    }

    #[test]
    fn leave_abandons_only_owners_and_loans_newer_than_its_label_baseline() {
        let mut types = Type::predefined();
        let pair = types.len() as grandiose_vm::TypeId;
        types.push(Type::Tuple {
            fields: vec![],
            copy: false,
        });
        let shared = types.len() as grandiose_vm::TypeId;
        types.push(Type::RefShared { referent: pair });
        let label = crate::compiler_mir::LabelId(0);
        let function = exported_function(
            vec![UNIT, pair, pair, shared, I64, I64],
            1,
            vec![
                block(
                    0,
                    vec![
                        statement(InstructionKind::LabelPush {
                            label,
                            result: 4,
                            target: 1,
                        }),
                        statement(InstructionKind::Construct {
                            dst: 2,
                            ty: pair,
                            variant: None,
                            fields: vec![],
                        }),
                        statement(InstructionKind::Borrow {
                            dst: 3,
                            src: 2,
                            unique: false,
                        }),
                        statement(InstructionKind::Const {
                            dst: 5,
                            value: grandiose_vm::Constant::I64(42),
                        }),
                    ],
                    Terminator::Leave {
                        label,
                        target: Edge {
                            target: 1,
                            args: vec![move_operand(5)],
                        },
                    },
                ),
                BasicBlock {
                    id: 1,
                    params: vec![BlockParam {
                        register: 4,
                        ty: I64,
                        role: BlockParamRole::ProtectedExitValue,
                    }],
                    statements: vec![statement(InstructionKind::Drop {
                        owner: move_operand(1),
                    })],
                    terminator: Terminator::Return {
                        value: Some(move_operand(4)),
                    },
                },
            ],
            &types,
        );
        let solution = solve_function(&function, &types)
            .expect("leave cleans the inner loan and owner but preserves its outer owner");
        let destination = &solution.entries[&1];
        assert!(!destination.loans.contains_key(&3));
        assert!(matches!(destination.regs[2], RegState::Consumed));
        assert!(matches!(destination.regs[1], RegState::Live));
        assert!(matches!(destination.regs[4], RegState::Live));

        let mut inactive = function;
        inactive.blocks[0].statements.remove(0);
        let error = solve_function(&inactive, &types).unwrap_err();
        assert!(error.message.contains("inactive label"), "{error:?}");
    }

    #[test]
    fn joins_reject_incompatible_label_stacks_but_ignore_unreachable_predecessors() {
        let types = Type::predefined();
        let label = crate::compiler_mir::LabelId(0);
        let mut mismatched = exported_function(
            vec![UNIT, grandiose_vm::U32, I64],
            1,
            vec![
                block(
                    0,
                    vec![],
                    Terminator::Switch {
                        discr: Operand {
                            register: 1,
                            mode: UseMode::Copy,
                        },
                        cases: vec![(
                            grandiose_vm::Constant::U32(0),
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
                block(
                    1,
                    vec![statement(InstructionKind::LabelPush {
                        label,
                        result: 2,
                        target: 3,
                    })],
                    Terminator::Goto(Edge {
                        target: 3,
                        args: vec![],
                    }),
                ),
                block(
                    2,
                    vec![],
                    Terminator::Goto(Edge {
                        target: 3,
                        args: vec![],
                    }),
                ),
                block(3, vec![], Terminator::Return { value: None }),
            ],
            &types,
        );
        let error = solve_function(&mismatched, &types).unwrap_err();
        assert!(error.message.contains("active label stacks"), "{error:?}");

        // The same malformed predecessor is harmless when no reachable edge
        // enters it: ownership joins consider executable predecessors only.
        mismatched.blocks[0].terminator = Terminator::Goto(Edge {
            target: 2,
            args: vec![],
        });
        let solution = solve_function(&mismatched, &types)
            .expect("an unreachable label predecessor cannot contaminate a join");
        assert!(!solution.entries.contains_key(&1));
    }

    #[test]
    fn block_parameter_transfers_preserve_owner_age_across_edges() {
        let (types, pair, _) = pair_types();
        let function = exported_function(
            vec![UNIT, pair, pair, pair],
            2,
            vec![
                block(
                    0,
                    vec![],
                    Terminator::Goto(Edge {
                        target: 1,
                        args: vec![move_operand(1)],
                    }),
                ),
                BasicBlock {
                    id: 1,
                    params: vec![BlockParam {
                        register: 3,
                        ty: pair,
                        role: BlockParamRole::Ordinary,
                    }],
                    statements: vec![
                        statement(InstructionKind::Drop {
                            owner: move_operand(2),
                        }),
                        statement(InstructionKind::Drop {
                            owner: move_operand(3),
                        }),
                    ],
                    terminator: Terminator::Return { value: None },
                },
            ],
            &types,
        );
        let solution = solve_function(&function, &types).expect("edge transfer");
        // r3 inherited r1's age (older than r2), so newest-first cleanup
        // lists r2 before r3 at the target block entry.
        assert_eq!(solution.cleanup_lists[&1][0], vec![2, 3]);
    }

    // Keep the unused mutability field exercised so the exported shape stays
    // honest about what the frontend records today.
    #[test]
    fn exported_local_facts_carry_storage_and_mutability() {
        let (types, pair, _) = pair_types();
        let fact = LocalFact::conservative(pair, &types[pair as usize]);
        assert_eq!(fact.storage, StorageClass::Ssa);
        assert_eq!(fact.mutability, Mutability::Immutable);
        assert!(!fact.use_interval.admits_zero_use());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(values: &[&str]) -> BTreeSet<String> {
        values.iter().map(|value| (*value).to_owned()).collect()
    }

    #[test]
    fn least_fixed_point_handles_diamond_joins_and_backedges() {
        let graph = PointGraph {
            points: BTreeMap::from([
                (
                    1,
                    Point {
                        successors: BTreeSet::from([2, 3]),
                        ..Point::default()
                    },
                ),
                (
                    2,
                    Point {
                        uses: names(&["left"]),
                        successors: BTreeSet::from([4]),
                        ..Point::default()
                    },
                ),
                (
                    3,
                    Point {
                        uses: names(&["right"]),
                        successors: BTreeSet::from([4]),
                        ..Point::default()
                    },
                ),
                (
                    4,
                    Point {
                        uses: names(&["joined"]),
                        successors: BTreeSet::from([5]),
                        ..Point::default()
                    },
                ),
                (
                    5,
                    Point {
                        uses: names(&["looped"]),
                        successors: BTreeSet::from([4]),
                        ..Point::default()
                    },
                ),
            ]),
        };
        let solution = graph.solve();
        assert_eq!(
            solution.live_out[&1],
            names(&["joined", "left", "looped", "right"])
        );
        assert_eq!(solution.live_in[&4], names(&["joined", "looped"]));
        assert_eq!(solution.live_out[&5], names(&["joined", "looped"]));
        assert_eq!(graph.solve(), solution);
    }

    #[test]
    fn kills_make_shadowing_a_point_local_transfer() {
        let graph = PointGraph {
            points: BTreeMap::from([
                (
                    1,
                    Point {
                        kills: names(&["value"]),
                        successors: BTreeSet::from([2]),
                        ..Point::default()
                    },
                ),
                (
                    2,
                    Point {
                        uses: names(&["value"]),
                        ..Point::default()
                    },
                ),
            ]),
        };
        let solution = graph.solve();
        assert!(!solution.live_in[&1].contains("value"));
        assert!(solution.live_out[&1].contains("value"));
    }
}
