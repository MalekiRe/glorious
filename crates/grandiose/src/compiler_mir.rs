//! Ownership-aware register MIR for the bytecode compiler slice.

use grandiose_vm::bytecode::Protocol;
use grandiose_vm::{Constant, Primitive, Type, TypeId};

use crate::compiler_traits::HostImportRole;
use crate::{compiler_core::stable_fingerprint, span::Span};

#[path = "compiler_mir_analysis.rs"]
pub(crate) mod analyses;
#[path = "compiler_mir_mutation.rs"]
pub(crate) mod mutation;
#[path = "compiler_opt.rs"]
pub(crate) mod optimizer;

pub(crate) use optimizer::{FeatureBits, MirPhase};
pub use optimizer::{
    OptimizationLevel, OptimizationReport, PassId as OptimizationPass,
    PassOutcome as OptimizationPassOutcome, PassReport as OptimizationPassReport,
};

pub type Register = u32;

/// A MIR local. The compact bootstrap MIR keeps one unified local universe:
/// a `LocalId` is exactly a virtual register index into `register_types`.
pub type LocalId = Register;

macro_rules! mir_id {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
        pub struct $name(pub u32);

        impl $name {
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

mir_id!(
    /// Stable identity of one MIR control-flow block.
    BlockId
);
mir_id!(
    /// Identity of one statically distinguishable owned projection subtree.
    MovePathId
);
mir_id!(
    /// Identity of one lexical scope exported by the frontend.
    ScopeId
);
mir_id!(
    /// Identity of one loan issued by a borrow/reborrow instruction.
    LoanId
);
mir_id!(
    /// Identity of the live region of one loan. Bootstrap regions are 1:1
    /// with loans; the ID is kept distinct so a later nonlexical solver can
    /// share regions without changing fact shapes.
    RegionId
);
mir_id!(
    /// Identity of one source label region. Source labels remain gated in the
    /// bootstrap frontend, so this arena is normally empty; the identity and
    /// cleanup representation exist so label cleanup facts have a stable form.
    LabelId
);
mir_id!(
    /// Identity of one `Handle` site.
    HandlerSiteId
);
mir_id!(
    /// Identity of one `Perform` site.
    PerformSiteId
);
mir_id!(
    /// Identity of one `Resume`/`Cancel` site.
    ResumptionSiteId
);
mir_id!(
    /// Identity of one elaborated cleanup plan.
    CleanupPlanId
);
mir_id!(
    /// Identity of one source-information record (a span in the bootstrap).
    SourceInfoId
);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UseMode {
    Copy,
    Move,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Operand {
    pub register: Register,
    pub mode: UseMode,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Program {
    pub functions: Vec<Function>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Function {
    pub declaration: u32,
    pub name: String,
    pub params: Vec<TypeId>,
    pub result: TypeId,
    pub receiver_mode: Option<u32>,
    pub receiver_type: TypeId,
    pub no_return: bool,
    pub outward_protocols: Vec<u32>,
    pub register_types: Vec<TypeId>,
    pub entry: u32,
    pub blocks: Vec<BasicBlock>,
    /// Validation/optimization phase reached by this body.
    pub phase: MirPhase,
    /// Deterministically inferred body properties used to skip irrelevant passes.
    pub features: FeatureBits,
    /// Owners destroyed at normal return, newest first.
    pub return_cleanup: Vec<Register>,
    /// Frontend-exported ownership facts plus imported/elaborated arenas.
    pub flow: PlaceFlow,
    /// Analyses invalidated by the most recent mutation; see `analysis` bits.
    /// Phase validators recompute (never trust) any facts whose bit is set.
    pub invalid_analyses: u8,
}

/// Analysis invalidation bits ORed into `Function::invalid_analyses` by
/// checked mutations. A set bit means the corresponding derived facts must be
/// recomputed before use; passes must not silently retain stale facts.
pub mod analysis {
    pub const CFG: u8 = 1;
    pub const USES: u8 = 2;
    pub const FLOW: u8 = 4;
    pub const EFFECTS: u8 = 8;
    pub const VALUES: u8 = 16;
    pub const COST: u8 = 32;
    pub const ALL: u8 = CFG | USES | FLOW | EFFECTS | VALUES | COST;
}

#[derive(Clone, Debug, PartialEq)]
pub struct BasicBlock {
    pub id: u32,
    pub params: Vec<BlockParam>,
    pub statements: Vec<Instruction>,
    pub terminator: Terminator,
}

/// Typed region classification retained by the checked CFG editor. The compact
/// compatibility MIR still serializes blocks in one vector; this classification
/// prevents transformations from silently treating cleanup/control boundaries
/// as ordinary forwarding blocks.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BlockKind {
    Entry,
    Normal,
    Cleanup,
    Handler,
    Resumption,
    Label,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BlockParamRole {
    Ordinary,
    ProtectedExitValue,
    CallResult,
    ResumeResult,
}

#[derive(Clone, Debug, PartialEq)]
pub struct BlockParam {
    pub register: Register,
    pub ty: TypeId,
    pub role: BlockParamRole,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Edge {
    pub target: u32,
    pub args: Vec<Operand>,
}

/// Ownership facts for the continuation suspended by a `Perform` terminator.
///
/// Both register lists are canonical sets (strictly increasing), and
/// `captured_references` is a subset of `captured_owners`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResidualCapture {
    pub register: Register,
    /// One entry per runtime aggregate field; `true` means still initialized.
    pub initialized_fields: Vec<bool>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContinuationCapture {
    pub captured_owners: Vec<Register>,
    pub captured_references: Vec<Register>,
    pub captured_residuals: Vec<ResidualCapture>,
    pub cancellation_safe: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Terminator {
    Goto(Edge),
    Switch {
        discr: Operand,
        cases: Vec<(Constant, Edge)>,
        otherwise: Edge,
    },
    Return {
        value: Option<Operand>,
    },
    Call {
        result: Option<Register>,
        function: u32,
        args: Vec<Operand>,
        normal: Edge,
    },
    CallSelf {
        result: Option<Register>,
        args: Vec<Operand>,
        normal: Edge,
    },
    CallKnownReceiver {
        result: Option<Register>,
        function: u32,
        receiver: Operand,
        args: Vec<Operand>,
        normal: Edge,
    },
    HostCall {
        result: Option<Register>,
        import: HostImportRole,
        args: Vec<Operand>,
        normal: Edge,
    },
    CallIndirect {
        result: Option<Register>,
        callable: Operand,
        /// Optimizer-proven exact descriptor target. The callable operand is
        /// retained because it still carries the receiver/capture environment.
        known_function: Option<u32>,
        receiver_mode: u32,
        cleanup_callable: bool,
        args: Vec<Operand>,
        normal: Edge,
    },
    Handle {
        result: Register,
        handler: Operand,
        body: Operand,
        normal: Edge,
    },
    Perform {
        result: Option<Register>,
        protocol: u32,
        operation: u32,
        payloads: Vec<Operand>,
        capture: ContinuationCapture,
        resume: Option<Edge>,
    },
    Resume {
        result: Register,
        resumption: Operand,
        receiver_mode: u32,
        value: Operand,
        normal: Edge,
    },
    /// Resume a captured continuation as this frame's terminal action. The
    /// continuation returns directly to this frame's caller.
    TailResume {
        resumption: Operand,
        receiver_mode: u32,
        value: Operand,
    },
    Cancel {
        result: Register,
        resumption: Operand,
        normal: Edge,
    },
    TailCall {
        function: u32,
        args: Vec<Operand>,
    },
    TailCallSelf {
        args: Vec<Operand>,
    },
    TailCallKnownReceiver {
        function: u32,
        receiver: Operand,
        args: Vec<Operand>,
    },
    TailCallIndirect {
        callable: Operand,
        /// Optimizer-proven exact descriptor target. This is a fact only; MIR
        /// and bytecode continue to invoke the callable receiver.
        known_function: Option<u32>,
        receiver_mode: u32,
        args: Vec<Operand>,
    },
    /// Transfer directly to an active typed label destination. The protected
    /// value is installed into the destination's result register by the VM;
    /// cleanup for scopes between this block and the label is attached through
    /// `CleanupEdge::Leave`. The target carries exactly one argument (the
    /// protected value) to a `ProtectedExitValue` block parameter. Keeping the
    /// destination as an ordinary edge makes CFG rewrites retain and remap the
    /// join even though bytecode lowering emits `Leave` rather than an ordinary
    /// edge transfer.
    Leave {
        label: LabelId,
        target: Edge,
    },
    /// Terminate immediately without running ordinary scope cleanup. This is
    /// the MIR form of the frozen VM abort operation, not an effect perform.
    Abort {
        message: Option<String>,
    },
    Unreachable,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Instruction {
    pub span: Span,
    pub kind: InstructionKind,
}

#[derive(Clone, Debug, PartialEq)]
pub enum InstructionKind {
    Const {
        dst: Register,
        value: Constant,
    },
    Copy {
        dst: Register,
        src: Operand,
    },
    Move {
        dst: Register,
        src: Operand,
    },
    Borrow {
        dst: Register,
        src: Register,
        unique: bool,
    },
    ProjectBorrow {
        dst: Register,
        src: Register,
        field: u32,
        unique: bool,
    },
    Reborrow {
        dst: Register,
        src: Register,
        unique: bool,
    },
    DerefCopy {
        dst: Register,
        src: Register,
    },
    /// Move the initialized referent out through a live unique reference. The
    /// reference/loan remains live and records an uninitialized referent.
    DerefMove {
        dst: Register,
        src: Register,
    },
    /// Store a moved value through a live unique reference whose referent is
    /// uninitialized. The reference/loan remains live and becomes initialized.
    DerefStore {
        dst: Register,
        src: Operand,
    },
    EndBorrow {
        reference: Register,
    },
    Construct {
        dst: Register,
        ty: TypeId,
        variant: Option<u32>,
        fields: Vec<Operand>,
    },
    ProjectCopy {
        dst: Register,
        src: Operand,
        field: u32,
    },
    ProjectMove {
        dst: Register,
        src: Operand,
        field: u32,
    },
    Deconstruct {
        src: Register,
    },
    EnumTag {
        dst: Register,
        src: Register,
    },
    Primitive {
        dst: Register,
        primitive: Primitive,
        args: Vec<Operand>,
    },
    MakeCallable {
        dst: Register,
        callable_type: TypeId,
        function: u32,
        captures: Vec<Operand>,
    },
    MakeHandler {
        dst: Register,
        handler_def: u32,
        clauses: Vec<Operand>,
    },
    MakeHandlerShared {
        dst: Register,
        handler_def: u32,
        functions: Vec<u32>,
        captures: Vec<Operand>,
    },
    /// Construct a runtime binding environment from its moved payload fields.
    MakeBindingPack {
        dst: Register,
        binding_type: TypeId,
        payloads: Vec<Operand>,
    },
    /// Activate one typed label destination. `target` is the destination block
    /// reached by `Leave`; ordinary execution continues in the same block.
    LabelPush {
        label: LabelId,
        result: Register,
        target: u32,
    },
    /// Deactivate the innermost label after its body completes normally.
    LabelPop {
        label: LabelId,
    },
    Drop {
        owner: Operand,
    },
}

/// Ownership-relevant use of a register by one MIR instruction.
///
/// Keeping this structural fact beside the instruction algebra prevents each
/// analysis from growing its own exhaustive match. `Consume` includes both
/// move-mode operands and the bare-register operations which end an owned MIR
/// state (`EndBorrow` and `Deconstruct`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RegisterUseKind {
    Inspect,
    Consume,
}

impl InstructionKind {
    pub(crate) fn destination(&self) -> Option<Register> {
        match self {
            Self::Const { dst, .. }
            | Self::Copy { dst, .. }
            | Self::Move { dst, .. }
            | Self::Borrow { dst, .. }
            | Self::ProjectBorrow { dst, .. }
            | Self::Reborrow { dst, .. }
            | Self::DerefCopy { dst, .. }
            | Self::DerefMove { dst, .. }
            | Self::Construct { dst, .. }
            | Self::ProjectCopy { dst, .. }
            | Self::ProjectMove { dst, .. }
            | Self::EnumTag { dst, .. }
            | Self::Primitive { dst, .. }
            | Self::MakeCallable { dst, .. }
            | Self::MakeHandler { dst, .. }
            | Self::MakeHandlerShared { dst, .. }
            | Self::MakeBindingPack { dst, .. } => Some(*dst),
            Self::EndBorrow { .. }
            | Self::DerefStore { .. }
            | Self::Deconstruct { .. }
            | Self::LabelPush { .. }
            | Self::LabelPop { .. }
            | Self::Drop { .. } => None,
        }
    }

    pub(crate) fn destination_mut(&mut self) -> Option<&mut Register> {
        match self {
            Self::Const { dst, .. }
            | Self::Copy { dst, .. }
            | Self::Move { dst, .. }
            | Self::Borrow { dst, .. }
            | Self::ProjectBorrow { dst, .. }
            | Self::Reborrow { dst, .. }
            | Self::DerefCopy { dst, .. }
            | Self::DerefMove { dst, .. }
            | Self::Construct { dst, .. }
            | Self::ProjectCopy { dst, .. }
            | Self::ProjectMove { dst, .. }
            | Self::EnumTag { dst, .. }
            | Self::Primitive { dst, .. }
            | Self::MakeCallable { dst, .. }
            | Self::MakeHandler { dst, .. }
            | Self::MakeHandlerShared { dst, .. }
            | Self::MakeBindingPack { dst, .. } => Some(dst),
            Self::EndBorrow { .. }
            | Self::DerefStore { .. }
            | Self::Deconstruct { .. }
            | Self::LabelPush { .. }
            | Self::LabelPop { .. }
            | Self::Drop { .. } => None,
        }
    }

    pub(crate) fn for_each_register_use(&self, mut visit: impl FnMut(Register, RegisterUseKind)) {
        fn operand(value: &Operand, visit: &mut impl FnMut(Register, RegisterUseKind)) {
            visit(
                value.register,
                match value.mode {
                    UseMode::Copy => RegisterUseKind::Inspect,
                    UseMode::Move => RegisterUseKind::Consume,
                },
            );
        }
        match self {
            Self::Copy { src, .. } | Self::Move { src, .. } | Self::Drop { owner: src } => {
                operand(src, &mut visit)
            }
            Self::Borrow { src, .. }
            | Self::ProjectBorrow { src, .. }
            | Self::Reborrow { src, .. }
            | Self::DerefCopy { src, .. }
            | Self::DerefMove { src, .. }
            | Self::EnumTag { src, .. } => visit(*src, RegisterUseKind::Inspect),
            Self::EndBorrow { reference } | Self::Deconstruct { src: reference } => {
                visit(*reference, RegisterUseKind::Consume)
            }
            Self::DerefStore { dst, src } => {
                visit(*dst, RegisterUseKind::Inspect);
                operand(src, &mut visit);
            }
            Self::Construct { fields, .. }
            | Self::Primitive { args: fields, .. }
            | Self::MakeCallable {
                captures: fields, ..
            }
            | Self::MakeHandler {
                clauses: fields, ..
            }
            | Self::MakeHandlerShared {
                captures: fields, ..
            }
            | Self::MakeBindingPack {
                payloads: fields, ..
            } => fields.iter().for_each(|field| operand(field, &mut visit)),
            // A projection move empties one field, not the entire aggregate
            // register. It is therefore a use of the base for whole-register
            // analyses, not a complete consumption.
            Self::ProjectCopy { src, .. } | Self::ProjectMove { src, .. } => {
                visit(src.register, RegisterUseKind::Inspect)
            }
            Self::Const { .. } | Self::LabelPush { .. } | Self::LabelPop { .. } => {}
        }
    }
}

/// Storage class of a local.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StorageClass {
    /// Defined exactly once; the common case for compact-MIR registers.
    Ssa,
    /// Source storage that may be legally re-stored after compiler-mediated
    /// emptying (ABI parameter places reconstructed by pattern fallback).
    Place,
    /// Erased zero-runtime evidence; generates no bytecode register.
    Erased,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mutability {
    Immutable,
    Mutable,
}

/// Ownership category of the value a local holds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OwnershipCategory {
    Owned,
    SharedRef,
    UniqueRef,
    CopyValue,
    ZstErased,
}

/// Why a local exists.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LocalKind {
    Receiver,
    Parameter(u32),
    Capture,
    User,
    Temporary,
    BlockParameter,
    DropFlag,
}

/// Drop-glue information for a local's runtime type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DropGlueKind {
    /// No owned substructure requires destruction work.
    None,
    /// Structural destruction only (fields in reverse declaration order).
    Structural,
    /// A custom `Drop` hook observes the fully initialized owner first.
    Custom,
}

/// Initialization state of a local at function entry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InitAtEntry {
    Uninitialized,
    Initialized,
}

/// A declared quantitative `Use` interval. `upper == None` means unbounded.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UseInterval {
    pub lower: u32,
    pub upper: Option<u32>,
}

impl UseInterval {
    pub const UNRESTRICTED: Self = Self {
        lower: 0,
        upper: None,
    };

    pub fn contains(self, uses: u32) -> bool {
        uses >= self.lower && self.upper.is_none_or(|upper| uses <= upper)
    }

    pub fn admits_zero_use(self) -> bool {
        self.lower == 0
    }
}

/// One fact per local, exported by the frontend at lowering time. Registers
/// allocated later by optimizer passes receive conservative `Temporary` facts
/// derived from their runtime type when the flow is re-imported.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LocalFact {
    pub ty: TypeId,
    pub storage: StorageClass,
    pub mutability: Mutability,
    pub ownership: OwnershipCategory,
    pub use_interval: UseInterval,
    pub drop_glue: DropGlueKind,
    pub initial: InitAtEntry,
    pub scope: ScopeId,
    pub kind: LocalKind,
    pub source: SourceInfoId,
}

/// One place projection step.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Projection {
    /// Read/write through a live reference.
    Deref,
    /// Tuple, struct, or enum-payload field. `variant` carries the proven
    /// active variant for enum payload projections.
    Field { variant: Option<u32>, field: u32 },
    /// Dynamically selected array element; conservatively overlaps every
    /// dynamic projection of the same base.
    DynamicIndex,
}

/// A place: a base local plus a projection path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Place {
    pub base: LocalId,
    pub projection: Vec<Projection>,
}

impl Place {
    pub fn local(base: LocalId) -> Self {
        Self {
            base,
            projection: Vec::new(),
        }
    }

    pub fn field(base: LocalId, variant: Option<u32>, field: u32) -> Self {
        Self {
            base,
            projection: vec![Projection::Field { variant, field }],
        }
    }

    /// Exact conservative overlap: two places overlap unless a statically
    /// distinct field step proves them disjoint.
    pub fn overlaps(&self, other: &Self) -> bool {
        if self.base != other.base {
            return false;
        }
        for (left, right) in self.projection.iter().zip(&other.projection) {
            // Only statically distinct field steps prove disjointness;
            // deref/dynamic steps never do.
            if let (
                Projection::Field {
                    variant: left_variant,
                    field: left_field,
                },
                Projection::Field {
                    variant: right_variant,
                    field: right_field,
                },
            ) = (left, right)
                && left_variant == right_variant
                && left_field != right_field
            {
                return false;
            }
        }
        true
    }

    pub fn disjoint(&self, other: &Self) -> bool {
        !self.overlaps(other)
    }

    /// True when `self` is `other` or a strict ancestor of it.
    pub fn contains(&self, other: &Self) -> bool {
        self.base == other.base
            && self.projection.len() <= other.projection.len()
            && self
                .projection
                .iter()
                .zip(&other.projection)
                .all(|(left, right)| matches!((left, right), (a, b) if a == b))
    }
}

/// One move-path node: a statically distinguishable owned projection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MovePathFact {
    pub parent: Option<MovePathId>,
    pub base: LocalId,
    pub projection: Option<Projection>,
    pub children: Vec<MovePathId>,
}

/// Deterministic interning arena for the move-path tree of one body.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MovePaths {
    pub facts: Vec<MovePathFact>,
}

impl MovePaths {
    /// Intern the root path of a local.
    pub fn root(&mut self, base: LocalId) -> MovePathId {
        if let Some(existing) = self.find_root(base) {
            return existing;
        }
        let id = MovePathId(self.facts.len() as u32);
        self.facts.push(MovePathFact {
            parent: None,
            base,
            projection: None,
            children: Vec::new(),
        });
        id
    }

    pub fn find_root(&self, base: LocalId) -> Option<MovePathId> {
        self.facts
            .iter()
            .position(|fact| fact.parent.is_none() && fact.base == base)
            .map(|index| MovePathId(index as u32))
    }

    /// Intern a child of `parent` reached through `projection`.
    pub fn child(&mut self, parent: MovePathId, projection: Projection) -> MovePathId {
        if let Some(existing) = self.facts[parent.index()]
            .children
            .iter()
            .copied()
            .find(|child| self.facts[child.index()].projection == Some(projection))
        {
            return existing;
        }
        let id = MovePathId(self.facts.len() as u32);
        let base = self.facts[parent.index()].base;
        self.facts.push(MovePathFact {
            parent: Some(parent),
            base,
            projection: Some(projection),
            children: Vec::new(),
        });
        self.facts[parent.index()].children.push(id);
        id
    }

    pub fn place(&self, id: MovePathId) -> Place {
        let mut projection = Vec::new();
        let mut at = Some(id);
        let mut base = 0;
        while let Some(current) = at {
            let fact = &self.facts[current.index()];
            if let Some(step) = fact.projection {
                projection.push(step);
            }
            base = fact.base;
            at = fact.parent;
        }
        projection.reverse();
        Place { base, projection }
    }

    /// True when `ancestor` is `descendant` or on its parent chain.
    pub fn is_ancestor(&self, ancestor: MovePathId, descendant: MovePathId) -> bool {
        let mut at = Some(descendant);
        while let Some(current) = at {
            if current == ancestor {
                return true;
            }
            at = self.facts[current.index()].parent;
        }
        false
    }

    /// Exact conservative disjointness. Sibling fields are disjoint, while
    /// dynamic indices and dereferences continue to overlap unless a field
    /// step above them already proves otherwise.
    pub fn disjoint(&self, left: MovePathId, right: MovePathId) -> bool {
        self.place(left).disjoint(&self.place(right))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LoanKind {
    Shared,
    Unique,
}

/// One loan created by a `Borrow`, `ProjectBorrow`, or `Reborrow`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoanFact {
    pub kind: LoanKind,
    /// Register holding the reference value while the loan is live.
    pub reference: LocalId,
    /// The borrowed place: root owner register plus field path.
    pub borrowed: Place,
    /// Reborrow parent; the parent loan is suspended while this loan lives.
    pub parent: Option<LoanId>,
    pub region: RegionId,
    pub issued_block: u32,
    pub source: SourceInfoId,
}

/// One exported lexical scope. The bootstrap frontend destroys scope-local
/// owners inline, so it exports a single function scope; the tree shape is
/// kept so finer scopes can be exported without changing fact shapes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScopeFact {
    pub parent: Option<ScopeId>,
    /// Owners introduced in this scope, in initialization order.
    pub owners: Vec<LocalId>,
}

/// One gated source-label region.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabelFact {
    pub result_type: TypeId,
    pub scope: ScopeId,
    pub destination: u32,
}

/// One `Handle` site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HandlerSiteFact {
    pub block: u32,
    pub scope: ScopeId,
}

/// One `Perform` site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PerformSiteFact {
    pub block: u32,
    pub resumptive: bool,
    /// Frame cleanup for terminal abandonment; attached by `ElaborateCleanup`.
    pub frame_cleanup: Option<CleanupPlanId>,
}

/// One `Resume`/`Cancel` site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResumptionSiteFact {
    pub block: u32,
    pub cancel: bool,
    /// Cleanup run when the continuation is cancelled; attached by
    /// `ElaborateCleanup` for cancel sites.
    pub cancellation_cleanup: Option<CleanupPlanId>,
}

/// The source ownership snapshot and effect row at an indirect-call
/// suspension boundary.  The ownership solver independently reconstructs the
/// snapshot before trusting the frontend's cancellation decision.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IndirectCallSiteFact {
    pub block: u32,
    pub outward_protocols: Vec<u32>,
    pub capture: ContinuationCapture,
}

/// One source-lowered control-flow join. Incoming block ids are canonical and
/// let PlaceFlow reject a frontend/CFG mismatch before ownership dataflow.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JoinSiteFact {
    pub block: u32,
    pub incoming: Vec<u32>,
}

/// One drop flag: a compiler-created `u32` local guarding conditional
/// initialization of `owner`. The VM `Empty` register state realizes the flag
/// at runtime, so no separate flag value is serialized.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DropFlagFact {
    pub flag: LocalId,
    pub owner: LocalId,
    /// A conditionally initialized aggregate field. `None` governs the whole
    /// owner, preserving the original live/dead drop-flag form.
    pub field: Option<u32>,
}

/// One ordered cleanup action.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CleanupAction {
    /// End the static loan; the surviving reference value is already dead.
    EndBorrow(LoanId),
    /// Destroy a whole initialized owner: custom hook first, then initialized
    /// fields in reverse declaration order, then storage release.
    Destroy(LocalId),
    /// Destroy the still-initialized remainder of a residual aggregate shell.
    DestroyResidual {
        local: LocalId,
        initialized_fields: Vec<bool>,
    },
    /// Conditionally destroy through a drop flag; at runtime the VM `Empty`
    /// state skips uninitialized owners.
    DestroyIf { local: LocalId, flag: LocalId },
}

/// The abandoning or scope-exiting edge a cleanup plan is attached to.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CleanupEdge {
    Return { block: u32 },
    TailCall { block: u32 },
    TerminalPerform { block: u32 },
    Cancel { block: u32 },
    Leave { block: u32, label: LabelId },
}

/// One elaborated cleanup plan. Actions are in execution order (newest owner
/// first); every destruction already carries `Use<[0,0]>` evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CleanupPlanFact {
    pub edge: CleanupEdge,
    pub source_scope: ScopeId,
    pub target_scope: ScopeId,
    pub actions: Vec<CleanupAction>,
    /// Values moved across the edge and therefore protected from cleanup.
    pub protected: Vec<LocalId>,
}

/// Where a body's ownership facts came from.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum FlowProvenance {
    /// The frontend exported the facts during lowering; the import phase
    /// validates them strictly against the instruction stream and every
    /// ownership obligation is enforced.
    Exported,
    /// The facts were synthesized conservatively from the instruction stream
    /// (hand-assembled MIR); structural loan discipline is still enforced but
    /// exported-only obligations are not. This is the documented migration
    /// bridge, never used by the compiler pipeline itself.
    #[default]
    Synthesized,
}

/// Frontend-exported ownership facts plus the derived arenas filled in by the
/// `ImportAndValidatePlaceFlow` and `ElaborateCleanup` phases.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PlaceFlow {
    pub provenance: FlowProvenance,
    /// One fact per register at export time. May be shorter than
    /// `register_types` after optimizer passes allocate registers; the import
    /// bridge extends it with conservative temporary facts.
    pub locals: Vec<LocalFact>,
    pub scopes: Vec<ScopeFact>,
    pub loans: Vec<LoanFact>,
    pub labels: Vec<LabelFact>,
    pub handlers: Vec<HandlerSiteFact>,
    pub performs: Vec<PerformSiteFact>,
    pub resumptions: Vec<ResumptionSiteFact>,
    pub indirect_calls: Vec<IndirectCallSiteFact>,
    pub joins: Vec<JoinSiteFact>,
    pub drop_flags: Vec<DropFlagFact>,
    /// Move paths discovered/validated during import.
    pub move_paths: MovePaths,
    /// Cleanup plans built by `ElaborateCleanup`.
    pub cleanup_plans: Vec<CleanupPlanFact>,
    /// Span table backing `SourceInfoId`.
    pub sources: Vec<Span>,
}

impl LocalFact {
    /// Conservative fact for a register whose provenance is unknown (allocated
    /// by an optimizer pass after export). Claims are derived from the runtime
    /// type only and never grant more than the type itself proves.
    pub fn conservative(ty: TypeId, descriptor: &Type) -> Self {
        let representation = descriptor.representation();
        let ownership = match representation {
            Type::RefShared { .. } => OwnershipCategory::SharedRef,
            Type::RefUnique { .. } => OwnershipCategory::UniqueRef,
            _ if descriptor.claimed_duplicable() => OwnershipCategory::CopyValue,
            _ => OwnershipCategory::Owned,
        };
        Self {
            ty,
            storage: StorageClass::Ssa,
            mutability: Mutability::Immutable,
            ownership,
            use_interval: UseInterval {
                lower: u32::from(!descriptor.claimed_zero_use_allowed()),
                upper: if descriptor.claimed_duplicable() {
                    None
                } else {
                    Some(1)
                },
            },
            drop_glue: DropGlueKind::Structural,
            initial: InitAtEntry::Uninitialized,
            scope: ScopeId(0),
            kind: LocalKind::Temporary,
            source: SourceInfoId(0),
        }
    }
}

impl PlaceFlow {
    pub fn source(&mut self, span: Span) -> SourceInfoId {
        if let Some(last) = self.sources.last()
            && *last == span
        {
            return SourceInfoId(self.sources.len() as u32 - 1);
        }
        let id = SourceInfoId(self.sources.len() as u32);
        self.sources.push(span);
        id
    }

    pub fn span_of(&self, source: SourceInfoId) -> Span {
        self.sources
            .get(source.index())
            .copied()
            .unwrap_or_default()
    }

    pub fn plan_for(&self, edge: &CleanupEdge) -> Option<(CleanupPlanId, &CleanupPlanFact)> {
        self.cleanup_plans
            .iter()
            .position(|plan| &plan.edge == edge)
            .map(|index| (CleanupPlanId(index as u32), &self.cleanup_plans[index]))
    }

    pub fn canonical_summary(&self) -> String {
        format!(
            "{:?} locals={} scopes={} loans={} labels={} handlers={} performs={} \
             resumptions={} indirect_calls={} joins={} flags={} move_paths={} plans={}",
            self.provenance,
            self.locals.len(),
            self.scopes.len(),
            self.loans.len(),
            self.labels.len(),
            self.handlers.len(),
            self.performs.len(),
            self.resumptions.len(),
            self.indirect_calls.len(),
            self.joins.len(),
            self.drop_flags.len(),
            self.move_paths.facts.len(),
            self.cleanup_plans.len(),
        )
    }
}

impl Program {
    /// Validate the explicit continuation facts before they are erased by
    /// bytecode lowering.
    pub fn validate_continuation_captures(
        &self,
        types: &[Type],
        protocols: &[Protocol],
    ) -> Result<(), String> {
        fn canonical(registers: &[Register]) -> bool {
            registers.windows(2).all(|pair| pair[0] < pair[1])
        }

        for function in &self.functions {
            for block in &function.blocks {
                let Terminator::Perform {
                    result,
                    protocol,
                    operation,
                    payloads,
                    capture,
                    ..
                } = &block.terminator
                else {
                    continue;
                };
                let site = format!("function `{}` block {}", function.name, block.id);
                if !canonical(&capture.captured_owners) || !canonical(&capture.captured_references)
                {
                    return Err(format!(
                        "{site} has non-canonical continuation capture registers"
                    ));
                }
                if !capture
                    .captured_residuals
                    .windows(2)
                    .all(|pair| pair[0].register < pair[1].register)
                {
                    return Err(format!(
                        "{site} has non-canonical residual capture registers"
                    ));
                }
                for residual in &capture.captured_residuals {
                    if capture
                        .captured_owners
                        .binary_search(&residual.register)
                        .is_err()
                    {
                        return Err(format!(
                            "{site} records residual fields for uncaptured r{}",
                            residual.register
                        ));
                    }
                    let ty = function.register_types[residual.register as usize];
                    let fields = match types.get(ty as usize).map(Type::representation) {
                        Some(Type::Tuple { fields, .. }) => fields.clone(),
                        Some(Type::Struct { fields, .. }) => {
                            fields.iter().map(|field| field.ty).collect()
                        }
                        _ => {
                            return Err(format!(
                                "{site} records residual fields for non-aggregate r{}",
                                residual.register
                            ));
                        }
                    };
                    if fields.len() != residual.initialized_fields.len()
                        || residual
                            .initialized_fields
                            .iter()
                            .all(|initialized| *initialized)
                    {
                        return Err(format!(
                            "{site} has invalid residual field state for r{}",
                            residual.register
                        ));
                    }
                }
                for &register in &capture.captured_owners {
                    if register as usize >= function.register_types.len() {
                        return Err(format!(
                            "{site} captures out-of-range owner register r{register}"
                        ));
                    }
                    if payloads.iter().any(|payload| payload.register == register)
                        || result.is_some_and(|result| result == register)
                    {
                        return Err(format!(
                            "{site} captures transferred or result register r{register}"
                        ));
                    }
                }
                for &register in &capture.captured_references {
                    if capture.captured_owners.binary_search(&register).is_err() {
                        return Err(format!(
                            "{site} captures reference r{register} without its owner"
                        ));
                    }
                    let ty = function.register_types[register as usize];
                    if !matches!(
                        types.get(ty as usize).map(Type::representation),
                        Some(Type::RefShared { .. } | Type::RefUnique { .. })
                    ) {
                        return Err(format!(
                            "{site} marks non-reference register r{register} as a captured reference"
                        ));
                    }
                }
                let cancellation_safe = capture.captured_owners.iter().all(|&register| {
                    let ty = function.register_types[register as usize];
                    if let Ok(index) = capture
                        .captured_residuals
                        .binary_search_by_key(&register, |residual| residual.register)
                    {
                        let residual = &capture.captured_residuals[index];
                        let fields = match types[ty as usize].representation() {
                            Type::Tuple { fields, .. } => fields.clone(),
                            Type::Struct { fields, .. } => {
                                fields.iter().map(|field| field.ty).collect()
                            }
                            _ => return false,
                        };
                        fields.into_iter().zip(&residual.initialized_fields).all(
                            |(field, initialized)| {
                                !*initialized || types[field as usize].claimed_zero_use_allowed()
                            },
                        )
                    } else {
                        types
                            .get(ty as usize)
                            .is_some_and(Type::claimed_zero_use_allowed)
                    }
                });
                if capture.cancellation_safe != cancellation_safe {
                    return Err(format!(
                        "{site} has inconsistent continuation cancellation safety"
                    ));
                }
                let cancellable = protocols
                    .get(*protocol as usize)
                    .and_then(|protocol| protocol.operations.get(*operation as usize))
                    .is_some_and(|operation| {
                        !operation.terminal && operation.resumption_lower == 0
                    });
                if cancellable && !capture.cancellation_safe {
                    return Err(format!(
                        "{site} may cancel a continuation with non-discardable owners"
                    ));
                }
            }
        }
        Ok(())
    }

    pub fn canonical_text(&self) -> String {
        let mut output = String::new();
        use std::fmt::Write as _;
        for function in &self.functions {
            writeln!(
                output,
                "fn#{} {:?} {:?}->t{} receiver={:?}:t{} no_return={} outward={:?} regs={:?} phase={:?} features={:#x} cleanup={:?}",
                function.declaration,
                function.name,
                function.params,
                function.result,
                function.receiver_mode,
                function.receiver_type,
                function.no_return,
                function.outward_protocols,
                function.register_types,
                function.phase,
                function.features.bits(),
                function.return_cleanup
            )
            .unwrap();
            writeln!(
                output,
                "  flow {} invalid={:#x}",
                function.flow.canonical_summary(),
                function.invalid_analyses
            )
            .unwrap();
            for block in &function.blocks {
                writeln!(output, "  block#{} params={:?}", block.id, block.params).unwrap();
                for instruction in &block.statements {
                    writeln!(
                        output,
                        "    @{}..{} {:?}",
                        instruction.span.start, instruction.span.end, instruction.kind
                    )
                    .unwrap();
                }
                writeln!(output, "    -> {:?}", block.terminator).unwrap();
            }
        }
        output
    }

    pub fn fingerprint(&self) -> u64 {
        stable_fingerprint(self.canonical_text().as_bytes())
    }
}

#[cfg(test)]
mod tests {
    use grandiose_vm::bytecode::{Operation, Protocol, Signature};
    use grandiose_vm::{I64, Type, UNIT};

    use super::*;

    #[test]
    fn move_path_disjointness_is_conservative_for_variants_and_dynamic_indices() {
        let mut paths = MovePaths::default();
        let root = paths.root(1);
        let dynamic_left = paths.child(root, Projection::DynamicIndex);
        // Interning gives an identical dynamic projection the same path.
        let dynamic_right = paths.child(root, Projection::DynamicIndex);
        assert!(!paths.disjoint(dynamic_left, dynamic_right));

        let first = paths.child(
            root,
            Projection::Field {
                variant: None,
                field: 0,
            },
        );
        let second = paths.child(
            root,
            Projection::Field {
                variant: None,
                field: 1,
            },
        );
        assert!(paths.disjoint(first, second));

        let first_dynamic = paths.child(first, Projection::DynamicIndex);
        let second_dynamic = paths.child(second, Projection::DynamicIndex);
        assert!(paths.disjoint(first_dynamic, second_dynamic));

        // Payload paths of mutually exclusive enum variants are not sibling
        // storage locations that can be independently live. Keeping them
        // overlapping prevents a stale variant proof from justifying a
        // second partial move after a variant change.
        let variant_zero = paths.child(
            root,
            Projection::Field {
                variant: Some(0),
                field: 0,
            },
        );
        let variant_one = paths.child(
            root,
            Projection::Field {
                variant: Some(1),
                field: 0,
            },
        );
        assert!(!paths.disjoint(variant_zero, variant_one));
    }

    fn program(capture: ContinuationCapture) -> Program {
        Program {
            functions: vec![Function {
                declaration: 0,
                name: "capture".into(),
                params: vec![UNIT, I64],
                result: UNIT,
                receiver_mode: None,
                receiver_type: UNIT,
                no_return: false,
                outward_protocols: vec![0],
                register_types: vec![UNIT, I64],
                entry: 0,
                blocks: vec![BasicBlock {
                    id: 0,
                    params: vec![],
                    statements: vec![],
                    terminator: Terminator::Perform {
                        result: None,
                        protocol: 0,
                        operation: 0,
                        payloads: vec![],
                        capture,
                        resume: None,
                    },
                }],
                phase: MirPhase::Raw,
                features: FeatureBits::empty(),
                return_cleanup: vec![],
                flow: PlaceFlow::default(),
                invalid_analyses: 0,
            }],
        }
    }

    fn terminal_protocol() -> Vec<Protocol> {
        vec![Protocol {
            display_name: "Abort".into(),
            type_arguments: vec![],
            operations: vec![Operation {
                name: "abort".into(),
                payload_signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                result_type: UNIT,
                resumption_lower: 0,
                resumption_upper: Some(0),
                terminal: true,
            }],
        }]
    }

    #[test]
    fn canonical_mir_and_fingerprint_include_continuation_capture_facts() {
        let first = program(ContinuationCapture {
            captured_owners: vec![0],
            captured_references: vec![],
            captured_residuals: vec![],
            cancellation_safe: true,
        });
        let repeated = first.clone();
        let different = program(ContinuationCapture {
            captured_owners: vec![],
            captured_references: vec![],
            captured_residuals: vec![],
            cancellation_safe: true,
        });

        assert_eq!(first.canonical_text(), repeated.canonical_text());
        assert_eq!(first.fingerprint(), repeated.fingerprint());
        assert_ne!(first.fingerprint(), different.fingerprint());
        assert!(first.canonical_text().contains("captured_owners: [0]"));
    }

    #[test]
    fn continuation_validation_rejects_noncanonical_and_false_facts() {
        let mut types = Type::predefined();
        let protocols = terminal_protocol();
        let unsorted = program(ContinuationCapture {
            captured_owners: vec![1, 0],
            captured_references: vec![],
            captured_residuals: vec![],
            cancellation_safe: false,
        });
        assert!(
            unsorted
                .validate_continuation_captures(&types, &protocols)
                .unwrap_err()
                .contains("non-canonical")
        );

        let restricted = types.len() as TypeId;
        types.push(Type::I64.restricted(false, false));
        let mut false_safety = program(ContinuationCapture {
            captured_owners: vec![1],
            captured_references: vec![],
            captured_residuals: vec![],
            cancellation_safe: true,
        });
        false_safety.functions[0].register_types[1] = restricted;
        assert!(
            false_safety
                .validate_continuation_captures(&types, &protocols)
                .unwrap_err()
                .contains("cancellation safety")
        );
    }

    #[test]
    fn continuation_validation_rejects_invalid_reference_and_payload_overlap() {
        let types = Type::predefined();
        let protocols = terminal_protocol();
        let invalid_reference = program(ContinuationCapture {
            captured_owners: vec![1],
            captured_references: vec![1],
            captured_residuals: vec![],
            cancellation_safe: false,
        });
        assert!(
            invalid_reference
                .validate_continuation_captures(&types, &protocols)
                .unwrap_err()
                .contains("non-reference")
        );

        let mut overlap = program(ContinuationCapture {
            captured_owners: vec![1],
            captured_references: vec![],
            captured_residuals: vec![],
            cancellation_safe: false,
        });
        let Terminator::Perform { payloads, .. } = &mut overlap.functions[0].blocks[0].terminator
        else {
            unreachable!()
        };
        payloads.push(Operand {
            register: 1,
            mode: UseMode::Move,
        });
        assert!(
            overlap
                .validate_continuation_captures(&types, &protocols)
                .unwrap_err()
                .contains("transferred")
        );
    }
}
