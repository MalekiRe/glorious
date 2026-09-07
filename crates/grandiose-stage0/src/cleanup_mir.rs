//! Concrete destruction and abandoning-edge contracts, before storage/ABI
//! lowering. This product owns its CFG; it retains no preceding MIR body.
use crate::control_mir::*;
use crate::ownership_mir::{
    Loan, LoanId, Owner, OwnerId, OwnerKind, OwnershipAggregate, OwnershipOperand,
    OwnershipSuccessor, ValueTransfer,
};
use crate::specialized_mir::{SpecializedCallTarget, SpecializedComputation, SpecializedLayout};
use crate::{DefKey, InstanceKey, PlaceFlow, Safety, Type};
use std::collections::{BTreeMap, BTreeSet};

mod flags;
mod graph;
mod inventory;
mod lower;
mod program;
mod replay;
mod resumptions;
#[cfg(test)]
pub(crate) mod tests;
mod validate;
pub use program::CleanupProgram;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DestructionField {
    pub ty: Type,
    pub glue: Option<InstanceKey>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DestructionShape {
    Leaf,
    Callable,
    Tuple(Vec<DestructionField>),
    Nominal {
        definition: DefKey,
        is_enum: bool,
        variants: Vec<Vec<DestructionField>>,
    },
    Array {
        element: Type,
        glue: InstanceKey,
    },
}
/// Custom hook first, then only initialized active fields in reverse order.
/// References and raw pointers never contribute owned structural children.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DestructionProgram {
    pub ty: Type,
    pub hook: Option<InstanceKey>,
    pub shape: DestructionShape,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CaptureDestruction {
    pub index: u32,
    pub ty: Type,
    pub destructor: DefKey,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct CleanupPlanId(pub u32);
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct DropFlagId(pub u32);

/// Logical initialization state, not a machine boolean. Runtime MIR chooses
/// storage for it; whole moves and projection takes clear the same state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DropFlag {
    pub place: ControlPlace,
    pub ty: Type,
    pub initialized_on_entry: bool,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FlagTransition {
    pub flag: DropFlagId,
    pub initialized: bool,
}
/// A move clears before ownership transfers; successful construction arms
/// afterwards. These logical writes share storage with initialized fields.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FlagEffects {
    pub before: Vec<FlagTransition>,
    pub after: Vec<FlagTransition>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CleanupAction {
    EndLoan(LoanId),
    Destroy {
        flag: DropFlagId,
        destructor: DefKey,
    },
    StorageDead(DropFlagId),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CleanupPlan {
    pub actions: Vec<CleanupAction>,
    pub protected: Vec<ControlValue>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CleanupInstruction {
    pub scope: ControlScopeId,
    pub destination: ControlValue,
    pub operation: CleanupOperation,
    pub flags: FlagEffects,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CleanupTerminator {
    pub control: CleanupControl,
    pub operands: Vec<OwnershipOperand>,
    pub successors: Vec<OwnershipSuccessor>,
    /// Run after preparing protected outgoing operands, before transferring.
    pub cleanup: CleanupPlanId,
    /// Retained, not executed before lookup. Used on dynamic abandonment.
    pub cancellation: CleanupPlanId,
    pub flags: FlagEffects,
    pub edge_flags: Vec<FlagEffects>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CleanupBlock {
    pub parameters: Vec<ControlValue>,
    pub instructions: Vec<CleanupInstruction>,
    pub terminator: CleanupTerminator,
}
#[derive(Clone, Debug)]
pub struct CleanupClosure {
    pub environment: crate::CaptureEnvironment,
    pub destructor: Option<DefKey>,
    pub cleanup: Vec<CaptureDestruction>,
    pub body: Box<CleanupMir>,
}
#[derive(Clone, Debug)]
pub struct CleanupMir {
    pub(crate) definition: DefKey,
    pub(crate) instance: InstanceKey,
    pub(crate) safety: Safety,
    pub(crate) unsafe_execution: bool,
    pub(crate) parameters: Vec<ControlValue>,
    pub(crate) values: Vec<ControlValueDecl>,
    pub(crate) result: Type,
    pub(crate) scopes: Vec<ControlScope>,
    pub(crate) entry: ControlBlockId,
    pub(crate) labels: Vec<ControlLabel>,
    pub(crate) handlers: Vec<ControlHandler>,
    pub(crate) closures: Vec<CleanupClosure>,
    pub(crate) source_bindings: BTreeMap<crate::placeflow::PlaceBindingOrigin, ControlValue>,
    pub(crate) source_flow: PlaceFlow,
    pub(crate) owners: Vec<Owner>,
    pub(crate) loans: Vec<Loan>,
    pub(crate) blocks: Vec<CleanupBlock>,
    pub(crate) symbols: BTreeSet<ControlValue>,
    pub(crate) aliases: BTreeMap<ControlValue, ControlValue>,
    pub(crate) layouts: Vec<SpecializedLayout>,
    pub(crate) flags: Vec<DropFlag>,
    pub(crate) plans: Vec<CleanupPlan>,
    pub(crate) frame_cleanup: CleanupPlanId,
    /// Lexical cleanup in the surviving destination frame of a label call.
    pub(crate) label_cleanup: Vec<CleanupPlanId>,
    /// Surviving-frame cleanup after a clause abandons its continuation.
    pub(crate) clause_cleanup: BTreeMap<ControlBlockId, CleanupPlanId>,
    /// Fully selected, recursively closed hook and structural programs.
    pub(crate) destruction: std::sync::Arc<BTreeMap<DefKey, crate::destruction::Plan>>,
    pub(crate) native_operations: BTreeMap<ControlBlockId, Vec<(Type, Option<DefKey>)>>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CleanupError(pub String);
impl CleanupMir {
    pub fn definition(&self) -> DefKey {
        self.definition
    }
    pub fn blocks(&self) -> &[CleanupBlock] {
        &self.blocks
    }
    pub fn plans(&self) -> &[CleanupPlan] {
        &self.plans
    }
    pub fn flags(&self) -> &[DropFlag] {
        &self.flags
    }
    pub fn frame_cleanup(&self) -> CleanupPlanId {
        self.frame_cleanup
    }
    pub fn closures(&self) -> &[CleanupClosure] {
        &self.closures
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CleanupOperation {
    Compute(SpecializedComputation),
    Construct {
        aggregate: OwnershipAggregate,
        fields: Vec<OwnershipOperand>,
    },
    Transfer {
        value: ControlValue,
        mode: ValueTransfer,
    },
    Read(ControlValue),
    ReadReference(ControlValue),
    ReadPlace {
        place: ControlPlace,
        mode: ValueTransfer,
    },
    Project {
        place: ControlPlace,
        base: ControlValue,
        index: u32,
        field_count: u32,
        mode: ValueTransfer,
    },
    Borrow(LoanId),
    MovePlace(ControlPlace),
    Replace {
        place: ControlPlace,
        value: ControlValue,
        mode: ValueTransfer,
        cleanup: CleanupPlanId,
    },
    Destroy(CleanupPlanId),
    RunCleanup {
        scope: ControlScopeId,
        result: ControlValue,
        mode: ValueTransfer,
        plan: CleanupPlanId,
    },
    Capture {
        closure: ControlClosureId,
        captures: Vec<(ControlValue, crate::CaptureMode)>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CleanupControl {
    Goto(ControlEdge),
    SwitchBool {
        condition: ControlValue,
        on_true: ControlEdge,
        on_false: ControlEdge,
    },
    Invoke {
        callee: ControlValue,
        target: SpecializedCallTarget,
        arguments: Vec<ControlValue>,
        result: ControlValue,
        contract: crate::evaluation_mir::EvaluationCallContract,
        continuation: Option<ControlBlockId>,
    },
    Return(ControlValue),
    Unreachable,
    Transfer(ControlTransfer),
}
