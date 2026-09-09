//! Concrete storage, executable ABI and dynamic-frame contracts. Runtime MIR
//! consumes Cleanup MIR directly and retains no earlier phase body.
use crate::mir::*;
use crate::mir_storage::{MirSourceStorageScopeId, MirSourceStorageTables};
use crate::placeflow::PlaceBindingOrigin;
use crate::runtime_manifest::FloatPrimitive;
use crate::{CoreId, DefKey, InstanceKey, Mutability, PlaceFlow, PrimitiveRole, Safety, Type};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

mod control;
pub(crate) mod destruction;
pub(crate) mod emission;
mod lower;
mod operation;
mod program;
mod proof_erasure;
mod protocol;
mod storage;
#[cfg(test)]
pub(crate) mod tests;
mod validate;
pub use operation::RuntimeOperation;
pub use program::RuntimeProgram;
pub use protocol::{
    RuntimeArgument, RuntimeFrame, RuntimePassing, RuntimeSlot, RuntimeSlotClass, RuntimeTransfer,
    RuntimeTransferKind,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeError(pub String);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeBlock {
    pub scope: MirScopeId,
    pub parameters: Vec<MirLocal>,
    pub instructions: Vec<RuntimeOperation>,
    pub terminator: RuntimeTerminator,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RuntimeTerminator {
    Goto {
        target: MirBlockId,
        arguments: Vec<MirLocal>,
    },
    Leave {
        label: MirLabelId,
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
    /// Outgoing carriers are protected and all frame cleanup has run before
    /// this terminator. There is no local result slot or return continuation.
    TailCall { callee: DefKey, arguments: Vec<MirLocal> },
    Unreachable,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeMir {
    pub(crate) safety: crate::Safety,
    pub(crate) unsafe_execution: bool,
    pub(crate) definition: DefKey,
    pub(crate) nominal_copy_descriptors: Vec<MirNominalCopyDescriptor>,
    pub(crate) captures: u32,
    pub(crate) parameters: Vec<MirLocal>,
    pub(crate) locals: Vec<MirLocalDecl>,
    pub(crate) result: Type,
    pub(crate) control: MirControlTables,
    pub(crate) entry: MirBlockId,
    pub(crate) blocks: Vec<RuntimeBlock>,
    pub(crate) frame: RuntimeFrame,
}
impl RuntimeMir {
    pub fn definition(&self) -> DefKey {
        self.definition
    }
    pub fn blocks(&self) -> &[RuntimeBlock] {
        &self.blocks
    }
    pub fn locals(&self) -> &[MirLocalDecl] {
        &self.locals
    }
    pub fn frame(&self) -> &RuntimeFrame {
        &self.frame
    }
}

fn destination(operation: &RuntimeOperation) -> Option<MirLocal> {
    operation.destination()
}
fn references(operation: &RuntimeOperation) -> Vec<MirLocal> {
    operation.references()
}
