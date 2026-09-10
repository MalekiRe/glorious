//! Execution-engine handoff at verified frame transitions.
//!
//! The interpreter and generated code have different implementations of local
//! computation. They share the program engine's actual activation, handler,
//! continuation and cleanup state. A generated segment stops before one of
//! these transitions; it does not execute a synchronous substitute for it.

use super::VmInstruction;

pub(super) fn is_frame_transition(instruction: &VmInstruction) -> bool {
    matches!(instruction,
        VmInstruction::Call { .. } | VmInstruction::CallOwned { .. }
        | VmInstruction::CallIndirect { .. } | VmInstruction::CallIndirectOwned { .. }
        | VmInstruction::TailCallOwned { .. } | VmInstruction::Return { .. }
        | VmInstruction::MakeCallable { .. } | VmInstruction::DestroyCallable { .. }
        | VmInstruction::MakeLabel { .. } | VmInstruction::Leave { .. }
        | VmInstruction::Perform { .. } | VmInstruction::PerformOwned { .. }
        | VmInstruction::InstallHandler { .. } | VmInstruction::InstallHandlerOwned { .. }
        | VmInstruction::UninstallHandler | VmInstruction::CompleteHandler { .. }
        | VmInstruction::ClaimEffectPayloads { .. } | VmInstruction::CaptureResumption { .. }
        | VmInstruction::RetainResumption { .. }
        | VmInstruction::Resume { .. } | VmInstruction::ResumeReturn { .. }
        | VmInstruction::ResumeSnapshot { .. } | VmInstruction::Forward | VmInstruction::Cancel
        | VmInstruction::StorageLive { .. } | VmInstruction::StorageDead { .. }
    )
}
