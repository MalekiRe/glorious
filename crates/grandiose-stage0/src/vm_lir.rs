//! Final compiler language: concrete VM registers, machine leaves and symbolic
//! block targets. No source body, interface, destruction planner or MIR body is
//! retained. Layout/relocation is the only transformation left before bytecode.
use crate::vm_backend::{
    CandidateVmProgram, STAGE0_VM_SCHEMA, VmArtifactError, VmCaptureEnvironment, VmCleanupProof,
    VmFrameDrop, VmFunction, VmInstruction, VmNominalCopyDescriptor, VmType,
};
use crate::{DefKey, Digest, Safety};
use std::collections::{BTreeMap, BTreeSet};

mod emission;
mod lower;
#[cfg(test)]
mod tests;
mod validate;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct VmLirBlockId(pub u32);

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VmLirTerminator {
    Jump(VmLirBlockId),
    Branch {
        condition: u32,
        then_target: VmLirBlockId,
        else_target: VmLirBlockId,
    },
    Return(u32),
    Leave {
        brand_owner: DefKey,
        brand_label: u32,
        handler_depth: u32,
        target: VmLirBlockId,
        arguments: Vec<u32>,
        destinations: Vec<u32>,
        cleanup: VmCleanupProof,
    },
    Trap,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmLirBlock {
    // InstallHandler/MakeLabel target operands are block IDs, never PCs.
    // The remaining leaves are exactly the independently verified VM schema.
    pub(crate) instructions: Vec<VmInstruction>,
    pub(crate) terminator: VmLirTerminator,
}
impl VmLirBlock {
    pub fn instructions(&self) -> &[VmInstruction] {
        &self.instructions
    }
    pub fn terminator(&self) -> &VmLirTerminator {
        &self.terminator
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmLirFunction {
    pub(crate) definition: DefKey,
    pub(crate) safety: Safety,
    pub(crate) unsafe_execution: bool,
    pub(crate) nominal_copy_descriptors: Vec<VmNominalCopyDescriptor>,
    pub(crate) captures: u32,
    pub(crate) parameters: u32,
    pub(crate) registers: Vec<VmType>,
    pub(crate) result: VmType,
    pub(crate) returns: bool,
    pub(crate) frame_cleanup: Vec<VmFrameDrop>,
    pub(crate) entry: VmLirBlockId,
    pub(crate) blocks: Vec<VmLirBlock>,
}
impl VmLirFunction {
    pub fn definition(&self) -> DefKey {
        self.definition
    }
    pub fn registers(&self) -> &[VmType] {
        &self.registers
    }
    pub fn blocks(&self) -> &[VmLirBlock] {
        &self.blocks
    }
    pub fn fingerprint(&self) -> Digest {
        Digest::of_parts([
            b"grandiose-stage0-vm-lir-v1".as_slice(),
            format!("{self:?}").as_bytes(),
        ])
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VmLirProgram {
    entry: DefKey,
    functions: BTreeMap<DefKey, VmLirFunction>,
    callable_environments: BTreeMap<DefKey, VmCaptureEnvironment>,
}
impl VmLirProgram {
    pub fn entry(&self) -> DefKey {
        self.entry
    }
    pub fn functions(&self) -> &BTreeMap<DefKey, VmLirFunction> {
        &self.functions
    }

    /// The same independent machine checker validates the compiler product and
    /// decoded bytecode. Symbolic target/layout checks happen before relocation.
    pub fn validate(&self) -> Result<(), VmArtifactError> {
        self.validate_closed_metadata()?;
        crate::vm_backend::verify_program(self.emit()?).map(|_| ())
    }

    /// Mechanical symbol relocation and artifact-envelope construction only.
    /// Publication must still pass independent bytecode verification.
    pub fn emit(&self) -> Result<CandidateVmProgram, VmArtifactError> {
        let functions = self
            .functions
            .iter()
            .map(|(key, body)| {
                if *key != body.definition {
                    return Err(invalid("VM LIR function identity mismatch"));
                }
                Ok((*key, body.emit()?))
            })
            .collect::<Result<BTreeMap<_, _>, VmArtifactError>>()?;
        let mut candidate = CandidateVmProgram {
            schema: STAGE0_VM_SCHEMA,
            runtime_manifest: None,
            host_capabilities: crate::vm_backend::reachable_host_capabilities(
                self.entry, &functions,
            ),
            entry: self.entry,
            functions,
            callable_environments: self.callable_environments.clone(),
            fingerprint: Digest::of_parts([b"unsealed-vm-lir".as_slice()]),
        };
        candidate.fingerprint = candidate.computed_fingerprint();
        Ok(candidate)
    }
}

fn invalid(message: &'static str) -> VmArtifactError {
    VmArtifactError::MalformedEncoding { message }
}
