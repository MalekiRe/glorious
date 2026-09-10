//! Receiver authority reconstructed from executable capture access.
//!
//! Physical capture ownership does not decide invocation mode. In particular
//! an owned non-Copy capture can be observed through a shared receiver. The
//! actual instruction graph must neither mutate it under shared access nor
//! vacate it under either borrowed form.

use super::*;

fn carries_reference(function: &VmFunction, ty: &VmType) -> bool {
    !vm_tail_owned_type(ty, &function.nominal_copy_descriptors, &mut vec![])
}

fn carries_unique(function: &VmFunction, ty: &VmType, active: &mut BTreeSet<DefKey>) -> bool {
    match ty {
        VmType::Reference { unique, referent } => *unique || carries_unique(function, referent, active),
        VmType::Tuple(fields) => fields.iter().any(|ty| carries_unique(function, ty, active)),
        VmType::Array(ty) | VmType::FixedArray { element: ty, .. } | VmType::StaticData { element: ty, .. } => carries_unique(function, ty, active),
        VmType::Nominal { definition, .. } => {
            if !active.insert(*definition) { return false; }
            let value = nominal_layout_descriptor(function, ty).map_or(true, |layout|
                layout.variants.iter().flatten().any(|ty| carries_unique(function, ty, active)));
            active.remove(definition);
            value
        }
        VmType::Generic(_) => true,
        _ => false,
    }
}

/// Compute a monotone may-alias graph over all executable paths. No branch,
/// loop, handler or source-only annotation can hide a capture access. Values
/// which merely contain scalar copies do not alias the capture's storage.
fn aliases(function: &VmFunction) -> Vec<bool> {
    let mut aliases = function.registers.iter().enumerate().map(|(index, ty)|
        index < function.captures as usize && carries_reference(function, ty)).collect::<Vec<_>>();
    loop {
        let mut changed = false;
        for instruction in &function.instructions {
            let Some(dst) = native_storage::instruction_result(instruction) else { continue; };
            if aliases.get(dst as usize) != Some(&false)
                || !(matches!(instruction, VmInstruction::PrepareInvocation { .. })
                    || function.registers.get(dst as usize).is_some_and(|ty| carries_reference(function, ty))) { continue; }
            let mut tainted = false;
            native_storage::visit_locals(instruction, |value| {
                if value != dst { tainted |= aliases.get(value as usize) == Some(&true); }
            });
            if let VmInstruction::Borrow { src, .. } | VmInstruction::PrepareInvocation { src, .. } = instruction {
                tainted |= *src < function.captures;
            }
            if tainted { aliases[dst as usize] = true; changed = true; }
        }
        if !changed { return aliases; }
    }
}

pub(super) fn is_execution_boundary(instruction: &VmInstruction) -> bool {
    matches!(instruction, VmInstruction::Call { .. } | VmInstruction::CallOwned { .. }
        | VmInstruction::CallIndirect { .. } | VmInstruction::CallIndirectOwned { .. }
        | VmInstruction::CallPrepared { .. }
        | VmInstruction::HostCall { .. } | VmInstruction::HostCallOwned { .. }
        | VmInstruction::Perform { .. } | VmInstruction::PerformOwned { .. }
        | VmInstruction::TailCallOwned { .. } | VmInstruction::Return { .. }
        | VmInstruction::Forward | VmInstruction::Leave { .. })
}

pub(super) fn verify_claim(function: &VmFunction, shared: bool, unique: bool, captures_intact: bool) -> Result<(), VmArtifactError> {
    if !shared && !unique || function.captures == 0 { return Ok(()); }
    let aliases = aliases(function);
    let captured = |value: u32| value < function.captures;
    let aliases_capture = |value: u32| aliases.get(value as usize) == Some(&true);
    let mut permits_shared = true;
    let mut permits_unique = captures_intact;
    for instruction in &function.instructions {
        if native_storage::instruction_result(instruction).is_some_and(captured) {
            permits_shared = false;
        }
        if let Some(arguments) = instruction.consumed_arguments() {
            permits_shared &= !arguments.iter().copied().any(captured);
        }
        match instruction {
            VmInstruction::Move { src, .. } | VmInstruction::DestroyCallable { value: src, .. }
            | VmInstruction::StorageDead { local: src, .. } | VmInstruction::DestroyIf { local: src, .. }
                if captured(*src) => permits_shared = false,
            VmInstruction::TakeProjection { base, .. } | VmInstruction::TakeArrayElement { value: base, .. }
                if captured(*base) => { permits_shared = false; permits_unique = false; }
            VmInstruction::Borrow { src, unique: true, .. } if captured(*src) || aliases_capture(*src) => permits_shared = false,
            VmInstruction::DerefStore { reference, .. } if aliases_capture(*reference) => permits_shared = false,
            VmInstruction::DerefMove { reference, .. } if aliases_capture(*reference) => {
                // A reusable environment may not expose a moved-out resident
                // to its owner. This also catches aliased projected references.
                permits_shared = false; permits_unique = false;
            }
            VmInstruction::Call { arguments, .. } | VmInstruction::CallOwned { arguments, .. }
            | VmInstruction::TailCallOwned { arguments, .. }
            | VmInstruction::HostCall { arguments, .. } | VmInstruction::HostCallOwned { arguments, .. }
            | VmInstruction::Perform { arguments, .. } | VmInstruction::PerformOwned { arguments, .. } => {
                permits_shared &= !arguments.iter().any(|argument| aliases_capture(*argument)
                    && function.registers.get(*argument as usize).is_some_and(|ty| carries_unique(function, ty, &mut BTreeSet::new())));
            }
            VmInstruction::CallIndirect { callee, arguments, .. } | VmInstruction::CallIndirectOwned { callee, arguments, .. }
            | VmInstruction::CallPrepared { callee, arguments, .. } => {
                if captured(*callee) || aliases_capture(*callee) {
                    match function.registers.get(*callee as usize) {
                        Some(VmType::Reference { unique: false, .. }) => {},
                        Some(VmType::Reference { unique: true, .. }) => permits_shared = false,
                        _ => { permits_shared = false; permits_unique = false; },
                    }
                }
                permits_shared &= !arguments.iter().any(|argument| aliases_capture(*argument)
                    && function.registers.get(*argument as usize).is_some_and(|ty| carries_unique(function, ty, &mut BTreeSet::new())));
            }
            VmInstruction::MemoryIntrinsic { primitive: MemoryPrimitive::Forget, arguments, .. }
                if arguments.iter().copied().any(captured) => { permits_shared = false; permits_unique = false; }
            _ => {}
        }
    }
    if (shared && !permits_shared) || (unique && !permits_unique) {
        return Err(VmArtifactError::InvalidCallableEnvironment {
            message: "borrowed callable authority is not established by its executable capture accesses",
        });
    }
    Ok(())
}
