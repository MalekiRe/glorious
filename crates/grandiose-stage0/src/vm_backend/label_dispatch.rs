//! Exact local label transfers through executable forwarding shims.
//!
//! A may-label taint is not authority to invoke an arbitrary callable as a
//! label. These must facts name a destination in this exact activation, and
//! only survive direct value transfers through storage whose address cannot
//! be exposed. Dispatch re-enters the normal verifier worklist: it does not
//! declare the destination or its cleanup harmless.

use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct LocalLabel {
    target: u32,
    destination: u32,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Shim {
    label: u32,
    payload: u32,
}

fn label_disposer(function: &VmFunction) -> bool {
    if function.parameters != 1 || function.captures != 0 { return false; }
    matches!(function.instructions.as_slice(), [
        VmInstruction::DeclareResult { result: VmType::Unit, returns: true },
        VmInstruction::DestroyCallable { dst, value: 0 },
        VmInstruction::ConstUnit { dst: unit },
        VmInstruction::Return { value },
    ] if *dst != 0 && *unit != 0 && unit == value)
}

/// Prove a shim's complete executable behavior, including frame destruction.
/// No name, source annotation, or merely nonreturning ABI selects this rule.
pub(super) fn shims(functions: &BTreeMap<DefKey, VmFunction>) -> BTreeMap<DefKey, Shim> {
    functions.iter().filter_map(|(key, function)| {
        recognize(function, functions).map(|shim| (*key, shim))
    }).collect()
}

fn recognize(function: &VmFunction, functions: &BTreeMap<DefKey, VmFunction>) -> Option<Shim> {
    if function.parameters != 2 || function.captures != 0
        || !matches!(function.instructions.first(), Some(VmInstruction::DeclareResult { result: VmType::Unit, returns: false })) {
        return None;
    }
    let mut origins = vec![None; function.registers.len()];
    let mut live = vec![false; function.registers.len()];
    for index in 0..2 { *origins.get_mut(index)? = Some(index as u32); *live.get_mut(index)? = true; }
    for (pc, instruction) in function.instructions.iter().enumerate() {
        match instruction {
            VmInstruction::DeclareResult { .. } | VmInstruction::DeclareFrameCleanup { .. } => {}
            VmInstruction::SetDropFlag { flag, .. } => {
                *origins.get_mut(*flag as usize)? = None;
                *live.get_mut(*flag as usize)? = true;
            }
            VmInstruction::Copy { dst, src } | VmInstruction::Move { dst, src } => {
                if !*live.get(*src as usize)? { return None; }
                let origin = *origins.get(*src as usize)?;
                if matches!(instruction, VmInstruction::Move { .. }) {
                    live[*src as usize] = false;
                    origins[*src as usize] = None;
                }
                *origins.get_mut(*dst as usize)? = origin;
                *live.get_mut(*dst as usize)? = true;
            }
            VmInstruction::CallIndirectOwned { callee, arguments, .. } => {
                if !matches!(&function.instructions[pc + 1..], [VmInstruction::Trap]) { return None; }
                let [argument] = arguments.as_slice() else { return None; };
                if !*live.get(*callee as usize)? || !*live.get(*argument as usize)? { return None; }
                let label = (*origins.get(*callee as usize)?)?;
                let payload = (*origins.get(*argument as usize)?)?;
                if label == payload { return None; }
                live[*argument as usize] = false;
                // The runtime retires the transferred payload, then destroys
                // every other live declared owner in the shim's frame.
                for action in declared_frame_cleanup(function).ok()? {
                    if !*live.get(action.owner as usize)? { continue; }
                    if *origins.get(action.owner as usize)? != Some(label)
                        || !functions.get(&action.destructor).is_some_and(label_disposer) { return None; }
                }
                return Some(Shim { label, payload });
            }
            _ => return None,
        }
    }
    None
}

/// Unrelated native mutations cannot replace an unexposed register. Exclude
/// label destinations as well: an ancestor rejoin can write those externally.
fn private_register(function: &VmFunction, register: u32) -> bool {
    !function.instructions.iter().any(|instruction| match instruction {
        VmInstruction::Borrow { src, reborrow: false, .. } => *src == register,
        VmInstruction::MakeLabel { destination, .. } => *destination == register,
        _ => false,
    })
}

pub(super) fn produced(
    function: &VmFunction, instruction: &VmInstruction, states: &VerifierState,
) -> Option<(u32, Option<LocalLabel>)> {
    let (destination, label) = match instruction {
        VmInstruction::MakeLabel { dst, target, destination, .. }
            if states.handlers.is_empty() && !states.resuming =>
                (*dst, Some(LocalLabel { target: *target, destination: *destination })),
        VmInstruction::Copy { dst, src } | VmInstruction::Move { dst, src }
        | VmInstruction::Store { dst, src } | VmInstruction::StoreOwned { dst, src } =>
            (*dst, states.local_labels.get(*src as usize).copied().flatten()),
        _ => return None,
    };
    Some((destination, label.filter(|_| private_register(function, destination))))
}

/// Simulate only the proven shim, then verify the actual destination normally.
/// Handler-crossing/replay transfers retain their separate control protocol.
pub(super) fn transfer(
    function: &VmFunction, instruction: &VmInstruction, states: &VerifierState,
    shims: &BTreeMap<DefKey, Shim>,
) -> Result<Option<(u32, VerifierState)>, VmArtifactError> {
    if !states.handlers.is_empty() || states.resuming { return Ok(None); }
    let VmInstruction::CallOwned { callee, arguments, .. } = instruction else { return Ok(None); };
    let Some(shim) = shims.get(callee) else { return Ok(None); };
    if arguments.len() != 2 { return Ok(None); }
    let Some(label) = states.local_labels.get(arguments[shim.label as usize] as usize).copied().flatten()
        else { return Ok(None); };
    let payload = arguments[shim.payload as usize];
    for argument in arguments {
        read(states, *argument)?;
        verify_call_frame_resumption_transfer(states, *argument)?;
    }
    if arguments[0] == arguments[1] {
        return Err(VmArtifactError::MalformedEncoding { message: "consuming call repeats an argument carrier" });
    }
    same_type(function, label.destination, payload)?;
    let index = payload as usize;
    let metadata = (states.reference_origins[index].clone(), states.frame_independent[index],
        states.referent_independent[index], states.destruction_preserves_frames[index],
        states.labels[index], states.resumptions[index], states.snapshots[index], states.invocation_preserves_frames[index]);
    let mut next = states.clone();
    for argument in arguments {
        let index = *argument as usize;
        next.registers[index] = Some(false);
        next.reference_origins[index].clear();
        next.frame_independent[index] = false;
        next.referent_independent[index] = false;
        next.destruction_preserves_frames[index] = false;
        next.invocation_preserves_frames[index] = false;
        next.local_labels[index] = None;
        next.labels[index] = false;
        next.resumptions[index] = false;
        next.snapshots[index] = None;
    }
    write(&mut next, label.destination)?;
    let destination = label.destination as usize;
    next.reference_origins[destination] = metadata.0;
    next.frame_independent[destination] = metadata.1;
    next.referent_independent[destination] = metadata.2;
    next.destruction_preserves_frames[destination] = metadata.3;
    next.labels[destination] = metadata.4;
    next.resumptions[destination] = metadata.5;
    next.snapshots[destination] = metadata.6;
    next.invocation_preserves_frames[destination] = metadata.7;
    Ok(Some((label.target, next)))
}

/// An opaque call that receives a local label can rejoin after mutating this
/// frame. A normal CFG predecessor of that destination cannot stand in for
/// this unproved path. Keep its tail frontier fail-closed until an executable
/// transfer proof supplies the actual destination state.
pub(super) fn opaque_targets(function: &VmFunction, instruction: &VmInstruction, states: &VerifierState) -> Vec<u32> {
    let tainted = |register: &u32| states.labels.get(*register as usize) == Some(&true);
    let may_rejoin = match instruction {
        VmInstruction::Call { arguments, .. } | VmInstruction::CallOwned { arguments, .. } => arguments.iter().any(tainted),
        VmInstruction::CallIndirect { callee, arguments, .. } | VmInstruction::CallIndirectOwned { callee, arguments, .. } =>
            tainted(callee) || arguments.iter().any(tainted),
        _ => false,
    };
    if !may_rejoin { return vec![]; }
    function.instructions.iter().filter_map(|instruction| match instruction {
        VmInstruction::MakeLabel { target, .. } => Some(*target),
        _ => None,
    }).collect()
}

pub(super) fn check_opaque_tail_frontier(function: &VmFunction, targets: BTreeSet<u32>) -> Result<(), VmArtifactError> {
    let mut pending = targets.into_iter().collect::<Vec<_>>();
    let mut seen = BTreeSet::new();
    while let Some(pc) = pending.pop() {
        if !seen.insert(pc) { continue; }
        let Some(instruction) = function.instructions.get(pc as usize) else { continue; };
        match instruction {
            VmInstruction::TailCallOwned { arguments, .. } => {
                for argument in arguments {
                    if !vm_tail_owned_type(&register_type(function, *argument)?, &function.nominal_copy_descriptors, &mut vec![]) {
                        return Err(VmArtifactError::UnprovenTailCarrier { function: function.definition, pc, register: *argument,
                            message: "mandatory tail carrier follows an opaque local label transfer" });
                    }
                }
            }
            VmInstruction::Return { .. } | VmInstruction::Trap => {}
            VmInstruction::Jump { target } | VmInstruction::Leave { target, .. } => pending.push(*target),
            VmInstruction::BranchBool { then_target, else_target, .. } => pending.extend([*then_target, *else_target]),
            VmInstruction::MakeLabel { target, .. } | VmInstruction::InstallHandler { target, .. }
            | VmInstruction::InstallHandlerOwned { target, .. } => pending.extend([*target, pc + 1]),
            _ => pending.push(pc + 1),
        }
    }
    Ok(())
}
