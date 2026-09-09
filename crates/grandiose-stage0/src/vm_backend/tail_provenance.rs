//! Positive frame-transfer evidence, reconstructed from executable bytecode.
//! Empty local-loan sets are not evidence: untracked pointers have empty sets
//! too. Unknown producers and mutating boundaries revoke the must fact.

use super::*;

#[derive(Default)]
pub(super) struct TransferProofs {
    pub(super) label_dispatches: BTreeMap<DefKey, label_dispatch::Shim>,
    preserving_calls: BTreeSet<DefKey>,
    conditional_preserving_calls: BTreeSet<DefKey>,
    invocation_conditional_preserving_calls: BTreeSet<DefKey>,
    independent_input_preserving_calls: BTreeSet<DefKey>,
    reference_contents_preserving_calls: BTreeSet<DefKey>,
    pub(super) independent_results: BTreeSet<DefKey>,
    pub(super) preserving_result_destruction: BTreeSet<DefKey>,
}

/// These summaries are recomputed from the program; no producer-supplied
/// annotation can certify a helper's reference result or memory behavior.
pub(super) fn summaries(functions: &BTreeMap<DefKey, VmFunction>) -> Result<TransferProofs, VmArtifactError> {
    let label_dispatches = label_dispatch::shims(functions);
    if !functions.values().any(|function| function.instructions.iter().any(|instruction|
        matches!(instruction, VmInstruction::TailCallOwned { arguments, .. }
            if arguments.iter().any(|argument| function.registers.get(*argument as usize)
                .is_some_and(|ty| !vm_tail_owned_type(ty, &function.nominal_copy_descriptors, &mut vec![])))))) {
        // Ordinary calls and structurally owned tail carriers do not consume
        // this proof. Avoid re-verifying unrelated programs for an unused fact.
        return Ok(TransferProofs { label_dispatches, ..TransferProofs::default() });
    }
    let mut proofs = TransferProofs {
        label_dispatches,
        preserving_calls: preserving_calls(functions),
        conditional_preserving_calls: functions.keys().copied().collect(),
        invocation_conditional_preserving_calls: functions.keys().copied().collect(),
        independent_input_preserving_calls: functions.keys().copied().collect(),
        reference_contents_preserving_calls: functions.keys().copied().collect(),
        independent_results: functions.keys().copied().collect(),
        preserving_result_destruction: functions.keys().copied().collect(),
    };
    let mut callers = BTreeMap::<DefKey, BTreeSet<DefKey>>::new();
    for (caller, function) in functions {
        for instruction in &function.instructions {
            if let VmInstruction::Call { callee, .. } | VmInstruction::CallOwned { callee, .. }
                | VmInstruction::TailCallOwned { callee, .. } = instruction {
                callers.entry(*callee).or_default().insert(*caller);
            }
            if let VmInstruction::MakeCallable { environment: Some(environment), .. } = instruction
                && let Some(destructor) = environment.destructor {
                callers.entry(destructor).or_default().insert(*caller);
            }
            if let VmInstruction::MakeCallable { callee, .. } = instruction {
                callers.entry(*callee).or_default().insert(*caller);
            }
        }
    }
    // Coinduction admits recursive forwarding SCCs, but a local or unknown
    // producer in any member revokes that member and rechecks every caller.
    let mut pending = functions.keys().copied().collect::<Vec<_>>();
    let mut queued = proofs.independent_results.clone();
    while let Some(definition) = pending.pop() {
        queued.remove(&definition);
        let control = verify_function_control(&functions[&definition], false, true, &proofs)?;
        let mut changed = false;
        if !control.result_independent { changed |= proofs.independent_results.remove(&definition); }
        if !control.result_destruction_preserving { changed |= proofs.preserving_result_destruction.remove(&definition); }
        if !control.preserves_frame_memory { changed |= proofs.conditional_preserving_calls.remove(&definition); }
        if !control.preserves_independent_frame_memory { changed |= proofs.independent_input_preserving_calls.remove(&definition); }
        let preserves_reference_contents = control.preserves_independent_frame_memory
            && (control.preserves_frame_memory
                || !functions[&definition].registers.iter().take(functions[&definition].parameters as usize)
                    .any(|ty| matches!(ty, VmType::Reference { .. }))
                || verify_function_control_with_reference_inputs(&functions[&definition], false, true, true, false, &proofs)?
                    .preserves_independent_frame_memory);
        if !preserves_reference_contents { changed |= proofs.reference_contents_preserving_calls.remove(&definition); }
        // This separate contract assumes invocation-preserving input
        // callables, never merely harmless destruction or an empty capture
        // graph. A real call must discharge both hypotheses for every input.
        if !control.preserves_frame_memory && proofs.invocation_conditional_preserving_calls.contains(&definition)
            && !verify_function_control_with_reference_inputs(&functions[&definition], false, true, false, true, &proofs)?.preserves_frame_memory {
            changed |= proofs.invocation_conditional_preserving_calls.remove(&definition);
        }
        if !changed { continue; }
        for caller in callers.get(&definition).into_iter().flatten() {
            if queued.insert(*caller) { pending.push(*caller); }
        }
    }
    Ok(proofs)
}

pub(super) fn call_preserving(proofs: &TransferProofs, callee: &DefKey, preserving_destructors: bool) -> bool {
    proofs.preserving_calls.contains(callee)
        || (preserving_destructors && proofs.conditional_preserving_calls.contains(callee))
}

fn call_preserving_invocations(function: &VmFunction, states: &VerifierState,
    proofs: &TransferProofs, callee: &DefKey, arguments: &[u32]) -> bool {
    let destructors = arguments.iter().all(|argument| destruction_preserving(function, states, *argument));
    call_preserving(proofs, callee, destructors)
        || (destructors && proofs.invocation_conditional_preserving_calls.contains(callee)
            && arguments.iter().all(|argument| invocation_preserving(function, states, *argument)))
}

/// A helper may install an input pointer in surviving storage only when
/// every input's transitive address graph already excludes the caller frame.
/// This is a separate summary from destructor-only conditional preservation:
/// a caller-local reference must never satisfy this stronger precondition.
pub(super) fn call_preserving_independent(
    function: &VmFunction, states: &VerifierState, proofs: &TransferProofs,
    callee: &DefKey, arguments: &[u32],
) -> bool {
    let destructors = arguments.iter().all(|argument| destruction_preserving(function, states, *argument));
    call_preserving_invocations(function, states, proofs, callee, arguments)
        || (destructors && proofs.independent_input_preserving_calls.contains(callee)
            && arguments.iter().all(|argument| independent(function, states, *argument)))
        || (destructors && proofs.reference_contents_preserving_calls.contains(callee)
            && arguments.iter().all(|argument| match function.registers.get(*argument as usize) {
                Some(VmType::Reference { .. }) => referent_independent(function, states, *argument),
                _ => independent(function, states, *argument),
            }))
}

fn preserving_calls(functions: &BTreeMap<DefKey, VmFunction>) -> BTreeSet<DefKey> {
    let mut preserving = functions.iter().filter_map(|(definition, function)| {
        function.instructions.iter().all(|instruction| locally_preserving(function, instruction))
            .then_some(*definition)
    }).collect::<BTreeSet<_>>();
    // A recursive SCC with no mutation is preserving. Removing unknown or
    // mutating dependencies computes that greatest fixed point without
    // assuming that a source name or safe signature proves body behavior.
    loop {
        let rejected = preserving.iter().copied().filter(|definition| {
            functions[definition].instructions.iter().any(|instruction| match instruction {
                VmInstruction::Call { callee, .. } | VmInstruction::CallOwned { callee, .. }
                | VmInstruction::TailCallOwned { callee, .. } => !preserving.contains(callee),
                _ => false,
            })
        }).collect::<Vec<_>>();
        if rejected.is_empty() { return preserving; }
        for definition in rejected { preserving.remove(&definition); }
    }
}

fn locally_preserving(function: &VmFunction, instruction: &VmInstruction) -> bool {
    match instruction {
        VmInstruction::CallIndirect { .. } | VmInstruction::CallIndirectOwned { .. }
        | VmInstruction::HostCall { .. } | VmInstruction::HostCallOwned { .. }
        | VmInstruction::Perform { .. } | VmInstruction::PerformOwned { .. }
        | VmInstruction::DestroyCallable { .. } => false,
        // A scalar store cannot install a reference to this activation in
        // older storage. Reference-bearing writes need alias-sensitive proof.
        VmInstruction::DerefStore { src, .. } => function.registers.get(*src as usize)
            .is_some_and(|ty| vm_tail_owned_type(ty, &function.nominal_copy_descriptors, &mut vec![])),
        VmInstruction::MemoryIntrinsic { primitive, types, .. } => match primitive {
            // Typed scalar/owned writes cannot install an activation address.
            // Copy's type is the resident type, not the pointer operand type.
            MemoryPrimitive::Write | MemoryPrimitive::Copy | MemoryPrimitive::CopyNonoverlapping =>
                types.first().is_some_and(|ty| vm_tail_owned_type(ty, &function.nominal_copy_descriptors, &mut vec![])),
            // Raw allocation/resize/release do not execute source destruction
            // or introduce a new reference into another initialized resident.
            // Forget likewise suppresses, rather than invokes, source Drop.
            _ => true,
        },
        _ => true,
    }
}

pub(super) fn independent(function: &VmFunction, states: &VerifierState, register: u32) -> bool {
    states.frame_independent.get(register as usize) == Some(&true)
        || function.registers.get(register as usize).is_some_and(|ty|
            vm_tail_owned_type(ty, &function.nominal_copy_descriptors, &mut vec![]))
}

/// Contents of a borrowed local owner can be independent even though the
/// address of that owner's slot is not. Never apply this weaker fact to raw
/// pointers: casts and offsets can expose storage outside a typed referent.
pub(super) fn referent_independent(function: &VmFunction, states: &VerifierState, register: u32) -> bool {
    let Some(VmType::Reference { referent, .. }) = function.registers.get(register as usize) else {
        return false;
    };
    independent(function, states, register)
        || states.referent_independent.get(register as usize) == Some(&true)
        || vm_tail_owned_type(referent, &function.nominal_copy_descriptors, &mut vec![])
}

/// A never-exposed local slot cannot be revived through an alias. This is a
/// may fact over the complete body, not an inference from empty loan sets.
pub(super) fn exposed_storage(function: &VmFunction) -> Vec<bool> {
    let mut exposed = (0..function.registers.len()).map(|index| index < function.parameters as usize).collect::<Vec<_>>();
    for instruction in &function.instructions {
        match instruction {
            VmInstruction::Borrow { src, reborrow: false, .. } => {
                if let Some(value) = exposed.get_mut(*src as usize) { *value = true; }
            }
            // These capabilities may restore the enclosing register file.
            VmInstruction::MakeLabel { .. } | VmInstruction::InstallHandler { .. }
            | VmInstruction::InstallHandlerOwned { .. } | VmInstruction::CaptureResumption { .. } => exposed.fill(true),
            _ => {}
        }
    }
    exposed
}

fn contains_no_callable(ty: &VmType, descriptors: &[VmNominalCopyDescriptor], active: &mut Vec<VmType>) -> bool {
    match ty {
        VmType::Callable { .. } | VmType::Generic(_) | VmType::ConstGeneric { .. } | VmType::ConstIntegerExpr(_) => false,
        VmType::Reference { referent: value, .. } | VmType::RawPointer { pointee: value, .. }
        | VmType::Array(value) | VmType::FixedArray { element: value, .. } | VmType::StaticData { element: value, .. } => contains_no_callable(value, descriptors, active),
        VmType::Tuple(fields) => fields.iter().all(|field| contains_no_callable(field, descriptors, active)),
        VmType::Nominal { definition, arguments } => {
            let Some(descriptor) = descriptors.iter().find(|descriptor|
                descriptor.definition == *definition && descriptor.arguments == *arguments) else { return false; };
            if active.contains(ty) { return true; }
            active.push(ty.clone());
            let result = descriptor.variants.iter().flatten().all(|field| contains_no_callable(field, descriptors, active));
            active.pop();
            result
        }
        _ => true,
    }
}

pub(super) fn destruction_preserving(function: &VmFunction, states: &VerifierState, register: u32) -> bool {
    states.local_labels.get(register as usize).is_some_and(Option::is_some)
        || states.destruction_preserves_frames.get(register as usize) == Some(&true)
        || function.registers.get(register as usize).is_some_and(|ty|
            contains_no_callable(ty, &function.nominal_copy_descriptors, &mut vec![]))
}

/// All callable leaves in this value preserve surrounding frame memory when
/// invoked with similarly preserving arguments. Unlike destruction, labels
/// and resumptions never receive this positive authority. Unknown resident
/// pointers and overwritten/joined values remain conservative.
pub(super) fn invocation_preserving(function: &VmFunction, states: &VerifierState, register: u32) -> bool {
    states.invocation_preserves_frames.get(register as usize) == Some(&true)
        || function.registers.get(register as usize).is_some_and(|ty|
            contains_no_callable(ty, &function.nominal_copy_descriptors, &mut vec![]))
}

fn invalidate_frames(frames: &mut [VerifierHandlerFrame], addresses: bool) {
    for frame in frames {
        for continuation in &mut frame.continuations {
            if addresses {
                continuation.frame_independent.fill(false);
                continuation.referent_independent.fill(false);
            }
            continuation.destruction_preserves_frames.fill(false);
            continuation.invocation_preserves_frames.fill(false);
            invalidate_frames(&mut continuation.above, addresses);
        }
    }
}

pub(super) fn invalidate_referent_storage(states: &mut VerifierState, storage: u32) {
    fn invalidate(origins: &[ReferenceOriginSet], proofs: &mut [bool], storage: u32) {
        for (origins, proof) in origins.iter().zip(proofs) {
            if origins.contains(&storage) { *proof = false; }
        }
    }
    fn invalidate_saved(saved_frames: &mut [VerifierHandlerFrame], storage: u32) {
        for frame in saved_frames {
            for continuation in &mut frame.continuations {
                invalidate(&continuation.reference_origins, &mut continuation.referent_independent, storage);
                invalidate(&continuation.reference_origins, &mut continuation.invocation_preserves_frames, storage);
                invalidate(&continuation.reference_origins, &mut continuation.destruction_preserves_frames, storage);
                invalidate_saved(&mut continuation.above, storage);
            }
        }
    }
    invalidate(&states.reference_origins, &mut states.referent_independent, storage);
    invalidate(&states.reference_origins, &mut states.invocation_preserves_frames, storage);
    invalidate(&states.reference_origins, &mut states.destruction_preserves_frames, storage);
    invalidate_saved(&mut states.handlers, storage);
}

/// Compute supported producer facts before an owned instruction consumes its
/// operands. Ordinary writes reset destinations; the result is installed only
/// after the instruction has independently passed its ABI and layout checks.
pub(super) fn before_instruction(
    function: &VmFunction, instruction: &VmInstruction, states: &mut VerifierState,
    proofs: &TransferProofs,
) -> (Option<(u32, bool, bool, bool, bool)>, bool, bool) {
    let result_proof = match instruction {
        VmInstruction::Call { callee, dst, arguments } | VmInstruction::CallOwned { callee, dst, arguments } => {
            Some((*dst, proofs.independent_results.contains(callee)
                && arguments.iter().all(|argument| independent(function, states, *argument)
                    && destruction_preserving(function, states, *argument))))
        }
        _ => None,
    };
    let call_result_destruction = match instruction {
        VmInstruction::Call { callee, arguments, .. } | VmInstruction::CallOwned { callee, arguments, .. } => {
            proofs.preserving_result_destruction.contains(callee)
                && arguments.iter().all(|argument| destruction_preserving(function, states, *argument))
        }
        _ => false,
    };
    let preserves_memory = match instruction {
        VmInstruction::Call { callee, arguments, .. } | VmInstruction::CallOwned { callee, arguments, .. } => {
            call_preserving_invocations(function, states, proofs, callee, arguments)
        }
        VmInstruction::CallIndirect { callee, arguments, .. } | VmInstruction::CallIndirectOwned { callee, arguments, .. } =>
            invocation_preserving(function, states, *callee)
                && destruction_preserving(function, states, *callee)
                && arguments.iter().all(|argument| invocation_preserving(function, states, *argument)
                    && destruction_preserving(function, states, *argument)),
        VmInstruction::DestroyCallable { value, .. } => destruction_preserving(function, states, *value),
        _ => locally_preserving(function, instruction),
    };
    let preserves = preserves_memory || match instruction {
        VmInstruction::DerefStore { src, .. } => independent(function, states, *src),
        VmInstruction::MemoryIntrinsic { primitive: MemoryPrimitive::Write, arguments, .. } =>
            arguments.get(1).is_some_and(|src| independent(function, states, *src)),
        VmInstruction::MemoryIntrinsic { primitive: MemoryPrimitive::Copy | MemoryPrimitive::CopyNonoverlapping, arguments, .. } =>
            arguments.first().is_some_and(|src| independent(function, states, *src)),
        VmInstruction::Call { callee, arguments, .. } | VmInstruction::CallOwned { callee, arguments, .. } =>
            call_preserving_independent(function, states, proofs, callee, arguments),
        _ => false,
    };
    if !preserves {
        states.frame_independent.fill(false);
        states.referent_independent.fill(false);
        states.destruction_preserves_frames.fill(false);
        states.invocation_preserves_frames.fill(false);
        // A clause can mutate memory observed by a retained continuation.
        // Restoring its old register file must not resurrect the old proof.
        invalidate_frames(&mut states.handlers, true);
    } else if !preserves_memory || match instruction {
        VmInstruction::DerefStore { src, .. } => !destruction_preserving(function, states, *src) || !invocation_preserving(function, states, *src),
        VmInstruction::MemoryIntrinsic { primitive: MemoryPrimitive::Write, arguments, .. } =>
            arguments.get(1).is_none_or(|src| !destruction_preserving(function, states, *src) || !invocation_preserving(function, states, *src)),
        VmInstruction::MemoryIntrinsic { primitive: MemoryPrimitive::Copy | MemoryPrimitive::CopyNonoverlapping, arguments, .. } =>
            arguments.first().is_none_or(|src| !destruction_preserving(function, states, *src) || !invocation_preserving(function, states, *src)),
        _ => false,
    } {
        // A call may preserve the absence of outgoing-frame addresses while
        // still replacing a callable resident with different executable
        // behavior. Do not retain invocation/destruction facts under that
        // weaker memory contract.
        states.destruction_preserves_frames.fill(false);
        states.invocation_preserves_frames.fill(false);
        invalidate_frames(&mut states.handlers, false);
    }
    let source = |register| independent(function, states, register);
    let destruction = |register| destruction_preserving(function, states, register);
    let invocation = |register| invocation_preserving(function, states, register);
    let invocation_proof = match instruction {
        VmInstruction::Copy { src, .. } | VmInstruction::Move { src, .. }
        | VmInstruction::Store { src, .. } | VmInstruction::StoreOwned { src, .. } => invocation(*src),
        VmInstruction::MakeTuple { fields, .. } | VmInstruction::MakeTupleOwned { fields, .. }
        | VmInstruction::MakeArray { fields, .. } | VmInstruction::MakeArrayOwned { fields, .. }
        | VmInstruction::MakeRecord { fields, .. } | VmInstruction::MakeRecordOwned { fields, .. }
        | VmInstruction::MakeEnum { fields, .. } | VmInstruction::MakeEnumOwned { fields, .. } => fields.iter().all(|field| invocation(*field)),
        VmInstruction::ProjectRecord { base, .. } | VmInstruction::ProjectTuple { base, .. }
        | VmInstruction::ProjectArray { base, .. } | VmInstruction::TakeProjection { base, .. } => invocation(*base),
        VmInstruction::TakeArrayElement { value, .. } => invocation(*value),
        VmInstruction::UpdateRecord { base, value, .. } => invocation(*base) && invocation(*value),
        VmInstruction::Borrow { src, .. } => invocation(*src),
        VmInstruction::DerefCopy { reference, .. } | VmInstruction::DerefMove { reference, .. } => invocation(*reference),
        VmInstruction::MakeCallable { callee, captures, .. } =>
            call_preserving_invocations(function, states, proofs, callee, captures),
        _ => false,
    };
    let destruction_proof = match instruction {
        // Disposing a lexical label releases only a control capability. It
        // neither invokes the target nor owns a callable capture environment.
        VmInstruction::MakeLabel { .. } => true,
        VmInstruction::Call { .. } | VmInstruction::CallOwned { .. } => call_result_destruction,
        VmInstruction::Copy { src, .. } | VmInstruction::Move { src, .. }
        | VmInstruction::Store { src, .. } | VmInstruction::StoreOwned { src, .. } => destruction(*src),
        VmInstruction::MakeTuple { fields, .. } | VmInstruction::MakeTupleOwned { fields, .. }
        | VmInstruction::MakeArray { fields, .. } | VmInstruction::MakeArrayOwned { fields, .. }
        | VmInstruction::MakeRecord { fields, .. } | VmInstruction::MakeRecordOwned { fields, .. }
        | VmInstruction::MakeEnum { fields, .. } | VmInstruction::MakeEnumOwned { fields, .. } => fields.iter().all(|field| destruction(*field)),
        VmInstruction::ProjectRecord { base, .. } | VmInstruction::ProjectTuple { base, .. }
        | VmInstruction::ProjectArray { base, .. } | VmInstruction::TakeProjection { base, .. } => destruction(*base),
        VmInstruction::TakeArrayElement { value, .. } => destruction(*value),
        VmInstruction::UpdateRecord { base, value, .. } => destruction(*base) && destruction(*value),
        VmInstruction::Borrow { src, .. } => destruction(*src),
        VmInstruction::DerefCopy { reference, .. } | VmInstruction::DerefMove { reference, .. } => destruction(*reference),
        VmInstruction::MakeCallable { environment, captures, .. } => environment.as_ref().and_then(|environment| environment.destructor)
            .is_none_or(|destructor| call_preserving(proofs, &destructor, captures.iter().all(|capture| destruction(*capture)))),
        _ => false,
    };
    let frame_proof = match instruction {
        // Its destruction is harmless, but the live label still depends on
        // this frame and can never be an independent tail carrier.
        VmInstruction::MakeLabel { dst, .. } => Some((*dst, false)),
        VmInstruction::Call { .. } | VmInstruction::CallOwned { .. } => result_proof,
        VmInstruction::Copy { dst, src } | VmInstruction::Move { dst, src }
        | VmInstruction::Store { dst, src } | VmInstruction::StoreOwned { dst, src } => Some((*dst, source(*src))),
        VmInstruction::MakeTuple { dst, fields } | VmInstruction::MakeTupleOwned { dst, fields }
        | VmInstruction::MakeArray { dst, fields, .. } | VmInstruction::MakeArrayOwned { dst, fields, .. }
        | VmInstruction::MakeRecord { dst, fields, .. } | VmInstruction::MakeRecordOwned { dst, fields, .. }
        | VmInstruction::MakeEnum { dst, fields, .. } | VmInstruction::MakeEnumOwned { dst, fields, .. } => {
            Some((*dst, fields.iter().all(|field| source(*field))))
        }
        VmInstruction::ProjectRecord { dst, base, .. } | VmInstruction::ProjectTuple { dst, base, .. }
        | VmInstruction::ProjectArray { dst, base, .. } | VmInstruction::TakeProjection { dst, base, .. } => Some((*dst, source(*base))),
        VmInstruction::TakeArrayElement { dst, value, .. } => Some((*dst, source(*value))),
        VmInstruction::UpdateRecord { dst, base, value, .. } => Some((*dst, source(*base) && source(*value))),
        VmInstruction::Borrow { dst, src, reborrow, .. } => Some((*dst, *reborrow && source(*src))),
        VmInstruction::DerefCopy { dst, reference } | VmInstruction::DerefMove { dst, reference } =>
            Some((*dst, referent_independent(function, states, *reference))),
        VmInstruction::MakeCallable { dst, captures, .. } => Some((*dst, captures.iter().all(|capture|
            source(*capture) && !states.labels[*capture as usize] && !states.resumptions[*capture as usize].contains()))),
        VmInstruction::MemoryIntrinsic { dst, primitive, arguments, .. } => {
            let independent = match primitive {
                MemoryPrimitive::Null | MemoryPrimitive::Dangling | MemoryPrimitive::Allocate
                | MemoryPrimitive::StaticUtf8Address | MemoryPrimitive::StaticBytesAddress => true,
                MemoryPrimitive::Reallocate | MemoryPrimitive::Offset | MemoryPrimitive::OffsetConst | MemoryPrimitive::Cast
                | MemoryPrimitive::CastConst | MemoryPrimitive::AsConst | MemoryPrimitive::Read
                | MemoryPrimitive::BorrowShared | MemoryPrimitive::BorrowUnique
                | MemoryPrimitive::AsRawShared | MemoryPrimitive::AsRawUnique => arguments.first().is_some_and(|value| source(*value)),
                _ => false,
            };
            Some((*dst, independent))
        }
        _ => None,
    };
    let referent_proof = match instruction {
        VmInstruction::Borrow { src, reborrow, .. } => if *reborrow {
            referent_independent(function, states, *src)
        } else { source(*src) },
        VmInstruction::Copy { src, .. } | VmInstruction::Move { src, .. }
        | VmInstruction::Store { src, .. } | VmInstruction::StoreOwned { src, .. } =>
            referent_independent(function, states, *src),
        // A full transitive-graph proof also proves its referent. No weaker
        // fact survives raw conversion, cast, projection, or unknown calls.
        _ => frame_proof.is_some_and(|(_, independent)| independent),
    };
    (frame_proof.map(|(destination, independent)| (destination, independent, referent_proof, destruction_proof, invocation_proof)), preserves_memory, preserves)
}
