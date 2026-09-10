//! Ordinary invocation contracts for caller-owned resumption capabilities.
//!
//! The existing executable control verifier is the sole fact producer. It
//! runs under symbolic input capabilities and records their invocations and
//! outgoing value relation. Consumers instantiate that relation with actual
//! live handler tokens. Unknown or recursive obligations publish no proof.
//! This contract admits at most one invocation of one input capability and
//! no helper-local handler around that invocation. More complex traces need
//! their ordered delimiter/quantity relation, not an unordered may-call set.

use super::*;
use super::resumption_values::InputPath;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Invocation {
    pub(super) parameter: VmType,
    pub(super) result: VmType,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct Contract {
    pub(super) invocations: BTreeMap<InputPath, Invocation>,
    pub(super) cancellations: BTreeSet<InputPath>,
    /// Every normal path invokes or cancels this input. This is not proof
    /// that an exact-positive capability was invoked.
    pub(super) disposed: BTreeSet<InputPath>,
    pub(super) required: BTreeSet<InputPath>,
    pub(super) result: ResumptionValue,
}

pub(super) fn input_values(function: &VmFunction) -> Vec<ResumptionValue> {
    function.registers.iter().enumerate().map(|(input, ty)| {
        if input >= function.parameters as usize { return ResumptionValue::None; }
        input_value(ty, input as u32, &mut vec![], &function.nominal_copy_descriptors, 0, &mut 4096)
    }).collect()
}

pub(super) fn may_contain(ty: &VmType, layouts: &[VmNominalCopyDescriptor]) -> bool {
    input_value(ty, 0, &mut vec![], layouts, 0, &mut 4096).contains()
}

fn input_value(ty: &VmType, input: u32, path: &mut Vec<u32>,
    layouts: &[VmNominalCopyDescriptor], depth: usize, nodes: &mut usize,
) -> ResumptionValue {
    if depth >= 32 || *nodes == 0 { return ResumptionValue::Unknown; }
    *nodes -= 1;
    match ty {
        VmType::Callable { .. } => ResumptionValue::Input(InputPath { input, fields: path.clone() }),
        VmType::Tuple(fields) => ResumptionValue::product(fields.iter().enumerate().map(|(index, ty)| {
            path.push(index as u32);
            let result = input_value(ty, input, path, layouts, depth + 1, nodes);
            path.pop(); result
        })),
        VmType::FixedArray { element, length } if *length <= 4096 =>
            ResumptionValue::product((0..*length).map(|index| {
                path.push(index as u32);
                let result = input_value(element, input, path, layouts, depth + 1, nodes);
                path.pop(); result
            })),
        VmType::Nominal { definition, arguments } => {
            let Some(layout) = layouts.iter().find(|layout| layout.definition == *definition && layout.arguments == *arguments) else {
                return ResumptionValue::Unknown;
            };
            layout.variants.iter().map(|fields| input_value(&VmType::Tuple(fields.clone()), input, path, layouts, depth + 1, nodes))
                .reduce(|left, right| left.join(&right)).unwrap_or_default()
        }
        // A borrowed capability needs a checked storage projection before
        // it can acquire a callable input path. No loan becomes an owned token.
        VmType::Reference { referent, .. } => input_value(referent, input, path, layouts, depth + 1, nodes).opaque(),
        VmType::Array(element) | VmType::FixedArray { element, .. } => input_value(element, input, path, layouts, depth + 1, nodes).opaque(),
        VmType::Generic(_) => ResumptionValue::Unknown,
        _ => ResumptionValue::None,
    }
}

/// Publish only complete finite proofs. Dependencies are demanded by actual
/// capability-bearing call edges in the same verifier, not a second call walker.
pub(super) fn publish(functions: &BTreeMap<DefKey, VmFunction>, proofs: &mut tail_provenance::TransferProofs) {
    let mut pending = functions.iter().filter(|(_, function)| input_values(function).iter().any(ResumptionValue::contains))
        .map(|(key, _)| *key).collect::<BTreeSet<_>>();
    proofs.symbolic_resumption_inputs = true;
    loop {
        let mut published = vec![];
        for key in &pending {
            if let Ok(control) = verify_function_control(&functions[key], false, false, proofs)
                && control.resumption_contract.invocations.len() <= 1
                && control.resumption_contract.invocations.keys().chain(control.resumption_contract.cancellations.iter())
                    .collect::<BTreeSet<_>>().len() <= 1
                && !control.resumption_contract.result.has_local_or_unknown() {
                proofs.resumption_calls.insert(*key, control.resumption_contract);
                published.push(*key);
            }
        }
        if published.is_empty() { break; }
        for key in published { pending.remove(&key); }
    }
    proofs.symbolic_resumption_inputs = false;
}

/// Frame-preservation hypotheses strengthen while their whole-program fixed
/// point settles. A contract found earlier is not authority under that final
/// input until its original producer checks the conjunction again. Failure
/// rejects the graph; no stale control contract crosses the publication seal.
pub(super) fn validate(functions: &BTreeMap<DefKey, VmFunction>, proofs: &mut tail_provenance::TransferProofs)
    -> Result<(), VmArtifactError>
{
    proofs.symbolic_resumption_inputs = true;
    let result = proofs.resumption_calls.iter().try_for_each(|(key, expected)| {
        let actual = verify_function_control(&functions[key], false, false, proofs)?;
        if actual.resumption_contract != *expected {
            return Err(VmArtifactError::HandlerStateMismatch);
        }
        Ok(())
    });
    proofs.symbolic_resumption_inputs = false;
    result
}

pub(super) fn record(
    path: &InputPath, invocation: &Invocation, contract: &mut Contract,
) -> Result<(), VmArtifactError> {
    if let Some(previous) = contract.invocations.insert(path.clone(), invocation.clone())
        && previous != *invocation {
        return Err(VmArtifactError::HandlerStateMismatch);
    }
    Ok(())
}

pub(super) fn apply(function: &VmFunction, pc: usize, inputs: &[ResumptionValue],
    contract: &Contract, states: &mut VerifierState, observed: &mut Contract,
    incoming: &mut VerifierIncoming, worklist: &mut VerifierWorklist,
) -> Result<ResumptionValue, VmArtifactError> {
    for path in &contract.cancellations {
        let value = inputs.get(path.input as usize).ok_or(VmArtifactError::HandlerResumeUnavailable)?.project(&path.fields);
        match value {
            ResumptionValue::None | ResumptionValue::Expired => {},
            ResumptionValue::Input(input) => {
                if !states.handlers.is_empty() || states.may_invoked_resumption_inputs.contains(&input) {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                observed.cancellations.insert(input);
            }
            ResumptionValue::Token(id) => {
                let frame = states.handlers.iter().find(|frame| frame.id == id)
                    .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                if frame.continuation != VmContinuationPolicy::Optional || frame.continuations.is_empty() {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
            }
            _ => return Err(VmArtifactError::HandlerResumeUnavailable),
        }
    }
    for (path, invocation) in &contract.invocations {
        let value = inputs.get(path.input as usize).ok_or(VmArtifactError::HandlerResumeUnavailable)?
            .project(&path.fields);
        let required = contract.required.contains(path);
        match value {
            ResumptionValue::None => {}
            ResumptionValue::Input(input) => {
                if !states.handlers.is_empty() || !states.may_invoked_resumption_inputs.insert(input.clone()) {
                    return Err(VmArtifactError::HandlerResumeUnavailable);
                }
                record(&input, invocation, observed)?;
                if required { states.invoked_resumption_inputs.insert(input); }
            }
            ResumptionValue::Token(frame) => {
                let index = states.handlers.iter().rposition(|handler| handler.id == frame)
                    .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                resume(function, pc, index, invocation, required, states, incoming, worklist)?;
            }
            _ => return Err(VmArtifactError::HandlerResumeUnavailable),
        }
    }
    for path in contract.cancellations.iter().chain(contract.disposed.iter()) {
        let value = inputs.get(path.input as usize).ok_or(VmArtifactError::HandlerResumeUnavailable)?.project(&path.fields);
        match value {
            ResumptionValue::Input(input) => {
                states.may_invoked_resumption_inputs.insert(input.clone());
                if contract.disposed.contains(path) { states.disposed_resumption_inputs.insert(input); }
            }
            ResumptionValue::Token(id) if contract.disposed.contains(path) => {
                let frame = states.handlers.iter_mut().find(|frame| frame.id == id)
                    .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                if frame.continuation == VmContinuationPolicy::Optional { frame.continuations.clear(); }
            }
            _ => {},
        }
    }
    let result = contract.result.instantiate(inputs);
    if matches!(result, ResumptionValue::Unknown) { return Err(VmArtifactError::HandlerResumeUnavailable); }
    Ok(result)
}

/// Audit every possible suspended suffix using the existing local control
/// machine. Direct resumption and an ordinary helper invocation consume the
/// same transition. May invocation audits the suffix; only a proved invocation
/// on every normal-return path can discharge a one-shot continuation.
pub(super) fn resume(function: &VmFunction, pc: usize, index: usize, invocation: &Invocation,
    required: bool, states: &mut VerifierState,
    incoming: &mut VerifierIncoming, worklist: &mut VerifierWorklist,
) -> Result<(), VmArtifactError> {
    let frame = states.handlers.get(index).ok_or(VmArtifactError::HandlerResumeUnavailable)?;
    if frame.continuation == VmContinuationPolicy::Terminal || frame.continuations.is_empty() {
        return Err(VmArtifactError::HandlerResumeUnavailable);
    }
    if invocation.parameter != frame.resume_type {
        return Err(VmArtifactError::ResultType { expected: frame.resume_type.clone(), found: invocation.parameter.clone() });
    }
    let continuations = frame.continuations.clone();
    let resumption_return_result = vec![(frame.id, invocation.result.clone())];
    let mut resumed_handlers = states.handlers[..index].to_vec();
    resumed_handlers.extend_from_slice(&states.handlers[index + 1..]);
    resumed_handlers.push(frame.clone());
    let active = resumed_handlers.last_mut().expect("checked resumable handler");
    active.payload_claim = None;
    active.continuations.clear();
    for continuation in continuations {
        let mut handlers = resumed_handlers.clone();
        handlers.extend(continuation.above);
        let resumption_return_handler_ids = handlers.iter().map(|frame| frame.id).collect::<Vec<_>>();
        if resumption_return_handler_ids.iter().copied().collect::<BTreeSet<_>>().len() != resumption_return_handler_ids.len() {
            return Err(VmArtifactError::HandlerStateMismatch);
        }
        let mut resumed = VerifierState {
            disposed_resumption_inputs: states.disposed_resumption_inputs.clone(),
            may_invoked_resumption_inputs: states.may_invoked_resumption_inputs.clone(),
            invoked_resumption_inputs: states.invoked_resumption_inputs.clone(),
            last_instruction: Some(pc),
            may_initialized: continuation.may_initialized,
            registers: continuation.registers,
            storage_live: continuation.storage_live,
            source_storage: states.source_storage.clone(),
            reference_origins: continuation.reference_origins,
            frame_independent: continuation.frame_independent,
            referent_independent: continuation.referent_independent,
            local_labels: continuation.local_labels,
            destruction_preserves_frames: continuation.destruction_preserves_frames,
            invocation_preserves_frames: continuation.invocation_preserves_frames,
            address_exposed: continuation.address_exposed,
            labels: continuation.labels,
            resumptions: continuation.resumptions,
            handlers,
            pending_leave: continuation.pending_leave,
            resuming: true,
            resumption_return_handler_ids,
            resumption_return_result: resumption_return_result.clone(),
        };
        write(&mut resumed, continuation.dst)?;
        propagate_state(incoming, worklist, continuation.target, &resumed)?;
    }
    if required && matches!(states.handlers[index].continuation, VmContinuationPolicy::Optional | VmContinuationPolicy::Consume) {
        states.handlers[index].continuations.clear();
    }
    let _ = function;
    Ok(())
}

pub(super) fn cancel(value: &ResumptionValue, states: &mut VerifierState, observed: &mut Contract)
    -> Result<(), VmArtifactError>
{
    match value {
        ResumptionValue::None | ResumptionValue::Expired => Ok(()),
        ResumptionValue::Input(input) => {
            if !states.handlers.is_empty() {
                return Err(VmArtifactError::HandlerResumeUnavailable);
            }
            if !states.invoked_resumption_inputs.contains(input) {
                observed.cancellations.insert(input.clone());
            }
            states.may_invoked_resumption_inputs.insert(input.clone());
            states.disposed_resumption_inputs.insert(input.clone());
            Ok(())
        }
        ResumptionValue::Token(id) => {
            let frame = states.handlers.iter_mut().find(|frame| frame.id == *id)
                .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
            if !frame.continuations.is_empty() && frame.continuation != VmContinuationPolicy::Optional {
                return Err(VmArtifactError::HandlerResumeUnavailable);
            }
            frame.continuations.clear();
            Ok(())
        }
        _ => Err(VmArtifactError::HandlerResumeUnavailable),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn helper(instructions: Vec<VmInstruction>, registers: Vec<VmType>, parameters: u32) -> VmFunction {
        VmFunction {
            definition: DefKey(Digest::of_bytes(b"resumption-input-contract")),
            safety: Safety::Safe, unsafe_execution: false, captures: 0, parameters,
            nominal_copy_descriptors: vec![], registers, instructions,
        }
    }
    fn callable() -> VmType {
        VmType::Callable { shared_receiver: false, unique_receiver: false,
            safety: Safety::Safe, parameters: vec![VmType::I64], result: Box::new(VmType::I64), effects: Box::default() }
    }
    fn declaration() -> VmInstruction {
        VmInstruction::DeclareResult { result: VmType::I64, returns: true }
    }
    fn proof(function: VmFunction) -> Option<Contract> {
        let key = function.definition;
        let mut proofs = tail_provenance::TransferProofs::default();
        publish(&BTreeMap::from([(key, function)]), &mut proofs);
        proofs.resumption_calls.remove(&key)
    }

    #[test]
    fn input_invocation_requires_every_normal_branch_but_may_paths_remain_visible() {
        for both in [false, true] {
            let mut instructions = vec![declaration(),
                VmInstruction::BranchBool { condition: 2, then_target: 2, else_target: 4 },
                VmInstruction::CallIndirectOwned { dst: 3, callee: 0, arguments: vec![1] },
                VmInstruction::Return { value: 3 }];
            if both {
                instructions.extend([VmInstruction::CallIndirectOwned { dst: 3, callee: 0, arguments: vec![1] },
                    VmInstruction::Return { value: 3 }]);
            } else { instructions.push(VmInstruction::Return { value: 1 }); }
            let contract = proof(helper(instructions, vec![callable(), VmType::I64, VmType::Bool, VmType::I64], 3)).unwrap();
            assert_eq!(contract.invocations.len(), 1);
            assert_eq!(contract.required.contains(&InputPath { input: 0, fields: vec![] }), both);
        }
    }

    #[test]
    fn repeated_input_invocations_do_not_acquire_a_single_use_proof() {
        let function = helper(vec![declaration(),
            VmInstruction::CallIndirectOwned { dst: 2, callee: 0, arguments: vec![1] },
            VmInstruction::ConstI64 { dst: 3, value: 42 },
            VmInstruction::CallIndirectOwned { dst: 2, callee: 0, arguments: vec![3] },
            VmInstruction::Return { value: 2 }], vec![callable(), VmType::I64, VmType::I64, VmType::I64], 2);
        assert!(proof(function).is_none());
    }

    #[test]
    fn conditional_disposal_proves_owned_parameter_slots_but_not_lent_capture_storage() {
        for capture in [false, true] {
            let mut function = helper(vec![declaration(),
                VmInstruction::IsInitialized { dst: 2, base: 0, fields: vec![] },
                VmInstruction::BranchBool { condition: 2, then_target: 3, else_target: 4 },
                VmInstruction::DestroyCallable { dst: 3, value: 0 },
                VmInstruction::Return { value: 1 }], vec![callable(), VmType::I64, VmType::Bool, VmType::Unit], 2);
            function.captures = u32::from(capture);
            let contract = proof(function).unwrap();
            assert_eq!(contract.disposed.contains(&InputPath { input: 0, fields: vec![] }), !capture);
        }
    }

    #[test]
    fn input_disposal_is_not_a_guaranteed_invocation() {
        let function = helper(vec![declaration(),
            VmInstruction::DestroyCallable { dst: 2, value: 0 },
            VmInstruction::Return { value: 1 }], vec![callable(), VmType::I64, VmType::Unit], 2);
        let contract = proof(function).unwrap();
        let path = InputPath { input: 0, fields: vec![] };
        assert!(contract.cancellations.contains(&path));
        assert!(contract.disposed.contains(&path));
        assert!(contract.required.is_empty());
        assert!(contract.invocations.is_empty());
    }

    #[test]
    fn invoked_input_cleanup_does_not_cancel_the_callers_remaining_authority() {
        let function = helper(vec![declaration(),
            VmInstruction::CallIndirectOwned { dst: 2, callee: 0, arguments: vec![1] },
            VmInstruction::DestroyCallable { dst: 3, value: 0 },
            VmInstruction::Return { value: 2 }], vec![callable(), VmType::I64, VmType::I64, VmType::Unit], 2);
        let contract = proof(function).unwrap();
        let path = InputPath { input: 0, fields: vec![] };
        assert!(contract.disposed.contains(&path));
        assert!(contract.required.contains(&path));
        assert!(contract.cancellations.is_empty());
    }

    #[test]
    fn final_publication_rechecks_the_complete_contract() {
        let function = helper(vec![declaration(),
            VmInstruction::CallIndirectOwned { dst: 2, callee: 0, arguments: vec![1] },
            VmInstruction::Return { value: 2 }], vec![callable(), VmType::I64, VmType::I64], 2);
        let key = function.definition;
        let functions = BTreeMap::from([(key, function)]);
        let mut proofs = tail_provenance::TransferProofs::default();
        publish(&functions, &mut proofs);
        validate(&functions, &mut proofs).unwrap();
        proofs.resumption_calls.get_mut(&key).unwrap().required.clear();
        assert!(validate(&functions, &mut proofs).is_err());
        assert!(!proofs.symbolic_resumption_inputs);
    }

    #[test]
    fn missing_generic_layouts_and_large_control_arrays_are_unknown_not_empty() {
        let mut nodes = 4096;
        assert_eq!(input_value(&VmType::Generic(0), 0, &mut vec![], &[], 0, &mut nodes), ResumptionValue::Unknown);
        let array = VmType::FixedArray { element: Box::new(callable()), length: 5000 };
        assert_eq!(input_value(&array, 0, &mut vec![], &[], 0, &mut nodes), ResumptionValue::Unknown);
        let scalar = VmType::FixedArray { element: Box::new(VmType::I64), length: 5000 };
        assert_eq!(input_value(&scalar, 0, &mut vec![], &[], 0, &mut nodes), ResumptionValue::None);
    }
}
