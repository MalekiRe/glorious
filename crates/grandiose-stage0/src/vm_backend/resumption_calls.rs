//! Ordinary invocation contracts for caller-owned resumption capabilities.
//!
//! The existing executable control verifier is the sole fact producer. It
//! runs under symbolic input capabilities and records their invocations and
//! outgoing value relation. Consumers instantiate that relation with actual
//! live handler tokens. Unknown or recursive obligations publish no proof.
//! Finite branch histories preserve invocation and disposal order, including
//! repeated and aliased inputs. Helper-local active delimiters remain an
//! explicit unsupported obligation, not an erased part of a call trace.

use super::*;
use super::resumption_values::InputPath;

/// Remaining invocations of one captured operation, not a count attached to
/// each alias. Joins retain the extrema of every represented execution: the
/// next invocation must be available on all paths and closure must leave no
/// required invocation on any path. None on a frame denotes active execution,
/// independently of whether a spent clause still retains audit snapshots.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Budget { minimum: u32, maximum: u32 }

impl Budget {
    pub(super) fn captured(policy: VmContinuationPolicy) -> Self {
        let uses = match policy {
            VmContinuationPolicy::Terminal => 0,
            VmContinuationPolicy::Optional | VmContinuationPolicy::Consume => 1,
            VmContinuationPolicy::Replay { uses } => uses,
        };
        Self { minimum: uses, maximum: uses }
    }

    pub(super) fn available(self) -> bool { self.minimum > 0 }
    pub(super) fn spent(self) -> bool { self.maximum == 0 }
    pub(super) fn final_invocation(self) -> bool { self.minimum == 1 && self.maximum == 1 }

    pub(super) fn consume(&mut self) -> Result<(), VmArtifactError> {
        if !self.available() { return Err(VmArtifactError::HandlerResumeUnavailable); }
        self.minimum -= 1;
        self.maximum -= 1;
        Ok(())
    }

    pub(super) fn join(&mut self, other: Self) -> bool {
        let joined = Self { minimum: self.minimum.min(other.minimum), maximum: self.maximum.max(other.maximum) };
        let changed = *self != joined;
        *self = joined;
        changed
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Invocation {
    pub(super) parameter: VmType,
    pub(super) result: VmType,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Event {
    Invoke { input: InputPath, invocation: Invocation },
    Dispose { input: InputPath },
}

/// Alternatives join by union; events within an alternative never commute.
/// Empty coverage is distinct from one known empty execution. Growing loops
/// and exhausted bounds reject instead of publishing a truncated proof.
#[derive(Clone, Debug, Default, Eq)]
pub(super) struct Paths(Vec<Vec<Event>>);

impl PartialEq for Paths {
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len() && self.0.iter().all(|path| other.0.contains(path))
    }
}

impl Paths {
    const MAX_PATHS: usize = 256;
    const MAX_EVENTS: usize = 64;

    pub(super) fn entry() -> Self { Self(vec![vec![]]) }

    pub(super) fn join(&mut self, other: &Self) -> Result<bool, VmArtifactError> {
        let mut changed = false;
        for path in &other.0 {
            if self.0.contains(path) { continue; }
            if self.0.len() >= Self::MAX_PATHS { return Err(VmArtifactError::HandlerResumeUnavailable); }
            self.0.push(path.clone());
            changed = true;
        }
        Ok(changed)
    }

    fn append(&mut self, event: Event) -> Result<(), VmArtifactError> {
        for path in &mut self.0 {
            if path.len() >= Self::MAX_EVENTS { return Err(VmArtifactError::HandlerResumeUnavailable); }
            path.push(event.clone());
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct Contract {
    /// Reachable event prefixes include non-returning paths. They must be
    /// audited even when they cannot discharge a normal caller's obligation.
    observed: Paths,
    normal: Paths,
    pub(super) result: ResumptionValue,
}

impl Contract {
    pub(super) fn returned(&mut self, paths: &Paths, result: &ResumptionValue) -> Result<(), VmArtifactError> {
        self.result = if self.normal.0.is_empty() { result.clone() } else { self.result.join(result) };
        self.normal.join(paths)?;
        Ok(())
    }
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

pub(super) fn record(event: Event, states: &mut VerifierState, contract: &mut Contract) -> Result<(), VmArtifactError> {
    if !states.handlers.is_empty() { return Err(VmArtifactError::HandlerResumeUnavailable); }
    states.resumption_paths.append(event)?;
    contract.observed.join(&states.resumption_paths)?;
    Ok(())
}

pub(super) fn apply(function: &VmFunction, pc: usize, inputs: &[ResumptionValue],
    contract: &Contract, states: &mut VerifierState, observed: &mut Contract,
    incoming: &mut VerifierIncoming, worklist: &mut VerifierWorklist,
) -> Result<Option<ResumptionValue>, VmArtifactError> {
    let mut merged = vec![BTreeMap::new()];
    let mut merge_worklist = vec![];
    for (paths, returns) in [(&contract.observed, false), (&contract.normal, true)] {
        for path in &paths.0 {
            let mut branch = states.clone();
            for event in path {
                let input = match event { Event::Invoke { input, .. } | Event::Dispose { input } => input };
                let value = inputs.get(input.input as usize).ok_or(VmArtifactError::HandlerResumeUnavailable)?.project(&input.fields);
                match event {
                    Event::Dispose { .. } => cancel(&value, &mut branch, observed)?,
                    Event::Invoke { invocation, .. } => match value {
                        ResumptionValue::None => {},
                        ResumptionValue::Input(input) => record(Event::Invoke { input, invocation: invocation.clone() }, &mut branch, observed)?,
                        ResumptionValue::Token(id) => {
                            let index = branch.handlers.iter().rposition(|frame| frame.id == id)
                                .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
                            resume(function, pc, index, invocation, &mut branch, incoming, worklist)?;
                        }
                        _ => return Err(VmArtifactError::HandlerResumeUnavailable),
                    },
                }
            }
            if returns { propagate_state(&mut merged, &mut merge_worklist, 0, &branch)?; }
        }
    }
    if merged[0].is_empty() { return Ok(None); }
    if merged[0].len() != 1 { return Err(VmArtifactError::HandlerStateMismatch); }
    *states = merged[0].pop_first().expect("checked normal execution").1;
    let result = contract.result.instantiate(inputs);
    if matches!(result, ResumptionValue::Unknown) { return Err(VmArtifactError::HandlerResumeUnavailable); }
    Ok(Some(result))
}

/// Audit every possible suspended suffix using the existing local control
/// machine. Direct resumption and an ordinary helper invocation consume the
/// same transition for one event on one represented path. Only normal paths
/// rejoin the caller; reachable non-returning prefixes are audited separately.
pub(super) fn resume(function: &VmFunction, pc: usize, index: usize, invocation: &Invocation,
    states: &mut VerifierState,
    incoming: &mut VerifierIncoming, worklist: &mut VerifierWorklist,
) -> Result<(), VmArtifactError> {
    let frame = states.handlers.get(index).ok_or(VmArtifactError::HandlerResumeUnavailable)?;
    if !frame.can_resume() {
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
    active.invocations = None;
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
            resumption_paths: states.resumption_paths.clone(),
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
    states.handlers[index].invocations.as_mut().ok_or(VmArtifactError::HandlerResumeUnavailable)?.consume()?;
    if matches!(states.handlers[index].continuation, VmContinuationPolicy::Optional | VmContinuationPolicy::Consume) {
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
        ResumptionValue::Input(input) => record(Event::Dispose { input: input.clone() }, states, observed),
        ResumptionValue::Token(id) => {
            let frame = states.handlers.iter_mut().find(|frame| frame.id == *id)
                .ok_or(VmArtifactError::HandlerResumeUnavailable)?;
            // Replay handles alias one delimiter-owned budget. Disposing a
            // carrier never abandons that delimiter's remaining invocations.
            if frame.continuation.is_replay() { return Ok(()); }
            if !frame.continuations.is_empty() && frame.continuation != VmContinuationPolicy::Optional {
                return Err(VmArtifactError::HandlerResumeUnavailable);
            }
            frame.continuations.clear();
            frame.invocations = Some(Budget { minimum: 0, maximum: 0 });
            Ok(())
        }
        _ => Err(VmArtifactError::HandlerResumeUnavailable),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn joined_replay_budgets_require_every_path_to_admit_the_next_invocation() {
        let mut two = Budget::captured(VmContinuationPolicy::Replay { uses: 2 });
        let mut one = two;
        one.consume().unwrap();
        assert!(two.join(one));
        assert!(two.available());
        assert!(!two.final_invocation());
        two.consume().unwrap();
        assert!(!two.spent());
        assert!(two.consume().is_err());
        let mut exact = Budget::captured(VmContinuationPolicy::Replay { uses: 2 });
        exact.consume().unwrap();
        assert!(exact.final_invocation());
        exact.consume().unwrap();
        assert!(exact.spent());
        assert!(exact.consume().is_err());
    }

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

    #[test]
    fn resumption_transport_cannot_authenticate_an_ordinary_callable_input() {
        let function = helper(vec![declaration(),
            VmInstruction::RetainResumption { dst: 2, src: 0, fields: vec![] },
            VmInstruction::Return { value: 1 }], vec![callable(), VmType::I64, callable()], 2);
        assert!(verify_function_control(&function, false, false, &Default::default()).is_err());
        assert!(proof(function).is_none());
    }

    #[test]
    fn prepared_field_receivers_preserve_order_without_transferring_the_owner() {
        let function = helper(vec![declaration(),
            VmInstruction::PrepareInvocation { dst: 2, src: 0, fields: vec![0], reborrow: false },
            VmInstruction::CallPrepared { dst: 3, callee: 2, arguments: vec![1] },
            VmInstruction::PrepareInvocation { dst: 5, src: 0, fields: vec![0], reborrow: false },
            VmInstruction::CallPrepared { dst: 4, callee: 5, arguments: vec![3] },
            VmInstruction::Return { value: 4 }],
            vec![VmType::Tuple(vec![callable()]), VmType::I64, callable(), VmType::I64, VmType::I64, callable()], 2);
        let contract = proof(function.clone()).expect("preparing a field must not move its owner");
        assert!(matches!(contract.normal.0.as_slice(), [trace] if matches!(trace.as_slice(),
            [Event::Invoke { input: first, .. }, Event::Invoke { input: second, .. }]
            if first == second && first.input == 0 && first.fields == [0])));
        let mut forged = function;
        forged.instructions[1] = VmInstruction::TakeProjection { dst: 2, base: 0, fields: vec![0] };
        assert!(proof(forged).is_none(), "moving a field must not forge invocation preparation");
    }

    #[test]
    fn prepared_receivers_cannot_escape_copy_reprepare_or_use_ordinary_invocation() {
        for invalid in [
            VmInstruction::Copy { dst: 4, src: 2 },
            VmInstruction::Move { dst: 4, src: 2 },
            VmInstruction::PrepareInvocation { dst: 4, src: 2, fields: vec![], reborrow: false },
            VmInstruction::CallIndirectOwned { dst: 3, callee: 2, arguments: vec![1] },
            VmInstruction::DestroyCallable { dst: 5, value: 2 },
        ] {
            let function = helper(vec![declaration(),
                VmInstruction::PrepareInvocation { dst: 2, src: 0, fields: vec![], reborrow: false },
                invalid.clone(), VmInstruction::Return { value: 1 }],
                vec![callable(), VmType::I64, callable(), VmType::I64, callable(), VmType::Unit], 2);
            assert!(proof(function).is_none(), "accepted {invalid:?}");
        }
        let escaping = helper(vec![VmInstruction::DeclareResult { result: callable(), returns: true },
            VmInstruction::PrepareInvocation { dst: 1, src: 0, fields: vec![], reborrow: false },
            VmInstruction::Return { value: 1 }], vec![callable(), callable()], 1);
        assert!(proof(escaping).is_none());
        let reused = helper(vec![declaration(),
            VmInstruction::PrepareInvocation { dst: 2, src: 0, fields: vec![], reborrow: false },
            VmInstruction::CallPrepared { dst: 3, callee: 2, arguments: vec![1] },
            VmInstruction::CallPrepared { dst: 4, callee: 2, arguments: vec![3] },
            VmInstruction::Return { value: 4 }],
            vec![callable(), VmType::I64, callable(), VmType::I64, VmType::I64], 2);
        assert!(proof(reused).is_none(), "a prepared receiver is consumed once");
    }

    #[test]
    fn receiver_preparation_cannot_turn_borrowed_storage_into_owned_fn_permission() {
        let function = helper(vec![declaration(),
            VmInstruction::PrepareInvocation { dst: 2, src: 0, fields: vec![], reborrow: true },
            VmInstruction::CallPrepared { dst: 3, callee: 2, arguments: vec![1] },
            VmInstruction::Return { value: 3 }],
            vec![VmType::Reference { unique: false, referent: Box::new(callable()) }, VmType::I64, callable(), VmType::I64], 2);
        assert!(verify_function_control(&function, false, false, &Default::default()).is_err());
    }

    #[test]
    fn source_copy_cannot_duplicate_owned_resumption_inputs() {
        let pair = VmType::Tuple(vec![VmType::I64, callable()]);
        for (ty, copied, result) in [
            (callable(), VmInstruction::Copy { dst: 2, src: 0 }, callable()),
            (callable(), VmInstruction::MakeTuple { dst: 2, fields: vec![0] }, VmType::Tuple(vec![callable()])),
            (pair.clone(), VmInstruction::ProjectTuple { dst: 2, base: 0, index: 1, field_count: 2, field_type: callable() }, callable()),
            (pair.clone(), VmInstruction::Copy { dst: 2, src: 0 }, pair),
        ] {
            let function = helper(vec![declaration(), copied, VmInstruction::Return { value: 1 }],
                vec![ty, VmType::I64, result], 2);
            let mut proofs = tail_provenance::TransferProofs::default();
            proofs.symbolic_resumption_inputs = true;
            assert!(matches!(verify_function_control(&function, false, false, &proofs), Err(VmArtifactError::AffineValueCopy { .. })));
        }
        let reference = VmType::Reference { unique: false, referent: Box::new(callable()) };
        assert!(ResumptionValue::Unknown.permits_source_copy(&reference, &[]));
        assert!(ResumptionValue::product([ResumptionValue::Unknown]).permits_source_copy(&VmType::Tuple(vec![reference]), &[]));
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
            assert_eq!(contract.observed.0.len(), 1);
            assert_eq!(contract.normal.0.iter().all(|trace|
                matches!(trace.as_slice(), [Event::Invoke { input, .. }] if input.input == 0)), both);
        }
    }

    #[test]
    fn repeated_input_invocations_do_not_acquire_a_single_use_proof() {
        let function = helper(vec![declaration(),
            VmInstruction::CallIndirectOwned { dst: 2, callee: 0, arguments: vec![1] },
            VmInstruction::ConstI64 { dst: 3, value: 42 },
            VmInstruction::CallIndirectOwned { dst: 4, callee: 0, arguments: vec![3] },
            VmInstruction::Return { value: 4 }], vec![callable(), VmType::I64, VmType::I64, VmType::I64, VmType::I64], 2);
        let contract = proof(function.clone()).unwrap();
        assert!(contract.normal.0.iter().all(|trace|
            matches!(trace.as_slice(), [Event::Invoke { input: first, .. }, Event::Invoke { input: second, .. }]
                if first == second && first.input == 0)));
        for continuation in [VmContinuationPolicy::Consume, VmContinuationPolicy::Replay { uses: 2 }] {
            let mut caller = helper(vec![declaration(),
                VmInstruction::InstallHandler { effect: function.definition, effect_arguments: vec![], operation: 0,
                    payload_destinations: vec![], resume_type: VmType::I64, continuation, target: 5 },
                VmInstruction::Perform { dst: 0, effect: function.definition, effect_arguments: vec![], operation: 0, arguments: vec![] },
                VmInstruction::UninstallHandler, VmInstruction::Return { value: 0 },
                VmInstruction::ConstI64 { dst: 1, value: 42 },
                VmInstruction::CaptureResumption { dst: 2 },
                VmInstruction::CallOwned { dst: 3, callee: function.definition, arguments: vec![2, 1] },
                if continuation.is_replay() { VmInstruction::Cancel } else { VmInstruction::UninstallHandler },
                VmInstruction::Return { value: 3 }], vec![VmType::I64, VmType::I64, callable(), VmType::I64], 0);
            caller.definition = DefKey(Digest::of_bytes(b"ordered-replay-caller"));
            let mut proofs = tail_provenance::TransferProofs::default();
            proofs.resumption_calls.insert(function.definition, contract.clone());
            assert_eq!(verify_function_control(&caller, false, false, &proofs).is_ok(), continuation.is_replay());
        }
    }

    #[test]
    fn ordered_inputs_and_nonreturning_prefixes_are_not_an_unordered_count() {
        let function = helper(vec![declaration(),
            VmInstruction::BranchBool { condition: 3, then_target: 2, else_target: 5 },
            VmInstruction::CallIndirect { dst: 4, callee: 1, arguments: vec![2] },
            VmInstruction::CallIndirect { dst: 5, callee: 0, arguments: vec![2] },
            VmInstruction::Return { value: 5 },
            VmInstruction::CallIndirect { dst: 6, callee: 0, arguments: vec![2] },
            VmInstruction::CallIndirect { dst: 7, callee: 1, arguments: vec![2] },
            VmInstruction::Trap], vec![callable(), callable(), VmType::I64, VmType::Bool,
                VmType::I64, VmType::I64, VmType::I64, VmType::I64], 4);
        let contract = proof(function).unwrap();
        let order = |path: &[Event]| path.iter().filter_map(|event|
            if let Event::Invoke { input, .. } = event { Some(input.input) } else { None }).collect::<Vec<_>>();
        assert_eq!(contract.normal.0.iter().map(|path| order(path)).collect::<Vec<_>>(), vec![vec![1, 0]]);
        assert!(contract.observed.0.iter().any(|path| order(path) == vec![0, 1]));
        assert!(contract.observed.0.iter().any(|path| order(path) == vec![1, 0]));
    }

    #[test]
    fn recursive_capability_histories_cannot_publish_a_truncated_proof() {
        let function = helper(vec![VmInstruction::DeclareResult { result: VmType::I64, returns: false },
            VmInstruction::CallIndirectOwned { dst: 2, callee: 0, arguments: vec![1] },
            VmInstruction::Move { dst: 1, src: 2 },
            VmInstruction::Jump { target: 1 }], vec![callable(), VmType::I64, VmType::I64], 2);
        assert!(proof(function).is_none());
        let mut paths = Paths::entry();
        let event = Event::Dispose { input: InputPath { input: 0, fields: vec![] } };
        for _ in 0..Paths::MAX_EVENTS { paths.append(event.clone()).unwrap(); }
        assert!(paths.append(event).is_err());
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
            assert_eq!(contract.normal.0.iter().all(|trace|
                matches!(trace.as_slice(), [Event::Dispose { input }] if input.input == 0)), !capture);
        }
    }

    #[test]
    fn input_disposal_is_not_a_guaranteed_invocation() {
        let function = helper(vec![declaration(),
            VmInstruction::DestroyCallable { dst: 2, value: 0 },
            VmInstruction::Return { value: 1 }], vec![callable(), VmType::I64, VmType::Unit], 2);
        let contract = proof(function).unwrap();
        let path = InputPath { input: 0, fields: vec![] };
        assert_eq!(contract.normal, Paths(vec![vec![Event::Dispose { input: path }]]));
    }

    #[test]
    fn invoked_input_cleanup_does_not_cancel_the_callers_remaining_authority() {
        let function = helper(vec![declaration(),
            VmInstruction::CallIndirectOwned { dst: 2, callee: 0, arguments: vec![1] },
            VmInstruction::DestroyCallable { dst: 3, value: 0 },
            VmInstruction::Return { value: 2 }], vec![callable(), VmType::I64, VmType::I64, VmType::Unit], 2);
        let contract = proof(function).unwrap();
        let path = InputPath { input: 0, fields: vec![] };
        assert!(contract.normal.0.iter().all(|trace|
            matches!(trace.as_slice(), [Event::Invoke { input, .. }, Event::Dispose { input: disposed }]
                if input == &path && disposed == &path)));
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
        proofs.resumption_calls.get_mut(&key).unwrap().normal = Paths::entry();
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
