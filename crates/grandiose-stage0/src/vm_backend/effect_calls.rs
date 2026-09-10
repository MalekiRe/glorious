//! May-perform edges of the executable control machine.
//!
//! The operation universe comes from the checked program-wide dynamic ABI.
//! Reachable instructions in `verify_function_control`, not an independent
//! instruction traversal, produce outward edges. The least fixed point is
//! private until every body has been checked against the closed product.

use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Operation {
    pub(super) effect: DefKey,
    pub(super) arguments: Vec<VmGenericArgument>,
    pub(super) operation: u32,
}

impl Operation {
    pub(super) fn matches(&self, frame: &VerifierHandlerFrame) -> bool {
        frame.active() && frame.effect == self.effect
            && frame.effect_arguments == self.arguments && frame.operation == self.operation
    }
}

#[derive(Clone, Debug, Default, Eq)]
pub(super) struct Footprint(Vec<Operation>);

impl PartialEq for Footprint {
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len() && self.0.iter().all(|operation| other.0.contains(operation))
    }
}

impl Footprint {
    pub(super) fn insert(&mut self, operation: Operation) -> bool {
        if self.0.contains(&operation) { return false; }
        self.0.push(operation);
        true
    }

    fn extend(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for operation in &other.0 { changed |= self.insert(operation.clone()); }
        changed
    }

    pub(super) fn operations(&self) -> &[Operation] { &self.0 }
}

pub(super) struct Proofs {
    universe: Footprint,
    outward: BTreeMap<DefKey, Footprint>,
    closed: bool,
}

fn row_admits(row: &VmEffectRow, operation: &Operation) -> bool {
    // An unresolved row is may permission for every operation in this closed
    // executable graph, never evidence that a callback cannot perform.
    !row.tails.is_empty() || !row.projections.is_empty()
        || row.effects.iter().any(|effect| effect.definition == operation.effect
            && effect.arguments == operation.arguments)
}

pub(super) fn invocation(function: &VmFunction, instruction: &VmInstruction,
    proofs: &tail_provenance::TransferProofs) -> Result<Footprint, VmArtifactError> {
    let Some(proofs) = &proofs.effect_calls else { return Ok(Footprint::default()); };
    match instruction {
        VmInstruction::Call { callee, .. } | VmInstruction::CallOwned { callee, .. }
        | VmInstruction::TailCallOwned { callee, .. } => proofs.outward.get(callee).cloned()
            .ok_or(VmArtifactError::MissingFunction { definition: *callee }),
        VmInstruction::CallIndirect { callee, .. } | VmInstruction::CallIndirectOwned { callee, .. }
        | VmInstruction::CallPrepared { callee, .. } => {
            let receiver = register_type(function, *callee)?;
            let Some(VmType::Callable { effects, .. }) = receiver.callable_receiver() else {
                return Err(VmArtifactError::NotCallable { register: *callee });
            };
            Ok(Footprint(proofs.universe.0.iter().filter(|operation| row_admits(effects, operation)).cloned().collect()))
        }
        _ => Ok(Footprint::default()),
    }
}

/// The same first-active-match rule selects local clause audits and outward
/// edges. A spent clause is not a newly installed delimiter.
pub(super) fn outward(footprint: &Footprint, states: &VerifierState, observed: &mut Footprint) {
    for operation in &footprint.0 {
        if !states.handlers.iter().any(|frame| operation.matches(frame)) {
            observed.insert(operation.clone());
        }
    }
}

pub(super) fn check(function: &VmFunction, observed: &Footprint,
    proofs: &tail_provenance::TransferProofs) -> Result<(), VmArtifactError> {
    let Some(proofs) = &proofs.effect_calls else { return Ok(()); };
    if proofs.closed && !observed.0.iter().all(|operation|
        proofs.outward.get(&function.definition).is_some_and(|expected| expected.0.contains(operation))) {
        return Err(VmArtifactError::MalformedEncoding { message: "executable outward-effect proof is incomplete" });
    }
    Ok(())
}

pub(super) fn check_callable(callee: DefKey, effects: &VmEffectRow,
    proofs: &tail_provenance::TransferProofs) -> Result<(), VmArtifactError> {
    let Some(proofs) = &proofs.effect_calls else { return Ok(()); };
    let actual = proofs.outward.get(&callee).ok_or(VmArtifactError::MissingFunction { definition: callee })?;
    if actual.0.iter().any(|operation| !row_admits(effects, operation)) {
        return Err(VmArtifactError::MalformedEncoding { message: "callable effect row conceals an executable performance" });
    }
    Ok(())
}

pub(super) fn publish(functions: &BTreeMap<DefKey, VmFunction>,
    proofs: &mut tail_provenance::TransferProofs) -> Result<(), VmArtifactError> {
    if proofs.effect_calls.is_none() {
        let universe = verify_program_effect_operation_abis(functions)?;
        if universe.operations().is_empty() { return Ok(()); }
        proofs.effect_calls = Some(Proofs {
            universe,
            outward: functions.keys().map(|key| (*key, Footprint::default())).collect(),
            closed: false,
        });
    }
    loop {
        let mut changed = false;
        // The existing helper producer must see newly reachable clauses as
        // well. Rebuild its finite contracts instead of retaining an earlier
        // contract whose normal paths were derived before an effect edge.
        proofs.resumption_calls.clear();
        resumption_calls::publish(functions, proofs);
        let mut failures = vec![];
        for (key, function) in functions {
            match verify_function_control_with_reference_inputs(function, false, true,
                &BTreeSet::new(), true, proofs) {
                Ok(control) => changed |= proofs.effect_calls.as_mut().expect("effect solver exists")
                    .outward.get_mut(key).expect("complete function domain").extend(&control.outward_operations),
                Err(error) => failures.push(error),
            }
        }
        if changed { continue; }
        // Missing successful coverage is not an empty outward set. A delayed
        // body gets retried after each growth step; an unresolved final body
        // rejects the graph, including recursive unsupported obligations.
        if let Some(error) = failures.into_iter().next() { return Err(error); }
        return Ok(());
    }
}

/// No provisional absence crosses the transfer-product publication boundary.
/// Subsequent body checks also ensure their observations remain covered when
/// actual entry hypotheses differ from the solver's parameter hypotheses.
pub(super) fn seal(proofs: &mut tail_provenance::TransferProofs) {
    if let Some(effects) = &mut proofs.effect_calls { effects.closed = true; }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(name: &[u8]) -> DefKey { DefKey(Digest::of_bytes(name)) }
    fn operation() -> Operation { Operation { effect: key(b"operation"), arguments: vec![], operation: 0 } }
    fn perform(dst: u32) -> VmInstruction {
        VmInstruction::PerformOwned { dst, effect: operation().effect, effect_arguments: vec![], operation: 0, arguments: vec![] }
    }
    fn function(name: &[u8], parameters: u32, registers: Vec<VmType>, instructions: Vec<VmInstruction>) -> VmFunction {
        let mut declared = vec![VmInstruction::DeclareResult { result: VmType::I64, returns: true }];
        declared.extend(instructions);
        VmFunction { definition: key(name), safety: Safety::Safe, unsafe_execution: false,
            captures: 0, parameters, nominal_copy_descriptors: vec![], registers, instructions: declared }
    }
    fn proof(functions: Vec<VmFunction>) -> tail_provenance::TransferProofs {
        tail_provenance::summaries(&functions.into_iter().map(|function| (function.definition, function)).collect()).unwrap()
    }

    #[test]
    fn reachable_operations_close_through_recursive_ordinary_calls() {
        let first = function(b"first", 1, vec![VmType::Bool, VmType::I64, VmType::I64], vec![
            VmInstruction::BranchBool { condition: 0, then_target: 2, else_target: 4 },
            perform(1), VmInstruction::Return { value: 1 },
            VmInstruction::CallOwned { dst: 2, callee: key(b"second"), arguments: vec![0] },
            VmInstruction::Return { value: 2 },
        ]);
        let second = function(b"second", 1, vec![VmType::Bool, VmType::I64], vec![
            VmInstruction::CallOwned { dst: 1, callee: key(b"first"), arguments: vec![0] },
            VmInstruction::Return { value: 1 },
        ]);
        let proofs = proof(vec![first, second]);
        let effects = proofs.effect_calls.as_ref().unwrap();
        assert!(effects.closed);
        for name in [b"first".as_slice(), b"second".as_slice()] {
            assert_eq!(effects.outward[&key(name)].operations(), &[operation()]);
        }
    }

    #[test]
    fn unreachable_performances_do_not_populate_an_outward_contract() {
        let leaf = function(b"leaf", 0, vec![VmType::I64, VmType::I64], vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 }, VmInstruction::Return { value: 0 },
            perform(1), VmInstruction::Return { value: 1 },
        ]);
        let proofs = proof(vec![leaf.clone()]);
        let effects = proofs.effect_calls.as_ref().unwrap();
        assert!(!effects.universe.operations().is_empty());
        assert!(effects.outward[&leaf.definition].operations().is_empty());
        check_callable(leaf.definition, &VmEffectRow::default(), &proofs).unwrap();

        let mut changed = leaf;
        changed.instructions[1] = perform(0);
        assert!(matches!(verify_function_control(&changed, false, false, &proofs),
            Err(VmArtifactError::MalformedEncoding { message: "executable outward-effect proof is incomplete" })));
    }

    #[test]
    fn missing_callee_is_not_a_proof_of_performance_absence() {
        let leaf = function(b"leaf", 0, vec![VmType::I64], vec![perform(0), VmInstruction::Return { value: 0 }]);
        let caller = function(b"caller", 0, vec![VmType::I64], vec![
            VmInstruction::CallOwned { dst: 0, callee: key(b"missing"), arguments: vec![] },
            VmInstruction::Return { value: 0 },
        ]);
        let functions = [leaf, caller].into_iter().map(|function| (function.definition, function)).collect();
        assert!(matches!(tail_provenance::summaries(&functions), Err(VmArtifactError::MissingFunction { .. })));
    }

    #[test]
    fn closed_and_open_callable_rows_use_the_same_checked_operation_universe() {
        let leaf = function(b"leaf", 0, vec![VmType::I64], vec![perform(0), VmInstruction::Return { value: 0 }]);
        let proofs = proof(vec![leaf.clone()]);
        assert!(check_callable(leaf.definition, &VmEffectRow::default(), &proofs).is_err());
        let named = VmEffectRow { effects: vec![VmEffectInstance { definition: operation().effect, arguments: vec![] }], ..Default::default() };
        check_callable(leaf.definition, &named, &proofs).unwrap();
        let open = VmEffectRow { tails: BTreeSet::from([EffectTail::Generic(0)]), ..Default::default() };
        for row in [named, open] {
            let callback = VmType::Callable { shared_receiver: false, unique_receiver: false, safety: Safety::Safe,
                parameters: vec![], result: Box::new(VmType::I64), effects: Box::new(row) };
            let caller = function(b"caller", 1, vec![callback, VmType::I64], vec![]);
            let invoked = invocation(&caller, &VmInstruction::CallIndirectOwned { dst: 1, callee: 0, arguments: vec![] }, &proofs).unwrap();
            assert_eq!(invoked.operations(), &[operation()]);
        }
    }
}
