//! Replay Copy obligations extend through suspended ordinary-call frames.
//! Destruction inventories are already independently checked by `inventory`;
//! this pass checks their permissions in each reachable replay context.
use super::*;

type Operation = (crate::EffectInstance, u32);

fn collect<'a>(body: &'a CleanupMir, bodies: &mut BTreeMap<DefKey, &'a CleanupMir>) {
    bodies.insert(body.definition, body);
    for closure in &body.closures {
        collect(&closure.body, bodies);
    }
}

fn callees(body: &CleanupMir, control: &CleanupControl, bodies: &BTreeMap<DefKey, &CleanupMir>) -> Vec<DefKey> {
    match control {
        CleanupControl::Invoke {
            target: SpecializedCallTarget::Direct(target),
            ..
        } => bodies
            .contains_key(target)
            .then_some(*target)
            .into_iter()
            .collect(),
        // An unresolved callable can designate any closed body. The effect
        // summaries below still restrict propagation to the operation at issue.
        CleanupControl::Invoke {
            callee, target: SpecializedCallTarget::Indirect,
            ..
        } => {
            let arity = match &body.values[callee.0 as usize].ty {
                Type::Callable { parameters, .. } => Some(parameters.len()),
                _ => None,
            };
            bodies.iter().filter(|(_, candidate)| arity.is_none_or(|arity| {
                let captures = candidate.parameters.iter().filter(|value|
                    matches!(candidate.owners[value.0 as usize].kind, OwnerKind::Capture(_))).count();
                candidate.parameters.len() == arity + captures
            })).map(|(key, _)| *key).collect()
        }
        _ => vec![],
    }
}

fn escapes_call(body: &CleanupMir, control: &CleanupControl, operation: &Operation) -> bool {
    let CleanupControl::Invoke { callee, .. } = control else { return false; };
    match &body.values[callee.0 as usize].ty {
        Type::Callable { effects, .. } => effects.effects.contains(&operation.0)
            || effects.tail.is_some() || !effects.projections.is_empty(),
        _ => true,
    }
}

pub(super) fn validate(program: &CleanupProgram) -> Result<(), CleanupError> {
    let mut bodies = BTreeMap::new();
    for body in program.functions().values() {
        collect(body, &mut bodies);
    }
    if !bodies.values().any(|body| {
        body.handlers.iter().any(|handler| {
            handler.clauses.iter().any(|clause| {
                clause
                    .contract
                    .as_ref()
                    .is_some_and(|contract| contract.invocation.lower >= 2)
            })
        })
    }) {
        return Ok(());
    }
    let captures = bodies.iter().map(|(key, body)| (*key, body.capture_inventories()))
        .collect::<BTreeMap<_, _>>();
    let mut effects = bodies
        .iter()
        .map(|(key, body)| {
            let operations = body
                .blocks
                .iter()
                .filter_map(|block| match &block.terminator.control {
                    CleanupControl::Transfer(ControlTransfer::Perform {
                        effect,
                        operation,
                        ..
                    }) => Some((effect.clone(), *operation)),
                    _ => None,
                })
                .collect::<BTreeSet<Operation>>();
            (*key, operations)
        })
        .collect::<BTreeMap<_, _>>();
    loop {
        let mut changed = false;
        for (key, body) in &bodies {
            let inherited = body
                .blocks
                .iter()
                .flat_map(|block| callees(body, &block.terminator.control, &bodies).into_iter()
                    .flat_map(|callee| effects[&callee].iter())
                    .filter(|operation| escapes_call(body, &block.terminator.control, operation)).cloned())
                .collect::<BTreeSet<_>>();
            let summary = effects.get_mut(key).unwrap();
            let previous = summary.len();
            summary.extend(inherited);
            changed |= previous != summary.len();
        }
        if !changed {
            break;
        }
    }
    for root in bodies.values() {
        for block in &root.blocks {
            let CleanupControl::Transfer(ControlTransfer::EnterHandler {
                handler,
                computation,
                ..
            }) = &block.terminator.control
            else {
                continue;
            };
            let delimiter = &root.handlers[handler.0 as usize];
            let owned_roots = root.replay_owned_roots(*handler);
            for clause in &delimiter.clauses {
                if !clause
                    .contract
                    .as_ref()
                    .is_some_and(|c| c.invocation.lower >= 2)
                {
                    continue;
                }
                let operation = (clause.effect.clone(), clause.operation);
                // `local` distinguishes the installing frame from recursive
                // invocations of that same function, which belong wholly to
                // the captured continuation.
                let mut pending = vec![(root.definition, computation.target, true)];
                let mut visited = BTreeSet::new();
                while let Some((definition, target, local)) = pending.pop() {
                    if !visited.insert((definition, target, local)) {
                        continue;
                    }
                    let body = bodies[&definition];
                    let block = &body.blocks[target.0 as usize];
                    let control = &block.terminator.control;
                    if local
                        && matches!(control,
                        CleanupControl::Transfer(ControlTransfer::CompleteHandler { handler: exited, .. }
                            | ControlTransfer::FinishClause { handler: exited, .. }) if exited == handler)
                    {
                        continue;
                    }
                    let called = callees(body, control, &bodies)
                        .into_iter()
                        .filter(|callee| effects[callee].contains(&operation) && escapes_call(body, control, &operation))
                        .collect::<Vec<_>>();
                    let performs = matches!(control,
                        CleanupControl::Transfer(ControlTransfer::Perform { effect, operation: op, .. })
                            if effect == &operation.0 && *op == operation.1);
                    if performs || !called.is_empty() {
                        for value in &captures[&definition][target.0 as usize] {
                            let owner = &body.owners[value.0 as usize];
                            if (!local || owned_roots.contains(value)) && match owner.kind {
                                OwnerKind::Capture(crate::CaptureMode::UniqueBorrow) => true,
                                OwnerKind::Capture(crate::CaptureMode::Copy | crate::CaptureMode::Move) =>
                                    owner.quantity != Some(crate::Quantity::UNRESTRICTED),
                                _ => false,
                            } {
                                return Err(CleanupError(format!(
                                    "Cleanup {:?} block {}: replay cannot duplicate capture {} without Copy permission",
                                    definition, target.0, value.0
                                )));
                            }
                        }
                        for value in body.plan_owners(block.terminator.cancellation) {
                            let owner = body
                                .owners
                                .iter()
                                .find(|owner| owner.value == value)
                                .ok_or_else(|| {
                                    CleanupError("replay inventory owner is absent".into())
                                })?;
                            if (!local || owned_roots.contains(&value))
                                && owner.quantity != Some(crate::Quantity::UNRESTRICTED)
                            {
                                return Err(CleanupError(format!(
                                    "Cleanup {:?} block {}: replay cannot duplicate live owner {} without Copy permission across a suspended call",
                                    definition, target.0, value.0
                                )));
                            }
                        }
                    }
                    for callee in called {
                        pending.push((callee, bodies[&callee].entry, false));
                    }
                    pending.extend(
                        block
                            .terminator
                            .successors
                            .iter()
                            .map(|edge| (definition, edge.target, local)),
                    );
                }
            }
        }
    }
    Ok(())
}
