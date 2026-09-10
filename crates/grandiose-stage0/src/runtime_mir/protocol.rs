use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeSlotClass {
    Capture,
    Parameter,
    Addressable,
    Flag,
    Counter,
    Temporary,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeSlot {
    pub local: MirLocal,
    pub class: RuntimeSlotClass,
    pub ty: Type,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimePassing {
    /// An owned value carrier, consumed by the call.
    Owned,
    /// A consumed reference carrier; the referenced owner remains borrowed.
    Shared,
    Unique,
    /// Invocation borrows the callable; only its prepared parameters move.
    Receiver,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeArgument {
    pub local: MirLocal,
    pub passing: RuntimePassing,
    pub ty: Type,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RuntimeTransferKind {
    Call(DefKey),
    TailCall(DefKey),
    IndirectCall,
    HostCall,
    Perform(MirPerformSiteId),
    Capture(MirResumptionSiteId),
    Resume(MirResumptionSiteId),
    ResumeReturn(MirResumptionSiteId),
    ResumeSnapshot(MirResumptionSiteId),
    Cancel(MirResumptionSiteId),
    Forward(MirResumptionSiteId),
    CompleteHandler,
    Return,
    Leave(MirLabelId),
    Abort,
}
/// A point before the named operation; `instruction == block.len()` denotes
/// the terminator. Results are installed only on a successful normal return.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeTransfer {
    pub id: u32,
    pub block: MirBlockId,
    pub instruction: u32,
    pub kind: RuntimeTransferKind,
    pub arguments: Vec<RuntimeArgument>,
    pub result: Option<MirLocal>,
    /// Owners remaining in this frame after outgoing carriers are handed off.
    pub retained: Vec<MirLocal>,
    pub cancellation: Vec<MirFrameDrop>,
    pub handler_prefix: Vec<MirHandlerSiteId>,
}
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RuntimeFrame {
    pub slots: Vec<RuntimeSlot>,
    pub capture_parameters: Vec<MirLocal>,
    pub invocation_parameters: Vec<RuntimeArgument>,
    pub owners: Vec<MirLocal>,
    pub abandonment: Vec<MirFrameDrop>,
    pub transfers: Vec<RuntimeTransfer>,
}

impl RuntimeMir {
    pub(super) fn derive_frame(&self) -> Result<RuntimeFrame, String> {
        if self.captures as usize > self.parameters.len() {
            return Err("Runtime capture ABI exceeds parameter layout".into());
        }
        let captures = &self.parameters[..self.captures as usize];
        let counters = self
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter_map(|op| {
                if let RuntimeOperation::StoreUsize { dst, .. } = op {
                    Some(*dst)
                } else {
                    None
                }
            })
            .collect::<BTreeSet<_>>();
        let parameters = self.parameters.iter().copied().collect::<BTreeSet<_>>();
        let bindings = self
            .control
            .source_storage
            .binding_locals
            .iter()
            .flatten()
            .copied()
            .collect::<BTreeSet<_>>();
        let flags = self
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter_map(|operation| match operation {
                RuntimeOperation::SetDropFlag { flag, .. } => Some(*flag),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let slots = self
            .locals
            .iter()
            .enumerate()
            .map(|(index, decl)| {
                let local = MirLocal(index as u32);
                RuntimeSlot {
                    local,
                    ty: decl.ty.clone(),
                    class: if captures.contains(&local) {
                        RuntimeSlotClass::Capture
                    } else if parameters.contains(&local) {
                        RuntimeSlotClass::Parameter
                    } else if bindings.contains(&local) {
                        RuntimeSlotClass::Addressable
                    } else if counters.contains(&local) {
                        RuntimeSlotClass::Counter
                    } else if flags.contains(&local) {
                        RuntimeSlotClass::Flag
                    } else {
                        RuntimeSlotClass::Temporary
                    },
                }
            })
            .collect();
        let argument = |local: MirLocal| -> Result<RuntimeArgument, String> {
            let ty = self
                .locals
                .get(local.0 as usize)
                .ok_or("Runtime ABI references an absent slot")?
                .ty
                .clone();
            let passing = match &ty {
                Type::Reference {
                    mutability: crate::Mutability::Shared,
                    ..
                } => RuntimePassing::Shared,
                Type::Reference {
                    mutability: crate::Mutability::Unique,
                    ..
                } => RuntimePassing::Unique,
                _ => RuntimePassing::Owned,
            };
            Ok(RuntimeArgument { local, ty, passing })
        };
        let owners = self.control.cleanup_owners.clone().unwrap_or_else(|| {
            self.parameters
                .iter()
                .skip(self.captures as usize)
                .rev()
                .copied()
                .collect()
        });
        let mut transfers = Vec::new();
        let entries = self.may_initialized_entries();
        for (index, block) in self.blocks.iter().enumerate() {
            let mut initialized = entries[index].clone();
            for parameter in &block.parameters {
                initialized.insert(*parameter);
            }
            let mut handlers = self.handler_prefix(block.scope)?;
            for (offset, operation) in block.instructions.iter().enumerate() {
                let contract = match operation {
                    RuntimeOperation::Call {
                        dst,
                        callee,
                        arguments,
                    } => Some((
                        RuntimeTransferKind::Call(*callee),
                        arguments.clone(),
                        Some(*dst),
                    )),
                    RuntimeOperation::CallPrepared { dst, callee, arguments }
                    | RuntimeOperation::CallIndirect {
                        dst,
                        callee,
                        arguments,
                    } => Some((
                        RuntimeTransferKind::IndirectCall,
                        std::iter::once(*callee)
                            .chain(arguments.iter().copied())
                            .collect(),
                        Some(*dst),
                    )),
                    RuntimeOperation::HostCall { dst, arguments, .. } => {
                        Some((RuntimeTransferKind::HostCall, arguments.clone(), Some(*dst)))
                    }
                    RuntimeOperation::Perform {
                        dst,
                        site,
                        arguments,
                        ..
                    } => Some((
                        RuntimeTransferKind::Perform(*site),
                        arguments.clone(),
                        Some(*dst),
                    )),
                    RuntimeOperation::CaptureResumption { dst, site } => {
                        Some((RuntimeTransferKind::Capture(*site), vec![], Some(*dst)))
                    }
                    RuntimeOperation::Resume { site, value } => {
                        Some((RuntimeTransferKind::Resume(*site), vec![*value], None))
                    }
                    RuntimeOperation::ResumeReturn { site, dst, value } => Some((
                        RuntimeTransferKind::ResumeReturn(*site),
                        vec![*value],
                        Some(*dst),
                    )),
                    RuntimeOperation::ResumeSnapshot {
                        site,
                        snapshot,
                        value,
                    } => Some((
                        RuntimeTransferKind::ResumeSnapshot(*site),
                        vec![*snapshot, *value],
                        None,
                    )),
                    RuntimeOperation::Cancel { site } => {
                        Some((RuntimeTransferKind::Cancel(*site), vec![], None))
                    }
                    RuntimeOperation::Forward { site } => {
                        Some((RuntimeTransferKind::Forward(*site), vec![], None))
                    }
                    RuntimeOperation::CompleteHandler { value } => {
                        Some((RuntimeTransferKind::CompleteHandler, vec![*value], None))
                    }
                    RuntimeOperation::Abort => Some((RuntimeTransferKind::Abort, vec![], None)),
                    _ => None,
                };
                if let Some((kind, arguments, result)) = contract {
                    let consumed = consumed_carriers(operation);
                    let retained = owners
                        .iter()
                        .copied()
                        .filter(|local| initialized.contains(local) && !consumed.contains(local))
                        .collect::<Vec<_>>();
                    let mut arguments = arguments
                        .into_iter()
                        .map(argument)
                        .collect::<Result<Vec<_>, _>>()?;
                    if matches!(kind, RuntimeTransferKind::IndirectCall) {
                        arguments[0].passing = RuntimePassing::Receiver;
                    }
                    transfers.push(RuntimeTransfer {
                        id: transfers.len() as u32,
                        block: MirBlockId(index as u32),
                        instruction: offset as u32,
                        kind,
                        arguments,
                        result,
                        cancellation: self
                            .control
                            .frame_cleanup
                            .iter()
                            .filter(|drop| retained.contains(&drop.owner))
                            .cloned()
                            .collect(),
                        retained,
                        handler_prefix: handlers.clone(),
                    });
                }
                match operation {
                    RuntimeOperation::InstallHandler { site, .. } => handlers.push(*site),
                    RuntimeOperation::UninstallHandler => {
                        handlers.pop();
                    }
                    _ => {}
                }
                transition(operation, &mut initialized);
            }
            let contract = match &block.terminator {
                RuntimeTerminator::TailCall { callee, arguments } =>
                    Some((RuntimeTransferKind::TailCall(*callee), arguments.clone())),
                RuntimeTerminator::Return { value } => {
                    Some((RuntimeTransferKind::Return, vec![*value]))
                }
                RuntimeTerminator::Leave {
                    label, arguments, ..
                } => Some((RuntimeTransferKind::Leave(*label), arguments.clone())),
                _ => None,
            };
            if let Some((kind, arguments)) = contract {
                let retained = owners
                    .iter()
                    .copied()
                    .filter(|local| initialized.contains(local) && !arguments.contains(local))
                    .collect::<Vec<_>>();
                transfers.push(RuntimeTransfer {
                    id: transfers.len() as u32,
                    block: MirBlockId(index as u32),
                    instruction: block.instructions.len() as u32,
                    kind,
                    arguments: arguments
                        .into_iter()
                        .map(argument)
                        .collect::<Result<_, _>>()?,
                    result: None,
                    cancellation: self
                        .control
                        .frame_cleanup
                        .iter()
                        .filter(|drop| retained.contains(&drop.owner))
                        .cloned()
                        .collect(),
                    retained,
                    handler_prefix: handlers,
                });
            }
        }
        Ok(RuntimeFrame {
            slots,
            capture_parameters: captures.to_vec(),
            invocation_parameters: self
                .parameters
                .iter()
                .skip(self.captures as usize)
                .copied()
                .map(argument)
                .collect::<Result<_, _>>()?,
            owners,
            abandonment: self.control.frame_cleanup.clone(),
            transfers,
        })
    }

    fn handler_prefix(&self, scope: MirScopeId) -> Result<Vec<MirHandlerSiteId>, String> {
        let mut current = Some(scope);
        let mut prefix = Vec::new();
        let mut seen = BTreeSet::new();
        while let Some(scope) = current {
            if !seen.insert(scope) {
                return Err("Runtime scope ancestry is cyclic".into());
            }
            let scope = self
                .control
                .scopes
                .get(scope.0 as usize)
                .ok_or("Runtime scope is absent")?;
            if let Some(site) = scope.entered_handler {
                prefix.push(site);
            }
            current = scope.parent;
        }
        prefix.reverse();
        Ok(prefix)
    }

    fn may_initialized_entries(&self) -> Vec<BTreeSet<MirLocal>> {
        let mut entries = vec![BTreeSet::new(); self.blocks.len()];
        if self.entry.0 as usize >= entries.len() {
            return entries;
        }
        entries[self.entry.0 as usize].extend(self.parameters.iter().copied());
        let mut pending = VecDeque::from([self.entry]);
        let mut visited = BTreeSet::new();
        while let Some(id) = pending.pop_front() {
            let block = &self.blocks[id.0 as usize];
            let mut live = entries[id.0 as usize].clone();
            live.extend(block.parameters.iter().copied());
            let mut dynamic = Vec::new();
            for operation in &block.instructions {
                match operation {
                    RuntimeOperation::MakeLabel {
                        target,
                        destination,
                        ..
                    } => dynamic.push((*target, vec![*destination], live.clone())),
                    RuntimeOperation::InstallHandler {
                        target,
                        payload_destinations,
                        ..
                    } => dynamic.push((*target, payload_destinations.clone(), live.clone())),
                    _ => {}
                }
                transition(operation, &mut live);
            }
            let edges = match &block.terminator {
                RuntimeTerminator::Goto { target, arguments }
                | RuntimeTerminator::Leave {
                    target, arguments, ..
                } => vec![(*target, arguments.clone())],
                RuntimeTerminator::SwitchBool {
                    then_target,
                    then_arguments,
                    else_target,
                    else_arguments,
                    ..
                } => vec![
                    (*then_target, then_arguments.clone()),
                    (*else_target, else_arguments.clone()),
                ],
                _ => vec![],
            };
            dynamic.extend(
                edges
                    .into_iter()
                    .map(|(target, arguments)| (target, arguments, live.clone())),
            );
            for (target, arguments, mut state) in dynamic {
                let Some(block) = self.blocks.get(target.0 as usize) else {
                    continue;
                };
                for argument in arguments {
                    state.remove(&argument);
                }
                state.extend(block.parameters.iter().copied());
                let entry = &mut entries[target.0 as usize];
                let old = entry.len();
                entry.extend(state);
                if visited.insert(target) || old != entry.len() {
                    pending.push_back(target);
                }
            }
        }
        entries
    }
}

pub(super) fn consumed_carriers(operation: &RuntimeOperation) -> &[MirLocal] {
    match operation {
        RuntimeOperation::Call { arguments, .. }
        | RuntimeOperation::CallIndirect { arguments, .. }
        | RuntimeOperation::CallPrepared { arguments, .. }
        | RuntimeOperation::HostCall { arguments, .. }
        | RuntimeOperation::Perform { arguments, .. } => arguments,
        RuntimeOperation::Resume { value, .. }
        | RuntimeOperation::ResumeReturn { value, .. }
        | RuntimeOperation::ResumeSnapshot { value, .. } => std::slice::from_ref(value),
        RuntimeOperation::Store { src, .. } => std::slice::from_ref(src),
        RuntimeOperation::MakeTuple { fields, .. } | RuntimeOperation::MakeArray { fields, .. }
        | RuntimeOperation::MakeRecord { fields, .. } | RuntimeOperation::MakeEnum { fields, .. } => fields,
        _ => &[],
    }
}

fn transition(operation: &RuntimeOperation, initialized: &mut BTreeSet<MirLocal>) {
    for argument in consumed_carriers(operation) {
        initialized.remove(argument);
    }
    match operation {
        RuntimeOperation::Move { src, .. }
        | RuntimeOperation::DestroyCallable { value: src, .. }
        | RuntimeOperation::StorageDead { local: src, .. }
        | RuntimeOperation::DestroyIf { local: src, .. } => {
            initialized.remove(src);
        }
        _ => {}
    }
    if let Some(destination) = operation.destination() {
        initialized.insert(destination);
    }
}
