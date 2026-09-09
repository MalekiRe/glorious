//! Forward owner availability is distinct from backwards value liveness.
//! An unread owner may still need destruction after a suspended invocation.
//! Values not yet initialized must never be included in that continuation.
use super::*;

type Inventory = BTreeSet<OwnerId>;
struct InventoryPlan {
    cleanup: Vec<Vec<Vec<OwnerId>>>,
    dispositions: Vec<Vec<(OwnerId, OwnerDisposition)>>,
    successors: Vec<Vec<Vec<OwnerId>>>,
}

impl OwnershipMir {
    fn common_operands<'a>(&self, terminator: &'a OwnershipTerminator) -> &'a [OwnershipOperand] {
        if matches!(terminator.control, ControlTerminator::SwitchBool { .. }) {
            &terminator.operands[..1]
        } else {
            &terminator.operands
        }
    }

    fn exit_scope(&self, terminator: &ControlTerminator) -> Option<ControlScopeId> {
        match terminator {
            ControlTerminator::Transfer(ControlTransfer::Leave { label, .. }) => {
                Some(self.labels[label.0 as usize].scope)
            }
            ControlTerminator::Transfer(
                ControlTransfer::FinishClause { handler, .. }
                | ControlTransfer::TailResume { handler, .. },
            ) => Some(self.handlers[handler.0 as usize].scope),
            _ => None,
        }
    }

    fn successor_inventory(
        &self,
        block: &OwnershipBlock,
        state: &Inventory,
        edge: &OwnershipSuccessor,
    ) -> Inventory {
        let mut state = state.clone();
        for operand in self.common_operands(&block.terminator) {
            self.consume_operand(*operand, &mut state);
        }
        if matches!(
            block.terminator.control,
            ControlTerminator::SwitchBool { .. }
        ) {
            for operand in &edge.arguments {
                self.consume_operand(*operand, &mut state);
            }
        }
        if let Some(scope) = self.exit_scope(&block.terminator.control) {
            state.retain(|owner| !self.scope_is_below(self.owners[owner.0 as usize].scope, scope));
        }
        state.extend(
            self.blocks[edge.target.0 as usize]
                .parameters
                .iter()
                .map(|value| self.owner_of(*value)),
        );
        state
    }
    fn scope_owners(&self, scope: ControlScopeId, destination: ControlValue) -> Vec<OwnerId> {
        self.owners
            .iter()
            .rev()
            .filter(|owner| {
                owner.scope == Some(scope)
                    && owner.value != destination
                    && !matches!(
                        owner.kind,
                        OwnerKind::View | OwnerKind::Continuation | OwnerKind::Capture(_)
                    )
            })
            .map(|owner| OwnerId(owner.value.0))
            .collect()
    }
    fn scope_is_below(&self, scope: Option<ControlScopeId>, ancestor: ControlScopeId) -> bool {
        let Some(mut scope) = scope else {
            return false;
        };
        if scope == ancestor {
            return false;
        }
        while let Some(parent) = self.scopes[scope.0 as usize].parent {
            if parent == ancestor {
                return true;
            }
            scope = parent;
        }
        false
    }
    fn owner_of(&self, mut value: ControlValue) -> OwnerId {
        while let Some(source) = self.aliases.get(&value) {
            value = *source;
        }
        OwnerId(value.0)
    }

    fn consume_operand(&self, operand: OwnershipOperand, state: &mut Inventory) {
        if operand.mode == ValueTransfer::Move {
            state.remove(&self.owner_of(operand.value));
        }
    }

    fn instruction_inventory(&self, instruction: &OwnershipInstruction, state: &mut Inventory) {
        match &instruction.operation {
            OwnershipOperation::Read(_) => return,
            OwnershipOperation::Transfer { value, mode } => self.consume_operand(
                OwnershipOperand {
                    value: *value,
                    mode: *mode,
                },
                state,
            ),
            OwnershipOperation::Construct { fields, .. } => {
                for operand in fields {
                    self.consume_operand(*operand, state);
                }
            }
            OwnershipOperation::Discard(owner) => {
                state.remove(&self.owner_of(ControlValue(owner.0)));
            }
            OwnershipOperation::ExitScope {
                scope,
                result,
                mode,
                ..
            } => {
                self.consume_operand(
                    OwnershipOperand {
                        value: *result,
                        mode: *mode,
                    },
                    state,
                );
                // The transfer function is independent of the emitted
                // cleanup certificate, which may be under validation.
                for owner in self.scope_owners(*scope, instruction.destination) {
                    state.remove(&owner);
                }
            }
            OwnershipOperation::MovePlace(
                ControlPlace::Local(value) | ControlPlace::Temporary(value),
            ) => {
                state.remove(&self.owner_of(*value));
            }
            OwnershipOperation::ReadPlace {
                place: ControlPlace::Local(value) | ControlPlace::Temporary(value),
                mode,
            } => {
                self.consume_operand(
                    OwnershipOperand {
                        value: *value,
                        mode: *mode,
                    },
                    state,
                );
            }
            OwnershipOperation::Replace { place, value, mode } => {
                self.consume_operand(
                    OwnershipOperand {
                        value: *value,
                        mode: *mode,
                    },
                    state,
                );
                if let ControlPlace::Local(value) | ControlPlace::Temporary(value) = place {
                    state.insert(self.owner_of(*value));
                }
            }
            OwnershipOperation::Capture { captures, .. } => {
                for (value, mode) in captures {
                    if *mode == crate::CaptureMode::Move {
                        state.remove(&self.owner_of(*value));
                    }
                }
            }
            _ => {}
        }
        if self.owners[instruction.destination.0 as usize].kind != OwnerKind::View {
            state.insert(OwnerId(instruction.destination.0));
        }
    }

    fn before_terminator(&self, block: &OwnershipBlock, incoming: &Inventory) -> Inventory {
        let mut state = incoming.clone();
        for instruction in &block.instructions {
            self.instruction_inventory(instruction, &mut state);
        }
        state
    }

    fn inventory_plan(&self) -> InventoryPlan {
        let mut incoming = vec![Inventory::new(); self.blocks.len()];
        let mut reachable = vec![false; self.blocks.len()];
        incoming[self.entry.0 as usize]
            .extend(self.parameters.iter().map(|value| self.owner_of(*value)));
        reachable[self.entry.0 as usize] = true;
        loop {
            let mut changed = false;
            for (index, block) in self.blocks.iter().enumerate() {
                if !reachable[index] {
                    continue;
                }
                let state = self.before_terminator(block, &incoming[index]);
                for edge in &block.terminator.successors {
                    let target = edge.target.0 as usize;
                    let edge_state = self.successor_inventory(block, &state, edge);
                    let previous = incoming[target].len();
                    incoming[target].extend(edge_state);
                    if previous != incoming[target].len() || !reachable[target] {
                        changed = true;
                    }
                    reachable[target] = true;
                }
            }
            if !changed {
                break;
            }
        }
        let mut cleanup = vec![];
        let mut dispositions = vec![];
        let mut successors = vec![];
        for (index, block) in self.blocks.iter().enumerate() {
            let mut state = incoming[index].clone();
            let mut block_cleanup = vec![];
            for instruction in &block.instructions {
                block_cleanup.push(match &instruction.operation {
                    OwnershipOperation::ExitScope {
                        scope,
                        result,
                        mode,
                        ..
                    } => {
                        // Forward the result first; its consumed source is no
                        // longer an owner at the following cleanup boundary.
                        let mut cleanup_state = state.clone();
                        self.consume_operand(
                            OwnershipOperand {
                                value: *result,
                                mode: *mode,
                            },
                            &mut cleanup_state,
                        );
                        self.scope_owners(*scope, instruction.destination)
                            .into_iter()
                            .filter(|owner| cleanup_state.contains(owner))
                            .collect()
                    }
                    _ => vec![],
                });
                self.instruction_inventory(instruction, &mut state);
            }
            cleanup.push(block_cleanup);
            successors.push(
                block
                    .terminator
                    .successors
                    .iter()
                    .map(|edge| {
                        self.successor_inventory(block, &state, edge)
                            .into_iter()
                            .collect()
                    })
                    .collect(),
            );
            // Copy exports a new value, not the original owner's identity.
            // The original still belongs to the active/suspended inventory.
            let transferred = self
                .common_operands(&block.terminator)
                .iter()
                .filter(|operand| operand.mode == ValueTransfer::Move)
                .map(|operand| self.owner_of(operand.value))
                .collect::<BTreeSet<_>>();
            let tail = matches!(&block.terminator.control,
                ControlTerminator::Invoke { contract, .. } if contract.mandatory_tail);
            let suspends = !tail && matches!(
                block.terminator.control,
                ControlTerminator::Invoke { .. }
                    | ControlTerminator::Transfer(ControlTransfer::Perform { .. })
            );
            let exit_scope = self.exit_scope(&block.terminator.control);
            dispositions.push(
                state
                    .into_iter()
                    .map(|owner| {
                        (
                            owner,
                            if transferred.contains(&owner) {
                                OwnerDisposition::Transfer
                            } else if suspends {
                                OwnerDisposition::Suspend
                            } else if matches!(
                                block.terminator.control,
                                ControlTerminator::Return(_)
                            ) && matches!(
                                self.owners[owner.0 as usize].kind,
                                OwnerKind::Capture(_)
                            ) {
                                OwnerDisposition::ReturnCapture
                            } else if matches!(
                                block.terminator.control,
                                ControlTerminator::Return(_)
                            ) || tail || exit_scope.is_some_and(|scope| {
                                self.scope_is_below(self.owners[owner.0 as usize].scope, scope)
                            }) {
                                OwnerDisposition::Abandon
                            } else {
                                OwnerDisposition::Retain
                            },
                        )
                    })
                    .collect(),
            );
        }
        InventoryPlan {
            cleanup,
            dispositions,
            successors,
        }
    }

    pub(super) fn validate_inventory(&self) -> Result<(), OwnershipError> {
        let InventoryPlan {
            cleanup,
            dispositions,
            successors,
        } = self.inventory_plan();
        for (((block, cleanup), dispositions), successors) in self
            .blocks
            .iter()
            .zip(cleanup)
            .zip(dispositions)
            .zip(successors)
        {
            for (instruction, expected) in block.instructions.iter().zip(cleanup) {
                if let OwnershipOperation::ExitScope { owners, .. } = &instruction.operation
                    && *owners != expected
                {
                    return Err(OwnershipError(
                        "scope cleanup disagrees with initialized owner inventory".into(),
                    ));
                }
            }
            if block.terminator.dispositions != dispositions {
                return Err(OwnershipError(
                    "terminator dispositions disagree with residual owner inventory".into(),
                ));
            }
            for (edge, inventory) in block.terminator.successors.iter().zip(successors) {
                if edge.inventory != inventory {
                    return Err(OwnershipError(
                        "successor inventory disagrees with selected edge transfers".into(),
                    ));
                }
            }
        }
        Ok(())
    }

    // Unlike cleanup's may-initialized inventory, a consuming use requires
    // an owner on every incoming path. Views are addresses whose production
    // was checked separately; lexical aliases resolve to their actual owner.
    pub(super) fn validate_owner_availability(&self) -> Result<(), OwnershipError> {
        let mut reachable = BTreeSet::new();
        let mut pending = vec![self.entry];
        while let Some(id) = pending.pop() {
            if reachable.insert(id) {
                pending.extend(
                    self.blocks[id.0 as usize]
                        .terminator
                        .successors
                        .iter()
                        .map(|edge| edge.target),
                );
            }
        }
        let all = self
            .owners
            .iter()
            .map(|owner| OwnerId(owner.value.0))
            .collect::<Inventory>();
        let mut incoming = vec![all; self.blocks.len()];
        incoming[self.entry.0 as usize] = self
            .parameters
            .iter()
            .map(|value| self.owner_of(*value))
            .collect();
        loop {
            let mut changed = false;
            for id in &reachable {
                let block = &self.blocks[id.0 as usize];
                let state = self.before_terminator(block, &incoming[id.0 as usize]);
                for edge in &block.terminator.successors {
                    let outgoing = self.successor_inventory(block, &state, edge);
                    let next = incoming[edge.target.0 as usize]
                        .intersection(&outgoing)
                        .copied()
                        .collect();
                    if next != incoming[edge.target.0 as usize] {
                        incoming[edge.target.0 as usize] = next;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        let require = |value: ControlValue, state: &Inventory| {
            let owner = self.owner_of(value);
            if state.contains(&owner) || self.owners[owner.0 as usize].kind == OwnerKind::View {
                Ok(())
            } else {
                Err(OwnershipError(format!(
                    "owner {} is not initialized on every incoming path in {:?} ({:?}, source {:?}, quantity {:?}, type {:?})",
                    owner.0, self.definition, self.owners[owner.0 as usize].kind,
                    self.values[owner.0 as usize].source,
                    self.owners[owner.0 as usize].quantity,
                    self.values[owner.0 as usize].ty
                )))
            }
        };
        let consume =
            |operand: OwnershipOperand, state: &mut Inventory| -> Result<(), OwnershipError> {
                require(operand.value, state)?;
                self.consume_operand(operand, state);
                Ok(())
            };
        for id in reachable {
            let block = &self.blocks[id.0 as usize];
            let mut state = incoming[id.0 as usize].clone();
            for instruction in &block.instructions {
                for value in instruction.operation.inputs(&self.loans) {
                    // Whole-slot replacement is initialization, not a read of
                    // the previously consumed value in that slot.
                    if matches!(&instruction.operation, OwnershipOperation::Replace { place: ControlPlace::Local(root) | ControlPlace::Temporary(root), value: replacement, .. }
                        if *root == value && *replacement != value)
                    {
                        continue;
                    }
                    require(value, &state).map_err(|error| OwnershipError(format!(
                        "{}; block {}, destination {}, operation {:?}",
                        error.0, id.0, instruction.destination.0, instruction.operation
                    )))?;
                }
                match &instruction.operation {
                    OwnershipOperation::Construct { fields, .. } => {
                        let mut consumed = state.clone();
                        for operand in fields {
                            consume(*operand, &mut consumed)?;
                        }
                    }
                    OwnershipOperation::Capture { captures, .. } => {
                        let mut consumed = state.clone();
                        for (value, mode) in captures {
                            consume(
                                OwnershipOperand {
                                    value: *value,
                                    mode: if *mode == crate::CaptureMode::Move {
                                        ValueTransfer::Move
                                    } else {
                                        ValueTransfer::Reborrow
                                    },
                                },
                                &mut consumed,
                            )?;
                        }
                    }
                    _ => {}
                }
                self.instruction_inventory(instruction, &mut state);
            }
            for operand in self.common_operands(&block.terminator) {
                consume(*operand, &mut state)?;
            }
            if matches!(
                block.terminator.control,
                ControlTerminator::SwitchBool { .. }
            ) {
                for edge in &block.terminator.successors {
                    let mut selected = state.clone();
                    for operand in &edge.arguments {
                        consume(*operand, &mut selected)?;
                    }
                }
            }
        }
        Ok(())
    }

    pub(super) fn elaborate_inventory(&mut self) {
        let InventoryPlan {
            cleanup,
            dispositions,
            successors,
        } = self.inventory_plan();
        for (((block, cleanup), dispositions), successors) in self
            .blocks
            .iter_mut()
            .zip(cleanup)
            .zip(dispositions)
            .zip(successors)
        {
            for (instruction, cleanup) in block.instructions.iter_mut().zip(cleanup) {
                if let OwnershipOperation::ExitScope { owners, .. } = &mut instruction.operation {
                    *owners = cleanup;
                }
            }
            block.terminator.dispositions = dispositions;
            for (edge, inventory) in block.terminator.successors.iter_mut().zip(successors) {
                edge.inventory = inventory;
            }
        }
    }
}
