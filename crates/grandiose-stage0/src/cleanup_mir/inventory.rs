//! Independent may-initialized inventory for abandoning and suspended edges.
//! Whole flags follow CFG moves; partial-path flags do not consume the root.
use super::*;
type Inventory = BTreeSet<ControlValue>;

pub(crate) struct HandlerStorageRoots {
    /// Protected graph roots, including outer owners consumed after resume.
    pub continuation: BTreeSet<ControlValue>,
    /// Fresh owning roots for each dynamically entered clause, in clause order.
    /// Outer lexical storage is shared, never reallocated as a clause local.
    pub clauses: Vec<BTreeSet<ControlValue>>,
}

impl CleanupMir {
    /// Partition protected and clause graph ownership using frozen definitions,
    /// scopes and control exits. Mere borrowed access keeps outer storage shared;
    /// lexical allocation time alone does not determine capture mode.
    pub(crate) fn handler_storage_roots(&self, handler: ControlHandlerId) -> HandlerStorageRoots {
        let delimiter = &self.handlers[handler.0 as usize];
        let entries = self
            .blocks
            .iter()
            .filter_map(|block| match &block.terminator.control {
                CleanupControl::Transfer(ControlTransfer::EnterHandler {
                    handler: entered,
                    computation,
                    ..
                }) if *entered == handler => Some(computation.target),
                _ => None,
            })
            .collect::<Vec<_>>();
        let (mut roots, mut resumed) = self.handler_region_roots(handler, entries);
        // Only consumption in a resumed suffix requires duplication of an
        // outer owner. Consuming it before suspension, or in the selected
        // clause rather than its continuation, does not capture that owner.
        let mut visited = BTreeSet::new();
        while let Some(target) = resumed.pop() {
            if !visited.insert(target) { continue; }
            let block = &self.blocks[target.0 as usize];
            for flags in block
                .instructions
                .iter()
                .map(|instruction| &instruction.flags)
                .chain(std::iter::once(&block.terminator.flags))
                .chain(&block.terminator.edge_flags)
            {
                for write in flags.before.iter().chain(&flags.after) {
                    if !write.initialized {
                        roots.insert(self.flags[write.flag.0 as usize].place.root());
                    }
                }
            }
            if self.exits_handler_region(&block.terminator.control, handler) { continue; }
            resumed.extend(block.terminator.successors.iter().map(|edge| edge.target));
        }
        HandlerStorageRoots {
            continuation: roots,
            clauses: delimiter.clauses.iter().map(|clause|
                self.handler_region_roots(handler, vec![clause.entry]).0).collect(),
        }
    }

    fn exits_handler_region(&self, control: &CleanupControl, handler: ControlHandlerId) -> bool {
        match control {
            CleanupControl::Transfer(ControlTransfer::CompleteHandler { handler: exited, .. }
                | ControlTransfer::FinishClause { handler: exited, .. }) => *exited == handler,
            CleanupControl::Transfer(ControlTransfer::Leave { label, .. }) =>
                !self.labels[label.0 as usize].handler_prefix.iter().any(|(retained, _)| *retained == handler),
            _ => false,
        }
    }

    fn handler_region_roots(&self, handler: ControlHandlerId, mut pending: Vec<ControlBlockId>)
        -> (BTreeSet<ControlValue>, Vec<ControlBlockId>) {
        let delimiter = &self.handlers[handler.0 as usize];
        let mut roots = BTreeSet::new();
        let mut visited = BTreeSet::new();
        let mut resumed = Vec::new();
        while let Some(target) = pending.pop() {
            if !visited.insert(target) {
                continue;
            }
            let block = &self.blocks[target.0 as usize];
            // Sibling storage can be lexically below the delimiter too.
            // Select actual definitions on this region's graph before
            // classifying roots, and stop at exits to enclosing labels.
            for value in block.parameters.iter().copied().chain(block.instructions.iter().map(|instruction| instruction.destination)) {
                let owner = &self.owners[value.0 as usize];
                if self.frame_owner(owner) && !self.aliases.contains_key(&value)
                    && self.below_scope(owner, delimiter.scope) {
                    roots.insert(value);
                }
            }
            if self.exits_handler_region(&block.terminator.control, handler) { continue; }
            let suspends = match &block.terminator.control {
                CleanupControl::Transfer(ControlTransfer::Perform { effect, operation, .. }) =>
                    delimiter.clauses.iter().any(|clause| clause.effect == *effect && clause.operation == *operation),
                CleanupControl::Invoke { callee, .. } => match &self.values[callee.0 as usize].ty {
                    Type::Callable { effects, .. } => delimiter.clauses.iter().any(|clause| effects.effects.contains(&clause.effect)),
                    _ => false,
                },
                _ => false,
            };
            if suspends {
                resumed.extend(block.terminator.successors.iter().map(|edge| edge.target));
            }
            pending.extend(block.terminator.successors.iter().map(|edge| edge.target));
        }
        (roots, resumed)
    }
    fn apply_writes(&self, state: &mut Inventory, writes: &[FlagTransition]) {
        for write in writes {
            let place = &self.flags[write.flag.0 as usize].place;
            if let ControlPlace::Local(value) | ControlPlace::Temporary(value) = place {
                if write.initialized {
                    state.insert(*value);
                } else {
                    state.remove(value);
                }
            }
        }
    }
    fn apply_plan(&self, state: &mut Inventory, plan: CleanupPlanId) {
        for action in &self.plans[plan.0 as usize].actions {
            if let CleanupAction::StorageDead(flag) = action
                && let ControlPlace::Local(value) | ControlPlace::Temporary(value) =
                    self.flags[flag.0 as usize].place
            {
                state.remove(&value);
            }
        }
    }
    fn before_transfer(&self, index: usize, incoming: &Inventory) -> Inventory {
        let mut state = incoming.clone();
        for instruction in &self.blocks[index].instructions {
            self.apply_writes(&mut state, &instruction.flags.before);
            if let CleanupOperation::Replace { cleanup, .. } = instruction.operation {
                self.apply_plan(&mut state, cleanup);
            }
            self.apply_writes(&mut state, &instruction.flags.after);
            match instruction.operation {
                CleanupOperation::Destroy(plan) | CleanupOperation::RunCleanup { plan, .. } => {
                    self.apply_plan(&mut state, plan)
                }
                _ => {}
            }
        }
        self.apply_writes(&mut state, &self.blocks[index].terminator.flags.before);
        state
    }
    fn boundary_scope(&self, control: &CleanupControl) -> Option<ControlScopeId> {
        match control {
            CleanupControl::Transfer(ControlTransfer::Leave { label, .. }) => {
                Some(self.labels[label.0 as usize].scope)
            }
            CleanupControl::Transfer(
                ControlTransfer::FinishClause { handler, .. }
                | ControlTransfer::TailResume { handler, .. },
            ) => Some(self.handlers[handler.0 as usize].scope),
            _ => None,
        }
    }
    pub(super) fn below_scope(&self, owner: &Owner, boundary: ControlScopeId) -> bool {
        let Some(mut scope) = owner.scope else {
            return false;
        };
        while let Some(parent) = self.scopes[scope.0 as usize].parent {
            if parent == boundary {
                return true;
            }
            scope = parent;
        }
        false
    }
    pub(super) fn plan_owners(&self, plan: CleanupPlanId) -> Vec<ControlValue> {
        self.plans[plan.0 as usize]
            .actions
            .iter()
            .filter_map(|action| match action {
                CleanupAction::StorageDead(flag) => Some(self.flags[flag.0 as usize].place.root()),
                _ => None,
            })
            .collect()
    }
    fn incoming_inventories(&self) -> (Vec<Inventory>, Vec<bool>) {
        let mut incoming = vec![Inventory::new(); self.blocks.len()];
        incoming[self.entry.0 as usize].extend(self.parameters.iter().copied());
        let mut reachable = vec![false; self.blocks.len()];
        reachable[self.entry.0 as usize] = true;
        loop {
            let mut changed = false;
            for (index, block) in self.blocks.iter().enumerate() {
                if !reachable[index] {
                    continue;
                }
                let mut state = self.before_transfer(index, &incoming[index]);
                self.apply_plan(&mut state, block.terminator.cleanup);
                self.apply_writes(&mut state, &block.terminator.flags.after);
                for (edge, flags) in block
                    .terminator
                    .successors
                    .iter()
                    .zip(&block.terminator.edge_flags)
                {
                    let mut outgoing = state.clone();
                    self.apply_writes(&mut outgoing, &flags.before);
                    self.apply_writes(&mut outgoing, &flags.after);
                    let target = edge.target.0 as usize;
                    let previous = incoming[target].len();
                    incoming[target].extend(outgoing);
                    changed |= previous != incoming[target].len() || !reachable[target];
                    reachable[target] = true;
                }
            }
            if !changed {
                break;
            }
        }
        (incoming, reachable)
    }

    pub(super) fn capture_inventories(&self) -> Vec<Vec<ControlValue>> {
        let (incoming, reachable) = self.incoming_inventories();
        incoming.iter().enumerate().map(|(index, state)| {
            if !reachable[index] { return vec![]; }
            let state = self.before_transfer(index, state);
            self.owners.iter().filter(|owner| matches!(owner.kind, OwnerKind::Capture(_))
                && state.contains(&owner.value)).map(|owner| owner.value).collect()
        }).collect()
    }

    pub(super) fn validate_inventories(&self) -> Result<(), CleanupError> {
        let mut replay_regions = Vec::new();
        for block in &self.blocks {
            let CleanupControl::Transfer(ControlTransfer::EnterHandler {
                handler, computation, ..
            }) = &block.terminator.control else { continue; };
            let owner = &self.handlers[handler.0 as usize];
            if !owner.clauses.iter().any(|clause| clause.contract.as_ref()
                .is_some_and(|contract| contract.invocation.lower >= 2)) { continue; }
            let mut region = BTreeSet::new();
            let mut pending = vec![computation.target];
            while let Some(target) = pending.pop() {
                if !region.insert(target) { continue; }
                let block = &self.blocks[target.0 as usize];
                if matches!(&block.terminator.control,
                    CleanupControl::Transfer(ControlTransfer::CompleteHandler { handler: exited, .. }
                        | ControlTransfer::FinishClause { handler: exited, .. }) if exited == handler)
                { continue; }
                pending.extend(block.terminator.successors.iter().map(|edge| edge.target));
            }
            replay_regions.push((owner, region));
        }
        let (incoming, reachable) = self.incoming_inventories();
        for (index, block) in self.blocks.iter().enumerate() {
            if !reachable[index] {
                continue;
            }
            let mut prefix = incoming[index].clone();
            for instruction in &block.instructions {
                self.apply_writes(&mut prefix, &instruction.flags.before);
                if let CleanupOperation::Replace { cleanup, .. } = instruction.operation {
                    self.apply_plan(&mut prefix, cleanup);
                }
                self.apply_writes(&mut prefix, &instruction.flags.after);
                if let CleanupOperation::RunCleanup { scope, plan, .. } = instruction.operation {
                    let protected = &self.plans[plan.0 as usize].protected;
                    let expected = self
                        .owners
                        .iter()
                        .rev()
                        .filter(|owner| {
                            owner.scope == Some(scope)
                                && self.frame_owner(owner)
                                && prefix.contains(&owner.value)
                                && !protected.contains(&owner.value)
                        })
                        .map(|owner| owner.value)
                        .collect::<Vec<_>>();
                    if self.plan_owners(plan) != expected {
                        return Err(CleanupError(format!(
                            "Cleanup {:?} block {index}: lexical scope cleanup is incomplete",
                            self.definition
                        )));
                    }
                }
                match instruction.operation {
                    CleanupOperation::Destroy(plan) | CleanupOperation::RunCleanup { plan, .. } => {
                        self.apply_plan(&mut prefix, plan)
                    }
                    _ => {}
                }
            }
            let state = self.before_transfer(index, &incoming[index]);
            let expected = self
                .owners
                .iter()
                .rev()
                .filter(|owner| self.frame_owner(owner) && state.contains(&owner.value))
                .collect::<Vec<_>>();
            if let CleanupControl::Transfer(ControlTransfer::Perform {
                effect, operation, ..
            }) = &block.terminator.control
            {
                for (handler, region) in &replay_regions {
                    if !region.contains(&ControlBlockId(index as u32))
                        || !handler.clauses.iter().any(|clause| {
                            &clause.effect == effect
                                && clause.operation == *operation
                                && clause
                                    .contract
                                    .as_ref()
                                    .is_some_and(|contract| contract.invocation.lower >= 2)
                        })
                    {
                        continue;
                    }
                    if let Some(owner) = expected.iter().find(|owner| {
                        self.below_scope(owner, handler.scope)
                            && owner.quantity != Some(crate::Quantity::UNRESTRICTED)
                    }) {
                        return Err(CleanupError(format!(
                            "Cleanup {:?} block {index}: replay cannot duplicate live owner {} without Copy permission",
                            self.definition, owner.value.0
                        )));
                    }
                }
            }
            if !matches!(&block.terminator.control,
                CleanupControl::Invoke { contract, .. } if contract.mandatory_tail) && matches!(
                block.terminator.control,
                CleanupControl::Invoke { .. }
                    | CleanupControl::Transfer(ControlTransfer::Perform { .. })
            ) {
                let expected = expected.iter().map(|owner| owner.value).collect::<Vec<_>>();
                if self.plan_owners(block.terminator.cancellation) != expected {
                    return Err(CleanupError(format!(
                        "Cleanup {:?} block {index}: suspension plan is not its exact residual inventory",
                        self.definition
                    )));
                }
            }
            if let Some(boundary) = self.boundary_scope(&block.terminator.control) {
                let expected = expected
                    .iter()
                    .filter(|owner| self.below_scope(owner, boundary))
                    .map(|owner| owner.value)
                    .collect::<Vec<_>>();
                if self.plan_owners(block.terminator.cleanup) != expected {
                    return Err(CleanupError(format!(
                        "Cleanup {:?} block {index}: abandoning edge has an incomplete scope cleanup",
                        self.definition
                    )));
                }
            }
        }
        Ok(())
    }
}
