//! Independent may-initialized inventory for abandoning and suspended edges.
//! Whole flags follow CFG moves; partial-path flags do not consume the root.
use super::*;
type Inventory = BTreeSet<ControlValue>;

impl CleanupMir {
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
    fn below_scope(&self, owner: &Owner, boundary: ControlScopeId) -> bool {
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
    fn plan_owners(&self, plan: CleanupPlanId) -> Vec<ControlValue> {
        self.plans[plan.0 as usize]
            .actions
            .iter()
            .filter_map(|action| match action {
                CleanupAction::StorageDead(flag) => Some(self.flags[flag.0 as usize].place.root()),
                _ => None,
            })
            .collect()
    }
    pub(super) fn validate_inventories(&self) -> Result<(), CleanupError> {
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
            if matches!(
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
