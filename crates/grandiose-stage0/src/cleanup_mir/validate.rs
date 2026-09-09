use super::*;

impl CleanupMir {
    pub fn validate(&self) -> Result<(), CleanupError> {
        let invalid =
            |message: &str| CleanupError(format!("Cleanup {:?}: {message}", self.definition));
        if self.blocks.is_empty()
            || self.entry.0 as usize >= self.blocks.len()
            || self.values.len() != self.owners.len()
        {
            return Err(invalid("incomplete body"));
        }
        for (index, scope) in self.scopes.iter().enumerate() {
            if scope
                .parent
                .is_some_and(|parent| parent.0 as usize >= index)
            {
                return Err(invalid("scope ancestry is cyclic or absent"));
            }
        }
        for (index, owner) in self.owners.iter().enumerate() {
            if owner.value.0 as usize != index
                || owner
                    .scope
                    .is_some_and(|scope| scope.0 as usize >= self.scopes.len())
            {
                return Err(invalid("owner identity or scope is absent"));
            }
        }
        for (index, loan) in self.loans.iter().enumerate() {
            let ty = self.place_type(&loan.place)?;
            if loan.id.0 as usize != index || self.values.get(loan.destination.0 as usize).is_none_or(|value|
                !matches!(&value.ty, Type::Reference { mutability, referent, .. } if **referent == ty && (*mutability == crate::Mutability::Unique) == loan.unique)) {
                return Err(invalid("loan identity or referent contract mismatch"));
            }
        }
        crate::specialized_mir::closed_type(&self.result).map_err(|error| CleanupError(error.0))?;
        for value in &self.values {
            crate::specialized_mir::closed_type(&value.ty)
                .map_err(|error| CleanupError(error.0))?;
        }
        crate::specialized_mir::validate_layout_closure(&self.layouts)
            .map_err(|error| CleanupError(error.0))?;
        self.validate_graph()?;
        for (index, flag) in self.flags.iter().enumerate() {
            if self.place_type(&flag.place)? != flag.ty
                || flag.place.root().0 as usize >= self.values.len()
                || self.flags[..index]
                    .iter()
                    .any(|previous| previous.place == flag.place)
            {
                return Err(invalid("invalid or duplicate initialization flag"));
            }
            if flag.initialized_on_entry != self.parameters.contains(&flag.place.root()) {
                return Err(invalid("flag entry initialization disagrees with ABI"));
            }
        }
        for plan in &self.plans {
            let mut destroyed = BTreeSet::new();
            let mut dead = BTreeSet::new();
            let mut loans = BTreeSet::new();
            for value in &plan.protected {
                if value.0 as usize >= self.values.len() {
                    return Err(invalid("protected value is absent"));
                }
            }
            for action in &plan.actions {
                match action {
                    CleanupAction::EndLoan(loan) => {
                        if loan.0 as usize >= self.loans.len()
                            || !loans.insert(*loan)
                            || !dead.is_empty()
                            || !destroyed.is_empty()
                        {
                            return Err(invalid(
                                "loan ending is absent, duplicated, or follows destruction",
                            ));
                        }
                    }
                    CleanupAction::Destroy { flag, destructor } => {
                        let path = self
                            .flags
                            .get(flag.0 as usize)
                            .ok_or_else(|| invalid("destroy flag is absent"))?;
                        let selected = self
                            .destruction
                            .get(destructor)
                            .ok_or_else(|| invalid("destroy target is absent"))?;
                        if selected.ty != path.ty || !destroyed.insert(*flag) || dead.contains(flag)
                        {
                            return Err(invalid("destroy type, order, or uniqueness mismatch"));
                        }
                        if plan.protected.contains(&path.place.root()) {
                            return Err(invalid("cleanup destroys a protected value"));
                        }
                    }
                    CleanupAction::StorageDead(flag) => {
                        let path = self
                            .flags
                            .get(flag.0 as usize)
                            .ok_or_else(|| invalid("storage flag is absent"))?;
                        if !dead.insert(*flag)
                            || self.destructor(&path.ty).is_some() && !destroyed.contains(flag)
                        {
                            return Err(invalid("storage ends before destruction"));
                        }
                    }
                }
            }
            if !destroyed.is_subset(&dead) {
                return Err(invalid("destroyed storage has no terminal disposition"));
            }
        }
        let check_plan = |plan: CleanupPlanId| {
            if plan.0 as usize >= self.plans.len() {
                Err(invalid("plan reference is absent"))
            } else {
                Ok(())
            }
        };
        let check_operand = |operand: &OwnershipOperand| -> Result<(), CleanupError> {
            let owner = self
                .owners
                .get(operand.value.0 as usize)
                .ok_or_else(|| invalid("operand owner is absent"))?;
            if operand.mode == ValueTransfer::Copy
                && owner.quantity != Some(crate::Quantity::UNRESTRICTED)
            {
                return Err(invalid("cleanup invented copy authority"));
            }
            Ok(())
        };
        check_plan(self.frame_cleanup)?;
        if self.label_cleanup.len() != self.labels.len() {
            return Err(invalid("label cleanup inventory is incomplete"));
        }
        if self.clause_cleanup.keys().any(|block| block.0 as usize >= self.blocks.len()) {
            return Err(invalid("clause cleanup references an absent block"));
        }
        for (label, plan) in self.labels.iter().zip(&self.label_cleanup) {
            check_plan(*plan)?;
            let plan = &self.plans[plan.0 as usize];
            let expected = self.owners.iter().rev()
                .filter(|owner| self.frame_owner(owner) && self.below_scope(owner, label.scope)
                    && owner.value != self.canonical_value(label.result))
                .map(|owner| owner.value).collect::<Vec<_>>();
            let actual = plan.actions.iter().filter_map(|action| match action {
                CleanupAction::StorageDead(flag) => Some(self.flags[flag.0 as usize].place.root()),
                _ => None,
            }).collect::<Vec<_>>();
            if actual != expected || plan.protected != vec![self.canonical_value(label.result)] {
                return Err(invalid("label cleanup is not its exact lexical owner inventory"));
            }
        }
        let frame = &self.plans[self.frame_cleanup.0 as usize];
        let expected_frame = self
            .owners
            .iter()
            .rev()
            .filter(|owner| self.frame_owner(owner))
            .map(|owner| owner.value)
            .collect::<Vec<_>>();
        let frame_owners = frame
            .actions
            .iter()
            .filter_map(|action| match action {
                CleanupAction::StorageDead(flag) => Some(self.flags[flag.0 as usize].place.root()),
                _ => None,
            })
            .collect::<Vec<_>>();
        if frame_owners != expected_frame || !frame.protected.is_empty() {
            return Err(invalid(
                "frame cancellation plan is not the complete reverse owner inventory",
            ));
        }
        for (block_index, block) in self.blocks.iter().enumerate() {
            if let CleanupControl::Transfer(ControlTransfer::FinishClause { handler, value, .. }) = &block.terminator.control {
                let id = self.clause_cleanup.get(&ControlBlockId(block_index as u32))
                    .ok_or_else(|| invalid("clause abandonment cleanup is absent"))?;
                check_plan(*id)?;
                let plan = &self.plans[id.0 as usize];
                let protected = self.canonical_value(*value);
                let expected = self.owners.iter().rev()
                    .filter(|owner| self.frame_owner(owner)
                        && self.below_scope(owner, self.handlers[handler.0 as usize].scope)
                        && owner.value != protected)
                    .map(|owner| owner.value).collect::<Vec<_>>();
                let actual = plan.actions.iter().filter_map(|action| match action {
                    CleanupAction::StorageDead(flag) => Some(self.flags[flag.0 as usize].place.root()),
                    _ => None,
                }).collect::<Vec<_>>();
                if actual != expected || plan.protected != vec![protected] {
                    return Err(invalid("clause abandonment cleanup is not its lexical owner inventory"));
                }
            } else if self.clause_cleanup.contains_key(&ControlBlockId(block_index as u32)) {
                return Err(invalid("clause cleanup is attached to a non-clause exit"));
            }
            let term = &block.terminator;
            if term.control.inputs()
                != term
                    .operands
                    .iter()
                    .map(|operand| operand.value)
                    .collect::<Vec<_>>()
            {
                return Err(invalid(
                    "terminator ownership operands disagree with control",
                ));
            }
            let edges = term.control.edges();
            if edges.len() != term.successors.len()
                || edges.iter().zip(&term.successors).any(|(edge, successor)| {
                    edge.target != successor.target
                        || edge.arguments
                            != successor
                                .arguments
                                .iter()
                                .map(|operand| operand.value)
                                .collect::<Vec<_>>()
                })
            {
                return Err(invalid("selected ownership edges disagree with control"));
            }
            for operand in term
                .operands
                .iter()
                .chain(term.successors.iter().flat_map(|edge| &edge.arguments))
            {
                check_operand(operand)?;
            }
            let host = matches!(
                block.terminator.control,
                CleanupControl::Invoke {
                    target: SpecializedCallTarget::Host { .. },
                    ..
                }
            );
            if host
                != self
                    .native_operations
                    .contains_key(&ControlBlockId(block_index as u32))
            {
                return Err(invalid("native boundary has no sealed resident operations"));
            }
            if let Some(operations) = self
                .native_operations
                .get(&ControlBlockId(block_index as u32))
            {
                let mut seen = BTreeSet::new();
                for (ty, destructor) in operations {
                    crate::specialized_mir::closed_type(ty)
                        .map_err(|error| CleanupError(error.0))?;
                    if self.destructor(ty) != *destructor
                        || !seen.insert(crate::types::canonical_type_encoding(ty))
                    {
                        return Err(invalid(
                            "native resident cleanup disagrees with the selected destruction program",
                        ));
                    }
                }
            }
            if block.terminator.flags != self.terminator_flags(&block.terminator)?
                || block.terminator.edge_flags.len() != block.terminator.successors.len()
            {
                return Err(invalid("terminator flag transitions are incomplete"));
            }
            check_plan(block.terminator.cleanup)?;
            check_plan(block.terminator.cancellation)?;
            if matches!(block.terminator.control, CleanupControl::Return(_)) || matches!(&block.terminator.control,
                CleanupControl::Invoke { contract, .. } if contract.mandatory_tail) {
                let plan = &self.plans[block.terminator.cleanup.0 as usize];
                let protected = block
                    .terminator
                    .operands
                    .iter()
                    .filter(|operand| operand.mode == ValueTransfer::Move)
                    .map(|operand| self.canonical_value(operand.value))
                    .collect::<Vec<_>>();
                let expected = expected_frame
                    .iter()
                    .filter(|owner| !protected.contains(owner))
                    .copied()
                    .collect::<Vec<_>>();
                let actual = plan
                    .actions
                    .iter()
                    .filter_map(|action| match action {
                        CleanupAction::StorageDead(flag) => {
                            Some(self.flags[flag.0 as usize].place.root())
                        }
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                if actual != expected || plan.protected != protected {
                    return Err(invalid("return bypasses its exact protected cleanup chain"));
                }
            }
            for value in block.parameters.iter().chain(
                block
                    .terminator
                    .operands
                    .iter()
                    .map(|operand| &operand.value),
            ) {
                if value.0 as usize >= self.values.len() {
                    return Err(invalid("operand is absent"));
                }
            }
            for (index, edge) in block.terminator.successors.iter().enumerate() {
                let target = self
                    .blocks
                    .get(edge.target.0 as usize)
                    .ok_or_else(|| invalid("successor is absent"))?;
                if edge.arguments.len() != target.parameters.len() {
                    return Err(invalid("successor ABI arity mismatch"));
                }
                if block.terminator.edge_flags[index]
                    != self.successor_flags(edge, &target.parameters)?
                {
                    return Err(invalid("selected edge flag transitions are incomplete"));
                }
            }
            for instruction in &block.instructions {
                if instruction.destination.0 as usize >= self.values.len()
                    || instruction.scope.0 as usize >= self.scopes.len()
                {
                    return Err(invalid("instruction identity is absent"));
                }
                if instruction.flags != self.instruction_flags(instruction)? {
                    return Err(invalid("instruction flag transitions are incomplete"));
                }
                match &instruction.operation {
                    CleanupOperation::Destroy(plan) | CleanupOperation::RunCleanup { plan, .. } => {
                        check_plan(*plan)?
                    }
                    CleanupOperation::Replace { place, cleanup, .. } => {
                        check_plan(*cleanup)?;
                        let place = self.canonical_place(place.clone());
                        let flag = self
                            .flags
                            .iter()
                            .position(|flag| flag.place == place)
                            .ok_or_else(|| invalid("replacement has no initialization flag"))?;
                        let plan = &self.plans[cleanup.0 as usize];
                        if plan.actions != self.flag_actions(DropFlagId(flag as u32))
                            || !plan.protected.is_empty()
                        {
                            return Err(invalid(
                                "replacement bypasses its old resident destruction",
                            ));
                        }
                    }
                    CleanupOperation::Borrow(id) => {
                        if self
                            .loans
                            .get(id.0 as usize)
                            .is_none_or(|loan| loan.destination != instruction.destination)
                        {
                            return Err(invalid("borrow operation has no loan"));
                        }
                    }
                    CleanupOperation::Capture { closure, captures } => {
                        let closure = self
                            .closures
                            .get(closure.0 as usize)
                            .ok_or_else(|| invalid("capture environment is absent"))?;
                        if captures.len() != closure.environment.captures.len()
                            || captures.iter().zip(&closure.environment.captures).any(
                                |((value, mode), slot)| {
                                    *mode != slot.mode
                                        || self
                                            .values
                                            .get(value.0 as usize)
                                            .is_none_or(|value| value.ty != slot.ty)
                                },
                            )
                        {
                            return Err(invalid("capture layout or transfer contract mismatch"));
                        }
                    }
                    _ => {}
                }
                match &instruction.operation {
                    CleanupOperation::Construct { fields, .. } => {
                        for field in fields {
                            check_operand(field)?;
                        }
                    }
                    CleanupOperation::Transfer { value, mode }
                    | CleanupOperation::RunCleanup {
                        result: value,
                        mode,
                        ..
                    }
                    | CleanupOperation::Replace { value, mode, .. } => {
                        check_operand(&OwnershipOperand {
                            value: *value,
                            mode: *mode,
                        })?
                    }
                    _ => {}
                }
            }
        }
        self.validate_inventories()?;
        for closure in &self.closures {
            closure.body.validate()?;
            let required = closure.environment.captures.iter().any(|capture| {
                matches!(
                    capture.mode,
                    crate::CaptureMode::Copy | crate::CaptureMode::Move
                ) && self.destructor(&capture.ty).is_some()
            });
            let expected = required.then(|| {
                crate::mir::callable_environment_destructor_definition(closure.body.definition)
            });
            if closure.destructor != expected {
                return Err(invalid("environment destruction contract mismatch"));
            }
            let expected = closure
                .environment
                .captures
                .iter()
                .enumerate()
                .rev()
                .filter_map(|(index, capture)| {
                    if !matches!(
                        capture.mode,
                        crate::CaptureMode::Copy | crate::CaptureMode::Move
                    ) {
                        return None;
                    }
                    self.destructor(&capture.ty)
                        .map(|destructor| CaptureDestruction {
                            index: index as u32,
                            ty: capture.ty.clone(),
                            destructor,
                        })
                })
                .collect::<Vec<_>>();
            if closure.cleanup != expected {
                return Err(invalid(
                    "environment cleanup is not the exact reverse owning capture plan",
                ));
            }
        }
        Ok(())
    }
}
