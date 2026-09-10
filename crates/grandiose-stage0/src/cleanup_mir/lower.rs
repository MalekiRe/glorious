use super::*;
use crate::ownership_mir::OwnerDisposition;
use crate::specialized_mir::{SpecializedControl, SpecializedMir, SpecializedOperation as S};

impl CleanupMir {
    pub(crate) fn lower(
        source: &SpecializedMir,
        signatures: &crate::ElaboratedInterface,
        destruction: &std::sync::Arc<BTreeMap<DefKey, crate::destruction::Plan>>,
    ) -> Result<Self, CleanupError> {
        source.validate().map_err(|error| CleanupError(error.0))?;
        let mut body = Self {
            definition: source.definition,
            instance: source.instance.clone(),
            safety: source.safety,
            unsafe_execution: source.unsafe_execution,
            parameters: source.parameters.clone(),
            values: source.values.clone(),
            result: source.result.clone(),
            scopes: source.scopes.clone(),
            entry: source.entry,
            labels: source.labels.clone(),
            handlers: source.handlers.clone(),
            closures: vec![],
            source_bindings: source.source_bindings.clone(),
            source_flow: source.source_flow.clone(),
            owners: source.owners.clone(),
            loans: source.loans.clone(),
            blocks: vec![],
            symbols: source.symbols.clone(),
            layouts: source.layouts.clone(),
            flags: vec![],
            aliases: source
                .blocks
                .iter()
                .flat_map(|block| &block.instructions)
                .filter_map(|instruction| match instruction.operation {
                    S::Read(value) => Some((instruction.destination, value)),
                    _ => None,
                })
                .collect(),
            plans: vec![CleanupPlan {
                actions: vec![],
                protected: vec![],
            }],
            frame_cleanup: CleanupPlanId(0),
            label_cleanup: vec![],
            clause_cleanup: BTreeMap::new(),
            destruction: destruction.clone(),
            native_operations: BTreeMap::new(),
        };
        // Views name an existing owner's storage and never acquire a flag.
        for (index, owner) in source.owners.iter().enumerate() {
            if owner.kind != OwnerKind::View && !source.symbols.contains(&owner.value) {
                body.flag(ControlPlace::Local(ControlValue(index as u32)))?;
            }
        }
        let frame = source
            .owners
            .iter()
            .rev()
            .filter(|owner| body.frame_owner(owner))
            .map(|owner| OwnerId(owner.value.0))
            .collect::<Vec<_>>();
        body.frame_cleanup = body.owner_plan(&frame, vec![])?;
        for label in &source.labels {
            let owners = source.owners.iter().rev()
                .filter(|owner| body.frame_owner(owner) && body.below_scope(owner, label.scope))
                .map(|owner| OwnerId(owner.value.0)).collect::<Vec<_>>();
            let plan = body.owner_plan(&owners, vec![label.result])?;
            body.label_cleanup.push(plan);
        }
        for closure in &source.closures {
            let child = Self::lower(&closure.body, signatures, destruction)?;
            let cleanup = closure
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
                    body.destructor(&capture.ty)
                        .map(|destructor| CaptureDestruction {
                            index: index as u32,
                            ty: capture.ty.clone(),
                            destructor,
                        })
                })
                .collect::<Vec<_>>();
            body.closures.push(CleanupClosure {
                environment: closure.environment.clone(),
                destructor: (!cleanup.is_empty()).then(|| {
                    crate::mir::callable_environment_destructor_definition(child.definition)
                }),
                cleanup,
                body: Box::new(child),
            });
        }
        for (block_index, block) in source.blocks.iter().enumerate() {
            let mut instructions = vec![];
            for instruction in &block.instructions {
                let operation = match &instruction.operation {
                    S::Compute(value) => CleanupOperation::Compute(value.clone()),
                    S::Construct { aggregate, fields } => CleanupOperation::Construct {
                        aggregate: aggregate.clone(),
                        fields: fields.clone(),
                    },
                    S::Transfer { value, mode } => CleanupOperation::Transfer {
                        value: *value,
                        mode: *mode,
                    },
                    S::Read(value) => CleanupOperation::Read(*value),
                    S::ReadReference(value) => CleanupOperation::ReadReference(*value),
                    S::PrepareInvocation(place) => CleanupOperation::PrepareInvocation(place.clone()),
                    S::ReadPlace { place, mode } => {
                        body.flag(place.clone())?;
                        CleanupOperation::ReadPlace {
                            place: place.clone(),
                            mode: *mode,
                        }
                    }
                    S::Project {
                        place,
                        base,
                        index,
                        field_count,
                        mode,
                    } => {
                        body.flag(place.clone())?;
                        CleanupOperation::Project {
                            place: place.clone(),
                            base: *base,
                            index: *index,
                            field_count: *field_count,
                            mode: *mode,
                        }
                    }
                    S::Borrow(loan) => CleanupOperation::Borrow(*loan),
                    S::MovePlace(place) => {
                        body.flag(place.clone())?;
                        CleanupOperation::MovePlace(place.clone())
                    }
                    S::Replace { place, value, mode } => {
                        let flag = body.flag(place.clone())?;
                        let actions = body.flag_actions(flag);
                        let plan = body.intern(CleanupPlan {
                            actions,
                            // Replace prepares an independent incoming value
                            // before running this resident-only plan.
                            protected: vec![],
                        });
                        CleanupOperation::Replace {
                            place: place.clone(),
                            value: *value,
                            mode: *mode,
                            cleanup: plan,
                        }
                    }
                    S::Discard(owner) => {
                        CleanupOperation::Destroy(body.owner_plan(&[*owner], vec![])?)
                    }
                    S::ExitScope {
                        scope,
                        result,
                        mode,
                        owners,
                    } => CleanupOperation::RunCleanup {
                        scope: *scope,
                        result: *result,
                        mode: *mode,
                        plan: body.owner_plan(owners, vec![instruction.destination])?,
                    },
                    S::Capture { closure, captures } => CleanupOperation::Capture {
                        closure: *closure,
                        captures: captures.clone(),
                    },
                };
                let mut lowered = CleanupInstruction {
                    scope: instruction.scope,
                    destination: instruction.destination,
                    operation,
                    flags: FlagEffects::default(),
                };
                lowered.flags = body.instruction_flags(&lowered)?;
                instructions.push(lowered);
            }
            let term = &block.terminator;
            if let SpecializedControl::Invoke {
                target: SpecializedCallTarget::Host { .. },
                arguments,
                result,
                ..
            } = &term.control
            {
                let roots = arguments
                    .iter()
                    .map(|value| body.values[value.0 as usize].ty.clone())
                    .chain(std::iter::once(body.values[result.0 as usize].ty.clone()))
                    .collect::<Vec<_>>();
                let mut residents = crate::mir::native_contract_residents(&roots, signatures)
                    .map_err(CleanupError)?;
                residents.sort_by_key(crate::types::canonical_type_encoding);
                let operations = residents
                    .into_iter()
                    .map(|ty| {
                        let destructor = body.destructor(&ty);
                        (ty, destructor)
                    })
                    .collect();
                body.native_operations
                    .insert(ControlBlockId(block_index as u32), operations);
            }
            let control = match &term.control {
                SpecializedControl::Goto(edge) => CleanupControl::Goto(edge.clone()),
                SpecializedControl::SwitchBool {
                    condition,
                    on_true,
                    on_false,
                } => CleanupControl::SwitchBool {
                    condition: *condition,
                    on_true: on_true.clone(),
                    on_false: on_false.clone(),
                },
                SpecializedControl::Invoke {
                    callee,
                    target,
                    arguments,
                    result,
                    contract,
                    continuation,
                } => CleanupControl::Invoke {
                    callee: *callee,
                    target: target.clone(),
                    arguments: arguments.clone(),
                    result: *result,
                    contract: contract.clone(),
                    continuation: *continuation,
                },
                SpecializedControl::Return(value) => CleanupControl::Return(*value),
                SpecializedControl::Unreachable => CleanupControl::Unreachable,
                SpecializedControl::Transfer(transfer) => {
                    CleanupControl::Transfer(transfer.clone())
                }
            };
            if let CleanupControl::Transfer(ControlTransfer::FinishClause { handler, value, .. }) = &control {
                let scope = body.handlers[handler.0 as usize].scope;
                let owners = body.owners.iter().rev()
                    .filter(|owner| body.frame_owner(owner) && body.below_scope(owner, scope))
                    .map(|owner| OwnerId(owner.value.0)).collect::<Vec<_>>();
                let plan = body.owner_plan(&owners, vec![*value])?;
                body.clause_cleanup.insert(ControlBlockId(block_index as u32), plan);
            }
            let protected = term
                .operands
                .iter()
                .filter(|operand| operand.mode == ValueTransfer::Move)
                .map(|operand| operand.value)
                .collect::<Vec<_>>();
            let mut exiting = term
                .dispositions
                .iter()
                .rev()
                .filter(|(_, disposition)| *disposition == OwnerDisposition::Abandon)
                .map(|(owner, _)| *owner)
                .collect::<Vec<_>>();
            if matches!(control, CleanupControl::Return(_)) || matches!(&control,
                CleanupControl::Invoke { contract, .. } if contract.mandatory_tail) {
                // Guarded residual owners include partially moved aggregates.
                // Captures belong to the environment, not this invocation.
                exiting = frame.clone();
            }
            let cleanup = body.owner_plan(&exiting, protected.clone())?;
            let suspended = term
                .dispositions
                .iter()
                .rev()
                .filter(|(_, disposition)| *disposition == OwnerDisposition::Suspend)
                .map(|(owner, _)| *owner)
                .collect::<Vec<_>>();
            let cancellation = body.owner_plan(&suspended, protected)?;
            let mut terminator = CleanupTerminator {
                control,
                operands: term.operands.clone(),
                successors: term.successors.clone(),
                cleanup,
                cancellation,
                flags: FlagEffects::default(),
                edge_flags: vec![],
            };
            terminator.flags = body.terminator_flags(&terminator)?;
            terminator.edge_flags = terminator
                .successors
                .iter()
                .map(|edge| {
                    body.successor_flags(edge, &source.blocks[edge.target.0 as usize].parameters)
                })
                .collect::<Result<_, _>>()?;
            body.blocks.push(CleanupBlock {
                parameters: block.parameters.clone(),
                instructions,
                terminator,
            });
        }
        body.validate()?;
        Ok(body)
    }

    pub(super) fn frame_owner(&self, owner: &Owner) -> bool {
        !matches!(
            owner.kind,
            OwnerKind::View | OwnerKind::Continuation | OwnerKind::Capture(_)
        ) && !self.symbols.contains(&owner.value)
    }
    pub(super) fn destructor(&self, ty: &Type) -> Option<DefKey> {
        self.destruction
            .iter()
            .find_map(|(key, plan)| (&plan.ty == ty).then_some(*key))
    }
    pub(super) fn place_type(&self, place: &ControlPlace) -> Result<Type, CleanupError> {
        match place {
            ControlPlace::Local(value) | ControlPlace::Temporary(value) => self
                .values
                .get(value.0 as usize)
                .map(|value| value.ty.clone())
                .ok_or_else(|| CleanupError("cleanup place is out of bounds".into())),
            ControlPlace::Deref { reference, ty } => {
                let root = self
                    .values
                    .get(reference.0 as usize)
                    .ok_or_else(|| CleanupError("cleanup reference is absent".into()))?;
                if !matches!(&root.ty, Type::Reference { referent, .. } if referent.as_ref() == ty)
                {
                    return Err(CleanupError(
                        "cleanup dereference type disagrees with its reference".into(),
                    ));
                }
                Ok(ty.clone())
            }
            ControlPlace::Field {
                base,
                index,
                field_count,
                ty,
            } => {
                let base = self.place_type(base)?;
                let fields = match &base {
                    Type::Tuple(fields) => Some(fields),
                    Type::Nominal { .. } => self
                        .layouts
                        .iter()
                        .find(|layout| layout.ty == base && !layout.is_enum)
                        .and_then(|layout| layout.variants.first()),
                    _ => None,
                };
                if index >= field_count
                    || fields.is_some_and(|fields| {
                        fields.len() != *field_count as usize
                            || fields.get(*index as usize) != Some(ty)
                    })
                {
                    return Err(CleanupError(
                        "cleanup projection disagrees with its concrete layout".into(),
                    ));
                }
                Ok(ty.clone())
            }
        }
    }
    pub(super) fn canonical_value(&self, mut value: ControlValue) -> ControlValue {
        for _ in 0..self.aliases.len() {
            let Some(source) = self.aliases.get(&value) else {
                break;
            };
            value = *source;
        }
        value
    }
    pub(super) fn canonical_place(&self, place: ControlPlace) -> ControlPlace {
        match place {
            ControlPlace::Local(value) | ControlPlace::Temporary(value) => {
                ControlPlace::Local(self.canonical_value(value))
            }
            ControlPlace::Deref { reference, ty } => ControlPlace::Deref {
                reference: self.canonical_value(reference),
                ty,
            },
            ControlPlace::Field {
                base,
                index,
                field_count,
                ty,
            } => ControlPlace::Field {
                base: Box::new(self.canonical_place(*base)),
                index,
                field_count,
                ty,
            },
        }
    }
    fn flag(&mut self, place: ControlPlace) -> Result<DropFlagId, CleanupError> {
        let place = self.canonical_place(place);
        if let Some(index) = self.flags.iter().position(|flag| flag.place == place) {
            return Ok(DropFlagId(index as u32));
        }
        let ty = self.place_type(&place)?;
        let initialized_on_entry = self.parameters.contains(&place.root());
        let id = DropFlagId(self.flags.len() as u32);
        self.flags.push(DropFlag {
            place,
            ty,
            initialized_on_entry,
        });
        Ok(id)
    }
    pub(super) fn flag_actions(&self, flag: DropFlagId) -> Vec<CleanupAction> {
        let mut actions = vec![];
        if let Some(destructor) = self.destructor(&self.flags[flag.0 as usize].ty) {
            actions.push(CleanupAction::Destroy { flag, destructor });
        }
        actions.push(CleanupAction::StorageDead(flag));
        actions
    }
    fn owner_plan(
        &mut self,
        owners: &[OwnerId],
        protected: Vec<ControlValue>,
    ) -> Result<CleanupPlanId, CleanupError> {
        let protected = protected
            .into_iter()
            .map(|value| self.canonical_value(value))
            .collect::<Vec<_>>();
        let mut actions = vec![];
        let mut seen = BTreeSet::new();
        // Loan ends precede destruction, not merely the storage-dead action
        // of the reference value which happened to carry that loan.
        for loan in self.loans.iter().rev() {
            if owners.iter().any(|owner| owner.0 == loan.destination.0)
                && !protected.contains(&loan.destination)
            {
                actions.push(CleanupAction::EndLoan(loan.id));
            }
        }
        for owner in owners {
            let owner = self
                .owners
                .get(owner.0 as usize)
                .ok_or_else(|| CleanupError("cleanup owner is out of bounds".into()))?;
            if !self.frame_owner(owner)
                || protected.contains(&owner.value)
                || !seen.insert(owner.value)
            {
                continue;
            }
            let flag = self.flag(ControlPlace::Local(owner.value))?;
            actions.extend(self.flag_actions(flag));
        }
        Ok(self.intern(CleanupPlan { actions, protected }))
    }
    fn intern(&mut self, plan: CleanupPlan) -> CleanupPlanId {
        if let Some(index) = self.plans.iter().position(|existing| *existing == plan) {
            return CleanupPlanId(index as u32);
        }
        let id = CleanupPlanId(self.plans.len() as u32);
        self.plans.push(plan);
        id
    }
}
