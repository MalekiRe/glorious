//! Structural proof over the concrete Specialized MIR graph. No previous-stage body is
//! reconstructed, and no source expression is evaluated to recover operands.
use super::*;

fn invalid(message: &str) -> SpecializedError {
    SpecializedError(message.into())
}

impl SpecializedMir {
    fn graph_type(&self, value: ControlValue) -> Result<&Type, SpecializedError> {
        self.values
            .get(value.0 as usize)
            .map(|value| &value.ty)
            .ok_or_else(|| invalid("unknown graph value"))
    }

    fn graph_edge(&self, edge: &ControlEdge) -> Result<(), SpecializedError> {
        let target = self
            .blocks
            .get(edge.target.0 as usize)
            .ok_or_else(|| invalid("unknown graph target"))?;
        if target.parameters.len() != edge.arguments.len() {
            return Err(invalid("edge argument arity disagrees with destination"));
        }
        for (argument, parameter) in edge.arguments.iter().zip(&target.parameters) {
            if self.graph_type(*argument)? != self.graph_type(*parameter)? {
                return Err(invalid("edge argument type disagrees with destination"));
            }
        }
        Ok(())
    }

    fn graph_operation(
        &self,
        instruction: &SpecializedInstruction,
    ) -> Result<(), SpecializedError> {
        let ty = self.graph_type(instruction.destination)?;
        for value in instruction.operation.inputs(&self.loans) {
            self.graph_type(value)?;
        }
        let valid = match &instruction.operation {
            SpecializedOperation::Compute(computation) => match computation {
                SpecializedComputation::Unit => ty == &Type::Unit,
                SpecializedComputation::Literal(_) => {
                    !matches!(ty, Type::Never | Type::Infer(_) | Type::Error)
                }
                SpecializedComputation::Function { .. }
                | SpecializedComputation::HostFunction { .. } => {
                    matches!(ty, Type::Callable { .. })
                        || self.symbols.contains(&instruction.destination)
                }
                SpecializedComputation::Constant { .. } => {
                    !matches!(ty, Type::Error | Type::Infer(_))
                }
                SpecializedComputation::Intrinsic { arguments, .. } => !arguments.is_empty(),
                SpecializedComputation::Test { .. } => ty == &Type::Scalar(crate::ScalarType::Bool),
                SpecializedComputation::Label(id) => {
                    let label = self
                        .labels
                        .get(id.0 as usize)
                        .ok_or_else(|| invalid("unknown label value"))?;
                    *ty == crate::types::label::new(label.brand, self.graph_type(label.result)?.clone())
                }
                SpecializedComputation::Resumption { handler, clause } => {
                    let clause = self
                        .handlers
                        .get(handler.0 as usize)
                        .and_then(|handler| handler.clauses.get(*clause as usize))
                        .ok_or_else(|| invalid("unknown resumption value"))?;
                    clause.contract.as_ref().is_some_and(|contract| matches!(ty, Type::Callable { parameters, result, invocation, .. }
                        if parameters == &vec![contract.parameter.clone()] && **result == contract.result && *invocation == contract.invocation))
                }
            },
            SpecializedOperation::Construct { aggregate, fields } => match aggregate {
                OwnershipAggregate::Tuple if fields.is_empty() && ty == &Type::Unit => true,
                OwnershipAggregate::Tuple => {
                    matches!(ty, Type::Tuple(types) if types.len() == fields.len()
                    && types.iter().zip(fields).all(|(ty, field)| self.graph_type(field.value)
                        .is_ok_and(|value| crate::types::regions::accepts_body_storage(ty, value))))
                }
                OwnershipAggregate::Array => ty.array_accepts_count(fields.len()) && ty.array_element().is_some_and(|element|
                    fields.iter().all(|field| self.graph_type(field.value)
                        .is_ok_and(|value| crate::types::regions::accepts_body_storage(element, value)))),
                OwnershipAggregate::Record(definition)
                | OwnershipAggregate::Enum { definition, .. } => {
                    matches!(ty, Type::Nominal { definition: actual, .. } if actual == definition)
                }
            },
            SpecializedOperation::Transfer { value, .. } | SpecializedOperation::Read(value) => {
                call_type_matches(ty, self.graph_type(*value)?)
            }
            SpecializedOperation::ReadReference(value) => {
                matches!(self.graph_type(*value)?, Type::Reference { referent, .. } if referent.as_ref() == ty)
            }
            SpecializedOperation::ExitScope { scope, result, .. } => {
                self.scopes.get(scope.0 as usize).is_some() && self.graph_type(*result)? == ty
            }
            SpecializedOperation::Discard(_) | SpecializedOperation::Replace { .. } => {
                ty == &Type::Unit
            }
            // Place layout, transfer permission and sealed capture contracts
            // are checked by the ownership validator, not inferred here.
            SpecializedOperation::ReadPlace { place, .. }
            | SpecializedOperation::PrepareInvocation(place)
            | SpecializedOperation::MovePlace(place)
            | SpecializedOperation::Project { place, .. } => self.checked_place_type(place)? == ty,
            SpecializedOperation::Borrow(_) | SpecializedOperation::Capture { .. } => true,
        };
        if !valid {
            return Err(invalid(
                "ownership operation result type disagrees with its contract",
            ));
        }
        Ok(())
    }

    fn graph_terminator(&self, terminator: &SpecializedControl) -> Result<(), SpecializedError> {
        for edge in terminator.edges() {
            self.graph_edge(&edge)?;
        }
        for value in terminator.inputs() {
            self.graph_type(value)?;
        }
        match terminator {
            SpecializedControl::SwitchBool { condition, .. } => {
                if self.graph_type(*condition)? != &Type::Scalar(crate::ScalarType::Bool) {
                    return Err(invalid(
                        "ownership branch condition is not a primitive predicate",
                    ));
                }
            }
            SpecializedControl::Invoke {
                callee,
                arguments,
                result,
                continuation,
                contract,
                ..
            } => {
                let mut ty = self.graph_type(*callee)?;
                while let Type::Reference { referent, .. } = ty {
                    ty = referent;
                }
                let label_callable = crate::types::label::callable(ty);
                let ty = label_callable.as_ref().unwrap_or(ty);
                self.graph_type(*result)?;
                if let Type::Callable {
                    parameters,
                    result: result_ty,
                    ..
                } = ty
                {
                    if parameters.len() != arguments.len()
                        || !parameters.iter().zip(arguments).all(|(ty, value)| {
                            self.graph_type(*value)
                                .is_ok_and(|actual| call_type_matches(ty, actual))
                        })
                        || !call_type_matches(result_ty, self.graph_type(*result)?)
                        || continuation.is_none() != (**result_ty == Type::Never || contract.mandatory_tail)
                    {
                        return Err(invalid(
                            "ownership invocation disagrees with callable contract",
                        ));
                    }
                } else if !self.symbols.contains(callee) {
                    return Err(invalid(&format!("specialized invocation lacks a callable contract in {:?} for value {}: {ty:?}", self.definition, callee.0)));
                }
                if let Some(target) = continuation
                    && self.blocks[target.0 as usize].parameters != vec![*result]
                {
                    return Err(invalid(
                        "invocation result is not its continuation parameter",
                    ));
                }
            }
            SpecializedControl::Transfer(transfer) => self.graph_transfer(transfer)?,
            _ => {}
        }
        Ok(())
    }

    fn graph_transfer(&self, transfer: &ControlTransfer) -> Result<(), SpecializedError> {
        let handler = |id: ControlHandlerId| {
            self.handlers
                .get(id.0 as usize)
                .ok_or_else(|| invalid("unknown handler transfer"))
        };
        let clause = |id: ControlHandlerId, index: u32| {
            handler(id)?
                .clauses
                .get(index as usize)
                .ok_or_else(|| invalid("unknown clause transfer"))
        };
        let valid = match transfer {
            ControlTransfer::Leave { label, edge } => {
                let label = self
                    .labels
                    .get(label.0 as usize)
                    .ok_or_else(|| invalid("unknown label transfer"))?;
                edge.target == label.target
            }
            ControlTransfer::EnterHandler {
                handler: id,
                computation,
                clauses,
            } => {
                let owner = handler(*id)?;
                clauses.len() == owner.clauses.len()
                    && clauses.iter().zip(&owner.clauses).all(|(edge, clause)| {
                        edge.target == clause.entry && edge.arguments == clause.payloads
                    })
                    && !clauses.iter().any(|edge| edge.target == computation.target)
            }
            ControlTransfer::CompleteHandler {
                handler: id,
                value,
                edge,
            } => {
                handler(*id)?;
                // Normal completion may transform the computation's type
                // before producing the delimiter's result.
                edge.arguments == vec![*value]
            }
            ControlTransfer::FinishClause {
                handler: id,
                clause: index,
                value,
                edge,
            } => {
                clause(*id, *index)?;
                edge.target == handler(*id)?.target
                    && self.graph_type(*value)? == self.graph_type(handler(*id)?.result)?
            }
            ControlTransfer::TailResume {
                handler: id,
                clause: index,
                value,
            } => clause(*id, *index)?
                .contract
                .as_ref()
                .is_some_and(|contract| self.graph_type(*value).ok() == Some(&contract.parameter)),
            ControlTransfer::Forward {
                handler: id,
                clause: index,
            } => {
                clause(*id, *index)?;
                true
            }
            ControlTransfer::Perform {
                arguments,
                payload_types,
                result,
                continuation,
                ..
            } => {
                let result_ty = self.graph_type(*result)?;
                arguments.len() == payload_types.len()
                    && arguments.iter().zip(payload_types).all(|(argument, ty)| {
                        self.graph_type(*argument)
                            .is_ok_and(|actual| call_type_matches(ty, actual))
                    })
                    && continuation.is_none() == (result_ty == &Type::Never)
                    && continuation.is_none_or(|target| {
                        self.blocks[target.0 as usize].parameters == vec![*result]
                    })
            }
        };
        if !valid {
            return Err(invalid(
                "dynamic ownership edge disagrees with its delimiter contract",
            ));
        }
        Ok(())
    }

    pub(super) fn validate_graph(&self) -> Result<(), SpecializedError> {
        for scope in &self.scopes {
            for value in &scope.bindings {
                self.graph_type(*value)?;
            }
        }
        for value in self.source_bindings.values() {
            self.graph_type(*value)?;
        }
        for label in &self.labels {
            if self.scopes.get(label.scope.0 as usize).is_none()
                || self
                    .blocks
                    .get(label.target.0 as usize)
                    .is_none_or(|block| block.parameters != vec![label.result])
            {
                return Err(invalid("invalid label delimiter"));
            }
            self.graph_type(label.result)?;
        }
        for handler in &self.handlers {
            if self.scopes.get(handler.scope.0 as usize).is_none()
                || self
                    .blocks
                    .get(handler.target.0 as usize)
                    .is_none_or(|block| block.parameters != vec![handler.result])
            {
                return Err(invalid("invalid handler delimiter"));
            }
            for clause in &handler.clauses {
                if self
                    .blocks
                    .get(clause.entry.0 as usize)
                    .is_none_or(|block| block.parameters != clause.payloads)
                {
                    return Err(invalid("invalid handler payload ABI"));
                }
                for value in &clause.payloads {
                    self.graph_type(*value)?;
                }
                if let Some(value) = clause.token {
                    self.graph_type(value)?;
                }
                match (&clause.resumption, &clause.contract) {
                    (crate::CoreHandlerResumption::Terminal, None) => {}
                    (
                        crate::CoreHandlerResumption::Tail { quantity }
                        | crate::CoreHandlerResumption::Explicit { quantity, .. }
                        | crate::CoreHandlerResumption::Discard { quantity },
                        Some(contract),
                    ) => {
                        if *quantity != contract.invocation
                            || (matches!(
                                clause.resumption,
                                crate::CoreHandlerResumption::Discard { .. }
                            ) && quantity.requires_positive_use())
                        {
                            return Err(invalid(
                                "handler resumption disagrees with its frozen ownership contract",
                            ));
                        }
                    }
                    _ => return Err(invalid("handler lost its terminal or resumptive contract")),
                }
            }
        }
        let mut definitions = BTreeSet::new();
        for block in &self.blocks {
            for value in block.parameters.iter().copied().chain(
                block
                    .instructions
                    .iter()
                    .map(|instruction| instruction.destination),
            ) {
                self.graph_type(value)?;
                if !definitions.insert(value) {
                    return Err(invalid("duplicate ownership value definition"));
                }
            }
            for instruction in &block.instructions {
                self.graph_operation(instruction)?;
            }
            self.graph_terminator(&block.terminator.control)?;
        }
        if self.blocks[self.entry.0 as usize].parameters != self.parameters {
            return Err(invalid("ownership entry ABI disagrees"));
        }
        let mut reachable = BTreeSet::new();
        let mut pending = vec![self.entry];
        while let Some(id) = pending.pop() {
            if reachable.insert(id) {
                pending.extend(
                    self.blocks[id.0 as usize]
                        .terminator
                        .control
                        .edges()
                        .iter()
                        .map(|edge| edge.target),
                );
            }
        }
        let mut incoming = vec![definitions; self.blocks.len()];
        incoming[self.entry.0 as usize].clear();
        loop {
            let mut changed = false;
            for id in &reachable {
                let block = &self.blocks[id.0 as usize];
                let mut available = incoming[id.0 as usize].clone();
                available.extend(&block.parameters);
                available.extend(
                    block
                        .instructions
                        .iter()
                        .map(|instruction| instruction.destination),
                );
                for edge in block.terminator.control.edges() {
                    let next = incoming[edge.target.0 as usize]
                        .intersection(&available)
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
        for id in reachable {
            let block = &self.blocks[id.0 as usize];
            let mut available = incoming[id.0 as usize].clone();
            available.extend(&block.parameters);
            for instruction in &block.instructions {
                if instruction
                    .operation
                    .inputs(&self.loans)
                    .iter()
                    .any(|value| !available.contains(value))
                {
                    return Err(invalid("ownership instruction uses an unavailable value"));
                }
                available.insert(instruction.destination);
            }
            if block
                .terminator
                .control
                .inputs()
                .iter()
                .any(|value| !available.contains(value))
            {
                return Err(invalid("ownership terminator uses an unavailable value"));
            }
        }
        Ok(())
    }
}
