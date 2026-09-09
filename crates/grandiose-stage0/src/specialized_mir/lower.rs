use super::*;
use crate::ownership_mir::{
    OwnershipComputation as OCompute, OwnershipMir, OwnershipOperation as OOperation,
};
use crate::{ElaboratedHeader, ElaboratedInterface, PrimitiveRole, TraitSolver};

struct Substitution<'a> {
    arguments: &'a [GenericArgument],
    solver: TraitSolver,
}
impl Substitution<'_> {
    fn ty(&mut self, ty: &Type) -> Result<Type, SpecializedError> {
        let ty = crate::service::specialize_type(ty, self.arguments);
        let ty = self
            .solver
            .normalize_type(ty)
            .map_err(|error| SpecializedError(format!("type specialization: {error:?}")))?;
        crate::service::normalize_materialized_type(&ty, &mut self.solver)
            .map(|ty| regions::body_type(&ty))
            .map_err(SpecializedError)
    }
    fn argument(
        &mut self,
        argument: &GenericArgument,
    ) -> Result<GenericArgument, SpecializedError> {
        let argument = crate::service::specialize_generic_argument(argument, self.arguments);
        let argument = self
            .solver
            .normalize_generic_argument(argument)
            .map_err(|error| SpecializedError(format!("argument specialization: {error:?}")))?;
        crate::service::normalize_materialized_generic_argument(&argument, &mut self.solver)
            .map_err(SpecializedError)
    }
    fn arguments(
        &mut self,
        arguments: &[GenericArgument],
    ) -> Result<Vec<GenericArgument>, SpecializedError> {
        arguments
            .iter()
            .map(|argument| self.argument(argument))
            .collect()
    }
    fn row(&mut self, row: &crate::EffectRow) -> Result<crate::EffectRow, SpecializedError> {
        crate::service::normalize_materialized_effect_row(
            &crate::service::specialize_effect_row(row, self.arguments),
            &mut self.solver,
            0,
        )
        .map(|row| regions::body_row(&row))
        .map_err(SpecializedError)
    }
    fn place(&mut self, place: &ControlPlace) -> Result<ControlPlace, SpecializedError> {
        Ok(match place {
            ControlPlace::Local(_) | ControlPlace::Temporary(_) => place.clone(),
            ControlPlace::Field {
                base,
                index,
                field_count,
                ty,
            } => ControlPlace::Field {
                base: Box::new(self.place(base)?),
                index: *index,
                field_count: *field_count,
                ty: self.ty(ty)?,
            },
            ControlPlace::Deref { reference, ty } => ControlPlace::Deref {
                reference: *reference,
                ty: self.ty(ty)?,
            },
        })
    }
    fn pattern(
        &mut self,
        pattern: &crate::CorePattern,
    ) -> Result<crate::CorePattern, SpecializedError> {
        use crate::CorePattern as P;
        Ok(match pattern {
            P::Tuple(fields) => P::Tuple(
                fields
                    .iter()
                    .map(|field| self.pattern(field))
                    .collect::<Result<_, _>>()?,
            ),
            P::Array { element, elements, rest } => P::Array {
                rest: *rest,
                element: self.ty(element)?,
                elements: elements
                    .iter()
                    .map(|field| self.pattern(field))
                    .collect::<Result<_, _>>()?,
            },
            P::Record {
                definition,
                field_types,
                field_count,
                fields,
            }
            | P::Enum {
                definition,
                field_types,
                field_count,
                fields,
                ..
            } => {
                let field_types = field_types
                    .iter()
                    .map(|ty| self.ty(ty))
                    .collect::<Result<_, _>>()?;
                let fields = fields
                    .iter()
                    .map(|field| {
                        Ok(crate::CorePatternField {
                            index: field.index,
                            ty: self.ty(&field.ty)?,
                            pattern: self.pattern(&field.pattern)?,
                        })
                    })
                    .collect::<Result<_, SpecializedError>>()?;
                match pattern {
                    P::Enum { variant, .. } => P::Enum {
                        definition: *definition,
                        variant: *variant,
                        field_types,
                        field_count: *field_count,
                        fields,
                    },
                    _ => P::Record {
                        definition: *definition,
                        field_types,
                        field_count: *field_count,
                        fields,
                    },
                }
            }
            _ => pattern.clone(),
        })
    }
    fn transfer(
        &mut self,
        transfer: &ControlTransfer,
    ) -> Result<ControlTransfer, SpecializedError> {
        let mut transfer = transfer.clone();
        if let ControlTransfer::Perform {
            effect,
            payload_types,
            ..
        } = &mut transfer
        {
            effect.arguments = self.arguments(&effect.arguments)?;
            *payload_types = payload_types
                .iter()
                .map(|ty| self.ty(ty))
                .collect::<Result<_, _>>()?;
        }
        Ok(transfer)
    }
}

pub(super) fn executable(key: &InstanceKey) -> DefKey {
    if key.arguments().is_empty() {
        key.callable
    } else {
        DefKey(key.fingerprint())
    }
}

/// Discharge addressability at the first boundary with closed generic types.
/// Frozen ownership loans supply the obligations; do not reconstruct borrows
/// from source or Core. Independent concrete validation checks the same rule.
pub(super) fn check_addressability(
    ownership: &OwnershipMir,
    instance: &InstanceKey,
    signatures: &ElaboratedInterface,
) -> Result<(), SpecializedDiscoveryError> {
    ownership.validate().map_err(|error| SpecializedError(error.0))?;
    let arguments = crate::service::materialization_body_arguments(instance, signatures)
        .map_err(SpecializedError)?;
    let mut substitution = Substitution { arguments: &arguments, solver: TraitSolver::new(signatures) };
    fn check(body: &OwnershipMir, substitution: &mut Substitution<'_>) -> Result<(), SpecializedDiscoveryError> {
        for loan in &body.loans {
            let Type::Reference { referent, .. } = &body.values[loan.destination.0 as usize].ty else {
                return Err(SpecializedError("ownership loan lacks its reference type".into()).into());
            };
            let ty = substitution.ty(referent)?;
            if crate::types::label::payload(&ty).is_some() {
                return Err(SpecializedDiscoveryError::NonAddressableLabel { definition: body.definition, ty });
            }
        }
        for closure in &body.closures { check(&closure.body, substitution)?; }
        Ok(())
    }
    check(ownership, &mut substitution)
}

pub(super) fn declaration_key(
    definition: DefKey,
    arguments: Vec<GenericArgument>,
    signatures: &ElaboratedInterface,
) -> Result<InstanceKey, SpecializedError> {
    let kinds = match signatures.definitions.get(&definition) {
        Some(ElaboratedHeader::Callable(signature))
        | Some(ElaboratedHeader::ValueAlias { signature, .. }) => signature.generic_kinds.clone(),
        Some(ElaboratedHeader::ValueInitializer { generic_kinds, .. }) => generic_kinds.clone(),
        _ if arguments.is_empty() => vec![],
        _ => {
            return Err(SpecializedError(format!(
                "specialized callee has no generic declaration: {definition:?}"
            )));
        }
    };
    InstanceKey::new(definition, &kinds, arguments).map_err(|error| {
        SpecializedError(format!(
            "callee instance {definition:?} is not closed: {error:?}"
        ))
    })
}

impl SpecializedMir {
    pub fn lower(
        ownership: &OwnershipMir,
        result: &Type,
        instance: InstanceKey,
        signatures: &ElaboratedInterface,
        primitives: Option<&BTreeMap<DefKey, PrimitiveRole>>,
    ) -> Result<Self, SpecializedError> {
        ownership
            .validate()
            .map_err(|error| SpecializedError(format!("invalid ownership input: {}", error.0)))?;
        if ownership.definition != instance.callable {
            return Err(SpecializedError(
                "instance does not name its ownership template".into(),
            ));
        }
        let arguments = crate::service::materialization_body_arguments(&instance, signatures)
            .map_err(SpecializedError)?;
        Self::lower_body(
            ownership,
            result,
            &instance,
            executable(&instance),
            &arguments,
            signatures,
            primitives,
        )
    }

    fn lower_body(
        ownership: &OwnershipMir,
        result: &Type,
        instance: &InstanceKey,
        definition: DefKey,
        arguments: &[GenericArgument],
        signatures: &ElaboratedInterface,
        primitives: Option<&BTreeMap<DefKey, PrimitiveRole>>,
    ) -> Result<Self, SpecializedError> {
        let mut substitution = Substitution {
            arguments,
            solver: TraitSolver::new(signatures),
        };
        let mut values = ownership.values.clone();
        for value in &mut values {
            value.ty = substitution.ty(&value.ty)?;
        }
        let result = substitution.ty(result)?;
        let mut loans = ownership.loans.clone();
        for loan in &mut loans {
            loan.place = substitution.place(&loan.place)?;
        }
        let mut handlers = ownership.handlers.clone();
        for handler in &mut handlers {
            for clause in &mut handler.clauses {
                clause.effect.arguments = substitution.arguments(&clause.effect.arguments)?;
                clause.patterns = clause
                    .patterns
                    .iter()
                    .map(|pattern| substitution.pattern(pattern))
                    .collect::<Result<_, _>>()?;
                if let Some(contract) = &mut clause.contract {
                    contract.parameter = substitution.ty(&contract.parameter)?;
                    contract.result = substitution.ty(&contract.result)?;
                    contract.effects = substitution.row(&contract.effects)?;
                }
            }
        }
        let mut dependencies = BTreeMap::new();
        let mut blocks = Vec::with_capacity(ownership.blocks.len());
        for block in &ownership.blocks {
            let mut instructions = vec![];
            for instruction in &block.instructions {
                let operation = match &instruction.operation {
                    OOperation::Compute(computation) => {
                        SpecializedOperation::Compute(match computation {
                            OCompute::Literal(text) => {
                                SpecializedComputation::Literal(text.clone())
                            }
                            OCompute::ConstValue(argument) => {
                                let argument = substitution.argument(argument)?;
                                let (literal, expected) = match argument {
                                    GenericArgument::ConstInteger(value) => (value.to_string(), Type::Scalar(value.scalar())),
                                    _ => return Err(SpecializedError("const value is not a closed supported integer".into())),
                                };
                                if values[instruction.destination.0 as usize].ty != expected {
                                    return Err(SpecializedError("const value has a different scalar kind than its result".into()));
                                }
                                SpecializedComputation::Literal(literal)
                            }
                            OCompute::Unit => SpecializedComputation::Unit,
                            OCompute::Function {
                                definition,
                                arguments,
                            }
                            | OCompute::HostFunction {
                                definition,
                                arguments,
                                ..
                            } => {
                                let arguments = substitution.arguments(arguments)?;
                                let key =
                                    declaration_key(*definition, arguments.clone(), signatures)?;
                                match computation {
                                    OCompute::HostFunction { import, .. } => {
                                        SpecializedComputation::HostFunction {
                                            definition: *definition,
                                            arguments,
                                            import: import.clone(),
                                        }
                                    }
                                    _ if primitives.is_some_and(|primitives| {
                                        primitives.contains_key(definition)
                                    }) =>
                                    {
                                        SpecializedComputation::Function {
                                            definition: *definition,
                                            arguments,
                                        }
                                    }
                                    _ => {
                                        let definition = executable(&key);
                                        dependencies.insert(definition, key);
                                        SpecializedComputation::Function {
                                            definition,
                                            arguments: vec![],
                                        }
                                    }
                                }
                            }
                            OCompute::TraitMethod {
                                evidence,
                                method,
                                trait_arguments,
                                method_arguments,
                                deferred,
                            } => {
                                let mut evidence = *evidence;
                                let mut method = *method;
                                let trait_arguments = substitution.arguments(trait_arguments)?;
                                let method_arguments = substitution.arguments(method_arguments)?;
                                if let Some(deferred) = deferred {
                                    let mut relation = deferred.relation.clone();
                                    relation.arguments =
                                        substitution.arguments(&relation.arguments)?;
                                    let subject = substitution.ty(&deferred.subject)?;
                                    match substitution.solver.select_method(
                                        crate::TraitGoal { relation, subject },
                                        &deferred.name,
                                        &method_arguments,
                                    ) {
                                        crate::TraitMethodAnswer::Selected {
                                            evidence: selected_evidence,
                                            method: selected_method,
                                            ..
                                        } => {
                                            evidence = selected_evidence;
                                            method = selected_method;
                                        }
                                        answer => {
                                            return Err(SpecializedError(format!(
                                                "closed trait method could not be selected: {answer:?}"
                                            )));
                                        }
                                    }
                                }
                                let receiver = crate::callable_declarations::receiver_candidate(
                                    &values[instruction.destination.0 as usize].ty).cloned();
                                let receiver = crate::service::trait_method_executable_receiver(
                                    evidence,
                                    method,
                                    receiver.as_ref(),
                                    signatures,
                                )
                                .map_err(SpecializedError)?;
                                let key = crate::service::trait_method_instance_key(
                                    evidence,
                                    method,
                                    &trait_arguments,
                                    &method_arguments,
                                    receiver.as_ref(),
                                )
                                .map_err(|error| {
                                    SpecializedError(format!(
                                        "selected trait instance is not closed: {error:?}"
                                    ))
                                })?;
                                let definition = executable(&key);
                                dependencies.insert(definition, key);
                                SpecializedComputation::Function {
                                    definition,
                                    arguments: vec![],
                                }
                            }
                            OCompute::Constant {
                                definition,
                                arguments,
                            } => {
                                let key = declaration_key(
                                    *definition,
                                    substitution.arguments(arguments)?,
                                    signatures,
                                )?;
                                let definition = executable(&key);
                                dependencies.insert(definition, key);
                                SpecializedComputation::Constant { definition }
                            }
                            OCompute::Intrinsic {
                                operator,
                                arguments,
                            } => SpecializedComputation::Intrinsic {
                                operator: operator.clone(),
                                arguments: arguments.clone(),
                            },
                            OCompute::Test { subject, pattern } => SpecializedComputation::Test {
                                subject: *subject,
                                pattern: substitution.pattern(pattern)?,
                            },
                            OCompute::Label(label) => SpecializedComputation::Label(*label),
                            OCompute::Resumption { handler, clause } => {
                                SpecializedComputation::Resumption {
                                    handler: *handler,
                                    clause: *clause,
                                }
                            }
                        })
                    }
                    OOperation::Construct { aggregate, fields } => {
                        SpecializedOperation::Construct {
                            aggregate: aggregate.clone(),
                            fields: fields.clone(),
                        }
                    }
                    OOperation::Transfer { value, mode } => SpecializedOperation::Transfer {
                        value: *value,
                        mode: *mode,
                    },
                    OOperation::Read(value) => SpecializedOperation::Read(*value),
                    OOperation::ReadReference(value) => SpecializedOperation::ReadReference(*value),
                    OOperation::ReadPlace { place, mode } => SpecializedOperation::ReadPlace {
                        place: substitution.place(place)?,
                        mode: *mode,
                    },
                    OOperation::Project {
                        place,
                        base,
                        index,
                        field_count,
                        mode,
                    } => SpecializedOperation::Project {
                        place: substitution.place(place)?,
                        base: *base,
                        index: *index,
                        field_count: *field_count,
                        mode: *mode,
                    },
                    OOperation::Borrow(loan) => SpecializedOperation::Borrow(*loan),
                    OOperation::MovePlace(place) => {
                        SpecializedOperation::MovePlace(substitution.place(place)?)
                    }
                    OOperation::Replace { place, value, mode } => SpecializedOperation::Replace {
                        place: substitution.place(place)?,
                        value: *value,
                        mode: *mode,
                    },
                    OOperation::Discard(owner) => SpecializedOperation::Discard(*owner),
                    OOperation::ExitScope {
                        scope,
                        result,
                        mode,
                        owners,
                    } => SpecializedOperation::ExitScope {
                        scope: *scope,
                        result: *result,
                        mode: *mode,
                        owners: owners.clone(),
                    },
                    OOperation::Capture { closure, captures } => SpecializedOperation::Capture {
                        closure: *closure,
                        captures: captures.clone(),
                    },
                };
                instructions.push(SpecializedInstruction {
                    scope: instruction.scope,
                    destination: instruction.destination,
                    operation,
                });
            }
            let control = match &block.terminator.control {
                ControlTerminator::Goto(edge) => SpecializedControl::Goto(edge.clone()),
                ControlTerminator::SwitchBool {
                    condition,
                    on_true,
                    on_false,
                } => SpecializedControl::SwitchBool {
                    condition: *condition,
                    on_true: on_true.clone(),
                    on_false: on_false.clone(),
                },
                ControlTerminator::Invoke {
                    callee,
                    arguments,
                    result,
                    contract,
                    continuation,
                } => SpecializedControl::Invoke {
                    callee: *callee,
                    target: SpecializedCallTarget::Indirect,
                    arguments: arguments.clone(),
                    result: *result,
                    contract: contract.clone(),
                    continuation: *continuation,
                },
                ControlTerminator::Return(value) => SpecializedControl::Return(*value),
                ControlTerminator::Unreachable => SpecializedControl::Unreachable,
                ControlTerminator::Transfer(transfer) => {
                    SpecializedControl::Transfer(substitution.transfer(transfer)?)
                }
            };
            blocks.push(SpecializedBlock {
                parameters: block.parameters.clone(),
                instructions,
                terminator: SpecializedTerminator {
                    control,
                    operands: block.terminator.operands.clone(),
                    dispositions: block.terminator.dispositions.clone(),
                    successors: block.terminator.successors.clone(),
                },
            });
        }
        let mut closures = vec![];
        for (index, closure) in ownership.closures.iter().enumerate() {
            let mut environment = closure.environment.clone();
            for capture in &mut environment.captures {
                capture.ty = substitution.ty(&capture.ty)?;
            }
            environment.runs_in.effects = substitution.row(&environment.runs_in.effects)?;
            let result = ownership.blocks.iter().flat_map(|block| &block.instructions).find_map(|instruction| {
                if matches!(instruction.operation, OOperation::Capture { closure, .. } if closure.0 as usize == index) {
                    if let Type::Callable { result, .. } = &ownership.values[instruction.destination.0 as usize].ty { return Some(result.as_ref()); }
                }
                None
            }).ok_or_else(|| SpecializedError("closure lacks a callable result contract".into()))?;
            let result = closure.body.refined_result_type(result);
            let definition = if instance.arguments().is_empty() {
                closure.body.definition
            } else {
                crate::mir::materialized_lifted_callable_definition(
                    instance,
                    closure.body.definition,
                )
            };
            let body = Self::lower_body(
                &closure.body,
                result,
                instance,
                definition,
                arguments,
                signatures,
                primitives,
            )?;
            dependencies.extend(body.dependencies.clone());
            closures.push(SpecializedClosure {
                environment,
                body: Box::new(body),
            });
        }
        let mut result = Self {
            definition,
            source_definition: ownership.definition,
            instance: instance.clone(),
            safety: ownership.safety,
            unsafe_execution: ownership.unsafe_execution,
            parameters: ownership.parameters.clone(),
            values,
            result,
            scopes: ownership.scopes.clone(),
            entry: ownership.entry,
            labels: ownership.labels.clone(),
            handlers,
            closures,
            source_bindings: ownership.source_bindings.clone(),
            source_flow: ownership.source_flow.clone(),
            owners: ownership.owners.clone(),
            loans,
            blocks,
            dependencies,
            symbols: BTreeSet::new(),
            primitive_definitions: primitives
                .into_iter()
                .flat_map(|primitives| primitives.keys().copied())
                .collect(),
            layouts: vec![],
        };
        result.seal_call_targets();
        result.freeze_layouts(signatures)?;
        result.validate()?;
        Ok(result)
    }

    fn seal_call_targets(&mut self) {
        let targets = self.symbolic_targets();
        let mut escaped = vec![];
        for block in &self.blocks {
            for instruction in &block.instructions {
                match &instruction.operation {
                    SpecializedOperation::Read(_)
                    | SpecializedOperation::Transfer { .. }
                    | SpecializedOperation::ExitScope { .. }
                        if targets.contains_key(&instruction.destination) => {}
                    SpecializedOperation::Discard(_) => {}
                    operation => {
                        for value in operation.inputs(&self.loans) {
                            if let Some(target) = targets.get(&value) {
                                escaped.push(target.clone());
                            }
                        }
                    }
                }
            }
            let inputs = match &block.terminator.control {
                SpecializedControl::Invoke {
                    callee, arguments, ..
                } if targets.contains_key(callee) => arguments.clone(),
                terminator => terminator.inputs(),
            };
            for value in inputs {
                if let Some(target) = targets.get(&value) {
                    escaped.push(target.clone());
                }
            }
        }
        for (value, target) in &targets {
            if !escaped.contains(target)
                && !matches!(target, SpecializedCallTarget::Resumption { .. })
            {
                self.symbols.insert(*value);
                self.values[value.0 as usize].ty = Type::Unit;
            }
        }
        for block in &mut self.blocks {
            if let SpecializedControl::Invoke { callee, target, .. } = &mut block.terminator.control
            {
                *target = targets
                    .get(callee)
                    .cloned()
                    .unwrap_or(SpecializedCallTarget::Indirect);
            }
        }
    }

    pub(super) fn symbolic_targets(&self) -> BTreeMap<ControlValue, SpecializedCallTarget> {
        let mutable = self
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter_map(|instruction| match &instruction.operation {
                SpecializedOperation::Replace { place, .. } => Some(place.root()),
                SpecializedOperation::Borrow(id) => Some(self.loans[id.0 as usize].place.root()),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let mut targets = BTreeMap::new();
        for instruction in self.blocks.iter().flat_map(|block| &block.instructions) {
            let target = match &instruction.operation {
                SpecializedOperation::Compute(SpecializedComputation::Function {
                    definition,
                    arguments,
                }) => {
                    if self.primitive_definitions.contains(definition) {
                        Some(SpecializedCallTarget::Primitive {
                            definition: *definition,
                            arguments: arguments.clone(),
                        })
                    } else {
                        Some(SpecializedCallTarget::Direct(*definition))
                    }
                }
                SpecializedOperation::Compute(SpecializedComputation::HostFunction {
                    definition,
                    arguments,
                    import,
                }) => Some(SpecializedCallTarget::Host {
                    definition: *definition,
                    arguments: arguments.clone(),
                    import: import.clone(),
                }),
                SpecializedOperation::Compute(SpecializedComputation::Resumption {
                    handler,
                    clause,
                }) => Some(SpecializedCallTarget::Resumption {
                    handler: *handler,
                    clause: *clause,
                }),
                _ => None,
            };
            if let Some(target) = target {
                targets.insert(instruction.destination, target);
            }
        }
        loop {
            let previous = targets.len();
            for instruction in self.blocks.iter().flat_map(|block| &block.instructions) {
                if !mutable.contains(&instruction.destination)
                    && !targets.contains_key(&instruction.destination)
                    && let SpecializedOperation::Read(source)
                    | SpecializedOperation::Transfer { value: source, .. }
                    | SpecializedOperation::ExitScope { result: source, .. } =
                        instruction.operation
                    && let Some(target) = targets.get(&source).cloned()
                {
                    targets.insert(instruction.destination, target);
                }
            }
            if previous == targets.len() {
                return targets;
            }
        }
    }
}
