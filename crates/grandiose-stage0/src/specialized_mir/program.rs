use super::*;

#[derive(Clone, Debug)]
pub struct SpecializationInput {
    pub ownership: crate::ownership_mir::OwnershipMir,
    pub result: Type,
    pub is_constant: bool,
}

#[derive(Clone, Debug)]
pub struct SpecializedProgram {
    entry: DefKey,
    functions: BTreeMap<DefKey, SpecializedMir>,
    constants: BTreeSet<DefKey>,
}

#[derive(Clone, Debug)]
pub enum SpecializedDiscoveryError {
    Invalid(SpecializedError),
    Limit(crate::InstanceGraphError),
    NonAddressableLabel { definition: DefKey, ty: Type },
}
impl From<SpecializedError> for SpecializedDiscoveryError {
    fn from(error: SpecializedError) -> Self {
        Self::Invalid(error)
    }
}

impl SpecializedProgram {
    /// Demand discovery walks the specialized owner graph, never a Core
    /// expression arena. Implicit destruction/native edges use the same closed
    /// types as explicit calls and are charged to the same instance limits.
    pub(crate) fn discover(
        entry: DefKey,
        templates: &BTreeMap<DefKey, SpecializationInput>,
        signatures: &crate::ElaboratedInterface,
        primitives: Option<&BTreeMap<DefKey, crate::PrimitiveRole>>,
        limits: crate::InstanceLimits,
        destruction: &mut crate::destruction::Planner<'_>,
    ) -> Result<(Self, crate::InstanceGraph), SpecializedDiscoveryError> {
        let mut graph = crate::InstanceGraph::default();
        let root = lower::declaration_key(entry, vec![], signatures)?;
        graph
            .discover_root(
                crate::InstanceRoot {
                    key: root,
                    reason: "executable entry".into(),
                },
                limits,
            )
            .map_err(SpecializedDiscoveryError::Limit)?;
        let mut functions = BTreeMap::new();
        let mut constants = BTreeSet::new();
        while let Some(instance) = graph.pop_pending() {
            if crate::destruction::is_glue(&instance) {
                for callee in destruction.callees(&instance).map_err(SpecializedError)? {
                    graph
                        .discover_callee(&instance, callee, limits)
                        .map_err(SpecializedDiscoveryError::Limit)?;
                }
                continue;
            }
            if primitives.is_some_and(|primitives| primitives.contains_key(&instance.callable))
                || signatures.host_imports.contains_key(&instance.callable)
            {
                continue;
            }
            let template = templates.get(&instance.callable).ok_or_else(|| {
                SpecializedError(format!(
                    "demanded ownership template is missing: {:?}",
                    instance.callable
                ))
            })?;
            lower::check_addressability(&template.ownership, &instance, signatures)?;
            let body = SpecializedMir::lower(
                &template.ownership,
                &template.result,
                instance.clone(),
                signatures,
                primitives,
            )?;
            let mut callees = body.dependencies.values().cloned().collect::<BTreeSet<_>>();
            fn implied(
                body: &SpecializedMir,
                signatures: &crate::ElaboratedInterface,
                destruction: &mut crate::destruction::Planner<'_>,
                callees: &mut BTreeSet<InstanceKey>,
            ) -> Result<(), SpecializedError> {
                for ty in body
                    .values
                    .iter()
                    .map(|value| &value.ty)
                    .chain(std::iter::once(&body.result))
                {
                    if let Some(glue) = destruction.discover(ty).map_err(SpecializedError)? {
                        callees.insert(glue);
                    }
                }
                for block in &body.blocks {
                    for instruction in &block.instructions {
                        if let SpecializedOperation::Compute(
                            SpecializedComputation::HostFunction {
                                definition,
                                arguments,
                                ..
                            }
                            | SpecializedComputation::Function {
                                definition,
                                arguments,
                            },
                        ) = &instruction.operation
                            && (body.primitive_definitions.contains(definition)
                                || signatures.host_imports.contains_key(definition))
                        {
                            callees.insert(lower::declaration_key(
                                *definition,
                                arguments.clone(),
                                signatures,
                            )?);
                            // Generic raw-memory leaves may destroy a pointee
                            // without owning a T in a source-level register.
                            for argument in arguments {
                                if let GenericArgument::Type(ty) = argument
                                    && let Some(glue) =
                                        destruction.discover(ty).map_err(SpecializedError)?
                                {
                                    callees.insert(glue);
                                }
                            }
                        }
                    }
                    if let SpecializedControl::Invoke {
                        target: SpecializedCallTarget::Host { .. },
                        arguments,
                        result,
                        ..
                    } = &block.terminator.control
                    {
                        let roots = arguments
                            .iter()
                            .map(|value| body.values[value.0 as usize].ty.clone())
                            .chain(std::iter::once(body.values[result.0 as usize].ty.clone()))
                            .collect::<Vec<_>>();
                        for ty in crate::mir::native_contract_residents(&roots, signatures)
                            .map_err(SpecializedError)?
                        {
                            if let Some(glue) =
                                destruction.discover(&ty).map_err(SpecializedError)?
                            {
                                callees.insert(glue);
                            }
                        }
                    }
                }
                for closure in &body.closures {
                    implied(&closure.body, signatures, destruction, callees)?;
                }
                Ok(())
            }
            implied(&body, signatures, destruction, &mut callees)?;
            for callee in callees {
                graph
                    .discover_callee(&instance, callee, limits)
                    .map_err(SpecializedDiscoveryError::Limit)?;
            }
            if template.is_constant {
                constants.insert(body.definition);
            }
            if functions.insert(body.definition, body).is_some() {
                return Err(
                    SpecializedError("specialized executable identity collision".into()).into(),
                );
            }
        }
        let program = Self {
            entry,
            functions,
            constants,
        };
        program.validate()?;
        Ok((program, graph))
    }
}

impl SpecializedProgram {
    pub fn lower(
        entry: DefKey,
        templates: &BTreeMap<DefKey, SpecializationInput>,
        graph: &crate::InstanceGraph,
        signatures: &crate::ElaboratedInterface,
        primitives: Option<&BTreeMap<DefKey, crate::PrimitiveRole>>,
    ) -> Result<Self, SpecializedError> {
        let mut functions = BTreeMap::new();
        let mut constants = BTreeSet::new();
        for instance in graph.ordered() {
            if crate::destruction::is_glue(&instance)
                || primitives.is_some_and(|primitives| primitives.contains_key(&instance.callable))
                || signatures.host_imports.contains_key(&instance.callable)
            {
                continue;
            }
            let template = templates.get(&instance.callable).ok_or_else(|| {
                SpecializedError(format!(
                    "demanded ownership template is missing: {:?}",
                    instance.callable
                ))
            })?;
            let body = SpecializedMir::lower(
                &template.ownership,
                &template.result,
                instance,
                signatures,
                primitives,
            )?;
            if template.is_constant {
                constants.insert(body.definition);
            }
            if functions.insert(body.definition, body).is_some() {
                return Err(SpecializedError(
                    "specialized executable identity collision".into(),
                ));
            }
        }
        let program = Self {
            entry,
            functions,
            constants,
        };
        program.validate()?;
        Ok(program)
    }
    pub fn entry(&self) -> DefKey {
        self.entry
    }
    pub fn functions(&self) -> &BTreeMap<DefKey, SpecializedMir> {
        &self.functions
    }
    pub fn constants(&self) -> &BTreeSet<DefKey> {
        &self.constants
    }

    pub fn validate(&self) -> Result<(), SpecializedError> {
        if !self.functions.contains_key(&self.entry) {
            return Err(SpecializedError("specialized entry is absent".into()));
        }
        fn validate_body(
            body: &SpecializedMir,
            functions: &BTreeMap<DefKey, SpecializedMir>,
        ) -> Result<(), SpecializedError> {
            body.validate()?;
            for (definition, instance) in &body.dependencies {
                let target = functions.get(definition).ok_or_else(|| {
                    SpecializedError(format!("specialized dependency is absent: {instance:?}"))
                })?;
                if &target.instance != instance {
                    return Err(SpecializedError(
                        "specialized dependency resolves to another instance".into(),
                    ));
                }
            }
            for block in &body.blocks {
                if let SpecializedControl::Invoke {
                    target: SpecializedCallTarget::Direct(definition),
                    arguments,
                    result,
                    ..
                } = &block.terminator.control
                {
                    let target = functions.get(definition).ok_or_else(|| {
                        SpecializedError("specialized direct call target is absent".into())
                    })?;
                    if arguments.len() != target.parameters.len()
                        || arguments
                            .iter()
                            .zip(&target.parameters)
                            .any(|(argument, parameter)| {
                                !crate::control_mir::call_type_matches(
                                    &target.values[parameter.0 as usize].ty,
                                    &body.values[argument.0 as usize].ty,
                                )
                            })
                        || !crate::control_mir::call_type_matches(
                            &target.result,
                            &body.values[result.0 as usize].ty,
                        )
                    {
                        return Err(SpecializedError(format!(
                            "specialized direct call ABI disagrees with target {definition:?}"
                        )));
                    }
                }
                for instruction in &block.instructions {
                    if let SpecializedOperation::Compute(SpecializedComputation::Constant {
                        definition,
                    }) = instruction.operation
                    {
                        let target = &functions[&definition];
                        if !target.parameters.is_empty()
                            || !crate::control_mir::call_type_matches(
                                &target.result,
                                &body.values[instruction.destination.0 as usize].ty,
                            )
                        {
                            return Err(SpecializedError(
                                "specialized constant initializer ABI mismatch".into(),
                            ));
                        }
                    }
                }
            }
            for closure in &body.closures {
                validate_body(&closure.body, functions)?;
            }
            Ok(())
        }
        for (definition, body) in &self.functions {
            if *definition != body.definition {
                return Err(SpecializedError(
                    "specialized function table identity mismatch".into(),
                ));
            }
            validate_body(body, &self.functions)?;
        }
        Ok(())
    }

}
