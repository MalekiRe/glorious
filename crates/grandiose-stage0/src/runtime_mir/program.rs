use super::*;
use crate::cleanup_mir::{CleanupMir, CleanupProgram};

#[derive(Clone, Debug)]
pub struct RuntimeProgram {
    entry: DefKey,
    functions: BTreeMap<DefKey, RuntimeMir>,
    constants: BTreeSet<DefKey>,
    instances: BTreeMap<DefKey, crate::MirInstance>,
}
impl RuntimeProgram {
    pub fn entry(&self) -> DefKey {
        self.entry
    }
    pub fn functions(&self) -> &BTreeMap<DefKey, RuntimeMir> {
        &self.functions
    }
    pub fn constants(&self) -> &BTreeSet<DefKey> {
        &self.constants
    }
    pub(crate) fn instances(&self) -> &BTreeMap<DefKey, crate::MirInstance> {
        &self.instances
    }

    pub(crate) fn reachable_function_keys(&self) -> BTreeSet<DefKey> {
        let mut pending = BTreeSet::from([self.entry]);
        let mut reachable = BTreeSet::new();
        while let Some(definition) = pending.pop_first() {
            if !reachable.insert(definition) {
                continue;
            }
            let Some(body) = self.functions.get(&definition) else {
                continue;
            };
            pending.extend(
                body.frame
                    .abandonment
                    .iter()
                    .map(|action| action.destructor),
            );
            for operation in body.blocks.iter().flat_map(|block| &block.instructions) {
                match operation {
                    RuntimeOperation::Call { callee, .. } => {
                        pending.insert(*callee);
                    }
                    RuntimeOperation::MakeCallable {
                        callee,
                        environment,
                        ..
                    } => {
                        pending.insert(*callee);
                        pending.extend(
                            environment
                                .as_ref()
                                .and_then(|environment| environment.destructor),
                        );
                    }
                    RuntimeOperation::HostCall {
                        resident_operations,
                        ..
                    } => {
                        pending.extend(
                            resident_operations
                                .iter()
                                .filter_map(|(_, destructor)| *destructor),
                        );
                    }
                    _ => {}
                }
            }
        }
        reachable
    }

    pub(crate) fn constant_cycle(&self) -> Option<Vec<DefKey>> {
        constant_cycle(&self.functions, &self.constants)
    }

    pub(crate) fn lower(
        source: &CleanupProgram,
        signatures: &crate::ElaboratedInterface,
        primitives: Option<&BTreeMap<DefKey, crate::PrimitiveRole>>,
    ) -> Result<Self, RuntimeError> {
        source.validate().map_err(|error| RuntimeError(error.0))?;
        let plans = source
            .destruction_programs()
            .iter()
            .map(|(key, plan)| (DefKey(key.fingerprint()), plan.clone()))
            .collect::<BTreeMap<_, _>>();
        let mut functions = BTreeMap::new();
        let mut instances = BTreeMap::new();
        fn environments(
            body: &CleanupMir,
            signatures: &crate::ElaboratedInterface,
            plans: &BTreeMap<DefKey, crate::destruction::Plan>,
            functions: &mut BTreeMap<DefKey, RuntimeMir>,
        ) -> Result<(), RuntimeError> {
            for closure in &body.closures {
                if let Some(function) =
                    destruction::environment(closure, signatures, plans).map_err(RuntimeError)?
                {
                    if let Some(previous) = functions.insert(function.definition, function.clone())
                        && previous != function
                    {
                        return Err(RuntimeError(
                            "Runtime environment identity collision".into(),
                        ));
                    }
                }
                environments(&closure.body, signatures, plans, functions)?;
            }
            Ok(())
        }
        for (definition, body) in source.functions() {
            let (function, lifted) = body
                .lower_runtime_values(body.result.clone(), 0, primitives, Some(signatures))
                .ok_or_else(|| {
                    RuntimeError(format!(
                        "Cleanup body {definition:?} has no runtime representation"
                    ))
                })?;
            if functions.insert(*definition, function).is_some() {
                return Err(RuntimeError("Runtime root collision".into()));
            }
            for (definition, function) in lifted {
                if functions.insert(definition, function).is_some() {
                    return Err(RuntimeError("Runtime closure collision".into()));
                }
            }
            environments(body, signatures, &plans, &mut functions)?;
            if !body.instance.arguments().is_empty() {
                instances.insert(
                    *definition,
                    crate::MirInstance {
                        executable: *definition,
                        key: body.instance.clone(),
                    },
                );
            }
        }
        for (key, plan) in source.destruction_programs() {
            let function = destruction::materialize(key, plan, signatures).map_err(RuntimeError)?;
            let executable = function.definition;
            if functions.insert(executable, function).is_some() {
                return Err(RuntimeError("Runtime destructor collision".into()));
            }
            instances.insert(
                executable,
                crate::MirInstance {
                    executable,
                    key: key.clone(),
                },
            );
        }
        for function in functions.values_mut() {
            function.frame = function.derive_frame().map_err(RuntimeError)?;
        }
        let program = Self {
            entry: source.entry(),
            functions,
            constants: source.constants().clone(),
            instances,
        };
        program.validate()?;
        Ok(program)
    }

    pub fn validate(&self) -> Result<(), RuntimeError> {
        if !self.functions.contains_key(&self.entry) {
            return Err(RuntimeError("Runtime entry is missing".into()));
        }
        let lifted = self
            .functions
            .values()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| &block.instructions)
            .filter_map(|operation| match operation {
                RuntimeOperation::MakeCallable {
                    callee,
                    environment: Some(_),
                    ..
                } => Some(*callee),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        for (definition, function) in &self.functions {
            if *definition != function.definition {
                return Err(RuntimeError("Runtime function identity mismatch".into()));
            }
            function
                .validate_with_specialized_lifted_targets(&lifted)
                .map_err(|error| RuntimeError(format!("Runtime {definition:?}: {error}")))?;
            if function.frame != function.derive_frame().map_err(RuntimeError)? {
                return Err(RuntimeError(
                    "Runtime frame ABI or transfer inventory is not exact".into(),
                ));
            }
            for block in &function.blocks {
                for operation in &block.instructions {
                    let target = match operation {
                        RuntimeOperation::Call { callee, .. }
                        | RuntimeOperation::MakeCallable { callee, .. } => Some(*callee),
                        _ => None,
                    };
                    if let Some(target) = target
                        && !self.functions.contains_key(&target)
                        && !self.constants.contains(&target)
                    {
                        return Err(RuntimeError(format!(
                            "Runtime call has no executable target: {target:?}"
                        )));
                    }
                    if let RuntimeOperation::Call {
                        dst,
                        callee,
                        arguments,
                    } = operation
                        && let Some(target) = self.functions.get(callee)
                    {
                        if target.captures != 0
                            || arguments.len() != target.parameters.len()
                            || arguments.iter().zip(&target.parameters).any(
                                |(argument, parameter)| {
                                    !crate::control_mir::call_type_matches(
                                        &target.locals[parameter.0 as usize].ty,
                                        &function.locals[argument.0 as usize].ty,
                                    )
                                },
                            )
                            // A diverging target has no normal result to
                            // inhabit the caller's otherwise-typed slot.
                            || (target.result != Type::Never
                                && !crate::control_mir::call_type_matches(
                                    &target.result,
                                    &function.locals[dst.0 as usize].ty,
                                ))
                        {
                            return Err(RuntimeError(format!(
                                "Runtime direct call ABI disagrees with its target: {definition:?} -> {callee:?}; arguments {:?}, parameters {:?}; result {:?}, expected {:?}",
                                arguments
                                    .iter()
                                    .map(|local| &function.locals[local.0 as usize].ty)
                                    .collect::<Vec<_>>(),
                                target
                                    .parameters
                                    .iter()
                                    .map(|local| &target.locals[local.0 as usize].ty)
                                    .collect::<Vec<_>>(),
                                function.locals[dst.0 as usize].ty,
                                target.result,
                            )));
                        }
                        if target.safety == crate::Safety::Unsafe && !function.unsafe_execution {
                            return Err(RuntimeError(
                                "Runtime unsafe call erased its execution requirement".into(),
                            ));
                        }
                    }
                    if let RuntimeOperation::MakeCallable {
                        dst,
                        callee,
                        captures,
                        environment,
                    } = operation
                        && let Some(target) = self.functions.get(callee)
                    {
                        let Type::Callable {
                            safety,
                            parameters,
                            result,
                            ..
                        } = &function.locals[dst.0 as usize].ty
                        else {
                            return Err(RuntimeError(
                                "Runtime callable ABI has no callable result type".into(),
                            ));
                        };
                        if *safety != target.safety
                            || target.captures as usize != captures.len()
                            || target.parameters.len() != captures.len() + parameters.len()
                            || captures.iter().zip(&target.parameters).any(
                                |(capture, parameter)| {
                                    !crate::control_mir::call_type_matches(
                                        &target.locals[parameter.0 as usize].ty,
                                        &function.locals[capture.0 as usize].ty,
                                    )
                                },
                            )
                            || parameters
                                .iter()
                                .zip(target.parameters.iter().skip(captures.len()))
                                .any(|(parameter, slot)| {
                                    !crate::control_mir::call_type_matches(
                                        &target.locals[slot.0 as usize].ty,
                                        parameter,
                                    )
                                })
                            || (target.result != Type::Never
                                && !crate::control_mir::call_type_matches(&target.result, result))
                        {
                            return Err(RuntimeError("Runtime callable environment/invocation ABI disagrees with its target".into()));
                        }
                        if let Some(environment) = environment
                            && let Some(destructor) = environment.destructor
                        {
                            let cleanup = self.functions.get(&destructor).ok_or_else(|| {
                                RuntimeError("Runtime capture cleanup is missing".into())
                            })?;
                            if destructor
                                != crate::mir::callable_environment_destructor_definition(*callee)
                                || cleanup.captures != 0
                                || cleanup.parameters.len() != environment.captures.len()
                                || cleanup.result != Type::Unit
                                || cleanup.safety != crate::Safety::Safe
                                || cleanup.parameters.iter().zip(&environment.captures).any(
                                    |(slot, capture)| {
                                        cleanup.locals[slot.0 as usize].ty != capture.ty
                                    },
                                )
                            {
                                return Err(RuntimeError("Runtime capture destruction ABI disagrees with its environment".into()));
                            }
                        }
                    }
                    if let RuntimeOperation::HostCall {
                        resident_operations,
                        ..
                    } = operation
                    {
                        for (ty, destructor) in resident_operations {
                            if let Some(destructor) = destructor {
                                let cleanup = self.functions.get(destructor).ok_or_else(|| {
                                    RuntimeError("Runtime native cleanup is missing".into())
                                })?;
                                if cleanup.captures != 0
                                    || cleanup.parameters.len() != 1
                                    || cleanup.result != Type::Unit
                                    || cleanup.safety != crate::Safety::Safe
                                    || cleanup.locals[cleanup.parameters[0].0 as usize].ty != *ty
                                {
                                    return Err(RuntimeError(
                                        "Runtime native cleanup has an incompatible resident ABI"
                                            .into(),
                                    ));
                                }
                            }
                        }
                    }
                    if let RuntimeOperation::MakeCallable {
                        environment: Some(environment),
                        ..
                    } = operation
                        && let Some(destructor) = environment.destructor
                        && !self.functions.contains_key(&destructor)
                    {
                        return Err(RuntimeError(
                            "Runtime environment destructor is missing".into(),
                        ));
                    }
                }
            }
            for drop in &function.frame.abandonment {
                let target = self
                    .functions
                    .get(&drop.destructor)
                    .ok_or_else(|| RuntimeError("Runtime frame destructor is missing".into()))?;
                if target.parameters.len() != 1
                    || target.locals[target.parameters[0].0 as usize].ty
                        != function.locals[drop.owner.0 as usize].ty
                    || target.result != Type::Unit
                {
                    return Err(RuntimeError(
                        "Runtime frame destructor has an incompatible ABI".into(),
                    ));
                }
            }
        }
        Ok(())
    }
}

fn constant_cycle(
    functions: &BTreeMap<crate::DefKey, RuntimeMir>,
    constants: &BTreeSet<crate::DefKey>,
) -> Option<Vec<crate::DefKey>> {
    fn visit(
        definition: crate::DefKey,
        functions: &BTreeMap<crate::DefKey, RuntimeMir>,
        constants: &BTreeSet<crate::DefKey>,
        visiting: &mut BTreeSet<crate::DefKey>,
        visited: &mut BTreeSet<crate::DefKey>,
        path: &mut Vec<crate::DefKey>,
    ) -> Option<Vec<crate::DefKey>> {
        if !visiting.insert(definition) {
            let start = path.iter().position(|key| *key == definition).unwrap_or(0);
            let mut cycle = path[start..].to_vec();
            cycle.push(definition);
            return Some(cycle);
        }
        path.push(definition);
        let function = functions.get(&definition)?;
        for callee in function
            .blocks
            .iter()
            .flat_map(|block| block.instructions.iter())
            .filter_map(|instruction| match instruction {
                RuntimeOperation::Call { callee, .. } if constants.contains(callee) => {
                    Some(*callee)
                }
                _ => None,
            })
        {
            if !visited.contains(&callee)
                && let Some(cycle) = visit(callee, functions, constants, visiting, visited, path)
            {
                return Some(cycle);
            }
            if visiting.contains(&callee) {
                let start = path.iter().position(|key| *key == callee).unwrap_or(0);
                let mut cycle = path[start..].to_vec();
                cycle.push(callee);
                return Some(cycle);
            }
        }
        path.pop();
        visiting.remove(&definition);
        visited.insert(definition);
        None
    }

    let mut visiting = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut path = vec![];
    for definition in constants {
        if !visited.contains(definition)
            && let Some(cycle) = visit(
                *definition,
                functions,
                constants,
                &mut visiting,
                &mut visited,
                &mut path,
            )
        {
            return Some(cycle);
        }
    }
    None
}

impl RuntimeMir {
    pub(super) fn register_layouts(
        &mut self,
        signatures: &crate::ElaboratedInterface,
    ) -> Result<(), String> {
        let types = self
            .locals
            .iter()
            .map(|local| local.ty.clone())
            .chain(std::iter::once(self.result.clone()))
            .collect::<Vec<_>>();
        let mut instructions = vec![];
        let mut building = vec![];
        let mut diagnostics = vec![];
        for ty in types {
            crate::mir::atomic::AtomicEmitter {
                locals: &mut self.locals,
                instructions: &mut instructions,
                nominal_copy_descriptors: &mut self.nominal_copy_descriptors,
                building_nominal_copy_descriptors: &mut building,
                diagnostics: &mut diagnostics,
                signatures: Some(signatures),
                runtime_primitives: None,
            }
            .register_nominal_copy_descriptors(&ty);
        }
        if !diagnostics.is_empty() || !instructions.is_empty() {
            return Err("Runtime layout sealing unexpectedly emitted executable work".into());
        }
        Ok(())
    }
}
