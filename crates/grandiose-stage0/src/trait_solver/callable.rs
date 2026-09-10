//! Structural callable predicates and their exact associated evidence.
use super::*;

pub(super) struct CallableEvidence {
    pub(super) output: Type,
    pub(super) effects: EffectRow,
    pub(super) after: Option<Type>,
}

impl TraitSolver {
    /// Crossing a written ABI can forget value refinements, but never the
    /// prerequisites for invoking that value. Discharge any prerequisites
    /// not retained by the destination in an isolated universal scope.
    pub(crate) fn callable_abi_erasure_proven(&mut self, expected: &Type, actual: &Type) -> bool {
        if expected == actual || *actual == Type::Never { return true; }
        if self.quantified_depth >= self.limits.max_depth || self.steps >= self.limits.max_steps { return false; }
        match (expected, actual) {
            (Type::Callable { contract: required, lifetime_binders: required_binders, parameters: required_parameters, result: required_result, .. },
             Type::Callable { contract: supplied, lifetime_binders, parameters, result, .. }) => {
                if required_binders != lifetime_binders || required_parameters.len() != parameters.len() { return false; }
                let mut scoped = self.fresh_query();
                scoped.quantified_depth += 1;
                scoped.steps = self.steps + 1;
                let Ok(scope) = scoped.quantified_inference.begin_universal_scope((*lifetime_binders).max(1)) else { return false; };
                let open = |value| crate::types::regions::open_argument(value, |index| scope.region(index));
                let proof = (|| -> Option<bool> {
                    let required = required.open(|index| scope.region(index))?;
                    let supplied = supplied.open(|index| scope.region(index))?;
                    let retained = supplied.residual.where_bounds.iter().all(|value| required.residual.where_bounds.contains(value))
                        && supplied.residual.where_outlives.iter().all(|value| required.residual.where_outlives.contains(value))
                        && supplied.residual.type_bindings.iter().all(|value| required.residual.type_bindings.contains(value))
                        && supplied.residual.effect_bindings.iter().all(|value| required.residual.effect_bindings.contains(value))
                        && supplied.universal.iter().all(|value| required.universal.contains(value));
                    if !retained {
                        scoped.remember_callable_environments(actual);
                        let assumptions = Arc::clone(&scoped.lexical_assumptions);
                        if !scoped.contract_proven(&supplied.residual, &assumptions, scoped.quantified_depth)
                            || !supplied.universal.iter().all(|bound| scoped.proves_universal(bound)) { return Some(false); }
                    }
                    for (required, supplied) in required_parameters.iter().zip(parameters) {
                        let GenericArgument::Type(required) = open(GenericArgument::Type(required.clone()))? else { return None; };
                        let GenericArgument::Type(supplied) = open(GenericArgument::Type(supplied.clone()))? else { return None; };
                        // The actual function receives arguments described
                        // by the public function value's input contract.
                        if !scoped.callable_abi_erasure_proven(&supplied, &required) { return Some(false); }
                    }
                    let GenericArgument::Type(required) = open(GenericArgument::Type((**required_result).clone()))? else { return None; };
                    let GenericArgument::Type(supplied) = open(GenericArgument::Type((**result).clone()))? else { return None; };
                    Some(scoped.callable_abi_erasure_proven(&required, &supplied))
                })().unwrap_or(false);
                let sealed = scoped.quantified_inference.finish_universal_scope(scope).is_ok();
                self.steps = scoped.steps;
                proof && sealed
            }
            (Type::Tuple(required), Type::Tuple(supplied)) => required.len() == supplied.len()
                && required.iter().zip(supplied).all(|(required, supplied)| self.callable_abi_erasure_proven(required, supplied)),
            (Type::Nominal { definition: required_definition, arguments: required }, Type::Nominal { definition, arguments })
                if required_definition == definition => required.len() == arguments.len() && required.iter().zip(arguments).all(|(required, supplied)| {
                    match (required, supplied) {
                        (GenericArgument::Type(required), GenericArgument::Type(supplied)) =>
                            self.callable_abi_erasure_proven(required, supplied) && self.callable_abi_erasure_proven(supplied, required),
                        _ => true,
                    }
                }),
            (Type::Reference { mutability, referent: required, .. }, Type::Reference { referent: supplied, .. }) => {
                self.callable_abi_erasure_proven(required, supplied)
                    && (*mutability != crate::Mutability::Unique || self.callable_abi_erasure_proven(supplied, required))
            }
            (Type::Array(required), Type::Array(supplied))
            | (Type::FixedArray { element: required, .. }, Type::FixedArray { element: supplied, .. })
            | (Type::StaticData { element: required, .. }, Type::StaticData { element: supplied, .. }) => self.callable_abi_erasure_proven(required, supplied),
            (Type::RawPointer { pointee: required, .. }, Type::RawPointer { pointee: supplied, .. }) =>
                self.callable_abi_erasure_proven(required, supplied) && self.callable_abi_erasure_proven(supplied, required),
            // Ordinary shape/region matching remains the type checker's job.
            _ => true,
        }
    }

    /// Associated Fn equalities can determine an impl binder which does not
    /// occur in its receiver head. Such a binder is existential at selection
    /// (e.g. Map's Output/Effects), not a new rigid caller type. Derive it only
    /// from exact callable evidence; never guess from its spelling or erase a
    /// quantifier. The complete predicate is still checked by the caller.
    fn refine_callable_implementation_substitution(
        &mut self,
        implementation: &ElaboratedImplementation,
        substitution: &mut ImplementationSubstitution,
    ) -> Option<()> {
        for bound in &implementation.universal_bounds {
            if !is_intrinsic_callable_trait(&bound.relation) { continue; }
            let needs_type = implementation.generic_kinds.iter().enumerate().any(|(index, kind)|
                *kind == crate::GenericKind::Type && !substitution.types.contains_key(&(index as u32)))
                && bound.type_bindings.iter().any(|binding| binding.name == "Output");
            let needs_row = bound.effect_bindings.iter().any(|binding| binding.value.tails.iter().any(|tail|
                matches!(tail, crate::EffectTail::Generic(index) if !substitution.effect_rows.contains_key(index))));
            if !needs_type && !needs_row { continue; }
            if self.quantified_depth >= self.limits.max_depth || self.steps >= self.limits.max_steps { return None; }
            let mut scoped = self.fresh_query();
            scoped.quantified_depth += 1;
            scoped.steps = self.steps + 1;
            let scope = scoped.quantified_inference.begin_universal_scope(bound.lifetime_binders).ok()?;
            let shifted = substitution_under_region_binder(substitution)?;
            let instantiated = bound.map_terms(|argument| substitute_generic_argument(&argument, &shifted));
            let opened = instantiated.open(&scope)?;
            let goal = scoped.normalize_goal(TraitGoal { subject: opened.subject, relation: opened.relation }).ok()?;
            let lexical = scoped.lexical_universal.iter().filter_map(|bound| bound.for_goal(&goal)).collect::<Vec<_>>();
            let evidence = scoped.callable_evidence(&goal);
            for binding in &bound.type_bindings {
                if binding.name != "Output" { continue; }
                let actual = evidence.as_ref().map(|value| value.output.clone()).or_else(|| {
                    let mut values = lexical.iter().flat_map(|bound| &bound.type_bindings)
                        .filter(|binding| binding.name == "Output" && binding.item_arguments.is_empty()).map(|binding| binding.value.clone());
                    let selected = values.next()?;
                    values.all(|value| value == selected).then_some(selected)
                });
                if let Some(actual) = actual {
                    // Match the complete associated output, not only a bare
                    // generic leaf: Option<U> can determine U as well. Open
                    // only this predicate's binder; the existing structural
                    // matcher prevents any new outer slot from capturing its
                    // placeholders, including beneath nested callable terms.
                    let GenericArgument::Type(template) = crate::types::regions::open_argument(
                        GenericArgument::Type(binding.value.clone()), |index| scope.region(index))? else { return None; };
                    match_type_at(&template, &actual, substitution, 1)?;
                }
            }
            for binding in &bound.effect_bindings {
                if binding.name != "Effects" || !binding.value.effects.is_empty() || !binding.value.projections.is_empty() { continue; }
                if binding.value.tails.len() != 1 { continue; }
                let Some(crate::EffectTail::Generic(index)) = binding.value.tails.first().copied() else { continue; };
                if substitution.effect_rows.contains_key(&index) { continue; }
                let actual = evidence.as_ref().map(|value| value.effects.clone()).or_else(|| {
                    let mut values = lexical.iter().flat_map(|bound| &bound.effect_bindings)
                        .filter(|binding| binding.name == "Effects" && binding.item_arguments.is_empty()).map(|binding| binding.value.clone());
                    let selected = values.next()?;
                    values.all(|value| value == selected).then_some(selected)
                });
                if let Some(actual) = actual {
                    if effect_row_contains_free_hrtb_placeholder(&actual, 0) { return None; }
                    install_item_argument(substitution, index, GenericArgument::EffectRow(actual));
                }
            }
            solve_pending_effect_rows(substitution)?;
            scoped.quantified_inference.finish_universal_scope(scope).ok()?;
            self.steps = scoped.steps;
        }
        Some(())
    }

    pub(super) fn match_rule_with_callable_bindings(
        &mut self,
        implementation: &ElaboratedImplementation,
        goal: &TraitGoal,
    ) -> Option<ImplementationSubstitution> {
        let mut substitution = match_rule(implementation, goal)?;
        self.refine_callable_implementation_substitution(implementation, &mut substitution)?;
        Some(substitution)
    }

    pub(crate) fn complete_callable_implementation_arguments(
        &mut self,
        implementation: &ElaboratedImplementation,
        arguments: &mut BTreeMap<u32, GenericArgument>,
    ) -> Option<()> {
        let mut substitution = ImplementationSubstitution::default();
        for (index, argument) in arguments.iter() { install_item_argument(&mut substitution, *index, argument.clone()); }
        self.refine_callable_implementation_substitution(implementation, &mut substitution)?;
        for (index, kind) in implementation.generic_kinds.iter().enumerate() {
            let index = index as u32;
            let value = match kind {
                crate::GenericKind::Type => substitution.types.get(&index).cloned().map(GenericArgument::Type),
                crate::GenericKind::Lifetime => substitution.lifetimes.get(&index).copied().map(GenericArgument::Lifetime),
                crate::GenericKind::EffectRow => substitution.effect_rows.get(&index).cloned().map(GenericArgument::EffectRow),
                crate::GenericKind::Const(_) => substitution.generic_arguments.get(&index).cloned(),
            };
            if let Some(value) = value { arguments.insert(index, value); }
        }
        Some(())
    }


    pub(super) fn remember_callable_environments(&mut self, ty: &Type) {
        fn argument(solver: &mut TraitSolver, value: &GenericArgument) {
            match value {
                GenericArgument::Type(value) => solver.remember_callable_environments(value),
                GenericArgument::EffectRow(row) => {
                    for effect in &row.effects { for value in &effect.arguments { argument(solver, value); } }
                    for projection in &row.projections {
                        solver.remember_callable_environments(&projection.subject);
                        for value in projection.trait_arguments.iter().chain(&projection.item_arguments) { argument(solver, value); }
                    }
                }
                _ => {}
            }
        }
        match ty {
            Type::Callable { contract, parameters, result, effects, .. } => {
                for environment in contract.environment.iter().chain(&contract.after_environment) {
                    if !self.callable_environments.contains(environment) {
                        self.callable_environments.push((**environment).clone());
                        self.tables.clear();
                    }
                }
                for value in parameters.iter().chain(std::iter::once(result.as_ref())).chain(&contract.captures) {
                    self.remember_callable_environments(value);
                }
                argument(self, &GenericArgument::EffectRow(effects.clone()));
            }
            Type::Nominal { arguments, .. } => for value in arguments { argument(self, value); },
            Type::Projection { subject, trait_arguments, item_arguments, .. } => {
                self.remember_callable_environments(subject);
                for value in trait_arguments.iter().chain(item_arguments) { argument(self, value); }
            }
            Type::Tuple(values) => for value in values { self.remember_callable_environments(value); },
            Type::Array(value) | Type::Reference { referent: value, .. }
                | Type::RawPointer { pointee: value, .. } | Type::StaticData { element: value, .. }
                | Type::FixedArray { element: value, .. } => self.remember_callable_environments(value),
            _ => {}
        }
    }

    pub(super) fn callable_evidence(&mut self, goal: &TraitGoal) -> Option<CallableEvidence> {
        if !is_intrinsic_callable_trait(&goal.relation) && !is_intrinsic_runs_in_trait(&goal.relation) { return None; }
        if crate::core::type_contains_inference(&goal.subject)
            || goal.relation.arguments.iter().any(crate::core::generic_argument_contains_inference) { return None; }
        let (callable, receiver) = match &goal.subject {
            Type::Reference { mutability, referent, .. } => (referent.as_ref(), Some(*mutability)),
            value => (value, None),
        };
        let label_callable = crate::types::label::callable(callable);
        let callable = label_callable.as_ref().unwrap_or(callable);
        let Type::Callable { contract, safety: crate::Safety::Safe, lifetime_binders, parameters, result, effects, .. } = callable else { return None; };
        if receiver.is_some_and(|receiver| match receiver {
            crate::Mutability::Shared => !contract.shared_receiver,
            crate::Mutability::Unique => !contract.unique_receiver,
        }) { return None; }
        let mut inference = crate::InferContext::default();
        let regions = (0..*lifetime_binders).map(|_| inference.fresh_lifetime()).collect::<Vec<_>>();
        let open = |argument| crate::types::regions::open_argument(argument, |index| regions.get(index as usize).copied());
        let GenericArgument::Type(inputs) = open(GenericArgument::Type(Type::Tuple(parameters.clone())))? else { return None; };
        let GenericArgument::Type(output) = open(GenericArgument::Type((**result).clone()))? else { return None; };
        let GenericArgument::EffectRow(effects) = open(GenericArgument::EffectRow(effects.clone()))? else { return None; };
        let contract = contract.open(|index| regions.get(index as usize).copied())?;
        let (required_inputs, after) = if is_intrinsic_runs_in_trait(&goal.relation) {
            let [GenericArgument::Type(access), GenericArgument::Type(inputs)] = goal.relation.arguments.as_slice() else { return None; };
            let environment = contract.environment.as_deref()?;
            let after = match access {
                Type::Reference { mutability, referent, .. } => {
                    if match mutability { crate::Mutability::Shared => !contract.shared_receiver, crate::Mutability::Unique => !contract.unique_receiver } { return None; }
                    inference.unify((**referent).clone(), environment.clone()).ok()?;
                    environment.clone()
                }
                access => {
                    inference.unify(access.clone(), environment.clone()).ok()?;
                    contract.after_environment.as_deref()?.clone()
                }
            };
            (inputs.clone(), Some(after))
        } else {
            let [GenericArgument::Type(inputs)] = goal.relation.arguments.as_slice() else { return None; };
            (inputs.clone(), None)
        };
        let required_inputs = if required_inputs == Type::Unit { Type::Tuple(vec![]) } else { required_inputs };
        let required_inputs = self.normalize_type(required_inputs).ok()?;
        inference.unify(required_inputs.clone(), inputs.clone()).ok()?;
        // Resolve only local region cells. The rigid regions in this goal
        // belong to the caller's live scope, not to this helper's inference.
        let mut resolve = |argument| crate::types::regions::map_argument_regions(argument, &mut |region, _| {
            let region = inference.resolve_lifetime(region).ok()?;
            (!matches!(region, crate::Lifetime::Infer(_))).then_some(region)
        });
        if resolve(GenericArgument::Type(inputs))? != GenericArgument::Type(required_inputs) { return None; }
        let GenericArgument::Type(output) = resolve(GenericArgument::Type(output))? else { return None; };
        let GenericArgument::EffectRow(effects) = resolve(GenericArgument::EffectRow(effects))? else { return None; };
        let after = match after {
            Some(after) => {
                let GenericArgument::Type(after) = resolve(GenericArgument::Type(after))? else { return None; };
                Some(after)
            }
            None => None,
        };
        if contract.has_residual() {
            if self.quantified_depth >= self.limits.max_depth || self.steps >= self.limits.max_steps { return None; }
            let contract = contract.try_map_terms(|argument, _| resolve(argument).ok_or(())).ok()?;
            let mut scoped = self.fresh_query();
            scoped.quantified_depth += 1;
            scoped.steps = self.steps + 1;
            let assumptions = Arc::clone(&scoped.lexical_assumptions);
            let proven = scoped.contract_proven(&contract.residual, &assumptions, scoped.quantified_depth)
                && contract.universal.iter().all(|bound| scoped.proves_universal(bound));
            self.steps = scoped.steps;
            if !proven { return None; }
        }
        Some(CallableEvidence { output, effects, after })
    }
}
