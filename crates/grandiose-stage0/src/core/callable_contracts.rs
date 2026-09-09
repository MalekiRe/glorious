//! Value-resident callable contracts and receiver authority.

use super::*;
use crate::CallableContract;

impl Elaborator<'_> {
    pub(super) fn queue_callable_abi_erasure(&mut self, expected: Type, actual: Type, span: Span) {
        fn may_require_proof(ty: &Type) -> bool {
            match ty {
                Type::Infer(_) => true,
                Type::Callable { contract, parameters, result, .. } => contract.has_residual()
                    || parameters.iter().any(may_require_proof) || may_require_proof(result),
                Type::Tuple(values) => values.iter().any(may_require_proof),
                Type::Nominal { arguments, .. } => arguments.iter().any(|value|
                    matches!(value, GenericArgument::Type(value) if may_require_proof(value))),
                Type::Array(value) | Type::FixedArray { element: value, .. } | Type::StaticData { element: value, .. }
                | Type::Reference { referent: value, .. } | Type::RawPointer { pointee: value, .. } => may_require_proof(value),
                Type::Projection { .. } => true,
                _ => false,
            }
        }
        let expected = self.inference.resolve_type_structure(expected);
        let actual = self.inference.resolve_type_structure(actual);
        if expected != actual && (may_require_proof(&expected) || may_require_proof(&actual)) {
            self.pending_callable_erasures.push((expected, actual, span));
        }
    }

    pub(super) fn joined_callable_value_type(&self, mut ty: Type) -> Type {
        for (from, to) in &self.callable_value_joins {
            let replacement = [(self.inference.resolve_type_structure(from.clone()), self.inference.resolve_type_structure(to.clone()))];
            let GenericArgument::Type(value) = CallableContract::replace_value_types(GenericArgument::Type(ty), &replacement, 0) else { unreachable!() };
            ty = value;
        }
        ty
    }

    /// Reconstruct invocation access from body operations, independently of
    /// how the environment acquired its residents. Reading a field of an
    /// owned capture is not a move of that capture.
    fn callable_capture_access(&self, body: CoreId, parameters: &[(String, Type)], environment: &CaptureEnvironment) -> (bool, bool) {
        #[derive(Clone, Copy)] enum Access { Shared, Unique, Owned, ExplicitMove }
        fn mark(name: &str, access: Access, locals: &std::collections::BTreeSet<String>, captures: &std::collections::BTreeSet<String>, result: &mut (bool, bool)) {
            if locals.contains(name) || !captures.contains(name) { return; }
            match access { Access::Shared => {}, Access::Unique => result.0 = false, Access::Owned | Access::ExplicitMove => *result = (false, false) }
        }
        fn place(elaborator: &Elaborator<'_>, value: &CorePlace, access: Access, locals: &mut std::collections::BTreeSet<String>, captures: &std::collections::BTreeSet<String>, result: &mut (bool, bool)) {
            match value {
                CorePlace::Local { name, .. } => mark(name, access, locals, captures, result),
                CorePlace::Field { base, .. } => place(elaborator, base, access, locals, captures, result),
                CorePlace::Deref { reference, .. } => walk(elaborator, *reference, access, locals, captures, result),
                CorePlace::Error => {},
            }
        }
        fn walk(elaborator: &Elaborator<'_>, id: CoreId, access: Access, locals: &mut std::collections::BTreeSet<String>, captures: &std::collections::BTreeSet<String>, result: &mut (bool, bool)) {
            let expression = &elaborator.expressions[id.0 as usize];
            let access = if matches!(access, Access::Owned) && elaborator.owned_capture_mode(&expression.ty) == CaptureMode::Copy { Access::Shared } else { access };
            match &expression.kind {
                CoreKind::Local(name) | CoreKind::Resumption { name, .. } => mark(name, access, locals, captures, result),
                CoreKind::Field { base, .. } | CoreKind::Deref(base) => walk(elaborator, *base, access, locals, captures, result),
                CoreKind::Borrow { value, unique } => walk(elaborator, *value, if *unique { Access::Unique } else { Access::Shared }, locals, captures, result),
                // Even a Copy-eligible resident is vacated by an explicit
                // move; borrowed invocation cannot restore it implicitly.
                CoreKind::Move(value) => walk(elaborator, *value, Access::ExplicitMove, locals, captures, result),
                CoreKind::Assign { place: target, value } => {
                    walk(elaborator, *value, Access::Owned, locals, captures, result);
                    place(elaborator, target, Access::Unique, locals, captures, result);
                }
                CoreKind::Let { name, value } => {
                    walk(elaborator, *value, Access::Owned, locals, captures, result);
                    locals.insert(name.clone());
                }
                CoreKind::Block(values) => {
                    let mut locals = locals.clone();
                    for value in values { walk(elaborator, *value, Access::Owned, &mut locals, captures, result); }
                }
                CoreKind::Closure { environment, .. } => for capture in &environment.captures {
                    let access = match capture.mode { CaptureMode::SharedBorrow | CaptureMode::Copy => Access::Shared, CaptureMode::UniqueBorrow => Access::Unique, CaptureMode::Move => Access::Owned };
                    mark(&capture.name, access, locals, captures, result);
                },
                CoreKind::Call { callee, arguments, .. } => {
                    let access = match elaborator.expressions[callee.0 as usize].ty {
                        Type::Reference { mutability: Mutability::Shared, .. } => Access::Shared,
                        Type::Reference { mutability: Mutability::Unique, .. } => Access::Unique,
                        _ => Access::Owned,
                    };
                    walk(elaborator, *callee, access, locals, captures, result);
                    for argument in arguments { walk(elaborator, *argument, Access::Owned, locals, captures, result); }
                }
                CoreKind::PatternTest { subject, .. } => walk(elaborator, *subject, Access::Shared, locals, captures, result),
                CoreKind::Handle { computation, clauses } => {
                    walk(elaborator, *computation, Access::Owned, locals, captures, result);
                    for clause in clauses {
                        let mut locals = locals.clone();
                        locals.extend(clause.bindings.iter().map(|(name, _)| name.clone()));
                        if let CoreHandlerResumption::Explicit { name, .. } = &clause.resumption { locals.insert(name.clone()); }
                        walk(elaborator, clause.body, Access::Owned, &mut locals, captures, result);
                    }
                }
                CoreKind::Completion { computation, clauses, .. } => {
                    walk(elaborator, *computation, Access::Owned, locals, captures, result);
                    for clause in clauses {
                        let mut locals = locals.clone();
                        locals.extend(clause.bindings.iter().map(|(name, _)| name.clone()));
                        walk(elaborator, clause.body, Access::Owned, &mut locals, captures, result);
                    }
                }
                kind => for child in core_children(kind) { walk(elaborator, child, Access::Owned, locals, captures, result); },
            }
        }
        let mut locals = parameters.iter().map(|(name, _)| name.clone()).collect();
        let captures = environment.captures.iter().map(|capture| capture.name.clone()).collect();
        let mut result = (true, true);
        walk(self, body, Access::Owned, &mut locals, &captures, &mut result);
        result
    }

    /// Eliminate only declaration-owned region binders. This runs inside the
    /// caller's universal proof transaction, so matching a lexical promise
    /// cannot export a fresh rigid region through an outer inference hole.
    pub(super) fn lexical_callable_predicate(
        &mut self,
        subject: &Type,
        relation: &crate::ElaboratedTraitReference,
        types: &[crate::ElaboratedAssociatedTypeBinding],
        effects: &[crate::ElaboratedAssociatedEffectBinding],
    ) -> bool {
        let mut candidates = self.ambient_universal_bounds.clone();
        candidates.extend(self.ambient_where_bounds.iter().map(|(subject, relation)| crate::QuantifiedWhereBound {
            lifetime_binders: 0, subject: subject.clone(), relation: relation.clone(),
            type_bindings: self.ambient_callable_type_bindings.iter()
                .filter(|binding| binding.subject == *subject && binding.relation == *relation).cloned().collect(),
            effect_bindings: self.ambient_callable_effect_bindings.iter()
                .filter(|binding| binding.subject == *subject && binding.relation == *relation).cloned().collect(),
        }));
        for candidate in candidates {
            if candidate.relation.definition != relation.definition { continue; }
            let mut inference = self.inference.clone();
            let lifetimes = (0..candidate.lifetime_binders).map(|_| inference.fresh_lifetime()).collect::<Vec<_>>();
            let mut valid = true;
            let candidate = if candidate.lifetime_binders == 0 { candidate } else {
                candidate.map_terms(|argument| crate::types::regions::open_argument(argument.clone(),
                    |index| lifetimes.get(index as usize).copied()).unwrap_or_else(|| { valid = false; argument }))
            };
            if !valid || inference.unify(candidate.subject, subject.clone()).is_err()
                || inference.unify_generic_arguments(candidate.relation.arguments, relation.arguments.clone()).is_err() { continue; }
            let matched = types.iter().all(|required| {
                let matches = candidate.type_bindings.iter().filter(|actual|
                    actual.name == required.name && actual.item_generic_kinds == required.item_generic_kinds
                        && actual.item_arguments == required.item_arguments).collect::<Vec<_>>();
                let [actual] = matches.as_slice() else { return false; };
                inference.unify(required.value.clone(), actual.value.clone()).is_ok()
            }) && effects.iter().all(|required| {
                let matches = candidate.effect_bindings.iter().filter(|actual|
                    actual.name == required.name && actual.item_generic_kinds == required.item_generic_kinds
                        && actual.item_arguments == required.item_arguments).collect::<Vec<_>>();
                let [actual] = matches.as_slice() else { return false; };
                inference.unify_effect_rows(required.value.clone(), actual.value.clone()).is_ok()
            });
            if matched { self.inference = inference; return true; }
        }
        false
    }

    pub(super) fn prove_intrinsic_callable_predicate(
        &mut self,
        subject: Type,
        relation: crate::ElaboratedTraitReference,
        type_bindings: Vec<crate::ElaboratedAssociatedTypeBinding>,
        effect_bindings: Vec<crate::ElaboratedAssociatedEffectBinding>,
        span: Span,
    ) -> Result<(), (&'static str, &'static str)> {
        if self.lexical_callable_predicate(&subject, &relation, &type_bindings, &effect_bindings) { return Ok(()); }
        let subject = self.inference.resolve_type_structure(subject);
        let (callable, receiver) = match subject {
            Type::Reference { mutability, referent, .. } => (self.inference.resolve_type_structure(*referent), Some(mutability)),
            value => (value, None),
        };
        let Type::Callable { contract, safety, lifetime_binders, parameters, result, effects, .. } = callable else {
            return Err(("G4105", "intrinsic callable predicate requires exact receiver evidence"));
        };
        if safety != crate::Safety::Safe { return Err(("G4200", "unsafe callable cannot supply safe callable evidence")); }
        if receiver.is_some_and(|receiver| match receiver {
            Mutability::Shared => !contract.shared_receiver, Mutability::Unique => !contract.unique_receiver,
        }) { return Err(("G4188", "callable capture access does not permit the required borrowed receiver")); }
        let lifetimes = (0..lifetime_binders).map(|_| self.inference.fresh_lifetime()).collect::<Vec<_>>();
        let open = |value| crate::types::regions::open_argument(value, |index| lifetimes.get(index as usize).copied())
            .ok_or(("G5017", "callable evidence has an invalid lifetime binder"));
        let parameters = parameters.into_iter().map(|parameter| {
            let GenericArgument::Type(parameter) = open(GenericArgument::Type(parameter))? else { unreachable!() };
            Ok(parameter)
        }).collect::<Result<Vec<_>, (&'static str, &'static str)>>()?;
        let GenericArgument::Type(result) = open(GenericArgument::Type(*result))? else { unreachable!() };
        let GenericArgument::EffectRow(effects) = open(GenericArgument::EffectRow(effects))? else { unreachable!() };
        let contract = contract.open(|index| lifetimes.get(index as usize).copied())
            .ok_or(("G5017", "callable residual contract has an invalid lifetime binder"))?;
        let runs_in = crate::is_intrinsic_runs_in_trait(&relation);
        let (inputs, after) = if runs_in {
            let Some((access, inputs)) = intrinsic_runs_in_arguments(&relation) else {
                return Err(("G4188", "intrinsic RunsIn requires an environment access and tuple input"));
            };
            let Some(environment) = contract.environment.as_deref() else {
                return Err(("G4188", "intrinsic RunsIn requires compiler-issued environment evidence"));
            };
            let Some(after_environment) = contract.after_environment.as_deref() else {
                return Err(("G4188", "intrinsic RunsIn requires a sealed environment post-state"));
            };
            self.remember_generated_environment_type(environment);
            self.remember_generated_environment_type(after_environment);
            let after = match self.match_runs_in_access(access, environment, span) {
                Some(RunsInAccess::Owned) => after_environment.clone(),
                Some(RunsInAccess::Shared) if contract.shared_receiver => environment.clone(),
                Some(RunsInAccess::Unique) if contract.unique_receiver => environment.clone(),
                _ => return Err(("G4188", "intrinsic RunsIn access exceeds the callable's sealed capture authority")),
            };
            (inputs, Some(after))
        } else {
            let [GenericArgument::Type(inputs)] = relation.arguments.as_slice() else {
                return Err(("G4164", "intrinsic Fn requires exactly one tuple input"));
            };
            (inputs.clone(), None)
        };
        let inputs = match inputs {
            Type::Tuple(inputs) => inputs, Type::Unit => vec![],
            _ => return Err(("G4164", "intrinsic callable input must be a tuple")),
        };
        // The actual argument can select an associated input family before
        // this predicate is opened (for example an iterator's concrete Item).
        // Compare its selected semantic type, never the projection spelling.
        let inputs = self.inference.resolve_type_structure(Type::Tuple(inputs));
        let inputs = self.normalize_selectable_type_projections(inputs);
        let parameters = self.inference.resolve_type_structure(Type::Tuple(parameters));
        let parameters = self.normalize_selectable_type_projections(parameters);
        self.inference.unify(inputs, parameters)
            .map_err(|_| ("G4166", "callable inputs do not satisfy the required lifetime contract"))?;
        for binding in type_bindings {
            let expected = match binding.name.as_str() {
                "Output" => &result,
                "After" if runs_in => after.as_ref().expect("RunsIn post-state"),
                _ => return Err(("G4165", "intrinsic callable predicate has an invalid associated equality")),
            };
            self.inference.unify(binding.value, expected.clone())
                .map_err(|_| ("G4167", "callable does not satisfy the exact associated type equality"))?;
        }
        for binding in effect_bindings {
            if binding.name != "Effects" { return Err(("G4165", "intrinsic callable predicate has an invalid effect equality")); }
            self.inference.unify_effect_rows(binding.value, effects.clone())
                .map_err(|_| ("G4168", "callable effects do not satisfy the exact associated row equality"))?;
        }
        // A value with residual prerequisites is not an unconditional Fn
        // witness. Supplying it to a generic consumer must discharge them.
        if contract.has_residual() {
            let contract = contract.try_map_terms(|argument, _| self.inference.zonk_generic_argument(argument))
                .map_err(|_| ("G4141", "callable residual predicates remain unresolved"))?;
            let assumptions = self.ambient_trait_solver_assumptions();
            let solver = self.trait_query();
            if !solver.contract_proven(&contract.residual, &assumptions, 0)
                || contract.universal.iter().any(|bound| !solver.proves_universal(bound)) {
                return Err(("G4143", "callable residual predicates are not established by this invocation"));
            }
        }
        Ok(())
    }

    pub(super) fn mint_callable_contract(&self, kind: &CoreKind, ty: &mut Type) {
        let Type::Callable { contract, .. } = ty else { return; };
        match kind {
            CoreKind::Function { definition, arguments, .. } => {
                let Ok(signature) = self.signatures.instantiate_callable_generic(*definition, arguments)
                    else { return; };
                **contract = CallableContract {
                    environment: Some(Box::new(Type::Unit)),
                    after_environment: Some(Box::new(Type::Unit)),
                    captures: vec![], shared_receiver: true, unique_receiver: true,
                    residual: crate::AssociatedItemContract {
                        where_bounds: signature.where_bounds,
                        where_outlives: signature.where_outlives,
                        type_bindings: signature.where_associated_type_bindings,
                        effect_bindings: signature.where_associated_effect_bindings,
                    },
                    universal: signature.universal_bounds,
                };
            }
            CoreKind::Closure { body, parameters, environment, .. } => {
                // Capture ownership and invocation access are different. A
                // forced-move capture may be read through the environment;
                // conversely a Copy capture can contain mutable local state.
                let (shared_receiver, unique_receiver) = self.callable_capture_access(*body, parameters, environment);
                let empty = environment.captures.is_empty();
                contract.captures = environment.captures.iter().map(|capture|
                    crate::capture_formation::CaptureFormation::new(capture).resident_type()).collect();
                contract.environment = Some(Box::new(if empty { Type::Unit } else { generated_environment_type(environment.brand, false, &contract.captures) }));
                contract.after_environment = Some(Box::new(if empty { Type::Unit } else { generated_environment_type(environment.brand, true, &contract.captures) }));
                contract.shared_receiver = shared_receiver;
                contract.unique_receiver = unique_receiver;
            }
            _ => {}
        }
    }

    pub(super) fn check_resident_callable_contract(
        &mut self,
        contract: &CallableContract,
        parameters: Vec<Type>,
        arguments: Option<&[CoreId]>,
        substitution: &CallLifetimeSubstitution,
        span: Span,
    ) {
        if !contract.has_residual() { return; }
        let contract = match contract.try_map_terms(|value, extra|
            substitute_call_generic_argument(value, substitution, extra)) {
            Ok(contract) => contract,
            Err(error) => { self.lifetime_error(span, error); self.recovered = true; return; }
        };
        self.check_callable_contract_bounds(CallableSignature {
            safety: crate::Safety::Safe, generics: 0, generic_kinds: vec![],
            parameters, result: Type::Unit, effects: EffectRow::empty(), invocation: crate::Quantity::ONCE,
            where_bounds: contract.residual.where_bounds,
            where_outlives: contract.residual.where_outlives,
            where_associated_type_bindings: contract.residual.type_bindings,
            where_associated_effect_bindings: contract.residual.effect_bindings,
            universal_bounds: contract.universal,
        }, arguments, span);
    }
}
