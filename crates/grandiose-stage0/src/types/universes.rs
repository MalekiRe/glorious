//! Transactional inference scopes for universal-region proofs.

use super::*;

pub(crate) struct UniversalScope {
    saved: InferContext,
    universe: u32,
    binder_count: u32,
}

impl UniversalScope {
    pub(crate) fn region(&self, index: u32) -> Option<Lifetime> {
        (index < self.binder_count).then_some(Lifetime::Placeholder(UniversalRegion {
            universe: self.universe,
            index,
        }))
    }
}

impl InferContext {
    pub(crate) fn begin_universal_scope(&mut self, binder_count: u32) -> Result<UniversalScope, TypeError> {
        if binder_count == 0 || self.checking_universe_leaks.is_some() || self.solving_effect_equalities {
            return Err(TypeError::InvalidUniversalScope);
        }
        let universe = self.next_universe;
        let next = universe.checked_add(1).ok_or(TypeError::InvalidUniversalScope)?;
        let saved = self.clone();
        self.next_universe = next;
        self.active_universes.push(universe);
        Ok(UniversalScope { saved, universe, binder_count })
    }

    pub(crate) fn abort_universal_scope(&mut self, scope: UniversalScope) {
        // Never reuse an identity after rollback: scoped solver tables may
        // still contain the failed query's keys until their next reset.
        let next_universe = self.next_universe;
        *self = scope.saved;
        self.next_universe = self.next_universe.max(next_universe);
    }

    pub(crate) fn finish_universal_scope(&mut self, scope: UniversalScope) -> Result<(), TypeError> {
        if self.active_universes.last() != Some(&scope.universe) {
            self.abort_universal_scope(scope);
            return Err(TypeError::InvalidUniversalScope);
        }
        let result = self.check_universal_leaks(&scope);
        if result.is_err() {
            self.abort_universal_scope(scope);
        } else {
            self.active_universes.pop();
            self.checking_universe_leaks = None;
            self.solving_effect_equalities = scope.saved.solving_effect_equalities;
        }
        result
    }

    fn check_universal_leaks(&mut self, scope: &UniversalScope) -> Result<(), TypeError> {
        self.solve_effect_equalities()?;
        self.checking_universe_leaks = Some(scope.universe);
        // The audit resolves existing bindings but must not re-enter solving
        // while traversing the pending-obligation queue itself.
        self.solving_effect_equalities = true;
        // Partial zonking follows indirect type, row, const, and lifetime
        // bindings without defaulting unrelated inference holes. A newer
        // placeholder anywhere reachable from an older cell is a leak.
        for index in 0..scope.saved.bindings.len() {
            if let Some(value) = self.bindings[index].clone() {
                self.bindings[index] = Some(self.zonk(value)?);
            }
        }
        for index in 0..scope.saved.effect_bindings.len() {
            if let Some(value) = self.effect_bindings[index].clone() {
                self.effect_bindings[index] = Some(self.zonk_effects_allowing_generic_tail(value)?);
            }
        }
        for index in 0..scope.saved.const_bindings.len() {
            if let Some(value) = self.const_bindings[index].clone() {
                self.const_bindings[index] = Some(self.zonk_generic_argument(value)?);
            }
        }
        for index in 0..scope.saved.lifetime_bindings.len() {
            if let Some(value) = self.lifetime_bindings[index] {
                self.lifetime_bindings[index] = Some(self.zonk_lifetime(value)?);
            }
        }
        // Deferred constraints are also outward state, including constraints
        // created by this proof. They cannot retain proof-local regions.
        let pending = self.pending_effect_equalities.clone();
        self.pending_effect_equalities = pending.into_iter().map(|(left, right)| {
            Ok((self.zonk_effects_allowing_generic_tail(left)?, self.zonk_effects_allowing_generic_tail(right)?))
        }).collect::<Result<_, TypeError>>()?;

        // Older cells have now been resolved through any younger aliases.
        // Discard proof-local assignments; remaining holes are ordinary
        // unconstrained cells, not owners of the now-closed rigid region.
        self.bindings[scope.saved.bindings.len()..].fill(None);
        self.effect_bindings[scope.saved.effect_bindings.len()..].fill(None);
        self.const_bindings[scope.saved.const_bindings.len()..].fill(None);
        self.lifetime_bindings[scope.saved.lifetime_bindings.len()..].fill(None);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reference(lifetime: Lifetime) -> Type {
        Type::Reference { mutability: Mutability::Shared, lifetime, referent: Box::new(Type::Unit) }
    }

    #[test]
    fn universal_regions_are_rigid_fresh_and_not_fingerprintable() {
        let mut inference = InferContext::default();
        let first = inference.begin_universal_scope(1).unwrap();
        let region = first.region(0).unwrap();
        assert!(inference.unify(reference(region), reference(Lifetime::Static)).is_err());
        assert!(inference.type_fingerprint(reference(region)).is_err());
        inference.finish_universal_scope(first).unwrap();
        assert!(inference.zonk(reference(region)).is_err());
        let second = inference.begin_universal_scope(1).unwrap();
        assert_ne!(Some(region), second.region(0));
        inference.abort_universal_scope(second);
    }

    #[test]
    fn indirect_outer_type_and_lifetime_leaks_roll_back_every_assignment() {
        let mut inference = InferContext::default();
        let outer = inference.fresh();
        let unrelated = inference.fresh();
        let scope = inference.begin_universal_scope(1).unwrap();
        let local = inference.fresh();
        inference.unify(outer.clone(), Type::Tuple(vec![local.clone()])).unwrap();
        inference.unify(local, reference(scope.region(0).unwrap())).unwrap();
        inference.unify(unrelated.clone(), Type::Unit).unwrap();
        assert!(matches!(inference.finish_universal_scope(scope), Err(TypeError::EscapingUniversalRegion(_))));
        assert!(matches!(inference.zonk(outer), Err(TypeError::Unresolved(_))));
        assert!(matches!(inference.zonk(unrelated), Err(TypeError::Unresolved(_))));

        let lifetime = inference.fresh_lifetime();
        let scope = inference.begin_universal_scope(1).unwrap();
        inference.unify(reference(lifetime), reference(scope.region(0).unwrap())).unwrap();
        assert!(inference.finish_universal_scope(scope).is_err());
        assert_eq!(inference.resolve_lifetime(lifetime).unwrap(), lifetime);
    }

    #[test]
    fn local_region_inference_is_discharged_but_safe_outer_constraints_commit() {
        let mut inference = InferContext::default();
        let outer = inference.fresh();
        let hole = inference.fresh();
        let scope = inference.begin_universal_scope(1).unwrap();
        let lifetime = inference.fresh_lifetime();
        inference.unify(reference(lifetime), reference(scope.region(0).unwrap())).unwrap();
        inference.unify(outer.clone(), Type::Tuple(vec![Type::Unit, hole.clone()])).unwrap();
        inference.finish_universal_scope(scope).unwrap();
        inference.unify(hole, Type::Unit).unwrap();
        assert_eq!(inference.zonk(outer).unwrap(), Type::Tuple(vec![Type::Unit, Type::Unit]));
    }

    #[test]
    fn a_region_hidden_in_an_outer_effect_instance_is_a_leak() {
        let mut inference = InferContext::default();
        let outer = inference.fresh_effects();
        let scope = inference.begin_universal_scope(1).unwrap();
        let row = EffectRow::closed_instances([EffectInstance {
            definition: DefKey(Digest::of_bytes(b"universal-effect-leak")),
            arguments: vec![GenericArgument::Lifetime(scope.region(0).unwrap())],
        }]);
        inference.unify_effect_rows(outer.clone(), row).unwrap();
        assert!(inference.finish_universal_scope(scope).is_err());
        assert!(inference.zonk_effects(outer).is_err());
    }

    #[test]
    fn associated_const_projection_regions_are_included_in_the_leak_check() {
        let mut inference = InferContext::default();
        let outer = inference.fresh_const(ConstKind::U32);
        let scope = inference.begin_universal_scope(1).unwrap();
        let projection = GenericArgument::ConstProjection {
            subject: Box::new(reference(scope.region(0).unwrap())),
            trait_definition: DefKey(Digest::of_bytes(b"universal-const-leak")),
            trait_arguments: vec![], name: "Size".into(), kind: ConstKind::U32,
        };
        inference.unify_generic_arguments(vec![outer.clone()], vec![projection]).unwrap();
        assert!(matches!(inference.finish_universal_scope(scope), Err(TypeError::EscapingUniversalRegion(_))));
        assert!(matches!(inference.zonk_generic_argument(outer), Err(TypeError::UnresolvedConst(_))));
    }

    #[test]
    fn nested_proof_scopes_preserve_outer_regions_without_confusing_their_identity() {
        let mut inference = InferContext::default();
        let outer = inference.begin_universal_scope(1).unwrap();
        let older_region = outer.region(0).unwrap();
        let value = inference.fresh();
        inference.unify(value.clone(), reference(older_region)).unwrap();
        let inner = inference.begin_universal_scope(1).unwrap();
        assert_ne!(inner.region(0), Some(older_region));
        let local = inference.fresh_lifetime();
        inference.unify(reference(local), reference(inner.region(0).unwrap())).unwrap();
        inference.finish_universal_scope(inner).unwrap();
        assert_eq!(inference.zonk(value).unwrap(), reference(older_region));
        inference.finish_universal_scope(outer).unwrap();
        assert!(inference.zonk(reference(older_region)).is_err());
    }
}
