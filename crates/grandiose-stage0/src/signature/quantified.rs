//! Declaration-owned universally quantified predicates.

use super::{ElaboratedAssociatedEffectBinding, ElaboratedAssociatedTypeBinding,
    ElaboratedTraitReference, GenericArgument, Type};

/// One lifetime-universal predicate, with a scope over the subject, relation,
/// and all associated equalities. Its `Lifetime::Bound` terms use the same
/// de Bruijn convention as callable types. This is never ordinary ambient
/// evidence until a checker explicitly opens or instantiates its binder.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QuantifiedWhereBound {
    pub lifetime_binders: u32,
    pub subject: Type,
    pub relation: ElaboratedTraitReference,
    pub type_bindings: Vec<ElaboratedAssociatedTypeBinding>,
    pub effect_bindings: Vec<ElaboratedAssociatedEffectBinding>,
}

#[derive(Clone)]
pub(crate) struct OpenedWhereBound {
    pub subject: Type,
    pub relation: ElaboratedTraitReference,
    pub type_bindings: Vec<ElaboratedAssociatedTypeBinding>,
    pub effect_bindings: Vec<ElaboratedAssociatedEffectBinding>,
}

impl QuantifiedWhereBound {
    /// Eliminate this binder for a particular lexical goal. Only its region
    /// variables are flexible: declaration type/row/const parameters remain
    /// rigid, and no inference state is returned to the caller.
    pub(crate) fn for_goal(&self, goal: &crate::TraitGoal) -> Option<OpenedWhereBound> {
        if self.relation.definition != goal.relation.definition || self.lifetime_binders == 0 {
            return None;
        }
        if crate::core::type_contains_inference(&goal.subject)
            || goal.relation.arguments.iter().any(crate::core::generic_argument_contains_inference) { return None; }
        let mut invalid = false;
        let _ = self.map_terms(|argument| {
            invalid |= crate::core::generic_argument_contains_inference(&argument);
            argument
        });
        if invalid { return None; }
        let mut inference = crate::InferContext::default();
        let lifetimes = (0..self.lifetime_binders).map(|_| inference.fresh_lifetime()).collect::<Vec<_>>();
        let opened = self.map_terms(|argument| {
            crate::types::regions::open_argument(argument.clone(), |index| lifetimes.get(index as usize).copied())
                .unwrap_or_else(|| { invalid = true; argument })
        });
        if invalid { return None; }
        inference.unify(opened.subject.clone(), goal.subject.clone()).ok()?;
        inference.unify_generic_arguments(opened.relation.arguments.clone(), goal.relation.arguments.clone()).ok()?;
        let resolved = opened.map_terms(|argument| {
            crate::types::regions::map_argument_regions(argument.clone(), &mut |region, _| {
                let region = inference.resolve_lifetime(region).ok()?;
                (!matches!(region, crate::Lifetime::Infer(_))).then_some(region)
            }).unwrap_or_else(|| { invalid = true; argument })
        });
        // Unification can queue open-row equalities or coerce bottom types.
        // Neither is lexical entailment: after region elimination the whole
        // kind-preserving predicate head must actually be identical.
        (!invalid && resolved.subject == goal.subject && resolved.relation == goal.relation).then_some(OpenedWhereBound {
            subject: resolved.subject, relation: resolved.relation,
            type_bindings: resolved.type_bindings, effect_bindings: resolved.effect_bindings,
        })
    }
    pub(crate) fn open(&self, scope: &crate::types::UniversalScope) -> Option<OpenedWhereBound> {
        let mut invalid = false;
        let opened = self.map_terms(|argument| {
            match crate::types::regions::open_argument(argument.clone(), |index| scope.region(index)) {
                Some(argument) => argument,
                None => { invalid = true; argument },
            }
        });
        (!invalid).then_some(OpenedWhereBound {
            subject: opened.subject, relation: opened.relation,
            type_bindings: opened.type_bindings, effect_bindings: opened.effect_bindings,
        })
    }
    /// Transform terms while retaining their containing binder. The caller
    /// must shift any inserted caller-owned terms under this scope first.
    /// Each callback sees a whole term, not a fabricated callable wrapper.
    pub(crate) fn map_terms(
        &self,
        mut map: impl FnMut(GenericArgument) -> GenericArgument,
    ) -> Self {
        fn ty(value: &Type, map: &mut impl FnMut(GenericArgument) -> GenericArgument) -> Type {
            match map(GenericArgument::Type(value.clone())) {
                GenericArgument::Type(value) => value,
                _ => Type::Error,
            }
        }
        fn relation(value: &ElaboratedTraitReference, map: &mut impl FnMut(GenericArgument) -> GenericArgument) -> ElaboratedTraitReference {
            ElaboratedTraitReference {
                definition: value.definition,
                arguments: value.arguments.iter().cloned().map(map).collect(),
            }
        }
        let mut invalid_row_kind = false;
        let result = Self {
            lifetime_binders: self.lifetime_binders,
            subject: ty(&self.subject, &mut map),
            relation: relation(&self.relation, &mut map),
            type_bindings: self.type_bindings.iter().map(|binding| ElaboratedAssociatedTypeBinding {
                subject: ty(&binding.subject, &mut map),
                relation: relation(&binding.relation, &mut map),
                name: binding.name.clone(), item_generic_kinds: binding.item_generic_kinds.clone(),
                item_arguments: binding.item_arguments.iter().cloned().map(&mut map).collect(),
                value: ty(&binding.value, &mut map),
            }).collect(),
            effect_bindings: self.effect_bindings.iter().map(|binding| ElaboratedAssociatedEffectBinding {
                subject: ty(&binding.subject, &mut map),
                relation: relation(&binding.relation, &mut map),
                name: binding.name.clone(), item_generic_kinds: binding.item_generic_kinds.clone(),
                item_arguments: binding.item_arguments.iter().cloned().map(&mut map).collect(),
                value: match map(GenericArgument::EffectRow(binding.value.clone())) {
                    GenericArgument::EffectRow(row) => row,
                    _ => {
                        invalid_row_kind = true;
                        binding.value.clone()
                    },
                },
            }).collect(),
        };
        if invalid_row_kind { Self { subject: Type::Error, ..result } } else { result }
    }

    pub(crate) fn instantiate(&self, arguments: &[GenericArgument]) -> Self {
        let shifted = arguments.iter().cloned()
            .map(|argument| crate::types::regions::shift_argument(argument, 1))
            .collect::<Option<Vec<_>>>();
        match shifted {
            Some(arguments) => self.map_terms(|value| super::substitute_alias_generic_identity_argument(value, &arguments)),
            None => Self { subject: Type::Error, ..self.clone() },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CallableSignature, DefKey, Digest, EffectRow, Lifetime, Mutability, Quantity, Safety};

    fn signature() -> CallableSignature {
        let subject = Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Bound { depth: 0, index: 0 },
            referent: Box::new(Type::Generic(0)),
        };
        let relation = ElaboratedTraitReference {
            definition: crate::intrinsic_callable_trait_definition(),
            arguments: vec![GenericArgument::Type(Type::Unit)],
        };
        CallableSignature {
            safety: Safety::Safe, generics: 1, generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![], result: Type::Unit, effects: EffectRow::empty(), invocation: Quantity::ONCE,
            where_bounds: vec![], where_outlives: vec![], where_associated_type_bindings: vec![], where_associated_effect_bindings: vec![],
            universal_bounds: vec![QuantifiedWhereBound {
                lifetime_binders: 1, subject: subject.clone(), relation: relation.clone(),
                type_bindings: vec![ElaboratedAssociatedTypeBinding {
                    subject: subject.clone(), relation: relation.clone(), name: "Output".into(),
                    item_generic_kinds: vec![], item_arguments: vec![], value: Type::Unit,
                }],
                effect_bindings: vec![ElaboratedAssociatedEffectBinding {
                    subject, relation, name: "Effects".into(), item_generic_kinds: vec![], item_arguments: vec![],
                    value: EffectRow::empty(),
                }],
            }],
        }
    }

    #[test]
    fn native_contract_fingerprint_retains_quantifiers_and_their_equalities() {
        let definition = DefKey(Digest::of_bytes(b"quantified-native-contract"));
        let signature = signature();
        let fingerprint = super::super::host_contract_fingerprint(definition, &signature);
        for mutation in 0..8 {
            let mut changed = signature.clone();
            let bound = &mut changed.universal_bounds[0];
            match mutation {
                0 => bound.lifetime_binders = 2,
                1 => bound.subject = Type::Unit,
                2 => bound.relation.arguments = vec![GenericArgument::Type(Type::Never)],
                3 => bound.type_bindings[0].value = Type::Never,
                4 => bound.effect_bindings[0].value = EffectRow::closed([definition]),
                5 => bound.type_bindings[0].item_arguments = vec![GenericArgument::Lifetime(Lifetime::Static)],
                6 => changed.universal_bounds.clear(),
                7 => changed.where_outlives.push(crate::OutlivesPredicate::Type {
                    subject: Type::Generic(0), lifetime: Lifetime::Static,
                }),
                _ => unreachable!(),
            }
            assert_ne!(fingerprint, super::super::host_contract_fingerprint(definition, &changed), "mutation {mutation}");
        }
    }

    #[test]
    fn quantified_term_mapping_never_grants_a_wrong_kind_row() {
        let bound = signature().universal_bounds.remove(0);
        let invalid = bound.map_terms(|value| match value {
            GenericArgument::EffectRow(_) => GenericArgument::Type(Type::Unit),
            value => value,
        });
        assert_eq!(invalid.subject, Type::Error);
        assert_eq!(invalid.lifetime_binders, 1);
    }

    #[test]
    fn frozen_quantified_contracts_reject_invalid_scopes_and_detached_equalities() {
        for mutation in 0..4 {
            let mut signature = signature();
            let bound = &mut signature.universal_bounds[0];
            match mutation {
                0 => bound.lifetime_binders = 0,
                1 => bound.type_bindings[0].subject = Type::Unit,
                2 => bound.subject = Type::Reference {
                    mutability: Mutability::Shared,
                    lifetime: Lifetime::Bound { depth: 1, index: 0 }, referent: Box::new(Type::Unit),
                },
                3 => bound.subject = Type::Reference {
                    mutability: Mutability::Shared,
                    lifetime: Lifetime::Placeholder(crate::types::UniversalRegion { universe: 0, index: 0 }),
                    referent: Box::new(Type::Unit),
                },
                _ => unreachable!(),
            }
            let mut interface = super::super::ElaboratedInterface::default();
            interface.definitions.insert(DefKey(Digest::of_bytes(b"invalid-quantified-contract")),
                super::super::ElaboratedHeader::Callable(signature));
            interface.validate_projection_obligations();
            assert!(interface.diagnostics.iter().any(|diagnostic| diagnostic.code == "G4199"), "mutation {mutation}: {:?}", interface.diagnostics);
        }
    }
}
