//! Declaration-owned predicates for nominal fields and every instantiated use.
use super::*;

pub(super) fn encode_contract(bytes: &mut Vec<u8>, contract: &AssociatedItemContract, universal: &[QuantifiedWhereBound]) {
    fn part(bytes: &mut Vec<u8>, value: &[u8]) {
        bytes.extend_from_slice(&(value.len() as u64).to_le_bytes());
        bytes.extend_from_slice(value);
    }
    fn predicate(bytes: &mut Vec<u8>, bound: &QuantifiedWhereBound) {
        bytes.extend_from_slice(&bound.lifetime_binders.to_le_bytes());
        bytes.extend_from_slice(&bound.relation.definition.0.as_bytes());
        bytes.extend_from_slice(&(bound.relation.arguments.len() as u64).to_le_bytes());
        bytes.extend_from_slice(&(bound.type_bindings.len() as u64).to_le_bytes());
        for binding in &bound.type_bindings {
            bytes.extend_from_slice(&binding.relation.definition.0.as_bytes());
            part(bytes, binding.name.as_bytes());
            part(bytes, &binding.item_generic_kinds.iter().map(|kind| kind.tag()).collect::<Vec<_>>());
            bytes.extend_from_slice(&(binding.relation.arguments.len() as u64).to_le_bytes());
            bytes.extend_from_slice(&(binding.item_arguments.len() as u64).to_le_bytes());
        }
        bytes.extend_from_slice(&(bound.effect_bindings.len() as u64).to_le_bytes());
        for binding in &bound.effect_bindings {
            bytes.extend_from_slice(&binding.relation.definition.0.as_bytes());
            part(bytes, binding.name.as_bytes());
            part(bytes, &binding.item_generic_kinds.iter().map(|kind| kind.tag()).collect::<Vec<_>>());
            bytes.extend_from_slice(&(binding.relation.arguments.len() as u64).to_le_bytes());
            bytes.extend_from_slice(&(binding.item_arguments.len() as u64).to_le_bytes());
        }
        bound.map_terms(|argument| {
            part(bytes, &crate::types::canonical_generic_arguments_encoding(&[argument.clone()]));
            argument
        });
    }
    bytes.extend_from_slice(&(contract.where_bounds.len() as u64).to_le_bytes());
    for (subject, relation) in &contract.where_bounds {
        predicate(bytes, &QuantifiedWhereBound { lifetime_binders: 0, subject: subject.clone(),
            relation: relation.clone(), type_bindings: vec![], effect_bindings: vec![] });
    }
    bytes.extend_from_slice(&(contract.where_outlives.len() as u64).to_le_bytes());
    for bound in &contract.where_outlives {
        bytes.push(match bound { OutlivesPredicate::Type { .. } => 0, OutlivesPredicate::Region { .. } => 1 });
        bound.map_terms(|argument| {
            part(bytes, &crate::types::canonical_generic_arguments_encoding(&[argument.clone()]));
            argument
        });
    }
    predicate(bytes, &QuantifiedWhereBound { lifetime_binders: 0, subject: Type::Unit,
        relation: ElaboratedTraitReference { definition: intrinsic_callable_trait_definition(), arguments: vec![] },
        type_bindings: contract.type_bindings.clone(), effect_bindings: contract.effect_bindings.clone() });
    bytes.extend_from_slice(&(universal.len() as u64).to_le_bytes());
    for bound in universal { predicate(bytes, bound); }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nominal_native_identity_retains_every_predicate_component() {
        let definition = DefKey(crate::Digest::of_bytes(b"nominal-contract-owner"));
        let relation = ElaboratedTraitReference { definition: DefKey(crate::Digest::of_bytes(b"nominal-contract-trait")), arguments: vec![] };
        let header = ElaboratedHeader::Nominal {
            generics: 1, generic_kinds: vec![GenericKind::Type], layout: ElaboratedNominalLayout::Struct(vec![]),
            contract: AssociatedItemContract { where_bounds: vec![(Type::Generic(0), relation.clone())],
                where_outlives: vec![], type_bindings: vec![], effect_bindings: vec![] }, universal_bounds: vec![],
        };
        let original = nominal_contract_fingerprint(definition, &header);
        for mutation in 0..6 {
            let mut changed = header.clone();
            let ElaboratedHeader::Nominal { contract, universal_bounds, .. } = &mut changed else { unreachable!() };
            match mutation {
                0 => contract.where_bounds.clear(),
                1 => contract.where_bounds[0].1.definition = definition,
                2 => contract.where_outlives.push(OutlivesPredicate::Type { subject: Type::Generic(0), lifetime: Lifetime::Static }),
                3 => contract.type_bindings.push(ElaboratedAssociatedTypeBinding { subject: Type::Generic(0), relation: relation.clone(),
                    name: "Item".into(), item_generic_kinds: vec![], item_arguments: vec![], value: Type::Unit }),
                4 => contract.effect_bindings.push(ElaboratedAssociatedEffectBinding { subject: Type::Generic(0), relation: relation.clone(),
                    name: "Effects".into(), item_generic_kinds: vec![], item_arguments: vec![], value: EffectRow::empty() }),
                _ => universal_bounds.push(QuantifiedWhereBound { lifetime_binders: 1, subject: Type::Generic(0), relation: relation.clone(),
                    type_bindings: vec![], effect_bindings: vec![] }),
            }
            assert_ne!(original, nominal_contract_fingerprint(definition, &changed), "mutation {mutation}");
        }
    }

    #[test]
    fn frozen_nominal_equalities_cannot_grant_unbound_trait_evidence() {
        let definition = DefKey(crate::Digest::of_bytes(b"detached-nominal"));
        let mut interface = ElaboratedInterface::default();
        interface.definitions.insert(definition, ElaboratedHeader::Nominal {
            generics: 1, generic_kinds: vec![GenericKind::Type], layout: ElaboratedNominalLayout::Struct(vec![]),
            contract: AssociatedItemContract { type_bindings: vec![ElaboratedAssociatedTypeBinding {
                subject: Type::Generic(0), relation: ElaboratedTraitReference { definition, arguments: vec![] },
                name: "Item".into(), item_generic_kinds: vec![], item_arguments: vec![], value: Type::Unit,
            }], ..Default::default() }, universal_bounds: vec![],
        });
        interface.validate_projection_obligations();
        assert!(interface.diagnostics.iter().any(|diagnostic| diagnostic.code == "G4199" && diagnostic.message.contains("detached")));
    }
}

impl ElaboratedInterface {
    pub(super) fn validate_nominal_projection_obligations(
        &self, layout: &ElaboratedNominalLayout, contract: &AssociatedItemContract,
        universal: &[QuantifiedWhereBound], base_solver: &crate::TraitSolver, diagnostics: &mut Vec<SignatureDiagnostic>,
    ) {
        let projection_solver = &ProjectionSolver::from(base_solver.fresh_query());
        let fields: Vec<&Type> = match layout {
            ElaboratedNominalLayout::Struct(fields) | ElaboratedNominalLayout::TupleStruct(fields) =>
                fields.iter().map(|field| &field.ty).collect(),
            ElaboratedNominalLayout::Enum(variants) => variants.iter().flat_map(|variant| match &variant.payload {
                ElaboratedEnumVariantPayload::Unit => vec![],
                ElaboratedEnumVariantPayload::Tuple(fields) => fields.iter().collect(),
                ElaboratedEnumVariantPayload::Struct(fields) => fields.iter().map(|field| &field.ty).collect(),
            }).collect(),
            ElaboratedNominalLayout::Opaque => vec![],
        };
        let ambient = &contract.where_bounds;
        let mut solver = base_solver.fresh_query();
        solver.set_lexical_assumptions(ambient.iter().map(|(subject, relation)| crate::TraitGoal {
            subject: subject.clone(), relation: relation.clone() }).collect());
        solver.set_associated_bindings(contract.type_bindings.clone(), contract.effect_bindings.clone());
        solver.set_universal_assumptions(universal.to_vec());
        solver.set_outlives_assumptions(contract.where_outlives.iter().cloned()
            .chain(solver.implied_outlives(fields.iter().map(|field| (*field).clone()))).collect());
        self.validate_quantified_projection_obligations(projection_solver, universal, ambient, diagnostics);
        self.validate_associated_binding_projection_obligations(projection_solver, &contract.type_bindings, &contract.effect_bindings, ambient, diagnostics);
        if contract.type_bindings.iter().map(|binding| (&binding.subject, &binding.relation))
            .chain(contract.effect_bindings.iter().map(|binding| (&binding.subject, &binding.relation)))
            .any(|(subject, relation)| !self.ambient_projection_goal_proves(&crate::TraitGoal {
                subject: subject.clone(), relation: relation.clone() }, ambient)) {
            diagnostics.push(SignatureDiagnostic { code: "G4199", message: "nominal associated equality is detached from its declared trait predicate".into() });
        }
        for (subject, relation) in ambient {
            self.validate_type_projection_obligations(projection_solver, subject, ambient, diagnostics);
            self.validate_trait_reference_projection_obligations(projection_solver, relation, ambient, diagnostics);
        }
        for field in &fields { self.validate_type_projection_obligations(projection_solver, field, ambient, diagnostics); }
        if !solver.contract_domains_proven(contract) || !fields.iter().all(|ty| solver.type_domains_proven(ty)) {
            diagnostics.push(SignatureDiagnostic { code: "G4303", message: "nominal field or predicate does not establish its declared domain requirements".into() });
        }
        if contract.where_outlives.iter().any(OutlivesPredicate::has_escaped_regions) {
            diagnostics.push(SignatureDiagnostic { code: "G4199", message: "nominal predicate contains an escaped lifetime".into() });
        }
    }
}
