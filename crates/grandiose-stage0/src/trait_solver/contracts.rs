use super::*;
use crate::AssociatedItemContract;

impl TraitSolver {
    pub(crate) fn callable_prerequisites_proven(&mut self, signature: &crate::CallableSignature) -> bool {
        let contract = signature.prerequisites();
        self.contract_domains_proven(&contract)
            && self.contract_proven(&contract, &Arc::clone(&self.lexical_assumptions), 0)
            && signature.universal_bounds.iter().all(|bound| self.proves_universal(bound))
    }
    pub(crate) fn outlives_proven(&mut self, predicate: &crate::OutlivesPredicate) -> bool {
        if predicate.proven_by(&self.lexical_outlives) {
            return true;
        }
        let normalize = |solver: &mut Self, predicate: &crate::OutlivesPredicate| match predicate {
            crate::OutlivesPredicate::Type { subject, lifetime } => solver
                .normalize_type(subject.clone())
                .ok()
                .map(|subject| crate::OutlivesPredicate::Type {
                    subject,
                    lifetime: *lifetime,
                }),
            value => Some(value.clone()),
        };
        let Some(predicate) = normalize(self, predicate) else {
            return false;
        };
        let assumptions = Arc::clone(&self.lexical_outlives);
        let assumptions = assumptions
            .iter()
            .filter_map(|predicate| normalize(self, predicate))
            .collect::<Vec<_>>();
        predicate.proven_by(&assumptions)
    }

    pub(crate) fn contract_domains_proven(&mut self, contract: &AssociatedItemContract) -> bool {
        for (subject, relation) in &contract.where_bounds {
            if !self.type_domains_proven(subject)
                || !relation
                    .arguments
                    .iter()
                    .all(|argument| self.argument_domains_proven(argument))
            {
                return false;
            }
        }
        for bound in &contract.where_outlives {
            if let crate::OutlivesPredicate::Type { subject, .. } = bound {
                if !self.type_domains_proven(subject) {
                    return false;
                }
            }
        }
        for binding in &contract.type_bindings {
            if !self.type_domains_proven(&binding.value)
                || !self.type_domains_proven(&binding.subject)
                || !binding
                    .relation
                    .arguments
                    .iter()
                    .chain(&binding.item_arguments)
                    .all(|argument| self.argument_domains_proven(argument))
                || (!(is_intrinsic_callable_trait(&binding.relation)
                    || is_intrinsic_runs_in_trait(&binding.relation))
                    && !self.projection_domain_proven(
                        &TraitGoal {
                            subject: binding.subject.clone(),
                            relation: binding.relation.clone(),
                        },
                        &binding.name,
                        &binding.item_arguments,
                    ))
            {
                return false;
            }
        }
        for binding in &contract.effect_bindings {
            if !self.row_domains_proven(&binding.value)
                || !self.type_domains_proven(&binding.subject)
                || !binding
                    .relation
                    .arguments
                    .iter()
                    .chain(&binding.item_arguments)
                    .all(|argument| self.argument_domains_proven(argument))
                || (!(is_intrinsic_callable_trait(&binding.relation)
                    || is_intrinsic_runs_in_trait(&binding.relation))
                    && !self.projection_domain_proven(
                        &TraitGoal {
                            subject: binding.subject.clone(),
                            relation: binding.relation.clone(),
                        },
                        &binding.name,
                        &binding.item_arguments,
                    ))
            {
                return false;
            }
        }
        true
    }

    /// Well-formed input/self types include the reference requirements of
    /// their instantiated nominal fields (for example `Iter<'a,T>` stores
    /// `&'a T`). Keep those facts scoped to the caller that owns the type.
    pub(crate) fn implied_outlives(
        &self,
        types: impl IntoIterator<Item = Type>,
    ) -> Vec<crate::OutlivesPredicate> {
        let mut pending = types
            .into_iter()
            .map(|ty| (ty, 0u32, Vec::<DefKey>::new()))
            .collect::<Vec<_>>();
        let mut seen = BTreeSet::new();
        let mut facts = vec![];
        while let Some((ty, depth, owners)) = pending.pop() {
            if depth >= self.limits.max_depth || seen.len() >= 4096 {
                break;
            }
            if !seen.insert(canonical_type_encoding(&ty)) {
                continue;
            }
            let children = match ty {
                Type::Reference {
                    lifetime, referent, ..
                } => {
                    facts.push(crate::OutlivesPredicate::Type {
                        subject: (*referent).clone(),
                        lifetime,
                    });
                    vec![*referent]
                }
                Type::Nominal {
                    definition,
                    arguments,
                } => {
                    // A recursive nominal can grow its generic argument on
                    // every field edge. Do not expand that declaration again
                    // on the same path before layout validation rejects it.
                    if !owners.contains(&definition) {
                        let mut nested = owners.clone();
                        nested.push(definition);
                        pending.extend(
                            self.nominal_structural_fields(definition, &arguments)
                                .unwrap_or_default()
                                .into_iter()
                                .map(|field| (field, depth + 1, nested.clone())),
                        );
                    }
                    arguments
                        .into_iter()
                        .filter_map(|argument| match argument {
                            GenericArgument::Type(ty) => Some(ty),
                            _ => None,
                        })
                        .collect()
                }
                Type::Tuple(types) => types,
                Type::Array(ty) | Type::FixedArray { element: ty, .. }
                | Type::RawPointer { pointee: ty, .. } => vec![*ty],
                _ => vec![],
            };
            pending.extend(
                children
                    .into_iter()
                    .map(|ty| (ty, depth + 1, owners.clone())),
            );
        }
        facts
    }

    pub(crate) fn type_domains_proven(&mut self, ty: &Type) -> bool {
        match ty {
            Type::FixedArray { element, length } =>
                self.type_domains_proven(element) && self.argument_domains_proven(length),
            Type::Projection {
                subject,
                trait_definition,
                trait_arguments,
                name,
                item_arguments,
                ..
            } => {
                self.type_domains_proven(subject)
                    && trait_arguments
                        .iter()
                        .chain(item_arguments)
                        .all(|argument| self.argument_domains_proven(argument))
                    && self.projection_domain_proven(
                        &TraitGoal {
                            subject: (**subject).clone(),
                            relation: ElaboratedTraitReference {
                                definition: *trait_definition,
                                arguments: trait_arguments.clone(),
                            },
                        },
                        name,
                        item_arguments,
                    )
            }
            Type::Nominal { definition, arguments } => {
                if !arguments.iter().all(|argument| self.argument_domains_proven(argument)) { return false; }
                let Some(ElaboratedHeader::Nominal { generic_kinds, contract, universal_bounds, .. }) = self.definitions.get(definition) else {
                    return true; // Intrinsic nominal families have separate validators.
                };
                if !generic_arguments_match_kinds(arguments, generic_kinds) { return false; }
                if *contract == AssociatedItemContract::default() && universal_bounds.is_empty() { return true; }
                let contract = contract.instantiate(arguments, ty);
                let universal = universal_bounds.iter().map(|bound| bound.instantiate(arguments)).collect::<Vec<_>>();
                let mut bytes = b"nominal-domain-v1".to_vec();
                bytes.extend_from_slice(&canonical_type_encoding(ty));
                self.instantiated_domain_proven(Digest::of_bytes(&bytes), &contract, &universal)
            }
            Type::Tuple(types) => types.iter().all(|ty| self.type_domains_proven(ty)),
            Type::Array(ty)
            | Type::Reference { referent: ty, .. }
            | Type::RawPointer { pointee: ty, .. } => self.type_domains_proven(ty),
            Type::Callable {
                parameters,
                result,
                effects,
                ..
            } => {
                let mut scoped = self.fresh_query();
                let mut outlives = (*scoped.lexical_outlives).clone();
                for parameter in parameters {
                    crate::OutlivesPredicate::implied_by_type(parameter, &mut outlives);
                }
                scoped.set_outlives_assumptions(outlives);
                parameters.iter().all(|ty| scoped.type_domains_proven(ty))
                    && scoped.type_domains_proven(result)
                    && scoped.row_domains_proven(effects)
            }
            _ => true,
        }
    }

    pub(crate) fn argument_domains_proven(&mut self, argument: &GenericArgument) -> bool {
        match argument {
            GenericArgument::Type(ty) => self.type_domains_proven(ty),
            GenericArgument::EffectRow(row) => self.row_domains_proven(row),
            GenericArgument::ConstProjection {
                subject,
                trait_arguments,
                ..
            } => {
                self.type_domains_proven(subject)
                    && trait_arguments
                        .iter()
                        .all(|argument| self.argument_domains_proven(argument))
            }
            _ => true,
        }
    }

    pub(crate) fn row_domains_proven(&mut self, row: &EffectRow) -> bool {
        row.effects.iter().all(|effect| self.effect_domain_proven(effect)) && row.projections.iter().all(|projection| {
            self.type_domains_proven(&projection.subject)
                && projection
                    .trait_arguments
                    .iter()
                    .chain(&projection.item_arguments)
                    .all(|argument| self.argument_domains_proven(argument))
                && self.projection_domain_proven(
                    &TraitGoal {
                        subject: (*projection.subject).clone(),
                        relation: ElaboratedTraitReference {
                            definition: projection.trait_definition,
                            arguments: projection.trait_arguments.clone(),
                        },
                    },
                    &projection.name,
                    &projection.item_arguments,
                )
        })
    }

    pub(crate) fn effect_domain_proven(&mut self, effect: &crate::EffectInstance) -> bool {
        if !effect.arguments.iter().all(|argument| self.argument_domains_proven(argument)) { return false; }
        let Some(ElaboratedHeader::Effect(declaration)) = self.definitions.get(&effect.definition) else {
            return false;
        };
        if !generic_arguments_match_kinds(&effect.arguments, &declaration.generic_kinds) { return false; }
        if declaration.contract == AssociatedItemContract::default() && declaration.universal_bounds.is_empty() { return true; }
        let contract = declaration.contract.instantiate(&effect.arguments, &Type::Unit);
        let universal = declaration.universal_bounds.iter().map(|bound| bound.instantiate(&effect.arguments)).collect::<Vec<_>>();
        let mut bytes = b"effect-domain-v1".to_vec();
        bytes.extend_from_slice(&effect.definition.0.as_bytes());
        bytes.extend_from_slice(&canonical_generic_arguments_encoding(&effect.arguments));
        self.instantiated_domain_proven(Digest::of_bytes(&bytes), &contract, &universal)
    }

    /// Nominal values and effect families admit applications under the same
    /// predicate rule. Recursive domain obligations consume the same query
    /// budget and never establish their own prerequisites.
    fn instantiated_domain_proven(&mut self, key: Digest, contract: &AssociatedItemContract, universal: &[crate::QuantifiedWhereBound]) -> bool {
        if self.steps >= self.limits.max_steps || self.active_domains.contains(&key)
            || self.active_domains.len() >= self.limits.max_depth as usize { return false; }
        self.steps += 1;
        self.active_domains.push(key);
        let proven = self.contract_domains_proven(contract)
            && self.contract_proven(contract, &Arc::clone(&self.lexical_assumptions), self.active_domains.len() as u32)
            && universal.iter().all(|bound| self.proves_universal(bound));
        self.active_domains.pop();
        proven
    }

    pub(crate) fn associated_contract(
        &self,
        goal: &TraitGoal,
        name: &str,
        arguments: &[GenericArgument],
    ) -> Option<(AssociatedItemContract, Vec<ElaboratedTraitReference>)> {
        let kind = if self
            .find_associated_item_goal(goal, name, AssociatedItemKind::Type, &mut vec![])
            .matches_found()
        {
            AssociatedItemKind::Type
        } else {
            AssociatedItemKind::EffectRow
        };
        let SupertraitLookup::Found(owner) =
            self.find_associated_item_goal(goal, name, kind, &mut vec![])
        else {
            return None;
        };
        let declaration = self
            .traits
            .get(&owner.relation.definition)?
            .associated_types
            .get(name)?;
        if !generic_arguments_match_kinds(arguments, &declaration.generic_kinds) {
            return None;
        }
        let mut substitution = ImplementationSubstitution::default();
        substitution
            .types
            .insert(TRAIT_SELF_GENERIC, owner.subject.clone());
        for (index, argument) in owner
            .relation
            .arguments
            .iter()
            .chain(arguments)
            .cloned()
            .enumerate()
        {
            install_item_argument(&mut substitution, index as u32, argument);
        }
        Some((
            declaration
                .domain
                .map_terms(|argument| substitute_generic_argument(&argument, &substitution)),
            declaration
                .bounds
                .iter()
                .map(|bound| substitute_relation(bound, &substitution))
                .collect(),
        ))
    }

    pub(crate) fn contract_proven(
        &mut self,
        domain: &AssociatedItemContract,
        assumptions: &[TraitGoal],
        depth: u32,
    ) -> bool {
        if depth >= self.limits.max_depth {
            return false;
        }
        // A conjunction has no source-order dependency. Register the
        // compiler-branded callable subjects through the existing evidence
        // producer before asking an Environment prerequisite, even when
        // that prerequisite was written before Fn/RunsIn.
        for (subject, _) in &domain.where_bounds {
            self.remember_callable_environments(subject);
        }
        if domain
            .where_outlives
            .iter()
            .any(|bound| !self.outlives_proven(bound))
        {
            return false;
        }
        for (subject, relation) in &domain.where_bounds {
            if !matches!(
                self.solve_at_with_assumptions(
                    TraitGoal {
                        subject: subject.clone(),
                        relation: relation.clone()
                    },
                    depth + 1,
                    false,
                    assumptions,
                    true
                ),
                TraitAnswerIndex::Proven(_)
            ) {
                return false;
            }
        }
        for binding in &domain.type_bindings {
            let projection = Type::Projection {
                subject: Box::new(binding.subject.clone()),
                trait_definition: binding.relation.definition,
                trait_arguments: binding.relation.arguments.clone(),
                name: binding.name.clone(),
                item_generic_kinds: binding.item_generic_kinds.clone(),
                item_arguments: binding.item_arguments.clone(),
            };
            if self.normalize_type(projection).ok()
                != self.normalize_type(binding.value.clone()).ok()
                || self.normalize_type(binding.value.clone()).is_err()
            {
                return false;
            }
        }
        for binding in &domain.effect_bindings {
            let projection = EffectRow {
                effects: Default::default(),
                tails: Default::default(),
                projections: vec![crate::EffectRowProjection {
                    subject: Box::new(binding.subject.clone()),
                    trait_definition: binding.relation.definition,
                    trait_arguments: binding.relation.arguments.clone(),
                    name: binding.name.clone(),
                    item_generic_kinds: binding.item_generic_kinds.clone(),
                    item_arguments: binding.item_arguments.clone(),
                }],
            };
            if self.normalize_effect_row(projection).ok()
                != self.normalize_effect_row(binding.value.clone()).ok()
                || self.normalize_effect_row(binding.value.clone()).is_err()
            {
                return false;
            }
        }
        true
    }

    pub(crate) fn projection_domain_proven(
        &mut self,
        goal: &TraitGoal,
        name: &str,
        arguments: &[GenericArgument],
    ) -> bool {
        if is_intrinsic_callable_trait(&goal.relation) || is_intrinsic_runs_in_trait(&goal.relation)
        {
            return arguments.is_empty() && matches!(name, "Output" | "Effects" | "After");
        }
        let Some((domain, _)) = self.associated_contract(goal, name, arguments) else {
            return false;
        };
        let key = associated_projection_key(goal, name, arguments);
        if self.active_domains.contains(&key)
            || self.active_domains.len() >= self.limits.max_depth as usize
        {
            return false;
        }
        self.active_domains.push(key);
        let proven = self.contract_proven(
            &domain,
            &Arc::clone(&self.lexical_assumptions),
            self.active_domains.len() as u32,
        );
        self.active_domains.pop();
        proven
    }

    pub(super) fn associated_result_proves(
        &mut self,
        goal: &TraitGoal,
        assumptions: &[TraitGoal],
        depth: u32,
    ) -> bool {
        let Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_arguments,
            ..
        } = &goal.subject
        else {
            return false;
        };
        let owner = TraitGoal {
            subject: (**subject).clone(),
            relation: ElaboratedTraitReference {
                definition: *trait_definition,
                arguments: trait_arguments.clone(),
            },
        };
        let Some((domain, bounds)) = self.associated_contract(&owner, name, item_arguments) else {
            return false;
        };
        let guarantees = bounds
            .into_iter()
            .map(|relation| TraitGoal {
                subject: goal.subject.clone(),
                relation,
            })
            .collect::<Vec<_>>();
        if !self.assumption_proves(goal, &guarantees) {
            return false;
        }
        let key = associated_projection_key(&owner, name, item_arguments);
        if self.active_domains.contains(&key)
            || self.active_domains.len() >= self.limits.max_depth as usize
        {
            return false;
        }
        self.active_domains.push(key);
        let proven = matches!(
            self.solve_at_with_assumptions(owner, depth + 1, false, assumptions, true),
            TraitAnswerIndex::Proven(_)
        ) && self.contract_proven(&domain, assumptions, depth + 1);
        self.active_domains.pop();
        proven
    }
}

impl<T> SupertraitLookup<T> {
    fn matches_found(&self) -> bool {
        matches!(self, Self::Found(_))
    }
}
