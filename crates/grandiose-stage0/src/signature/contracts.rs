use super::*;

impl CallableSignature {
    pub(crate) fn outlives_environment(&self) -> Vec<OutlivesPredicate> {
        let mut facts = self.where_outlives.clone();
        for parameter in &self.parameters {
            OutlivesPredicate::implied_by_type(parameter, &mut facts);
        }
        facts
    }
}

/// Outlives is directional region evidence, never an ordinary source trait.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OutlivesPredicate {
    Type { subject: Type, lifetime: Lifetime },
    Region { longer: Lifetime, shorter: Lifetime },
}

impl OutlivesPredicate {
    pub(crate) fn has_escaped_regions(&self) -> bool {
        let mut invalid = false;
        self.map_terms(|argument| {
            invalid |=
                crate::core::generic_argument_contains_out_of_scope_bound_lifetime(&argument, &[])
                    || matches!(argument, GenericArgument::Lifetime(Lifetime::Elided));
            argument
        });
        invalid
    }
    /// Reference inputs are well formed in the declaration's rigid scope.
    /// Their referents must remain valid for the reference's whole region.
    pub(crate) fn implied_by_type(ty: &Type, output: &mut Vec<Self>) {
        match ty {
            Type::Reference {
                lifetime, referent, ..
            } => {
                output.push(Self::Type {
                    subject: (**referent).clone(),
                    lifetime: *lifetime,
                });
                Self::implied_by_type(referent, output);
            }
            Type::Nominal { arguments, .. } => {
                for argument in arguments {
                    if let GenericArgument::Type(ty) = argument {
                        Self::implied_by_type(ty, output);
                    }
                }
            }
            Type::Tuple(types) => {
                for ty in types {
                    Self::implied_by_type(ty, output);
                }
            }
            Type::Array(ty) | Type::FixedArray { element: ty, .. } => Self::implied_by_type(ty, output),
            // Callable inputs live in their own binder scope. Never export
            // their well-formedness requirements into the containing scope.
            _ => {}
        }
    }

    /// Read-only entailment. In particular, this never unifies a rigid region
    /// with an inference hole or assigns an outer variable a newer universe.
    pub fn proven_by(&self, assumptions: &[Self]) -> bool {
        let mut facts = assumptions.to_vec();
        let mut position = 0;
        while position < facts.len() {
            if position > 4096 {
                return false;
            }
            let fact = facts[position].clone();
            position += 1;
            if let Self::Type { subject, lifetime } = fact {
                for child in Self::components(&subject, lifetime).unwrap_or_default() {
                    if !facts.contains(&child) {
                        facts.push(child);
                    }
                }
            }
        }
        self.proven_from_closed_facts(&facts, 0)
    }

    fn proven_from_closed_facts(&self, facts: &[Self], depth: usize) -> bool {
        if depth > 128 {
            return false;
        }
        match self {
            Self::Region { longer, shorter } => {
                if longer == shorter || *longer == Lifetime::Static {
                    return true;
                }
                let mut pending = vec![*longer];
                let mut seen = vec![];
                while let Some(region) = pending.pop() {
                    if seen.contains(&region) {
                        continue;
                    }
                    seen.push(region);
                    for fact in facts {
                        if let Self::Region {
                            longer,
                            shorter: next,
                        } = fact
                        {
                            if *longer == region {
                                if next == shorter {
                                    return true;
                                }
                                pending.push(*next);
                            }
                        }
                    }
                }
                false
            }
            Self::Type { subject, lifetime } => {
                if facts.iter().any(|fact| matches!(fact, Self::Type { subject: known, lifetime: region }
                    if known == subject && Self::Region { longer: *region, shorter: *lifetime }.proven_from_closed_facts(facts, depth + 1))) {
                    return true;
                }
                Self::components(subject, *lifetime).is_some_and(|parts| {
                    parts
                        .iter()
                        .all(|part| part.proven_from_closed_facts(facts, depth + 1))
                })
            }
        }
    }

    fn components(subject: &Type, lifetime: Lifetime) -> Option<Vec<Self>> {
        let value = |subject: &Type| Self::Type {
            subject: subject.clone(),
            lifetime,
        };
        let argument = |argument: &GenericArgument| match argument {
            GenericArgument::Type(ty) => Some(value(ty)),
            GenericArgument::Lifetime(longer) => Some(Self::Region {
                longer: *longer,
                shorter: lifetime,
            }),
            // Effect identities do not denote stored borrowed values.
            _ => None,
        };
        Some(match subject {
            Type::Unit | Type::Never | Type::Scalar(_) | Type::StaticData { .. } => vec![],
            Type::Tuple(types) => types.iter().map(value).collect(),
            Type::Array(ty) | Type::FixedArray { element: ty, .. }
            | Type::RawPointer { pointee: ty, .. } => vec![value(ty)],
            Type::Reference {
                lifetime: longer,
                referent,
                ..
            } => vec![
                Self::Region {
                    longer: *longer,
                    shorter: lifetime,
                },
                value(referent),
            ],
            Type::Nominal { arguments, .. } => arguments.iter().filter_map(argument).collect(),
            _ => return None,
        })
    }

    pub(crate) fn map_terms(
        &self,
        mut map: impl FnMut(GenericArgument) -> GenericArgument,
    ) -> Self {
        let mut region = |lifetime| match map(GenericArgument::Lifetime(lifetime)) {
            GenericArgument::Lifetime(value) => value,
            _ => unreachable!("region substitution must preserve kind"),
        };
        match self {
            Self::Region { longer, shorter } => Self::Region {
                longer: region(*longer),
                shorter: region(*shorter),
            },
            Self::Type { subject, lifetime } => {
                let lifetime = region(*lifetime);
                let GenericArgument::Type(subject) = map(GenericArgument::Type(subject.clone()))
                else {
                    unreachable!("type substitution must preserve kind");
                };
                Self::Type { subject, lifetime }
            }
        }
    }
}

/// The domain on which an associated item may be selected. Result bounds are
/// retained separately: they are consequences of selection, not prerequisites.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct AssociatedItemContract {
    pub where_bounds: Vec<(Type, ElaboratedTraitReference)>,
    pub where_outlives: Vec<OutlivesPredicate>,
    pub type_bindings: Vec<ElaboratedAssociatedTypeBinding>,
    pub effect_bindings: Vec<ElaboratedAssociatedEffectBinding>,
}

impl AssociatedItemContract {
    pub(crate) fn instantiate(&self, arguments: &[GenericArgument], self_ty: &Type) -> Self {
        self.map_terms(|argument| {
            replace_trait_self_generic_argument(
                substitute_alias_generic_identity_argument(argument, arguments),
                self_ty,
            )
        })
    }
    pub(crate) fn map_terms(
        &self,
        mut map: impl FnMut(GenericArgument) -> GenericArgument,
    ) -> Self {
        // Reuse the quantified predicate's kind-preserving walk; there is no
        // binder opening here, only substitution in the item's owner scope.
        let mapped = self
            .where_bounds
            .iter()
            .map(|(subject, relation)| {
                QuantifiedWhereBound {
                    lifetime_binders: 0,
                    subject: subject.clone(),
                    relation: relation.clone(),
                    type_bindings: vec![],
                    effect_bindings: vec![],
                }
                .map_terms(&mut map)
            })
            .collect::<Vec<_>>();
        let carrier = QuantifiedWhereBound {
            lifetime_binders: 0,
            subject: Type::Unit,
            relation: ElaboratedTraitReference {
                definition: intrinsic_callable_trait_definition(),
                arguments: vec![],
            },
            type_bindings: self.type_bindings.clone(),
            effect_bindings: self.effect_bindings.clone(),
        }
        .map_terms(&mut map);
        Self {
            where_bounds: mapped
                .into_iter()
                .map(|bound| (bound.subject, bound.relation))
                .collect(),
            where_outlives: self
                .where_outlives
                .iter()
                .map(|bound| bound.map_terms(&mut map))
                .collect(),
            type_bindings: carrier.type_bindings,
            effect_bindings: carrier.effect_bindings,
        }
    }
}

impl ElaboratedInterface {
    pub(super) fn validate_noncallable_projection_domains(
        &self,
        header: &ElaboratedHeader,
        solver: &crate::TraitSolver,
        diagnostics: &mut Vec<SignatureDiagnostic>,
    ) {
        let mut types = vec![];
        match header {
            ElaboratedHeader::Alias { target, .. } => types.push(target.clone()),
            ElaboratedHeader::Constant(Some(ty))
            | ElaboratedHeader::ValueInitializer { ty: Some(ty), .. } => types.push(ty.clone()),
            // Nominal fields are checked with their declaration contract by
            // validate_nominal_projection_obligations, not an empty scope.
            ElaboratedHeader::Nominal { .. } => return,
            ElaboratedHeader::Effect(effect) => {
                for operation in &effect.operations {
                    let mut scoped = solver.fresh_query();
                    scoped.set_outlives_assumptions(
                        scoped.implied_outlives(operation.parameters.clone()),
                    );
                    if !operation
                        .parameters
                        .iter()
                        .chain(std::iter::once(&operation.result))
                        .all(|ty| scoped.type_domains_proven(ty))
                    {
                        diagnostics.push(SignatureDiagnostic { code: "G4303", message: "effect operation projection does not establish its declared domain requirements".into() });
                    }
                }
            }
            _ => {}
        }
        if types.is_empty() {
            return;
        }
        let mut scoped = solver.fresh_query();
        if !types.iter().all(|ty| scoped.type_domains_proven(ty)) {
            diagnostics.push(SignatureDiagnostic { code: "G4303", message: "type declaration projection does not establish its declared domain requirements".into() });
        }
    }

    pub(super) fn validate_associated_contracts(&mut self) {
        use crate::{TraitAnswer, TraitGoal, TraitSolver};
        let mut diagnostics = vec![];
        let solver = TraitSolver::new(self);
        for (definition, header) in &self.definitions {
            if let ElaboratedHeader::Trait(trait_header) = header {
                let self_ty = Type::Generic(TRAIT_SELF_GENERIC);
                let self_goal = TraitGoal {
                    subject: self_ty.clone(),
                    relation: ElaboratedTraitReference {
                        definition: *definition,
                        arguments: nominal_identity_arguments(&trait_header.generic_kinds),
                    },
                };
                for (name, item) in &trait_header.associated_types {
                    if item
                        .domain
                        .where_outlives
                        .iter()
                        .any(OutlivesPredicate::has_escaped_regions)
                    {
                        diagnostics.push(SignatureDiagnostic { code: "G4306", message: format!("associated item `{name}` contains an out-of-scope outlives predicate") });
                    }
                    let mut scoped = solver.fresh_query();
                    let assumptions = std::iter::once(self_goal.clone())
                        .chain(item.domain.where_bounds.iter().map(|(subject, relation)| {
                            TraitGoal {
                                subject: subject.clone(),
                                relation: relation.clone(),
                            }
                        }))
                        .collect::<Vec<_>>();
                    scoped.set_lexical_assumptions(assumptions.clone());
                    scoped.set_outlives_assumptions(item.domain.where_outlives.clone());
                    scoped.set_associated_bindings(
                        item.domain.type_bindings.clone(),
                        item.domain.effect_bindings.clone(),
                    );
                    if !scoped.contract_domains_proven(&item.domain) {
                        diagnostics.push(SignatureDiagnostic { code: "G4303", message: format!("associated item `{name}` domain contains a projection without its required domain evidence") });
                    }
                    if let Some(row) = &item.effect_row_default {
                        if !scoped.row_domains_proven(row) {
                            diagnostics.push(SignatureDiagnostic { code: "G4303", message: format!("associated effect default `{name}` contains a projection without its required domain evidence") });
                        }
                    }
                    let Some(value) = &item.default else {
                        continue;
                    };
                    let mut well_formedness = vec![];
                    OutlivesPredicate::implied_by_type(value, &mut well_formedness);
                    if well_formedness
                        .iter()
                        .any(|bound| !scoped.outlives_proven(bound))
                        || !scoped.type_domains_proven(value)
                    {
                        diagnostics.push(SignatureDiagnostic { code: "G4305", message: format!("default associated type `{name}` is not well formed throughout its declared domain") });
                    }
                    for bound in &item.bounds {
                        if !matches!(
                            scoped.solve_with_assumptions(
                                TraitGoal {
                                    subject: value.clone(),
                                    relation: bound.clone()
                                },
                                &assumptions
                            ),
                            TraitAnswer::Proven { .. }
                        ) {
                            diagnostics.push(SignatureDiagnostic { code: "G4302", message: format!("default associated type `{name}` does not establish its declared result bound") });
                        }
                    }
                }
            }
            let ElaboratedHeader::Implementation(implementation) = header else {
                continue;
            };
            if implementation
                .where_outlives
                .iter()
                .any(OutlivesPredicate::has_escaped_regions)
            {
                diagnostics.push(SignatureDiagnostic {
                    code: "G4306",
                    message: "implementation contains an out-of-scope outlives predicate".into(),
                });
            }
            if implementation.negative {
                continue;
            }
            let Some(ElaboratedHeader::Trait(trait_header)) =
                self.definitions.get(&implementation.relation.definition)
            else {
                continue;
            };
            let implementation_domain = AssociatedItemContract {
                where_bounds: implementation.where_bounds.clone(),
                where_outlives: implementation.where_outlives.clone(),
                type_bindings: implementation.where_associated_type_bindings.clone(),
                effect_bindings: implementation.where_associated_effect_bindings.clone(),
            };
            let mut implementation_solver = solver.fresh_query();
            implementation_solver.set_universal_assumptions(implementation.universal_bounds.clone());
            implementation_solver.set_lexical_assumptions(
                implementation
                    .where_bounds
                    .iter()
                    .map(|(subject, relation)| TraitGoal {
                        subject: subject.clone(),
                        relation: relation.clone(),
                    })
                    .collect(),
            );
            implementation_solver.set_outlives_assumptions(
                implementation
                    .where_outlives
                    .iter()
                    .cloned()
                    .chain(solver.implied_outlives(std::iter::once(implementation.self_ty.clone())))
                    .collect(),
            );
            implementation_solver.set_associated_bindings(
                implementation.where_associated_type_bindings.clone(),
                implementation.where_associated_effect_bindings.clone(),
            );
            if !implementation_solver.contract_domains_proven(&implementation_domain)
                || !implementation_solver.type_domains_proven(&implementation.self_ty)
                || !implementation
                    .relation
                    .arguments
                    .iter()
                    .all(|argument| implementation_solver.argument_domains_proven(argument))
            {
                diagnostics.push(SignatureDiagnostic {
                    code: "G4303",
                    message:
                        "implementation contains a projection without its required domain evidence"
                            .into(),
                });
            }
            for (name, declaration) in &trait_header.associated_types {
                let mut arguments = implementation.relation.arguments.clone();
                arguments.extend(
                    nominal_identity_arguments(&declaration.generic_kinds)
                        .into_iter()
                        .map(|argument| offset_generic_argument(argument, implementation.generics)),
                );
                let required = declaration
                    .domain
                    .instantiate(&arguments, &implementation.self_ty);
                let assumptions = implementation
                    .where_bounds
                    .iter()
                    .chain(&required.where_bounds)
                    .map(|(subject, relation)| TraitGoal {
                        subject: subject.clone(),
                        relation: relation.clone(),
                    })
                    .collect::<Vec<_>>();
                let mut outlives = implementation.where_outlives.clone();
                outlives.extend(required.where_outlives.clone());
                outlives.extend(
                    solver.implied_outlives(std::iter::once(implementation.self_ty.clone())),
                );
                let mut scoped = solver.fresh_query();
                scoped.set_universal_assumptions(implementation.universal_bounds.clone());
                scoped.set_lexical_assumptions(assumptions.clone());
                scoped.set_outlives_assumptions(outlives.clone());
                scoped.set_associated_bindings(
                    implementation
                        .where_associated_type_bindings
                        .iter()
                        .chain(&required.type_bindings)
                        .cloned()
                        .collect(),
                    implementation
                        .where_associated_effect_bindings
                        .iter()
                        .chain(&required.effect_bindings)
                        .cloned()
                        .collect(),
                );
                let provided_domain = implementation
                    .associated_types
                    .get(name)
                    .map(|item| &item.domain)
                    .or_else(|| {
                        implementation
                            .associated_effect_rows
                            .get(name)
                            .map(|item| &item.domain)
                    });
                if let Some(provided) = provided_domain {
                    if provided
                        .where_outlives
                        .iter()
                        .any(OutlivesPredicate::has_escaped_regions)
                    {
                        diagnostics.push(SignatureDiagnostic { code: "G4306", message: format!("associated item `{name}` contains an out-of-scope outlives predicate") });
                    }
                    if !scoped.contract_proven(provided, &assumptions, 0) {
                        diagnostics.push(SignatureDiagnostic { code: "G4301", message: format!("associated item `{name}` introduces stronger requirements than its trait declaration") });
                    }
                }
                if let Some(item) = implementation.associated_effect_rows.get(name) {
                    if !scoped.row_domains_proven(&item.value) {
                        diagnostics.push(SignatureDiagnostic { code: "G4303", message: format!("associated effect `{name}` contains a projection without its required domain evidence") });
                    }
                }
                let value = implementation
                    .associated_types
                    .get(name)
                    .map(|item| item.value.clone())
                    .or_else(|| {
                        declaration.default.clone().map(|value| {
                            replace_trait_self_type(
                                substitute_alias_generic_identity(value, &arguments),
                                &implementation.self_ty,
                            )
                        })
                    });
                let Some(value) = value else {
                    continue;
                };
                let mut well_formedness = vec![];
                OutlivesPredicate::implied_by_type(&value, &mut well_formedness);
                if well_formedness
                    .iter()
                    .any(|bound| !scoped.outlives_proven(bound))
                    || !scoped.type_domains_proven(&value)
                {
                    diagnostics.push(SignatureDiagnostic { code: "G4305", message: format!("associated type `{name}` is not well formed throughout its declared domain") });
                }
                for bound in &declaration.bounds {
                    let relation = replace_trait_self_trait_reference(
                        substitute_trait_reference(bound, &arguments),
                        &implementation.self_ty,
                    );
                    if !matches!(
                        scoped.solve_with_assumptions(
                            TraitGoal {
                                subject: value.clone(),
                                relation
                            },
                            &assumptions
                        ),
                        TraitAnswer::Proven { .. }
                    ) {
                        diagnostics.push(SignatureDiagnostic { code: "G4302", message: format!("associated type `{name}` does not establish its declared result bound") });
                    }
                }
            }
        }
        self.diagnostics.extend(diagnostics);
    }
}

fn offset_generic_argument(value: GenericArgument, offset: u32) -> GenericArgument {
    match value {
        GenericArgument::Type(Type::Generic(index)) => {
            GenericArgument::Type(Type::Generic(index + offset))
        }
        GenericArgument::Lifetime(Lifetime::Generic(index)) => {
            GenericArgument::Lifetime(Lifetime::Generic(index + offset))
        }
        GenericArgument::ConstGeneric { index, kind } => GenericArgument::ConstGeneric {
            index: index + offset,
            kind,
        },
        GenericArgument::EffectRow(row) => GenericArgument::EffectRow(EffectRow {
            tails: row
                .tails
                .into_iter()
                .map(|tail| match tail {
                    EffectTail::Generic(index) => EffectTail::Generic(index + offset),
                    other => other,
                })
                .collect(),
            ..row
        }),
        value => value,
    }
}
