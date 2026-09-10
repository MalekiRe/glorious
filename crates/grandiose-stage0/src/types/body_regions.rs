//! Closed existential region constraints, produced by body inference.
//!
//! An inferred region is not a new universal assumption. A set of directed
//! constraints has a solution only if every induced relation between rigid
//! boundaries already follows from the lexical environment. Internal nodes
//! then denote regions between those boundaries; no equality or `'static`
//! fallback is needed. The same immutable constraints travel with frozen Core
//! and with callable captures that retain their existential regions.

use super::{BodyRegion, GenericArgument, Lifetime, Type};
use crate::OutlivesPredicate;
use std::collections::{BTreeMap, BTreeSet};

const LIMIT: usize = 4096;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BodyRegionConstraints {
    regions: BTreeSet<BodyRegion>,
    /// Storage extents are rigid upper boundaries, not holes that may be
    /// solved to a caller region or to static. Loan regions lie below them.
    local_storage: BTreeSet<BodyRegion>,
    facts: Vec<OutlivesPredicate>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ConstraintFailure {
    LocalStorage,
    Unsatisfied,
    Limit,
}

impl BodyRegionConstraints {
    pub(super) fn solve(
        regions: BTreeSet<BodyRegion>,
        local_storage: BTreeSet<BodyRegion>,
        requirements: Vec<OutlivesPredicate>,
        ambient: &[OutlivesPredicate],
    ) -> Result<(Self, BTreeMap<BodyRegion, Lifetime>), ConstraintFailure> {
        let facts = leaves(&requirements).ok_or(ConstraintFailure::Limit)?;
        let candidate = Self {
            regions,
            local_storage,
            facts,
        };
        candidate.check_in(ambient)?;

        // Equalities implied by two directed paths share a representative.
        // In particular X:static implies X=static, but an unrelated hole
        // does not acquire that lifetime. Named boundaries are never rebound.
        let mut evidence = ambient.to_vec();
        evidence.extend(candidate.facts.clone());
        let mut replacements = BTreeMap::new();
        for component in equivalent_regions(&evidence)? {
            let replacement = if component.contains(&Lifetime::Static) {
                Lifetime::Static
            } else {
                component
                    .iter()
                    .copied()
                    .find(|lifetime| !candidate.owns(*lifetime))
                    .unwrap_or(component[0])
            };
            for lifetime in component {
                if lifetime != replacement
                    && candidate.owns(lifetime)
                    && let Lifetime::Inferred(region) = lifetime
                {
                    replacements.insert(region, replacement);
                }
            }
        }
        let value = candidate.map_terms(|argument| {
            super::regions::map_argument_regions(argument, &mut |lifetime, _| {
                Some(match lifetime {
                    Lifetime::Inferred(region) => {
                        replacements.get(&region).copied().unwrap_or(lifetime)
                    }
                    _ => lifetime,
                })
            })
            .expect("closed region replacement preserves binder depth")
        });
        Ok((value, replacements))
    }

    fn owns(&self, lifetime: Lifetime) -> bool {
        matches!(lifetime, Lifetime::Inferred(region) if self.regions.contains(&region) && !self.local_storage.contains(&region))
    }

    /// Check rigid-boundary consistency independently of the inference
    /// producer. Following only internal nodes suffices: once a path reaches
    /// a rigid boundary, its remainder has its own checked rigid premise.
    pub(crate) fn valid_in(&self, ambient: &[OutlivesPredicate]) -> bool {
        self.check_in(ambient).is_ok()
    }

    fn check_in(&self, ambient: &[OutlivesPredicate]) -> Result<(), ConstraintFailure> {
        if self.regions.len() > LIMIT || self.facts.len() > LIMIT {
            return Err(ConstraintFailure::Limit);
        }
        let facts = leaves(&self.facts).ok_or(ConstraintFailure::Limit)?;
        let mut edges = BTreeMap::<Lifetime, Vec<Lifetime>>::new();
        for fact in &facts {
            if let OutlivesPredicate::Region { longer, shorter } = fact {
                edges.entry(*longer).or_default().push(*shorter);
            }
        }
        let mut work = 0usize;
        for fact in &facts {
            let (source, target) = match fact {
                OutlivesPredicate::Region { longer, shorter } => {
                    if self.owns(*longer) {
                        continue;
                    }
                    (None, (*longer, *shorter))
                }
                OutlivesPredicate::Type { subject, lifetime } => {
                    (Some(subject), (Lifetime::Static, *lifetime))
                }
            };
            let mut pending = vec![target.1];
            let mut seen = BTreeSet::new();
            while let Some(shorter) = pending.pop() {
                work += 1;
                if work > LIMIT * 16 {
                    return Err(ConstraintFailure::Limit);
                }
                if !seen.insert(shorter) {
                    continue;
                }
                if !self.owns(shorter) {
                    let obligation = match source {
                        Some(subject) => OutlivesPredicate::Type {
                            subject: subject.clone(),
                            lifetime: shorter,
                        },
                        None => OutlivesPredicate::Region {
                            longer: target.0,
                            shorter,
                        },
                    };
                    if !obligation.proven_by(ambient) {
                        return Err(
                            if source.is_none()
                                && matches!(target.0, Lifetime::Inferred(region)
                            if self.local_storage.contains(&region))
                            {
                                ConstraintFailure::LocalStorage
                            } else {
                                ConstraintFailure::Unsatisfied
                            },
                        );
                    }
                } else {
                    pending.extend(edges.get(&shorter).into_iter().flatten().copied());
                }
            }
        }
        Ok(())
    }

    pub(crate) fn facts(&self) -> &[OutlivesPredicate] {
        &self.facts
    }
    pub(crate) fn regions(&self) -> &BTreeSet<BodyRegion> {
        &self.regions
    }
    pub(crate) fn is_empty(&self) -> bool {
        self.regions.is_empty() && self.facts.is_empty()
    }
    pub(crate) fn includes(&self, required: &Self) -> bool {
        required.regions.is_subset(&self.regions)
            && required.local_storage.is_subset(&self.local_storage)
            && required
                .facts
                .iter()
                .all(|fact| fact.proven_by(&self.facts))
    }

    /// A callable retains the connected constraint component of its free
    /// value terms. This includes borrowing owned capture storage in its
    /// result, even when the owned capture type itself contains no lifetime.
    /// This is a projection, not a second analysis of the closure's body or
    /// a new invocation prerequisite.
    pub(crate) fn for_callable(
        &self,
        contract: &super::CallableContract,
        parameters: &[Type],
        result: &Type,
        effects: &super::EffectRow,
    ) -> Self {
        self.project(
            contract
                .terms()
                .into_iter()
                .map(|(argument, _)| argument)
                .chain(parameters.iter().cloned().map(GenericArgument::Type))
                .chain([
                    GenericArgument::Type(result.clone()),
                    GenericArgument::EffectRow(effects.clone()),
                ]),
        )
    }

    fn project(&self, terms: impl IntoIterator<Item = GenericArgument>) -> Self {
        let mut selected = BTreeSet::new();
        for argument in terms {
            let _ = super::regions::map_argument_regions(argument, &mut |lifetime, _| {
                if let Lifetime::Inferred(region) = lifetime
                    && self.regions.contains(&region)
                {
                    selected.insert(region);
                }
                Some(lifetime)
            });
        }
        let components = self
            .facts
            .iter()
            .map(|fact| {
                lifetimes(fact)
                    .into_iter()
                    .filter_map(|lifetime| match lifetime {
                        Lifetime::Inferred(region) if self.regions.contains(&region) => {
                            Some(region)
                        }
                        _ => None,
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut edges = BTreeMap::<BodyRegion, Vec<usize>>::new();
        for (index, regions) in components.iter().enumerate() {
            for region in regions {
                edges.entry(*region).or_default().push(index);
            }
        }
        let mut pending = selected.iter().copied().collect::<Vec<_>>();
        let mut facts = BTreeSet::new();
        while let Some(region) = pending.pop() {
            for index in edges.get(&region).into_iter().flatten() {
                if !facts.insert(*index) {
                    continue;
                }
                for next in &components[*index] {
                    if selected.insert(*next) {
                        pending.push(*next);
                    }
                }
            }
        }
        Self {
            facts: facts
                .into_iter()
                .map(|index| self.facts[index].clone())
                .collect(),
            local_storage: self
                .local_storage
                .intersection(&selected)
                .copied()
                .collect(),
            regions: selected,
        }
    }

    pub(crate) fn union(&self, other: &Self) -> Self {
        let mut value = self.clone();
        value.regions.extend(&other.regions);
        value.local_storage.extend(&other.local_storage);
        for fact in &other.facts {
            if !value.facts.contains(fact) {
                value.facts.push(fact.clone());
            }
        }
        value.canonicalize();
        value
    }

    pub(crate) fn map_terms(
        &self,
        mut map: impl FnMut(GenericArgument) -> GenericArgument,
    ) -> Self {
        let regions = self
            .regions
            .iter()
            .filter_map(|region| {
                match map(GenericArgument::Lifetime(Lifetime::Inferred(*region))) {
                    GenericArgument::Lifetime(Lifetime::Inferred(region)) => Some(region),
                    _ => None,
                }
            })
            .collect();
        let local_storage = self
            .local_storage
            .iter()
            .filter_map(|region| {
                match map(GenericArgument::Lifetime(Lifetime::Inferred(*region))) {
                    GenericArgument::Lifetime(Lifetime::Inferred(region)) => Some(region),
                    _ => None,
                }
            })
            .collect();
        let facts = self
            .facts
            .iter()
            .map(|fact| fact.map_terms(&mut map))
            .collect();
        let mut value = Self {
            regions,
            local_storage,
            facts,
        };
        value.facts.retain(|fact| !fact.proven_by(&[]));
        value.canonicalize();
        value
    }

    fn canonicalize(&mut self) {
        self.facts.sort_by_cached_key(fact_encoding);
        self.facts.dedup();
    }

    pub(crate) fn encode(&self, output: &mut Vec<u8>) {
        output.extend_from_slice(&(self.regions.len() as u64).to_le_bytes());
        for region in &self.regions {
            output.extend_from_slice(&region.owner.0.as_bytes());
            output.extend_from_slice(&region.index.to_le_bytes());
            output.push(u8::from(self.local_storage.contains(region)));
        }
        output.extend_from_slice(&(self.facts.len() as u64).to_le_bytes());
        for fact in &self.facts {
            output.extend(fact_encoding(fact));
        }
    }
}

/// Iterative SCCs of the region-only proof graph. This is an equality
/// quotient, not an alternative outlives checker. Structural type premises
/// use the same component expansion as rigid-boundary validation above.
fn equivalent_regions(
    evidence: &[OutlivesPredicate],
) -> Result<Vec<Vec<Lifetime>>, ConstraintFailure> {
    let mut edges = BTreeMap::<Lifetime, BTreeSet<Lifetime>>::new();
    for fact in leaves(evidence).ok_or(ConstraintFailure::Limit)? {
        if let OutlivesPredicate::Region { longer, shorter } = fact {
            edges.entry(longer).or_default().insert(shorter);
            edges.entry(shorter).or_default();
        }
    }
    if edges.len() > LIMIT {
        return Err(ConstraintFailure::Limit);
    }
    let nodes = edges.keys().copied().collect::<BTreeSet<_>>();
    edges.entry(Lifetime::Static).or_default().extend(nodes);
    let mut reverse = BTreeMap::<Lifetime, BTreeSet<Lifetime>>::new();
    for (node, children) in &edges {
        reverse.entry(*node).or_default();
        for child in children {
            reverse.entry(*child).or_default().insert(*node);
        }
    }
    let mut order = vec![];
    let mut seen = BTreeSet::new();
    for start in edges.keys() {
        let mut pending = vec![(*start, false)];
        while let Some((node, exiting)) = pending.pop() {
            if exiting {
                order.push(node);
            } else if seen.insert(node) {
                pending.push((node, true));
                pending.extend(edges[&node].iter().map(|child| (*child, false)));
            }
        }
    }
    seen.clear();
    let mut components = vec![];
    for start in order.into_iter().rev() {
        if seen.contains(&start) {
            continue;
        }
        let mut component = vec![];
        let mut pending = vec![start];
        while let Some(node) = pending.pop() {
            if !seen.insert(node) {
                continue;
            }
            component.push(node);
            pending.extend(&reverse[&node]);
        }
        component.sort();
        components.push(component);
    }
    Ok(components)
}

fn lifetimes(fact: &OutlivesPredicate) -> BTreeSet<Lifetime> {
    let mut regions = BTreeSet::new();
    fact.map_terms(|argument| {
        super::regions::map_argument_regions(argument, &mut |lifetime, _| {
            regions.insert(lifetime);
            Some(lifetime)
        })
        .expect("region observation preserves binder depth")
    });
    regions
}

fn fact_encoding(fact: &OutlivesPredicate) -> Vec<u8> {
    let mut bytes = vec![];
    match fact {
        OutlivesPredicate::Region { longer, shorter } => {
            bytes.push(0);
            super::encode_generic_arguments(
                &[
                    GenericArgument::Lifetime(*longer),
                    GenericArgument::Lifetime(*shorter),
                ],
                &mut bytes,
            );
        }
        OutlivesPredicate::Type { subject, lifetime } => {
            bytes.push(1);
            super::encode_generic_arguments(
                &[
                    GenericArgument::Type(subject.clone()),
                    GenericArgument::Lifetime(*lifetime),
                ],
                &mut bytes,
            );
        }
    }
    bytes
}

fn leaves(requirements: &[OutlivesPredicate]) -> Option<Vec<OutlivesPredicate>> {
    let mut pending = requirements
        .iter()
        .cloned()
        .map(|fact| (fact, 0))
        .collect::<Vec<_>>();
    let mut result = vec![];
    let mut work = 0;
    while let Some((fact, depth)) = pending.pop() {
        work += 1;
        if work > LIMIT || depth > 128 {
            return None;
        }
        if lifetimes(&fact)
            .iter()
            .any(|lifetime| matches!(lifetime, Lifetime::Infer(_) | Lifetime::Placeholder(_)))
        {
            return None;
        }
        if let OutlivesPredicate::Type { subject, lifetime } = &fact
            && let Some(parts) = OutlivesPredicate::components(subject, *lifetime)
        {
            pending.extend(parts.into_iter().map(|part| (part, depth + 1)));
        } else if !result.contains(&fact) {
            result.push(fact);
        }
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::InferContext;
    use crate::{DefKey, Digest, Mutability, Quantity, Safety};

    fn owner(name: &[u8]) -> DefKey {
        DefKey(Digest::of_bytes(name))
    }
    fn relation(longer: Lifetime, shorter: Lifetime) -> OutlivesPredicate {
        OutlivesPredicate::Region { longer, shorter }
    }
    fn reference(lifetime: Lifetime) -> Type {
        Type::Reference {
            mutability: Mutability::Shared,
            lifetime,
            referent: Box::new(Type::Unit),
        }
    }

    #[test]
    fn freezing_preserves_independent_roots_aliases_and_body_owners() {
        let mut inference = InferContext::for_body();
        let first = inference.fresh_lifetime();
        let second = inference.fresh_lifetime();
        let alias = inference.fresh_lifetime();
        inference.unify_lifetimes(first, alias).unwrap();
        inference
            .finish_body_lifetimes(owner(b"first-body"), &[], &[])
            .unwrap();
        let first = inference.resolve_lifetime(first).unwrap();
        let second = inference.resolve_lifetime(second).unwrap();
        assert_ne!(first, second);
        assert_eq!(first, inference.resolve_lifetime(alias).unwrap());
        assert!(matches!(first, Lifetime::Inferred(_)));
        assert!(!relation(first, second).proven_by(inference.body_regions().facts()));
        assert!(!relation(first, Lifetime::Elided).proven_by(inference.body_regions().facts()));
        let mut other = InferContext::for_body();
        let other_first = other.fresh_lifetime();
        let other_second = other.fresh_lifetime();
        let other_alias = other.fresh_lifetime();
        other.unify_lifetimes(other_first, other_alias).unwrap();
        other
            .finish_body_lifetimes(owner(b"second-body"), &[], &[])
            .unwrap();
        assert_ne!(first, other.resolve_lifetime(other_first).unwrap());
        assert_ne!(second, other.resolve_lifetime(other_second).unwrap());
        assert_ne!(
            super::super::canonical_type_encoding(&reference(first)),
            super::super::canonical_type_encoding(&reference(second))
        );
    }

    #[test]
    fn unconstrained_phantom_bounds_remain_directional_not_equal() {
        let mut inference = InferContext::for_body();
        let longer = inference.fresh_lifetime();
        let shorter = inference.fresh_lifetime();
        inference
            .finish_body_lifetimes(owner(b"phantom"), &[relation(longer, shorter)], &[])
            .unwrap();
        let longer = inference.resolve_lifetime(longer).unwrap();
        let shorter = inference.resolve_lifetime(shorter).unwrap();
        assert_ne!(longer, shorter);
        assert!(relation(longer, shorter).proven_by(inference.body_regions().facts()));
        assert!(!relation(shorter, longer).proven_by(inference.body_regions().facts()));
        assert!(!relation(longer, Lifetime::Static).proven_by(inference.body_regions().facts()));
        assert!(inference.body_regions().valid_in(&[]));
    }

    #[test]
    fn interval_constraints_do_not_equate_independent_rigid_upper_bounds() {
        let a = Lifetime::Generic(0);
        let b = Lifetime::Generic(1);
        let c = Lifetime::Generic(2);
        for sufficient in [false, true] {
            let mut inference = InferContext::for_body();
            let middle = inference.fresh_lifetime();
            let requirements = [
                relation(a, middle),
                relation(c, middle),
                relation(middle, b),
            ];
            let mut ambient = vec![relation(a, b)];
            if sufficient {
                ambient.push(relation(c, b));
            }
            let result =
                inference.finish_body_lifetimes(owner(b"interval"), &requirements, &ambient);
            assert_eq!(result.is_ok(), sufficient);
            if !sufficient {
                continue;
            }
            let middle = inference.resolve_lifetime(middle).unwrap();
            assert!(matches!(middle, Lifetime::Inferred(_)));
            let facts = inference.body_regions().facts();
            assert!(requirements.iter().all(|requirement| {
                let requirement = requirement
                    .map_terms(|argument| inference.resolve_argument_structure(argument));
                requirement.proven_by(facts)
            }));
            assert!(!relation(a, c).proven_by(facts));
            assert!(!relation(c, a).proven_by(facts));
            assert!(!inference.body_regions().valid_in(&[]));
        }
    }

    #[test]
    fn static_is_selected_only_when_constraints_force_it() {
        let mut inference = InferContext::for_body();
        let required = inference.fresh_lifetime();
        let independent = inference.fresh_lifetime();
        inference
            .finish_body_lifetimes(
                owner(b"static-bound"),
                &[relation(required, Lifetime::Static)],
                &[],
            )
            .unwrap();
        assert_eq!(
            inference.resolve_lifetime(required).unwrap(),
            Lifetime::Static
        );
        assert!(matches!(
            inference.resolve_lifetime(independent).unwrap(),
            Lifetime::Inferred(_)
        ));
        let inferred = inference.resolve_lifetime(independent).unwrap();
        assert!(
            relation(inferred, Lifetime::Elided).proven_by(&[relation(inferred, Lifetime::Static)])
        );
    }

    #[test]
    fn generic_type_constraints_cannot_smuggle_a_rigid_outlives_fact() {
        let boundary = Lifetime::Generic(0);
        for sufficient in [false, true] {
            let mut inference = InferContext::for_body();
            let middle = inference.fresh_lifetime();
            let requirement = OutlivesPredicate::Type {
                subject: Type::Generic(1),
                lifetime: middle,
            };
            let ambient = if sufficient {
                vec![OutlivesPredicate::Type {
                    subject: Type::Generic(1),
                    lifetime: boundary,
                }]
            } else {
                vec![]
            };
            assert_eq!(
                inference
                    .finish_body_lifetimes(
                        owner(b"type-bound"),
                        &[requirement, relation(middle, boundary)],
                        &ambient
                    )
                    .is_ok(),
                sufficient
            );
        }
    }

    #[test]
    fn already_solved_cells_do_not_introduce_new_rigid_assumptions() {
        let mut inference = InferContext::for_body();
        let hole = inference.fresh_lifetime();
        inference
            .unify_lifetimes(hole, Lifetime::Generic(0))
            .unwrap();
        assert!(
            inference
                .finish_body_lifetimes(
                    owner(b"solved-cell"),
                    &[relation(hole, Lifetime::Generic(1))],
                    &[]
                )
                .is_err()
        );
    }

    #[test]
    fn capture_projection_and_substitution_transport_the_same_constraints() {
        let mut inference = InferContext::for_body();
        let longer = inference.fresh_lifetime();
        let shorter = inference.fresh_lifetime();
        let unrelated = inference.fresh_lifetime();
        inference
            .finish_body_lifetimes(owner(b"capture-regions"), &[relation(longer, shorter)], &[])
            .unwrap();
        let callable = Type::Callable {
            contract: Box::new(super::super::CallableContract {
                captures: vec![reference(shorter)],
                ..Default::default()
            }),
            safety: Safety::Safe,
            lifetime_binders: 0,
            parameters: vec![],
            result: Box::new(Type::Unit),
            effects: super::super::EffectRow::empty(),
            invocation: Quantity::ONCE,
        };
        let Type::Callable { contract, .. } = inference.zonk(callable).unwrap() else {
            panic!("callable");
        };
        let longer = inference.resolve_lifetime(longer).unwrap();
        let shorter = inference.resolve_lifetime(shorter).unwrap();
        let unrelated = inference.resolve_lifetime(unrelated).unwrap();
        assert!(relation(longer, shorter).proven_by(contract.body_regions.facts()));
        assert!(!contract.body_regions.owns(unrelated));
        let mapped = contract.map_terms(|argument, _| {
            super::super::regions::map_argument_regions(argument, &mut |value, _| {
                Some(if value == longer {
                    Lifetime::Generic(2)
                } else {
                    value
                })
            })
            .unwrap()
        });
        assert!(relation(Lifetime::Generic(2), shorter).proven_by(mapped.body_regions.facts()));
        assert!(mapped.body_regions.owns(shorter));
        assert!(!mapped.body_regions.owns(longer));
    }

    #[test]
    fn local_loans_can_share_an_inferred_region_without_equating_storage() {
        let mut inference = InferContext::for_body();
        let first = inference.fresh_borrow_lifetime(owner(b"local-loans"));
        let second = inference.fresh_borrow_lifetime(owner(b"local-loans"));
        inference.unify_lifetimes(first, second).unwrap();
        inference
            .finish_body_lifetimes(owner(b"local-loans"), &[], &[])
            .unwrap();
        let loan = inference.resolve_lifetime(first).unwrap();
        assert_eq!(loan, inference.resolve_lifetime(second).unwrap());
        let constraints = inference.body_regions();
        assert_eq!(constraints.local_storage.len(), 2);
        for storage in &constraints.local_storage {
            assert!(relation(Lifetime::Inferred(*storage), loan).proven_by(constraints.facts()));
            assert!(!relation(loan, Lifetime::Inferred(*storage)).proven_by(constraints.facts()));
        }
        assert!(constraints.valid_in(&[]));
    }

    #[test]
    fn local_storage_bounds_reject_static_and_external_caller_regions() {
        for required in [Lifetime::Static, Lifetime::Generic(0), Lifetime::Elided] {
            let mut inference = InferContext::for_body();
            let loan = inference.fresh_borrow_lifetime(owner(b"local-upper-bound"));
            inference.unify_lifetimes(loan, required).unwrap();
            assert_eq!(
                inference.finish_body_lifetimes(owner(b"local-upper-bound"), &[], &[]),
                Err(super::super::TypeError::BorrowExceedsLocalStorage)
            );
        }
    }
}
