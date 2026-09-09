//! Logical resident regions are type relations, not checked memory addresses.
//! A source-managed owner may be empty and may share its storage with another
//! owner. Preserve those identities separately from the currently known loans
//! so later writes cannot erase the relation by starting from an empty set.

use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct Region {
    pub site: String,
    pub path: Vec<u32>,
}

#[derive(Clone, Debug)]
pub(crate) struct RegionGraph<T> {
    values: BTreeMap<Region, T>,
    edges: BTreeMap<Region, BTreeSet<Region>>,
}

impl<T> Default for RegionGraph<T> {
    fn default() -> Self { Self { values: BTreeMap::new(), edges: BTreeMap::new() } }
}

impl<T: Clone> RegionGraph<T> {
    pub fn reachable(&self, roots: &BTreeSet<Region>) -> BTreeSet<Region> {
        let mut pending = roots.iter().cloned().collect::<Vec<_>>();
        let mut found = BTreeSet::new();
        while let Some(region) = pending.pop() {
            if !found.insert(region.clone()) { continue; }
            if let Some(edges) = self.edges.get(&region) { pending.extend(edges.iter().cloned()); }
        }
        found
    }

    pub fn contents(&self, roots: &BTreeSet<Region>) -> Vec<T> {
        self.reachable(roots).iter().filter_map(|region| self.values.get(region).cloned()).collect()
    }

    pub fn insert(&mut self, region: Region, value: T, merge: impl FnOnce(&mut T, T)) {
        match self.values.entry(region) {
            std::collections::btree_map::Entry::Vacant(entry) => { entry.insert(value); }
            std::collections::btree_map::Entry::Occupied(mut entry) => merge(entry.get_mut(), value),
        }
    }

    /// A frozen callable relation can permit either aliasing or independent
    /// storage. Joining the logical regions is conservative for both; unlike
    /// a snapshot of their current contents it also accounts for later writes.
    pub fn connect(&mut self, regions: &BTreeSet<Region>) {
        let Some(first) = regions.first() else { return; };
        for other in regions.iter().skip(1) {
            self.edges.entry(first.clone()).or_default().insert(other.clone());
            self.edges.entry(other.clone()).or_default().insert(first.clone());
        }
    }

    pub fn merge_from(&mut self, other: &Self, merge: impl Fn(&mut T, T)) {
        for (region, value) in &other.values { self.insert(region.clone(), value.clone(), &merge); }
        for (region, edges) in &other.edges { self.edges.entry(region.clone()).or_default().extend(edges.iter().cloned()); }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ResidentTransfer {
    pub destination: usize,
    pub destination_path: Vec<u32>,
    pub source: usize,
    pub source_path: Vec<u32>,
}

/// Recover the selected declaration before its independently elided outer
/// receiver is conflated with a reference supplied as T. A Vec<&T> resident
/// and the short &mut Vec receiver are distinct regions, even if their final
/// caller-facing type encodings both contain `Elided`.
pub(crate) fn call_transfers(
    signatures: &crate::ElaboratedInterface,
    body: &crate::core::TypedBody,
    callee: crate::core::CoreId,
) -> Vec<ResidentTransfer> {
    use crate::Type;
    let expression = body.expression(callee);
    let Type::Callable { parameters: realized, .. } = &expression.ty else { return vec![]; };
    let realized = parameter_transfers(signatures, realized);
    if realized.is_empty() { return realized; }
    let parameters = rigid_callable_signature(signatures, expression).map(|signature| signature.parameters);
    parameters.as_deref().map(|parameters| parameter_transfers(signatures, parameters)).unwrap_or(realized)
}

pub(crate) fn call_origin(signatures: &crate::ElaboratedInterface, callee: &crate::core::CoreExpr) -> Option<crate::core::CallReferenceOrigin> {
    let signature = rigid_callable_signature(signatures, callee)?;
    let origin = crate::core::callable_reference_origin_from_contract(signatures, &signature.parameters, &signature.result);
    (!matches!(origin, crate::core::CallReferenceOrigin::Opaque)).then_some(origin)
}

fn rigid_callable_signature(signatures: &crate::ElaboratedInterface, expression: &crate::core::CoreExpr) -> Option<crate::CallableSignature> {
    use crate::core::CoreKind;
    match &expression.kind {
        CoreKind::Function { definition, arguments, .. } => {
            // Distinct type slots can be connected by an ordinary trait
            // conversion. Preserve equality of their realized regions; only
            // declaration-local elision, absent from these substitutions,
            // remains separate from a generic resident's region.
            let mut regions = BTreeMap::new();
            let arguments = arguments.iter().map(|argument| rigid_resident_argument(argument, &mut regions)).collect::<Vec<_>>();
            signatures.instantiate_callable_generic(*definition, &arguments).ok()
        }
        _ => None,
    }
}

pub(crate) fn parameter_transfers(signatures: &crate::ElaboratedInterface, parameters: &[crate::Type]) -> Vec<ResidentTransfer> {
    let mut inputs = vec![];
    for (index, parameter) in parameters.iter().enumerate() {
        let mut leaves = vec![];
        let _ = crate::core::input_reference_leaf_paths(signatures, parameter, &mut leaves);
        inputs.extend(leaves.into_iter().map(|(path, ty)| (index, path, ty)));
    }
    let mut transfers = vec![];
    for (destination, destination_path, destination_ty) in &inputs {
        if !crate::core::reference_path_is_logical(destination_path) { continue; }
        let crate::Type::Reference { lifetime, .. } = destination_ty else { continue; };
        for (source, source_path, source_ty) in &inputs {
            if destination == source { continue; }
            if !matches!(source_ty, crate::Type::Reference { lifetime: source_lifetime, .. } if lifetime == source_lifetime) { continue; }
            transfers.push(ResidentTransfer { destination: *destination, destination_path: destination_path.clone(),
                source: *source, source_path: source_path.clone() });
        }
    }
    transfers
}

fn rigid_resident_lifetime(lifetime: crate::Lifetime, regions: &mut BTreeMap<crate::Lifetime, crate::Lifetime>) -> crate::Lifetime {
    if lifetime == crate::Lifetime::Static { return lifetime; }
    let next = crate::Lifetime::Placeholder(crate::types::UniversalRegion { universe: u32::MAX, index: regions.len() as u32 });
    *regions.entry(lifetime).or_insert(next)
}

fn rigid_resident_argument(argument: &crate::GenericArgument, regions: &mut BTreeMap<crate::Lifetime, crate::Lifetime>) -> crate::GenericArgument {
    use crate::GenericArgument;
    match argument {
        GenericArgument::Type(ty) => GenericArgument::Type(rigid_resident_type(ty, regions)),
        GenericArgument::Lifetime(lifetime) => GenericArgument::Lifetime(rigid_resident_lifetime(*lifetime, regions)),
        _ => argument.clone(),
    }
}

fn rigid_resident_type(ty: &crate::Type, regions: &mut BTreeMap<crate::Lifetime, crate::Lifetime>) -> crate::Type {
    use crate::Type;
    match ty {
        Type::Reference { lifetime, mutability, referent } => Type::Reference {
            lifetime: rigid_resident_lifetime(*lifetime, regions),
            mutability: *mutability, referent: Box::new(rigid_resident_type(referent, regions)),
        },
        Type::Tuple(values) => Type::Tuple(values.iter().map(|value| rigid_resident_type(value, regions)).collect()),
        Type::FixedArray { element, length } => Type::FixedArray { element: Box::new(rigid_resident_type(element, regions)), length: length.clone() },
        Type::Array(element) => Type::Array(Box::new(rigid_resident_type(element, regions))),
        Type::Nominal { definition, arguments } => Type::Nominal { definition: *definition, arguments: arguments.iter().map(|argument| rigid_resident_argument(argument, regions)).collect() },
        Type::Projection { subject, trait_definition, trait_arguments, name, item_generic_kinds, item_arguments } => Type::Projection {
            subject: Box::new(rigid_resident_type(subject, regions)), trait_definition: *trait_definition,
            trait_arguments: trait_arguments.iter().map(|argument| rigid_resident_argument(argument, regions)).collect(), name: name.clone(),
            item_generic_kinds: item_generic_kinds.clone(), item_arguments: item_arguments.iter().map(|argument| rigid_resident_argument(argument, regions)).collect(),
        },
        _ => ty.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_aliases_receive_later_stores_and_branch_joins() {
        let a = Region { site: "a".into(), path: vec![] };
        let b = Region { site: "b".into(), path: vec![] };
        let mut graph = RegionGraph::<BTreeSet<u32>>::default();
        graph.connect(&BTreeSet::from([a.clone(), b.clone()]));
        let mut branch = graph.clone();
        branch.insert(a.clone(), BTreeSet::from([1]), |values, incoming| values.extend(incoming));
        graph.insert(b.clone(), BTreeSet::from([2]), |values, incoming| values.extend(incoming));
        graph.merge_from(&branch, |values, incoming| values.extend(incoming));
        let contents = graph.contents(&BTreeSet::from([b])).into_iter().flatten().collect::<BTreeSet<_>>();
        assert_eq!(contents, BTreeSet::from([1, 2]));
    }

    #[test]
    fn rigid_substitutions_keep_cross_argument_equality_without_receiver_elision() {
        let reference = crate::Type::Reference {
            lifetime: crate::Lifetime::Elided, mutability: crate::types::Mutability::Shared,
            referent: Box::new(crate::Type::Unit),
        };
        let mut regions = BTreeMap::new();
        let first = rigid_resident_type(&crate::Type::Tuple(vec![reference.clone()]), &mut regions);
        let second = rigid_resident_type(&reference, &mut regions);
        assert_eq!(first, crate::Type::Tuple(vec![second.clone()]));
        assert!(matches!(second, crate::Type::Reference { lifetime: crate::Lifetime::Placeholder(_), .. }));
        assert_eq!(rigid_resident_lifetime(crate::Lifetime::Static, &mut regions), crate::Lifetime::Static);
    }
}
