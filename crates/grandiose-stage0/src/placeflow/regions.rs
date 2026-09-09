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

/// A callable is a resident value, not a reference to its environment. Keep
/// its entire value footprint even when a contextual nominal argument has
/// erased the producer's capture refinements. These paths never participate
/// in Core's physical-reference authority or manufacture a reference leaf.
pub(crate) fn callable_paths(signatures: &crate::ElaboratedInterface, ty: &crate::Type, input: bool) -> Vec<(Vec<u32>, crate::Type)> {
    use crate::{ElaboratedHeader, ElaboratedNominalLayout, GenericArgument, Type};
    fn weight(ty: &Type) -> usize {
        let arguments = |values: &[GenericArgument]| values.iter().fold(0usize, |sum, value|
            sum.saturating_add(match value { GenericArgument::Type(ty) => weight(ty), _ => 1 }));
        1usize.saturating_add(match ty {
            Type::Nominal { arguments: values, .. } => arguments(values),
            Type::Tuple(values) => values.iter().fold(0usize, |sum, value| sum.saturating_add(weight(value))),
            Type::Reference { referent, .. } => weight(referent),
            Type::Array(element) | Type::FixedArray { element, .. } => weight(element),
            _ => 0,
        })
    }
    fn visit(signatures: &crate::ElaboratedInterface, ty: &Type, input: bool, path: &mut Vec<u32>,
        active: &mut BTreeMap<crate::DefKey, usize>, leaves: &mut Vec<(Vec<u32>, Type)>) {
        match ty {
            Type::Callable { .. } => leaves.push((path.clone(), ty.clone())),
            Type::Reference { referent, .. } if input => {
                path.push(crate::core::REFERENCE_PATH_DEREF);
                visit(signatures, referent, input, path, active, leaves);
                path.pop();
            }
            Type::Tuple(fields) => for (index, field) in fields.iter().enumerate() {
                path.push(index as u32); visit(signatures, field, input, path, active, leaves); path.pop();
            },
            Type::Array(element) | Type::FixedArray { element, .. } if ty.fixed_array_length() != Some(0) => {
                path.push(crate::core::REFERENCE_PATH_ARRAY_ELEMENT);
                visit(signatures, element, input, path, active, leaves); path.pop();
            }
            Type::Nominal { definition, arguments } => {
                let size = weight(ty);
                if active.get(definition).is_some_and(|previous| size >= *previous) { return; }
                let previous = active.insert(*definition, size);
                let mut fields = vec![];
                match signatures.definitions.get(definition) {
                    Some(ElaboratedHeader::Nominal { layout: ElaboratedNominalLayout::Struct(values) | ElaboratedNominalLayout::TupleStruct(values), .. }) =>
                        fields.extend(values.iter().enumerate().map(|(index, field)| (index, &field.ty))),
                    Some(ElaboratedHeader::Nominal { layout: ElaboratedNominalLayout::Enum(variants), .. }) => for variant in variants {
                        match &variant.payload {
                            crate::signature::ElaboratedEnumVariantPayload::Tuple(values) => fields.extend(values.iter().enumerate()),
                            crate::signature::ElaboratedEnumVariantPayload::Struct(values) => fields.extend(values.iter().enumerate().map(|(index, field)| (index, &field.ty))),
                            crate::signature::ElaboratedEnumVariantPayload::Unit => {},
                        }
                    },
                    _ => {},
                }
                for (index, field) in fields {
                    if let Ok(field) = crate::core::instantiate_nominal_field_type(field, arguments) {
                        path.push(index as u32); visit(signatures, &field, input, path, active, leaves); path.pop();
                    }
                }
                for (index, argument) in arguments.iter().enumerate() {
                    if let GenericArgument::Type(argument) = argument {
                        path.extend([crate::core::REFERENCE_PATH_LOGICAL_ARGUMENT, index as u32]);
                        visit(signatures, argument, input, path, active, leaves); path.truncate(path.len() - 2);
                    }
                }
                if let Some(previous) = previous { active.insert(*definition, previous); }
                else { active.remove(definition); }
            }
            _ => {},
        }
    }
    let mut leaves = vec![];
    visit(signatures, ty, input, &mut vec![], &mut BTreeMap::new(), &mut leaves);
    leaves.dedup();
    leaves
}

fn same_callable_abi(left: &crate::Type, right: &crate::Type) -> bool {
    match (left, right) {
        (crate::Type::Callable { safety: a, lifetime_binders: b, parameters: c, result: d, effects: e, .. },
         crate::Type::Callable { safety: f, lifetime_binders: g, parameters: h, result: i, effects: j, .. }) =>
            (a, b, c, d, e) == (f, g, h, i, j),
        _ => false,
    }
}

/// Logical callable result forwarding is separate from checked reference
/// provenance. A plain callable nominal argument still forwards the actual
/// value's capture footprint; no environment address is exposed.
pub(crate) fn callable_result_paths(signatures: &crate::ElaboratedInterface, expression: &crate::core::CoreExpr) -> Vec<crate::core::CallReferencePath> {
    let crate::Type::Callable { parameters, result, .. } = &expression.ty else { return vec![]; };
    if callable_paths(signatures, result, false).is_empty() { return vec![]; }
    let rigid = rigid_callable_signature(signatures, expression);
    let (parameters, result) = rigid.as_ref().map(|signature| (&signature.parameters, &signature.result)).unwrap_or((parameters, result));
    let inputs = parameters.iter().enumerate().flat_map(|(index, parameter)|
        callable_paths(signatures, parameter, true).into_iter().map(move |(path, ty)| (index, path, ty))).collect::<Vec<_>>();
    let literal_results = match &expression.kind {
        crate::core::CoreKind::Function { definition, .. } => match signatures.definitions.get(definition) {
            Some(crate::ElaboratedHeader::Callable(signature)) => Some(callable_paths(signatures, &signature.result, false)),
            _ => None,
        },
        _ => None,
    };
    let mut paths = vec![];
    for (result_fields, result_ty) in callable_paths(signatures, result, false) {
        let mut matched = false;
        for (argument, argument_fields, ty) in &inputs {
            if !same_callable_abi(&result_ty, ty) { continue; }
            matched = true;
            paths.push(crate::core::CallReferencePath { result_fields: result_fields.clone(),
                argument: *argument as u32, argument_fields: argument_fields.clone() });
        }
        let crate::Type::Callable { contract, .. } = &result_ty else { unreachable!("callable resident"); };
        let captures = contract.open(|_| None).map(|contract| contract.captures).unwrap_or_else(|| contract.captures.clone());
        let mut captured_regions = vec![];
        for capture in &captures {
            let _ = crate::core::input_reference_leaf_paths(signatures, capture, &mut captured_regions);
        }
        // A declared plain Fn result can close over a non-callable input even
        // though its ABI mentions no region. In contrast, `pop<T> -> T`
        // forwards T's existing environment, not the short receiver borrow.
        // A known empty environment is positive noncapture evidence.
        let unknown_factory = contract.environment.is_none() && (!matched || literal_results.as_ref()
            .is_none_or(|results| results.iter().any(|(path, _)| crate::core::reference_path_matches(path, &result_fields))));
        if !unknown_factory && captured_regions.is_empty() { continue; }
        for (argument, parameter) in parameters.iter().enumerate() {
            let mut references = vec![];
            let _ = crate::core::input_reference_leaf_paths(signatures, parameter, &mut references);
            for (argument_fields, ty) in references {
                let crate::Type::Reference { lifetime, .. } = ty else { continue; };
                if !unknown_factory && !captured_regions.iter().any(|(_, ty)|
                    matches!(ty, crate::Type::Reference { lifetime: captured, .. } if *captured == lifetime)) { continue; }
                paths.push(crate::core::CallReferencePath { result_fields: result_fields.clone(), argument: argument as u32, argument_fields });
            }
        }
    }
    paths
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
        leaves.extend(callable_paths(signatures, parameter, true));
        inputs.extend(leaves.into_iter().map(|(path, ty)| (index, path, ty)));
    }
    let mut transfers = vec![];
    for (destination, destination_path, destination_ty) in &inputs {
        if !crate::core::reference_path_is_logical(destination_path) { continue; }
        for (source, source_path, source_ty) in &inputs {
            if destination == source { continue; }
            let related = match (destination_ty, source_ty) {
                (crate::Type::Reference { lifetime, .. }, crate::Type::Reference { lifetime: other, .. }) => lifetime == other,
                _ => same_callable_abi(destination_ty, source_ty),
            };
            if !related { continue; }
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
        Type::Callable { contract, safety, lifetime_binders, parameters, result, effects, invocation } => {
            let mut contract = (**contract).clone();
            // A substituted callable's free capture regions belong to T,
            // just like an ordinary substituted reference. They are not the
            // independently elided &mut Owner<T> receiver. Its invocation
            // binder and proof-only environment identities stay untouched.
            contract.captures = contract.captures.iter().map(|capture| rigid_resident_type(capture, regions)).collect();
            Type::Callable { contract: Box::new(contract), safety: *safety, lifetime_binders: *lifetime_binders,
                parameters: parameters.clone(), result: result.clone(), effects: effects.clone(), invocation: *invocation }
        }
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
    fn callable_residents_are_whole_values_not_physical_reference_leaves() {
        let callable = crate::Type::Callable {
            contract: Default::default(), safety: crate::Safety::Safe, lifetime_binders: 0,
            parameters: vec![], result: Box::new(crate::Type::Unit), effects: crate::EffectRow::empty(),
            invocation: crate::Quantity::ONCE,
        };
        let signatures = crate::ElaboratedInterface::default();
        let array = crate::Type::fixed_array(callable.clone(), u64::MAX);
        let paths = callable_paths(&signatures, &array, false);
        assert_eq!(paths, vec![(vec![crate::core::REFERENCE_PATH_ARRAY_ELEMENT], callable.clone())]);
        assert!(callable_paths(&signatures, &crate::Type::fixed_array(callable.clone(), 0), false).is_empty());
        let mut references = vec![];
        crate::core::reference_leaf_paths(&signatures, &array, &mut vec![], &mut references).unwrap();
        assert!(references.is_empty(), "callable residency must not mint reference authority");
        let borrowed = crate::Type::Reference { lifetime: crate::Lifetime::Elided,
            mutability: crate::Mutability::Shared, referent: Box::new(array) };
        assert!(callable_paths(&signatures, &borrowed, false).is_empty());
        assert_eq!(callable_paths(&signatures, &borrowed, true), vec![(
            vec![crate::core::REFERENCE_PATH_DEREF, crate::core::REFERENCE_PATH_ARRAY_ELEMENT], callable)]);
    }

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
        let callable = crate::Type::Callable {
            contract: Box::new(crate::CallableContract { captures: vec![reference], ..Default::default() }),
            safety: crate::Safety::Safe, lifetime_binders: 0, parameters: vec![], result: Box::new(crate::Type::Unit),
            effects: crate::EffectRow::empty(), invocation: crate::Quantity::ONCE,
        };
        let crate::Type::Callable { contract, .. } = rigid_resident_type(&callable, &mut regions) else { unreachable!() };
        assert_eq!(contract.captures, vec![second]);
    }
}
