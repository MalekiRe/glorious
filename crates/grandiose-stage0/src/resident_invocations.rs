//! Shared may-store rules for explicit and captured invocation operands.
//!
//! The producer reads typed provenance operands without mutating their domain,
//! then publishes store edges. Consumers apply edges to their own storage
//! graph; they do not rediscover which callbacks may run or match their inputs.
//! Unresolved capture coverage is retained separately from known-empty input.

use crate::callable_declarations::declared_invocation_contract;
use crate::{
    Type,
    core::{CoreExpr, CoreKind},
    placeflow::regions,
};
use std::collections::BTreeSet;

#[derive(Clone, Debug)]
pub(crate) struct Operand<V> {
    pub ty: Type,
    pub value: V,
}

// Canonical type identity is already the compiler's key for capture snapshots.
// Use the same equivalence for invocation sharing, including bound regions and
// effect/type/const argument kinds; Debug spelling is not semantic identity.
impl<V: Ord> Ord for Operand<V> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        crate::types::canonical_type_encoding(&self.ty)
            .cmp(&crate::types::canonical_type_encoding(&other.ty))
            .then_with(|| self.value.cmp(&other.value))
    }
}
impl<V: Ord> PartialOrd for Operand<V> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<V: Ord> PartialEq for Operand<V> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl<V: Ord> Eq for Operand<V> {}

pub(crate) struct CapturedInputs<V> {
    pub operands: Vec<Operand<V>>,
    pub unresolved: bool,
}

pub(crate) trait Inputs {
    type Value: Clone + Ord;
    fn project(&self, value: &Self::Value, path: &[u32]) -> Option<Self::Value>;
    fn captures(&self, callable: &Operand<Self::Value>) -> CapturedInputs<Self::Value>;
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct Store<V> {
    pub destination: V,
    pub source: V,
    pub source_is_callable: bool,
}

pub(crate) struct Relations<V> {
    pub stores: Vec<Store<V>>,
    pub unresolved: Vec<Operand<V>>,
}

/// Derive invocation edges from frozen signatures and the caller's operand
/// snapshots. The worklist expands nested captured callables using the same
/// rules as argument callbacks. Repeated identical invocation inputs share one
/// expansion; this is a may-store relation, never an execution-order rewrite.
pub(crate) fn derive<D: Inputs>(
    signatures: &crate::ElaboratedInterface,
    expression: &CoreExpr,
    callee: D::Value,
    arguments: &[Operand<D::Value>],
    domain: &D,
) -> Relations<D::Value> {
    let mut stores = BTreeSet::new();
    let mut unresolved = BTreeSet::new();
    let mut pending = vec![];
    // Declaration-local elision remains distinct from substituted residents.
    // This is the same relation for all domains, not a consumer-side recovery.
    add_stores(
        signatures,
        arguments,
        regions::expression_transfers(signatures, expression),
        domain,
        &mut stores,
    );
    if !matches!(
        expression.kind,
        CoreKind::Function { .. } | CoreKind::TraitMethod { .. }
    ) {
        for (path, ty) in regions::callable_paths(signatures, &expression.ty, true) {
            let Some(value) = domain.project(&callee, &path) else {
                continue;
            };
            let Type::Callable { parameters, .. } = &ty else {
                unreachable!("callable path");
            };
            let actual = parameters
                .iter()
                .zip(arguments)
                .map(|(ty, argument)| Operand {
                    ty: ty.clone(),
                    value: argument.value.clone(),
                })
                .collect();
            pending.push((Operand { ty, value }, actual, false));
        }
    }
    let argument_types = arguments
        .iter()
        .map(|argument| argument.ty.clone())
        .collect::<Vec<_>>();
    for (argument, authorized) in invoked_argument_paths(signatures, expression) {
        let Some(argument) = arguments.get(argument) else {
            continue;
        };
        for (path, ty) in regions::callable_paths(signatures, &argument.ty, true) {
            if !crate::core::reference_path_is_prefix(&authorized, &path) {
                continue;
            }
            let Some(value) = domain.project(&argument.value, &path) else {
                continue;
            };
            let actual = select_arguments(signatures, &ty, &argument_types, arguments, domain);
            pending.push((Operand { ty, value }, actual, true));
        }
    }
    let mut expanded = BTreeSet::new();
    while let Some((callable, arguments, include_explicit)) = pending.pop() {
        if !expanded.insert((callable.clone(), arguments.clone(), include_explicit)) {
            continue;
        }
        let captured = domain.captures(&callable);
        if captured.unresolved {
            unresolved.insert(callable.clone());
        }
        let count = captured.operands.len();
        let operands = captured
            .operands
            .into_iter()
            .chain(arguments)
            .collect::<Vec<_>>();
        let types = operands
            .iter()
            .map(|operand| operand.ty.clone())
            .collect::<Vec<_>>();
        let transfers = regions::parameter_transfers(signatures, &types)
            .into_iter()
            .filter(|transfer| {
                include_explicit || transfer.destination < count || transfer.source < count
            })
            .collect();
        add_stores(signatures, &operands, transfers, domain, &mut stores);
        for operand in &operands[..count] {
            for (path, ty) in regions::callable_paths(signatures, &operand.ty, true) {
                let Some(value) = domain.project(&operand.value, &path) else {
                    continue;
                };
                let actual = select_arguments(signatures, &ty, &types, &operands, domain);
                pending.push((Operand { ty, value }, actual, true));
            }
        }
    }
    Relations {
        stores: stores.into_iter().collect(),
        unresolved: unresolved.into_iter().collect(),
    }
}

fn add_stores<D: Inputs>(
    signatures: &crate::ElaboratedInterface,
    operands: &[Operand<D::Value>],
    transfers: Vec<regions::ResidentTransfer>,
    domain: &D,
    stores: &mut BTreeSet<Store<D::Value>>,
) {
    for transfer in transfers {
        let (Some(destination), Some(source)) = (
            operands.get(transfer.destination),
            operands.get(transfer.source),
        ) else {
            continue;
        };
        let source_is_callable = regions::callable_paths(signatures, &source.ty, true)
            .iter()
            .any(|(path, _)| crate::core::reference_path_matches(path, &transfer.source_path));
        let (Some(destination), Some(source)) = (
            domain.project(&destination.value, &transfer.destination_path),
            domain.project(&source.value, &transfer.source_path),
        ) else {
            continue;
        };
        stores.insert(Store {
            destination,
            source,
            source_is_callable,
        });
    }
}

fn select_arguments<D: Inputs>(
    signatures: &crate::ElaboratedInterface,
    callable: &Type,
    types: &[Type],
    operands: &[Operand<D::Value>],
    domain: &D,
) -> Vec<Operand<D::Value>> {
    possible_arguments(signatures, callable, types)
        .into_iter()
        .filter_map(|input| {
            domain
                .project(&operands[input.argument].value, &input.path)
                .map(|value| Operand {
                    ty: input.ty,
                    value,
                })
        })
        .collect()
}

/// A generic storage/forwarding function cannot invoke an unconstrained T.
/// Only a declared callable or the intrinsic Fn relation grants that access.
fn invoked_argument_paths(
    signatures: &crate::ElaboratedInterface,
    expression: &CoreExpr,
) -> Vec<(usize, Vec<u32>)> {
    use crate::GenericArgument;
    let Type::Callable { parameters, .. } = &expression.ty else {
        return vec![];
    };
    let mut replacements = vec![];
    let parameters = if let Some((signature, ambient_subjects)) =
        declared_invocation_contract(signatures, expression)
    {
        let callable = Type::Callable {
            contract: Default::default(),
            safety: crate::Safety::Safe,
            lifetime_binders: 0,
            parameters: vec![],
            result: Box::new(Type::Unit),
            effects: crate::EffectRow::empty(),
            invocation: crate::Quantity::ONCE,
        };
        for subject in signature
            .where_bounds
            .iter()
            .filter(|(_, relation)| crate::is_intrinsic_callable_trait(relation))
            .map(|(subject, _)| subject)
            .chain(
                signature
                    .universal_bounds
                    .iter()
                    .filter(|bound| crate::is_intrinsic_callable_trait(&bound.relation))
                    .map(|bound| &bound.subject),
            )
            .chain(ambient_subjects)
        {
            let subject = match subject {
                Type::Reference { referent, .. } => &**referent,
                subject => subject,
            };
            replacements.push((subject.clone(), callable.clone()));
        }
        &signature.parameters
    } else {
        parameters
    };
    parameters
        .iter()
        .enumerate()
        .flat_map(|(argument, parameter)| {
            let GenericArgument::Type(parameter) = crate::CallableContract::replace_value_types(
                GenericArgument::Type(parameter.clone()),
                &replacements,
                0,
            ) else {
                unreachable!("type replacement");
            };
            regions::callable_paths(signatures, &parameter, true)
                .into_iter()
                .map(move |(path, _)| (argument, path))
        })
        .collect()
}

struct Argument {
    argument: usize,
    path: Vec<u32>,
    ty: Type,
}

fn possible_arguments(
    signatures: &crate::ElaboratedInterface,
    callable: &Type,
    arguments: &[Type],
) -> Vec<Argument> {
    use crate::GenericArgument;
    let Type::Callable { parameters, .. } = callable else {
        return vec![];
    };
    fn shape(ty: &Type) -> GenericArgument {
        let mut ty = ty.clone();
        if let Type::Reference { mutability, .. } = &mut ty {
            *mutability = crate::Mutability::Shared;
        }
        crate::types::regions::map_argument_regions(GenericArgument::Type(ty), &mut |_, _| {
            Some(crate::Lifetime::Elided)
        })
        .expect("region erasure does not perform binder arithmetic")
    }
    let mut inputs = vec![];
    for (argument, ty) in arguments.iter().enumerate() {
        let mut leaves = vec![(vec![], ty.clone())];
        let _ = crate::core::input_reference_leaf_paths(signatures, ty, &mut leaves);
        leaves.extend(regions::callable_paths(signatures, ty, true));
        for (path, actual) in leaves {
            for parameter in parameters {
                if matches!(
                    (parameter, &actual),
                    (
                        Type::Reference {
                            mutability: crate::Mutability::Unique,
                            ..
                        },
                        Type::Reference {
                            mutability: crate::Mutability::Shared,
                            ..
                        }
                    )
                ) {
                    continue;
                }
                if shape(parameter) != shape(&actual) {
                    continue;
                }
                if inputs.iter().any(|input: &Argument| {
                    input.argument == argument && input.path == path && input.ty == *parameter
                }) {
                    continue;
                }
                // Candidate selection preserves the formal binder. Erasing it
                // in a store edge would let a fresh HRTB loan enter an older slot.
                inputs.push(Argument {
                    argument,
                    path: path.clone(),
                    ty: parameter.clone(),
                });
            }
        }
    }
    inputs
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{cell::Cell, collections::BTreeMap};
    type Value = (u32, Vec<u32>);
    #[derive(Default)]
    struct Domain {
        captured: BTreeMap<u32, Vec<Operand<Value>>>,
        reads: Cell<usize>,
    }
    impl Inputs for Domain {
        type Value = Value;
        fn project(&self, value: &Value, path: &[u32]) -> Option<Value> {
            Some((value.0, value.1.iter().chain(path).copied().collect()))
        }
        fn captures(&self, callable: &Operand<Value>) -> CapturedInputs<Value> {
            self.reads.set(self.reads.get() + 1);
            CapturedInputs {
                operands: self
                    .captured
                    .get(&callable.value.0)
                    .cloned()
                    .unwrap_or_default(),
                unresolved: !self.captured.contains_key(&callable.value.0),
            }
        }
    }
    fn callable(parameters: Vec<Type>) -> Type {
        Type::Callable {
            contract: Default::default(),
            safety: crate::Safety::Safe,
            lifetime_binders: 0,
            parameters,
            result: Box::new(Type::Unit),
            effects: crate::EffectRow::empty(),
            invocation: crate::Quantity::ONCE,
        }
    }
    fn expression(ty: Type) -> CoreExpr {
        CoreExpr {
            kind: CoreKind::Local("callback".into()),
            ty,
            span: crate::Span {
                file: crate::FileKey(crate::Digest::of_bytes(b"invocation-rules")),
                start: 0,
                end: 1,
            },
        }
    }
    fn reference(lifetime: crate::Lifetime) -> Type {
        Type::Reference {
            lifetime,
            mutability: crate::Mutability::Shared,
            referent: Box::new(Type::Scalar(crate::ScalarType::I64)),
        }
    }
    fn slot(element: Type) -> (crate::ElaboratedInterface, Type) {
        let definition = crate::DefKey(crate::Digest::of_bytes(b"invocation-slot"));
        let mut signatures = crate::ElaboratedInterface::default();
        signatures.definitions.insert(
            definition,
            crate::ElaboratedHeader::Nominal {
                generics: 1,
                generic_kinds: vec![crate::GenericKind::Type],
                layout: crate::ElaboratedNominalLayout::Struct(vec![]),
                contract: Default::default(),
                universal_bounds: vec![],
            },
        );
        (
            signatures,
            Type::Nominal {
                definition,
                arguments: vec![crate::GenericArgument::Type(element)],
            },
        )
    }

    #[test]
    fn explicit_and_captured_inputs_use_one_store_relation() {
        let reference = reference(crate::Lifetime::Elided);
        let (signatures, slot) = slot(reference.clone());
        let mut domain = Domain::default();
        domain.captured.insert(
            0,
            vec![Operand {
                ty: slot,
                value: (1, vec![]),
            }],
        );
        let relations = derive(
            &signatures,
            &expression(callable(vec![reference.clone()])),
            (0, vec![]),
            &[Operand {
                ty: reference,
                value: (2, vec![]),
            }],
            &domain,
        );
        assert_eq!(
            relations.stores,
            vec![Store {
                destination: (1, vec![crate::core::REFERENCE_PATH_LOGICAL_ARGUMENT, 0]),
                source: (2, vec![]),
                source_is_callable: false
            }]
        );
        assert!(relations.unresolved.is_empty());
    }

    #[test]
    fn fresh_callback_binders_do_not_match_older_capture_regions() {
        let captured = reference(crate::Lifetime::Elided);
        let fresh = reference(crate::Lifetime::Bound { depth: 0, index: 0 });
        let (signatures, slot) = slot(captured.clone());
        let mut domain = Domain::default();
        domain.captured.insert(
            0,
            vec![Operand {
                ty: slot,
                value: (1, vec![]),
            }],
        );
        let mut callback = callable(vec![fresh]);
        if let Type::Callable {
            lifetime_binders, ..
        } = &mut callback
        {
            *lifetime_binders = 1;
        }
        let relations = derive(
            &signatures,
            &expression(callback),
            (0, vec![]),
            &[Operand {
                ty: captured,
                value: (2, vec![]),
            }],
            &domain,
        );
        assert!(relations.stores.is_empty());
    }

    #[test]
    fn unknown_capture_coverage_is_distinct_from_a_represented_empty_environment() {
        let signatures = crate::ElaboratedInterface::default();
        let expression = expression(callable(vec![]));
        let mut domain = Domain::default();
        let unknown = derive(&signatures, &expression, (0, vec![]), &[], &domain);
        assert_eq!(unknown.unresolved.len(), 1);
        domain.captured.insert(0, vec![]);
        let known = derive(&signatures, &expression, (0, vec![]), &[], &domain);
        assert!(known.unresolved.is_empty());
    }

    #[test]
    fn nested_invocations_expand_without_recursive_visitors_and_share_cycles() {
        let callback = callable(vec![]);
        let signatures = crate::ElaboratedInterface::default();
        let mut domain = Domain::default();
        for index in 0..10_000 {
            domain.captured.insert(
                index,
                vec![Operand {
                    ty: callback.clone(),
                    value: (index + 1, vec![]),
                }],
            );
        }
        domain.captured.insert(10_000, vec![]);
        let relations = derive(
            &signatures,
            &expression(callback.clone()),
            (0, vec![]),
            &[],
            &domain,
        );
        assert!(relations.stores.is_empty() && relations.unresolved.is_empty());
        assert_eq!(domain.reads.get(), 10_001);
        domain.captured.clear();
        domain.reads.set(0);
        domain.captured.insert(
            0,
            vec![Operand {
                ty: callback.clone(),
                value: (0, vec![]),
            }],
        );
        let relations = derive(
            &signatures,
            &expression(callback),
            (0, vec![]),
            &[],
            &domain,
        );
        assert!(relations.stores.is_empty());
        assert_eq!(domain.reads.get(), 2);
    }

    #[test]
    fn candidate_selection_preserves_formal_regions_and_reference_access() {
        let fresh = reference(crate::Lifetime::Bound { depth: 0, index: 0 });
        let actual = reference(crate::Lifetime::Elided);
        let signatures = crate::ElaboratedInterface::default();
        let inputs = possible_arguments(
            &signatures,
            &callable(vec![fresh.clone()]),
            &[Type::fixed_array(actual.clone(), u64::MAX)],
        );
        assert_eq!(inputs.len(), 1);
        assert_eq!(inputs[0].ty, fresh);
        assert_eq!(
            inputs[0].path,
            vec![crate::core::REFERENCE_PATH_ARRAY_ELEMENT]
        );
        let mut unique = actual.clone();
        if let Type::Reference { mutability, .. } = &mut unique {
            *mutability = crate::Mutability::Unique;
        }
        assert!(possible_arguments(&signatures, &callable(vec![unique]), &[actual]).is_empty());
    }
}
