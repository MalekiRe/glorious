//! Opening a shell requires proof that no custom destructor can observe it.
//! A failed positive trait query for an open template is not that proof: a
//! later substitution may satisfy a conditional implementation.

use super::*;

/// Positive absence of executable cleanup for a source resident. Open or
/// unavailable layouts are not the concrete planner's "not demanded yet"
/// result. This query uses the same custom-Drop selection and owned structural
/// layout as destruction planning; references never own their referents.
pub(crate) fn cleanup_is_trivial(
    signatures: &ElaboratedInterface, solver: &mut TraitSolver, ty: &Type,
    assumptions: &[TraitGoal], stateless_callable: bool,
) -> bool {
    fn visit(signatures: &ElaboratedInterface, solver: &mut TraitSolver, ty: &Type,
        assumptions: &[TraitGoal], stateless_callable: bool, active: &mut BTreeSet<Vec<u8>>,
    ) -> bool {
        if active.len() >= 128 { return false; }
        let Ok(ty) = solver.normalize_type(ty.clone()) else { return false; };
        // Generative labels are proof values, not owners of their payload.
        if crate::types::label::payload(&ty).is_some() { return true; }
        let key = crate::types::canonical_type_encoding(&ty);
        if !active.insert(key.clone()) { return false; }
        let trivial = !custom_drop_may_apply(signatures, solver, &ty, assumptions) && match &ty {
            Type::Tuple(fields) => fields.iter().all(|ty| visit(signatures, solver, ty, assumptions, false, active)),
            Type::Nominal { definition, .. } if *definition == crate::refinement::bindings_definition() =>
                crate::refinement::binding_pack_fields(&ty).is_some_and(|fields| fields.iter()
                    .all(|ty| visit(signatures, solver, ty, assumptions, false, active))),
            Type::Nominal { definition, arguments } => match signatures.definitions.get(definition) {
                Some(ElaboratedHeader::Nominal { layout, .. }) => crate::mir::instantiate_nominal_copy_layout(layout, arguments)
                    .is_some_and(|variants| variants.iter().flatten().all(|ty| visit(signatures, solver, ty, assumptions, false, active))),
                _ => false,
            },
            Type::FixedArray { .. } if ty.fixed_array_length() == Some(0) => true,
            Type::Array(element) | Type::FixedArray { element, .. } => visit(signatures, solver, element, assumptions, false, active),
            Type::Callable { contract, .. } => stateless_callable || (contract.environment.is_some()
                && contract.captures.iter().all(|ty| visit(signatures, solver, ty, assumptions, false, active))),
            Type::Unit | Type::Never | Type::Scalar(_) | Type::Reference { .. }
            | Type::RawPointer { .. } | Type::StaticData { .. } => true,
            _ => false,
        };
        active.remove(&key);
        trivial
    }
    visit(signatures, solver, ty, assumptions, stateless_callable, &mut BTreeSet::new())
}

pub(crate) fn custom_drop_may_apply(
    signatures: &ElaboratedInterface,
    solver: &mut TraitSolver,
    ty: &Type,
    assumptions: &[TraitGoal],
) -> bool {
    let Ok(ty) = solver.normalize_type(ty.clone()) else {
        return true;
    };
    let drop = crate::resolution::language_drop_trait_definition();
    match solver.solve_with_assumptions(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: drop,
                arguments: vec![],
            },
            subject: ty.clone(),
        },
        assumptions,
    ) {
        TraitAnswer::Refuted { .. } => false,
        TraitAnswer::NoSolution => {
            has_open_selection(&ty)
                && signatures.definitions.values().any(|header| {
                    let ElaboratedHeader::Implementation(implementation) = header else {
                        return false;
                    };
                    implementation.relation.definition == drop
                        && heads_can_match(&ty, &implementation.self_ty)
                })
        }
        TraitAnswer::Proven { .. } | TraitAnswer::Ambiguous | TraitAnswer::Overflow => true,
    }
}

fn heads_can_match(left: &Type, right: &Type) -> bool {
    match (left, right) {
        (_, Type::Generic(_) | Type::Projection { .. })
        | (Type::Generic(_) | Type::Projection { .. }, _) => true,
        (
            Type::Nominal {
                definition: left, ..
            },
            Type::Nominal {
                definition: right, ..
            },
        ) => left == right,
        (Type::Tuple(left), Type::Tuple(right)) => left.len() == right.len(),
        _ => std::mem::discriminant(left) == std::mem::discriminant(right),
    }
}

fn has_open_selection(ty: &Type) -> bool {
    match ty {
        Type::Generic(_)
        | Type::Projection { .. }
        | Type::Infer(_)
        | Type::Error
        | Type::ConstGeneric { .. } => true,
        Type::Nominal { arguments, .. } => arguments.iter().any(argument_is_open),
        Type::FixedArray { element, length } => {
            has_open_selection(element) || argument_is_open(length)
        }
        Type::Tuple(fields) => fields.iter().any(has_open_selection),
        Type::Array(element)
        | Type::StaticData { element, .. }
        | Type::Reference {
            referent: element, ..
        }
        | Type::RawPointer {
            pointee: element, ..
        } => has_open_selection(element),
        Type::Callable {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters.iter().any(has_open_selection)
                || has_open_selection(result)
                || row_is_open(effects)
        }
        _ => false,
    }
}

fn argument_is_open(argument: &GenericArgument) -> bool {
    match argument {
        GenericArgument::Type(ty) => has_open_selection(ty),
        GenericArgument::EffectRow(row) => row_is_open(row),
        GenericArgument::Lifetime(_)
        | GenericArgument::ConstInteger(_)
        | GenericArgument::ConstQuantity(_) => false,
        GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstInfer { .. }
        | GenericArgument::ConstProjection { .. }
        | GenericArgument::ConstIntegerExpr(_) => true,
    }
}

fn row_is_open(row: &crate::EffectRow) -> bool {
    !row.tails.is_empty()
        || !row.projections.is_empty()
        || row
            .effects
            .iter()
            .any(|effect| effect.arguments.iter().any(argument_is_open))
}
