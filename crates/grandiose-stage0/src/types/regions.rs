//! Capture-avoiding movement of semantic terms under region binders.
//!
//! Every callable node owns a de Bruijn scope, including an empty binder
//! list, matching header elaboration and the frozen type representation.

use super::{EffectRow, GenericArgument, Lifetime, Type};

/// Body-local region identities constrain source loans, not stored bits. A
/// checked store may replace one such loan with another without changing its
/// storage type. Retain rigid/bound regions, mutability and every other type
/// contract; this is not a new outlives proof or callable coercion.
pub(crate) fn same_body_storage(left: &Type, right: &Type) -> bool {
    if left == right { return true; }
    let erase = |value: &Type| map_argument_regions(GenericArgument::Type(value.clone()),
        &mut |region, _| Some(match region {
            Lifetime::Inferred(_) => Lifetime::Elided,
            region => region,
        }));
    matches!((erase(left), erase(right)), (Some(left), Some(right)) if left == right)
}

/// A store consumes a directional callable input view, just like argument
/// transfer. Keep the acquired value's contract intact, and independently
/// compare every other stored type component modulo closed body regions.
pub(crate) fn accepts_body_storage(destination: &Type, source: &Type) -> bool {
    same_body_storage(destination, &super::CallableContract::invocation_input_view(destination, source.clone()))
}

/// Move a caller-owned argument beneath `amount` additional scopes. Regions
/// bound inside the argument keep their identity; only its free bound regions
/// move. Overflow is rejected instead of wrapping into a different binder.
pub(crate) fn shift_argument(
    argument: GenericArgument,
    amount: u32,
) -> Option<GenericArgument> {
    map_argument_regions(argument, &mut |value, cutoff| {
        Some(match value {
            Lifetime::Bound { depth, index } if depth >= cutoff =>
                Lifetime::Bound { depth: depth.checked_add(amount)?, index },
            value => value,
        })
    })
}

pub(crate) fn shift_type_argument(value: Type, amount: u32) -> Option<Type> {
    let GenericArgument::Type(value) = shift_argument(GenericArgument::Type(value), amount)? else { return None; };
    Some(value)
}

pub(crate) fn map_argument_regions(
    mut argument: GenericArgument,
    map: &mut dyn FnMut(Lifetime, u32) -> Option<Lifetime>,
) -> Option<GenericArgument> {
    map_argument_at(&mut argument, 0, map)?;
    Some(argument)
}

/// Remove one containing binder, replacing its regions with caller-provided
/// identities. Inner binders stay closed; references to outer scopes move up.
pub(crate) fn open_argument(
    argument: GenericArgument,
    mut region: impl FnMut(u32) -> Option<Lifetime>,
) -> Option<GenericArgument> {
    map_argument_regions(argument, &mut |value, cutoff| {
        Some(match value {
            Lifetime::Bound { depth, index } if depth == cutoff => match region(index)? {
                Lifetime::Bound { depth, index } => Lifetime::Bound { depth: depth.checked_add(cutoff)?, index },
                value => value,
            },
            Lifetime::Bound { depth, index } if depth > cutoff => Lifetime::Bound { depth: depth - 1, index },
            value => value,
        })
    })
}

fn map_argument_at(argument: &mut GenericArgument, cutoff: u32, map: &mut dyn FnMut(Lifetime, u32) -> Option<Lifetime>) -> Option<()> {
    match argument {
        GenericArgument::Type(value) => map_type(value, cutoff, map)?,
        GenericArgument::Lifetime(value) => *value = map(*value, cutoff)?,
        GenericArgument::EffectRow(value) => map_row(value, cutoff, map)?,
        GenericArgument::ConstProjection { subject, trait_arguments, .. } => {
            map_type(subject, cutoff, map)?;
            map_arguments(trait_arguments, cutoff, map)?;
        }
        GenericArgument::ConstInteger(_)
        | GenericArgument::ConstIntegerExpr(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstInfer { .. } => {}
    }
    Some(())
}

fn map_arguments(arguments: &mut [GenericArgument], cutoff: u32, map: &mut dyn FnMut(Lifetime, u32) -> Option<Lifetime>) -> Option<()> {
    for argument in arguments {
        map_argument_at(argument, cutoff, map)?;
    }
    Some(())
}

fn map_row(row: &mut EffectRow, cutoff: u32, map: &mut dyn FnMut(Lifetime, u32) -> Option<Lifetime>) -> Option<()> {
    // Effect identity is ordered by its arguments. Reinsert transformed
    // instances rather than mutating keys in an ordered collection.
    for mut effect in std::mem::take(&mut row.effects) {
        map_arguments(&mut effect.arguments, cutoff, map)?;
        row.effects.insert(effect);
    }
    for projection in &mut row.projections {
        map_type(&mut projection.subject, cutoff, map)?;
        map_arguments(&mut projection.trait_arguments, cutoff, map)?;
        map_arguments(&mut projection.item_arguments, cutoff, map)?;
    }
    row.canonicalize();
    Some(())
}

fn map_type(value: &mut Type, cutoff: u32, map: &mut dyn FnMut(Lifetime, u32) -> Option<Lifetime>) -> Option<()> {
    match value {
        Type::FixedArray { element, length } => {
            map_type(element, cutoff, map)?;
            map_argument_at(length, cutoff, map)?;
        }
        Type::Nominal { arguments, .. } => map_arguments(arguments, cutoff, map)?,
        Type::Projection { subject, trait_arguments, item_arguments, .. } => {
            map_type(subject, cutoff, map)?;
            map_arguments(trait_arguments, cutoff, map)?;
            map_arguments(item_arguments, cutoff, map)?;
        }
        Type::Tuple(values) => {
            for value in values {
                map_type(value, cutoff, map)?;
            }
        }
        Type::Array(value)
        | Type::StaticData { element: value, .. }
        | Type::RawPointer { pointee: value, .. } => map_type(value, cutoff, map)?,
        Type::Reference { lifetime, referent, .. } => {
            *lifetime = map(*lifetime, cutoff)?;
            map_type(referent, cutoff, map)?;
        }
        Type::Callable { contract, parameters, result, effects, .. } => {
            let cutoff = cutoff.checked_add(1)?;
            **contract = contract.try_map_terms(|mut argument, extra| {
                map_argument_at(&mut argument, cutoff.checked_add(extra).ok_or(())?, map).ok_or(())?;
                Ok::<_, ()>(argument)
            }).ok()?;
            for parameter in parameters {
                map_type(parameter, cutoff, map)?;
            }
            map_type(result, cutoff, map)?;
            map_row(effects, cutoff, map)?;
        }
        Type::Unit | Type::Never | Type::Scalar(_) | Type::ConstInteger(_)
        | Type::ConstQuantity(_) | Type::ConstGeneric { .. } | Type::Generic(_)
        | Type::Infer(_) | Type::Error => {}
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{DefKey, Digest, EffectRowProjection, GenericKind, Mutability, Quantity, Safety};

    #[test]
    fn stored_loan_regions_do_not_erase_rigid_or_callable_contracts() {
        let owner = DefKey(Digest::of_bytes(b"stored-loan-regions"));
        let reference = |index| Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Inferred(crate::types::BodyRegion { owner, index }),
            referent: Box::new(Type::Unit),
        };
        let first = reference(0);
        let second = reference(1);
        assert!(same_body_storage(&first, &second));
        assert!(same_body_storage(&Type::Tuple(vec![first.clone()]), &Type::Tuple(vec![second.clone()])));
        for rigid in [Lifetime::Static, Lifetime::Generic(0), Lifetime::Bound { depth: 0, index: 0 }] {
            let mut changed = second.clone();
            let Type::Reference { lifetime, .. } = &mut changed else { unreachable!() };
            *lifetime = rigid;
            assert!(!same_body_storage(&first, &changed));
        }
        let mut unique = second;
        let Type::Reference { mutability, .. } = &mut unique else { unreachable!() };
        *mutability = Mutability::Unique;
        assert!(!same_body_storage(&first, &unique));
        let callable = Type::Callable { contract: Default::default(), safety: Safety::Safe,
            lifetime_binders: 0, parameters: vec![first], result: Box::new(Type::Unit),
            effects: EffectRow::empty(), invocation: Quantity::ONCE };
        let mut changed = callable.clone();
        let Type::Callable { safety, .. } = &mut changed else { unreachable!() };
        *safety = Safety::Unsafe;
        assert!(!same_body_storage(&callable, &changed));
        let mut changed = callable.clone();
        let Type::Callable { contract, .. } = &mut changed else { unreachable!() };
        contract.shared_receiver = true;
        assert!(!same_body_storage(&callable, &changed));
    }

    #[test]
    fn stored_callable_input_views_are_directional_and_do_not_coerce_referents() {
        let once = Type::Callable { contract: Default::default(), safety: Safety::Safe,
            lifetime_binders: 0, parameters: vec![Type::Unit], result: Box::new(Type::Unit),
            effects: EffectRow::empty(), invocation: Quantity::ONCE };
        let mut reusable = once.clone();
        let Type::Callable { invocation, .. } = &mut reusable else { unreachable!() };
        *invocation = Quantity::UNRESTRICTED;
        for wrap in [
            (|ty| ty) as fn(Type) -> Type,
            |ty| Type::Tuple(vec![ty, Type::Unit]),
            |ty| Type::FixedArray { element: Box::new(ty), length: Box::new(GenericArgument::ConstInteger(2.into())) },
        ] {
            assert!(accepts_body_storage(&wrap(once.clone()), &wrap(reusable.clone())));
            assert!(!accepts_body_storage(&wrap(reusable.clone()), &wrap(once.clone())));
        }
        for mutability in [Mutability::Shared, Mutability::Unique] {
            let wrap = |ty| Type::Reference { mutability, lifetime: Lifetime::Elided, referent: Box::new(ty) };
            assert!(!accepts_body_storage(&wrap(once.clone()), &wrap(reusable.clone())));
        }
        let mut stronger = once.clone();
        let Type::Callable { contract, .. } = &mut stronger else { unreachable!() };
        contract.shared_receiver = true;
        assert!(!accepts_body_storage(&stronger, &reusable));
        let mut unsafe_value = reusable.clone();
        let Type::Callable { safety, .. } = &mut unsafe_value else { unreachable!() };
        *safety = Safety::Unsafe;
        assert!(!accepts_body_storage(&once, &unsafe_value));
    }

    fn region(depth: u32, index: u32) -> GenericArgument {
        GenericArgument::Lifetime(Lifetime::Bound { depth, index })
    }

    fn reference(depth: u32) -> Type {
        Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Bound { depth, index: 0 },
            referent: Box::new(Type::Unit),
        }
    }

    #[test]
    fn opening_removes_only_its_own_scope_and_avoids_capturing_replacements() {
        let argument = GenericArgument::Type(Type::Callable { contract: Default::default(),
            safety: Safety::Safe, lifetime_binders: 1,
            parameters: vec![reference(0), reference(1), reference(2)],
            result: Box::new(Type::Unit), effects: EffectRow::empty(), invocation: Quantity::ONCE,
        });
        let GenericArgument::Type(Type::Callable { parameters, .. }) = open_argument(argument, |_| {
            Some(Lifetime::Bound { depth: 3, index: 0 })
        }).unwrap() else { panic!("callable") };
        assert_eq!(parameters, [reference(0), reference(4), reference(1)]);
        assert!(open_argument(region(0, 2), |_| None).is_none());
    }

    #[test]
    fn shifting_preserves_internal_binders_and_moves_only_free_regions() {
        for lifetime_binders in [0, 1] {
            let argument = GenericArgument::Type(Type::Callable { contract: Default::default(),
                safety: Safety::Safe, lifetime_binders,
                parameters: vec![reference(0), reference(1)],
                result: Box::new(reference(2)), effects: EffectRow::empty(), invocation: Quantity::ONCE,
            });
            let GenericArgument::Type(Type::Callable { parameters, result, .. }) = shift_argument(argument, 2).unwrap() else { panic!("callable") };
            assert_eq!(parameters, [reference(0), reference(3)]);
            assert_eq!(*result, reference(4));
        }
    }

    #[test]
    fn shifting_traverses_const_and_row_projection_arguments_and_static_data() {
        let definition = DefKey(Digest::of_bytes(b"region-projection"));
        let mut row = EffectRow::empty();
        row.projections.push(EffectRowProjection {
            subject: Box::new(Type::StaticData { element: Box::new(reference(0)), tag: 3, alignment: 8 }),
            trait_definition: definition, trait_arguments: vec![region(0, 2)],
            name: "Effects".into(), item_generic_kinds: vec![GenericKind::Lifetime],
            item_arguments: vec![region(0, 3)],
        });
        let argument = GenericArgument::ConstProjection {
            subject: Box::new(reference(0)), trait_definition: definition,
            trait_arguments: vec![GenericArgument::EffectRow(row)], name: "Value".into(), kind: crate::ConstKind::U32,
        };
        let GenericArgument::ConstProjection { subject, trait_arguments, .. } = shift_argument(argument, 1).unwrap() else { panic!("const projection") };
        assert_eq!(*subject, reference(1));
        let GenericArgument::EffectRow(row) = &trait_arguments[0] else { panic!("row") };
        let projection = &row.projections[0];
        assert_eq!(projection.trait_arguments, [region(1, 2)]);
        assert_eq!(projection.item_arguments, [region(1, 3)]);
        assert!(matches!(projection.subject.as_ref(), Type::StaticData { element, .. } if element.as_ref() == &reference(1)));
    }

    #[test]
    fn shifting_rejects_depth_overflow_and_leaves_nonbound_regions_alone() {
        assert!(shift_argument(region(u32::MAX, 0), 1).is_none());
        for lifetime in [Lifetime::Static, Lifetime::Generic(0), Lifetime::Elided] {
            let argument = GenericArgument::Lifetime(lifetime);
            assert_eq!(shift_argument(argument.clone(), 1), Some(argument));
        }
    }
}
