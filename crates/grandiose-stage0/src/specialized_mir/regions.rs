//! Applying a callable binder creates body-local regions. Bound lifetimes
//! remain bound only inside nested higher-ranked callable types; a function's
//! locals cannot refer back to a binder owned by its producer's signature.
use super::*;

fn lifetime(value: crate::Lifetime, depth: u32) -> crate::Lifetime {
    match value {
        crate::Lifetime::Bound { depth: binder, .. } if binder >= depth => crate::Lifetime::Elided,
        value => value,
    }
}
fn argument(value: &GenericArgument, depth: u32) -> GenericArgument {
    match value {
        GenericArgument::Type(value) => GenericArgument::Type(ty(value, depth)),
        GenericArgument::Lifetime(value) => GenericArgument::Lifetime(lifetime(*value, depth)),
        GenericArgument::EffectRow(value) => GenericArgument::EffectRow(row(value, depth)),
        _ => value.clone(),
    }
}
fn row(value: &crate::EffectRow, depth: u32) -> crate::EffectRow {
    let mut result = value.clone();
    result.effects = result
        .effects
        .into_iter()
        .map(|mut effect| {
            effect.arguments = effect
                .arguments
                .iter()
                .map(|value| argument(value, depth))
                .collect();
            effect
        })
        .collect();
    result
}
fn ty(value: &Type, depth: u32) -> Type {
    match value {
        Type::Reference {
            mutability,
            lifetime: region,
            referent,
        } => Type::Reference {
            mutability: *mutability,
            lifetime: lifetime(*region, depth),
            referent: Box::new(ty(referent, depth)),
        },
        Type::RawPointer {
            mutability,
            pointee,
        } => Type::RawPointer {
            mutability: *mutability,
            pointee: Box::new(ty(pointee, depth)),
        },
        Type::Tuple(fields) => Type::Tuple(fields.iter().map(|value| ty(value, depth)).collect()),
        Type::Array(value) => Type::Array(Box::new(ty(value, depth))),
        Type::FixedArray { element, length } => Type::FixedArray {
            element: Box::new(ty(element, depth)), length: Box::new(argument(length, depth)),
        },
        Type::StaticData {
            tag,
            alignment,
            element,
        } => Type::StaticData {
            tag: *tag,
            alignment: *alignment,
            element: Box::new(ty(element, depth)),
        },
        Type::Nominal {
            definition,
            arguments,
        } => Type::Nominal {
            definition: *definition,
            arguments: arguments
                .iter()
                .map(|value| argument(value, depth))
                .collect(),
        },
        Type::Callable {
            safety,
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => {
            let depth = depth + u32::from(*lifetime_binders != 0);
            Type::Callable {
                safety: *safety,
                lifetime_binders: *lifetime_binders,
                parameters: parameters.iter().map(|value| ty(value, depth)).collect(),
                result: Box::new(ty(result, depth)),
                effects: row(effects, depth),
                invocation: *invocation,
            }
        }
        _ => value.clone(),
    }
}
pub(super) fn body_type(value: &Type) -> Type {
    ty(value, 0)
}
pub(super) fn body_row(value: &crate::EffectRow) -> crate::EffectRow {
    row(value, 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detached_nominal_layout_opens_its_outer_region_without_relaxing_validation() {
        let detached = Type::Nominal {
            definition: DefKey(crate::Digest::of_bytes(b"detached-layout-region")),
            arguments: vec![GenericArgument::Lifetime(crate::Lifetime::Bound { depth: 0, index: 0 })],
        };
        assert!(super::super::validate::closed_type(&detached).is_err());
        let opened = body_type(&detached);
        assert!(matches!(&opened, Type::Nominal { arguments, .. }
            if arguments == &[GenericArgument::Lifetime(crate::Lifetime::Elided)]));
        assert!(super::super::validate::closed_type(&opened).is_ok());
    }

    #[test]
    fn detached_callable_layout_preserves_its_own_nested_binder() {
        let reference = |depth| Type::Reference {
            mutability: crate::Mutability::Shared,
            lifetime: crate::Lifetime::Bound { depth, index: 0 },
            referent: Box::new(Type::Scalar(crate::ScalarType::I64)),
        };
        let detached = Type::Callable {
            safety: crate::Safety::Safe, lifetime_binders: 1,
            parameters: vec![reference(1)], result: Box::new(reference(0)),
            effects: crate::EffectRow::empty(), invocation: crate::Quantity::ONCE,
        };
        assert!(super::super::validate::closed_type(&detached).is_err());
        let opened = body_type(&detached);
        let Type::Callable { parameters, result, lifetime_binders, .. } = &opened else { unreachable!(); };
        assert_eq!(*lifetime_binders, 1);
        assert!(matches!(parameters.as_slice(), [Type::Reference { lifetime: crate::Lifetime::Elided, .. }]));
        assert_eq!(result.as_ref(), &reference(0));
        assert!(super::super::validate::closed_type(&opened).is_ok());
    }
}
