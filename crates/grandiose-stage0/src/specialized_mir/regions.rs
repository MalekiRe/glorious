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
