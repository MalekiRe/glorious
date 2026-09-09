//! Compiler-created nominal label types. The payload is an ordinary mapped
//! type term; the invariant brand is an opaque nominal identity, never an ABI
//! refinement that can be joined onto an unrelated function value.
use super::{GenericArgument, Type};
use crate::{DefKey, Digest, LabelBrand};

fn definition() -> DefKey {
    DefKey(Digest::of_bytes(b"grandiose-intrinsic-label-type-v1"))
}

pub(crate) fn new(brand: LabelBrand, payload: Type) -> Type {
    let identity = DefKey(Digest::of_parts([
        b"grandiose-generative-label-brand-v1".as_slice(),
        brand.owner.0.as_bytes().as_slice(),
        brand.label.to_le_bytes().as_slice(),
    ]));
    Type::Nominal {
        definition: definition(),
        arguments: vec![
            GenericArgument::Type(Type::Nominal {
                definition: identity,
                arguments: vec![],
            }),
            GenericArgument::Type(payload),
        ],
    }
}

pub(crate) fn payload(ty: &Type) -> Option<&Type> {
    let Type::Nominal {
        definition: actual,
        arguments,
    } = ty
    else {
        return None;
    };
    if *actual != definition() {
        return None;
    }
    let [
        GenericArgument::Type(Type::Nominal {
            arguments: brand, ..
        }),
        GenericArgument::Type(payload),
    ] = arguments.as_slice()
    else {
        return None;
    };
    brand.is_empty().then_some(payload)
}

pub(crate) fn matches_brand(ty: &Type, brand: LabelBrand) -> bool {
    payload(ty).is_some_and(|payload| *ty == new(brand, payload.clone()))
}

/// A label supplies intrinsic Fn evidence, but this view is not its nominal
/// type and must not replace the type stored on its value or generic argument.
pub(crate) fn callable(ty: &Type) -> Option<Type> {
    let GenericArgument::Type(payload) =
        super::regions::shift_argument(GenericArgument::Type(payload(ty)?.clone()), 1)?
    else {
        return None;
    };
    Some(Type::Callable {
        contract: Default::default(),
        safety: crate::Safety::Safe,
        lifetime_binders: 0,
        parameters: vec![payload],
        result: Box::new(Type::Never),
        effects: super::EffectRow::empty(),
        invocation: crate::Quantity::ONCE,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn brand(label: u32) -> LabelBrand {
        LabelBrand {
            owner: DefKey(Digest::of_bytes(b"nominal label tests")),
            label,
        }
    }

    #[test]
    fn generative_identity_is_invariant_and_not_a_callable_refinement() {
        let first = new(brand(0), Type::Unit);
        let second = new(brand(1), Type::Unit);
        let callable = callable(&first).unwrap();
        assert_ne!(
            super::super::canonical_type_encoding(&first),
            super::super::canonical_type_encoding(&second)
        );
        for (left, right) in [
            (first.clone(), second),
            (first.clone(), callable.clone()),
            (callable, first.clone()),
        ] {
            assert!(crate::InferContext::default().unify(left, right).is_err());
        }
        assert!(matches_brand(&first, brand(0)));
        assert!(!matches_brand(&first, brand(1)));
        assert_eq!(
            crate::InferContext::default()
                .unify(first.clone(), first.clone())
                .unwrap(),
            first
        );
    }

    #[test]
    fn fn_view_does_not_capture_the_payloads_outer_region_binder() {
        let payload = Type::Reference {
            mutability: crate::Mutability::Shared,
            lifetime: crate::Lifetime::Bound { depth: 0, index: 0 },
            referent: Box::new(Type::Unit),
        };
        let Type::Callable { parameters, .. } = callable(&new(brand(0), payload.clone())).unwrap()
        else {
            unreachable!()
        };
        assert!(matches!(
            &parameters[0],
            Type::Reference {
                lifetime: crate::Lifetime::Bound { depth: 1, index: 0 },
                ..
            }
        ));
        let opened = super::super::regions::open_argument(
            GenericArgument::Type(parameters[0].clone()),
            |_| None,
        )
        .unwrap();
        assert_eq!(opened, GenericArgument::Type(payload));
    }

    #[test]
    fn generic_payload_substitution_preserves_the_opaque_brand() {
        let value = new(brand(0), Type::Generic(0));
        let crate::GenericArgument::Type(value) =
            crate::signature::substitute_trait_generic_argument(
                GenericArgument::Type(value),
                &[GenericArgument::Type(Type::Unit)],
            )
        else {
            unreachable!()
        };
        assert_eq!(value, new(brand(0), Type::Unit));
        assert_eq!(payload(&value), Some(&Type::Unit));
        assert_eq!(payload(&Type::Unit), None);
    }

    #[test]
    fn concrete_and_assumed_labels_share_unrestricted_use_evidence() {
        let source = "pub fn main() {}";
        let package = crate::PackageKey("label-use-evidence@0.1.0".into());
        let lexed =
            crate::LexedFile::lex(crate::FileKey::new(&package, "src/main.glorious"), source);
        let scan = crate::DeclarationScan::scan(&lexed, source);
        let interface =
            crate::InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
        let signatures = crate::ElaboratedInterface::elaborate(&interface);
        let concrete = new(brand(0), Type::Unit);
        assert_eq!(
            signatures.principal_use_interval(&concrete),
            Some(crate::Quantity::UNRESTRICTED)
        );
        let solver = crate::TraitSolver::new(&signatures);
        let assumptions = [crate::TraitGoal {
            subject: Type::Generic(0),
            relation: crate::ElaboratedTraitReference {
                definition: crate::intrinsic_label_trait_definition(),
                arguments: vec![GenericArgument::Type(Type::Unit)],
            },
        }];
        assert_eq!(
            solver.principal_use_with_assumptions(&Type::Generic(0), &assumptions),
            Some(crate::Quantity::UNRESTRICTED)
        );
        assert_eq!(
            solver.principal_use_with_assumptions(&concrete, &[]),
            Some(crate::Quantity::UNRESTRICTED)
        );
    }
}
