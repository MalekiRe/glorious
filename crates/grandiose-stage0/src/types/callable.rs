//! Callable evidence that survives ordinary value storage and substitution.

use super::{GenericArgument, Type};

/// Refinements of the ordinary callable ABI. An absent refinement is not
/// authority for a borrowed receiver; it promises only owned invocation.
/// Residual predicates remain attached to the value until its invocation
/// establishes them. Environment identities are compiler-created and cannot
/// be manufactured by a same-spelled source relation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallableContract {
    pub environment: Option<Box<Type>>,
    pub after_environment: Option<Box<Type>>,
    /// Capture types retain free regions even when the ABI does not mention
    /// them in its arguments or result.
    pub captures: Vec<Type>,
    /// Existential facts retained by the callable's free value terms,
    /// including capture-storage borrows in its result. These are checked
    /// environment guarantees, not residual call prerequisites.
    pub(crate) body_regions: super::BodyRegionConstraints,
    pub shared_receiver: bool,
    pub unique_receiver: bool,
    pub residual: crate::AssociatedItemContract,
    pub universal: Vec<crate::QuantifiedWhereBound>,
}

impl Default for CallableContract {
    fn default() -> Self {
        Self {
            environment: None, after_environment: None, captures: vec![],
            body_regions: Default::default(),
            shared_receiver: false, unique_receiver: false,
            residual: crate::AssociatedItemContract::default(), universal: vec![],
        }
    }
}

#[cfg(test)]
mod abi_refinement_tests {
    use super::*;
    use crate::{EffectRow, Lifetime, Mutability, Quantity, Safety};

    fn reference(lifetime: Lifetime, referent: Type) -> Type {
        Type::Reference { mutability: Mutability::Shared, lifetime, referent: Box::new(referent) }
    }

    #[test]
    fn assignment_refinement_preserves_reference_regions_and_the_declared_callable_abi() {
        let function = |lifetime, contract| Type::Callable { contract: Box::new(contract), safety: Safety::Safe,
            lifetime_binders: 0, parameters: vec![reference(lifetime, Type::Unit)], result: Box::new(Type::Unit),
            effects: EffectRow::empty(), invocation: Quantity::ONCE };
        let previous = reference(Lifetime::Elided, function(Lifetime::Static, CallableContract::default()));
        let mut resident = CallableContract::default();
        resident.captures.push(Type::Unit);
        let aligned = reference(Lifetime::Generic(0), function(Lifetime::Elided, resident.clone()));
        let refined = CallableContract::retain_abi_with_refinements(previous, &aligned);
        assert_eq!(refined, reference(Lifetime::Elided, function(Lifetime::Static, resident)));
        assert_eq!(CallableContract::retain_abi_with_refinements(reference(Lifetime::Elided, Type::Unit),
            &reference(Lifetime::Generic(0), Type::Unit)), reference(Lifetime::Elided, Type::Unit));
    }
}

impl CallableContract {
    /// A successful assignment may join resident callable refinements. That
    /// is not permission to replace the destination's declared ABI or its
    /// reference regions with the temporary aligned view used by unification.
    pub(crate) fn retain_abi_with_refinements(previous: Type, joined: &Type) -> Type {
        let argument = |previous, joined: &GenericArgument| match (previous, joined) {
            (GenericArgument::Type(previous), GenericArgument::Type(joined)) =>
                GenericArgument::Type(Self::retain_abi_with_refinements(previous, joined)),
            (previous, _) => previous,
        };
        match (previous, joined) {
            (Type::Callable { contract: _, safety, lifetime_binders, parameters, result, effects, invocation },
             Type::Callable { contract, parameters: joined_parameters, result: joined_result, .. }) if parameters.len() == joined_parameters.len() => Type::Callable {
                contract: contract.clone(), safety, lifetime_binders,
                parameters: parameters.into_iter().zip(joined_parameters).map(|(previous, joined)| Self::retain_abi_with_refinements(previous, joined)).collect(),
                result: Box::new(Self::retain_abi_with_refinements(*result, joined_result)), effects, invocation,
            },
            (Type::Reference { mutability, lifetime, referent }, Type::Reference { referent: joined, .. }) => Type::Reference {
                mutability, lifetime, referent: Box::new(Self::retain_abi_with_refinements(*referent, joined)),
            },
            (Type::RawPointer { mutability, pointee }, Type::RawPointer { pointee: joined, .. }) => Type::RawPointer {
                mutability, pointee: Box::new(Self::retain_abi_with_refinements(*pointee, joined)),
            },
            (Type::Nominal { definition, arguments }, Type::Nominal { definition: other, arguments: joined })
                if definition == *other && arguments.len() == joined.len() => Type::Nominal {
                    definition, arguments: arguments.into_iter().zip(joined).map(|(previous, joined)| argument(previous, joined)).collect(),
                },
            (Type::Tuple(fields), Type::Tuple(joined)) if fields.len() == joined.len() => Type::Tuple(fields.into_iter().zip(joined)
                .map(|(previous, joined)| Self::retain_abi_with_refinements(previous, joined)).collect()),
            (Type::Array(element), Type::Array(joined)) => Type::Array(Box::new(Self::retain_abi_with_refinements(*element, joined))),
            (Type::FixedArray { element, length }, Type::FixedArray { element: joined, .. }) => Type::FixedArray {
                element: Box::new(Self::retain_abi_with_refinements(*element, joined)), length,
            },
            (Type::StaticData { element, tag, alignment }, Type::StaticData { element: joined, .. }) => Type::StaticData {
                element: Box::new(Self::retain_abi_with_refinements(*element, joined)), tag, alignment,
            },
            (previous, _) => previous,
        }
    }

    /// Replace complete callable refinements without changing ABI structure
    /// or binding any type/region cell. The replacement terms are shifted
    /// under nested callable and predicate binders to avoid capture.
    pub(crate) fn replace_value_types(argument: GenericArgument, replacements: &[(Type, Type)], depth: u32) -> GenericArgument {
        fn ty(value: Type, pairs: &[(Type, Type)], depth: u32) -> Type {
            for (from, to) in pairs {
                let Some(GenericArgument::Type(from)) = super::regions::shift_argument(GenericArgument::Type(from.clone()), depth) else { continue; };
                if value == from {
                    if let Some(GenericArgument::Type(to)) = super::regions::shift_argument(GenericArgument::Type(to.clone()), depth) { return to; }
                }
            }
            let arg = |value| CallableContract::replace_value_types(value, pairs, depth);
            match value {
                Type::Nominal { definition, arguments } => Type::Nominal { definition, arguments: arguments.into_iter().map(arg).collect() },
                Type::Projection { subject, trait_definition, trait_arguments, name, item_generic_kinds, item_arguments } => Type::Projection {
                    subject: Box::new(ty(*subject, pairs, depth)), trait_definition,
                    trait_arguments: trait_arguments.into_iter().map(arg).collect(), name, item_generic_kinds,
                    item_arguments: item_arguments.into_iter().map(arg).collect(),
                },
                Type::Tuple(values) => Type::Tuple(values.into_iter().map(|value| ty(value, pairs, depth)).collect()),
                Type::Array(value) => Type::Array(Box::new(ty(*value, pairs, depth))),
                Type::FixedArray { element, length } => Type::FixedArray { element: Box::new(ty(*element, pairs, depth)), length: Box::new(arg(*length)) },
                Type::Reference { mutability, lifetime, referent } => Type::Reference { mutability, lifetime, referent: Box::new(ty(*referent, pairs, depth)) },
                Type::RawPointer { mutability, pointee } => Type::RawPointer { mutability, pointee: Box::new(ty(*pointee, pairs, depth)) },
                Type::StaticData { element, tag, alignment } => Type::StaticData { element: Box::new(ty(*element, pairs, depth)), tag, alignment },
                Type::Callable { contract, safety, lifetime_binders, parameters, result, effects, invocation } => Type::Callable {
                    contract: Box::new(contract.map_terms(|value, extra| CallableContract::replace_value_types(value, pairs, depth + 1 + extra))),
                    safety, lifetime_binders, parameters: parameters.into_iter().map(|value| ty(value, pairs, depth + 1)).collect(),
                    result: Box::new(ty(*result, pairs, depth + 1)), effects: row(effects, pairs, depth + 1), invocation,
                },
                value => value,
            }
        }
        fn row(mut value: super::EffectRow, pairs: &[(Type, Type)], depth: u32) -> super::EffectRow {
            value.effects = value.effects.into_iter().map(|mut effect| {
                effect.arguments = effect.arguments.into_iter().map(|value| CallableContract::replace_value_types(value, pairs, depth)).collect(); effect
            }).collect();
            for projection in &mut value.projections {
                projection.subject = Box::new(ty((*projection.subject).clone(), pairs, depth));
                projection.trait_arguments = projection.trait_arguments.iter().cloned().map(|value| CallableContract::replace_value_types(value, pairs, depth)).collect();
                projection.item_arguments = projection.item_arguments.iter().cloned().map(|value| CallableContract::replace_value_types(value, pairs, depth)).collect();
            }
            value.canonicalized()
        }
        match argument {
            GenericArgument::Type(value) => GenericArgument::Type(ty(value, replacements, depth)),
            GenericArgument::EffectRow(value) => GenericArgument::EffectRow(row(value, replacements, depth)),
            GenericArgument::ConstProjection { subject, trait_definition, trait_arguments, name, kind } => GenericArgument::ConstProjection {
                subject: Box::new(ty(*subject, replacements, depth)), trait_definition,
                trait_arguments: trait_arguments.into_iter().map(|value| Self::replace_value_types(value, replacements, depth)).collect(), name, kind,
            },
            value => value,
        }
    }

    pub(crate) fn open(&self, mut region: impl FnMut(u32) -> Option<super::Lifetime>) -> Option<Self> {
        self.try_map_terms(|argument, extra| {
            super::regions::map_argument_regions(argument, &mut |value, nested| {
                let cutoff = nested.checked_add(extra)?;
                Some(match value {
                    super::Lifetime::Bound { depth, index } if depth == cutoff => match region(index)? {
                        super::Lifetime::Bound { depth, index } => super::Lifetime::Bound { depth: depth.checked_add(cutoff)?, index },
                        value => value,
                    },
                    super::Lifetime::Bound { depth, index } if depth > cutoff => super::Lifetime::Bound { depth: depth - 1, index },
                    value => value,
                })
            }).ok_or(())
        }).ok()
    }

    pub(crate) fn is_empty(&self) -> bool { self == &Self::default() }

    pub(crate) fn has_residual(&self) -> bool {
        self.residual != crate::AssociatedItemContract::default() || !self.universal.is_empty()
    }

    /// A value join promises only access common to both alternatives, but
    /// retains every capture region and every possible invocation obligation.
    /// An absent structural annotation is not a second concrete alternative.
    pub(crate) fn join(&self, other: &Self) -> Self {
        if self.is_empty() { return other.clone(); }
        if other.is_empty() || self == other { return self.clone(); }
        fn union<T: Clone + PartialEq>(left: &[T], right: &[T]) -> Vec<T> {
            let mut result = left.to_vec();
            for item in right { if !result.contains(item) { result.push(item.clone()); } }
            result
        }
        Self {
            environment: (self.environment == other.environment).then(|| self.environment.clone()).flatten(),
            after_environment: (self.after_environment == other.after_environment).then(|| self.after_environment.clone()).flatten(),
            captures: union(&self.captures, &other.captures),
            body_regions: self.body_regions.union(&other.body_regions),
            shared_receiver: self.shared_receiver && other.shared_receiver,
            unique_receiver: self.unique_receiver && other.unique_receiver,
            residual: crate::AssociatedItemContract {
                where_bounds: union(&self.residual.where_bounds, &other.residual.where_bounds),
                where_outlives: union(&self.residual.where_outlives, &other.residual.where_outlives),
                type_bindings: union(&self.residual.type_bindings, &other.residual.type_bindings),
                effect_bindings: union(&self.residual.effect_bindings, &other.residual.effect_bindings),
            },
            universal: union(&self.universal, &other.universal),
        }
    }

    /// Map complete, kind-preserving terms. `extra_binders` is one only for a
    /// quantified residual predicate; inserted caller terms must remain
    /// outside that predicate's local region scope.
    pub(crate) fn map_terms(&self, mut map: impl FnMut(GenericArgument, u32) -> GenericArgument) -> Self {
        self.map_scoped_terms(|value, scopes| map(value, scopes.len() as u32))
    }

    pub(crate) fn map_scoped_terms(&self, mut map: impl FnMut(GenericArgument, &[u32]) -> GenericArgument) -> Self {
        let mut map_type = |value: &Type| match map(GenericArgument::Type(value.clone()), &[]) {
            GenericArgument::Type(value) => value,
            _ => Type::Error,
        };
        let environment = self.environment.as_deref().map(&mut map_type).map(Box::new);
        let after_environment = self.after_environment.as_deref().map(&mut map_type).map(Box::new);
        let captures = self.captures.iter().map(&mut map_type).collect();
        Self {
            environment, after_environment, captures,
            body_regions: self.body_regions.map_terms(|value| map(value, &[])),
            shared_receiver: self.shared_receiver,
            unique_receiver: self.unique_receiver,
            residual: self.residual.map_terms(|value| map(value, &[])),
            universal: self.universal.iter().map(|bound| bound.map_terms(|value| map(value, &[bound.lifetime_binders]))).collect(),
        }
    }

    pub(crate) fn instantiate(&self, arguments: &[GenericArgument]) -> Self {
        self.map_terms(|value, extra| {
            let Some(arguments) = arguments.iter().cloned()
                .map(|argument| super::regions::shift_argument(argument, 1 + extra))
                .collect::<Option<Vec<_>>>() else { return GenericArgument::Type(Type::Error); };
            crate::signature::substitute_trait_generic_argument(value, &arguments)
        })
    }

    pub(crate) fn try_map_terms<E>(&self, mut map: impl FnMut(GenericArgument, u32) -> Result<GenericArgument, E>) -> Result<Self, E> {
        let mut error = None;
        let value = self.map_terms(|argument, binders| {
            if error.is_some() { return argument; }
            match map(argument.clone(), binders) {
                Ok(value) => value,
                Err(failure) => { error = Some(failure); argument },
            }
        });
        match error { Some(error) => Err(error), None => Ok(value) }
    }

    pub(crate) fn terms(&self) -> Vec<(GenericArgument, u32)> {
        let mut terms = vec![];
        let _ = self.map_terms(|argument, binders| { terms.push((argument.clone(), binders)); argument });
        terms
    }

    pub(super) fn encode(&self, output: &mut Vec<u8>) {
        fn contract(value: &crate::AssociatedItemContract, output: &mut Vec<u8>) {
            output.extend_from_slice(&(value.where_bounds.len() as u64).to_le_bytes());
            for (subject, relation) in &value.where_bounds {
                super::encode_type(subject, output);
                output.extend_from_slice(&relation.definition.0.as_bytes());
                super::encode_generic_arguments(&relation.arguments, output);
            }
            output.extend_from_slice(&(value.where_outlives.len() as u64).to_le_bytes());
            for predicate in &value.where_outlives {
                match predicate {
                    crate::OutlivesPredicate::Type { subject, lifetime } => {
                        output.push(0);
                        super::encode_type(subject, output);
                        super::encode_generic_arguments(&[GenericArgument::Lifetime(*lifetime)], output);
                    },
                    crate::OutlivesPredicate::Region { longer, shorter } => {
                        output.push(1);
                        super::encode_generic_arguments(&[GenericArgument::Lifetime(*longer), GenericArgument::Lifetime(*shorter)], output);
                    },
                }
            }
            output.extend_from_slice(&(value.type_bindings.len() as u64).to_le_bytes());
            for binding in &value.type_bindings {
                super::encode_type(&binding.subject, output);
                output.extend_from_slice(&binding.relation.definition.0.as_bytes());
                super::encode_generic_arguments(&binding.relation.arguments, output);
                output.extend_from_slice(&(binding.name.len() as u64).to_le_bytes());
                output.extend_from_slice(binding.name.as_bytes());
                super::encode_generic_kinds(&binding.item_generic_kinds, output);
                super::encode_generic_arguments(&binding.item_arguments, output);
                super::encode_type(&binding.value, output);
            }
            output.extend_from_slice(&(value.effect_bindings.len() as u64).to_le_bytes());
            for binding in &value.effect_bindings {
                super::encode_type(&binding.subject, output);
                output.extend_from_slice(&binding.relation.definition.0.as_bytes());
                super::encode_generic_arguments(&binding.relation.arguments, output);
                output.extend_from_slice(&(binding.name.len() as u64).to_le_bytes());
                output.extend_from_slice(binding.name.as_bytes());
                super::encode_generic_kinds(&binding.item_generic_kinds, output);
                super::encode_generic_arguments(&binding.item_arguments, output);
                super::encode_generic_arguments(&[GenericArgument::EffectRow(binding.value.clone())], output);
            }
        }
        output.push(u8::from(self.shared_receiver));
        output.push(u8::from(self.unique_receiver));
        output.push(u8::from(self.environment.is_some()));
        if let Some(environment) = &self.environment { super::encode_type(environment, output); }
        output.push(u8::from(self.after_environment.is_some()));
        if let Some(environment) = &self.after_environment { super::encode_type(environment, output); }
        super::encode_types(&self.captures, output);
        self.body_regions.encode(output);
        contract(&self.residual, output);
        output.extend_from_slice(&(self.universal.len() as u64).to_le_bytes());
        for bound in &self.universal {
            output.extend_from_slice(&bound.lifetime_binders.to_le_bytes());
            contract(&crate::AssociatedItemContract {
                where_bounds: vec![(bound.subject.clone(), bound.relation.clone())], where_outlives: vec![],
                type_bindings: bound.type_bindings.clone(), effect_bindings: bound.effect_bindings.clone(),
            }, output);
        }
    }
}
