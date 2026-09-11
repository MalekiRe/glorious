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
    fn stored_callable_views_are_directional_and_do_not_change_referents() {
        let callable = |contract| Type::Callable { contract: Box::new(contract), safety: Safety::Safe,
            lifetime_binders: 0, parameters: vec![], result: Box::new(Type::Unit),
            effects: EffectRow::empty(), invocation: Quantity::ONCE };
        let mut resident = CallableContract::default();
        resident.environment = Some(Box::new(Type::Unit));
        resident.shared_receiver = true;
        resident.unique_receiver = true;
        resident.captures.push(reference(Lifetime::Generic(0), Type::Unit));
        let stored = callable(resident.join_residents(&CallableContract::default()));
        let produced = callable(resident);
        for (stored, produced) in [(stored.clone(), produced.clone()),
            (Type::Tuple(vec![stored.clone()]), Type::Tuple(vec![produced.clone()])),
            (Type::Array(Box::new(stored.clone())), Type::Array(Box::new(produced.clone())))] {
            assert!(super::super::regions::accepts_body_storage(&stored, &produced));
            assert!(!super::super::regions::accepts_body_storage(&produced, &stored));
        }
        for mutability in [Mutability::Shared, Mutability::Unique] {
            let reference = |ty| Type::Reference { mutability, lifetime: Lifetime::Static, referent: Box::new(ty) };
            assert!(!super::super::regions::accepts_body_storage(&reference(stored.clone()), &reference(produced.clone())));
        }
        assert!(!super::super::regions::accepts_body_storage(&callable(CallableContract::default()), &produced),
            "an erased storage annotation cannot delete captured loan debt");
    }

    #[test]
    fn writable_residents_intersect_authority_and_retain_capture_obligations() {
        let mut resident = CallableContract::default();
        resident.environment = Some(Box::new(Type::Unit));
        resident.after_environment = Some(Box::new(Type::Unit));
        resident.shared_receiver = true;
        resident.unique_receiver = true;
        resident.captures.push(reference(Lifetime::Generic(0), Type::Unit));
        resident.residual.where_outlives.push(crate::OutlivesPredicate::Type {
            subject: Type::Unit, lifetime: Lifetime::Static,
        });
        let writer = CallableContract::default();
        assert_eq!(resident.join(&writer), resident, "annotation remains contextual");
        let joined = resident.join_residents(&writer);
        assert!(!joined.shared_receiver && !joined.unique_receiver);
        assert!(joined.environment.is_none() && joined.after_environment.is_none());
        assert_eq!(joined.captures, resident.captures);
        assert_eq!(joined.residual, resident.residual);
        assert_eq!(writer.join_residents(&resident), joined, "writer cannot grant initial permissions");
    }

    #[test]
    fn writable_storage_views_preserve_abi_and_do_not_reinterpret_references() {
        let mut resident = CallableContract::default();
        resident.shared_receiver = true;
        resident.unique_receiver = true;
        let function = |contract, invocation| Type::Callable { contract: Box::new(contract), safety: Safety::Safe,
            lifetime_binders: 0, parameters: vec![reference(Lifetime::Static, Type::Unit)],
            result: Box::new(Type::Unit), effects: EffectRow::empty(), invocation };
        let previous = function(resident, Quantity::UNRESTRICTED);
        let writer = function(CallableContract::default(), Quantity::ONCE);
        let expected = function(CallableContract::default(), Quantity::UNRESTRICTED);
        assert_eq!(CallableContract::writable_storage_view(previous.clone(), &writer), expected.clone());
        assert_eq!(CallableContract::writable_storage_view(Type::Tuple(vec![previous.clone()]),
            &Type::Tuple(vec![writer.clone()])), Type::Tuple(vec![expected]));
        let existing = reference(Lifetime::Generic(0), previous);
        assert_eq!(CallableContract::writable_storage_view(existing.clone(),
            &reference(Lifetime::Static, writer)), existing);
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
    /// A resident may enter a wider storage contract only if that contract
    /// retains all its debt and promises no additional receiver/environment
    /// authority. Apply this through owned structural products, never through
    /// reference handles, callable ABIs, or nominal identities.
    pub(crate) fn storage_input_view(required: &Type, provided: Type) -> Option<Type> {
        let provided = Self::invocation_input_view(required, provided);
        Some(match (required, provided) {
            (Type::Callable { contract: required, .. },
                Type::Callable { contract, safety, lifetime_binders, parameters, result, effects, invocation }) => {
                if required.as_ref() != &required.join_residents(&contract) { return None; }
                Type::Callable { contract: required.clone(), safety, lifetime_binders, parameters, result, effects, invocation }
            }
            (Type::Tuple(required), Type::Tuple(provided)) if required.len() == provided.len() =>
                Type::Tuple(required.iter().zip(provided).map(|(required, provided)| Self::storage_input_view(required, provided)).collect::<Option<_>>()?),
            (Type::Array(required), Type::Array(provided)) => Type::Array(Box::new(Self::storage_input_view(required, *provided)?)),
            (Type::FixedArray { element: required, .. }, Type::FixedArray { element, length }) =>
                Type::FixedArray { element: Box::new(Self::storage_input_view(required, *element)?), length },
            (_, provided) => provided,
        })
    }

    /// A writable owned place must admit every resident promised by the
    /// writer's referent type. Unlike an annotation, an empty contract here
    /// is an actual alternative. Never reinterpret an existing reference or
    /// change callable inputs/results while inferring this storage view.
    pub(crate) fn writable_storage_view(previous: Type, writer: &Type) -> Type {
        match (previous, writer) {
            (Type::Callable { contract, safety, lifetime_binders, parameters, result, effects, invocation },
             Type::Callable { contract: writer, .. }) => Type::Callable {
                contract: Box::new(contract.join_residents(writer)), safety, lifetime_binders,
                parameters, result, effects, invocation,
            },
            (Type::Tuple(fields), Type::Tuple(writers)) if fields.len() == writers.len() =>
                Type::Tuple(fields.into_iter().zip(writers).map(|(field, writer)| Self::writable_storage_view(field, writer)).collect()),
            (Type::Array(element), Type::Array(writer)) =>
                Type::Array(Box::new(Self::writable_storage_view(*element, writer))),
            (Type::FixedArray { element, length }, Type::FixedArray { element: writer, .. }) =>
                Type::FixedArray { element: Box::new(Self::writable_storage_view(*element, writer)), length },
            (previous, _) => previous,
        }
    }

    /// Apply the same one-way callable view through owned value products and
    /// nominal type arguments. References are deliberately not traversed:
    /// replacing a value is not permission to weaken writable referent storage.
    /// This matters for `Box<(T) -> U>`-style source records: inference may
    /// first construct the record with a reusable named function, then later
    /// pass it to a parameter whose instantiated field is one-shot.
    pub(crate) fn invocation_input_view(required: &Type, provided: Type) -> Type {
        if crate::types::label::payload(&provided).is_some() { return provided; }
        match (required, provided) {
            (Type::Tuple(required), Type::Tuple(provided)) if required.len() == provided.len() =>
                Type::Tuple(required.iter().zip(provided).map(|(required, provided)|
                    Self::invocation_input_view(required, provided)).collect()),
            (Type::Array(required), Type::Array(provided)) => Type::Array(Box::new(
                Self::invocation_input_view(required, *provided))),
            (Type::FixedArray { element: required, .. }, Type::FixedArray { element: provided, length }) =>
                Type::FixedArray { element: Box::new(Self::invocation_input_view(required, *provided)), length },
            (
                Type::Callable {
                    invocation: required,
                    ..
                },
                Type::Callable { contract,
                    safety,
                    lifetime_binders,
                    parameters,
                    result,
                    effects,
                    invocation: provided,
                },
            ) if provided.contains(*required) => Type::Callable { contract,
                safety,
                lifetime_binders,
                parameters,
                result,
                effects,
                invocation: *required,
            },
            (
                Type::Nominal {
                    definition: required_definition,
                    arguments: required_arguments,
                },
                Type::Nominal {
                    definition: provided_definition,
                    arguments: provided_arguments,
                },
            ) if required_definition == &provided_definition
                && required_arguments.len() == provided_arguments.len() => Type::Nominal {
                definition: provided_definition,
                arguments: required_arguments
                    .iter()
                    .zip(provided_arguments)
                    .map(|(required, provided)| match (required, provided) {
                        (GenericArgument::Type(required), GenericArgument::Type(provided)) => {
                            GenericArgument::Type(Self::invocation_input_view(
                                required, provided,
                            ))
                        }
                        (_, provided) => provided,
                    })
                    .collect(),
            },
            (_, provided) => provided,
        }
    }

    /// A sealed resident environment owns its captures, independently of the
    /// invocation interval of each callable value. An erased callable (and a
    /// resumption, whose environment is not a capture layout) retains its
    /// declared interval; an empty capture list alone is not Copy evidence.
    pub(crate) fn resident_quantity(
        &self, invocation: crate::Quantity,
        mut capture_quantity: impl FnMut(&Type) -> Option<crate::Quantity>,
    ) -> Option<crate::Quantity> {
        if self.environment.is_none() { return Some(invocation); }
        self.captures.iter().try_fold(crate::Quantity::UNRESTRICTED, |quantity, capture| {
            quantity.intersection(capture_quantity(capture)?).ok()
        })
    }

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
        self.join_residents(other)
    }

    fn join_residents(&self, other: &Self) -> Self {
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
