//! Declaration-owned callable identities and selected implementation bindings.
//! Analysis and materialization share these checked facts without translating
//! semantic queries into executable instance keys.
use crate::core::{CoreExpr, CoreKind};
use crate::{DefKey, ElaboratedHeader, ElaboratedInterface, GenericArgument, TraitSolver, Type};
use std::collections::BTreeMap;

/// Select a declaration and its ambient invocation bounds using the frozen
/// identity. Generic substitution must not manufacture new body capabilities.
pub(crate) fn declared_invocation_contract<'a>(
    signatures: &'a crate::ElaboratedInterface,
    expression: &CoreExpr,
) -> Option<(&'a crate::CallableSignature, Vec<&'a Type>)> {
    use crate::ElaboratedHeader;
    match &expression.kind {
        CoreKind::Function { definition, .. } => match signatures.definitions.get(definition)? {
            ElaboratedHeader::Callable(signature)
            | ElaboratedHeader::ValueAlias { signature, .. } => Some((signature, vec![])),
            _ => None,
        },
        CoreKind::TraitMethod {
            deferred: Some(deferred),
            ..
        } => {
            let ElaboratedHeader::Trait(header) =
                signatures.definitions.get(&deferred.relation.definition)?
            else {
                return None;
            };
            Some((header.methods.get(&deferred.name)?, vec![]))
        }
        CoreKind::TraitMethod {
            evidence,
            method,
            deferred: None,
            ..
        } => {
            let ElaboratedHeader::Implementation(implementation) =
                signatures.definitions.get(evidence)?
            else {
                return None;
            };
            let signature = implementation
                .methods
                .iter()
                .find_map(|(name, signature)| {
                    (crate::implementation_method_key(*evidence, name) == *method)
                        .then_some(signature)
                })?;
            let ambient = implementation
                .where_bounds
                .iter()
                .filter(|(_, relation)| crate::is_intrinsic_callable_trait(relation))
                .map(|(subject, _)| subject)
                .chain(
                    implementation
                        .universal_bounds
                        .iter()
                        .filter(|bound| crate::is_intrinsic_callable_trait(&bound.relation))
                        .map(|bound| &bound.subject),
                )
                .collect();
            Some((signature, ambient))
        }
        _ => None,
    }
}

/// A declaration template paired with its selected substitution in declaration
/// slot order. Consumers may rigidify the values before instantiating; they
/// must not rigidify independently elided regions in the template itself.
pub(crate) struct SelectedTemplate {
    pub signature: crate::CallableSignature,
    pub arguments: Vec<GenericArgument>,
}

/// An evaluated top-level value has no caller inputs. Use the ordinary
/// interface-aware result producer, including static and unknown coverage,
/// rather than classifying every initializer as an opaque reference result.
pub(crate) fn value_reference_contract(signatures: &ElaboratedInterface, result: &Type)
    -> (crate::core::CallReferenceOrigin, crate::core::CallReferenceShape) {
    let origin = crate::core::callable_reference_origin_from_contract(signatures, &[], result);
    let shape = crate::core::call_reference_shape(signatures, result, &origin);
    (origin, shape)
}

fn implementation_body_signature(
    implementation: &crate::signature::ElaboratedImplementation,
    method: &crate::CallableSignature,
) -> crate::CallableSignature {
    let mut signature = method.clone();
    signature.generic_kinds = implementation
        .generic_kinds
        .iter()
        .chain(&method.generic_kinds)
        .copied()
        .collect();
    signature.generics = signature.generic_kinds.len() as u32;
    signature
        .where_bounds
        .extend(implementation.where_bounds.clone());
    signature.where_bounds.push((
        implementation.self_ty.clone(),
        implementation.relation.clone(),
    ));
    signature
        .where_outlives
        .extend(implementation.where_outlives.clone());
    signature
        .universal_bounds
        .extend(implementation.universal_bounds.clone());
    signature
        .where_associated_type_bindings
        .extend(implementation.where_associated_type_bindings.clone());
    signature
        .where_associated_effect_bindings
        .extend(implementation.where_associated_effect_bindings.clone());
    signature
}

/// The declaration contract for an independently checked body. Evaluated
/// initializers contribute their frozen pure, zero-input body contract, but
/// their source value does not acquire a function type or invocation authority.
pub(crate) fn body_signature(
    signatures: &ElaboratedInterface,
    definition: DefKey,
) -> Option<crate::CallableSignature> {
    if let Some(ElaboratedHeader::Callable(signature)) = signatures.definitions.get(&definition) {
        return Some(signature.clone());
    }
    if let Some(ElaboratedHeader::ValueInitializer { generic_kinds, ty: Some(result) }) = signatures.definitions.get(&definition) {
        // Evaluated values are frozen, pure zero-argument bodies. Their
        // generalized result belongs to this declaration's binder namespace,
        // just as a function's result does; it is not a source function value.
        return Some(crate::CallableSignature {
            safety: crate::Safety::Safe, generics: generic_kinds.len() as u32,
            generic_kinds: generic_kinds.clone(), parameters: vec![], result: result.clone(),
            effects: crate::EffectRow::empty(), invocation: crate::Quantity::ONCE,
            where_bounds: vec![], where_outlives: vec![], where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![], universal_bounds: vec![],
        });
    }
    signatures.definitions.iter().find_map(|(key, header)| {
        let ElaboratedHeader::Implementation(implementation) = header else {
            return None;
        };
        implementation.methods.iter().find_map(|(name, signature)| {
            (crate::implementation_method_key(*key, name) == definition)
                .then(|| implementation_body_signature(implementation, signature))
        })
    })
}

pub(crate) fn receiver_candidate(ty: &Type) -> Option<&Type> {
    let Type::Callable {
        parameters, result, ..
    } = ty
    else {
        return None;
    };
    Some(parameters.first().unwrap_or(result))
}

pub(crate) fn selected_template(
    signatures: &ElaboratedInterface,
    expression: &CoreExpr,
) -> Option<SelectedTemplate> {
    if let CoreKind::Constant { definition, arguments } = &expression.kind {
        let signature = body_signature(signatures, *definition)?;
        signature.instantiate_generic(arguments).ok()?;
        return Some(SelectedTemplate { signature, arguments: arguments.clone() });
    }
    let (signature, _) = declared_invocation_contract(signatures, expression)?;
    match &expression.kind {
        CoreKind::Function { arguments, .. } => Some(SelectedTemplate {
            signature: signature.clone(),
            arguments: arguments.clone(),
        }),
        CoreKind::TraitMethod {
            evidence,
            method,
            trait_arguments,
            method_arguments,
            deferred: None,
        } => {
            let ElaboratedHeader::Implementation(implementation) =
                signatures.definitions.get(evidence)?
            else {
                return None;
            };
            let receiver = trait_method_executable_receiver(
                *evidence,
                *method,
                receiver_candidate(&expression.ty),
                signatures,
            )
            .ok()?;
            let arguments = implementation_arguments(
                signatures,
                implementation,
                trait_arguments,
                method_arguments,
                receiver.as_ref(),
            )
            .ok()?;
            let signature = implementation_body_signature(implementation, signature);
            Some(SelectedTemplate {
                signature,
                arguments,
            })
        }
        // A deferred selection has no implementation substitution yet. Its
        // realized contract remains conservative input, not an empty proof.
        _ => None,
    }
}

/// Bind the selected implementation's declared slots, independently of an
/// executable key. Semantic analysis and materialization consume this same
/// checked substitution; unresolved slots never acquire invented defaults.
pub(crate) fn implementation_arguments(
    signatures: &ElaboratedInterface,
    implementation: &crate::signature::ElaboratedImplementation,
    relation_values: &[GenericArgument],
    method_arguments: &[GenericArgument],
    receiver: Option<&Type>,
) -> Result<Vec<GenericArgument>, String> {
    if relation_values.len() != implementation.relation.arguments.len() {
        return Err("selected trait relation has the wrong argument arity".into());
    }
    let mut bindings = BTreeMap::new();
    let mut pending: Vec<_> = implementation
        .relation
        .arguments
        .iter()
        .zip(relation_values)
        .map(|(template, value)| (template.clone(), value.clone()))
        .collect();
    if let Some(receiver) = receiver {
        pending.push((
            GenericArgument::Type(implementation.self_ty.clone()),
            GenericArgument::Type(receiver.clone()),
        ));
    }
    while !pending.is_empty() {
        let previous = bindings.len();
        let mut next = vec![];
        let mut failure = None;
        for (template, value) in pending {
            let mut candidate = bindings.clone();
            match bind_impl_head_argument(&template, &value, &mut candidate) {
                Ok(()) => bindings = candidate,
                Err(error) => {
                    failure = Some(error);
                    next.push((template, value));
                }
            }
        }
        if !next.is_empty() && bindings.len() == previous {
            return Err(failure.expect("pending head equation has a failure"));
        }
        pending = next;
    }
    if implementation
        .generic_kinds
        .iter()
        .enumerate()
        .any(|(index, _)| !bindings.contains_key(&(index as u32)))
        && !implementation.universal_bounds.is_empty()
    {
        // The solver-selected Fn equalities may functionally
        // determine Output/Effects binders absent from the Self
        // head. Recover those exact frozen terms, not new body
        // inference or a default for an unconstrained binder.
        TraitSolver::new(signatures)
            .complete_callable_implementation_arguments(implementation, &mut bindings)
            .ok_or_else(|| {
                "selected trait implementation has invalid quantified callable arguments".to_owned()
            })?;
    }
    // Static trait methods have no receiver slot in their executable
    // identity. Their implementation generics may nevertheless be
    // fully determined by the selected trait relation (for example
    // `impl<T> Parent<T> for i64`). The binder completeness check
    // below remains the authority for rejecting genuinely
    // unconstrained generic implementations.
    let mut arguments =
        Vec::with_capacity(implementation.generic_kinds.len() + method_arguments.len());
    for (index, kind) in implementation.generic_kinds.iter().enumerate() {
        let argument = bindings.get(&(index as u32)).cloned().ok_or_else(|| {
            format!("selected trait implementation leaves generic binder {index} unconstrained")
        })?;
        if instance_argument_kind(&argument) != *kind {
            return Err(format!(
                "selected trait implementation binds generic {index} with the wrong kind"
            ));
        }
        arguments.push(argument);
    }
    arguments.extend_from_slice(method_arguments);
    Ok(arguments)
}

/// Invert the selected trait head into an implementation binder substitution.
/// This operates only on the frozen, solver-selected head and therefore never
/// re-runs inference while materializing an executable body.
fn bind_impl_head_argument(
    template: &GenericArgument,
    value: &GenericArgument,
    bindings: &mut BTreeMap<u32, GenericArgument>,
) -> Result<(), String> {
    if let (GenericArgument::EffectRow(template), GenericArgument::EffectRow(value)) =
        (template, value)
    {
        let mut resolved = template.clone();
        resolved.substitute_tails(|tail| match tail {
            crate::EffectTail::Generic(index) => match bindings.get(&index) {
                Some(GenericArgument::EffectRow(row)) => Some(row.clone()),
                _ => None,
            },
            _ => None,
        });
        if resolved == *value {
            return Ok(());
        }
        let unknown: Vec<_> = template
            .tails
            .iter()
            .filter_map(|tail| match tail {
                crate::EffectTail::Generic(index) if !bindings.contains_key(index) => Some(*index),
                _ => None,
            })
            .collect();
        if *value == crate::EffectRow::empty()
            && resolved.effects.is_empty()
            && resolved.projections.is_empty()
            && resolved.tails.iter().all(|tail| match tail {
                crate::EffectTail::Generic(index) => unknown.contains(index),
                _ => false,
            })
        {
            for index in unknown {
                bind_impl_head_slot(
                    index,
                    GenericArgument::EffectRow(crate::EffectRow::empty()),
                    bindings,
                )?;
            }
            return Ok(());
        }
        if let [index] = unknown.as_slice()
            && resolved.effects.is_subset(&value.effects)
            && resolved
                .projections
                .iter()
                .all(|projection| value.projections.contains(projection))
        {
            resolved.tails.remove(&crate::EffectTail::Generic(*index));
            if resolved.tails.is_subset(&value.tails) {
                return bind_impl_head_slot(
                    *index,
                    GenericArgument::EffectRow(
                        crate::EffectRow {
                            effects: value
                                .effects
                                .difference(&resolved.effects)
                                .cloned()
                                .collect(),
                            projections: value
                                .projections
                                .iter()
                                .filter(|projection| !resolved.projections.contains(projection))
                                .cloned()
                                .collect(),
                            tails: value.tails.difference(&resolved.tails).copied().collect(),
                        }
                        .canonicalized(),
                    ),
                    bindings,
                );
            }
        }
        return Err(
            "selected trait implementation has an unresolved or incompatible effect-row union"
                .into(),
        );
    }
    match (template, value) {
        (GenericArgument::Type(template), GenericArgument::Type(value)) => {
            bind_impl_head_type(template, value, bindings)
        }
        (
            GenericArgument::Lifetime(crate::Lifetime::Generic(index)),
            GenericArgument::Lifetime(value),
        ) => bind_impl_head_slot(*index, GenericArgument::Lifetime(*value), bindings),
        (GenericArgument::EffectRow(template), GenericArgument::EffectRow(value))
            if template.effects.is_empty()
                && template.projections.is_empty()
                && template.tails.len() == 1
                && matches!(template.tails.first(), Some(crate::EffectTail::Generic(_))) =>
        {
            let Some(crate::EffectTail::Generic(index)) = template.tails.first().copied() else {
                unreachable!("effect-row guard established a generic tail");
            };
            bind_impl_head_slot(index, GenericArgument::EffectRow(value.clone()), bindings)
        }
        (GenericArgument::ConstGeneric { index, kind }, value)
            if instance_argument_kind(value) == crate::GenericKind::Const(*kind) =>
        {
            bind_impl_head_slot(*index, value.clone(), bindings)
        }
        _ if template == value => Ok(()),
        _ => Err("selected trait implementation head does not match its executable key".into()),
    }
}

fn bind_impl_head_type(
    template: &Type,
    value: &Type,
    bindings: &mut BTreeMap<u32, GenericArgument>,
) -> Result<(), String> {
    match (template, value) {
        (Type::Generic(index), value) => {
            bind_impl_head_slot(*index, GenericArgument::Type(value.clone()), bindings)
        }
        (
            Type::Nominal {
                definition: template_definition,
                arguments: template_arguments,
            },
            Type::Nominal {
                definition: value_definition,
                arguments: value_arguments,
            },
        ) if template_definition == value_definition
            && template_arguments.len() == value_arguments.len() =>
        {
            for (template, value) in template_arguments.iter().zip(value_arguments) {
                bind_impl_head_argument(template, value, bindings)?;
            }
            Ok(())
        }
        (Type::Tuple(template), Type::Tuple(value)) if template.len() == value.len() => {
            for (template, value) in template.iter().zip(value) {
                bind_impl_head_type(template, value, bindings)?;
            }
            Ok(())
        }
        (
            Type::FixedArray {
                element: template,
                length: tn,
            },
            Type::FixedArray {
                element: value,
                length: vn,
            },
        ) => {
            bind_impl_head_type(template, value, bindings)?;
            bind_impl_head_argument(tn, vn, bindings)
        }
        (Type::Array(template), Type::Array(value)) => {
            bind_impl_head_type(template, value, bindings)
        }
        (
            Type::RawPointer {
                mutability: template_mutability,
                pointee: template_pointee,
            },
            Type::RawPointer {
                mutability: value_mutability,
                pointee: value_pointee,
            },
        ) if template_mutability == value_mutability => {
            bind_impl_head_type(template_pointee, value_pointee, bindings)
        }
        (
            Type::Reference {
                mutability: template_mutability,
                lifetime: template_lifetime,
                referent: template_referent,
            },
            Type::Reference {
                mutability: value_mutability,
                lifetime: value_lifetime,
                referent: value_referent,
            },
        ) if template_mutability == value_mutability => {
            bind_impl_head_argument(
                &GenericArgument::Lifetime(*template_lifetime),
                &GenericArgument::Lifetime(*value_lifetime),
                bindings,
            )?;
            bind_impl_head_type(template_referent, value_referent, bindings)
        }
        _ if template == value => Ok(()),
        _ => {
            Err("selected trait implementation Self type does not match its executable key".into())
        }
    }
}

fn bind_impl_head_slot(
    index: u32,
    value: GenericArgument,
    bindings: &mut BTreeMap<u32, GenericArgument>,
) -> Result<(), String> {
    match bindings.get(&index) {
        Some(previous) if previous != &value => Err(format!(
            "selected trait implementation assigns incompatible values to generic binder {index}"
        )),
        Some(_) => Ok(()),
        None => {
            bindings.insert(index, value);
            Ok(())
        }
    }
}

/// Recover Core's selected Self using the same declaration-owned receiver
/// shape. In particular, a blanket impl head matches both T and &T, so matching
/// the implementation head alone cannot distinguish Self from a borrow of it.
pub(crate) fn trait_method_executable_receiver(
    evidence: DefKey,
    method: DefKey,
    receiver: Option<&Type>,
    signatures: &ElaboratedInterface,
) -> Result<Option<Type>, String> {
    let Some(receiver) = receiver else {
        return Ok(None);
    };
    let Some(ElaboratedHeader::Implementation(implementation)) =
        signatures.definitions.get(&evidence)
    else {
        return Err("selected trait method evidence does not name an implementation".into());
    };
    let matches_head = |candidate: &Type| {
        bind_impl_head_type(&implementation.self_ty, candidate, &mut BTreeMap::new()).is_ok()
    };
    let declaration = implementation
        .methods
        .keys()
        .find(|name| crate::implementation_method_key(evidence, name) == method)
        .and_then(|name| {
            match signatures
                .definitions
                .get(&implementation.relation.definition)
            {
                Some(ElaboratedHeader::Trait(header)) => header.methods.get(name),
                _ => None,
            }
        });
    if let Some(parameter) = declaration.and_then(|method| method.parameters.first())
        && let Some(subject) = crate::core::declared_receiver_subject(parameter, receiver)
    {
        return matches_head(&subject)
            .then_some(Some(subject))
            .ok_or_else(|| {
                "selected trait implementation Self type does not match its declared receiver"
                    .into()
            });
    }
    if matches_head(receiver) {
        return Ok(Some(receiver.clone()));
    }
    if let Type::Reference { referent, .. } = receiver
        && matches_head(referent)
    {
        return Ok(Some((**referent).clone()));
    }
    // A contextually selected monomorphic static method need not mention Self
    // in its callable parameters. There are no impl slots to recover from it.
    if implementation.generics == 0 {
        return Ok(None);
    }
    Err("selected trait implementation Self type does not match its executable receiver".into())
}

pub(crate) fn instance_argument_kind(argument: &GenericArgument) -> crate::GenericKind {
    match argument {
        GenericArgument::Type(_) => crate::GenericKind::Type,
        GenericArgument::EffectRow(_) => crate::GenericKind::EffectRow,
        GenericArgument::Lifetime(_) => crate::GenericKind::Lifetime,
        GenericArgument::ConstInteger(value) => crate::GenericKind::Const(value.kind()),
        GenericArgument::ConstIntegerExpr(value) => value
            .scalar()
            .ok()
            .and_then(crate::ConstKind::from_integer_scalar)
            .map(crate::GenericKind::Const)
            .unwrap_or(crate::GenericKind::Type),
        GenericArgument::ConstQuantity(_) => crate::GenericKind::Const(crate::ConstKind::Quantity),
        GenericArgument::ConstGeneric { kind, .. } => crate::GenericKind::Const(*kind),
        GenericArgument::ConstInfer { kind, .. } => crate::GenericKind::Const(*kind),
        GenericArgument::ConstProjection { kind, .. } => crate::GenericKind::Const(*kind),
    }
}
