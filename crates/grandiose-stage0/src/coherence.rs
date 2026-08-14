//! Global trait implementation coherence.
//!
//! This deliberately runs after every interface is frozen and before body
//! elaboration.  A body must never select an implementation whose identity or
//! legality depends on source traversal order.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    header::{HeaderGenericArgument, HeaderType, ImplementationHeader, ParsedHeader},
    identity::{DefKey, ModuleKey},
    interface::{DefinitionNamespace, PackageInterface},
    resolution::{DefinitionIndex, ResolutionState},
    signature::{ElaboratedHeader, ElaboratedImplementation, ElaboratedInterface},
    source::Span,
    trait_solver::{TraitAnswer, TraitGoal, TraitSolver},
    types::{GenericArgument, Type},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CoherenceDiagnostic {
    pub code: &'static str,
    pub span: Span,
    pub message: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImplHead {
    pub definition: DefKey,
    pub trait_definition: DefKey,
    pub negative: bool,
    pub self_ty: HeaderType,
    pub trait_arguments: Vec<HeaderGenericArgument>,
    pub generics: BTreeSet<String>,
    pub span: Span,
}

#[derive(Clone, Debug, Default)]
pub struct CoherenceSet {
    pub implementations: BTreeMap<DefKey, ImplHead>,
    pub diagnostics: Vec<CoherenceDiagnostic>,
}

impl CoherenceSet {
    pub fn collect<'a>(
        interfaces: impl IntoIterator<Item = &'a PackageInterface>,
        index: &DefinitionIndex,
    ) -> Self {
        let interfaces = interfaces.into_iter().collect::<Vec<_>>();
        let signatures = ElaboratedInterface::merge(
            interfaces
                .iter()
                .map(|interface| ElaboratedInterface::elaborate_with_index(interface, index)),
        );
        Self::collect_with_signatures(interfaces, index, &signatures)
    }

    /// Collect coherence facts using the same frozen signatures consumed by
    /// trait selection.  This keeps overlap legality independent of header
    /// traversal and lets combined implementation bounds be checked through
    /// the canonical solver rather than guessed from syntax alone.
    pub fn collect_with_signatures<'a>(
        interfaces: impl IntoIterator<Item = &'a PackageInterface>,
        index: &DefinitionIndex,
        signatures: &ElaboratedInterface,
    ) -> Self {
        let mut result = Self::default();
        let mut pending = vec![];
        for interface in interfaces {
            for definition in &interface.definitions {
                let ParsedHeader::Implementation(header) = &definition.syntax.header else {
                    continue;
                };
                pending.push((
                    definition.key,
                    definition.module.clone(),
                    definition.span,
                    header,
                ));
            }
        }
        pending.sort_by_key(|(key, _, _, _)| *key);
        for (definition, module, span, header) in pending {
            let Some(trait_definition) =
                resolve_trait(index, &module, header, &mut result.diagnostics)
            else {
                continue;
            };
            let trait_local = index
                .owner(trait_definition)
                .is_some_and(|owner| owner.package == module.package);
            let self_head = resolve_self_head(
                index,
                &module,
                &header.self_ty,
                span,
                &mut result.diagnostics,
            );
            if self_head == SelfHeadResolution::Invalid {
                continue;
            }
            let self_local = matches!(self_head, SelfHeadResolution::Resolved(definition) if index
                .owner(definition)
                .is_some_and(|owner| owner.package == module.package));
            if !trait_local && !self_local {
                result.diagnostics.push(CoherenceDiagnostic {
                    code: "G3407",
                    span,
                    message: "implementation violates the orphan boundary: trait and self type are both foreign".into(),
                });
                continue;
            }
            validate_negative_generics(header, span, &mut result.diagnostics);
            let head = ImplHead {
                definition,
                trait_definition,
                negative: header.negative,
                self_ty: header.self_ty.clone(),
                trait_arguments: header.relation.arguments.clone(),
                generics: header.generics.iter().cloned().collect(),
                span,
            };
            result.implementations.insert(definition, head);
        }
        let heads = result.implementations.values().cloned().collect::<Vec<_>>();
        for (offset, left) in heads.iter().enumerate() {
            for right in &heads[offset + 1..] {
                if left.trait_definition != right.trait_definition
                    || !implementations_may_overlap(left, right, signatures)
                {
                    continue;
                }
                let (code, message) = match (left.negative, right.negative) {
                    (false, false) => (
                        "G3404",
                        "overlapping positive implementations for one trait head",
                    ),
                    (true, true) => (
                        "G3405",
                        "overlapping negative implementations for one trait head",
                    ),
                    _ => (
                        "G3406",
                        "positive and negative implementations overlap for one trait head",
                    ),
                };
                result.diagnostics.push(CoherenceDiagnostic {
                    code,
                    span: right.span,
                    message: format!(
                        "{message}; conflicts with implementation at byte {}",
                        left.span.start
                    ),
                });
            }
        }
        result.diagnostics.sort_by(|left, right| {
            (
                left.code,
                left.span.file,
                left.span.start,
                left.span.end,
                &left.message,
            )
                .cmp(&(
                    right.code,
                    right.span.file,
                    right.span.start,
                    right.span.end,
                    &right.message,
                ))
        });
        result
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SelfHeadResolution {
    Resolved(DefKey),
    /// Primitives, generic parameters, and recovered type syntax do not have
    /// a declaration owner. They remain valid anchors only for a local trait.
    Unowned,
    /// A nominal path that was ambiguous or private is a resolution failure,
    /// not evidence that the self type is foreign.
    Invalid,
}

fn resolve_self_head(
    index: &DefinitionIndex,
    module: &ModuleKey,
    ty: &HeaderType,
    span: Span,
    diagnostics: &mut Vec<CoherenceDiagnostic>,
) -> SelfHeadResolution {
    let path = match ty {
        HeaderType::Path(path) => path,
        HeaderType::Application(base, _) => {
            return resolve_self_head(index, module, base, span, diagnostics);
        }
        _ => return SelfHeadResolution::Unowned,
    };
    match index.resolve_path(DefinitionNamespace::Type, module, path) {
        ResolutionState::Resolved(definition) => SelfHeadResolution::Resolved(definition),
        ResolutionState::Ambiguous(_) => {
            diagnostics.push(CoherenceDiagnostic {
                code: "G3408",
                span,
                message: format!(
                    "implementation self type `{}` is ambiguous",
                    path.join("::")
                ),
            });
            SelfHeadResolution::Invalid
        }
        ResolutionState::Inaccessible(_) => {
            diagnostics.push(CoherenceDiagnostic {
                code: "G3409",
                span,
                message: format!("implementation self type `{}` is private", path.join("::")),
            });
            SelfHeadResolution::Invalid
        }
        ResolutionState::Unresolved | ResolutionState::Recovered => SelfHeadResolution::Unowned,
    }
}

fn resolve_trait(
    index: &DefinitionIndex,
    module: &ModuleKey,
    header: &ImplementationHeader,
    diagnostics: &mut Vec<CoherenceDiagnostic>,
) -> Option<DefKey> {
    match index.resolve_path(DefinitionNamespace::Trait, module, &header.relation.path) {
        ResolutionState::Resolved(definition) => Some(definition),
        ResolutionState::Ambiguous(_) => {
            diagnostics.push(CoherenceDiagnostic {
                code: "G3401",
                span: header.relation.span,
                message: format!(
                    "implementation trait `{}` is ambiguous",
                    header.relation.path.join("::")
                ),
            });
            None
        }
        ResolutionState::Inaccessible(_) => {
            diagnostics.push(CoherenceDiagnostic {
                code: "G3402",
                span: header.relation.span,
                message: format!(
                    "implementation trait `{}` is private",
                    header.relation.path.join("::")
                ),
            });
            None
        }
        _ => {
            diagnostics.push(CoherenceDiagnostic {
                code: "G3403",
                span: header.relation.span,
                message: format!(
                    "implementation trait `{}` is unresolved",
                    header.relation.path.join("::")
                ),
            });
            None
        }
    }
}

fn validate_negative_generics(
    header: &ImplementationHeader,
    span: Span,
    diagnostics: &mut Vec<CoherenceDiagnostic>,
) {
    if !header.negative {
        return;
    }
    let declared = header.generics.iter().cloned().collect::<BTreeSet<_>>();
    let mut used = BTreeSet::new();
    collect_generic_names(&header.self_ty, &declared, &mut used);
    for argument in &header.relation.arguments {
        collect_generic_argument_names(argument, &declared, &mut used);
    }
    for name in declared.difference(&used) {
        diagnostics.push(CoherenceDiagnostic {
            code: "G3407",
            span,
            message: format!(
                "negative implementation has unconstrained generic parameter `{name}`"
            ),
        });
    }
}

fn collect_generic_names(
    value: &HeaderType,
    declared: &BTreeSet<String>,
    used: &mut BTreeSet<String>,
) {
    match value {
        HeaderType::Path(path) if path.len() == 1 && declared.contains(&path[0]) => {
            used.insert(path[0].clone());
        }
        HeaderType::Application(base, arguments) => {
            collect_generic_names(base, declared, used);
            for argument in arguments {
                if let crate::header::HeaderGenericArgument::Type(argument) = argument {
                    collect_generic_names(argument, declared, used);
                }
            }
        }
        HeaderType::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            collect_generic_names(subject, declared, used);
            for argument in trait_arguments {
                collect_generic_argument_names(argument, declared, used);
            }
            for argument in item_arguments {
                collect_generic_argument_names(argument, declared, used);
            }
        }
        HeaderType::Tuple(values) => {
            for value in values {
                collect_generic_names(value, declared, used);
            }
        }
        HeaderType::Callable {
            parameters, result, ..
        } => {
            for parameter in parameters {
                collect_generic_names(parameter, declared, used);
            }
            collect_generic_names(result, declared, used);
        }
        HeaderType::Reference {
            lifetime, referent, ..
        } => {
            // Lifetime binders live outside the type namespace, so walking
            // only the referent makes `impl<'a> !Marker for &'a T` look as
            // though `'a` were unconstrained.  Coherence must account for
            // every binder that contributes to an implementation head.
            if let Some(lifetime) = lifetime
                && declared.contains(lifetime)
            {
                used.insert(lifetime.clone());
            }
            collect_generic_names(referent, declared, used);
        }
        HeaderType::Path(_) | HeaderType::Never | HeaderType::Recovered => {}
    }
}

fn collect_generic_argument_names(
    value: &HeaderGenericArgument,
    declared: &BTreeSet<String>,
    used: &mut BTreeSet<String>,
) {
    match value {
        HeaderGenericArgument::Type(value) => collect_generic_names(value, declared, used),
        HeaderGenericArgument::Lifetime(value) if declared.contains(value) => {
            used.insert(value.clone());
        }
        HeaderGenericArgument::EffectRow(value) => {
            for effect in &value.effects {
                collect_generic_names(effect, declared, used);
            }
            if let Some(tail) = &value.tail
                && declared.contains(tail)
            {
                used.insert(tail.clone());
            }
        }
        HeaderGenericArgument::U32(_)
        | HeaderGenericArgument::Quantity(_)
        | HeaderGenericArgument::Lifetime(_) => {}
    }
}

fn heads_may_unify(left: &ImplHead, right: &ImplHead) -> bool {
    if left.trait_arguments.len() != right.trait_arguments.len() {
        return false;
    }
    let left_generics = left.generics.clone();
    let right_generics = right.generics.clone();
    let mut bindings = Bindings::default();
    unify_type(
        &left.self_ty,
        &right.self_ty,
        &left_generics,
        &right_generics,
        &mut bindings,
    ) && left
        .trait_arguments
        .iter()
        .zip(&right.trait_arguments)
        .all(|(left, right)| {
            unify_generic_argument(left, right, &left_generics, &right_generics, &mut bindings)
        })
}

/// Decide overlap from a canonical common head and the satisfiability of the
/// two implementations' combined bounds.  Head unification alone is too
/// coarse: `impl<T> Display for T where T: Left` and the corresponding
/// `T: Right` implementation are disjoint when no type can prove both
/// relations.  Conversely, merely syntactic differences in bounds must not
/// hide an actual shared witness.
fn implementations_may_overlap(
    left_head: &ImplHead,
    right_head: &ImplHead,
    signatures: &ElaboratedInterface,
) -> bool {
    if !heads_may_unify(left_head, right_head) {
        return false;
    }
    let Some(ElaboratedHeader::Implementation(left)) =
        signatures.definitions.get(&left_head.definition)
    else {
        // A malformed signature is handled by header diagnostics. Preserve
        // the former conservative head-only result rather than making an
        // invalid interface accidentally coherent.
        return true;
    };
    let Some(ElaboratedHeader::Implementation(right)) =
        signatures.definitions.get(&right_head.definition)
    else {
        return true;
    };
    let right_offset = left.generics;
    let right = rebase_implementation_generics(right, right_offset);
    if left.relation.definition != right.relation.definition
        || left.relation.arguments.len() != right.relation.arguments.len()
    {
        return false;
    }
    let mut bindings = OverlapBindings::default();
    let Some(subject) = unify_overlap_type(&left.self_ty, &right.self_ty, &mut bindings) else {
        return false;
    };
    let Some(arguments) = left
        .relation
        .arguments
        .iter()
        .zip(&right.relation.arguments)
        .map(|(left, right)| unify_overlap_argument(left, right, &mut bindings))
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    let witness = TraitGoal {
        relation: crate::ElaboratedTraitReference {
            definition: left.relation.definition,
            arguments,
        },
        subject,
    };
    let mut solver = TraitSolver::new(signatures);
    left.where_bounds
        .iter()
        .chain(&right.where_bounds)
        .all(|(subject, relation)| {
            matches!(
                solver.solve(TraitGoal {
                    relation: resolve_overlap_relation(relation, &bindings),
                    subject: resolve_overlap_type(subject, &bindings),
                }),
                TraitAnswer::Proven { .. }
            )
        })
        // Keep the common head construction explicit in this boundary.  It
        // guarantees all relation arguments were unified even if neither
        // implementation has a where-bound today.
        && witness.relation.definition == left.relation.definition
}

#[derive(Default)]
struct OverlapBindings {
    types: BTreeMap<u32, Type>,
}

fn unify_overlap_argument(
    left: &GenericArgument,
    right: &GenericArgument,
    bindings: &mut OverlapBindings,
) -> Option<GenericArgument> {
    match (left, right) {
        (GenericArgument::Type(left), GenericArgument::Type(right)) => {
            unify_overlap_type(left, right, bindings).map(GenericArgument::Type)
        }
        (GenericArgument::EffectRow(left), GenericArgument::EffectRow(right)) if left == right => {
            Some(GenericArgument::EffectRow(left.clone()))
        }
        (GenericArgument::Lifetime(left), GenericArgument::Lifetime(right)) if left == right => {
            Some(GenericArgument::Lifetime(*left))
        }
        (GenericArgument::ConstU32(left), GenericArgument::ConstU32(right)) if left == right => {
            Some(GenericArgument::ConstU32(*left))
        }
        (GenericArgument::ConstQuantity(left), GenericArgument::ConstQuantity(right))
            if left == right =>
        {
            Some(GenericArgument::ConstQuantity(*left))
        }
        (
            GenericArgument::ConstGeneric {
                index: left_index,
                kind: left_kind,
            },
            GenericArgument::ConstGeneric {
                index: right_index,
                kind: right_kind,
            },
        ) if left_index == right_index && left_kind == right_kind => Some(left.clone()),
        _ => None,
    }
}

fn unify_overlap_type(left: &Type, right: &Type, bindings: &mut OverlapBindings) -> Option<Type> {
    let left = resolve_overlap_type(left, bindings);
    let right = resolve_overlap_type(right, bindings);
    match (&left, &right) {
        (Type::Generic(left), Type::Generic(right)) if left == right => Some(Type::Generic(*left)),
        (Type::Generic(index), value) => bind_overlap_type(*index, value.clone(), bindings),
        (value, Type::Generic(index)) => bind_overlap_type(*index, value.clone(), bindings),
        (
            Type::Nominal {
                definition: left_definition,
                arguments: left_arguments,
            },
            Type::Nominal {
                definition: right_definition,
                arguments: right_arguments,
            },
        ) if left_definition == right_definition
            && left_arguments.len() == right_arguments.len() =>
        {
            left_arguments
                .iter()
                .zip(right_arguments)
                .map(|(left, right)| unify_overlap_argument(left, right, bindings))
                .collect::<Option<Vec<_>>>()
                .map(|arguments| Type::Nominal {
                    definition: *left_definition,
                    arguments,
                })
        }
        (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => left
            .iter()
            .zip(right)
            .map(|(left, right)| unify_overlap_type(left, right, bindings))
            .collect::<Option<Vec<_>>>()
            .map(Type::Tuple),
        (Type::Array(left), Type::Array(right)) => {
            unify_overlap_type(left, right, bindings).map(|value| Type::Array(Box::new(value)))
        }
        (
            Type::Reference {
                mutability: left_mutability,
                lifetime: left_lifetime,
                referent: left_referent,
            },
            Type::Reference {
                mutability: right_mutability,
                lifetime: right_lifetime,
                referent: right_referent,
            },
        ) if left_mutability == right_mutability && left_lifetime == right_lifetime => {
            unify_overlap_type(left_referent, right_referent, bindings).map(|referent| {
                Type::Reference {
                    mutability: *left_mutability,
                    lifetime: *left_lifetime,
                    referent: Box::new(referent),
                }
            })
        }
        (
            Type::Projection {
                subject: left_subject,
                trait_definition: left_trait,
                trait_arguments: left_trait_arguments,
                name: left_name,
                item_arguments: left_item_arguments,
            },
            Type::Projection {
                subject: right_subject,
                trait_definition: right_trait,
                trait_arguments: right_trait_arguments,
                name: right_name,
                item_arguments: right_item_arguments,
            },
        ) if left_trait == right_trait
            && left_name == right_name
            && left_trait_arguments.len() == right_trait_arguments.len()
            && left_item_arguments.len() == right_item_arguments.len() =>
        {
            let subject = unify_overlap_type(left_subject, right_subject, bindings)?;
            let trait_arguments = left_trait_arguments
                .iter()
                .zip(right_trait_arguments)
                .map(|(left, right)| unify_overlap_type(left, right, bindings))
                .collect::<Option<Vec<_>>>()?;
            let item_arguments = left_item_arguments
                .iter()
                .zip(right_item_arguments)
                .map(|(left, right)| unify_overlap_type(left, right, bindings))
                .collect::<Option<Vec<_>>>()?;
            Some(Type::Projection {
                subject: Box::new(subject),
                trait_definition: *left_trait,
                trait_arguments,
                name: left_name.clone(),
                item_arguments,
            })
        }
        (left, right) if left == right => Some(left.clone()),
        _ => None,
    }
}

fn bind_overlap_type(index: u32, value: Type, bindings: &mut OverlapBindings) -> Option<Type> {
    if value == Type::Generic(index) {
        return Some(value);
    }
    if contains_overlap_generic(&value, index, bindings) {
        return None;
    }
    bindings.types.insert(index, value.clone());
    Some(value)
}

fn contains_overlap_generic(value: &Type, index: u32, bindings: &OverlapBindings) -> bool {
    match resolve_overlap_type(value, bindings) {
        Type::Generic(found) => found == index,
        Type::Nominal { arguments, .. } => arguments
            .iter()
            .any(|argument| contains_overlap_argument_generic(argument, index, bindings)),
        Type::Tuple(arguments) => arguments
            .iter()
            .any(|argument| contains_overlap_generic(argument, index, bindings)),
        Type::Array(value) => contains_overlap_generic(&value, index, bindings),
        Type::Reference { referent, .. } => contains_overlap_generic(&referent, index, bindings),
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            contains_overlap_generic(&subject, index, bindings)
                || trait_arguments
                    .iter()
                    .chain(&item_arguments)
                    .any(|argument| contains_overlap_generic(argument, index, bindings))
        }
        Type::Callable {
            parameters, result, ..
        } => {
            parameters
                .iter()
                .any(|parameter| contains_overlap_generic(parameter, index, bindings))
                || contains_overlap_generic(&result, index, bindings)
        }
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Infer(_)
        | Type::Error => false,
    }
}

fn contains_overlap_argument_generic(
    argument: &GenericArgument,
    index: u32,
    bindings: &OverlapBindings,
) -> bool {
    match argument {
        GenericArgument::Type(value) => contains_overlap_generic(value, index, bindings),
        GenericArgument::EffectRow(_)
        | GenericArgument::Lifetime(_)
        | GenericArgument::ConstU32(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. } => false,
    }
}

fn resolve_overlap_relation(
    relation: &crate::ElaboratedTraitReference,
    bindings: &OverlapBindings,
) -> crate::ElaboratedTraitReference {
    crate::ElaboratedTraitReference {
        definition: relation.definition,
        arguments: relation
            .arguments
            .iter()
            .map(|argument| resolve_overlap_argument(argument, bindings))
            .collect(),
    }
}

fn resolve_overlap_argument(
    argument: &GenericArgument,
    bindings: &OverlapBindings,
) -> GenericArgument {
    match argument {
        GenericArgument::Type(value) => {
            GenericArgument::Type(resolve_overlap_type(value, bindings))
        }
        argument => argument.clone(),
    }
}

fn resolve_overlap_type(value: &Type, bindings: &OverlapBindings) -> Type {
    match value {
        Type::Generic(index) => bindings
            .types
            .get(index)
            .map(|value| resolve_overlap_type(value, bindings))
            .unwrap_or_else(|| value.clone()),
        Type::Nominal {
            definition,
            arguments,
        } => Type::Nominal {
            definition: *definition,
            arguments: arguments
                .iter()
                .map(|argument| resolve_overlap_argument(argument, bindings))
                .collect(),
        },
        Type::Tuple(values) => Type::Tuple(
            values
                .iter()
                .map(|value| resolve_overlap_type(value, bindings))
                .collect(),
        ),
        Type::Array(value) => Type::Array(Box::new(resolve_overlap_type(value, bindings))),
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability: *mutability,
            lifetime: *lifetime,
            referent: Box::new(resolve_overlap_type(referent, bindings)),
        },
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_arguments,
        } => Type::Projection {
            subject: Box::new(resolve_overlap_type(subject, bindings)),
            trait_definition: *trait_definition,
            trait_arguments: trait_arguments
                .iter()
                .map(|argument| resolve_overlap_type(argument, bindings))
                .collect(),
            name: name.clone(),
            item_arguments: item_arguments
                .iter()
                .map(|argument| resolve_overlap_type(argument, bindings))
                .collect(),
        },
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
            lifetime_binders: *lifetime_binders,
            parameters: parameters
                .iter()
                .map(|parameter| resolve_overlap_type(parameter, bindings))
                .collect(),
            result: Box::new(resolve_overlap_type(result, bindings)),
            effects: effects.clone(),
            invocation: *invocation,
        },
        value => value.clone(),
    }
}

fn rebase_implementation_generics(
    implementation: &ElaboratedImplementation,
    offset: u32,
) -> ElaboratedImplementation {
    let mut implementation = implementation.clone();
    implementation.self_ty = rebase_overlap_type(&implementation.self_ty, offset);
    implementation.relation = rebase_overlap_relation(&implementation.relation, offset);
    implementation.where_bounds = implementation
        .where_bounds
        .iter()
        .map(|(subject, relation)| {
            (
                rebase_overlap_type(subject, offset),
                rebase_overlap_relation(relation, offset),
            )
        })
        .collect();
    implementation
}

fn rebase_overlap_relation(
    relation: &crate::ElaboratedTraitReference,
    offset: u32,
) -> crate::ElaboratedTraitReference {
    crate::ElaboratedTraitReference {
        definition: relation.definition,
        arguments: relation
            .arguments
            .iter()
            .map(|argument| match argument {
                GenericArgument::Type(value) => {
                    GenericArgument::Type(rebase_overlap_type(value, offset))
                }
                argument => argument.clone(),
            })
            .collect(),
    }
}

fn rebase_overlap_type(value: &Type, offset: u32) -> Type {
    match value {
        Type::Generic(index) => Type::Generic(index.saturating_add(offset)),
        Type::Nominal {
            definition,
            arguments,
        } => Type::Nominal {
            definition: *definition,
            arguments: arguments
                .iter()
                .map(|argument| rebase_overlap_argument(argument, offset))
                .collect(),
        },
        Type::Tuple(values) => Type::Tuple(
            values
                .iter()
                .map(|value| rebase_overlap_type(value, offset))
                .collect(),
        ),
        Type::Array(value) => Type::Array(Box::new(rebase_overlap_type(value, offset))),
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability: *mutability,
            lifetime: *lifetime,
            referent: Box::new(rebase_overlap_type(referent, offset)),
        },
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_arguments,
        } => Type::Projection {
            subject: Box::new(rebase_overlap_type(subject, offset)),
            trait_definition: *trait_definition,
            trait_arguments: trait_arguments
                .iter()
                .map(|argument| rebase_overlap_type(argument, offset))
                .collect(),
            name: name.clone(),
            item_arguments: item_arguments
                .iter()
                .map(|argument| rebase_overlap_type(argument, offset))
                .collect(),
        },
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
            lifetime_binders: *lifetime_binders,
            parameters: parameters
                .iter()
                .map(|parameter| rebase_overlap_type(parameter, offset))
                .collect(),
            result: Box::new(rebase_overlap_type(result, offset)),
            effects: effects.clone(),
            invocation: *invocation,
        },
        value => value.clone(),
    }
}

fn rebase_overlap_argument(argument: &GenericArgument, offset: u32) -> GenericArgument {
    match argument {
        GenericArgument::Type(value) => GenericArgument::Type(rebase_overlap_type(value, offset)),
        GenericArgument::ConstGeneric { index, kind } => GenericArgument::ConstGeneric {
            index: index.saturating_add(offset),
            kind: *kind,
        },
        argument => argument.clone(),
    }
}

fn unify_generic_argument(
    left: &HeaderGenericArgument,
    right: &HeaderGenericArgument,
    left_generics: &BTreeSet<String>,
    right_generics: &BTreeSet<String>,
    bindings: &mut Bindings,
) -> bool {
    match (left, right) {
        (HeaderGenericArgument::Type(left), HeaderGenericArgument::Type(right)) => {
            unify_type(left, right, left_generics, right_generics, bindings)
        }
        (HeaderGenericArgument::Lifetime(left), HeaderGenericArgument::Lifetime(right)) => {
            left == right || left_generics.contains(left) || right_generics.contains(right)
        }
        (HeaderGenericArgument::EffectRow(left), HeaderGenericArgument::EffectRow(right)) => {
            left == right
        }
        (HeaderGenericArgument::U32(left), HeaderGenericArgument::U32(right)) => left == right,
        (HeaderGenericArgument::Quantity(left), HeaderGenericArgument::Quantity(right)) => {
            left == right
        }
        _ => false,
    }
}

#[derive(Default)]
struct Bindings {
    left: BTreeMap<String, HeaderType>,
    right: BTreeMap<String, HeaderType>,
}

fn unify_type(
    left: &HeaderType,
    right: &HeaderType,
    left_generics: &BTreeSet<String>,
    right_generics: &BTreeSet<String>,
    bindings: &mut Bindings,
) -> bool {
    if let Some(name) = generic_name(left, left_generics) {
        return bind(
            bindings,
            BindingSide::Left,
            name,
            right,
            left_generics,
            right_generics,
        );
    }
    if let Some(name) = generic_name(right, right_generics) {
        return bind(
            bindings,
            BindingSide::Right,
            name,
            left,
            right_generics,
            left_generics,
        );
    }
    match (left, right) {
        (HeaderType::Path(left), HeaderType::Path(right)) => left == right,
        (
            HeaderType::Application(left_base, left_arguments),
            HeaderType::Application(right_base, right_arguments),
        ) => {
            left_arguments.len() == right_arguments.len()
                && unify_type(
                    left_base,
                    right_base,
                    left_generics,
                    right_generics,
                    bindings,
                )
                && left_arguments
                    .iter()
                    .zip(right_arguments)
                    .all(|(left, right)| match (left, right) {
                        (
                            crate::header::HeaderGenericArgument::Type(left),
                            crate::header::HeaderGenericArgument::Type(right),
                        ) => unify_type(left, right, left_generics, right_generics, bindings),
                        (
                            crate::header::HeaderGenericArgument::U32(left),
                            crate::header::HeaderGenericArgument::U32(right),
                        ) => left == right,
                        (
                            crate::header::HeaderGenericArgument::Quantity(left),
                            crate::header::HeaderGenericArgument::Quantity(right),
                        ) => left == right,
                        _ => false,
                    })
        }
        (HeaderType::Tuple(left), HeaderType::Tuple(right)) => {
            left.len() == right.len()
                && left.iter().zip(right).all(|(left, right)| {
                    unify_type(left, right, left_generics, right_generics, bindings)
                })
        }
        (
            HeaderType::Callable {
                lifetime_binders: left_binders,
                parameters: left_parameters,
                result: left_result,
            },
            HeaderType::Callable {
                lifetime_binders: right_binders,
                parameters: right_parameters,
                result: right_result,
            },
        ) => {
            left_binders.len() == right_binders.len()
                && left_parameters.len() == right_parameters.len()
                && left_parameters
                    .iter()
                    .zip(right_parameters)
                    .all(|(left, right)| {
                        unify_type(left, right, left_generics, right_generics, bindings)
                    })
                && unify_type(
                    left_result,
                    right_result,
                    left_generics,
                    right_generics,
                    bindings,
                )
        }
        (
            HeaderType::Reference {
                unique: left_unique,
                referent: left_referent,
                ..
            },
            HeaderType::Reference {
                unique: right_unique,
                referent: right_referent,
                ..
            },
        ) => {
            left_unique == right_unique
                && unify_type(
                    left_referent,
                    right_referent,
                    left_generics,
                    right_generics,
                    bindings,
                )
        }
        (HeaderType::Never, HeaderType::Never)
        | (HeaderType::Recovered, _)
        | (_, HeaderType::Recovered) => true,
        _ => false,
    }
}

fn generic_name<'a>(value: &'a HeaderType, names: &'a BTreeSet<String>) -> Option<&'a String> {
    match value {
        HeaderType::Path(path) if path.len() == 1 => names.get(&path[0]),
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum BindingSide {
    Left,
    Right,
}

fn bind(
    bindings: &mut Bindings,
    side: BindingSide,
    name: &String,
    value: &HeaderType,
    own_generics: &BTreeSet<String>,
    other_generics: &BTreeSet<String>,
) -> bool {
    let existing = match side {
        BindingSide::Left => bindings.left.get(name).cloned(),
        BindingSide::Right => bindings.right.get(name).cloned(),
    };
    let Some(existing) = existing else {
        match side {
            BindingSide::Left => {
                bindings.left.insert(name.clone(), value.clone());
            }
            BindingSide::Right => {
                bindings.right.insert(name.clone(), value.clone());
            }
        }
        return true;
    };
    unify_type(&existing, value, own_generics, other_generics, bindings)
}
