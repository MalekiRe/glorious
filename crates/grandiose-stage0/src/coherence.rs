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
    /// The prior implementation participating in an overlap, when this is a
    /// two-site coherence failure.  This remains a source fact rather than a
    /// byte offset embedded in the message so the service can publish it as a
    /// structured related location.
    pub related_span: Option<Span>,
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
    pub effect_row_generics: BTreeSet<String>,
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
                    related_span: None,
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
                effect_row_generics: header
                    .generics
                    .iter()
                    .filter(|name| header.generics.is_effect_row(name))
                    .cloned()
                    .collect(),
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
                    related_span: Some(left.span),
                    message: message.into(),
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
                related_span: None,
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
                related_span: None,
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
                related_span: None,
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
                related_span: None,
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
                related_span: None,
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
            related_span: None,
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
            parameters,
            result,
            effects,
            ..
        } => {
            for parameter in parameters {
                collect_generic_names(parameter, declared, used);
            }
            collect_generic_names(result, declared, used);
            for effect in &effects.effects {
                collect_generic_names(effect, declared, used);
            }
            if let Some(tail) = &effects.tail
                && declared.contains(tail)
            {
                used.insert(tail.clone());
            }
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
        | HeaderGenericArgument::StructuralConst(_)
        | HeaderGenericArgument::Quantity(_)
        | HeaderGenericArgument::Lifetime(_) => {}
    }
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

#[derive(Clone, Default)]
struct OverlapBindings {
    types: BTreeMap<u32, Type>,
    lifetimes: BTreeMap<u32, crate::Lifetime>,
    effect_rows: BTreeMap<u32, crate::EffectRow>,
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
        (GenericArgument::Lifetime(crate::Lifetime::Generic(index)), right) => {
            bind_overlap_lifetime(*index, right, bindings)
        }
        (left, GenericArgument::Lifetime(crate::Lifetime::Generic(index))) => {
            bind_overlap_lifetime(*index, left, bindings)
        }
        (GenericArgument::EffectRow(left), GenericArgument::EffectRow(right)) => {
            unify_overlap_effect_row(left, right, bindings).map(GenericArgument::EffectRow)
        }
        (
            GenericArgument::ConstProjection {
                subject: left_subject,
                trait_definition: left_trait,
                trait_arguments: left_arguments,
                name: left_name,
                kind: left_kind,
            },
            GenericArgument::ConstProjection {
                subject: right_subject,
                trait_definition: right_trait,
                trait_arguments: right_arguments,
                name: right_name,
                kind: right_kind,
            },
        ) if left_trait == right_trait
            && left_name == right_name
            && left_kind == right_kind
            && left_arguments.len() == right_arguments.len() =>
        {
            Some(GenericArgument::ConstProjection {
                subject: Box::new(unify_overlap_type(left_subject, right_subject, bindings)?),
                trait_definition: *left_trait,
                trait_arguments: left_arguments
                    .iter()
                    .zip(right_arguments)
                    .map(|(left, right)| unify_overlap_argument(left, right, bindings))
                    .collect::<Option<_>>()?,
                name: left_name.clone(),
                kind: *left_kind,
            })
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

fn bind_overlap_lifetime(
    index: u32,
    value: &GenericArgument,
    bindings: &mut OverlapBindings,
) -> Option<GenericArgument> {
    let GenericArgument::Lifetime(value) = value else {
        return None;
    };
    match bindings.lifetimes.get(&index) {
        Some(previous) if previous != value => None,
        Some(previous) => Some(GenericArgument::Lifetime(*previous)),
        None => {
            bindings.lifetimes.insert(index, *value);
            Some(GenericArgument::Lifetime(*value))
        }
    }
}

fn unify_overlap_effect_row(
    left: &crate::EffectRow,
    right: &crate::EffectRow,
    bindings: &mut OverlapBindings,
) -> Option<crate::EffectRow> {
    if let Some(index) = pure_generic_effect_row(left) {
        return bind_overlap_effect_row(index, right, bindings);
    }
    if let Some(index) = pure_generic_effect_row(right) {
        return bind_overlap_effect_row(index, left, bindings);
    }
    if left.effects.len() != right.effects.len()
        || left.projections.len() != right.projections.len()
    {
        return None;
    }
    // A failed match must not leak its partial bindings into another type or
    // projection candidate.  Publish this row's bindings only as one unit.
    let mut row_bindings = bindings.clone();

    // Effect rows are sets, so their canonical ordering must not turn a
    // generic argument in one implementation head into accidental evidence
    // that two otherwise equal rows are disjoint.  Keep the matching
    // transactional: a failed candidate must not publish any of its generic
    // bindings into the next candidate.
    let mut unmatched = right.effects.iter().cloned().collect::<Vec<_>>();
    let mut effects = BTreeSet::new();
    for left_effect in &left.effects {
        let mut selected = None;
        for (index, right_effect) in unmatched.iter().enumerate() {
            if left_effect.definition != right_effect.definition
                || left_effect.arguments.len() != right_effect.arguments.len()
            {
                continue;
            }
            let mut trial = row_bindings.clone();
            let Some(arguments) = left_effect
                .arguments
                .iter()
                .zip(&right_effect.arguments)
                .map(|(left, right)| unify_overlap_argument(left, right, &mut trial))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            selected = Some((index, trial, arguments));
            break;
        }
        let (index, trial, arguments) = selected?;
        row_bindings = trial;
        unmatched.remove(index);
        effects.insert(crate::EffectInstance {
            definition: left_effect.definition,
            arguments,
        });
    }

    let mut projections = Vec::with_capacity(left.projections.len());
    for (left_projection, right_projection) in left.projections.iter().zip(&right.projections) {
        if left_projection.trait_definition != right_projection.trait_definition
            || left_projection.name != right_projection.name
            || left_projection.item_generic_kinds != right_projection.item_generic_kinds
            || left_projection.trait_arguments.len() != right_projection.trait_arguments.len()
            || left_projection.item_arguments.len() != right_projection.item_arguments.len()
        {
            return None;
        }
        projections.push(crate::EffectRowProjection {
            subject: Box::new(unify_overlap_type(
                &left_projection.subject,
                &right_projection.subject,
                &mut row_bindings,
            )?),
            trait_definition: left_projection.trait_definition,
            trait_arguments: left_projection
                .trait_arguments
                .iter()
                .zip(&right_projection.trait_arguments)
                .map(|(left, right)| unify_overlap_argument(left, right, &mut row_bindings))
                .collect::<Option<Vec<_>>>()?,
            name: left_projection.name.clone(),
            item_generic_kinds: left_projection.item_generic_kinds.clone(),
            item_arguments: left_projection
                .item_arguments
                .iter()
                .zip(&right_projection.item_arguments)
                .map(|(left, right)| unify_overlap_argument(left, right, &mut row_bindings))
                .collect::<Option<Vec<_>>>()?,
        });
    }
    let tail = unify_overlap_effect_tail(left.tail, right.tail, &mut row_bindings)?;
    let result = crate::EffectRow {
        effects,
        projections,
        tail,
    }
    .canonicalized();
    *bindings = row_bindings;
    Some(result)
}

/// Unify the residual of two already-aligned effect rows.  A declaration row
/// variable denotes an arbitrary residual, so `{Trace | e}` and
/// `{Trace | f}` overlap even when `e` and `f` occupy distinct implementation
/// binder slots.  Record the smallest witness (`e = f`), represented as a
/// pure row, rather than treating slot identity as semantic evidence of
/// disjointness.
fn unify_overlap_effect_tail(
    left: Option<crate::EffectTail>,
    right: Option<crate::EffectTail>,
    bindings: &mut OverlapBindings,
) -> Option<Option<crate::EffectTail>> {
    match (left, right) {
        (left, right) if left == right => Some(left),
        (Some(crate::EffectTail::Generic(left)), Some(crate::EffectTail::Generic(right))) => {
            let row = crate::EffectRow {
                effects: BTreeSet::new(),
                projections: vec![],
                tail: Some(crate::EffectTail::Generic(right)),
            };
            bind_overlap_effect_row(left, &row, bindings)?;
            Some(Some(crate::EffectTail::Generic(right)))
        }
        (Some(crate::EffectTail::Generic(index)), None) => {
            bind_overlap_effect_row(index, &crate::EffectRow::empty(), bindings)?;
            Some(None)
        }
        (None, Some(crate::EffectTail::Generic(index))) => {
            bind_overlap_effect_row(index, &crate::EffectRow::empty(), bindings)?;
            Some(None)
        }
        // Body-local inference tails cannot appear in a frozen interface;
        // retaining this conservative arm prevents malformed fixtures from
        // manufacturing an overlap proof.
        _ => None,
    }
}

fn pure_generic_effect_row(value: &crate::EffectRow) -> Option<u32> {
    (value.effects.is_empty() && value.projections.is_empty())
        .then_some(value.tail)
        .flatten()
        .and_then(|tail| match tail {
            crate::EffectTail::Generic(index) => Some(index),
            crate::EffectTail::Infer(_) => None,
        })
}

fn bind_overlap_effect_row(
    index: u32,
    value: &crate::EffectRow,
    bindings: &mut OverlapBindings,
) -> Option<crate::EffectRow> {
    match bindings.effect_rows.get(&index) {
        Some(previous) if previous != value => None,
        Some(previous) => Some(previous.clone()),
        None => {
            bindings.effect_rows.insert(index, value.clone());
            Some(value.clone())
        }
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
        ) if left_mutability == right_mutability => {
            let lifetime = unify_overlap_lifetime(*left_lifetime, *right_lifetime, bindings)?;
            unify_overlap_type(left_referent, right_referent, bindings).map(|referent| {
                Type::Reference {
                    mutability: *left_mutability,
                    lifetime,
                    referent: Box::new(referent),
                }
            })
        }
        (
            Type::Callable {
                lifetime_binders: left_binders,
                parameters: left_parameters,
                result: left_result,
                effects: left_effects,
                invocation: left_invocation,
            },
            Type::Callable {
                lifetime_binders: right_binders,
                parameters: right_parameters,
                result: right_result,
                effects: right_effects,
                invocation: right_invocation,
            },
        ) if left_binders == right_binders
            && left_parameters.len() == right_parameters.len()
            && left_invocation == right_invocation =>
        {
            let parameters = left_parameters
                .iter()
                .zip(right_parameters)
                .map(|(left, right)| unify_overlap_type(left, right, bindings))
                .collect::<Option<Vec<_>>>()?;
            let result = unify_overlap_type(left_result, right_result, bindings)?;
            let effects = unify_overlap_effect_row(left_effects, right_effects, bindings)?;
            Some(Type::Callable {
                lifetime_binders: *left_binders,
                parameters,
                result: Box::new(result),
                effects,
                invocation: *left_invocation,
            })
        }
        (
            Type::Projection {
                subject: left_subject,
                trait_definition: left_trait,
                trait_arguments: left_trait_arguments,
                name: left_name,
                item_generic_kinds: left_item_kinds,
                item_arguments: left_item_arguments,
            },
            Type::Projection {
                subject: right_subject,
                trait_definition: right_trait,
                trait_arguments: right_trait_arguments,
                name: right_name,
                item_generic_kinds: right_item_kinds,
                item_arguments: right_item_arguments,
            },
        ) if left_trait == right_trait
            && left_name == right_name
            && left_item_kinds == right_item_kinds
            && left_trait_arguments.len() == right_trait_arguments.len()
            && left_item_arguments.len() == right_item_arguments.len() =>
        {
            let subject = unify_overlap_type(left_subject, right_subject, bindings)?;
            let trait_arguments = left_trait_arguments
                .iter()
                .zip(right_trait_arguments)
                .map(|(left, right)| unify_overlap_argument(left, right, bindings))
                .collect::<Option<Vec<_>>>()?;
            let item_arguments = left_item_arguments
                .iter()
                .zip(right_item_arguments)
                .map(|(left, right)| unify_overlap_argument(left, right, bindings))
                .collect::<Option<Vec<_>>>()?;
            Some(Type::Projection {
                subject: Box::new(subject),
                trait_definition: *left_trait,
                trait_arguments,
                name: left_name.clone(),
                item_generic_kinds: left_item_kinds.clone(),
                item_arguments,
            })
        }
        (left, right) if left == right => Some(left.clone()),
        _ => None,
    }
}

/// Bound lifetimes are already alpha-canonical (De Bruijn depth/index), so
/// they are rigid while comparing two HRTB heads.  Declaration-generic
/// lifetimes, in contrast, are existential variables of an implementation
/// head and must participate in the same overlap witness as generic types.
fn unify_overlap_lifetime(
    left: crate::Lifetime,
    right: crate::Lifetime,
    bindings: &mut OverlapBindings,
) -> Option<crate::Lifetime> {
    match (left, right) {
        (crate::Lifetime::Generic(left), crate::Lifetime::Generic(right)) if left == right => {
            Some(crate::Lifetime::Generic(left))
        }
        (crate::Lifetime::Generic(index), value) => {
            bind_overlap_lifetime_value(index, value, bindings)
        }
        (value, crate::Lifetime::Generic(index)) => {
            bind_overlap_lifetime_value(index, value, bindings)
        }
        (left, right) if left == right => Some(left),
        _ => None,
    }
}

fn bind_overlap_lifetime_value(
    index: u32,
    value: crate::Lifetime,
    bindings: &mut OverlapBindings,
) -> Option<crate::Lifetime> {
    match bindings.lifetimes.get(&index) {
        Some(previous) if *previous != value => None,
        Some(previous) => Some(*previous),
        None => {
            bindings.lifetimes.insert(index, value);
            Some(value)
        }
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
                    .any(|argument| contains_overlap_argument_generic(argument, index, bindings))
                || item_arguments
                    .iter()
                    .any(|argument| contains_overlap_argument_generic(argument, index, bindings))
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
        GenericArgument::ConstProjection {
            subject,
            trait_arguments,
            ..
        } => {
            contains_overlap_generic(subject, index, bindings)
                || trait_arguments
                    .iter()
                    .any(|argument| contains_overlap_argument_generic(argument, index, bindings))
        }
        GenericArgument::EffectRow(_)
        | GenericArgument::Lifetime(_)
        | GenericArgument::ConstU32(_)
        | GenericArgument::ConstU32Expr(_)
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
        GenericArgument::Lifetime(crate::Lifetime::Generic(index)) => bindings
            .lifetimes
            .get(index)
            .copied()
            .map(GenericArgument::Lifetime)
            .unwrap_or_else(|| argument.clone()),
        GenericArgument::EffectRow(value) => {
            if let Some(index) = pure_generic_effect_row(value)
                && let Some(row) = bindings.effect_rows.get(&index)
            {
                return GenericArgument::EffectRow(row.clone());
            }
            argument.clone()
        }
        GenericArgument::ConstProjection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            kind,
        } => GenericArgument::ConstProjection {
            subject: Box::new(resolve_overlap_type(subject, bindings)),
            trait_definition: *trait_definition,
            trait_arguments: trait_arguments
                .iter()
                .map(|argument| resolve_overlap_argument(argument, bindings))
                .collect(),
            name: name.clone(),
            kind: *kind,
        },
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
            lifetime: match lifetime {
                crate::Lifetime::Generic(index) => {
                    bindings.lifetimes.get(index).copied().unwrap_or(*lifetime)
                }
                lifetime => *lifetime,
            },
            referent: Box::new(resolve_overlap_type(referent, bindings)),
        },
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_generic_kinds,
            item_arguments,
        } => Type::Projection {
            subject: Box::new(resolve_overlap_type(subject, bindings)),
            trait_definition: *trait_definition,
            trait_arguments: trait_arguments
                .iter()
                .map(|argument| resolve_overlap_argument(argument, bindings))
                .collect(),
            name: name.clone(),
            item_generic_kinds: item_generic_kinds.clone(),
            item_arguments: item_arguments
                .iter()
                .map(|argument| resolve_overlap_argument(argument, bindings))
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
            effects: resolve_overlap_effect_row(effects, bindings),
            invocation: *invocation,
        },
        value => value.clone(),
    }
}

fn resolve_overlap_effect_row(
    value: &crate::EffectRow,
    bindings: &OverlapBindings,
) -> crate::EffectRow {
    if let Some(index) = pure_generic_effect_row(value)
        && let Some(row) = bindings.effect_rows.get(&index)
    {
        return row.clone();
    }
    crate::EffectRow {
        effects: value
            .effects
            .iter()
            .map(|effect| crate::EffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .iter()
                    .map(|argument| resolve_overlap_argument(argument, bindings))
                    .collect(),
            })
            .collect(),
        projections: value
            .projections
            .iter()
            .map(|projection| crate::EffectRowProjection {
                subject: Box::new(resolve_overlap_type(&projection.subject, bindings)),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .iter()
                    .map(|argument| resolve_overlap_argument(argument, bindings))
                    .collect(),
                name: projection.name.clone(),
                item_generic_kinds: projection.item_generic_kinds.clone(),
                item_arguments: projection
                    .item_arguments
                    .iter()
                    .map(|argument| resolve_overlap_argument(argument, bindings))
                    .collect(),
            })
            .collect(),
        tail: value.tail,
    }
    .canonicalized()
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
            .map(|argument| rebase_overlap_argument(argument, offset))
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
            lifetime: match lifetime {
                crate::Lifetime::Generic(index) => {
                    crate::Lifetime::Generic(index.saturating_add(offset))
                }
                lifetime => *lifetime,
            },
            referent: Box::new(rebase_overlap_type(referent, offset)),
        },
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_generic_kinds,
            item_arguments,
        } => Type::Projection {
            subject: Box::new(rebase_overlap_type(subject, offset)),
            trait_definition: *trait_definition,
            trait_arguments: trait_arguments
                .iter()
                .map(|argument| rebase_overlap_argument(argument, offset))
                .collect(),
            name: name.clone(),
            item_generic_kinds: item_generic_kinds.clone(),
            item_arguments: item_arguments
                .iter()
                .map(|argument| rebase_overlap_argument(argument, offset))
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
            effects: rebase_overlap_effect_row(effects, offset),
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
        GenericArgument::Lifetime(crate::Lifetime::Generic(index)) => {
            GenericArgument::Lifetime(crate::Lifetime::Generic(index.saturating_add(offset)))
        }
        GenericArgument::EffectRow(value) => {
            GenericArgument::EffectRow(rebase_overlap_effect_row(value, offset))
        }
        GenericArgument::ConstProjection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            kind,
        } => GenericArgument::ConstProjection {
            subject: Box::new(rebase_overlap_type(subject, offset)),
            trait_definition: *trait_definition,
            trait_arguments: trait_arguments
                .iter()
                .map(|argument| rebase_overlap_argument(argument, offset))
                .collect(),
            name: name.clone(),
            kind: *kind,
        },
        argument => argument.clone(),
    }
}

fn rebase_overlap_effect_row(value: &crate::EffectRow, offset: u32) -> crate::EffectRow {
    crate::EffectRow {
        effects: value
            .effects
            .iter()
            .map(|effect| crate::EffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .iter()
                    .map(|argument| rebase_overlap_argument(argument, offset))
                    .collect(),
            })
            .collect(),
        projections: value
            .projections
            .iter()
            .map(|projection| crate::EffectRowProjection {
                subject: Box::new(rebase_overlap_type(&projection.subject, offset)),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .iter()
                    .map(|argument| rebase_overlap_argument(argument, offset))
                    .collect(),
                name: projection.name.clone(),
                item_generic_kinds: projection.item_generic_kinds.clone(),
                item_arguments: projection
                    .item_arguments
                    .iter()
                    .map(|argument| rebase_overlap_argument(argument, offset))
                    .collect(),
            })
            .collect(),
        tail: value.tail.map(|tail| match tail {
            crate::EffectTail::Generic(index) => {
                crate::EffectTail::Generic(index.saturating_add(offset))
            }
            crate::EffectTail::Infer(index) => crate::EffectTail::Infer(index),
        }),
    }
    .canonicalized()
}

#[cfg(test)]
mod frozen_overlap_tests {
    use std::collections::BTreeSet;

    use super::{OverlapBindings, unify_overlap_type};
    use crate::{
        EffectInstance, EffectRow, EffectTail, GenericArgument, Lifetime, Mutability, Quantity,
        ScalarType, Type,
        identity::{DefKey, Digest},
    };

    fn trace() -> DefKey {
        DefKey(Digest::of_bytes(b"coherence-frozen-hrtb-trace"))
    }

    fn higher_ranked(referent: Type, tail: u32) -> Type {
        Type::Callable {
            lifetime_binders: 1,
            parameters: vec![Type::Reference {
                mutability: Mutability::Shared,
                lifetime: Lifetime::Bound { depth: 0, index: 0 },
                referent: Box::new(referent.clone()),
            }],
            result: Box::new(Type::Reference {
                mutability: Mutability::Shared,
                lifetime: Lifetime::Bound { depth: 0, index: 0 },
                referent: Box::new(referent),
            }),
            effects: EffectRow {
                effects: BTreeSet::from([EffectInstance {
                    definition: trace(),
                    arguments: vec![GenericArgument::Type(Type::Generic(0))],
                }]),
                projections: vec![],
                tail: Some(EffectTail::Generic(tail)),
            },
            invocation: Quantity::ONCE,
        }
    }

    #[test]
    fn frozen_hrtb_overlap_unifies_reference_binders_and_open_effect_tails() {
        let mut bindings = OverlapBindings::default();
        let left = higher_ranked(Type::Generic(0), 1);
        let right = higher_ranked(Type::Scalar(ScalarType::I64), 2);
        assert!(
            unify_overlap_type(&left, &right, &mut bindings).is_some(),
            "distinct generic residual slots describe one common HRTB witness"
        );
    }

    #[test]
    fn failed_effect_matching_does_not_publish_partial_overlap_bindings() {
        let mut bindings = OverlapBindings::default();
        let left = EffectRow {
            effects: BTreeSet::from([
                EffectInstance {
                    definition: DefKey(Digest::of_bytes(b"coherence-a")),
                    arguments: vec![GenericArgument::Type(Type::Generic(9))],
                },
                EffectInstance {
                    definition: DefKey(Digest::of_bytes(b"coherence-b")),
                    arguments: vec![GenericArgument::Type(Type::Generic(9))],
                },
            ]),
            projections: vec![],
            tail: None,
        };
        let right = EffectRow {
            effects: BTreeSet::from([
                EffectInstance {
                    definition: DefKey(Digest::of_bytes(b"coherence-a")),
                    arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
                },
                EffectInstance {
                    definition: DefKey(Digest::of_bytes(b"coherence-b")),
                    arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::Bool))],
                },
            ]),
            projections: vec![],
            tail: None,
        };
        assert!(super::unify_overlap_effect_row(&left, &right, &mut bindings).is_none());
        assert!(
            bindings.types.is_empty(),
            "failed candidate leaked a type binding"
        );
    }
}
