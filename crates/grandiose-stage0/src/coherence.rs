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
    source::Span,
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
            let self_local = resolve_self_head(index, &module, &header.self_ty)
                .and_then(|definition| index.owner(definition))
                .is_some_and(|owner| owner.package == module.package);
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
                if left.trait_definition != right.trait_definition || !heads_may_unify(left, right)
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

fn resolve_self_head(
    index: &DefinitionIndex,
    module: &ModuleKey,
    ty: &HeaderType,
) -> Option<DefKey> {
    let path = match ty {
        HeaderType::Path(path) => path,
        HeaderType::Application(base, _) => return resolve_self_head(index, module, base),
        _ => return None,
    };
    match index.resolve_path(DefinitionNamespace::Type, module, path) {
        ResolutionState::Resolved(definition) => Some(definition),
        _ => None,
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
