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
        // Every pair sees the same frozen interface. Share its immutable
        // solver data; overlap probes still own separate tables and budgets.
        let solver = TraitSolver::new(signatures);
        for (offset, left) in heads.iter().enumerate() {
            for right in &heads[offset + 1..] {
                if left.trait_definition != right.trait_definition
                    || !implementations_may_overlap(left, right, signatures, &solver)
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
        HeaderType::FixedArray { element, length } => {
            collect_generic_names(element, declared, used);
            collect_generic_argument_names(&HeaderGenericArgument::StructuralConst((**length).clone()), declared, used);
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
        HeaderType::RawPointer { pointee, .. } => collect_generic_names(pointee, declared, used),
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
            for tail in effects.tails.iter().filter(|tail| declared.contains(*tail)) {
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
        HeaderGenericArgument::AssociatedTypeBinding {
            item_arguments,
            value,
            ..
        } => {
            for argument in item_arguments {
                collect_generic_argument_names(argument, declared, used);
            }
            collect_generic_names(value, declared, used);
        }
        HeaderGenericArgument::AssociatedEffectBinding {
            item_arguments,
            value,
            ..
        } => {
            for argument in item_arguments {
                collect_generic_argument_names(argument, declared, used);
            }
            for effect in &value.effects {
                collect_generic_names(effect, declared, used);
            }
            for tail in value.tails.iter().filter(|tail| declared.contains(*tail)) {
                used.insert(tail.clone());
            }
        }
        HeaderGenericArgument::Lifetime(value) if declared.contains(value) => {
            used.insert(value.clone());
        }
        HeaderGenericArgument::EffectRow(value) => {
            for effect in &value.effects {
                collect_generic_names(effect, declared, used);
            }
            for tail in value.tails.iter().filter(|tail| declared.contains(*tail)) {
                used.insert(tail.clone());
            }
        }
        HeaderGenericArgument::StructuralConst(value) => {
            use crate::header::{HeaderStructuralConst as Const, HeaderIntegerExpr as Expr};
            fn expression(value: &Expr, declared: &BTreeSet<String>, used: &mut BTreeSet<String>) {
                match value {
                    Expr::Param(name) if declared.contains(name) => { used.insert(name.clone()); }
                    Expr::Neg(value) => expression(value, declared, used),
                    Expr::Add(left, right) | Expr::Sub(left, right) | Expr::Mul(left, right)
                    | Expr::Div(left, right) | Expr::Rem(left, right) => {
                        expression(left, declared, used); expression(right, declared, used);
                    }
                    _ => {}
                }
            }
            match value {
                Const::Generic(name) if declared.contains(name) => { used.insert(name.clone()); }
                Const::IntegerExpression(value) => expression(value, declared, used),
                Const::Projection(value) => collect_generic_names(value, declared, used),
                _ => {}
            }
        }
        HeaderGenericArgument::Integer(_)
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
    snapshot: &TraitSolver,
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
    let mut solver = snapshot.fresh_query();
    let left = normalize_overlap_implementation(left, &mut solver);
    let right = normalize_overlap_implementation(&right, &mut solver);
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
    if !solve_overlap_effect_unions(&mut bindings) {
        return false;
    }
    let witness = TraitGoal {
        relation: crate::ElaboratedTraitReference {
            definition: left.relation.definition,
            arguments,
        },
        subject,
    };
    // An overlap witness is existential. Positive outlives requirements
    // cannot separate two heads: every free region can be chosen static and
    // every free value type can be chosen to contain no shorter borrow.
    // Install that witness before querying conditional trait implementations,
    // otherwise a missing lexical `T: 'static` fact masquerades as disjointness.
    let mut outlives = vec![];
    for (index, kind) in left.generic_kinds.iter().chain(&right.generic_kinds).enumerate() {
        match kind {
            crate::GenericKind::Type => outlives.push(crate::OutlivesPredicate::Type {
                subject: resolve_overlap_type(&Type::Generic(index as u32), &bindings),
                lifetime: crate::Lifetime::Static,
            }),
            crate::GenericKind::Lifetime => {
                let GenericArgument::Lifetime(longer) = resolve_overlap_argument(
                    &GenericArgument::Lifetime(crate::Lifetime::Generic(index as u32)), &bindings) else { unreachable!(); };
                outlives.push(crate::OutlivesPredicate::Region { longer, shorter: crate::Lifetime::Static });
            },
            _ => {},
        }
    }
    solver.set_outlives_assumptions(outlives);
    // Universal requirements are facts of this common existential domain,
    // not a reason to invent disjointness when a conditional impl needs one.
    // Inconsistent universal domains remain conservatively overlapping.
    solver.set_universal_assumptions(left.universal_bounds.iter().chain(&right.universal_bounds)
        .map(|bound| bound.map_terms(|argument| resolve_overlap_argument(&argument, &bindings))).collect());
    if !overlap_associated_equalities(&left, &right, &mut bindings, &mut solver) { return false; }
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

/// Coherence compares implementation heads in the same semantic domain used
/// by trait selection.  In particular, `<i64 as Source>::Output` must not
/// remain an opaque head when selection has already frozen it as `i64`.
/// Projection failures keep their original structure so malformed or
/// symbolic interfaces remain conservatively checked by the legacy matcher.
fn normalize_overlap_implementation(
    implementation: &ElaboratedImplementation,
    solver: &mut TraitSolver,
) -> ElaboratedImplementation {
    let mut implementation = implementation.clone();
    implementation.self_ty = solver
        .normalize_type(implementation.self_ty.clone())
        .unwrap_or(implementation.self_ty);
    implementation.relation.arguments = implementation
        .relation
        .arguments
        .clone()
        .into_iter()
        .map(|argument| normalize_overlap_argument(argument, solver))
        .collect();
    implementation.where_bounds = implementation
        .where_bounds
        .clone()
        .into_iter()
        .map(|(subject, mut relation)| {
            let subject = solver.normalize_type(subject.clone()).unwrap_or(subject);
            relation.arguments = relation
                .arguments
                .into_iter()
                .map(|argument| normalize_overlap_argument(argument, solver))
                .collect();
            (subject, relation)
        })
        .collect();
    map_implementation_associated_constraints(&mut implementation, |argument| normalize_overlap_argument(argument, solver));
    implementation
}

fn map_implementation_associated_constraints(
    implementation: &mut ElaboratedImplementation,
    mut map: impl FnMut(GenericArgument) -> GenericArgument,
) {
    implementation.universal_bounds = implementation.universal_bounds.iter().map(|bound| bound.map_terms(&mut map)).collect();
    let contract = crate::AssociatedItemContract {
        where_bounds: vec![], where_outlives: implementation.where_outlives.clone(),
        type_bindings: implementation.where_associated_type_bindings.clone(),
        effect_bindings: implementation.where_associated_effect_bindings.clone(),
    }.map_terms(map);
    implementation.where_outlives = contract.where_outlives;
    implementation.where_associated_type_bindings = contract.type_bindings;
    implementation.where_associated_effect_bindings = contract.effect_bindings;
}

/// Associated equalities constrain the same existential overlap witness as
/// the implementation heads. A shared projection cannot simultaneously be
/// two incompatible types or effect rows.
fn overlap_associated_equalities(
    left: &ElaboratedImplementation, right: &ElaboratedImplementation,
    bindings: &mut OverlapBindings, solver: &mut TraitSolver,
) -> bool {
    let mut types = BTreeMap::<Vec<u8>, Type>::new();
    for binding in left.where_associated_type_bindings.iter().chain(&right.where_associated_type_bindings) {
        let subject = resolve_overlap_type(&binding.subject, bindings);
        let relation = resolve_overlap_relation(&binding.relation, bindings);
        let arguments = binding.item_arguments.iter().map(|argument| resolve_overlap_argument(argument, bindings)).collect::<Vec<_>>();
        let projection = Type::Projection { subject: Box::new(subject.clone()), trait_definition: relation.definition,
            trait_arguments: relation.arguments.clone(), name: binding.name.clone(),
            item_generic_kinds: binding.item_generic_kinds.clone(), item_arguments: arguments.clone() };
        let value = resolve_overlap_type(&binding.value, bindings);
        if let crate::TraitProjectionAnswer::Normalized { ty, .. } = solver.normalize_associated_type_application(
            TraitGoal { subject, relation }, &binding.name, &arguments) {
            if unify_overlap_type(&value, &ty, bindings).is_none() { return false; }
        }
        let key = crate::types::canonical_type_encoding(&projection);
        if let Some(previous) = types.get(&key) {
            if unify_overlap_type(previous, &value, bindings).is_none() { return false; }
        } else { types.insert(key, value); }
    }
    let mut effects = BTreeMap::<Vec<u8>, crate::EffectRow>::new();
    for binding in left.where_associated_effect_bindings.iter().chain(&right.where_associated_effect_bindings) {
        let subject = resolve_overlap_type(&binding.subject, bindings);
        let relation = resolve_overlap_relation(&binding.relation, bindings);
        let arguments = binding.item_arguments.iter().map(|argument| resolve_overlap_argument(argument, bindings)).collect::<Vec<_>>();
        let projection = Type::Projection { subject: Box::new(subject.clone()), trait_definition: relation.definition,
            trait_arguments: relation.arguments.clone(), name: binding.name.clone(),
            item_generic_kinds: binding.item_generic_kinds.clone(), item_arguments: arguments.clone() };
        let GenericArgument::EffectRow(value) = resolve_overlap_argument(&GenericArgument::EffectRow(binding.value.clone()), bindings) else { unreachable!(); };
        if let crate::TraitEffectRowProjectionAnswer::Normalized { row, .. } = solver.normalize_associated_effect_row_application(
            TraitGoal { subject, relation }, &binding.name, &arguments) {
            if unify_overlap_argument(&GenericArgument::EffectRow(value.clone()), &GenericArgument::EffectRow(row), bindings).is_none() { return false; }
        }
        let key = crate::types::canonical_type_encoding(&projection);
        if let Some(previous) = effects.get(&key) {
            if unify_overlap_argument(&GenericArgument::EffectRow(previous.clone()), &GenericArgument::EffectRow(value), bindings).is_none() { return false; }
        } else { effects.insert(key, value); }
    }
    solve_overlap_effect_unions(bindings)
}

fn normalize_overlap_argument(
    argument: GenericArgument,
    solver: &mut TraitSolver,
) -> GenericArgument {
    match argument {
        GenericArgument::EffectRow(row) => solver
            .normalize_effect_row(row.clone())
            .map(GenericArgument::EffectRow)
            .unwrap_or(GenericArgument::EffectRow(row)),
        argument => solver
            .normalize_generic_argument(argument.clone())
            .unwrap_or(argument),
    }
}

#[derive(Clone, Default)]
struct OverlapBindings {
    types: BTreeMap<u32, Type>,
    lifetimes: BTreeMap<u32, crate::Lifetime>,
    effect_rows: BTreeMap<u32, crate::EffectRow>,
    effect_equations: Vec<(crate::EffectRow, crate::EffectRow)>,
}

/// Coherence needs an existential witness, not a unique inferred partition.
/// For each known effect atom, row equality is equality of two disjunctions
/// of membership variables. Propagate forced absence from an empty side;
/// assigning every remaining variable presence is a maximal satisfying
/// witness. Unknown atoms can all be absent. This is polynomial and retains
/// correlations between operands appearing in several head arguments.
fn solve_overlap_effect_unions(bindings: &mut OverlapBindings) -> bool {
    let equations = std::mem::take(&mut bindings.effect_equations);
    let equations: Vec<_> = equations.into_iter().map(|(left, right)|
        (resolve_overlap_effect_row(&left, bindings), resolve_overlap_effect_row(&right, bindings)))
        .collect();
    let mut atoms = BTreeMap::new();
    let mut variables = BTreeSet::new();
    for row in equations.iter().flat_map(|(left, right)| [left, right]) {
        for tail in &row.tails {
            let crate::EffectTail::Generic(index) = tail else { return false; };
            variables.insert(*index);
        }
        for effect in &row.effects {
            let atom = crate::EffectRow::closed_instances([effect.clone()]);
            atoms.insert(crate::types::canonical_generic_arguments_encoding(&[GenericArgument::EffectRow(atom.clone())]), atom);
        }
        for projection in &row.projections {
            let atom = crate::EffectRow { effects: BTreeSet::new(), projections: vec![projection.clone()], tails: BTreeSet::new() };
            atoms.insert(crate::types::canonical_generic_arguments_encoding(&[GenericArgument::EffectRow(atom.clone())]), atom);
        }
    }
    let mut assignments: BTreeMap<_, _> = variables.iter().map(|index| (*index, crate::EffectRow::empty())).collect();
    for atom in atoms.values() {
        let contains = |row: &crate::EffectRow| atom.effects.iter().all(|effect| row.effects.contains(effect))
            && atom.projections.iter().all(|projection| row.projections.contains(projection));
        let mut absent = BTreeSet::new();
        loop {
            let previous = absent.len();
            for (left, right) in &equations {
                for (source, target) in [(left, right), (right, left)] {
                    if !contains(source) && source.tails.iter().all(|tail| match tail {
                        crate::EffectTail::Generic(index) => absent.contains(index), _ => false,
                    }) {
                        if contains(target) { return false; }
                        for tail in &target.tails {
                            let crate::EffectTail::Generic(index) = tail else { return false; };
                            absent.insert(*index);
                        }
                    }
                }
            }
            if previous == absent.len() { break; }
        }
        for index in variables.difference(&absent) {
            assignments.get_mut(index).unwrap().extend(atom.clone());
        }
    }
    bindings.effect_rows.extend(assignments);
    true
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
        (GenericArgument::ConstInteger(left), GenericArgument::ConstInteger(right)) if left == right => {
            Some(GenericArgument::ConstInteger(*left))
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
    if !left.tails.is_empty() || !right.tails.is_empty() {
        if left.tails.iter().chain(&right.tails).any(|tail| matches!(tail, crate::EffectTail::Infer(_))) {
            return None;
        }
        // Fixed instances may determine ordinary generic arguments before
        // their memberships become atoms (Trace<T> versus Trace<i64>).
        for expected in &left.effects {
            for found in &right.effects {
                if expected.definition != found.definition || expected.arguments.len() != found.arguments.len() { continue; }
                let mut trial = bindings.clone();
                if expected.arguments.iter().zip(&found.arguments)
                    .map(|(left, right)| unify_overlap_argument(left, right, &mut trial))
                    .collect::<Option<Vec<_>>>().is_some() {
                    *bindings = trial;
                    break;
                }
            }
        }
        bindings.effect_equations.push((left.clone(), right.clone()));
        return Some(left.clone());
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
    let result = crate::EffectRow {
        effects,
        projections,
        tails: BTreeSet::new(),
    }
    .canonicalized();
    *bindings = row_bindings;
    Some(result)
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
        (Type::FixedArray { element: left, length: ln }, Type::FixedArray { element: right, length: rn }) => Some(Type::FixedArray {
            element: Box::new(unify_overlap_type(left, right, bindings)?),
            length: Box::new(unify_overlap_argument(ln, rn, bindings)?),
        }),
        (Type::Array(left), Type::Array(right)) => {
            unify_overlap_type(left, right, bindings).map(|value| Type::Array(Box::new(value)))
        }
        (
            Type::RawPointer { mutability: left_mutability, pointee: left },
            Type::RawPointer { mutability: right_mutability, pointee: right },
        ) if left_mutability == right_mutability => {
            unify_overlap_type(left, right, bindings).map(|pointee| Type::RawPointer {
                mutability: *left_mutability,
                pointee: Box::new(pointee),
            })
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
            Type::Callable { contract: left_contract,
                safety: left_safety,
                lifetime_binders: left_binders,
                parameters: left_parameters,
                result: left_result,
                effects: left_effects,
                invocation: left_invocation,
            },
            Type::Callable { contract: right_contract,
                safety: right_safety,
                lifetime_binders: right_binders,
                parameters: right_parameters,
                result: right_result,
                effects: right_effects,
                invocation: right_invocation,
            },
        ) if left_safety == right_safety && left_binders == right_binders
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
            // Refinements cannot make otherwise identical executable shapes
            // disjoint. Preserve either nonempty side for downstream checks.
            Some(Type::Callable { contract: if left_contract.is_empty() { right_contract.clone() } else { left_contract.clone() },
                safety: *left_safety,
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
        Type::FixedArray { element, length } => contains_overlap_generic(&element, index, bindings)
            || contains_overlap_argument_generic(&length, index, bindings),
        Type::Generic(found) => found == index,
        Type::Nominal { arguments, .. } => arguments
            .iter()
            .any(|argument| contains_overlap_argument_generic(argument, index, bindings)),
        Type::Tuple(arguments) => arguments
            .iter()
            .any(|argument| contains_overlap_generic(argument, index, bindings)),
        Type::Array(value) | Type::StaticData { element: value, .. } => {
            contains_overlap_generic(&value, index, bindings)
        }
        Type::Reference { referent, .. }
        | Type::RawPointer { pointee: referent, .. } => contains_overlap_generic(&referent, index, bindings),
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
        | Type::ConstInteger(_)
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
        | GenericArgument::ConstInteger(_)
        | GenericArgument::ConstIntegerExpr(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstInfer { .. } => false,
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
        GenericArgument::EffectRow(value) => GenericArgument::EffectRow(resolve_overlap_effect_row(value, bindings)),
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
        Type::FixedArray { element, length } => Type::FixedArray {
            element: Box::new(resolve_overlap_type(element, bindings)),
            length: Box::new(resolve_overlap_argument(length, bindings)),
        },
        Type::RawPointer { mutability, pointee } => Type::RawPointer {
            mutability: *mutability,
            pointee: Box::new(resolve_overlap_type(pointee, bindings)),
        },
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
        Type::Callable { contract,
            safety,
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable { contract: Box::new(contract.map_terms(|value, _| resolve_overlap_argument(&value, bindings))),
            safety: *safety,
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
    let mut row = crate::EffectRow {
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
        tails: value.tails.clone(),
    };
    row.substitute_tails(|tail| match tail {
        crate::EffectTail::Generic(index) => bindings.effect_rows.get(&index).cloned(), _ => None,
    });
    row
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
    map_implementation_associated_constraints(&mut implementation, |argument| rebase_overlap_argument(&argument, offset));
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
        Type::FixedArray { element, length } => Type::FixedArray {
            element: Box::new(rebase_overlap_type(element, offset)), length: Box::new(rebase_overlap_argument(length, offset)),
        },
        Type::RawPointer { mutability, pointee } => Type::RawPointer {
            mutability: *mutability,
            pointee: Box::new(rebase_overlap_type(pointee, offset)),
        },
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
        Type::Callable { contract,
            safety,
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable { contract: Box::new(contract.map_terms(|value, _| rebase_overlap_argument(&value, offset))),
            safety: *safety,
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
        tails: value.tails.iter().copied().map(|tail| match tail {
            crate::EffectTail::Generic(index) => {
                crate::EffectTail::Generic(index.saturating_add(offset))
            }
            crate::EffectTail::Infer(index) => crate::EffectTail::Infer(index),
        }).collect(),
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
        Type::Callable { contract: Default::default(),
            safety: crate::Safety::Safe,
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
                tails: [EffectTail::Generic(tail)].into_iter().collect(),
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
            tails: Default::default(),
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
            tails: Default::default(),
        };
        assert!(super::unify_overlap_effect_row(&left, &right, &mut bindings).is_none());
        assert!(
            bindings.types.is_empty(),
            "failed candidate leaked a type binding"
        );
    }
}
