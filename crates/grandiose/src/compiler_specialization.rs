//! Deterministic, allocation-independent specialization request discovery.
//!
//! This phase is intentionally rejection-only: it records requirements that a
//! future generic lowering could satisfy, but never authorizes bytecode emission.

#[cfg(test)]
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::ops::ControlFlow;
use std::rc::Rc;

use crate::ast::{
    AssignmentPlaceKind, AssociatedArgumentSyntax, BinaryOp, Expr, ExprKind, ExprVisitor,
    GenericParamKind, GoalArgument, GoalPolarity, PatternKind, Program, Stmt, TypeSyntax,
    TypeSyntaxKind, UnaryOp, pattern_field_index, visit_expr_preorder, walk_expr,
};
use crate::compiler::decode_nominal_instance;
use crate::compiler_traits::{
    AssociatedValue, ConstValue, GenericArg, GenericParameterKind, IntrinsicRole, LifetimeArg,
    ParamEnv, SolveResult, SolverBudget, TraitDb, TraitFact, TraitKey,
};
use crate::compiler_typeck::{
    CallableShape, DeclarationKey, GenericParamKey, NominalInstanceKey, NominalKey,
    ProvisionalConst, ProvisionalType, ProvisionalTypeFolder, fold_provisional_type_children,
    label_payload_type, label_provisional_type, predefined_runtime_use_interval,
    provisional_signature_children_any, provisional_signature_type_any, provisional_type_any,
};

const ASSOCIATED_PROJECTION_PREFIX: &str = "$associated_projection$";

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct ClosureSiteKey {
    pub(crate) owner: DeclarationKey,
    pub(crate) ordinal: u32,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SpecializationKey {
    pub(crate) template: DeclarationKey,
    pub(crate) arguments: Vec<SpecializationArgument>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum SpecializationArgument {
    Type(ProvisionalType),
    EffectRow(Vec<crate::compiler_typeck::CallableEffect>),
    Closure(
        ClosureSiteKey,
        Box<CallableShape>,
        Vec<ClosureCapture>,
        ParamEnv,
        BTreeMap<String, ProvisionalType>,
        BTreeMap<String, Vec<ClosureRequest>>,
    ),
}

pub(crate) fn contains_late_callable(ty: &ProvisionalType) -> bool {
    provisional_type_any(ty, &mut |ty| {
        matches!(ty, ProvisionalType::Callable(_)) || label_payload_type(ty).is_some()
    })
}

fn late_specialization(key: &SpecializationKey) -> bool {
    key.arguments.iter().any(|argument| {
        matches!(argument, SpecializationArgument::Type(ty) if contains_late_callable(ty))
            || matches!(argument, SpecializationArgument::Closure(_, _, _, _, active_labels, _)
                if !active_labels.is_empty())
    })
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct ClosureCapture {
    pub(crate) name: String,
    pub(crate) ty: ProvisionalType,
    /// The strongest access the closure body requires from the captured place.
    /// This is semantic environment evidence, not a physical ABI choice: the
    /// backend may scalarize a nonescaping environment, but it must preserve
    /// this access and its ordinary place-flow consequences.
    pub(crate) mode: CaptureMode,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum CaptureMode {
    Observe,
    Mutate,
    Move,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum ClosureTupleField {
    Type(ProvisionalType),
    Closure(ClosureRequest),
    ClosureSet(Vec<ClosureRequest>),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct ClosureNominalInstance {
    pub(crate) declaration: String,
    pub(crate) arguments: Vec<ClosureTupleField>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct ClosureRequest {
    pub(crate) site: ClosureSiteKey,
    pub(crate) shape: Box<CallableShape>,
    pub(crate) captures: Vec<ClosureCapture>,
    pub(crate) param_env: ParamEnv,
    pub(crate) active_labels: BTreeMap<String, ProvisionalType>,
    /// Exact callable identities captured only for static beta reduction.
    /// These are proof values, not fields in the runtime closure environment.
    pub(crate) static_captures: BTreeMap<String, Vec<ClosureRequest>>,
}

/// Stable source identity for a recursive closure binding. Recursive calls
/// reuse the current callable receiver; this marker never denotes an
/// environment capture or a cyclic `MakeCallable` value.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct RecursiveSelf {
    pub(crate) binding: String,
    pub(crate) site: ClosureSiteKey,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct RecursiveSelfCall {
    pub(crate) recursive_self: RecursiveSelf,
    pub(crate) shape: Box<CallableShape>,
    pub(crate) requested_receiver_mode: Option<u32>,
}

/// A closure whose environment contains a callable identity that only becomes
/// concrete while lowering the enclosing handler.  Discovery still retains
/// the complete closure plan so Core does not have to rediscover capture modes
/// or the contextual signature from syntax.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct LateClosurePlan {
    pub(crate) request: ClosureRequest,
    pub(crate) body_kind: ClosureBodyKind,
    pub(crate) recursive_self: Option<RecursiveSelf>,
}

impl ClosureRequest {
    pub(crate) fn receiver_mode(&self) -> u32 {
        // A ClosureRequest is exact compiler-sealed producer evidence. Its
        // capture access therefore determines the receiver contract even when
        // the sealed environment stores references: mode 0 observes through a
        // shared reborrow, mode 1 creates one per-call unique reborrow, and
        // mode 2 consumes the environment. Open callable shapes never acquire
        // a ClosureRequest and retain their conservative owned-call fallback.
        match self
            .captures
            .iter()
            .map(|capture| capture.mode)
            .max()
            .unwrap_or(CaptureMode::Observe)
        {
            CaptureMode::Observe => 0,
            CaptureMode::Mutate => 1,
            CaptureMode::Move => 2,
        }
    }
}

fn contains_late_callable_captures(request: &ClosureRequest) -> bool {
    request
        .captures
        .iter()
        .any(|capture| contains_late_callable(&capture.ty))
        || request.shape.params.iter().any(contains_late_callable)
        || contains_late_callable(&request.shape.result)
}

fn compatible_sealed_producer_contracts(
    left_shape: &CallableShape,
    left_captures: &[ClosureCapture],
    left_environment: &ParamEnv,
    left_labels: &BTreeMap<String, ProvisionalType>,
    left_static: &BTreeMap<String, Vec<ClosureRequest>>,
    right_shape: &CallableShape,
    right_captures: &[ClosureCapture],
    right_environment: &ParamEnv,
    right_labels: &BTreeMap<String, ProvisionalType>,
    right_static: &BTreeMap<String, Vec<ClosureRequest>>,
) -> bool {
    left_shape == right_shape
        && left_environment == right_environment
        && left_labels == right_labels
        && left_static == right_static
        && left_captures.len() == right_captures.len()
        && left_captures
            .iter()
            .zip(right_captures)
            .all(|(left, right)| left.ty == right.ty && left.mode == right.mode)
}

impl ClosureCapture {
    pub(crate) fn lifted_name(site: &ClosureSiteKey, ordinal: usize) -> String {
        let (kind, owner) = match &site.owner {
            DeclarationKey::Function(name) => ('f', name),
            DeclarationKey::Global(name) => ('g', name),
        };
        let mut encoded = format!("$capture${kind}");
        for byte in owner.bytes() {
            write!(encoded, "{byte:02x}").unwrap();
        }
        format!("{encoded}${}${ordinal}", site.ordinal)
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum BodyInstanceKey {
    Root(DeclarationKey),
    Drop(String),
    Specialization(SpecializationKey),
    Closure(ClosureRequest),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct CallSiteKey {
    pub(crate) body: BodyInstanceKey,
    pub(crate) expression_ordinal: u32,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum ClosureBodyKind {
    Explicit,
    ContextualBlock,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum EmissionKey {
    Source {
        wire_name: String,
        declaration: DeclarationKey,
    },
    Specialization(SpecializationKey),
    Closure(ClosureRequest),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct EmissionPlan {
    pub(crate) ordered: Vec<EmissionKey>,
    pub(crate) ids: BTreeMap<EmissionKey, u32>,
}

fn hidden_global_wire_name(name: &str) -> String {
    let mut encoded = String::from("$global$");
    for byte in name.bytes() {
        write!(&mut encoded, "{byte:02x}").expect("writing to a String cannot fail");
    }
    encoded
}

pub(crate) fn emission_plan(
    program: &Program,
    discovery: &Discovery,
    retained_sources: Option<&BTreeSet<DeclarationKey>>,
) -> EmissionPlan {
    let retained_requests = retained_sources.map(|sources| {
        let mut retained = discovery
            .graph
            .roots
            .iter()
            .filter(|(owner, _)| {
                sources.contains(owner)
                    || matches!(owner, DeclarationKey::Function(name) if name.starts_with("$drop$"))
            })
            .map(|(_, key)| key.clone())
            .collect::<BTreeSet<_>>();
        loop {
            let before = retained.len();
            for (parent, child) in &discovery.graph.edges {
                if retained.contains(parent) {
                    retained.insert(child.clone());
                }
            }
            if retained.len() == before {
                break;
            }
        }
        retained
    });
    let mut ordered = program
        .functions
        .iter()
        .filter(|function| {
            function.generics.is_none()
                && retained_sources.is_none_or(|sources| {
                    sources.contains(&DeclarationKey::Function(function.name.clone()))
                })
        })
        .map(|function| EmissionKey::Source {
            wire_name: function.name.clone(),
            declaration: DeclarationKey::Function(function.name.clone()),
        })
        .chain(program.globals.iter().map(|global| EmissionKey::Source {
            wire_name: hidden_global_wire_name(&global.name),
            declaration: DeclarationKey::Global(global.name.clone()),
        }))
        .collect::<Vec<_>>();
    ordered.sort();
    ordered.extend(
        discovery
            .graph
            .requests
            .keys()
            .filter(|key| !late_specialization(key))
            .filter(|key| {
                retained_requests
                    .as_ref()
                    .is_none_or(|retained| retained.contains(*key))
            })
            .cloned()
            .map(EmissionKey::Specialization),
    );
    let closures = discovery
        .graph
        .closure_bodies
        .keys()
        // A closure that references a generative destination is proof-only
        // control syntax. It must be beta-reduced into that destination's
        // frame and therefore has no independently emittable runtime body.
        .filter(|request| request.active_labels.is_empty() && request.static_captures.is_empty())
        .filter(|request| {
            retained_sources.is_none_or(|sources| sources.contains(&request.site.owner))
                || matches!(
                    &request.site.owner,
                    DeclarationKey::Function(name) if name.starts_with("$drop$")
                )
                || retained_requests.as_ref().is_some_and(|retained| {
                    retained
                        .iter()
                        .any(|key| key.template == request.site.owner)
                })
        })
        .cloned()
        .map(EmissionKey::Closure)
        .collect::<BTreeSet<_>>();
    ordered.extend(closures);
    let ids = ordered
        .iter()
        .cloned()
        .enumerate()
        .map(|(id, key)| (key, id as u32))
        .collect();
    EmissionPlan { ordered, ids }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SpecializationRequest {
    pub(crate) key: SpecializationKey,
    pub(crate) closures: BTreeSet<ClosureRequest>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct FunctionTemplate {
    pub(crate) declaration: DeclarationKey,
    pub(crate) generic_params: Vec<GenericParamKey>,
    pub(crate) params: Vec<ProvisionalType>,
    pub(crate) parameter_binders: Vec<Option<GenericParamKey>>,
    pub(crate) result_binder: Option<GenericParamKey>,
    pub(crate) result_nominal_binders: Option<(String, Vec<Option<GenericParamKey>>)>,
    pub(crate) result: ProvisionalType,
    pub(crate) callable_constraints: BTreeMap<GenericParamKey, CallableShape>,
    pub(crate) effectful_callable_binders: BTreeSet<GenericParamKey>,
    pub(crate) marker_constraints: Vec<MarkerConstraint>,
    pub(crate) transparent_identity: bool,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MarkerConstraint {
    pub(crate) polarity: GoalPolarity,
    pub(crate) trait_key: TraitKey,
    pub(crate) subject: ProvisionalType,
    /// The source-level subject before an `Fn` bound projects a callable
    /// parameter to its shape. Keeping this identity is required to carry
    /// lexical marker evidence and exact closure capabilities through nested
    /// generic calls; a `CallableShape` alone has neither.
    pub(crate) subject_binder: Option<GenericParamKey>,
    pub(crate) arguments: Vec<GenericArg>,
    pub(crate) bindings: Vec<AssociatedValue>,
}

fn template_param_env(
    trait_db: &TraitDb,
    template: &FunctionTemplate,
    substitutions: Option<&BTreeMap<GenericParamKey, SpecializationArgument>>,
) -> Result<ParamEnv, ()> {
    let facts = template
        .marker_constraints
        .iter()
        .map(|constraint| {
            let resolve = |ty: &ProvisionalType| match substitutions {
                Some(substitutions) => substitute(ty, substitutions),
                None => Some(ty.clone()),
            };
            let resolve_argument = |argument: &GenericArg| match substitutions {
                Some(substitutions) => substitute_generic_arg(argument, substitutions),
                None => Some(argument.clone()),
            };
            Ok(TraitFact {
                polarity: constraint.polarity,
                trait_key: constraint.trait_key.clone(),
                subject: resolve(
                    &constraint
                        .subject_binder
                        .clone()
                        .map(ProvisionalType::Param)
                        .unwrap_or_else(|| constraint.subject.clone()),
                )
                .ok_or(())?,
                arguments: constraint
                    .arguments
                    .iter()
                    .map(resolve_argument)
                    .collect::<Option<Vec<_>>>()
                    .ok_or(())?,
                bindings: constraint
                    .bindings
                    .iter()
                    .map(|binding| {
                        Some(AssociatedValue {
                            item: binding.item.clone(),
                            arguments: binding
                                .arguments
                                .iter()
                                .map(resolve_argument)
                                .collect::<Option<Vec<_>>>()?,
                            value: resolve(&binding.value)?,
                        })
                    })
                    .collect::<Option<Vec<_>>>()
                    .ok_or(())?,
            })
        })
        .collect::<Result<Vec<_>, ()>>()?;
    Ok(trait_db.param_env(facts))
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct RequestGraph {
    pub(crate) templates: BTreeMap<DeclarationKey, FunctionTemplate>,
    pub(crate) requests: BTreeMap<SpecializationKey, SpecializationRequest>,
    pub(crate) roots: BTreeSet<(DeclarationKey, SpecializationKey)>,
    pub(crate) edges: BTreeSet<(SpecializationKey, SpecializationKey)>,
    pub(crate) direct_calls: BTreeMap<CallSiteKey, SpecializationKey>,
    /// Ordinary library `else(if(...))` whose complementary Result/Option
    /// constructors were structurally specialized as one CFG expression.
    pub(crate) structural_elses: BTreeSet<CallSiteKey>,
    pub(crate) callable_calls: BTreeMap<CallSiteKey, ClosureRequest>,
    /// First-class closure construction sites retained as runtime values.
    pub(crate) closure_values: BTreeMap<CallSiteKey, ClosureRequest>,
    /// Exact source closure bodies available for static beta reduction. This
    /// is separate from `closure_values`: a callback can require complete
    /// nested-call planning without ever becoming a runtime callable.
    pub(crate) static_closure_bodies: BTreeMap<CallSiteKey, LateClosurePlan>,
    /// Calls through a retained closure local rather than a scalarized wrapper.
    pub(crate) indirect_calls: BTreeMap<CallSiteKey, ClosureRequest>,
    /// Canonical finite producer sets selected by ordinary source control.
    pub(crate) indirect_call_sets: BTreeMap<CallSiteKey, Vec<ClosureRequest>>,
    /// Explicit receiver mode requested at an indirect call site (`move f()` is owned).
    pub(crate) indirect_call_modes: BTreeMap<CallSiteKey, u32>,
    /// Exact closure identity returned by a specialized callable-valued call.
    pub(crate) returned_closures: BTreeMap<CallSiteKey, ClosureRequest>,
    pub(crate) returned_closure_sets: BTreeMap<CallSiteKey, Vec<ClosureRequest>>,
    pub(crate) opaque_closure_sets: BTreeMap<CallSiteKey, String>,
    /// Exact generic nominal identity returned by a specialized call.
    pub(crate) returned_closure_nominals: BTreeMap<CallSiteKey, ClosureNominalInstance>,
    pub(crate) closure_tuples: BTreeSet<Vec<ClosureTupleField>>,
    pub(crate) closure_nominal_constructions: BTreeMap<CallSiteKey, ClosureNominalInstance>,
    /// Generic nominal construction whose exact argument is a handler-site
    /// resumption and therefore cannot receive a runtime identity until Core.
    pub(crate) late_nominal_constructions: BTreeMap<CallSiteKey, NominalInstanceKey>,
    /// First-class or contextual closures containing handler-site callable
    /// identities. These cannot enter ordinary emitted specialization keys,
    /// but their signature, captures, and receiver evidence are fully known.
    pub(crate) late_closures: BTreeMap<CallSiteKey, LateClosurePlan>,
    /// Recursive binding associated with an otherwise ordinary emitted
    /// closure. Kept outside `ClosureRequest` so existing compiler construction
    /// sites remain source-compatible until Core consumes the contract.
    pub(crate) recursive_closures: BTreeMap<ClosureRequest, RecursiveSelf>,
    /// Calls which target the current callable receiver rather than a captured
    /// callable value. Core chooses CallSelf versus TailCallSelf from position.
    pub(crate) recursive_self_calls: BTreeMap<CallSiteKey, RecursiveSelfCall>,
    pub(crate) erased_callable_aliases: BTreeSet<CallSiteKey>,
    /// Contextually inferred result of a generative label destination. The
    /// body instance is part of the site because one source label inside a
    /// generic closure may acquire a different ground payload per
    /// specialization.
    pub(crate) label_results: BTreeMap<CallSiteKey, ProvisionalType>,
    pub(crate) constructions: BTreeMap<CallSiteKey, NominalInstanceKey>,
    pub(crate) constructed_nominals: BTreeSet<NominalInstanceKey>,
    pub(crate) closure_bodies: BTreeMap<ClosureRequest, ClosureBodyKind>,
    pub(crate) validated_symbolic: BTreeSet<DeclarationKey>,
}

impl RequestGraph {
    pub(crate) fn canonical_text(&self) -> String {
        let mut output = String::new();
        for (key, template) in &self.templates {
            writeln!(
                output,
                "template {key:?} generics={:?} params={:?} binders={:?} result={:?} callable={:?}",
                template.generic_params,
                template.params,
                template.parameter_binders,
                template.result,
                template.callable_constraints
            )
            .unwrap();
        }
        for (key, request) in &self.requests {
            writeln!(output, "request {key:?} closures={:?}", request.closures).unwrap();
        }
        for edge in &self.edges {
            writeln!(output, "edge {edge:?}").unwrap();
        }
        for root in &self.roots {
            writeln!(output, "root {root:?}").unwrap();
        }
        for call in &self.direct_calls {
            writeln!(output, "direct-call {call:?}").unwrap();
        }
        for call in &self.structural_elses {
            writeln!(output, "structural-else {call:?}").unwrap();
        }
        for call in &self.callable_calls {
            writeln!(output, "callable-call {call:?}").unwrap();
        }
        for value in &self.closure_values {
            writeln!(output, "closure-value {value:?}").unwrap();
        }
        for body in &self.static_closure_bodies {
            writeln!(output, "static-closure-body {body:?}").unwrap();
        }
        for call in &self.indirect_calls {
            writeln!(output, "indirect-call {call:?}").unwrap();
        }
        for call in &self.indirect_call_sets {
            writeln!(output, "indirect-call-set {call:?}").unwrap();
        }
        for mode in &self.indirect_call_modes {
            writeln!(output, "indirect-call-mode {mode:?}").unwrap();
        }
        for returned in &self.returned_closures {
            writeln!(output, "returned-closure {returned:?}").unwrap();
        }
        for returned in &self.returned_closure_sets {
            writeln!(output, "returned-closure-set {returned:?}").unwrap();
        }
        for opaque in &self.opaque_closure_sets {
            writeln!(output, "opaque-closure-set {opaque:?}").unwrap();
        }
        for returned in &self.returned_closure_nominals {
            writeln!(output, "returned-closure-nominal {returned:?}").unwrap();
        }
        for tuple in &self.closure_tuples {
            writeln!(output, "closure-tuple {tuple:?}").unwrap();
        }
        for nominal in &self.closure_nominal_constructions {
            writeln!(output, "closure-nominal {nominal:?}").unwrap();
        }
        for nominal in &self.late_nominal_constructions {
            writeln!(output, "late-nominal {nominal:?}").unwrap();
        }
        for closure in &self.late_closures {
            writeln!(output, "late-closure {closure:?}").unwrap();
        }
        for closure in &self.recursive_closures {
            writeln!(output, "recursive-closure {closure:?}").unwrap();
        }
        for call in &self.recursive_self_calls {
            writeln!(output, "recursive-self-call {call:?}").unwrap();
        }
        for alias in &self.erased_callable_aliases {
            writeln!(output, "erased-callable-alias {alias:?}").unwrap();
        }
        for result in &self.label_results {
            writeln!(output, "label-result {result:?}").unwrap();
        }
        for construction in &self.constructions {
            writeln!(output, "construction {construction:?}").unwrap();
        }
        for body in &self.closure_bodies {
            writeln!(output, "closure-body {body:?}").unwrap();
        }
        for declaration in &self.validated_symbolic {
            writeln!(output, "validated-symbolic {declaration:?}").unwrap();
        }
        output
    }

    pub(crate) fn fingerprint(&self) -> u64 {
        let mut hash = 0xcbf29ce484222325_u64;
        for byte in self.canonical_text().bytes() {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
        hash
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct DiscoveryError {
    pub(crate) owner: DeclarationKey,
    pub(crate) message: String,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Discovery {
    pub(crate) graph: RequestGraph,
    pub(crate) errors: BTreeSet<DiscoveryError>,
}

/// Homeomorphic embedding over ground specialization types. If an ancestor
/// embeds a distinct recursive descendant, the descendant has repeated the
/// ancestor's constructor skeleton while retaining or adding structure; over
/// this finite signature that is the standard whistle for non-well-founded
/// specialization growth.
fn specialization_type_embeds(ancestor: &ProvisionalType, descendant: &ProvisionalType) -> bool {
    if ancestor == descendant {
        return true;
    }
    let coupled = match (ancestor, descendant) {
        (ProvisionalType::Const(_), ProvisionalType::Const(_)) => true,
        (ProvisionalType::Nominal(left), ProvisionalType::Nominal(right)) => {
            left.declaration == right.declaration
                && left.arguments.len() == right.arguments.len()
                && left
                    .arguments
                    .iter()
                    .zip(&right.arguments)
                    .all(|(left, right)| specialization_type_embeds(left, right))
        }
        (ProvisionalType::Tuple(left), ProvisionalType::Tuple(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| specialization_type_embeds(left, right))
        }
        (ProvisionalType::Shared(left), ProvisionalType::Shared(right))
        | (ProvisionalType::Unique(left), ProvisionalType::Unique(right)) => {
            specialization_type_embeds(left, right)
        }
        (ProvisionalType::Callable(left), ProvisionalType::Callable(right)) => {
            left.effects == right.effects
                && left.effect_tail == right.effect_tail
                && left.params.len() == right.params.len()
                && left
                    .params
                    .iter()
                    .zip(&right.params)
                    .all(|(left, right)| specialization_type_embeds(left, right))
                && specialization_type_embeds(&left.result, &right.result)
        }
        _ => false,
    };
    if coupled {
        return true;
    }
    provisional_signature_children_any(descendant, &mut |child| {
        specialization_type_embeds(ancestor, child)
    })
}

fn specialization_argument_embeds(
    ancestor: &SpecializationArgument,
    descendant: &SpecializationArgument,
) -> bool {
    match (ancestor, descendant) {
        (SpecializationArgument::Type(left), SpecializationArgument::Type(right)) => {
            specialization_type_embeds(left, right)
        }
        (
            SpecializationArgument::Closure(
                _,
                left,
                left_captures,
                left_environment,
                left_labels,
                left_static,
            ),
            SpecializationArgument::Closure(
                _,
                right,
                right_captures,
                right_environment,
                right_labels,
                right_static,
            ),
        ) => {
            left_environment == right_environment
                && left_labels == right_labels
                && left_static == right_static
                && left_captures.len() == right_captures.len()
                && left_captures
                    .iter()
                    .zip(right_captures)
                    .all(|(left, right)| {
                        left.mode == right.mode && specialization_type_embeds(&left.ty, &right.ty)
                    })
                && specialization_type_embeds(
                    &ProvisionalType::Callable(left.clone()),
                    &ProvisionalType::Callable(right.clone()),
                )
        }
        (SpecializationArgument::EffectRow(left), SpecializationArgument::EffectRow(right)) => {
            left.len() == right.len()
                && left.iter().zip(right).all(|(left, right)| {
                    left.declaration == right.declaration
                        && left.arguments.len() == right.arguments.len()
                        && left
                            .arguments
                            .iter()
                            .zip(&right.arguments)
                            .all(|(left, right)| specialization_type_embeds(left, right))
                })
        }
        _ => false,
    }
}

fn symbolic_type(
    syntax: &TypeSyntax,
    generics: &BTreeMap<String, GenericParamKey>,
    callable_constraints: &BTreeMap<GenericParamKey, CallableShape>,
) -> Option<ProvisionalType> {
    match &syntax.kind {
        TypeSyntaxKind::Never => Some(ProvisionalType::Predefined("Never".into())),
        TypeSyntaxKind::Path(path) if path.len() == 1 => {
            let name = &path[0].name;
            if let Some(key) = generics.get(name) {
                Some(
                    callable_constraints
                        .get(key)
                        .cloned()
                        .map(|shape| ProvisionalType::Callable(Box::new(shape)))
                        .unwrap_or_else(|| ProvisionalType::Param(key.clone())),
                )
            } else if let Some(value) = ProvisionalConst::decode_encoded_name(name) {
                Some(ProvisionalType::Const(value))
            } else if matches!(
                name.as_str(),
                "Unit"
                    | "Text"
                    | "Bytes"
                    | "Char"
                    | "f32"
                    | "f64"
                    | "i8"
                    | "i16"
                    | "i32"
                    | "i64"
                    | "i128"
                    | "isize"
                    | "u8"
                    | "u16"
                    | "u32"
                    | "u64"
                    | "u128"
                    | "usize"
            ) {
                Some(ProvisionalType::Predefined(name.clone()))
            } else {
                Some(ProvisionalType::Nominal(NominalInstanceKey::monomorphic(
                    name.clone(),
                )))
            }
        }
        TypeSyntaxKind::Application {
            constructor,
            arguments,
            ..
        } => {
            let name = constructor.simple_name()?;
            if generics.contains_key(name) {
                return None;
            }
            Some(ProvisionalType::Nominal(NominalInstanceKey {
                declaration: NominalKey(name.to_owned()),
                arguments: arguments
                    .iter()
                    .map(|argument| symbolic_type(argument, generics, callable_constraints))
                    .collect::<Option<Vec<_>>>()?,
            }))
        }
        TypeSyntaxKind::Tuple(elements) if elements.is_empty() => {
            Some(ProvisionalType::Predefined("Unit".into()))
        }
        TypeSyntaxKind::Tuple(elements) => Some(ProvisionalType::Tuple(
            elements
                .iter()
                .map(|element| symbolic_type(element, generics, callable_constraints))
                .collect::<Option<Vec<_>>>()?,
        )),
        TypeSyntaxKind::SharedReference { referent, .. } => {
            symbolic_type(referent, generics, callable_constraints).map(ProvisionalType::shared)
        }
        TypeSyntaxKind::UniqueReference { referent, .. } => {
            symbolic_type(referent, generics, callable_constraints).map(ProvisionalType::unique)
        }
        TypeSyntaxKind::Projection {
            subject,
            trait_ref,
            item,
            arguments,
            const_arguments,
        } if trait_ref.path.len() == 1 && const_arguments.is_empty() => {
            let mut projected_arguments =
                vec![symbolic_type(subject, generics, callable_constraints)?];
            projected_arguments.extend(
                arguments
                    .iter()
                    .map(|argument| match argument {
                        AssociatedArgumentSyntax::Type(ty) => {
                            symbolic_type(ty, generics, callable_constraints)
                        }
                        AssociatedArgumentSyntax::Lifetime { .. } => None,
                    })
                    .collect::<Option<Vec<_>>>()?,
            );
            Some(ProvisionalType::Nominal(NominalInstanceKey {
                declaration: NominalKey(format!(
                    "{ASSOCIATED_PROJECTION_PREFIX}{}${}",
                    trait_ref.path[0].name, item.name
                )),
                arguments: projected_arguments,
            }))
        }
        _ => None,
    }
}

fn const_expression_identity(
    expression: &crate::ast::ConstExprSyntax,
    generics: &BTreeMap<String, GenericParamKey>,
) -> Option<ProvisionalType> {
    use crate::ast::{ConstBinaryOp, ConstExprSyntaxKind, EvaluatedConst};
    if let Ok(value) = crate::ast::evaluate_const_expression(expression, |_| None) {
        return Some(ProvisionalType::Const(match value {
            EvaluatedConst::U32(value) => ProvisionalConst::U32(value),
            EvaluatedConst::Quantity { lower, upper } => {
                ProvisionalConst::Quantity { lower, upper }
            }
        }));
    }
    match &expression.kind {
        ConstExprSyntaxKind::Path(path) if path.len() == 1 => generics
            .get(&path[0].name)
            .cloned()
            .map(ProvisionalType::Param),
        ConstExprSyntaxKind::Binary { op, lhs, rhs } => {
            Some(ProvisionalType::Nominal(NominalInstanceKey {
                declaration: NominalKey(format!(
                    "$const$expr${}",
                    match op {
                        ConstBinaryOp::Add => "add",
                        ConstBinaryOp::Subtract => "sub",
                        ConstBinaryOp::Multiply => "mul",
                        ConstBinaryOp::Divide => "div",
                        ConstBinaryOp::Remainder => "rem",
                    }
                )),
                arguments: vec![
                    const_expression_identity(lhs, generics)?,
                    const_expression_identity(rhs, generics)?,
                ],
            }))
        }
        ConstExprSyntaxKind::Neg(value) => Some(ProvisionalType::Nominal(NominalInstanceKey {
            declaration: NominalKey("$const$expr$neg".to_owned()),
            arguments: vec![const_expression_identity(value, generics)?],
        })),
        ConstExprSyntaxKind::U32(_) | ConstExprSyntaxKind::Quantity(_) => None,
        ConstExprSyntaxKind::Path(_) => None,
    }
}

fn const_identity(
    value: &crate::ast::ConstArgumentValueSyntax,
    generics: &BTreeMap<String, GenericParamKey>,
) -> Option<ProvisionalType> {
    let value = match value {
        crate::ast::ConstArgumentValueSyntax::U32 { value, .. } => {
            ProvisionalConst::U32(u32::try_from(*value).ok()?)
        }
        crate::ast::ConstArgumentValueSyntax::Quantity(quantity) => {
            let lower = u32::try_from(quantity.lower).ok()?;
            let upper = quantity.upper.map(u32::try_from).transpose().ok()?;
            ProvisionalConst::Quantity { lower, upper }
        }
        crate::ast::ConstArgumentValueSyntax::Expression(expression) => {
            return const_expression_identity(expression, generics);
        }
    };
    Some(ProvisionalType::Const(value))
}

/// Enrich the compatibility type/lifetime application tree with structural const
/// identities retained in `Program`'s span-keyed side table.
fn symbolic_type_in(
    program: &Program,
    syntax: &TypeSyntax,
    generics: &BTreeMap<String, GenericParamKey>,
    callable_constraints: &BTreeMap<GenericParamKey, CallableShape>,
) -> Option<ProvisionalType> {
    let mut ty = symbolic_type(syntax, generics, callable_constraints)?;
    match (&syntax.kind, &mut ty) {
        (
            TypeSyntaxKind::Application {
                arguments,
                lifetime_arguments,
                ..
            },
            ProvisionalType::Nominal(instance),
        ) => {
            let const_arguments = program.type_const_arguments(syntax.span);
            if const_arguments.is_empty() {
                for (source, argument) in arguments.iter().zip(&mut instance.arguments) {
                    *argument = symbolic_type_in(program, source, generics, callable_constraints)?;
                }
                return Some(ty);
            }
            let const_by_position = const_arguments
                .iter()
                .map(|argument| (argument.position, &argument.value))
                .collect::<BTreeMap<_, _>>();
            let lifetime_positions = lifetime_arguments
                .iter()
                .map(|argument| argument.position)
                .collect::<BTreeSet<_>>();
            let total = arguments.len() + const_arguments.len() + lifetime_arguments.len();
            let mut source_types = arguments.iter();
            let mut merged = Vec::with_capacity(arguments.len() + const_arguments.len());
            for position in 0..total {
                if lifetime_positions.contains(&position) {
                    continue;
                }
                if let Some(value) = const_by_position.get(&position) {
                    merged.push(const_identity(value, generics)?);
                } else {
                    merged.push(symbolic_type_in(
                        program,
                        source_types.next()?,
                        generics,
                        callable_constraints,
                    )?);
                }
            }
            instance.arguments = merged;
        }
        (TypeSyntaxKind::Tuple(elements), ProvisionalType::Tuple(resolved)) => {
            for (source, target) in elements.iter().zip(resolved) {
                *target = symbolic_type_in(program, source, generics, callable_constraints)?;
            }
        }
        (
            TypeSyntaxKind::SharedReference {
                referent: source, ..
            },
            ProvisionalType::Shared(target),
        )
        | (
            TypeSyntaxKind::UniqueReference {
                referent: source, ..
            },
            ProvisionalType::Unique(target),
        ) => {
            **target = symbolic_type_in(program, source, generics, callable_constraints)?;
        }
        _ => {}
    }
    Some(ty)
}

pub(crate) fn normalize_projection_placeholders(
    ty: &ProvisionalType,
    trait_db: &TraitDb,
    budget: &mut SolverBudget,
) -> Option<ProvisionalType> {
    fn syntax(ty: &ProvisionalType) -> Option<TypeSyntax> {
        let span = crate::span::Span::default();
        let kind = match ty {
            ProvisionalType::Predefined(name) => {
                TypeSyntaxKind::Path(vec![crate::ast::TypePathSegment {
                    name: name.clone(),
                    span,
                }])
            }
            ProvisionalType::Const(value) => {
                TypeSyntaxKind::Path(vec![crate::ast::TypePathSegment {
                    name: value.encoded_name(),
                    span,
                }])
            }
            ProvisionalType::Nominal(instance) => {
                let constructor = TypeSyntax {
                    kind: TypeSyntaxKind::Path(vec![crate::ast::TypePathSegment {
                        name: instance.declaration.0.clone(),
                        span,
                    }]),
                    span,
                };
                if instance.arguments.is_empty() {
                    return Some(constructor);
                }
                TypeSyntaxKind::Application {
                    constructor: Box::new(constructor),
                    arguments: instance
                        .arguments
                        .iter()
                        .map(syntax)
                        .collect::<Option<Vec<_>>>()?,
                    lifetime_arguments: vec![],
                }
            }
            ProvisionalType::Tuple(elements) => {
                TypeSyntaxKind::Tuple(elements.iter().map(syntax).collect::<Option<Vec<_>>>()?)
            }
            ProvisionalType::Shared(referent) => TypeSyntaxKind::SharedReference {
                lifetime: None,
                referent: Box::new(syntax(referent)?),
            },
            ProvisionalType::Unique(referent) => TypeSyntaxKind::UniqueReference {
                lifetime: None,
                referent: Box::new(syntax(referent)?),
            },
            ProvisionalType::Param(_) | ProvisionalType::Callable(_) => return None,
        };
        Some(TypeSyntax { kind, span })
    }

    struct ProjectionFolder<'a> {
        trait_db: &'a TraitDb,
        budget: &'a mut SolverBudget,
    }

    impl ProvisionalTypeFolder for ProjectionFolder<'_> {
        type Error = ();

        fn fold_type(&mut self, ty: &ProvisionalType) -> Result<ProvisionalType, Self::Error> {
            let rebuilt = fold_provisional_type_children(self, ty)?;
            let ProvisionalType::Nominal(instance) = &rebuilt else {
                return Ok(rebuilt);
            };
            let Some(encoded) = instance
                .declaration
                .0
                .strip_prefix(ASSOCIATED_PROJECTION_PREFIX)
            else {
                return Ok(rebuilt);
            };
            let (trait_name, item_name) = encoded.split_once('$').ok_or(())?;
            let (subject, arguments) = instance.arguments.split_first().ok_or(())?;
            let span = crate::span::Span::default();
            let projection = TypeSyntax {
                kind: TypeSyntaxKind::Projection {
                    subject: Box::new(syntax(subject).ok_or(())?),
                    trait_ref: crate::ast::TraitRefSyntax {
                        path: vec![crate::ast::TypePathSegment {
                            name: trait_name.to_owned(),
                            span,
                        }],
                        arguments: vec![],
                        bindings: vec![],
                        span,
                    },
                    item: crate::ast::TypePathSegment {
                        name: item_name.to_owned(),
                        span,
                    },
                    arguments: arguments
                        .iter()
                        .map(|argument| {
                            syntax(argument)
                                .map(AssociatedArgumentSyntax::Type)
                                .ok_or(())
                        })
                        .collect::<Result<_, _>>()?,
                    const_arguments: vec![],
                },
                span,
            };
            self.trait_db
                .normalize_type_detailed_with_budget(&projection, self.budget)
                .map_err(|_| ())
        }

        fn fold_callable_effect(
            &mut self,
            effect: &crate::compiler_typeck::CallableEffect,
        ) -> Result<crate::compiler_typeck::CallableEffect, Self::Error> {
            // Projection normalization historically applies to the callable
            // signature, not to its already-canonical effect row.
            Ok(effect.clone())
        }
    }

    ProjectionFolder { trait_db, budget }.fold_type(ty).ok()
}

fn contains_projection_placeholder(ty: &ProvisionalType) -> bool {
    provisional_type_any(ty, &mut |ty| {
        matches!(
            ty,
            ProvisionalType::Nominal(instance)
                if instance.declaration.0.starts_with(ASSOCIATED_PROJECTION_PREFIX)
        )
    })
}

fn expand_effect_member(
    member: &TypeSyntax,
    program: &Program,
    generics: &BTreeMap<String, GenericParamKey>,
    visiting: &mut BTreeSet<String>,
    output: &mut BTreeSet<crate::compiler_typeck::CallableEffect>,
) -> bool {
    if matches!(&member.kind, TypeSyntaxKind::Tuple(elements) if elements.is_empty()) {
        return true;
    }
    if let TypeSyntaxKind::Tuple(elements) = &member.kind {
        return elements
            .iter()
            .all(|element| expand_effect_member(element, program, generics, visiting, output));
    }
    let (name, arguments) = match &member.kind {
        TypeSyntaxKind::Application {
            constructor,
            arguments,
            ..
        } => {
            let Some(name) = constructor.simple_name() else {
                return false;
            };
            (name, arguments.as_slice())
        }
        _ => {
            let Some(name) = member.simple_name() else {
                return false;
            };
            (name, &[][..])
        }
    };
    if let Some(effect) = program.effects.iter().find(|effect| effect.name == name) {
        if effect
            .generics
            .iter()
            .flat_map(|generics| &generics.params)
            .count()
            != arguments.len()
        {
            return false;
        }
        let Some(arguments) = arguments
            .iter()
            .map(|argument| symbolic_type(argument, generics, &BTreeMap::new()))
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };
        output.insert(crate::compiler_typeck::CallableEffect {
            declaration: crate::compiler_typeck::ProtocolKey(name.to_owned()),
            arguments,
        });
        return true;
    }
    if !arguments.is_empty() {
        return false;
    }
    let Some(alias) = program
        .effect_row_aliases
        .iter()
        .find(|alias| alias.name == name)
    else {
        return false;
    };
    if !visiting.insert(name.to_owned()) {
        return false;
    }
    let valid = alias
        .row
        .effects
        .iter()
        .all(|nested| expand_effect_member(nested, program, generics, visiting, output));
    visiting.remove(name);
    valid
}

fn callable_constraints(
    program: &Program,
    function: &crate::ast::Function,
    owner: &DeclarationKey,
    generics: &BTreeMap<String, GenericParamKey>,
    trait_db: &TraitDb,
) -> (
    BTreeMap<GenericParamKey, CallableShape>,
    BTreeSet<DiscoveryError>,
) {
    fn callable_type(
        program: &Program,
        function: &crate::ast::Function,
        syntax: &TypeSyntax,
        generics: &BTreeMap<String, GenericParamKey>,
        visiting: &mut BTreeSet<(usize, usize)>,
    ) -> Option<ProvisionalType> {
        fn goal_argument_eq(
            program: &Program,
            left: &GoalArgument,
            right: &GoalArgument,
            generics: &BTreeMap<String, GenericParamKey>,
        ) -> bool {
            match (left, right) {
                (GoalArgument::Type(left), GoalArgument::Type(right)) => {
                    symbolic_type_in(program, left, generics, &BTreeMap::new())
                        == symbolic_type_in(program, right, generics, &BTreeMap::new())
                }
                (
                    GoalArgument::Lifetime { name: left, .. },
                    GoalArgument::Lifetime { name: right, .. },
                ) => left == right,
                (GoalArgument::Quantity(left), GoalArgument::Quantity(right)) => left == right,
                (GoalArgument::U32 { value: left, .. }, GoalArgument::U32 { value: right, .. }) => {
                    left == right
                }
                _ => false,
            }
        }
        fn associated_argument_eq(
            program: &Program,
            left: &AssociatedArgumentSyntax,
            right: &AssociatedArgumentSyntax,
            generics: &BTreeMap<String, GenericParamKey>,
        ) -> bool {
            match (left, right) {
                (AssociatedArgumentSyntax::Type(left), AssociatedArgumentSyntax::Type(right)) => {
                    symbolic_type_in(program, left, generics, &BTreeMap::new())
                        == symbolic_type_in(program, right, generics, &BTreeMap::new())
                }
                (
                    AssociatedArgumentSyntax::Lifetime { name: left, .. },
                    AssociatedArgumentSyntax::Lifetime { name: right, .. },
                ) => left == right,
                _ => false,
            }
        }
        let TypeSyntaxKind::Projection {
            subject,
            trait_ref,
            item,
            arguments,
            const_arguments,
        } = &syntax.kind
        else {
            return symbolic_type_in(program, syntax, generics, &BTreeMap::new());
        };
        if !const_arguments.is_empty() || !visiting.insert((syntax.span.start, syntax.span.end)) {
            return None;
        }
        let mut candidates = function
            .where_clause
            .iter()
            .flat_map(|clause| &clause.goals)
            .filter(|goal| {
                goal.polarity == GoalPolarity::Positive
                    && goal.subject.simple_name() == subject.simple_name()
                    && goal
                        .relation
                        .path
                        .iter()
                        .map(|segment| &segment.name)
                        .eq(trait_ref.path.iter().map(|segment| &segment.name))
                    && goal.relation.arguments.len() == trait_ref.arguments.len()
                    && goal
                        .relation
                        .arguments
                        .iter()
                        .zip(&trait_ref.arguments)
                        .all(|(left, right)| goal_argument_eq(program, left, right, generics))
            })
            .flat_map(|goal| &goal.relation.bindings)
            .filter(|binding| {
                binding.name == item.name
                    && binding.arguments.len() == arguments.len()
                    && binding
                        .arguments
                        .iter()
                        .zip(arguments)
                        .all(|(left, right)| associated_argument_eq(program, left, right, generics))
            })
            .filter_map(|binding| binding.value.as_type());
        let Some(value) = candidates.next() else {
            visiting.remove(&(syntax.span.start, syntax.span.end));
            return symbolic_type_in(program, syntax, generics, &BTreeMap::new());
        };
        if candidates.next().is_some() {
            visiting.remove(&(syntax.span.start, syntax.span.end));
            return None;
        }
        let result = callable_type(program, function, value, generics, visiting);
        visiting.remove(&(syntax.span.start, syntax.span.end));
        result
    }

    let mut normalized = BTreeMap::new();
    let mut errors = BTreeSet::new();
    let effect_row_binders = function
        .generics
        .iter()
        .flat_map(|generics| &generics.params)
        .filter(|parameter| parameter.kind == GenericParamKind::EffectRow)
        .filter_map(|parameter| {
            generics
                .get(&parameter.name)
                .cloned()
                .map(|key| (parameter.name.as_str(), key))
        })
        .collect::<BTreeMap<_, _>>();
    for goal in function
        .where_clause
        .iter()
        .flat_map(|clause| &clause.goals)
    {
        let is_fn = goal.relation.path.len() == 1
            && trait_db.trait_key(&goal.relation.path[0].name)
                == trait_db.intrinsic_key(IntrinsicRole::Fn);
        if goal.polarity != GoalPolarity::Positive || goal.relation.path.len() != 1 || !is_fn {
            continue;
        }
        let subject = goal
            .subject
            .simple_name()
            .and_then(|name| generics.get(name))
            .cloned();
        let singleton;
        let tuple = match goal.relation.arguments.as_slice() {
            [
                GoalArgument::Type(TypeSyntax {
                    kind: TypeSyntaxKind::Tuple(params),
                    ..
                }),
            ] => Some(params.as_slice()),
            [
                GoalArgument::Type(
                    ty @ TypeSyntax {
                        kind: TypeSyntaxKind::Path(path),
                        ..
                    },
                ),
            ] if path.len() == 1 && ty.span != path[0].span => {
                singleton = [ty.clone()];
                Some(singleton.as_slice())
            }
            [
                GoalArgument::Type(
                    ty @ TypeSyntax {
                        kind:
                            TypeSyntaxKind::SharedReference { referent: _, .. }
                            | TypeSyntaxKind::UniqueReference { referent: _, .. },
                        ..
                    },
                ),
            ] if matches!(&ty.kind,
                TypeSyntaxKind::SharedReference { lifetime: Some(lifetime), referent }
                | TypeSyntaxKind::UniqueReference { lifetime: Some(lifetime), referent }
                if ty.span.start < lifetime.span.start.saturating_sub(1)
                    || referent.span.end < ty.span.end) =>
            {
                singleton = [ty.clone()];
                Some(singleton.as_slice())
            }
            _ => None,
        };
        let output_binding = goal
            .relation
            .bindings
            .iter()
            .find(|binding| binding.name == "Output");
        let effects_binding = goal
            .relation
            .bindings
            .iter()
            .find(|binding| binding.name == "Effects");
        if let Some(binding) = effects_binding {
            let mut checked = BTreeSet::new();
            let valid = match &binding.value {
                crate::ast::AssociatedBindingValue::EffectRow(row) => {
                    row.tail
                        .as_ref()
                        .is_none_or(|tail| effect_row_binders.contains_key(tail.name.as_str()))
                        && row.effects.iter().all(|member| {
                            expand_effect_member(
                                member,
                                program,
                                generics,
                                &mut BTreeSet::new(),
                                &mut checked,
                            )
                        })
                }
                crate::ast::AssociatedBindingValue::Type(value)
                    if value
                        .simple_name()
                        .is_some_and(|name| effect_row_binders.contains_key(name)) =>
                {
                    true
                }
                crate::ast::AssociatedBindingValue::Type(value) => expand_effect_member(
                    value,
                    program,
                    generics,
                    &mut BTreeSet::new(),
                    &mut checked,
                ),
            };
            if !valid {
                errors.insert(DiscoveryError {
                    owner: owner.clone(),
                    message: "`Fn::Effects` requires declared effects plus at most one bound `EffectRow` tail; unknown effect row member or wrong-kind tail".into(),
                });
                continue;
            }
        }
        let exact = goal.relation.path.len() == 1
            && is_fn
            && (goal.relation.bindings.len() == 1 || goal.relation.bindings.len() == 2)
            && output_binding.is_some()
            && goal
                .relation
                .bindings
                .iter()
                .all(|binding| binding.arguments.is_empty());
        let shape = subject.as_ref().and_then(|_| {
            exact.then_some(())?;
            let params = tuple?
                .iter()
                .map(|param| {
                    callable_type(program, function, param, generics, &mut BTreeSet::new())
                })
                .collect::<Option<Vec<_>>>()?;
            let output_binding = output_binding?;
            let output = output_binding.value.as_type()?;
            let result = callable_type(program, function, output, generics, &mut BTreeSet::new())?;
            let mut effects = BTreeSet::new();
            let infer_effects = effects_binding.is_none();
            let mut effect_tail = None;
            if let Some(binding) = effects_binding {
                let valid =
                    if let crate::ast::AssociatedBindingValue::EffectRow(row) = &binding.value {
                        effect_tail = row
                            .tail
                            .as_ref()
                            .and_then(|tail| effect_row_binders.get(tail.name.as_str()).cloned());
                        row.effects.iter().all(|member| {
                            expand_effect_member(
                                member,
                                program,
                                generics,
                                &mut BTreeSet::new(),
                                &mut effects,
                            )
                        })
                    } else {
                        let value = binding.value.as_type()?;
                        if let Some(tail) = value
                            .simple_name()
                            .and_then(|name| effect_row_binders.get(name).cloned())
                        {
                            effect_tail = Some(tail);
                            true
                        } else {
                            expand_effect_member(
                                value,
                                program,
                                generics,
                                &mut BTreeSet::new(),
                                &mut effects,
                            )
                        }
                    };
                valid.then_some(())?;
            }
            Some(CallableShape {
                params,
                result,
                effects: effects.into_iter().collect(),
                effect_tail,
                infer_effects,
            })
        });
        match (subject, shape) {
            (Some(subject), Some(shape)) if !normalized.contains_key(&subject) => {
                normalized.insert(subject, shape);
            }
            _ => {
                errors.insert(DiscoveryError {
                    owner: owner.clone(),
                    message:
                        "only one exact `F: Fn<Tuple, Output=R, Effects=e>` constraint is discoverable; `Effects` may be omitted for contextual inference"
                            .into(),
                });
            }
        }
    }
    (normalized, errors)
}

pub(crate) fn marker_constraints(
    program: &Program,
    function: &crate::ast::Function,
    owner: &DeclarationKey,
    generics: &BTreeMap<String, GenericParamKey>,
    callable_constraints: &BTreeMap<GenericParamKey, CallableShape>,
    trait_db: &TraitDb,
) -> (Vec<MarkerConstraint>, BTreeSet<DiscoveryError>) {
    let mut constraints = Vec::new();
    let mut errors = BTreeSet::new();
    for goal in function
        .where_clause
        .iter()
        .flat_map(|clause| &clause.goals)
    {
        let mut goal_generics = generics.clone();
        for (index, parameter) in goal.higher_ranked_lifetimes.iter().enumerate() {
            if parameter.kind == GenericParamKind::Type {
                goal_generics.insert(
                    parameter.name.clone(),
                    GenericParamKey {
                        owner: DeclarationKey::Function("$higher_ranked_universe_1".into()),
                        ordinal: index as u32,
                    },
                );
            }
        }
        let symbolic_lifetime = |name: &str| {
            if name == "'static" {
                return Some(LifetimeArg::Static);
            }
            if let Some(index) = goal
                .higher_ranked_lifetimes
                .iter()
                .position(|parameter| parameter.name == name)
            {
                return Some(LifetimeArg::Placeholder {
                    universe: 1,
                    index: index as u32,
                });
            }
            function
                .generics
                .iter()
                .flat_map(|generics| &generics.params)
                .enumerate()
                .find(|(_, parameter)| {
                    parameter.name == name && parameter.kind == GenericParamKind::Lifetime
                })
                .map(|(ordinal, _)| LifetimeArg::Rigid(ordinal as u32))
        };
        if goal.polarity == GoalPolarity::Positive
            && goal.relation.path.len() == 1
            && trait_db.trait_key(&goal.relation.path[0].name)
                == trait_db.intrinsic_key(IntrinsicRole::Fn)
        {
            continue;
        }
        let valid_relation = goal.relation.path.len() == 1
            && (goal.polarity == GoalPolarity::Positive || goal.relation.bindings.is_empty());
        let trait_name = valid_relation.then(|| goal.relation.path[0].name.clone());
        let subject = symbolic_type(&goal.subject, &goal_generics, callable_constraints);
        let arguments = valid_relation
            .then(|| {
                let expected = trait_name
                    .as_deref()
                    .and_then(|name| trait_db.parameter_kinds(name))?;
                goal.relation
                    .arguments
                    .iter()
                    .zip(expected)
                    .map(|(argument, expected)| match (argument, expected) {
                        (GoalArgument::Type(argument), GenericParameterKind::Type) => {
                            symbolic_type(argument, &goal_generics, callable_constraints)
                                .map(GenericArg::Type)
                        }
                        (
                            GoalArgument::Type(argument),
                            GenericParameterKind::Const(expected_kind),
                        ) => {
                            let name = argument.simple_name()?;
                            function
                                .generics
                                .iter()
                                .flat_map(|generics| &generics.params)
                                .enumerate()
                                .find(|(_, parameter)| {
                                    parameter.name == name
                                        && parameter.kind == GenericParamKind::Const(*expected_kind)
                                })
                                .map(|(ordinal, _)| {
                                    GenericArg::RigidConst(ordinal as u32, *expected_kind)
                                })
                        }
                        (GoalArgument::Quantity(quantity), GenericParameterKind::Const(_)) => {
                            let lower = u32::try_from(quantity.lower).ok()?;
                            let upper = quantity.upper.map(u32::try_from).transpose().ok()?;
                            (upper.is_none_or(|upper| lower <= upper))
                                .then_some(GenericArg::Const(ConstValue::Quantity { lower, upper }))
                        }
                        (GoalArgument::U32 { value, .. }, GenericParameterKind::Const(_)) => {
                            u32::try_from(*value)
                                .ok()
                                .map(|value| GenericArg::Const(ConstValue::U32(value)))
                        }
                        (GoalArgument::Lifetime { name, .. }, GenericParameterKind::Lifetime) => {
                            symbolic_lifetime(name).map(GenericArg::Lifetime)
                        }
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()
            })
            .flatten();
        let bindings = valid_relation
            .then(|| {
                goal.relation
                    .bindings
                    .iter()
                    .map(|binding| {
                        Some(AssociatedValue {
                            item: binding.name.clone(),
                            arguments: binding
                                .arguments
                                .iter()
                                .map(|argument| match argument {
                                    AssociatedArgumentSyntax::Type(argument) => symbolic_type(
                                        argument,
                                        &goal_generics,
                                        callable_constraints,
                                    )
                                    .map(GenericArg::Type),
                                    AssociatedArgumentSyntax::Lifetime { name, .. } => {
                                        symbolic_lifetime(name).map(GenericArg::Lifetime)
                                    }
                                })
                                .collect::<Option<Vec<_>>>()?,
                            value: match &binding.value {
                                crate::ast::AssociatedBindingValue::Type(value) => symbolic_type(
                                    value,
                                    &goal_generics,
                                    callable_constraints,
                                )?,
                                crate::ast::AssociatedBindingValue::EffectRow(row) => {
                                    if row.tail.is_some() {
                                        return None;
                                    }
                                    let mut effects = BTreeSet::new();
                                    if !row.effects.iter().all(|member| {
                                        expand_effect_member(
                                            member,
                                            program,
                                            &goal_generics,
                                            &mut BTreeSet::new(),
                                            &mut effects,
                                        )
                                    }) {
                                        return None;
                                    }
                                    ProvisionalType::Tuple(
                                        effects
                                            .into_iter()
                                            .map(|effect| {
                                                ProvisionalType::Nominal(NominalInstanceKey {
                                                    declaration: crate::compiler_typeck::NominalKey(
                                                        format!(
                                                            "{}{}",
                                                            crate::compiler_traits::EFFECT_ROW_MEMBER_PREFIX,
                                                            effect.declaration.0
                                                        ),
                                                    ),
                                                    arguments: effect.arguments,
                                                })
                                            })
                                            .collect(),
                                    )
                                }
                            },
                        })
                    })
                    .collect::<Option<Vec<_>>>()
            })
            .flatten();
        match (trait_name, subject, arguments, bindings) {
            (Some(trait_name), Some(subject), Some(arguments), Some(bindings)) => {
                match trait_db.arity(&trait_name) {
                    Some(expected)
                        if expected == arguments.len()
                            && trait_db.arguments_match(&trait_name, &arguments)
                            && bindings.iter().all(|binding| {
                                trait_db.associated_type_arity(&trait_name, &binding.item)
                                    == Some(binding.arguments.len())
                            }) =>
                    {
                        constraints.push(MarkerConstraint {
                            polarity: goal.polarity,
                            trait_key: trait_db
                                .trait_key(&trait_name)
                                .cloned()
                                .expect("validated trait"),
                            subject,
                            subject_binder: goal
                                .subject
                                .simple_name()
                                .and_then(|name| generics.get(name))
                                .cloned(),
                            arguments,
                            bindings,
                        });
                    }
                    Some(expected) if expected == arguments.len() => {
                        let invalid = bindings.iter().find(|binding| {
                            trait_db.associated_type_arity(&trait_name, &binding.item)
                                != Some(binding.arguments.len())
                        });
                        let message = match invalid.and_then(|binding| {
                            trait_db
                                .associated_type_arity(&trait_name, &binding.item)
                                .map(|arity| (binding, arity))
                        }) {
                            Some((binding, arity)) => format!(
                                "wrong arity for associated type `{}` in marker trait `{trait_name}` equality; expected {arity}, found {}",
                                binding.item,
                                binding.arguments.len()
                            ),
                            None => format!(
                                "unknown associated type `{}` in marker trait `{trait_name}` equality",
                                invalid.map_or("<unknown>", |binding| binding.item.as_str())
                            ),
                        };
                        errors.insert(DiscoveryError {
                            owner: owner.clone(),
                            message,
                        });
                    }
                    Some(expected) => {
                        errors.insert(DiscoveryError {
                            owner: owner.clone(),
                            message: format!(
                                "marker trait `{trait_name}` expects {expected} type arguments, but {} were provided (wrong arity)",
                                arguments.len()
                            ),
                        });
                    }
                    None => {
                        errors.insert(DiscoveryError {
                            owner: owner.clone(),
                            message: format!("unknown marker trait `{trait_name}`"),
                        });
                    }
                }
            }
            _ => {
                errors.insert(DiscoveryError {
                    owner: owner.clone(),
                    message: "only declared marker traits with a discoverable subject are supported in where clauses".into(),
                });
            }
        }
    }
    constraints.sort();
    constraints.dedup();
    (constraints, errors)
}

fn discover_templates(
    program: &Program,
    trait_db: &TraitDb,
) -> (BTreeMap<String, FunctionTemplate>, BTreeSet<DiscoveryError>) {
    fn variable_name(expression: &Expr) -> Option<&str> {
        match &expression.kind {
            ExprKind::Variable(path) if path.len() == 1 => Some(path[0].as_ref()),
            ExprKind::Move(subject) => variable_name(subject),
            _ => None,
        }
    }

    fn callable_parameter_positions(function: &crate::ast::Function) -> Vec<bool> {
        function
            .params
            .iter()
            .map(|parameter| {
                let Some(subject) = parameter.ty.simple_name() else {
                    return false;
                };
                function
                    .where_clause
                    .iter()
                    .flat_map(|clause| &clause.goals)
                    .any(|goal| {
                        goal.subject.simple_name() == Some(subject)
                            && goal.relation.path.len() == 1
                            && goal.relation.path[0].name == "Fn"
                    })
            })
            .collect()
    }

    fn callable_use_summary(
        expression: &Expr,
        aliases: &BTreeSet<String>,
        callable_positions: &BTreeMap<String, Vec<bool>>,
        dependencies: &mut BTreeSet<(String, usize)>,
    ) -> bool {
        match &expression.kind {
            ExprKind::Call(callee, arguments) => {
                let callee_name = variable_name(callee);
                let callee_callable_positions =
                    callee_name.and_then(|name| callable_positions.get(name));
                let mut invoked = callee_name.is_some_and(|name| aliases.contains(name));
                for (index, argument) in arguments.iter().enumerate() {
                    if let Some(alias) = variable_name(argument)
                        && aliases.contains(alias)
                    {
                        match callee_name.and_then(|name| callable_positions.get(name)) {
                            Some(positions) if positions.get(index) == Some(&true) => {
                                dependencies.insert((callee_name.unwrap().to_owned(), index));
                            }
                            // Passing a callable to a declaration without a
                            // matching Fn parameter is a value use, not an
                            // invocation. Unknown/indirect callees remain
                            // conservative because their interface is absent.
                            Some(_) => {}
                            None if !invoked => invoked = true,
                            None => {}
                        }
                    } else if callee_callable_positions.and_then(|positions| positions.get(index))
                        == Some(&true)
                        && match &argument.kind {
                            ExprKind::Closure { body, .. }
                            | ExprKind::TypedClosure { body, .. } => {
                                let mut nested_dependencies = BTreeSet::new();
                                callable_use_summary(
                                    body,
                                    aliases,
                                    callable_positions,
                                    &mut nested_dependencies,
                                )
                            }
                            _ => false,
                        }
                    {
                        dependencies.insert((callee_name.unwrap().to_owned(), index));
                    } else {
                        invoked |= callable_use_summary(
                            argument,
                            aliases,
                            callable_positions,
                            dependencies,
                        );
                    }
                }
                invoked
            }
            ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                let mut aliases = aliases.clone();
                let mut invoked = false;
                for statement in statements.iter() {
                    match statement {
                        Stmt::Let { name, value, .. } => {
                            invoked |= callable_use_summary(
                                value,
                                &aliases,
                                callable_positions,
                                dependencies,
                            );
                            if variable_name(value).is_some_and(|name| aliases.contains(name)) {
                                aliases.insert(name.clone());
                            } else {
                                aliases.remove(name);
                            }
                        }
                        Stmt::Deconstruct { value, .. } | Stmt::Expr(value) => {
                            invoked |= callable_use_summary(
                                value,
                                &aliases,
                                callable_positions,
                                dependencies,
                            );
                        }
                        Stmt::Assign {
                            destination, value, ..
                        } => {
                            invoked |= callable_use_summary(
                                value,
                                &aliases,
                                callable_positions,
                                dependencies,
                            );
                            if let AssignmentPlaceKind::Dereference { reference, .. } =
                                &destination.kind
                            {
                                invoked |= callable_use_summary(
                                    reference,
                                    &aliases,
                                    callable_positions,
                                    dependencies,
                                );
                            }
                        }
                    }
                }
                invoked
            }
            ExprKind::List(values) | ExprKind::Tuple(values) => values.iter().any(|value| {
                callable_use_summary(value, aliases, callable_positions, dependencies)
            }),
            ExprKind::Struct { fields, .. } => fields.iter().any(|(_, value)| {
                callable_use_summary(value, aliases, callable_positions, dependencies)
            }),
            ExprKind::Closure { .. } | ExprKind::TypedClosure { .. } => false,
            ExprKind::Move(value)
            | ExprKind::Field(value, _)
            | ExprKind::Unary { operand: value, .. } => {
                callable_use_summary(value, aliases, callable_positions, dependencies)
            }
            ExprKind::Perform { args, .. } => args.iter().any(|value| {
                callable_use_summary(value, aliases, callable_positions, dependencies)
            }),
            ExprKind::Handle {
                computation,
                clauses,
            } => {
                callable_use_summary(computation, aliases, callable_positions, dependencies)
                    || clauses.iter().any(|clause| {
                        callable_use_summary(
                            &clause.body,
                            aliases,
                            callable_positions,
                            dependencies,
                        )
                    })
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                callable_use_summary(lhs, aliases, callable_positions, dependencies)
                    || callable_use_summary(rhs, aliases, callable_positions, dependencies)
            }
            ExprKind::LabelDestination { body, .. } => {
                callable_use_summary(body, aliases, callable_positions, dependencies)
            }
            ExprKind::Is { subject, .. } => {
                callable_use_summary(subject, aliases, callable_positions, dependencies)
            }
            ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Char(_)
            | ExprKind::Byte(_)
            | ExprKind::ByteString(_)
            | ExprKind::String(_)
            | ExprKind::Variable(_) => false,
            ExprKind::LabelReference(_) => false,
            ExprKind::Resume { resumption, value } | ExprKind::TailResume { resumption, value } => {
                callable_use_summary(resumption, aliases, callable_positions, dependencies)
                    || value.as_deref().is_some_and(|value| {
                        callable_use_summary(value, aliases, callable_positions, dependencies)
                    })
            }
            ExprKind::Cancel { resumption } => {
                callable_use_summary(resumption, aliases, callable_positions, dependencies)
            }
        }
    }

    let callable_positions = program
        .functions
        .iter()
        .map(|function| {
            (
                function.name.clone(),
                callable_parameter_positions(function),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut callable_invocations = BTreeMap::<String, Vec<bool>>::new();
    let mut callable_dependencies = BTreeMap::<String, Vec<BTreeSet<(String, usize)>>>::new();
    for function in &program.functions {
        let positions = &callable_positions[&function.name];
        let mut direct = vec![false; positions.len()];
        let mut dependencies = vec![BTreeSet::new(); positions.len()];
        for (index, parameter) in function.params.iter().enumerate() {
            if !positions[index] {
                continue;
            }
            let aliases = BTreeSet::from([parameter.name.clone()]);
            direct[index] = callable_use_summary(
                &function.body,
                &aliases,
                &callable_positions,
                &mut dependencies[index],
            );
        }
        callable_invocations.insert(function.name.clone(), direct);
        callable_dependencies.insert(function.name.clone(), dependencies);
    }
    loop {
        let previous = callable_invocations.clone();
        let mut changed = false;
        for (function, dependencies) in &callable_dependencies {
            for (index, dependencies) in dependencies.iter().enumerate() {
                if callable_invocations[function][index] {
                    continue;
                }
                let invoked = dependencies.iter().any(|(callee, parameter)| {
                    previous
                        .get(callee)
                        .and_then(|summary| summary.get(*parameter))
                        .copied()
                        .unwrap_or(true)
                });
                if invoked {
                    callable_invocations.get_mut(function).unwrap()[index] = true;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    let mut templates = BTreeMap::new();
    let mut errors = BTreeSet::new();
    for function in &program.functions {
        let declaration = DeclarationKey::Function(function.name.clone());
        let generics = function
            .generics
            .iter()
            .flat_map(|generics| &generics.params)
            .enumerate()
            .map(|(ordinal, param)| {
                (
                    param.name.clone(),
                    GenericParamKey {
                        owner: declaration.clone(),
                        ordinal: ordinal as u32,
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        let generic_params = function
            .generics
            .iter()
            .flat_map(|generics| &generics.params)
            .filter(|param| {
                matches!(
                    param.kind,
                    GenericParamKind::Type
                        | GenericParamKind::Const(_)
                        | GenericParamKind::EffectRow
                )
            })
            .map(|param| generics[&param.name].clone())
            .collect::<Vec<_>>();
        let (callable_constraints, constraint_errors) =
            callable_constraints(program, function, &declaration, &generics, trait_db);
        let effectful_callable_binders = function
            .params
            .iter()
            .enumerate()
            .filter_map(|(index, parameter)| {
                let binder = parameter
                    .ty
                    .simple_name()
                    .and_then(|name| generics.get(name))?;
                (callable_constraints.contains_key(binder)
                    && callable_invocations[&function.name][index])
                    .then(|| binder.clone())
            })
            .collect();
        let (marker_constraints, marker_errors) = marker_constraints(
            program,
            function,
            &declaration,
            &generics,
            &callable_constraints,
            trait_db,
        );
        let lexical_environment =
            trait_db.param_env(marker_constraints.iter().map(|constraint| TraitFact {
                polarity: constraint.polarity,
                trait_key: constraint.trait_key.clone(),
                subject: constraint.subject.clone(),
                arguments: constraint.arguments.clone(),
                bindings: constraint.bindings.clone(),
            }));
        let constraints_consistent = lexical_environment.is_consistent();
        if !constraints_consistent {
            errors.insert(DiscoveryError {
                owner: declaration.clone(),
                message: "lexical trait environment contains contradictory polarity or associated equality facts".into(),
            });
        }
        let constraints_discoverable =
            constraint_errors.is_empty() && marker_errors.is_empty() && constraints_consistent;
        errors.extend(constraint_errors);
        errors.extend(marker_errors);
        if !constraints_discoverable {
            continue;
        }
        let params = function
            .params
            .iter()
            .map(|param| symbolic_type_in(program, &param.ty, &generics, &callable_constraints))
            .collect::<Option<Vec<_>>>();
        let result = function
            .return_type
            .as_ref()
            .map(|result| symbolic_type_in(program, result, &generics, &callable_constraints))
            .unwrap_or_else(|| Some(ProvisionalType::Predefined("Unit".into())));
        let (Some(params), Some(result)) = (params, result) else {
            errors.insert(DiscoveryError {
                owner: declaration,
                message: "function signature is not symbolically discoverable".into(),
            });
            continue;
        };
        let parameter_binders = function
            .params
            .iter()
            .map(|param| {
                param
                    .ty
                    .simple_name()
                    .and_then(|name| generics.get(name))
                    .filter(|key| callable_constraints.contains_key(*key))
                    .cloned()
            })
            .collect();
        let result_binder = function
            .return_type
            .as_ref()
            .and_then(TypeSyntax::simple_name)
            .and_then(|name| generics.get(name))
            .filter(|key| callable_constraints.contains_key(*key))
            .cloned();
        let result_nominal_binders = function.return_type.as_ref().and_then(|result| {
            let TypeSyntaxKind::Application {
                constructor,
                arguments,
                ..
            } = &result.kind
            else {
                return None;
            };
            Some((
                constructor.simple_name()?.to_owned(),
                arguments
                    .iter()
                    .map(|argument| {
                        argument
                            .simple_name()
                            .and_then(|name| generics.get(name))
                            .filter(|key| callable_constraints.contains_key(*key))
                            .cloned()
                    })
                    .collect(),
            ))
        });
        fn returns_binding(expression: &Expr, name: &str) -> bool {
            match &expression.kind {
                ExprKind::Variable(path) => path.len() == 1 && path[0].as_ref() == name,
                ExprKind::Block(statements) if statements.len() == 1 => {
                    matches!(&statements[0], Stmt::Expr(value) if returns_binding(value, name))
                }
                _ => false,
            }
        }
        let transparent_identity = function.params.len() == 1
            && returns_binding(&function.body, &function.params[0].name)
            && params[0] == result;
        templates.insert(
            function.name.clone(),
            FunctionTemplate {
                declaration,
                generic_params,
                params,
                parameter_binders,
                result_binder,
                result_nominal_binders,
                result,
                callable_constraints,
                effectful_callable_binders,
                marker_constraints,
                transparent_identity,
            },
        );
    }
    (templates, errors)
}

fn fold_const_expression_identity(ty: ProvisionalType) -> Option<ProvisionalType> {
    let ProvisionalType::Nominal(instance) = &ty else {
        return Some(ty);
    };
    if !instance.declaration.0.starts_with("$const$expr$") {
        return Some(ty);
    }
    let [
        ProvisionalType::Const(ProvisionalConst::U32(left)),
        ProvisionalType::Const(ProvisionalConst::U32(right)),
    ] = instance.arguments.as_slice()
    else {
        return Some(ty);
    };
    let value = match instance.declaration.0.as_str() {
        "$const$expr$add" => left.checked_add(*right),
        "$const$expr$sub" => left.checked_sub(*right),
        "$const$expr$mul" => left.checked_mul(*right),
        "$const$expr$div" => left.checked_div(*right),
        "$const$expr$rem" => left.checked_rem(*right),
        _ => return Some(ty),
    }?;
    Some(ProvisionalType::Const(ProvisionalConst::U32(value)))
}

pub(crate) fn substitute(
    ty: &ProvisionalType,
    substitutions: &BTreeMap<GenericParamKey, SpecializationArgument>,
) -> Option<ProvisionalType> {
    SubstitutionFolder {
        substitutions,
        visiting: BTreeSet::new(),
        missing: MissingParameter::Reject,
    }
    .fold_type(ty)
    .ok()
}

fn substitute_preserving_missing(
    ty: &ProvisionalType,
    substitutions: &BTreeMap<GenericParamKey, SpecializationArgument>,
) -> Option<ProvisionalType> {
    SubstitutionFolder {
        substitutions,
        visiting: BTreeSet::new(),
        missing: MissingParameter::Preserve,
    }
    .fold_type(ty)
    .ok()
}

fn collapse_type_substitution_chains(
    substitutions: &mut BTreeMap<GenericParamKey, SpecializationArgument>,
) {
    let available = substitutions.clone();
    for argument in substitutions.values_mut() {
        if let SpecializationArgument::Type(ty) = argument
            && let Some(resolved) = substitute_preserving_missing(ty, &available)
        {
            *ty = resolved;
        }
    }
}

/// Controls whether an incomplete contextual type preserves rigid parameters
/// owned by its generic caller. Recursively resolving a substitution value
/// always preserves such a rigid tail.
#[derive(Clone, Copy, Eq, PartialEq)]
enum MissingParameter {
    Reject,
    Preserve,
}

struct SubstitutionFolder<'a> {
    substitutions: &'a BTreeMap<GenericParamKey, SpecializationArgument>,
    visiting: BTreeSet<GenericParamKey>,
    missing: MissingParameter,
}

impl ProvisionalTypeFolder for SubstitutionFolder<'_> {
    type Error = ();

    fn fold_type(&mut self, ty: &ProvisionalType) -> Result<ProvisionalType, Self::Error> {
        if let ProvisionalType::Param(key) = ty {
            let Some(argument) = self.substitutions.get(key).cloned() else {
                return (self.missing == MissingParameter::Preserve)
                    .then(|| ty.clone())
                    .ok_or(());
            };
            if self.visiting.is_empty()
                && matches!(&argument, SpecializationArgument::Type(value) if value == ty)
            {
                // Recursive symbolic validation uses the declaration's
                // canonical binder as both caller-rigid and callee-local.
                return Ok(ty.clone());
            }
            if !self.visiting.insert(key.clone()) {
                return Err(());
            }
            let outer_missing = self.missing;
            self.missing = MissingParameter::Preserve;
            let resolved = match &argument {
                SpecializationArgument::Type(value) => self.fold_type(value),
                SpecializationArgument::Closure(_, shape, _, _, _, _) => {
                    Ok(ProvisionalType::Callable(shape.clone()))
                }
                SpecializationArgument::EffectRow(_) => Err(()),
            };
            self.missing = outer_missing;
            self.visiting.remove(key);
            return resolved;
        }
        let folded = fold_provisional_type_children(self, ty)?;
        if matches!(folded, ProvisionalType::Nominal(_)) {
            fold_const_expression_identity(folded).ok_or(())
        } else {
            Ok(folded)
        }
    }
}

fn substitute_generic_arg(
    argument: &GenericArg,
    substitutions: &BTreeMap<GenericParamKey, SpecializationArgument>,
) -> Option<GenericArg> {
    match argument {
        GenericArg::Type(ty) => substitute(ty, substitutions).map(GenericArg::Type),
        GenericArg::Lifetime(lifetime) => Some(GenericArg::Lifetime(lifetime.clone())),
        GenericArg::Const(value) => Some(GenericArg::Const(value.clone())),
        GenericArg::RigidConst(ordinal, kind) => substitutions
            .iter()
            .find(|(key, _)| key.ordinal == *ordinal)
            .and_then(|(_, argument)| match argument {
                SpecializationArgument::Type(ProvisionalType::Const(ProvisionalConst::U32(
                    value,
                ))) if *kind == crate::ast::ConstKind::U32 => Some(ConstValue::U32(*value)),
                SpecializationArgument::Type(ProvisionalType::Const(
                    ProvisionalConst::Quantity { lower, upper },
                )) if *kind == crate::ast::ConstKind::Quantity => Some(ConstValue::Quantity {
                    lower: *lower,
                    upper: *upper,
                }),
                _ => None,
            })
            .map(GenericArg::Const),
    }
}

fn ground(ty: &ProvisionalType) -> bool {
    !provisional_type_any(ty, &mut |ty| matches!(ty, ProvisionalType::Param(_)))
}

fn supported_capture_shape(ty: &ProvisionalType) -> bool {
    !provisional_type_any(ty, &mut |ty| {
        matches!(ty, ProvisionalType::Callable(_) | ProvisionalType::Param(_))
    })
}

fn contains_unique_reference_shape(ty: &ProvisionalType) -> bool {
    provisional_signature_type_any(ty, &mut |ty| matches!(ty, ProvisionalType::Unique(_)))
}

fn bind_callable_effects(
    formal: &CallableShape,
    actual: &CallableShape,
    substitutions: &mut BTreeMap<GenericParamKey, SpecializationArgument>,
) -> bool {
    if formal.infer_effects {
        return true;
    }
    if actual.infer_effects {
        return false;
    }
    let mut actual_effects = actual.effects.clone();
    let actual_open = if let Some(tail) = &actual.effect_tail {
        match substitutions.get(tail) {
            Some(SpecializationArgument::EffectRow(residual)) => {
                actual_effects.extend(residual.iter().cloned());
                false
            }
            Some(_) => return false,
            None => true,
        }
    } else {
        false
    };
    actual_effects.sort();
    actual_effects.dedup();
    let mut unmatched = (0..actual_effects.len()).collect::<BTreeSet<_>>();
    for expected in &formal.effects {
        let mut matched = None;
        for index in unmatched.iter().copied() {
            let found = &actual_effects[index];
            if expected.declaration != found.declaration
                || expected.arguments.len() != found.arguments.len()
            {
                continue;
            }
            let mut trial = substitutions.clone();
            if expected
                .arguments
                .iter()
                .zip(&found.arguments)
                .all(|(expected, found)| bind(expected, found, &mut trial))
            {
                matched = Some((index, trial));
                break;
            }
        }
        let Some((index, trial)) = matched else {
            return false;
        };
        *substitutions = trial;
        unmatched.remove(&index);
    }
    let residual = unmatched
        .into_iter()
        .map(|index| actual_effects[index].clone())
        .collect::<Vec<_>>();
    let Some(tail) = &formal.effect_tail else {
        return !actual_open && residual.is_empty();
    };
    if actual_open {
        return true;
    }
    match substitutions.get(tail) {
        Some(SpecializationArgument::EffectRow(existing)) => existing == &residual,
        Some(_) => false,
        None => {
            substitutions.insert(tail.clone(), SpecializationArgument::EffectRow(residual));
            true
        }
    }
}

fn bind(
    formal: &ProvisionalType,
    actual: &ProvisionalType,
    substitutions: &mut BTreeMap<GenericParamKey, SpecializationArgument>,
) -> bool {
    match formal {
        ProvisionalType::Param(key) => match substitutions.get(key) {
            Some(SpecializationArgument::Type(existing)) => existing == actual,
            Some(SpecializationArgument::Closure(_, shape, _, _, _, _)) => {
                actual == &ProvisionalType::Callable(shape.clone())
            }
            Some(SpecializationArgument::EffectRow(_)) => false,
            None => {
                substitutions.insert(key.clone(), SpecializationArgument::Type(actual.clone()));
                true
            }
        },
        ProvisionalType::Shared(left) => {
            matches!(actual, ProvisionalType::Shared(right) if bind(left, right, substitutions))
        }
        ProvisionalType::Unique(left) => {
            matches!(actual, ProvisionalType::Unique(right) if bind(left, right, substitutions))
        }
        ProvisionalType::Callable(left) => matches!(actual, ProvisionalType::Callable(right)
        if left.params.len() == right.params.len()
            && left.params.iter().zip(&right.params).all(|(left, right)| bind(left, right, substitutions))
            && bind(&left.result, &right.result, substitutions)
            && bind_callable_effects(left, right, substitutions)),
        ProvisionalType::Nominal(left) => matches!(actual, ProvisionalType::Nominal(right)
            if left.declaration == right.declaration
                && left.arguments.len() == right.arguments.len()
                && left.arguments.iter().zip(&right.arguments)
                    .all(|(left, right)| bind(left, right, substitutions))),
        ProvisionalType::Tuple(left) => matches!(actual, ProvisionalType::Tuple(right)
            if left.len() == right.len()
                && left.iter().zip(right).all(|(left, right)| bind(left, right, substitutions))),
        concrete => concrete == actual,
    }
}

fn inference_occurs(
    key: &GenericParamKey,
    ty: &ProvisionalType,
    substitutions: &BTreeMap<GenericParamKey, SpecializationArgument>,
    visiting: &mut BTreeSet<GenericParamKey>,
) -> bool {
    provisional_type_any(ty, &mut |ty| {
        let ProvisionalType::Param(candidate) = ty else {
            return false;
        };
        if candidate == key {
            return true;
        }
        if !visiting.insert(candidate.clone()) {
            return false;
        }
        let occurs = substitutions
            .get(candidate)
            .is_some_and(|argument| match argument {
                SpecializationArgument::Type(ty) => {
                    inference_occurs(key, ty, substitutions, visiting)
                }
                SpecializationArgument::Closure(_, shape, _, _, _, _) => {
                    shape
                        .params
                        .iter()
                        .any(|ty| inference_occurs(key, ty, substitutions, visiting))
                        || inference_occurs(key, &shape.result, substitutions, visiting)
                }
                SpecializationArgument::EffectRow(_) => false,
            });
        visiting.remove(candidate);
        occurs
    })
}

/// Recover the structural identity hidden behind a post-instantiation ground
/// nominal declaration. Specialization discovery normally reasons about
/// generic source heads (`Vec<T>`, `Result<T, E>`), but a nested expression may
/// already expose the generated monomorphic declaration name. Treating that
/// name as an unrelated zero-argument nominal loses otherwise exact inference
/// evidence at calls such as `Vec::truncate(&mut grounded_vec, length)`.
fn expand_ground_nominals(ty: &ProvisionalType) -> ProvisionalType {
    match ty {
        ProvisionalType::Nominal(instance) if instance.arguments.is_empty() => {
            decode_nominal_instance(&instance.declaration.0)
                .map(|instance| expand_ground_nominals(&ProvisionalType::Nominal(instance)))
                .unwrap_or_else(|| ty.clone())
        }
        ProvisionalType::Nominal(instance) => ProvisionalType::Nominal(NominalInstanceKey {
            declaration: instance.declaration.clone(),
            arguments: instance
                .arguments
                .iter()
                .map(expand_ground_nominals)
                .collect(),
        }),
        ProvisionalType::Shared(referent) => {
            ProvisionalType::shared(expand_ground_nominals(referent))
        }
        ProvisionalType::Unique(referent) => {
            ProvisionalType::unique(expand_ground_nominals(referent))
        }
        ProvisionalType::Tuple(elements) if elements.is_empty() => {
            ProvisionalType::Predefined("Unit".into())
        }
        ProvisionalType::Tuple(elements) => {
            ProvisionalType::Tuple(elements.iter().map(expand_ground_nominals).collect())
        }
        ProvisionalType::Callable(shape) => ProvisionalType::Callable(Box::new(CallableShape {
            params: shape.params.iter().map(expand_ground_nominals).collect(),
            result: expand_ground_nominals(&shape.result),
            effects: shape
                .effects
                .iter()
                .map(|effect| crate::compiler_typeck::CallableEffect {
                    declaration: effect.declaration.clone(),
                    arguments: effect
                        .arguments
                        .iter()
                        .map(expand_ground_nominals)
                        .collect(),
                })
                .collect(),
            effect_tail: shape.effect_tail.clone(),
            infer_effects: shape.infer_effects,
        })),
        ProvisionalType::Predefined(_) | ProvisionalType::Const(_) | ProvisionalType::Param(_) => {
            ty.clone()
        }
    }
}

fn equivalent_specialization_type(left: &ProvisionalType, right: &ProvisionalType) -> bool {
    left == right || expand_ground_nominals(left) == expand_ground_nominals(right)
}

fn unify_inference_with_rigid_mode(
    left: &ProvisionalType,
    right: &ProvisionalType,
    mutable: &BTreeSet<GenericParamKey>,
    substitutions: &mut BTreeMap<GenericParamKey, SpecializationArgument>,
    rigid_are_unknown: bool,
) -> bool {
    fn resolve(
        ty: &ProvisionalType,
        substitutions: &BTreeMap<GenericParamKey, SpecializationArgument>,
    ) -> ProvisionalType {
        match ty {
            ProvisionalType::Param(key) => match substitutions.get(key) {
                Some(SpecializationArgument::Type(value)) if value != ty => {
                    expand_ground_nominals(&resolve(value, substitutions))
                }
                Some(SpecializationArgument::Closure(_, shape, _, _, _, _)) => {
                    ProvisionalType::Callable(shape.clone())
                }
                _ => ty.clone(),
            },
            _ => expand_ground_nominals(ty),
        }
    }
    fn bind_var(
        key: &GenericParamKey,
        value: &ProvisionalType,
        substitutions: &mut BTreeMap<GenericParamKey, SpecializationArgument>,
    ) -> bool {
        if inference_occurs(key, value, substitutions, &mut BTreeSet::new()) {
            return false;
        }
        substitutions.insert(key.clone(), SpecializationArgument::Type(value.clone()));
        true
    }
    let left = resolve(left, substitutions);
    let right = resolve(right, substitutions);
    if left == right {
        if !rigid_are_unknown
            && let ProvisionalType::Param(key) = &left
            && mutable.contains(key)
        {
            substitutions
                .entry(key.clone())
                .or_insert_with(|| SpecializationArgument::Type(left.clone()));
        }
        return true;
    }
    if let ProvisionalType::Param(key) = &left
        && mutable.contains(key)
    {
        if rigid_are_unknown
            && provisional_type_any(
                &right,
                &mut |ty| matches!(ty, ProvisionalType::Param(candidate) if !mutable.contains(candidate)),
            )
        {
            return true;
        }
        return bind_var(key, &right, substitutions);
    }
    if let ProvisionalType::Param(key) = &right
        && mutable.contains(key)
    {
        if rigid_are_unknown
            && provisional_type_any(
                &left,
                &mut |ty| matches!(ty, ProvisionalType::Param(candidate) if !mutable.contains(candidate)),
            )
        {
            return true;
        }
        return bind_var(key, &left, substitutions);
    }
    if rigid_are_unknown
        && (matches!(left, ProvisionalType::Param(_)) || matches!(right, ProvisionalType::Param(_)))
    {
        return true;
    }
    match (&left, &right) {
        (ProvisionalType::Shared(a), ProvisionalType::Shared(b))
        | (ProvisionalType::Unique(a), ProvisionalType::Unique(b)) => {
            unify_inference_with_rigid_mode(a, b, mutable, substitutions, rigid_are_unknown)
        }
        (ProvisionalType::Tuple(a), ProvisionalType::Tuple(b)) if a.len() == b.len() => {
            a.iter().zip(b).all(|(a, b)| {
                unify_inference_with_rigid_mode(a, b, mutable, substitutions, rigid_are_unknown)
            })
        }
        (ProvisionalType::Nominal(a), ProvisionalType::Nominal(b))
            if a.declaration == b.declaration && a.arguments.len() == b.arguments.len() =>
        {
            a.arguments.iter().zip(&b.arguments).all(|(a, b)| {
                unify_inference_with_rigid_mode(a, b, mutable, substitutions, rigid_are_unknown)
            })
        }
        (ProvisionalType::Callable(a), ProvisionalType::Callable(b))
            if a.params.len() == b.params.len() && a.effects == b.effects =>
        {
            a.params.iter().zip(&b.params).all(|(a, b)| {
                unify_inference_with_rigid_mode(a, b, mutable, substitutions, rigid_are_unknown)
            }) && unify_inference_with_rigid_mode(
                &a.result,
                &b.result,
                mutable,
                substitutions,
                rigid_are_unknown,
            )
        }
        _ => false,
    }
}

fn unify_inference(
    left: &ProvisionalType,
    right: &ProvisionalType,
    mutable: &BTreeSet<GenericParamKey>,
    substitutions: &mut BTreeMap<GenericParamKey, SpecializationArgument>,
) -> bool {
    unify_inference_with_rigid_mode(left, right, mutable, substitutions, false)
}

/// Constrain inference variables owned by the current call from a contextual
/// type that may still contain rigid variables owned by an enclosing call.
///
/// A rigid variable is an unknown here, not evidence that two otherwise
/// matching structures conflict. For example, an inner `Result<(), E>` must
/// learn `E = WalkError` from the outer context `Result<T, WalkError>` even
/// though only the enclosing call is allowed to solve `T`.
fn constrain_contextual_inference(
    left: &ProvisionalType,
    right: &ProvisionalType,
    mutable: &BTreeSet<GenericParamKey>,
    substitutions: &mut BTreeMap<GenericParamKey, SpecializationArgument>,
) -> bool {
    unify_inference_with_rigid_mode(left, right, mutable, substitutions, true)
}

pub(crate) fn captured_outer_uses(
    expression: &Expr,
    outer: &BTreeSet<String>,
    initially_bound: &[String],
) -> Vec<(String, CaptureMode)> {
    fn bind_pattern(pattern: &crate::ast::Pattern, bound: &mut BTreeSet<String>) {
        match &pattern.kind {
            PatternKind::Binding(name) => {
                bound.insert(name.clone());
            }
            PatternKind::Variant { fields, .. } => {
                for field in fields {
                    bind_pattern(field, bound);
                }
            }
            PatternKind::Tuple { elements, .. } => {
                for element in elements {
                    bind_pattern(element, bound);
                }
            }
            PatternKind::Struct { fields, .. } => {
                for field in fields {
                    bind_pattern(&field.pattern, bound);
                }
            }
            PatternKind::Wildcard
            | PatternKind::Unit
            | PatternKind::Int(_)
            | PatternKind::Float(_)
            | PatternKind::String(_)
            | PatternKind::Char(_)
            | PatternKind::Byte(_) => {}
        }
    }

    fn record(found: &mut Vec<(String, CaptureMode)>, name: &str, mode: CaptureMode) {
        if let Some((_, existing)) = found.iter_mut().find(|(candidate, _)| candidate == name) {
            *existing = (*existing).max(mode);
        } else {
            found.push((name.to_owned(), mode));
        }
    }

    fn visit(
        expression: &Expr,
        outer: &BTreeSet<String>,
        bound: &mut BTreeSet<String>,
        found: &mut Vec<(String, CaptureMode)>,
        access: CaptureMode,
    ) {
        match &expression.kind {
            ExprKind::Variable(path) if path.len() == 1 => {
                let name = path[0].as_ref();
                if outer.contains(name) && !bound.contains(name) {
                    record(found, name, access);
                }
            }
            ExprKind::Closure { params, body } => {
                let saved = bound.clone();
                bound.extend(params.iter().map(|param| param.to_string()));
                visit(body, outer, bound, found, CaptureMode::Observe);
                *bound = saved;
            }
            ExprKind::TypedClosure { params, body, .. } => {
                let saved = bound.clone();
                bound.extend(params.iter().map(|param| param.name.clone()));
                visit(body, outer, bound, found, CaptureMode::Observe);
                *bound = saved;
            }
            ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                let saved = bound.clone();
                for statement in statements.iter() {
                    match statement {
                        Stmt::Let { name, value, .. } => {
                            visit(value, outer, bound, found, CaptureMode::Observe);
                            bound.insert(name.clone());
                        }
                        Stmt::Deconstruct { fields, value, .. } => {
                            visit(value, outer, bound, found, CaptureMode::Move);
                            bound.extend(fields.iter().filter_map(|field| field.binding.clone()));
                        }
                        Stmt::Expr(value) => {
                            visit(value, outer, bound, found, CaptureMode::Observe)
                        }
                        Stmt::Assign {
                            destination, value, ..
                        } => {
                            visit(value, outer, bound, found, CaptureMode::Observe);
                            match &destination.kind {
                                AssignmentPlaceKind::Local { name, .. } => {
                                    if outer.contains(name.as_ref())
                                        && !bound.contains(name.as_ref())
                                    {
                                        record(found, name, CaptureMode::Mutate);
                                    }
                                }
                                AssignmentPlaceKind::Dereference { reference, .. } => {
                                    visit(reference, outer, bound, found, CaptureMode::Mutate)
                                }
                            }
                        }
                    }
                }
                *bound = saved;
            }
            ExprKind::List(values) | ExprKind::Tuple(values) => {
                for value in values.iter() {
                    visit(value, outer, bound, found, CaptureMode::Observe);
                }
            }
            ExprKind::Struct { fields, .. } => {
                for (_, value) in fields.iter() {
                    visit(value, outer, bound, found, CaptureMode::Observe);
                }
            }
            ExprKind::Move(subject) => visit(subject, outer, bound, found, CaptureMode::Move),
            ExprKind::Unary {
                op: UnaryOp::BorrowUnique,
                operand,
            } => visit(operand, outer, bound, found, CaptureMode::Mutate),
            ExprKind::Unary {
                op: UnaryOp::BorrowShared,
                operand,
            } => visit(operand, outer, bound, found, CaptureMode::Observe),
            ExprKind::Field(subject, _)
            | ExprKind::Unary {
                operand: subject, ..
            } => visit(subject, outer, bound, found, access),
            ExprKind::Call(callee, args) => {
                visit(callee, outer, bound, found, CaptureMode::Observe);
                for argument in args.iter() {
                    visit(argument, outer, bound, found, CaptureMode::Observe);
                }
            }
            ExprKind::Perform { args, .. } => {
                for argument in args.iter() {
                    visit(argument, outer, bound, found, CaptureMode::Observe);
                }
            }
            ExprKind::Handle {
                computation,
                clauses,
            } => {
                visit(computation, outer, bound, found, CaptureMode::Observe);
                for clause in clauses.iter() {
                    let saved = bound.clone();
                    for pattern in &clause.patterns {
                        bind_pattern(pattern, bound);
                    }
                    if let Some(resumption) = &clause.resumption {
                        bound.insert(resumption.clone());
                    }
                    visit(&clause.body, outer, bound, found, CaptureMode::Observe);
                    *bound = saved;
                }
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                visit(lhs, outer, bound, found, CaptureMode::Observe);
                visit(rhs, outer, bound, found, CaptureMode::Observe);
            }
            ExprKind::LabelDestination { body, .. } => {
                visit(body, outer, bound, found, CaptureMode::Observe)
            }
            ExprKind::Is { subject, .. } => {
                visit(subject, outer, bound, found, CaptureMode::Observe)
            }
            ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Char(_)
            | ExprKind::Byte(_)
            | ExprKind::ByteString(_)
            | ExprKind::String(_)
            | ExprKind::Variable(_) => {}
            ExprKind::LabelReference(_) => {}
            ExprKind::Resume { resumption, value } | ExprKind::TailResume { resumption, value } => {
                visit(resumption, outer, bound, found, CaptureMode::Observe);
                if let Some(value) = value {
                    visit(value, outer, bound, found, CaptureMode::Observe);
                }
            }
            ExprKind::Cancel { resumption } => {
                visit(resumption, outer, bound, found, CaptureMode::Observe)
            }
        }
    }
    let mut found = Vec::new();
    visit(
        expression,
        outer,
        &mut initially_bound.iter().cloned().collect(),
        &mut found,
        CaptureMode::Observe,
    );
    found
}

fn passed_as_unique_call_argument(
    body: &Expr,
    name: &str,
    templates: &BTreeMap<String, FunctionTemplate>,
) -> bool {
    visit_expr_preorder(body, |expression| {
        let ExprKind::Call(callee, arguments) = &expression.kind else {
            return ControlFlow::Continue(());
        };
        let ExprKind::Variable(path) = &callee.kind else {
            return ControlFlow::Continue(());
        };
        let Some(template) = (path.len() == 1)
            .then(|| templates.get(path[0].as_ref()))
            .flatten()
        else {
            return ControlFlow::Continue(());
        };
        if arguments
            .iter()
            .zip(&template.params)
            .any(|(argument, formal)| {
                let argument = match &argument.kind {
                    ExprKind::Move(argument) => argument.as_ref(),
                    _ => argument,
                };
                matches!(formal, ProvisionalType::Unique(_))
                    && matches!(&argument.kind, ExprKind::Variable(argument_path)
                    if argument_path.len() == 1 && argument_path[0].as_ref() == name)
            })
        {
            ControlFlow::Break(())
        } else {
            ControlFlow::Continue(())
        }
    })
    .is_break()
}

pub(crate) fn recursive_closure_binding(value: &Expr, name: &str) -> bool {
    let (params, body) = match &value.kind {
        ExprKind::Closure { params, body } => (
            params.iter().map(ToString::to_string).collect::<Vec<_>>(),
            body.as_ref(),
        ),
        ExprKind::TypedClosure { params, body, .. } => (
            params
                .iter()
                .map(|parameter| parameter.name.clone())
                .collect::<Vec<_>>(),
            body.as_ref(),
        ),
        _ => return false,
    };
    captured_outer_uses(body, &BTreeSet::from([name.to_owned()]), &params)
        .iter()
        .any(|(capture, _)| capture == name)
}

/// Infer the closed direct outward row of an anonymous body in declaration
/// space. Direct performs and the exact outward rows recorded by ordinary call
/// resolution participate, so an open `Fn::Effects` projection can bind before
/// generated signatures exist. A handled protocol is removed only for the body
/// of that handler; final coverage checking remains authoritative in Core
/// lowering.
fn direct_closure_effects(
    expression: &Expr,
    resolve: &impl Fn(crate::span::Span, &str) -> Option<crate::compiler_typeck::CallableEffect>,
    resolve_call: &impl Fn(&Expr) -> BTreeSet<crate::compiler_typeck::CallableEffect>,
) -> BTreeSet<crate::compiler_typeck::CallableEffect> {
    struct Collector<'a, R, C> {
        resolve: &'a R,
        resolve_call: &'a C,
        output: BTreeSet<crate::compiler_typeck::CallableEffect>,
    }

    impl<'ast, R, C> ExprVisitor<'ast> for Collector<'_, R, C>
    where
        R: Fn(crate::span::Span, &str) -> Option<crate::compiler_typeck::CallableEffect>,
        C: Fn(&Expr) -> BTreeSet<crate::compiler_typeck::CallableEffect>,
    {
        type Break = ();

        fn visit_expr(&mut self, expression: &'ast Expr) -> ControlFlow<()> {
            match &expression.kind {
                ExprKind::Perform { effect, .. } => {
                    walk_expr(self, expression)?;
                    if let Some(effect) = (self.resolve)(expression.span, effect) {
                        self.output.insert(effect);
                    }
                }
                ExprKind::Handle {
                    computation,
                    clauses,
                } => {
                    let mut nested = Collector {
                        resolve: self.resolve,
                        resolve_call: self.resolve_call,
                        output: BTreeSet::new(),
                    };
                    nested.visit_expr(computation)?;
                    for clause in clauses.iter() {
                        if let Some(effect) = (self.resolve)(clause.span, &clause.effect) {
                            nested.output.remove(&effect);
                        }
                        self.visit_expr(&clause.body)?;
                    }
                    self.output.extend(nested.output);
                }
                ExprKind::Call(_, _) => {
                    walk_expr(self, expression)?;
                    self.output.extend((self.resolve_call)(expression));
                }
                // Nested anonymous callables have independent outward rows.
                ExprKind::Closure { .. } | ExprKind::TypedClosure { .. } => {}
                _ => walk_expr(self, expression)?,
            }
            ControlFlow::Continue(())
        }
    }

    let mut collector = Collector {
        resolve,
        resolve_call,
        output: BTreeSet::new(),
    };
    let _ = collector.visit_expr(expression);
    collector.output
}

fn referenced_active_labels(
    expression: &Expr,
    active: &BTreeMap<String, ProvisionalType>,
) -> BTreeMap<String, ProvisionalType> {
    struct Collector<'a> {
        active: &'a BTreeMap<String, ProvisionalType>,
        output: BTreeMap<String, ProvisionalType>,
    }

    impl<'ast> ExprVisitor<'ast> for Collector<'_> {
        type Break = ();

        fn visit_expr(&mut self, expression: &'ast Expr) -> ControlFlow<()> {
            match &expression.kind {
                ExprKind::LabelReference(label) => {
                    if let Some(ty) = self.active.get(label.name.as_ref()) {
                        self.output.insert(label.name.to_string(), ty.clone());
                    }
                }
                // A nested callable retains its own independently filtered
                // static-label context when it is planned.
                ExprKind::Closure { .. } | ExprKind::TypedClosure { .. } => {}
                _ => walk_expr(self, expression)?,
            }
            ControlFlow::Continue(())
        }
    }

    let mut collector = Collector {
        active,
        output: BTreeMap::new(),
    };
    let _ = collector.visit_expr(expression);
    collector.output
}

#[derive(Clone)]
enum LocalBinding {
    Type(ProvisionalType),
    Closure(ClosureRequest),
    ClosureSet(Vec<ClosureRequest>),
    DeferredFunctionItem(DeferredFunctionItem),
    RecursiveSelf(RecursiveSelf, Box<CallableShape>),
    ClosureTuple(Vec<ClosureTupleField>),
    ClosureNominal(ClosureNominalInstance),
}

#[derive(Clone)]
struct DeferredFunctionItem {
    target: String,
    site: ClosureSiteKey,
    value_site: CallSiteKey,
    params: Vec<String>,
    active_labels: BTreeMap<String, ProvisionalType>,
    provisionally_called: bool,
}

enum PlannedClosure {
    Exact(ClosureRequest),
    Late(ClosureRequest),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ContextualValidationKey {
    site: ClosureSiteKey,
    shape: CallableShape,
    captures: Vec<ClosureCapture>,
    param_env: ParamEnv,
    active_variants: BTreeMap<String, String>,
    active_labels: BTreeMap<String, ProvisionalType>,
}

enum ContextualValidation {
    InProgress(
        ProvisionalType,
        BTreeSet<crate::compiler_typeck::CallableEffect>,
    ),
    Complete(
        ProvisionalType,
        BTreeSet<crate::compiler_typeck::CallableEffect>,
    ),
}

#[cfg(test)]
thread_local! {
    static CONTEXTUAL_VALIDATION_CACHE_HITS: Cell<usize> = const { Cell::new(0) };
}

#[derive(Clone)]
struct NominalTemplate {
    params: Vec<GenericParamKey>,
    fields: BTreeMap<String, ProvisionalType>,
    variants: BTreeMap<String, Vec<ProvisionalType>>,
}

#[derive(Clone)]
struct OperationTemplate {
    effect_params: Vec<GenericParamKey>,
    operation_params: Vec<GenericParamKey>,
    params: Vec<ProvisionalType>,
    result: ProvisionalType,
}

fn discover_operation_templates(
    program: &Program,
) -> BTreeMap<(String, String), OperationTemplate> {
    program
        .effects
        .iter()
        .flat_map(|effect| {
            let effect_owner = DeclarationKey::Function(format!("$effect${}", effect.name));
            let generic_map = effect
                .generics
                .iter()
                .flat_map(|generics| &generics.params)
                .enumerate()
                .map(|(ordinal, parameter)| {
                    (
                        parameter.name.clone(),
                        GenericParamKey {
                            owner: effect_owner.clone(),
                            ordinal: ordinal as u32,
                        },
                    )
                })
                .collect::<BTreeMap<_, _>>();
            let effect_params = effect
                .generics
                .iter()
                .flat_map(|generics| &generics.params)
                .filter(|parameter| parameter.kind == GenericParamKind::Type)
                .filter_map(|parameter| generic_map.get(&parameter.name).cloned())
                .collect::<Vec<_>>();
            effect.operations.iter().filter_map(move |operation| {
                let operation_owner = DeclarationKey::Function(format!(
                    "$effect${}::{}",
                    effect.name, operation.name
                ));
                let mut operation_generic_map = generic_map.clone();
                operation_generic_map.extend(
                    operation
                        .generics
                        .iter()
                        .flat_map(|generics| &generics.params)
                        .enumerate()
                        .map(|(ordinal, parameter)| {
                            (
                                parameter.name.clone(),
                                GenericParamKey {
                                    owner: operation_owner.clone(),
                                    ordinal: ordinal as u32,
                                },
                            )
                        }),
                );
                let operation_params = operation
                    .generics
                    .iter()
                    .flat_map(|generics| &generics.params)
                    .filter(|parameter| parameter.kind == GenericParamKind::Type)
                    .filter_map(|parameter| operation_generic_map.get(&parameter.name).cloned())
                    .collect::<Vec<_>>();
                let params = operation
                    .params
                    .iter()
                    .map(|param| symbolic_type(&param.ty, &operation_generic_map, &BTreeMap::new()))
                    .collect::<Option<Vec<_>>>()?;
                let result = operation.return_type.as_ref().map_or_else(
                    || Some(ProvisionalType::Predefined("Unit".into())),
                    |ty| symbolic_type(ty, &operation_generic_map, &BTreeMap::new()),
                )?;
                Some((
                    (effect.name.clone(), operation.name.clone()),
                    OperationTemplate {
                        effect_params: effect_params.clone(),
                        operation_params,
                        params,
                        result,
                    },
                ))
            })
        })
        .collect()
}

fn nominal_params(
    name: &str,
    generics: &crate::ast::GenericParams,
) -> (Vec<GenericParamKey>, BTreeMap<String, GenericParamKey>) {
    let keys = generics
        .params
        .iter()
        .enumerate()
        .filter(|(_, parameter)| {
            matches!(
                parameter.kind,
                GenericParamKind::Type | GenericParamKind::Const(_)
            )
        })
        .map(|(ordinal, _)| GenericParamKey {
            owner: DeclarationKey::Function(format!("$nominal${name}")),
            ordinal: ordinal as u32,
        })
        .collect::<Vec<_>>();
    let by_name = generics
        .params
        .iter()
        .enumerate()
        .filter(|(_, parameter)| {
            matches!(
                parameter.kind,
                GenericParamKind::Type | GenericParamKind::Const(_)
            )
        })
        .zip(&keys)
        .map(|((_, param), key)| (param.name.clone(), key.clone()))
        .collect();
    (keys, by_name)
}

fn discover_nominal_templates(program: &Program) -> BTreeMap<String, NominalTemplate> {
    let structs = program.structs.iter().filter_map(|declaration| {
        let (params, by_name) = declaration.generics.as_ref().map_or_else(
            || (Vec::new(), BTreeMap::new()),
            |generics| nominal_params(&declaration.name, generics),
        );
        let fields = declaration
            .fields
            .iter()
            .map(|field| {
                Some((
                    field.name.clone(),
                    symbolic_type_in(program, &field.ty, &by_name, &BTreeMap::new())?,
                ))
            })
            .collect::<Option<BTreeMap<_, _>>>()?;
        Some((
            declaration.name.clone(),
            NominalTemplate {
                params,
                fields,
                variants: BTreeMap::new(),
            },
        ))
    });
    let enums = program.enums.iter().filter_map(|declaration| {
        let (params, by_name) = declaration.generics.as_ref().map_or_else(
            || (Vec::new(), BTreeMap::new()),
            |generics| nominal_params(&declaration.name, generics),
        );
        let variants = declaration
            .variants
            .iter()
            .map(|variant| {
                let fields = variant
                    .fields
                    .iter()
                    .map(|field| symbolic_type_in(program, field, &by_name, &BTreeMap::new()))
                    .collect::<Option<Vec<_>>>()?;
                Some((variant.name.clone(), fields))
            })
            .collect::<Option<BTreeMap<_, _>>>()?;
        Some((
            declaration.name.clone(),
            NominalTemplate {
                params,
                fields: BTreeMap::new(),
                variants,
            },
        ))
    });
    structs.chain(enums).collect()
}

fn implicit_function_labels(
    function: &crate::ast::Function,
    owner: &DeclarationKey,
    result: ProvisionalType,
) -> BTreeMap<String, ProvisionalType> {
    if !function.uses_implicit_label() {
        return BTreeMap::new();
    }
    let label = crate::ast::LabelSyntax {
        name: Rc::from(function.name.as_str()),
        span: crate::span::Span::new(
            function.span.start,
            function.span.start + function.name.len(),
        ),
    };
    BTreeMap::from([(
        function.name.clone(),
        label_provisional_type(owner, &label, result),
    )])
}

struct Walker<'a> {
    program: &'a Program,
    templates: &'a BTreeMap<String, FunctionTemplate>,
    nominal_templates: &'a BTreeMap<String, NominalTemplate>,
    struct_fields: &'a BTreeMap<String, BTreeMap<String, ProvisionalType>>,
    operations: &'a BTreeMap<(String, String), OperationTemplate>,
    discovery: &'a mut Discovery,
    owner: DeclarationKey,
    parent: Option<SpecializationKey>,
    locals: BTreeMap<String, LocalBinding>,
    bindings: BTreeSet<String>,
    active_variants: BTreeMap<String, String>,
    active_labels: BTreeMap<String, ProvisionalType>,
    expression_ordinals: &'a BTreeMap<usize, u32>,
    body_instance: BodyInstanceKey,
    recording: bool,
    trait_db: &'a TraitDb,
    solver_budget: &'a mut SolverBudget,
    param_env: ParamEnv,
    symbolic_validation: bool,
    active_recursive_self: Option<RecursiveSelf>,
    contextual_validations: &'a mut BTreeMap<ContextualValidationKey, ContextualValidation>,
    resolved_call_effects:
        &'a mut BTreeMap<usize, BTreeSet<crate::compiler_typeck::CallableEffect>>,
}

impl<'a> Walker<'a> {
    fn assignment_fields(
        destination: &crate::ast::AssignmentPlace,
    ) -> &[crate::ast::AssignmentField] {
        match &destination.kind {
            AssignmentPlaceKind::Local { fields, .. }
            | AssignmentPlaceKind::Dereference { fields, .. } => fields,
        }
    }

    fn assignment_active_variant(
        &self,
        destination: &crate::ast::AssignmentPlace,
    ) -> Option<String> {
        match &destination.kind {
            AssignmentPlaceKind::Local { name, .. } => {
                self.active_variants.get(name.as_ref()).cloned()
            }
            AssignmentPlaceKind::Dereference { reference, .. } => {
                let ExprKind::Variable(path) = &reference.kind else {
                    return None;
                };
                (path.len() == 1)
                    .then(|| self.active_variants.get(path[0].as_ref()).cloned())
                    .flatten()
            }
        }
    }

    fn assignment_projected_type(
        &self,
        mut ty: ProvisionalType,
        destination: &crate::ast::AssignmentPlace,
    ) -> Option<ProvisionalType> {
        let mut variant = self.assignment_active_variant(destination);
        for field in Self::assignment_fields(destination) {
            ty = match ty {
                ProvisionalType::Tuple(elements) => {
                    elements.get(field.name.parse::<usize>().ok()?)?.clone()
                }
                ProvisionalType::Nominal(instance) => {
                    let formal = variant
                        .take()
                        .and_then(|variant| {
                            self.nominal_templates
                                .get(&instance.declaration.0)?
                                .variants
                                .get(&variant)?
                                .get(field.name.parse::<usize>().ok()?)
                        })
                        .or_else(|| {
                            self.nominal_templates
                                .get(&instance.declaration.0)?
                                .fields
                                .get(field.name.as_str())
                        });
                    if let Some(formal) = formal {
                        let template = self.nominal_templates.get(&instance.declaration.0)?;
                        if template.params.len() != instance.arguments.len() {
                            return None;
                        }
                        let substitutions = template
                            .params
                            .iter()
                            .cloned()
                            .zip(
                                instance
                                    .arguments
                                    .iter()
                                    .cloned()
                                    .map(SpecializationArgument::Type),
                            )
                            .collect();
                        substitute(formal, &substitutions)?
                    } else {
                        self.struct_fields
                            .get(&instance.declaration.0)?
                            .get(field.name.as_str())?
                            .clone()
                    }
                }
                ProvisionalType::Shared(_)
                | ProvisionalType::Unique(_)
                | ProvisionalType::Predefined(_)
                | ProvisionalType::Const(_)
                | ProvisionalType::Param(_)
                | ProvisionalType::Callable(_) => return None,
            };
        }
        Some(ty)
    }

    fn assignment_expected_type(
        &mut self,
        destination: &crate::ast::AssignmentPlace,
    ) -> Option<ProvisionalType> {
        let fields = Self::assignment_fields(destination);
        let base = match &destination.kind {
            AssignmentPlaceKind::Local { name, .. } => {
                let LocalBinding::Type(ty) = self.locals.get(name.as_ref())? else {
                    return None;
                };
                match ty {
                    ProvisionalType::Unique(referent) if !fields.is_empty() => (**referent).clone(),
                    ty => ty.clone(),
                }
            }
            AssignmentPlaceKind::Dereference { reference, .. } => {
                let ProvisionalType::Unique(referent) = self.expression(reference, None)? else {
                    return None;
                };
                *referent
            }
        };
        self.assignment_projected_type(base, destination)
    }

    fn static_label_shape(&self, name: &str) -> Option<CallableShape> {
        let LocalBinding::Type(subject) = self.locals.get(name)? else {
            return None;
        };
        let payload = if let Some(payload) = label_payload_type(subject) {
            payload.clone()
        } else {
            let ProvisionalType::Param(binder) = subject else {
                return None;
            };
            let DeclarationKey::Function(owner) = &self.owner else {
                return None;
            };
            let template = self.templates.get(owner)?;
            template.marker_constraints.iter().find_map(|constraint| {
                (constraint.polarity == GoalPolarity::Positive
                    && self
                        .trait_db
                        .intrinsic_key(IntrinsicRole::Label)
                        .is_some_and(|key| key == &constraint.trait_key)
                    && constraint.subject_binder.as_ref() == Some(binder))
                .then(|| match constraint.arguments.as_slice() {
                    [GenericArg::Type(payload)] => Some(payload.clone()),
                    _ => None,
                })
                .flatten()
            })?
        };
        Some(CallableShape {
            params: vec![payload],
            result: ProvisionalType::Predefined("Never".into()),
            effects: vec![],
            effect_tail: None,
            infer_effects: false,
        })
    }

    fn source_type(&self, syntax: &TypeSyntax) -> Option<ProvisionalType> {
        let generic_map = self
            .program
            .functions
            .iter()
            .find(|function| self.owner == DeclarationKey::Function(function.name.clone()))
            .into_iter()
            .flat_map(|function| {
                function
                    .generics
                    .iter()
                    .flat_map(|generics| &generics.params)
                    .enumerate()
                    .map(|(ordinal, parameter)| {
                        (
                            parameter.name.clone(),
                            GenericParamKey {
                                owner: self.owner.clone(),
                                ordinal: ordinal as u32,
                            },
                        )
                    })
            })
            .collect::<BTreeMap<_, _>>();
        let callable_constraints = match &self.owner {
            DeclarationKey::Function(name) => self
                .templates
                .get(name)
                .map(|template| template.callable_constraints.clone())
                .unwrap_or_default(),
            DeclarationKey::Global(_) => BTreeMap::new(),
        };
        let ty = symbolic_type(syntax, &generic_map, &callable_constraints)?;
        match &self.body_instance {
            BodyInstanceKey::Specialization(key) => {
                let DeclarationKey::Function(name) = &key.template else {
                    return Some(ty);
                };
                let template = self.templates.get(name)?;
                substitute(&ty, &substitutions_for_key(template, key))
            }
            _ => Some(ty),
        }
    }

    fn generic_call_binding_expected(
        &self,
        callee: &Expr,
        arguments: &[Expr],
        binding: &str,
    ) -> Option<ProvisionalType> {
        self.generic_call_binding_expected_with_result(callee, arguments, binding, None)
    }

    fn generic_call_binding_expected_with_result(
        &self,
        callee: &Expr,
        arguments: &[Expr],
        binding: &str,
        expected_result: Option<&ProvisionalType>,
    ) -> Option<ProvisionalType> {
        let ExprKind::Variable(path) = &callee.kind else {
            return None;
        };
        let [name] = path.as_ref() else {
            return None;
        };
        let template = self.templates.get(name.as_ref())?;
        if arguments.len() != template.params.len() {
            return None;
        }
        let named_binding = |expression: &Expr| {
            let expression = match &expression.kind {
                ExprKind::Move(value) => value.as_ref(),
                _ => expression,
            };
            matches!(&expression.kind, ExprKind::Variable(path)
                if path.len() == 1 && path[0].as_ref() == binding)
        };
        let mutable = template
            .generic_params
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut substitutions = BTreeMap::new();
        if let Some(expected_result) = expected_result {
            let mut trial = substitutions.clone();
            if unify_inference(&template.result, expected_result, &mutable, &mut trial) {
                substitutions = trial;
            }
        }
        for (argument, formal) in arguments.iter().zip(&template.params) {
            if let Some((actual, false)) = self.obvious_argument_type(argument) {
                let mut trial = substitutions.clone();
                if unify_inference(formal, &actual, &mutable, &mut trial) {
                    substitutions = trial;
                }
            }
        }
        let mut candidates = arguments
            .iter()
            .zip(&template.params)
            .filter_map(|(argument, formal)| {
                let formal = substitute(formal, &substitutions).unwrap_or_else(|| formal.clone());
                if !ground(&formal) {
                    return None;
                }
                let argument = match &argument.kind {
                    ExprKind::Move(value) => value.as_ref(),
                    _ => argument,
                };
                match (&argument.kind, &formal) {
                    (
                        ExprKind::Unary {
                            op: UnaryOp::BorrowShared,
                            operand,
                        },
                        ProvisionalType::Shared(referent),
                    )
                    | (
                        ExprKind::Unary {
                            op: UnaryOp::BorrowUnique,
                            operand,
                        },
                        ProvisionalType::Unique(referent),
                    ) if named_binding(operand) => Some((**referent).clone()),
                    (_, formal) if named_binding(argument) => Some(formal.clone()),
                    (ExprKind::Call(nested_callee, nested_arguments), formal) => self
                        .generic_call_binding_expected_with_result(
                            nested_callee,
                            nested_arguments,
                            binding,
                            Some(formal),
                        ),
                    _ => None,
                }
            })
            .collect::<BTreeSet<_>>();
        (candidates.len() == 1).then(|| candidates.pop_first().unwrap())
    }

    fn moved_binding_name(expression: &Expr) -> Option<&str> {
        let expression = match &expression.kind {
            ExprKind::Move(value) => value,
            _ => expression,
        };
        let ExprKind::Variable(path) = &expression.kind else {
            return None;
        };
        (path.len() == 1).then_some(path[0].as_ref())
    }

    fn pattern_binds_name(pattern: &crate::ast::Pattern, binding: &str) -> bool {
        match &pattern.kind {
            PatternKind::Binding(name) => name == binding,
            PatternKind::Variant { fields, .. } => fields
                .iter()
                .any(|field| Self::pattern_binds_name(field, binding)),
            PatternKind::Tuple { elements, .. } => elements
                .iter()
                .any(|element| Self::pattern_binds_name(element, binding)),
            PatternKind::Struct { fields, .. } => fields
                .iter()
                .any(|field| Self::pattern_binds_name(&field.pattern, binding)),
            PatternKind::Wildcard
            | PatternKind::Unit
            | PatternKind::Int(_)
            | PatternKind::Float(_)
            | PatternKind::String(_)
            | PatternKind::Char(_)
            | PatternKind::Byte(_) => false,
        }
    }

    fn expression_mentions_live_name(expression: &Expr, live: &BTreeSet<String>) -> bool {
        if Self::moved_binding_name(expression).is_some_and(|name| live.contains(name)) {
            return true;
        }
        match &expression.kind {
            ExprKind::Binary { lhs, rhs, .. } => {
                Self::expression_mentions_live_name(lhs, live)
                    || Self::expression_mentions_live_name(rhs, live)
            }
            ExprKind::Move(operand)
            | ExprKind::Unary { operand, .. }
            | ExprKind::Field(operand, _) => Self::expression_mentions_live_name(operand, live),
            _ => false,
        }
    }

    fn collect_statement_expectations(
        &self,
        statements: &[Stmt],
        inherited: &BTreeSet<String>,
        candidates: &mut BTreeSet<ProvisionalType>,
        structural_initializer: Option<&Expr>,
        block_expected: Option<&ProvisionalType>,
    ) {
        let mut live = inherited.clone();
        for (index, statement) in statements.iter().enumerate() {
            if candidates.len() > 1 {
                return;
            }
            let is_tail = index + 1 == statements.len();
            let value = match statement {
                Stmt::Let { value, .. }
                | Stmt::Deconstruct { value, .. }
                | Stmt::Expr(value)
                | Stmt::Assign { value, .. } => value,
            };
            if is_tail && let (Some(expected), Stmt::Expr(result)) = (block_expected, statement) {
                if Self::moved_binding_name(result).is_some_and(|name| live.contains(name)) {
                    candidates.insert(expected.clone());
                }
                if let (ExprKind::Struct { name, fields }, ProvisionalType::Nominal(instance)) =
                    (&result.kind, expected)
                    && instance.declaration.0 == name.as_ref()
                    && let Some(template) = self.nominal_templates.get(name.as_ref())
                    && template.params.len() == instance.arguments.len()
                {
                    let substitutions = template
                        .params
                        .iter()
                        .cloned()
                        .zip(
                            instance
                                .arguments
                                .iter()
                                .cloned()
                                .map(SpecializationArgument::Type),
                        )
                        .collect::<BTreeMap<_, _>>();
                    for (field, value) in fields.iter() {
                        if Self::expression_mentions_live_name(value, &live)
                            && let Some(formal) = template.fields.get(field)
                            && let Some(expected) = substitute(formal, &substitutions)
                        {
                            candidates.insert(expected);
                        }
                    }
                }
            }
            if let Stmt::Assign { destination, .. } = statement
                && let AssignmentPlaceKind::Dereference { reference, .. } = &destination.kind
            {
                self.collect_expression_expectations(
                    reference,
                    &live,
                    candidates,
                    structural_initializer,
                );
            }
            self.collect_expression_expectations(value, &live, candidates, structural_initializer);
            match statement {
                Stmt::Let { name, value, .. } => {
                    if let Some(source) =
                        Self::moved_binding_name(value).filter(|source| live.contains(*source))
                    {
                        let source = source.to_owned();
                        live.remove(&source);
                        live.insert(name.clone());
                    } else {
                        live.remove(name);
                    }
                }
                Stmt::Deconstruct { fields, .. } => {
                    for binding in fields.iter().filter_map(|field| field.binding.as_ref()) {
                        live.remove(binding);
                    }
                }
                Stmt::Assign { .. } | Stmt::Expr(_) => {}
            }
        }
    }

    fn collect_expression_expectations(
        &self,
        expression: &Expr,
        live: &BTreeSet<String>,
        candidates: &mut BTreeSet<ProvisionalType>,
        structural_initializer: Option<&Expr>,
    ) {
        // Candidate sets only grow. Once two distinct ground expectations
        // exist, this binding is ambiguous and no deeper scan can restore a
        // unique answer.
        if candidates.len() > 1 {
            return;
        }
        if let ExprKind::Call(callee, arguments) = &expression.kind {
            for binding in live {
                if let Some(expected) =
                    self.generic_call_binding_expected(callee, arguments, binding)
                {
                    candidates.insert(expected);
                }
            }
        }
        match &expression.kind {
            ExprKind::Closure { params, body } => {
                let retained = live
                    .iter()
                    .filter(|name| !params.iter().any(|param| param.as_ref() == name.as_str()))
                    .cloned()
                    .collect::<BTreeSet<_>>();
                self.collect_expression_expectations(
                    body,
                    &retained,
                    candidates,
                    structural_initializer,
                );
            }
            ExprKind::TypedClosure { params, body, .. } => {
                let retained = live
                    .iter()
                    .filter(|name| !params.iter().any(|param| param.name == name.as_str()))
                    .cloned()
                    .collect::<BTreeSet<_>>();
                self.collect_expression_expectations(
                    body,
                    &retained,
                    candidates,
                    structural_initializer,
                );
            }
            ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => self
                .collect_statement_expectations(
                    statements,
                    live,
                    candidates,
                    structural_initializer,
                    None,
                ),
            ExprKind::Call(callee, arguments) => {
                if let ExprKind::Variable(else_path) = &callee.kind
                    && else_path.len() == 1
                    && else_path[0].as_ref() == "else"
                    && let [if_expression, negative] = arguments.as_slice()
                    && let ExprKind::Call(if_callee, if_arguments) = &if_expression.kind
                    && let ExprKind::Variable(if_path) = &if_callee.kind
                    && if_path.len() == 1
                    && if_path[0].as_ref() == "if"
                    && let [condition, positive] = if_arguments.as_slice()
                    && let ExprKind::Is { subject, pattern } = &condition.kind
                {
                    self.collect_expression_expectations(
                        condition,
                        live,
                        candidates,
                        structural_initializer,
                    );
                    if Self::moved_binding_name(subject).is_some_and(|name| live.contains(name))
                        && let Some(initializer) = structural_initializer
                        && let Some(expected) = self.structural_pattern_initializer_expected(
                            initializer,
                            pattern,
                            positive,
                        )
                    {
                        candidates.insert(expected);
                    }
                    let positive_live = live
                        .iter()
                        .filter(|name| !Self::pattern_binds_name(pattern, name))
                        .cloned()
                        .collect::<BTreeSet<_>>();
                    self.collect_expression_expectations(
                        positive,
                        &positive_live,
                        candidates,
                        structural_initializer,
                    );
                    self.collect_expression_expectations(
                        negative,
                        live,
                        candidates,
                        structural_initializer,
                    );
                } else {
                    self.collect_expression_expectations(
                        callee,
                        live,
                        candidates,
                        structural_initializer,
                    );
                    for argument in arguments.iter() {
                        self.collect_expression_expectations(
                            argument,
                            live,
                            candidates,
                            structural_initializer,
                        );
                    }
                }
            }
            ExprKind::Handle {
                computation,
                clauses,
            } => {
                self.collect_expression_expectations(
                    computation,
                    live,
                    candidates,
                    structural_initializer,
                );
                for clause in clauses.iter() {
                    let retained = live
                        .iter()
                        .filter(|name| {
                            clause.resumption.as_deref() != Some(name.as_str())
                                && !clause
                                    .patterns
                                    .iter()
                                    .any(|pattern| Self::pattern_binds_name(pattern, name))
                        })
                        .cloned()
                        .collect::<BTreeSet<_>>();
                    self.collect_expression_expectations(
                        &clause.body,
                        &retained,
                        candidates,
                        structural_initializer,
                    );
                }
            }
            ExprKind::List(values) | ExprKind::Tuple(values) => {
                for value in values.iter() {
                    self.collect_expression_expectations(
                        value,
                        live,
                        candidates,
                        structural_initializer,
                    );
                }
            }
            ExprKind::Struct { name, fields } => {
                let exact_fields = self.nominal_templates.get(name.as_ref());
                for (field, value) in fields.iter() {
                    // A later monomorphic struct construction is an exact
                    // bidirectional use of a preceding inferred binding.
                    // Recover that field context before recursively walking
                    // the value so generic constructors such as `None` retain
                    // their complete nominal arguments inside an inlined
                    // recursive control block. Generic-dependent fields stay
                    // excluded until an enclosing nominal instance supplies
                    // substitutions; a ground field is independent of them.
                    if Self::expression_mentions_live_name(value, live)
                        && let Some(expected) = exact_fields
                            .and_then(|template| template.fields.get(field))
                            .filter(|expected| ground(expected))
                    {
                        candidates.insert(expected.clone());
                    }
                    self.collect_expression_expectations(
                        value,
                        live,
                        candidates,
                        structural_initializer,
                    );
                }
            }
            ExprKind::Field(subject, _)
            | ExprKind::Move(subject)
            | ExprKind::Unary {
                operand: subject, ..
            }
            | ExprKind::LabelDestination { body: subject, .. }
            | ExprKind::Cancel {
                resumption: subject,
            }
            | ExprKind::Is {
                subject,
                pattern: _,
            } => self.collect_expression_expectations(
                subject,
                live,
                candidates,
                structural_initializer,
            ),
            ExprKind::Binary { lhs, rhs, .. } => {
                if Self::expression_mentions_live_name(lhs, live)
                    && let Some((ty, defaulted)) = self.obvious_argument_type(rhs)
                    && !defaulted
                    && ground(&ty)
                {
                    candidates.insert(ty);
                }
                if Self::expression_mentions_live_name(rhs, live)
                    && let Some((ty, defaulted)) = self.obvious_argument_type(lhs)
                    && !defaulted
                    && ground(&ty)
                {
                    candidates.insert(ty);
                }
                self.collect_expression_expectations(lhs, live, candidates, structural_initializer);
                self.collect_expression_expectations(rhs, live, candidates, structural_initializer);
            }
            ExprKind::Perform { args, .. } => {
                for argument in args.iter() {
                    self.collect_expression_expectations(
                        argument,
                        live,
                        candidates,
                        structural_initializer,
                    );
                }
            }
            ExprKind::Resume { resumption, value } | ExprKind::TailResume { resumption, value } => {
                self.collect_expression_expectations(
                    resumption,
                    live,
                    candidates,
                    structural_initializer,
                );
                if let Some(value) = value {
                    self.collect_expression_expectations(
                        value,
                        live,
                        candidates,
                        structural_initializer,
                    );
                }
            }
            ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::String(_)
            | ExprKind::Char(_)
            | ExprKind::Byte(_)
            | ExprKind::ByteString(_)
            | ExprKind::Variable(_)
            | ExprKind::LabelReference(_) => {}
        }
    }

    fn expression_binding_expected(
        &self,
        expression: &Expr,
        binding: &str,
    ) -> Option<ProvisionalType> {
        let live = BTreeSet::from([binding.to_owned()]);
        let mut candidates = BTreeSet::new();
        self.collect_expression_expectations(expression, &live, &mut candidates, None);
        (candidates.len() == 1).then(|| candidates.pop_first().unwrap())
    }

    fn structural_pattern_initializer_expected(
        &self,
        initializer: &Expr,
        pattern: &crate::ast::Pattern,
        positive: &Expr,
    ) -> Option<ProvisionalType> {
        let PatternKind::Variant { fields, .. } = &pattern.kind else {
            return None;
        };
        let payload_binding = fields.iter().find_map(|field| {
            let PatternKind::Binding(binding) = &field.kind else {
                return None;
            };
            Some(binding.as_str())
        })?;
        let payload = self.expression_binding_expected(positive, payload_binding)?;
        self.structural_pattern_initializer_expected_for_payload(
            initializer,
            pattern,
            payload_binding,
            &payload,
        )
    }

    fn structural_pattern_initializer_expected_for_payload(
        &self,
        initializer: &Expr,
        pattern: &crate::ast::Pattern,
        payload_binding: &str,
        payload: &ProvisionalType,
    ) -> Option<ProvisionalType> {
        let PatternKind::Variant {
            path, fields, rest, ..
        } = &pattern.kind
        else {
            return None;
        };
        let [owner, variant] = path.as_slice() else {
            return None;
        };
        let payload_position = fields.iter().position(
            |field| matches!(&field.kind, PatternKind::Binding(binding) if binding == payload_binding),
        )?;
        let pattern_field_count = fields.len();
        let initializer = match &initializer.kind {
            ExprKind::Move(value) => value.as_ref(),
            _ => initializer,
        };
        let ExprKind::Call(callee, arguments) = &initializer.kind else {
            return None;
        };
        let ExprKind::Variable(callee) = &callee.kind else {
            return None;
        };
        let [callee] = callee.as_ref() else {
            return None;
        };
        let producer = self.templates.get(callee.as_ref())?;
        if arguments.len() != producer.params.len() {
            return None;
        }
        let ProvisionalType::Nominal(produced) = &producer.result else {
            return None;
        };
        if produced.declaration.0 != *owner {
            return None;
        }
        let nominal = self.nominal_templates.get(owner.as_str())?;
        if nominal.params.len() != produced.arguments.len() {
            return None;
        }
        let fields = nominal.variants.get(variant.as_str())?;
        let payload_index =
            pattern_field_index(*rest, payload_position, pattern_field_count, fields.len());
        let field = fields.get(payload_index)?;
        let nominal_substitutions = nominal
            .params
            .iter()
            .cloned()
            .zip(
                produced
                    .arguments
                    .iter()
                    .cloned()
                    .map(SpecializationArgument::Type),
            )
            .collect::<BTreeMap<_, _>>();
        let produced_payload = substitute(field, &nominal_substitutions)?;
        let mutable = producer
            .generic_params
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut substitutions = BTreeMap::new();
        if !unify_inference(&produced_payload, payload, &mutable, &mut substitutions) {
            return None;
        }
        let expected = substitute(&producer.result, &substitutions)?;
        ground(&expected).then_some(expected)
    }

    fn completion_binding(expression: &Expr) -> Option<&str> {
        match &expression.kind {
            ExprKind::Move(value) => Self::completion_binding(value),
            ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                let Stmt::Expr(value) = statements.last()? else {
                    return None;
                };
                Self::completion_binding(value)
            }
            _ => Self::moved_binding_name(expression),
        }
    }

    /// Handles are structurally lowered before specialization discovery into
    /// a temporary initializer followed by a nested `if`/`else` pattern-test
    /// chain. Recover the initializer's complete generic nominal result from
    /// an enclosing expected type when a matching branch returns its payload.
    fn lowered_handle_initializer_expected(
        &self,
        expression: &Expr,
        initializer: &Expr,
        temporary: &str,
        expected: &ProvisionalType,
    ) -> Option<ProvisionalType> {
        let mut candidates = BTreeSet::new();
        fn visit(
            walker: &Walker<'_>,
            expression: &Expr,
            initializer: &Expr,
            temporary: &str,
            expected: &ProvisionalType,
            candidates: &mut BTreeSet<ProvisionalType>,
        ) {
            match &expression.kind {
                ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                    for statement in statements.iter() {
                        if let Stmt::Expr(value) = statement {
                            visit(walker, value, initializer, temporary, expected, candidates);
                        }
                    }
                }
                ExprKind::Call(callee, arguments)
                    if matches!(&callee.kind, ExprKind::Variable(path)
                        if path.len() == 1 && path[0].as_ref() == "else")
                        && arguments.len() == 2 =>
                {
                    let positive_if = &arguments[0];
                    if let ExprKind::Call(if_callee, if_arguments) = &positive_if.kind
                        && matches!(&if_callee.kind, ExprKind::Variable(path)
                            if path.len() == 1 && path[0].as_ref() == "if")
                        && let [condition, positive] = if_arguments.as_slice()
                        && let ExprKind::Is { subject, pattern } = &condition.kind
                        && Walker::moved_binding_name(subject).is_some_and(|name| name == temporary)
                        && let Some(returned) = Walker::completion_binding(positive)
                        && Walker::pattern_binds_name(pattern, returned)
                        && let Some(candidate) = walker
                            .structural_pattern_initializer_expected_for_payload(
                                initializer,
                                pattern,
                                returned,
                                expected,
                            )
                    {
                        candidates.insert(candidate);
                    }
                    visit(
                        walker,
                        &arguments[1],
                        initializer,
                        temporary,
                        expected,
                        candidates,
                    );
                }
                _ => {}
            }
        }
        visit(
            self,
            expression,
            initializer,
            temporary,
            expected,
            &mut candidates,
        );
        (candidates.len() == 1).then(|| candidates.pop_first().unwrap())
    }

    fn block_binding_expected_type(
        &self,
        binding: &str,
        initializer: &Expr,
        remaining: &[Stmt],
        block_expected: Option<&ProvisionalType>,
    ) -> Option<ProvisionalType> {
        let live = BTreeSet::from([binding.to_owned()]);
        let mut candidates = BTreeSet::new();
        if let Some(block_expected) = block_expected {
            for statement in remaining {
                if let Stmt::Expr(expression) = statement
                    && let Some(expected) = self.lowered_handle_initializer_expected(
                        expression,
                        initializer,
                        binding,
                        block_expected,
                    )
                {
                    candidates.insert(expected);
                }
            }
        }
        self.collect_statement_expectations(
            remaining,
            &live,
            &mut candidates,
            Some(initializer),
            block_expected,
        );
        (candidates.len() == 1).then(|| candidates.pop_first().unwrap())
    }
    fn may_use_bidirectional_result_fallback(&self, expression: &Expr) -> bool {
        let mut expression = expression;
        loop {
            expression = match &expression.kind {
                ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                    match statements.last() {
                        Some(Stmt::Expr(value)) => value,
                        _ => return false,
                    }
                }
                ExprKind::Move(value) => value,
                _ => break,
            };
        }
        match &expression.kind {
            ExprKind::Variable(path) if path.len() == 1 => self
                .program
                .globals
                .iter()
                .any(|global| global.name == path[0].as_ref()),
            ExprKind::Call(callee, _) => {
                match &callee.kind {
                    // Static label application is bottom-typed. Its ordinary
                    // expression walk remains valueless so captured labels
                    // keep their mandatory direct-control classification, but
                    // a refinement join may adopt its exact sibling context.
                    ExprKind::LabelReference(_) => true,
                    ExprKind::Variable(path) => {
                        path.len() == 2
                            && self
                                .program
                                .traits
                                .iter()
                                .any(|declaration| declaration.name == path[0].as_ref())
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn symbolic_callable_parameter(&self, name: &str) -> Option<GenericParamKey> {
        if !self.symbolic_validation {
            return None;
        }
        let DeclarationKey::Function(owner) = &self.owner else {
            return None;
        };
        let template = self.templates.get(owner)?;
        let function = self
            .program
            .functions
            .iter()
            .find(|function| function.name == *owner)?;
        function
            .params
            .iter()
            .position(|parameter| parameter.name == name)
            .and_then(|index| template.parameter_binders[index].clone())
    }

    fn symbolically_known_type(&self, ty: &ProvisionalType) -> bool {
        !provisional_signature_type_any(ty, &mut |ty| {
            matches!(
                ty,
                ProvisionalType::Nominal(instance)
                    if !instance.declaration.0.starts_with(crate::compiler_typeck::LABEL_TYPE_PREFIX)
                        && !self.nominal_templates.contains_key(instance.declaration.0.as_str())
            )
        })
    }

    fn effect_instance(
        &self,
        site: crate::span::Span,
        fallback: &str,
    ) -> Option<crate::compiler_typeck::CallableEffect> {
        let Some(syntax) = self.program.effect_path(site) else {
            return Some(crate::compiler_typeck::CallableEffect {
                declaration: crate::compiler_typeck::ProtocolKey(fallback.to_owned()),
                arguments: vec![],
            });
        };
        let (name, arguments) = match &syntax.kind {
            TypeSyntaxKind::Application {
                constructor,
                arguments,
                ..
            } => (constructor.simple_name()?, arguments.as_slice()),
            _ => (syntax.simple_name()?, &[][..]),
        };
        let generic_map = self
            .program
            .functions
            .iter()
            .find(|function| self.owner == DeclarationKey::Function(function.name.clone()))
            .into_iter()
            .flat_map(|function| {
                function
                    .generics
                    .iter()
                    .flat_map(|generics| &generics.params)
                    .enumerate()
                    .map(|(ordinal, parameter)| {
                        (
                            parameter.name.clone(),
                            GenericParamKey {
                                owner: self.owner.clone(),
                                ordinal: ordinal as u32,
                            },
                        )
                    })
            })
            .collect::<BTreeMap<_, _>>();
        let mut arguments = arguments
            .iter()
            .map(|argument| symbolic_type(argument, &generic_map, &BTreeMap::new()))
            .collect::<Option<Vec<_>>>()?;
        fn canonicalize_module_nominals(
            ty: &mut ProvisionalType,
            templates: &BTreeMap<String, NominalTemplate>,
        ) {
            match ty {
                ProvisionalType::Nominal(instance) => {
                    for argument in &mut instance.arguments {
                        canonicalize_module_nominals(argument, templates);
                    }
                    if !templates.contains_key(instance.declaration.0.as_str()) {
                        let suffix = format!(":{}", instance.declaration.0);
                        let mut candidates =
                            templates.keys().filter(|name| name.ends_with(&suffix));
                        if let Some(candidate) = candidates.next()
                            && candidates.next().is_none()
                        {
                            instance.declaration.0 = candidate.clone();
                        }
                    }
                }
                ProvisionalType::Tuple(elements) => {
                    for element in elements {
                        canonicalize_module_nominals(element, templates);
                    }
                }
                ProvisionalType::Shared(referent) | ProvisionalType::Unique(referent) => {
                    canonicalize_module_nominals(referent, templates)
                }
                ProvisionalType::Predefined(_)
                | ProvisionalType::Const(_)
                | ProvisionalType::Param(_)
                | ProvisionalType::Callable(_) => {}
            }
        }
        for argument in &mut arguments {
            canonicalize_module_nominals(argument, &self.nominal_templates);
        }
        if let BodyInstanceKey::Specialization(key) = &self.body_instance
            && let DeclarationKey::Function(template_name) = &key.template
            && let Some(template) = self.templates.get(template_name)
        {
            let substitutions = substitutions_for_key(template, key);
            arguments = arguments
                .iter()
                .map(|argument| substitute(argument, &substitutions))
                .collect::<Option<Vec<_>>>()?;
        }
        Some(crate::compiler_typeck::CallableEffect {
            declaration: crate::compiler_typeck::ProtocolKey(name.to_owned()),
            arguments,
        })
    }

    fn record_call_effects(
        &mut self,
        source: &Expr,
        effects: impl IntoIterator<Item = crate::compiler_typeck::CallableEffect>,
    ) {
        self.resolved_call_effects.insert(
            std::ptr::from_ref(source) as usize,
            effects.into_iter().collect(),
        );
    }

    fn resolved_effects_at(
        &self,
        source: &Expr,
    ) -> BTreeSet<crate::compiler_typeck::CallableEffect> {
        self.resolved_call_effects
            .get(&(std::ptr::from_ref(source) as usize))
            .cloned()
            .unwrap_or_default()
    }

    fn operation_at(
        &self,
        site: crate::span::Span,
        effect: &str,
        operation: &str,
    ) -> Option<OperationTemplate> {
        let instance = self.effect_instance(site, effect)?;
        let template = self
            .operations
            .get(&(instance.declaration.0, operation.to_owned()))?;
        if template.effect_params.len() != instance.arguments.len() {
            return None;
        }
        let substitutions = template
            .effect_params
            .iter()
            .cloned()
            .zip(
                instance
                    .arguments
                    .iter()
                    .cloned()
                    .map(SpecializationArgument::Type),
            )
            .collect::<BTreeMap<_, _>>();
        Some(OperationTemplate {
            effect_params: vec![],
            operation_params: template.operation_params.clone(),
            params: template
                .params
                .iter()
                .map(|param| substitute(param, &substitutions))
                .collect::<Option<Vec<_>>>()?,
            result: substitute(&template.result, &substitutions)?,
        })
    }

    fn operation_at_for_args(
        &self,
        site: crate::span::Span,
        effect: &str,
        operation: &str,
        args: &[Expr],
    ) -> Option<OperationTemplate> {
        let shape = self.operation_at(site, effect, operation)?;
        let mutable = shape.operation_params.iter().cloned().collect();
        let mut substitutions = BTreeMap::new();
        for (argument, formal) in args.iter().zip(&shape.params) {
            if let Some((actual, defaulted)) = self.obvious_argument_type(argument)
                && !defaulted
                && !unify_inference(formal, &actual, &mutable, &mut substitutions)
            {
                return None;
            }
        }
        Some(OperationTemplate {
            effect_params: vec![],
            operation_params: vec![],
            params: shape
                .params
                .iter()
                .map(|param| substitute(param, &substitutions))
                .collect::<Option<Vec<_>>>()?,
            result: substitute(&shape.result, &substitutions)?,
        })
    }

    /// Return only types that an expression can synthesize without committing
    /// discovery state or consulting an expected type. This small prepass lets
    /// later call arguments constrain earlier context-dependent constructors.
    fn obvious_argument_type(&self, expression: &Expr) -> Option<(ProvisionalType, bool)> {
        match &expression.kind {
            ExprKind::Unit => Some((ProvisionalType::Predefined("Unit".into()), false)),
            // An unconstrained integer defaults to i64, but a concrete type
            // synthesized by any other argument must get the first chance to
            // provide its context.
            ExprKind::Int(_) => Some((ProvisionalType::Predefined("i64".into()), true)),
            // An unconstrained float defaults to f64 with the same one-chance
            // deferral to concrete context as integers.
            ExprKind::Float(_) => Some((ProvisionalType::Predefined("f64".into()), true)),
            ExprKind::String(_) => Some((ProvisionalType::Predefined("Text".into()), false)),
            ExprKind::Char(_) => Some((ProvisionalType::Predefined("Char".into()), false)),
            ExprKind::Byte(_) => Some((ProvisionalType::Predefined("u8".into()), false)),
            ExprKind::ByteString(_) => Some((ProvisionalType::Predefined("Bytes".into()), false)),
            ExprKind::Move(operand) => self.obvious_argument_type(operand),
            ExprKind::LabelReference(label) => self
                .active_labels
                .get(label.name.as_ref())
                .cloned()
                .map(|ty| (ty, false)),
            ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                let Stmt::Expr(tail) = statements.last()? else {
                    return None;
                };
                self.obvious_argument_type(tail)
            }
            ExprKind::Tuple(values) => {
                let values = values
                    .iter()
                    .map(|value| self.obvious_argument_type(value))
                    .collect::<Option<Vec<_>>>()?;
                let defaulted = values.iter().all(|(_, defaulted)| *defaulted);
                Some((
                    ProvisionalType::Tuple(values.into_iter().map(|(ty, _)| ty).collect()),
                    defaulted,
                ))
            }
            // These unary forms preserve or structurally wrap an already
            // synthesizable operand type. In particular, an exact borrowed
            // local must constrain `T` before a sibling numeric literal is
            // allowed to install its i64/f64 default.
            ExprKind::Unary {
                op: UnaryOp::BorrowShared,
                operand,
            } => self
                .obvious_argument_type(operand)
                .map(|(ty, defaulted)| (ProvisionalType::shared(ty), defaulted)),
            ExprKind::Unary {
                op: UnaryOp::BorrowUnique,
                operand,
            } => self
                .obvious_argument_type(operand)
                .map(|(ty, defaulted)| (ProvisionalType::unique(ty), defaulted)),
            ExprKind::Unary {
                op: UnaryOp::Dereference,
                operand,
            } => self
                .obvious_argument_type(operand)
                .and_then(|(ty, defaulted)| match ty {
                    ProvisionalType::Shared(referent) | ProvisionalType::Unique(referent) => {
                        Some((*referent, defaulted))
                    }
                    _ => None,
                }),
            ExprKind::Unary {
                op: UnaryOp::Negate,
                operand,
            } => self.obvious_argument_type(operand),
            ExprKind::Variable(path) if path.len() == 1 => {
                match self.locals.get(path[0].as_ref()) {
                    Some(LocalBinding::Type(ty)) => Some((ty.clone(), false)),
                    Some(LocalBinding::ClosureNominal(instance)) => Some((
                        ProvisionalType::Nominal(NominalInstanceKey {
                            declaration: NominalKey(instance.declaration.clone()),
                            arguments: instance
                                .arguments
                                .iter()
                                .map(|argument| match argument {
                                    ClosureTupleField::Type(ty) => ty.clone(),
                                    ClosureTupleField::Closure(closure) => {
                                        ProvisionalType::Callable(closure.shape.clone())
                                    }
                                    ClosureTupleField::ClosureSet(closures) => {
                                        ProvisionalType::Callable(closures[0].shape.clone())
                                    }
                                })
                                .collect(),
                        }),
                        false,
                    )),
                    Some(
                        LocalBinding::Closure(_)
                        | LocalBinding::ClosureSet(_)
                        | LocalBinding::DeferredFunctionItem(_)
                        | LocalBinding::ClosureTuple(_)
                        | LocalBinding::RecursiveSelf(_, _),
                    )
                    | None => None,
                }
            }
            ExprKind::Field(subject, field) => {
                let (subject, defaulted) = self.obvious_argument_type(subject)?;
                let subject = match subject {
                    ProvisionalType::Shared(referent) | ProvisionalType::Unique(referent) => {
                        *referent
                    }
                    subject => subject,
                };
                if let ProvisionalType::Tuple(elements) = &subject
                    && let Ok(index) = field.parse::<usize>()
                {
                    return elements.get(index).cloned().map(|ty| (ty, defaulted));
                }
                let ProvisionalType::Nominal(instance) = subject else {
                    return None;
                };
                if let Some(template) = self.nominal_templates.get(&instance.declaration.0)
                    && let Some(formal) = template.fields.get(field)
                    && template.params.len() == instance.arguments.len()
                {
                    let substitutions = template
                        .params
                        .iter()
                        .cloned()
                        .zip(
                            instance
                                .arguments
                                .iter()
                                .cloned()
                                .map(SpecializationArgument::Type),
                        )
                        .collect();
                    return substitute(formal, &substitutions).map(|ty| (ty, defaulted));
                }
                self.struct_fields
                    .get(&instance.declaration.0)
                    .and_then(|fields| fields.get(field.as_str()))
                    .cloned()
                    .map(|ty| (ty, defaulted))
            }
            ExprKind::Call(callee, arguments) => {
                let ExprKind::Variable(path) = &callee.kind else {
                    return None;
                };
                let [name] = path.as_ref() else {
                    return None;
                };
                let Some(template) = self.templates.get(name.as_ref()) else {
                    let function = self
                        .program
                        .functions
                        .iter()
                        .find(|function| function.name == name.as_ref())?;
                    if arguments.len() != function.params.len()
                        || function.generics.as_ref().is_some_and(|generics| {
                            generics.params.iter().any(|parameter| {
                                matches!(
                                    parameter.kind,
                                    GenericParamKind::Type | GenericParamKind::Const(_)
                                )
                            })
                        })
                    {
                        return None;
                    }
                    let result = function.return_type.as_ref().map_or_else(
                        || Some(ProvisionalType::Predefined("Unit".into())),
                        |result| symbolic_type(result, &BTreeMap::new(), &BTreeMap::new()),
                    )?;
                    return ground(&result).then_some((result, false));
                };
                if arguments.len() != template.params.len() {
                    return None;
                }
                if template.generic_params.is_empty() {
                    let result = template.result.clone();
                    return ground(&result).then_some((result, false));
                }
                let argument_types = arguments
                    .iter()
                    .map(|argument| self.obvious_argument_type(argument))
                    .collect::<Vec<_>>();
                let mutable = template
                    .generic_params
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<_>>();
                let mut substitutions = BTreeMap::new();
                for defaulting in [false, true] {
                    for (actual, formal) in argument_types.iter().zip(&template.params) {
                        let Some((actual, is_default)) = actual else {
                            continue;
                        };
                        if *is_default != defaulting {
                            continue;
                        }
                        let mut trial = substitutions.clone();
                        if unify_inference(formal, &actual, &mutable, &mut trial) {
                            substitutions = trial;
                        }
                    }
                }
                let result = substitute(&template.result, &substitutions)?;
                ground(&result).then_some((result, false))
            }
            ExprKind::Binary { lhs, rhs, op }
                if !matches!(
                    op,
                    BinaryOp::Eq
                        | BinaryOp::NotEq
                        | BinaryOp::Lt
                        | BinaryOp::LtEq
                        | BinaryOp::Gt
                        | BinaryOp::GtEq
                ) =>
            {
                match (
                    self.obvious_argument_type(lhs),
                    self.obvious_argument_type(rhs),
                ) {
                    (Some((left, left_default)), Some((right, right_default))) => {
                        if left == right {
                            Some((left, left_default && right_default))
                        } else if left_default && !right_default {
                            Some((right, false))
                        } else if right_default && !left_default {
                            Some((left, false))
                        } else {
                            None
                        }
                    }
                    (Some(value), None) | (None, Some(value)) => Some(value),
                    (None, None) => None,
                }
            }
            _ => None,
        }
    }

    fn error(&mut self, message: impl Into<String>) {
        self.discovery.errors.insert(DiscoveryError {
            owner: self.owner.clone(),
            message: message.into(),
        });
    }

    fn bind_handler_pattern(&mut self, pattern: &crate::ast::Pattern, ty: &ProvisionalType) {
        match &pattern.kind {
            PatternKind::Binding(name) => {
                self.locals
                    .insert(name.clone(), LocalBinding::Type(ty.clone()));
                self.bindings.insert(name.clone());
            }
            PatternKind::Variant { path, fields, rest } if path.len() == 2 => {
                let ProvisionalType::Nominal(instance) = ty else {
                    return;
                };
                if instance.declaration.0 != path[0] {
                    return;
                }
                let Some(template) = self.nominal_templates.get(&instance.declaration.0) else {
                    return;
                };
                let Some(formals) = template.variants.get(&path[1]) else {
                    return;
                };
                if template.params.len() != instance.arguments.len() || fields.len() > formals.len()
                {
                    return;
                }
                let substitutions = template
                    .params
                    .iter()
                    .cloned()
                    .zip(
                        instance
                            .arguments
                            .iter()
                            .cloned()
                            .map(SpecializationArgument::Type),
                    )
                    .collect::<BTreeMap<_, _>>();
                let resolved = formals
                    .iter()
                    .map(|formal| substitute(formal, &substitutions))
                    .collect::<Option<Vec<_>>>();
                if let Some(resolved) = resolved {
                    for (position, field) in fields.iter().enumerate() {
                        let index =
                            pattern_field_index(*rest, position, fields.len(), resolved.len());
                        self.bind_handler_pattern(field, &resolved[index]);
                    }
                }
            }
            PatternKind::Tuple { elements, rest } => {
                let ProvisionalType::Tuple(element_types) = ty else {
                    return;
                };
                if elements.len() > element_types.len() {
                    return;
                }
                for (position, element) in elements.iter().enumerate() {
                    let index =
                        pattern_field_index(*rest, position, elements.len(), element_types.len());
                    self.bind_handler_pattern(element, &element_types[index].clone());
                }
            }
            PatternKind::Struct { name, fields, .. } => {
                let ProvisionalType::Nominal(instance) = ty else {
                    return;
                };
                if instance.declaration.0 != *name {
                    return;
                }
                let Some(template) = self.nominal_templates.get(&instance.declaration.0) else {
                    return;
                };
                if template.params.len() != instance.arguments.len() {
                    return;
                }
                let substitutions = template
                    .params
                    .iter()
                    .cloned()
                    .zip(
                        instance
                            .arguments
                            .iter()
                            .cloned()
                            .map(SpecializationArgument::Type),
                    )
                    .collect::<BTreeMap<_, _>>();
                let resolved = fields
                    .iter()
                    .filter_map(|field| {
                        template
                            .fields
                            .get(&field.field)
                            .and_then(|formal| substitute(formal, &substitutions))
                            .map(|ty| (&field.pattern, ty))
                    })
                    .collect::<Vec<_>>();
                for (pattern, ty) in resolved {
                    self.bind_handler_pattern(pattern, &ty);
                }
            }
            PatternKind::Wildcard
            | PatternKind::Unit
            | PatternKind::Int(_)
            | PatternKind::Float(_)
            | PatternKind::String(_)
            | PatternKind::Char(_)
            | PatternKind::Byte(_)
            | PatternKind::Variant { .. } => {}
        }
    }

    /// `Use` is compiler-derived evidence rather than an ordinary impl-table
    /// marker.  Specialization can decide the frozen predefined principals
    /// without accepting a source-forged implementation.
    fn principal_use_evidence(
        &self,
        subject: &ProvisionalType,
        visiting: &mut BTreeSet<ProvisionalType>,
    ) -> Option<(u32, Option<u32>)> {
        if !visiting.insert(subject.clone()) {
            return None;
        }
        let principal = match subject {
            ProvisionalType::Predefined(name) => predefined_runtime_use_interval(name)?,
            ProvisionalType::Nominal(instance) => {
                // These library-facing scalar spellings are sealed primitive
                // leaves even though type lowering represents them as
                // zero-argument nominal keys.  Keep generic `Use<Q>`
                // specialization consistent with final ownership elaboration:
                // primitive scalar values are structurally unrestricted and
                // do not require a source-forgeable principal `Use` impl.
                if instance.arguments.is_empty()
                    && let Some(principal) =
                        predefined_runtime_use_interval(instance.declaration.0.as_str())
                {
                    visiting.remove(subject);
                    return Some(principal);
                }
                if instance.declaration.0 == "Array" {
                    let [element] = instance.arguments.as_slice() else {
                        return None;
                    };
                    let element = self.principal_use_evidence(element, visiting)?;
                    let principal = (u32::from(element.0 > 0), Some(1));
                    visiting.remove(subject);
                    return Some(principal);
                }
                let mut selected = None;
                for declaration in &self.program.uses {
                    let bindings = if let Some(generics) = &declaration.generics {
                        let TypeSyntaxKind::Application {
                            constructor,
                            arguments,
                            ..
                        } = &declaration.target.kind
                        else {
                            continue;
                        };
                        if constructor.simple_name() != Some(instance.declaration.0.as_str())
                            || arguments.len() != instance.arguments.len()
                        {
                            continue;
                        }
                        let names = arguments
                            .iter()
                            .map(TypeSyntax::simple_name)
                            .collect::<Option<Vec<_>>>()?;
                        let generic_names = generics
                            .params
                            .iter()
                            .filter(|parameter| parameter.kind == GenericParamKind::Type)
                            .map(|parameter| parameter.name.as_str())
                            .collect::<Vec<_>>();
                        if names != generic_names {
                            continue;
                        }
                        generic_names
                            .into_iter()
                            .zip(instance.arguments.iter().cloned())
                            .collect::<BTreeMap<_, _>>()
                    } else {
                        if declaration.where_clause.is_some()
                            || symbolic_type(
                                &declaration.target,
                                &BTreeMap::new(),
                                &BTreeMap::new(),
                            )
                            .as_ref()
                                != Some(subject)
                        {
                            continue;
                        }
                        BTreeMap::new()
                    };

                    let mut conditions_hold = true;
                    if let Some(where_clause) = &declaration.where_clause {
                        let generic_keys = bindings
                            .keys()
                            .enumerate()
                            .map(|(ordinal, name)| {
                                (
                                    (*name).to_owned(),
                                    GenericParamKey {
                                        owner: DeclarationKey::Function(
                                            "$intrinsic_use_evidence".into(),
                                        ),
                                        ordinal: ordinal as u32,
                                    },
                                )
                            })
                            .collect::<BTreeMap<_, _>>();
                        let substitutions = generic_keys
                            .iter()
                            .filter_map(|(name, key)| {
                                bindings
                                    .get(name.as_str())
                                    .cloned()
                                    .map(|ty| (key.clone(), SpecializationArgument::Type(ty)))
                            })
                            .collect::<BTreeMap<_, _>>();
                        for goal in &where_clause.goals {
                            let is_use = goal.polarity == GoalPolarity::Positive
                                && goal.relation.path.len() == 1
                                && self.trait_db.trait_key(&goal.relation.path[0].name)
                                    == self.trait_db.intrinsic_key(IntrinsicRole::Use)
                                && goal.relation.bindings.is_empty();
                            let [GoalArgument::Quantity(quantity)] =
                                goal.relation.arguments.as_slice()
                            else {
                                conditions_hold = false;
                                break;
                            };
                            let Some(goal_subject) =
                                symbolic_type(&goal.subject, &generic_keys, &BTreeMap::new())
                                    .and_then(|ty| substitute(&ty, &substitutions))
                            else {
                                conditions_hold = false;
                                break;
                            };
                            let Some(required) = Some((
                                u32::try_from(quantity.lower).ok(),
                                quantity.upper.map(u32::try_from).transpose().ok(),
                            ))
                            .and_then(|(lower, upper)| Some((lower?, upper?))) else {
                                conditions_hold = false;
                                break;
                            };
                            let Some(actual) = self.principal_use_evidence(&goal_subject, visiting)
                            else {
                                conditions_hold = false;
                                break;
                            };
                            let contains = actual.0 <= required.0
                                && match (actual.1, required.1) {
                                    (None, _) => true,
                                    (Some(_), None) => false,
                                    (Some(actual), Some(required)) => actual >= required,
                                };
                            if !is_use || !contains {
                                conditions_hold = false;
                                break;
                            }
                        }
                    }
                    if conditions_hold {
                        selected = Some((
                            u32::try_from(declaration.quantity.lower).ok()?,
                            declaration
                                .quantity
                                .upper
                                .map(u32::try_from)
                                .transpose()
                                .ok()?,
                        ));
                        break;
                    }
                }
                if let Some(selected) = selected {
                    selected
                } else {
                    // Generic specialization must be able to discharge the
                    // same structural principal that final type elaboration
                    // derives. In particular, nested shapes such as
                    // `Vec<Result<(K, V), ()>>` have no source-written `Use`
                    // impl for each intermediate nominal; their principal is
                    // the intersection of the instantiated payload fields.
                    let template = self
                        .nominal_templates
                        .get(instance.declaration.0.as_str())?;
                    if template.params.len() != instance.arguments.len() {
                        return None;
                    }
                    let substitutions = template
                        .params
                        .iter()
                        .cloned()
                        .zip(
                            instance
                                .arguments
                                .iter()
                                .cloned()
                                .map(SpecializationArgument::Type),
                        )
                        .collect::<BTreeMap<_, _>>();
                    let children = template
                        .fields
                        .values()
                        .chain(template.variants.values().flatten());
                    let mut lower = 0;
                    let mut upper = None;
                    for child in children {
                        let child = substitute(child, &substitutions)?;
                        let child = self.principal_use_evidence(&child, visiting)?;
                        lower = lower.max(child.0);
                        upper = match (upper, child.1) {
                            (None, right) => right,
                            (left, None) => left,
                            (Some(left), Some(right)) => Some(left.min(right)),
                        };
                    }
                    (lower, upper)
                }
            }
            ProvisionalType::Shared(_) => (0, None),
            ProvisionalType::Unique(_) => (0, Some(1)),
            ProvisionalType::Tuple(elements) => {
                let mut lower = 0;
                let mut upper = None;
                for element in elements {
                    let element = self.principal_use_evidence(element, visiting)?;
                    lower = lower.max(element.0);
                    upper = match (upper, element.1) {
                        (None, right) => right,
                        (left, None) => left,
                        (Some(left), Some(right)) => Some(left.min(right)),
                    };
                }
                (lower, upper)
            }
            ProvisionalType::Const(_)
            | ProvisionalType::Callable(_)
            | ProvisionalType::Param(_) => return None,
        };
        visiting.remove(subject);
        Some(principal)
    }

    fn intrinsic_use_evidence(
        &mut self,
        constraint: &MarkerConstraint,
        subject: &ProvisionalType,
        arguments: &[GenericArg],
        exact_argument: Option<&SpecializationArgument>,
    ) -> Option<bool> {
        if constraint.polarity != GoalPolarity::Positive
            || self.trait_db.intrinsic_key(IntrinsicRole::Use) != Some(&constraint.trait_key)
        {
            return None;
        }
        let [GenericArg::Const(ConstValue::Quantity { lower, upper })] = arguments else {
            return Some(false);
        };
        let principal = match exact_argument {
            Some(SpecializationArgument::Closure(_, shape, captures, _, _, _))
                if subject == &ProvisionalType::Callable(shape.clone()) =>
            {
                let mut environment_zero_use = true;
                let mut environment_copy = captures
                    .iter()
                    .all(|capture| capture.mode != CaptureMode::Move);
                for capture in captures {
                    let interval =
                        self.principal_use_evidence(&capture.ty, &mut BTreeSet::new())?;
                    environment_zero_use &= interval.0 == 0;
                    environment_copy &= interval.1.is_none_or(|upper| upper > 1);
                }
                let receiver_mode = captures
                    .iter()
                    .map(|capture| capture.mode)
                    .max()
                    .unwrap_or(CaptureMode::Observe);
                (
                    u32::from(!environment_zero_use),
                    (receiver_mode != CaptureMode::Observe || !environment_copy).then_some(1),
                )
            }
            _ => match self.principal_use_evidence(subject, &mut BTreeSet::new()) {
                Some(principal) => principal,
                None => {
                    return self.structural_use_contains(
                        subject,
                        *lower,
                        *upper,
                        &mut BTreeSet::new(),
                    );
                }
            },
        };
        let lower_contained = principal.0 <= *lower;
        let upper_contained = match (principal.1, *upper) {
            (None, _) => true,
            (Some(_), None) => false,
            (Some(principal), Some(requested)) => principal >= requested,
        };
        Some(lower_contained && upper_contained)
    }

    /// Proves structural `Use<Q>` without inventing a principal interval for
    /// a symbolic type parameter. Generic aggregate payloads may be justified
    /// by the caller's lexical `ParamEnv`; the final ground specialization
    /// still recomputes and validates the concrete principal independently.
    fn structural_use_contains(
        &mut self,
        subject: &ProvisionalType,
        lower: u32,
        upper: Option<u32>,
        visiting: &mut BTreeSet<ProvisionalType>,
    ) -> Option<bool> {
        if !visiting.insert(subject.clone()) {
            return None;
        }
        let result = match subject {
            ProvisionalType::Param(_) => {
                let trait_key = self.trait_db.intrinsic_key(IntrinsicRole::Use)?;
                self.param_env
                    .use_quantity_contains(trait_key, subject, lower, upper)
                    || matches!(
                        self.trait_db
                            .solve_with_key_detailed_with_budget(
                                self.solver_budget,
                                &self.param_env,
                                GoalPolarity::Positive,
                                trait_key,
                                subject,
                                &[GenericArg::Const(ConstValue::Quantity { lower, upper })],
                                &[],
                            )
                            .result,
                        SolveResult::Proven
                    )
            }
            ProvisionalType::Tuple(elements) => elements.iter().all(|element| {
                self.structural_use_contains(element, lower, upper, visiting) == Some(true)
            }),
            ProvisionalType::Nominal(instance) => {
                if instance.declaration.0 == "Array" {
                    let [element] = instance.arguments.as_slice() else {
                        return None;
                    };
                    upper.is_some_and(|upper| upper <= 1)
                        && (lower > 0
                            || self.structural_use_contains(element, 0, Some(0), visiting)
                                == Some(true))
                } else {
                    if instance.arguments.is_empty() {
                        return None;
                    }
                    let template = self
                        .nominal_templates
                        .get(instance.declaration.0.as_str())?;
                    if template.params.len() != instance.arguments.len() {
                        return None;
                    }
                    let substitutions = template
                        .params
                        .iter()
                        .cloned()
                        .zip(
                            instance
                                .arguments
                                .iter()
                                .cloned()
                                .map(SpecializationArgument::Type),
                        )
                        .collect::<BTreeMap<_, _>>();
                    template
                        .fields
                        .values()
                        .chain(template.variants.values().flatten())
                        .all(|child| {
                            substitute(child, &substitutions).is_some_and(|child| {
                                self.structural_use_contains(&child, lower, upper, visiting)
                                    == Some(true)
                            })
                        })
                }
            }
            _ => self
                .principal_use_evidence(subject, &mut BTreeSet::new())
                .is_some_and(|principal| {
                    principal.0 <= lower
                        && match (principal.1, upper) {
                            (None, _) => true,
                            (Some(_), None) => false,
                            (Some(principal), Some(requested)) => principal >= requested,
                        }
                }),
        };
        visiting.remove(subject);
        Some(result)
    }

    fn exact_constraint_argument<'b>(
        subject: &ProvisionalType,
        substitutions: &'b BTreeMap<GenericParamKey, SpecializationArgument>,
    ) -> Option<&'b SpecializationArgument> {
        let mut current = subject;
        let mut visiting = BTreeSet::new();
        loop {
            let ProvisionalType::Param(key) = current else {
                return None;
            };
            if !visiting.insert(key.clone()) {
                return None;
            }
            match substitutions.get(key)? {
                argument @ SpecializationArgument::Closure(..) => return Some(argument),
                SpecializationArgument::Type(ty) => current = ty,
                SpecializationArgument::EffectRow(_) => return None,
            }
        }
    }

    fn closure_site(&mut self, expression: &Expr) -> Option<ClosureSiteKey> {
        let ordinal = self
            .expression_ordinals
            .get(&(std::ptr::from_ref(expression) as usize))
            .copied();
        let Some(ordinal) = ordinal else {
            self.error("closure expression is outside its declaration syntax tree");
            return None;
        };
        Some(ClosureSiteKey {
            owner: self.owner.clone(),
            ordinal,
        })
    }

    fn call_site(&mut self, expression: &Expr) -> Option<CallSiteKey> {
        let expression_ordinal = self
            .expression_ordinals
            .get(&(std::ptr::from_ref(expression) as usize))
            .copied();
        let Some(expression_ordinal) = expression_ordinal else {
            self.error("call expression is outside its declaration syntax tree");
            return None;
        };
        Some(CallSiteKey {
            body: self.body_instance.clone(),
            expression_ordinal,
        })
    }

    fn has_non_well_founded_request_growth(&self, candidate: &SpecializationKey) -> bool {
        let Some(parent) = &self.parent else {
            return false;
        };
        let mut pending = vec![parent.clone()];
        let mut visited = BTreeSet::new();
        while let Some(ancestor) = pending.pop() {
            if !visited.insert(ancestor.clone()) {
                continue;
            }
            if ancestor.template == candidate.template
                && ancestor != *candidate
                && ancestor.arguments.len() == candidate.arguments.len()
                && ancestor
                    .arguments
                    .iter()
                    .zip(&candidate.arguments)
                    .all(|(left, right)| specialization_argument_embeds(left, right))
            {
                return true;
            }
            pending.extend(
                self.discovery
                    .graph
                    .edges
                    .iter()
                    .filter(|(_, child)| child == &ancestor)
                    .map(|(parent, _)| parent.clone()),
            );
        }
        false
    }

    fn deferred_function_item(&mut self, expression: &Expr) -> Option<DeferredFunctionItem> {
        let ExprKind::Closure { params, body } = &expression.kind else {
            return None;
        };
        let ExprKind::Call(callee, arguments) = &body.kind else {
            return None;
        };
        let ExprKind::Variable(target) = &callee.kind else {
            return None;
        };
        let [target] = target.as_ref() else {
            return None;
        };
        let template = self.templates.get(target.as_ref())?;
        if template.generic_params.is_empty() || arguments.len() != params.len() {
            return None;
        }
        let forwards_parameters = arguments
            .iter()
            .zip(params.iter())
            .all(|(argument, param)| {
                matches!(&argument.kind, ExprKind::Variable(path)
                if path.len() == 1 && path[0].as_ref() == param.as_ref())
            });
        if !forwards_parameters {
            return None;
        }
        Some(DeferredFunctionItem {
            target: target.to_string(),
            site: self.closure_site(expression)?,
            value_site: self.call_site(expression)?,
            params: params.iter().map(ToString::to_string).collect(),
            active_labels: referenced_active_labels(body, &self.active_labels),
            provisionally_called: false,
        })
    }

    fn specialized_function_effects(
        &mut self,
        target: &str,
        substitutions: &BTreeMap<GenericParamKey, SpecializationArgument>,
    ) -> Option<Vec<crate::compiler_typeck::CallableEffect>> {
        let function = self
            .program
            .functions
            .iter()
            .find(|function| function.name == target)?;
        let Some(row) = &function.outward_effects else {
            return Some(Vec::new());
        };
        let owner = DeclarationKey::Function(target.to_owned());
        let generic_map = function
            .generics
            .iter()
            .flat_map(|generics| &generics.params)
            .enumerate()
            .map(|(ordinal, parameter)| {
                (
                    parameter.name.clone(),
                    GenericParamKey {
                        owner: owner.clone(),
                        ordinal: ordinal as u32,
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut effects = BTreeSet::new();
        for member in &row.effects {
            if !expand_effect_member(
                member,
                self.program,
                &generic_map,
                &mut BTreeSet::new(),
                &mut effects,
            ) {
                self.error(format!(
                    "generic function item `{target}` names an unknown outward effect"
                ));
                return None;
            }
        }
        let mut effects = effects
            .into_iter()
            .map(|effect| {
                Some(crate::compiler_typeck::CallableEffect {
                    declaration: effect.declaration,
                    arguments: effect
                        .arguments
                        .iter()
                        .map(|argument| substitute(argument, substitutions))
                        .collect::<Option<Vec<_>>>()?,
                })
            })
            .collect::<Option<BTreeSet<_>>>()?;
        if let Some(tail) = &row.tail {
            let Some(key) = generic_map.get(tail.name.as_str()) else {
                self.error(format!(
                    "function `{target}` has an unknown outward effect-row tail"
                ));
                return None;
            };
            let Some(SpecializationArgument::EffectRow(tail_effects)) = substitutions.get(key)
            else {
                self.error(format!(
                    "call to `{target}` leaves its outward effect-row tail unresolved"
                ));
                return None;
            };
            effects.extend(tail_effects.iter().cloned());
        }
        Some(effects.into_iter().collect())
    }

    fn resolve_deferred_function_item(
        &mut self,
        source: &Expr,
        name: &str,
        item: DeferredFunctionItem,
        args: &[Expr],
        expected: Option<&ProvisionalType>,
        requested_receiver_mode: Option<u32>,
    ) -> Option<ProvisionalType> {
        if !self.recording {
            let result = self.direct_call(source, &item.target, args, expected, None);
            let mut item = item;
            item.provisionally_called = true;
            self.locals
                .insert(name.to_owned(), LocalBinding::DeferredFunctionItem(item));
            return result;
        }
        let call_site = self.call_site(source)?;
        let result = self.direct_call(source, &item.target, args, expected, None)?;
        let key = self.discovery.graph.direct_calls.remove(&call_site)?;
        let template = self.templates.get(&item.target)?.clone();
        let substitutions = substitutions_for_key(&template, &key);
        let params = template
            .params
            .iter()
            .map(|parameter| substitute(parameter, &substitutions))
            .collect::<Option<Vec<_>>>()?;
        if params.len() != item.params.len() {
            self.error(format!(
                "generic function item `{}` resolved to an incompatible arity",
                item.target
            ));
            return None;
        }
        let effects = self.specialized_function_effects(&item.target, &substitutions)?;
        let shape = Box::new(CallableShape {
            params,
            result: result.clone(),
            effects,
            effect_tail: None,
            infer_effects: false,
        });
        let request = ClosureRequest {
            site: item.site,
            shape,
            captures: Vec::new(),
            param_env: self.param_env.clone(),
            active_labels: item.active_labels,
            static_captures: BTreeMap::new(),
        };
        self.discovery
            .graph
            .closure_bodies
            .insert(request.clone(), ClosureBodyKind::Explicit);
        self.discovery
            .graph
            .closure_values
            .insert(item.value_site, request.clone());
        self.discovery
            .graph
            .indirect_calls
            .insert(call_site.clone(), request.clone());
        self.discovery
            .graph
            .callable_calls
            .insert(call_site.clone(), request.clone());
        if let Some(mode) = requested_receiver_mode {
            self.discovery
                .graph
                .indirect_call_modes
                .insert(call_site, mode);
        }
        self.locals
            .insert(name.to_owned(), LocalBinding::Closure(request));
        Some(result)
    }

    fn contextual_closure(
        &mut self,
        expression: &Expr,
        expected: &CallableShape,
        substitutions: &mut BTreeMap<GenericParamKey, SpecializationArgument>,
    ) -> Option<PlannedClosure> {
        let site = self.closure_site(expression)?;
        let (params, body, body_kind): (Vec<String>, &Expr, ClosureBodyKind) = match &expression
            .kind
        {
            ExprKind::Closure { params, body } if params.len() == expected.params.len() => (
                params.iter().map(ToString::to_string).collect(),
                body,
                ClosureBodyKind::Explicit,
            ),
            ExprKind::TypedClosure { params, body, .. }
                if params.len() == expected.params.len() =>
            {
                (
                    params.iter().map(|param| param.name.clone()).collect(),
                    body,
                    ClosureBodyKind::Explicit,
                )
            }
            ExprKind::TypedClosure { params, .. } => {
                self.error(format!(
                        "typed closure declares {} parameter(s), but its contextual callable shape expects {}",
                        params.len(),
                        expected.params.len()
                    ));
                return None;
            }
            ExprKind::Block(_) | ExprKind::ContextBlock(_) if expected.params.is_empty() => {
                (vec![], expression, ClosureBodyKind::ContextualBlock)
            }
            _ => {
                self.error("callable argument is not a contextually matching closure");
                return None;
            }
        };
        // A typed anonymous callable carries its own explicit signature; each
        // declared annotation must agree with the contextual callable shape.
        let declared = if matches!(expression.kind, ExprKind::TypedClosure { .. }) {
            let declared = self.typed_closure_shape(expression)?;
            for (index, (expected_param, declared_param)) in
                expected.params.iter().zip(&declared.params).enumerate()
            {
                if !bind(expected_param, declared_param, substitutions) {
                    self.error(format!(
                        "typed closure parameter {index} does not match its contextual callable shape"
                    ));
                    return None;
                }
            }
            if !bind(&expected.result, &declared.result, substitutions) {
                self.error(
                    "typed closure result type does not match its contextual callable shape",
                );
                return None;
            }
            Some(declared)
        } else {
            None
        };
        let outer = self.bindings.clone();
        let mut captures = Vec::new();
        let mut static_captures = BTreeMap::new();
        let mut late = false;
        for (name, mut mode) in captured_outer_uses(body, &outer, &params) {
            if let Some(LocalBinding::RecursiveSelf(recursive_self, _)) = self.locals.get(&name)
                && self.active_recursive_self.as_ref() == Some(recursive_self)
            {
                // Recursive calls reuse the current receiver identity. The
                // binding is planning evidence, never an environment field.
                continue;
            }
            let ty = match self.locals.get(&name) {
                Some(LocalBinding::Type(ty)) => ty.clone(),
                Some(LocalBinding::Closure(request)) => {
                    // A control wrapper commonly builds a short-lived closure
                    // around one of its own Fn-bound parameters. The captured
                    // callable identity is static during late control
                    // inlining, but discovery still has to validate the
                    // nested closure before Core beta-reduces it. Retain the
                    // callable shape as late evidence instead of demanding an
                    // ordinary runtime local.
                    static_captures.insert(name, vec![request.clone()]);
                    continue;
                }
                Some(LocalBinding::ClosureSet(requests))
                    if requests.first().is_some_and(|first| {
                        requests.iter().all(|request| request.shape == first.shape)
                    }) =>
                {
                    static_captures.insert(name, requests.clone());
                    continue;
                }
                _ => {
                    self.error(format!(
                        "captureful closure specialization: closure capture `{name}` is not an ordinary typed local or one statically known callable"
                    ));
                    return None;
                }
            };
            let ty = substitute(&ty, substitutions).unwrap_or(ty);
            if mode == CaptureMode::Observe
                && matches!(ty, ProvisionalType::Unique(_))
                && passed_as_unique_call_argument(body, &name, self.templates)
            {
                mode = CaptureMode::Mutate;
            }
            if contains_late_callable(&ty) {
                // Handler-site resumptions receive their exact runtime
                // identity only during Core lowering. Retain the complete
                // closure plan, including callable-bearing aggregates, but do
                // not put it in an ordinary emitted specialization key.
                late = true;
                captures.push(ClosureCapture { name, ty, mode });
                continue;
            }
            if !ground(&ty) {
                // A closure nested in a generic specialization cannot acquire
                // its concrete environment shape until the enclosing body is
                // instantiated. Retain it as a late plan; Core lowering will
                // substitute the active specialization key before allocating
                // the callable environment.
                late = true;
                captures.push(ClosureCapture { name, ty, mode });
                continue;
            }
            if !supported_capture_shape(&ty) {
                self.error(format!(
                    "captureful closure specialization: closure capture `{name}` must have a ground shape without reference or callable values"
                ));
                return None;
            }
            captures.push(ClosureCapture { name, ty, mode });
        }
        let recursive_local = self.active_recursive_self.as_ref().and_then(|active| {
            self.locals
                .get(&active.binding)
                .and_then(|binding| match binding {
                    LocalBinding::RecursiveSelf(recursive_self, shape)
                        if recursive_self == active =>
                    {
                        Some((recursive_self.clone(), shape.clone()))
                    }
                    _ => None,
                })
        });
        // A contextual block can be encountered first while validating every
        // enclosing block and then once more as each planned closure body is
        // discovered. For a closed, non-recursive environment those walks are
        // identical and have no recording side effects. Canonicalize that
        // validation context so a shared suffix is type-walked only once.
        let validation_key = (!self.symbolic_validation
            && recursive_local.is_none()
            && captures.iter().all(|capture| ground(&capture.ty))
            && self.active_labels.values().all(ground))
        .then(|| {
            Some(ContextualValidationKey {
                site: site.clone(),
                shape: CallableShape {
                    params: expected
                        .params
                        .iter()
                        .map(|param| substitute(param, substitutions))
                        .collect::<Option<Vec<_>>>()?,
                    result: substitute(&expected.result, substitutions)?,
                    effects: expected
                        .effects
                        .iter()
                        .map(|effect| {
                            Some(crate::compiler_typeck::CallableEffect {
                                declaration: effect.declaration.clone(),
                                arguments: effect
                                    .arguments
                                    .iter()
                                    .map(|argument| substitute(argument, substitutions))
                                    .collect::<Option<Vec<_>>>()?,
                            })
                        })
                        .collect::<Option<Vec<_>>>()?,
                    effect_tail: expected.effect_tail.clone(),
                    infer_effects: expected.infer_effects,
                },
                captures: captures.clone(),
                param_env: self.param_env.clone(),
                active_variants: self.active_variants.clone(),
                active_labels: self.active_labels.clone(),
            })
        })
        .flatten()
        .filter(|key| {
            key.shape.params.iter().all(ground)
                && ground(&key.shape.result)
                && key
                    .shape
                    .effects
                    .iter()
                    .flat_map(|effect| &effect.arguments)
                    .all(ground)
        });
        let saved = std::mem::take(&mut self.locals);
        let saved_bindings = std::mem::take(&mut self.bindings);
        if let Some((recursive_self, shape)) = &recursive_local {
            self.locals.insert(
                recursive_self.binding.clone(),
                LocalBinding::RecursiveSelf(recursive_self.clone(), shape.clone()),
            );
            self.bindings.insert(recursive_self.binding.clone());
        }
        for capture in &captures {
            self.locals
                .insert(capture.name.clone(), LocalBinding::Type(capture.ty.clone()));
            self.bindings.insert(capture.name.clone());
        }
        for (name, requests) in &static_captures {
            let binding = if requests.len() == 1 {
                LocalBinding::Closure(requests[0].clone())
            } else {
                LocalBinding::ClosureSet(requests.clone())
            };
            self.locals.insert(name.clone(), binding);
            self.bindings.insert(name.clone());
        }
        for (name, ty) in params.iter().zip(&expected.params) {
            let ty = substitute(ty, substitutions).unwrap_or_else(|| ty.clone());
            self.locals.insert(name.clone(), LocalBinding::Type(ty));
            self.bindings.insert(name.clone());
        }
        let saved_recording = self.recording;
        let saved_symbolic_validation = self.symbolic_validation;
        // Static control callbacks may close over another exact callback.
        // Their callable identity is intentionally unavailable as a runtime
        // local because Core lowering beta-reduces both layers. Validate the
        // nested body from its exact callable shape and defer identity checks
        // to that control-inlining step.
        self.symbolic_validation |= !static_captures.is_empty()
            || captures
                .iter()
                .any(|capture| contains_late_callable(&capture.ty));
        self.recording = false;
        let expected_result =
            substitute(&expected.result, substitutions).unwrap_or_else(|| expected.result.clone());
        let cached_result = validation_key.as_ref().and_then(|key| {
            self.contextual_validations
                .get(key)
                .map(|validation| match validation {
                    ContextualValidation::InProgress(expected, effects) => {
                        (expected.clone(), effects.clone())
                    }
                    ContextualValidation::Complete(expected, effects) => {
                        (expected.clone(), effects.clone())
                    }
                })
        });
        #[cfg(test)]
        if cached_result.is_some() {
            CONTEXTUAL_VALIDATION_CACHE_HITS.with(|hits| hits.set(hits.get() + 1));
        }
        let (actual_result, inferred_effects) = cached_result
            .map(|(result, effects)| (Some(result), effects))
            .unwrap_or_else(|| {
                if let Some(key) = &validation_key {
                    // Recursive contextual validation may observe this entry
                    // before call resolution completes. Preserve the direct
                    // syntactic performs while withholding any stale
                    // pointer-keyed call facts.
                    let direct_performs = direct_closure_effects(
                        body,
                        &|site, effect| self.effect_instance(site, effect),
                        &|_| BTreeSet::new(),
                    );
                    self.contextual_validations.insert(
                        key.clone(),
                        ContextualValidation::InProgress(expected_result.clone(), direct_performs),
                    );
                }
                let result = self.expression(body, Some(&expected_result));
                let effects = result
                    .as_ref()
                    .map(|_| {
                        direct_closure_effects(
                            body,
                            &|site, effect| self.effect_instance(site, effect),
                            &|call| self.resolved_effects_at(call),
                        )
                    })
                    .unwrap_or_default();
                if let Some(key) = &validation_key {
                    if let Some(result) = &result {
                        self.contextual_validations.insert(
                            key.clone(),
                            ContextualValidation::Complete(result.clone(), effects.clone()),
                        );
                    } else {
                        self.contextual_validations.remove(key);
                    }
                }
                (result, effects)
            });
        self.recording = saved_recording;
        self.symbolic_validation = saved_symbolic_validation;
        self.locals = saved;
        self.bindings = saved_bindings;
        let actual_result = actual_result?;
        let diverges =
            matches!(actual_result, ProvisionalType::Predefined(ref name) if name == "Never");
        if !late && !diverges && !bind(&expected.result, &actual_result, substitutions) {
            self.error(if declared.is_some() {
                "typed closure body result does not unify with its declared result type"
            } else {
                "closure body result does not unify with its callable Output"
            });
            return None;
        }
        let actual_effects = if let Some(declared) = &declared {
            let declared_effects = declared.effects.iter().cloned().collect::<BTreeSet<_>>();
            if !inferred_effects.is_subset(&declared_effects) {
                let missing = inferred_effects
                    .difference(&declared_effects)
                    .map(|effect| effect.declaration.0.as_str())
                    .collect::<Vec<_>>()
                    .join(", ");
                self.error(format!(
                    "typed closure body performs effect(s) absent from its declared effect row: {missing}"
                ));
                return None;
            }
            declared_effects
        } else {
            inferred_effects
        };
        let expected_effects = expected
            .effects
            .iter()
            .map(|effect| {
                Some(crate::compiler_typeck::CallableEffect {
                    declaration: effect.declaration.clone(),
                    arguments: effect
                        .arguments
                        .iter()
                        .map(|argument| substitute(argument, substitutions))
                        .collect::<Option<Vec<_>>>()?,
                })
            })
            .collect::<Option<BTreeSet<_>>>()?;
        if !expected.infer_effects
            && expected.effect_tail.is_none()
            && !actual_effects.is_subset(&expected_effects)
        {
            let missing = actual_effects
                .difference(&expected_effects)
                .map(|effect| effect.declaration.0.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            self.error(format!(
                "closure body performs effect(s) absent from its exact Effects row: {missing}"
            ));
            return None;
        }
        let effects = if let Some(tail) = &expected.effect_tail {
            let residual = actual_effects
                .difference(&expected_effects)
                .cloned()
                .collect::<Vec<_>>();
            match substitutions.get(tail) {
                Some(SpecializationArgument::EffectRow(existing)) if existing == &residual => {}
                Some(SpecializationArgument::EffectRow(_)) => {
                    self.error(
                        "effect-row variable has conflicting residual rows in this call island",
                    );
                    return None;
                }
                Some(_) => {
                    self.error("effect-row variable was also used as a type or callable binder");
                    return None;
                }
                None => {
                    substitutions.insert(tail.clone(), SpecializationArgument::EffectRow(residual));
                }
            }
            expected_effects.union(&actual_effects).cloned().collect()
        } else if expected.infer_effects {
            actual_effects.into_iter().collect()
        } else {
            expected.effects.clone()
        };
        let shape = CallableShape {
            params: expected
                .params
                .iter()
                .map(|param| substitute(param, substitutions))
                .collect::<Option<Vec<_>>>()?,
            result: substitute(&expected.result, substitutions)?,
            effects: effects
                .iter()
                .map(|effect| {
                    Some(crate::compiler_typeck::CallableEffect {
                        declaration: effect.declaration.clone(),
                        arguments: effect
                            .arguments
                            .iter()
                            .map(|argument| substitute(argument, substitutions))
                            .collect::<Option<Vec<_>>>()?,
                    })
                })
                .collect::<Option<Vec<_>>>()?,
            effect_tail: None,
            infer_effects: false,
        };
        if (!shape.params.iter().all(ground) || !ground(&shape.result)) && !self.symbolic_validation
        {
            self.error("closure callable shape remains symbolic after inference");
            return None;
        }
        let request = ClosureRequest {
            site,
            shape: Box::new(shape),
            captures,
            param_env: self.param_env.clone(),
            active_labels: referenced_active_labels(body, &self.active_labels),
            static_captures,
        };
        let late = late || contains_late_callable_captures(&request);
        if let Some(recursive_self) = &self.active_recursive_self {
            let validation_body = self.body_instance.clone();
            let calls = self
                .discovery
                .graph
                .recursive_self_calls
                .iter()
                .filter(|(site, call)| {
                    site.body == validation_body && &call.recursive_self == recursive_self
                })
                .map(|(site, call)| (site.clone(), call.clone()))
                .collect::<Vec<_>>();
            for (site, call) in calls {
                self.discovery.graph.recursive_self_calls.remove(&site);
                self.discovery.graph.recursive_self_calls.insert(
                    CallSiteKey {
                        body: BodyInstanceKey::Closure(request.clone()),
                        expression_ordinal: site.expression_ordinal,
                    },
                    call,
                );
            }
        }
        if self.recording {
            if late {
                let call_site = self.call_site(expression)?;
                let plan = LateClosurePlan {
                    request: request.clone(),
                    body_kind,
                    recursive_self: self.active_recursive_self.clone(),
                };
                self.discovery
                    .graph
                    .static_closure_bodies
                    .insert(call_site.clone(), plan.clone());
                self.discovery.graph.late_closures.insert(call_site, plan);
            } else {
                self.discovery
                    .graph
                    .closure_bodies
                    .insert(request.clone(), body_kind);
            }
        }
        Some(if late {
            PlannedClosure::Late(request)
        } else {
            PlannedClosure::Exact(request)
        })
    }

    /// Resolve the explicit signature of a typed anonymous callable into a
    /// closed `CallableShape`: annotated parameter types, the annotated (or
    /// implied Unit) result, and the declared outward effect row.
    fn typed_closure_shape(&mut self, expression: &Expr) -> Option<Box<CallableShape>> {
        let ExprKind::TypedClosure {
            params,
            return_type,
            outward_effects,
            ..
        } = &expression.kind
        else {
            return None;
        };
        let generic_map = self
            .program
            .functions
            .iter()
            .find(|function| self.owner == DeclarationKey::Function(function.name.clone()))
            .into_iter()
            .flat_map(|function| {
                function
                    .generics
                    .iter()
                    .flat_map(|generics| &generics.params)
                    .enumerate()
                    .map(|(ordinal, parameter)| {
                        (
                            parameter.name.clone(),
                            GenericParamKey {
                                owner: self.owner.clone(),
                                ordinal: ordinal as u32,
                            },
                        )
                    })
            })
            .collect::<BTreeMap<_, _>>();
        let callable_constraints = match &self.owner {
            DeclarationKey::Function(name) => self
                .templates
                .get(name)
                .map(|template| template.callable_constraints.clone())
                .unwrap_or_default(),
            DeclarationKey::Global(_) => BTreeMap::new(),
        };
        let instance_substitutions = if let BodyInstanceKey::Specialization(key) =
            &self.body_instance
            && let DeclarationKey::Function(template_name) = &key.template
            && let Some(template) = self.templates.get(template_name)
        {
            Some(substitutions_for_key(template, key))
        } else {
            None
        };
        let resolve = |walker: &mut Self, syntax: &TypeSyntax, what: &str| {
            let resolved =
                symbolic_type(syntax, &generic_map, &callable_constraints).and_then(|ty| {
                    match &instance_substitutions {
                        Some(substitutions) => substitute(&ty, substitutions),
                        None => Some(ty),
                    }
                });
            if resolved.is_none() {
                walker.error(format!(
                    "typed closure {what} has an unsupported or unresolved type annotation"
                ));
            }
            resolved
        };
        let mut param_types = Vec::with_capacity(params.len());
        for param in params.iter() {
            param_types.push(resolve(
                self,
                &param.ty,
                &format!("parameter `{}`", param.name),
            )?);
        }
        let result = match return_type {
            None => ProvisionalType::Predefined("Unit".into()),
            Some(syntax) => resolve(self, syntax, "result")?,
        };
        let mut effects = BTreeSet::new();
        if let Some(row) = outward_effects {
            if row.tail.is_some() {
                self.error(
                    "typed closure effect rows must be closed; open `| tail` rows need a named callable",
                );
                return None;
            }
            for member in &row.effects {
                if !expand_effect_member(
                    member,
                    self.program,
                    &generic_map,
                    &mut BTreeSet::new(),
                    &mut effects,
                ) {
                    self.error(
                        "typed closure effect row names an unknown effect or effect-row alias",
                    );
                    return None;
                }
            }
        }
        let effects = effects
            .into_iter()
            .map(|effect| {
                Some(crate::compiler_typeck::CallableEffect {
                    declaration: effect.declaration.clone(),
                    arguments: match &instance_substitutions {
                        Some(substitutions) => effect
                            .arguments
                            .iter()
                            .map(|argument| substitute(argument, substitutions))
                            .collect::<Option<Vec<_>>>()?,
                        None => effect.arguments.clone(),
                    },
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(Box::new(CallableShape {
            params: param_types,
            result,
            effects,
            effect_tail: None,
            infer_effects: false,
        }))
    }

    /// A typed anonymous callable in value position: its explicit signature is
    /// the expected shape, so no call-site context is required.
    fn typed_value_closure(&mut self, expression: &Expr) -> Option<ClosureRequest> {
        let shape = self.typed_closure_shape(expression)?;
        let mut substitutions = BTreeMap::new();
        let planned = self.contextual_closure(expression, &shape, &mut substitutions)?;
        let request = match planned {
            PlannedClosure::Exact(request) | PlannedClosure::Late(request) => request,
        };
        // Typed source closures are compiler-sealed producers: their exact
        // capture types and origin-bearing environment are recorded below.
        // Region/type checking remains responsible for each later unique
        // reborrow and for rejecting an overlapping or expired loan.
        if self.recording && !contains_late_callable_captures(&request) {
            let site = self.call_site(expression)?;
            self.discovery
                .graph
                .closure_values
                .insert(site, request.clone());
        }
        (!contains_late_callable_captures(&request)).then_some(request)
    }

    fn exact_closure_result(&mut self, expression: &Expr) -> Option<ClosureRequest> {
        self.exact_closure_results(expression)?.into_iter().next()
    }

    fn exact_closure_results(&mut self, expression: &Expr) -> Option<Vec<ClosureRequest>> {
        let expression = match &expression.kind {
            ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                match statements.last()? {
                    Stmt::Expr(value) => value,
                    _ => return None,
                }
            }
            ExprKind::Move(value) => value,
            _ => expression,
        };
        if let ExprKind::Variable(path) = &expression.kind
            && path.len() == 1
        {
            return match self.locals.get(path[0].as_ref()) {
                Some(LocalBinding::Closure(request)) => Some(vec![request.clone()]),
                Some(LocalBinding::ClosureSet(requests)) => Some(requests.clone()),
                _ => None,
            };
        }
        let site = self.call_site(expression)?;
        self.discovery
            .graph
            .returned_closure_sets
            .get(&site)
            .cloned()
            .or_else(|| {
                self.discovery
                    .graph
                    .closure_values
                    .get(&site)
                    .or_else(|| self.discovery.graph.returned_closures.get(&site))
                    .cloned()
                    .map(|request| vec![request])
            })
    }

    fn explicit_closure_result_shape(&mut self, expression: &Expr) -> Option<CallableShape> {
        let expression = match &expression.kind {
            ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                match statements.last()? {
                    Stmt::Expr(value) => value,
                    _ => return None,
                }
            }
            ExprKind::Move(value) => value,
            _ => expression,
        };
        matches!(expression.kind, ExprKind::TypedClosure { .. })
            .then(|| self.typed_closure_shape(expression))
            .flatten()
            .map(|shape| *shape)
    }

    /// Infer the complete nominal result of ordinary library `if`/`else`
    /// from complementary enum constructors. This is deliberately structural:
    /// `Result::Ok(value)` may fix `T` while `Result::Err(error)` fixes `E`, and
    /// `Option::None` contributes no payload evidence. No branch is lowered
    /// speculatively, so source order cannot affect discovery state.
    fn structural_else_nominal_context(
        &self,
        positive: &Expr,
        negative: &Expr,
    ) -> Option<ProvisionalType> {
        fn leaf(expression: &Expr) -> &Expr {
            match &expression.kind {
                ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                    match statements.last() {
                        Some(Stmt::Expr(value)) => leaf(value),
                        _ => expression,
                    }
                }
                ExprKind::Move(value) => leaf(value),
                _ => expression,
            }
        }

        fn collect_completion_leaves<'a>(expression: &'a Expr, leaves: &mut Vec<&'a Expr>) {
            let expression = leaf(expression);
            if let ExprKind::Call(callee, arguments) = &expression.kind
                && let ExprKind::Variable(path) = &callee.kind
                && path.len() == 1
                && path[0].as_ref() == "else"
                && let [conditional, negative] = arguments.as_slice()
                && let ExprKind::Call(if_callee, if_arguments) = &conditional.kind
                && let ExprKind::Variable(if_path) = &if_callee.kind
                && if_path.len() == 1
                && if_path[0].as_ref() == "if"
                && let [_, positive] = if_arguments.as_slice()
            {
                collect_completion_leaves(positive, leaves);
                collect_completion_leaves(negative, leaves);
                return;
            }
            if matches!(&expression.kind,
                ExprKind::Call(callee, arguments)
                    if arguments.is_empty()
                        && matches!(&callee.kind,
                            ExprKind::Variable(path)
                                if path.len() == 1 && path[0].as_ref() == "unreachable"))
            {
                return;
            }
            leaves.push(expression);
        }

        let mut branches = Vec::new();
        collect_completion_leaves(positive, &mut branches);
        collect_completion_leaves(negative, &mut branches);
        self.structural_nominal_context(&branches)
    }

    fn structural_else_obvious_context(
        &self,
        positive: &Expr,
        negative: &Expr,
    ) -> Option<ProvisionalType> {
        fn leaf(expression: &Expr) -> &Expr {
            match &expression.kind {
                ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                    match statements.last() {
                        Some(Stmt::Expr(value)) => leaf(value),
                        _ => expression,
                    }
                }
                ExprKind::Move(value) => leaf(value),
                _ => expression,
            }
        }

        fn collect_completion_leaves<'a>(expression: &'a Expr, leaves: &mut Vec<&'a Expr>) {
            let expression = leaf(expression);
            if let ExprKind::Call(callee, arguments) = &expression.kind
                && let ExprKind::Variable(path) = &callee.kind
                && path.len() == 1
                && path[0].as_ref() == "else"
                && let [conditional, negative] = arguments.as_slice()
                && let ExprKind::Call(if_callee, if_arguments) = &conditional.kind
                && let ExprKind::Variable(if_path) = &if_callee.kind
                && if_path.len() == 1
                && if_path[0].as_ref() == "if"
                && let [_, positive] = if_arguments.as_slice()
            {
                collect_completion_leaves(positive, leaves);
                collect_completion_leaves(negative, leaves);
                return;
            }
            leaves.push(expression);
        }

        let mut leaves = Vec::new();
        collect_completion_leaves(positive, &mut leaves);
        collect_completion_leaves(negative, &mut leaves);
        let mut known = leaves.into_iter().filter_map(|leaf| {
            self.obvious_argument_type(leaf)
                .filter(|(_, defaulted)| !defaulted)
                .map(|(ty, _)| ty)
                .filter(|ty| ty != &ProvisionalType::Predefined("Never".into()))
        });
        let first = known.next()?;
        known.all(|candidate| candidate == first).then_some(first)
    }

    /// Infer one complete generic nominal result from complementary
    /// constructor branches. Each branch may fix only part of the nominal:
    /// for example `Result::Ok(value)` fixes `T`, while `Result::Err(error)`
    /// fixes `E`.
    fn structural_nominal_context(&self, branches: &[&Expr]) -> Option<ProvisionalType> {
        fn leaf(expression: &Expr) -> Option<&Expr> {
            match &expression.kind {
                ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                    match statements.last()? {
                        Stmt::Expr(value) => Some(value),
                        _ => None,
                    }
                }
                ExprKind::Move(value) => leaf(value),
                _ => Some(expression),
            }
        }

        fn constructor(expression: &Expr) -> Option<(&str, &str, &[Expr], bool)> {
            let expression = leaf(expression)?;
            let (callee, arguments) = match &expression.kind {
                ExprKind::Call(callee, arguments) => (callee.as_ref(), arguments.as_slice()),
                ExprKind::Variable(_) => (expression, &[][..]),
                _ => return None,
            };
            let ExprKind::Variable(path) = &callee.kind else {
                return None;
            };
            if path.len() == 1 && path[0].as_ref() == "None" {
                return Some(("Result", "Err", &[][..], true));
            }
            if path.len() != 2 {
                return None;
            }
            match (path[0].as_ref(), path[1].as_ref()) {
                ("Option", "Some") => Some(("Result", "Ok", arguments, false)),
                (head, variant) => Some((head, variant, arguments, false)),
            }
        }

        let constructors = branches
            .iter()
            .map(|branch| constructor(branch))
            .collect::<Option<Vec<_>>>()?;
        let head = constructors.first()?.0;
        if !matches!(head, "Result" | "Option")
            || constructors
                .iter()
                .any(|(candidate, ..)| *candidate != head)
        {
            return None;
        }
        let template = self.nominal_templates.get(head)?;
        let mutable = template.params.iter().cloned().collect::<BTreeSet<_>>();
        let mut substitutions = BTreeMap::new();
        for (_, variant, arguments, unit_payload) in constructors {
            let fields = template.variants.get(variant)?;
            if (!unit_payload && fields.len() != arguments.len())
                || (unit_payload && fields.len() != 1)
            {
                return None;
            }
            for (argument, formal) in arguments.iter().zip(fields) {
                let (actual, _) = self.obvious_argument_type(argument)?;
                if !unify_inference(formal, &actual, &mutable, &mut substitutions) {
                    return None;
                }
            }
            if unit_payload
                && !unify_inference(
                    &fields[0],
                    &ProvisionalType::Predefined("Unit".into()),
                    &mutable,
                    &mut substitutions,
                )
            {
                return None;
            }
        }
        let arguments = template
            .params
            .iter()
            .map(|param| match substitutions.get(param)? {
                SpecializationArgument::Type(ty) => Some(ty.clone()),
                SpecializationArgument::Closure(_, shape, _, _, _, _) => {
                    Some(ProvisionalType::Callable(shape.clone()))
                }
                SpecializationArgument::EffectRow(_) => None,
            })
            .collect::<Option<Vec<_>>>()?;
        Some(ProvisionalType::Nominal(NominalInstanceKey {
            declaration: NominalKey(head.to_owned()),
            arguments,
        }))
    }

    fn value_closure(
        &mut self,
        expression: &Expr,
        expected: Option<&CallableShape>,
    ) -> Option<ClosureRequest> {
        let inferred;
        let expected = if let Some(expected) = expected {
            expected
        } else {
            let ExprKind::Closure { params, body } = &expression.kind else {
                return None;
            };
            if !params.is_empty() {
                self.error(
                    "an uncontextualized closure with parameters needs one exact Fn constraint",
                );
                return None;
            }
            let saved_recording = self.recording;
            self.recording = false;
            let result = self.expression(body, None);
            self.recording = saved_recording;
            inferred = CallableShape {
                params: vec![],
                result: result?,
                effects: direct_closure_effects(
                    body,
                    &|site, effect| self.effect_instance(site, effect),
                    &|call| self.resolved_effects_at(call),
                )
                .into_iter()
                .collect(),
                effect_tail: None,
                infer_effects: false,
            };
            &inferred
        };
        let mut substitutions = BTreeMap::new();
        let planned = self.contextual_closure(expression, expected, &mut substitutions)?;
        let request = match planned {
            PlannedClosure::Exact(request) | PlannedClosure::Late(request) => request,
        };
        if self.recording && !contains_late_callable_captures(&request) {
            let site = self.call_site(expression)?;
            self.discovery
                .graph
                .closure_values
                .insert(site, request.clone());
        }
        (!contains_late_callable_captures(&request)).then_some(request)
    }

    fn infer_nominal_construction(
        &mut self,
        source: &Expr,
        head: &str,
        params: &[GenericParamKey],
        values: &[(&Expr, &ProvisionalType)],
        expected: Option<&ProvisionalType>,
    ) -> Option<ProvisionalType> {
        let expected_instance = expected.and_then(|ty| match ty {
            ProvisionalType::Nominal(instance)
                if instance.declaration.0 == head && instance.arguments.len() == params.len() =>
            {
                Some(instance)
            }
            _ => None,
        });
        let mut substitutions = expected_instance
            .map(|instance| {
                params
                    .iter()
                    .cloned()
                    .zip(
                        instance
                            .arguments
                            .iter()
                            .cloned()
                            .map(SpecializationArgument::Type),
                    )
                    .collect::<BTreeMap<_, _>>()
            })
            .unwrap_or_default();
        let mut exact_closure_sets = BTreeMap::<GenericParamKey, Vec<ClosureRequest>>::new();
        for (value, formal) in values {
            let exact_callable = match &value.kind {
                ExprKind::Variable(path) if path.len() == 1 => {
                    match self.locals.get(path[0].as_ref()).cloned() {
                        Some(LocalBinding::Closure(closure)) => {
                            Some(ClosureTupleField::Closure(closure))
                        }
                        Some(LocalBinding::ClosureSet(closures)) => {
                            Some(ClosureTupleField::ClosureSet(closures))
                        }
                        _ => None,
                    }
                }
                ExprKind::Move(operand) => match &operand.kind {
                    ExprKind::Variable(path) if path.len() == 1 => {
                        match self.locals.get(path[0].as_ref()).cloned() {
                            Some(LocalBinding::Closure(closure)) => {
                                Some(ClosureTupleField::Closure(closure))
                            }
                            Some(LocalBinding::ClosureSet(closures)) => {
                                Some(ClosureTupleField::ClosureSet(closures))
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                },
                _ => None,
            };
            let exact_closure = match &exact_callable {
                Some(ClosureTupleField::Closure(closure)) => Some(closure),
                Some(ClosureTupleField::ClosureSet(closures)) => closures.first(),
                Some(ClosureTupleField::Type(_)) | None => None,
            };
            if let (ProvisionalType::Param(param), Some(closure)) = (formal, exact_closure) {
                substitutions.insert(
                    param.clone(),
                    SpecializationArgument::Closure(
                        closure.site.clone(),
                        closure.shape.clone(),
                        closure.captures.clone(),
                        closure.param_env.clone(),
                        closure.active_labels.clone(),
                        closure.static_captures.clone(),
                    ),
                );
                if let Some(ClosureTupleField::ClosureSet(closures)) = &exact_callable {
                    exact_closure_sets.insert(param.clone(), closures.clone());
                }
            }
            let contextual = substitute(formal, &substitutions);
            // A reference-bearing contextual field can retain symbolic generic
            // referents while still fixing the constructor's complete shape.
            // Pass that context through so a refined enum projection such as
            // `Ok(&value.0)` does not lose the declared `Result<&A, &E>` shape
            // merely because A/E are not ground during symbolic validation.
            let contextual = contextual.as_ref().filter(|contextual| {
                self.symbolic_validation
                    || ground(contextual)
                    || matches!(
                        contextual,
                        ProvisionalType::Shared(_) | ProvisionalType::Unique(_)
                    )
            });
            let actual = self.expression(value, contextual)?;
            if !bind(formal, &actual, &mut substitutions)
                && !(self.symbolic_validation
                    && (!ground(&actual) || contextual.as_ref().is_some_and(|ty| !ground(ty))))
            {
                self.error(format!(
                    "generic nominal construction `{head}` has conflicting type arguments"
                ));
                return None;
            }
        }
        let arguments = params
            .iter()
            .map(|param| match substitutions.get(param) {
                Some(SpecializationArgument::Type(ty))
                    if ground(ty) || self.symbolic_validation =>
                {
                    Some(ty.clone())
                }
                Some(SpecializationArgument::Closure(_, shape, _, _, _, _)) => {
                    Some(ProvisionalType::Callable(shape.clone()))
                }
                _ => None,
            })
            .collect::<Option<Vec<_>>>();
        let Some(arguments) = arguments else {
            self.error(format!(
                "generic nominal construction `{head}` is ambiguous because not every type parameter is fixed by an expected type or payload"
            ));
            return None;
        };
        let instance = NominalInstanceKey {
            declaration: NominalKey(head.to_owned()),
            arguments,
        };
        if self.recording
            && let Some(site) = self.call_site(source)
        {
            let exact_arguments = params
                .iter()
                .filter_map(|param| {
                    if let Some(closures) = exact_closure_sets.get(param) {
                        return Some(ClosureTupleField::ClosureSet(closures.clone()));
                    }
                    match substitutions.get(param)? {
                        SpecializationArgument::Type(ty) => {
                            Some(ClosureTupleField::Type(ty.clone()))
                        }
                        SpecializationArgument::Closure(
                            site,
                            shape,
                            captures,
                            environment,
                            active_labels,
                            static_captures,
                        ) => Some(ClosureTupleField::Closure(ClosureRequest {
                            site: site.clone(),
                            shape: shape.clone(),
                            captures: captures.clone(),
                            param_env: environment.clone(),
                            active_labels: active_labels.clone(),
                            static_captures: static_captures.clone(),
                        })),
                        SpecializationArgument::EffectRow(_) => None,
                    }
                })
                .collect::<Vec<_>>();
            let has_closure = exact_arguments.iter().any(|argument| {
                matches!(
                    argument,
                    ClosureTupleField::Closure(_) | ClosureTupleField::ClosureSet(_)
                )
            });
            let has_late_callable = !has_closure
                && instance
                    .arguments
                    .iter()
                    .any(|argument| matches!(argument, ProvisionalType::Callable(_)));
            if has_closure {
                self.discovery.graph.closure_nominal_constructions.insert(
                    site.clone(),
                    ClosureNominalInstance {
                        declaration: head.to_owned(),
                        arguments: exact_arguments,
                    },
                );
            }
            if has_late_callable {
                self.discovery
                    .graph
                    .late_nominal_constructions
                    .insert(site.clone(), instance.clone());
            }
            if !has_closure
                && !has_late_callable
                && self
                    .discovery
                    .graph
                    .constructions
                    .insert(site, instance.clone())
                    .is_some_and(|existing| existing != instance)
            {
                self.error(format!(
                    "generic nominal construction `{head}` has inconsistent ground choices"
                ));
                return None;
            }
            if !has_closure && !has_late_callable {
                self.discovery
                    .graph
                    .constructed_nominals
                    .insert(instance.clone());
            }
        }
        Some(ProvisionalType::Nominal(instance))
    }

    fn enum_construction(
        &mut self,
        source: &Expr,
        head: &str,
        variant: &str,
        args: &[Expr],
        expected: Option<&ProvisionalType>,
    ) -> Option<ProvisionalType> {
        // Recursive expression discovery needs `&mut self`, so retain only the
        // selected constructor shape across it instead of cloning every
        // variant in the nominal template.
        let (params, fields) = {
            let template = self.nominal_templates.get(head)?;
            (
                template.params.clone(),
                template.variants.get(variant)?.clone(),
            )
        };
        if fields.len() != args.len() {
            args.iter().for_each(|argument| {
                self.expression(argument, None);
            });
            return None;
        }
        if params.is_empty() {
            for (argument, field) in args.iter().zip(&fields) {
                self.expression(argument, Some(field));
            }
            return Some(ProvisionalType::Nominal(NominalInstanceKey::monomorphic(
                head.to_owned(),
            )));
        }
        let values = args.iter().zip(&fields).collect::<Vec<_>>();
        self.infer_nominal_construction(source, head, &params, &values, expected)
    }

    fn direct_call(
        &mut self,
        source: &Expr,
        name: &str,
        args: &[Expr],
        expected: Option<&ProvisionalType>,
        requested_receiver_mode: Option<u32>,
    ) -> Option<ProvisionalType> {
        // A call nested in a specialized generic body may receive contextual
        // evidence that still uses the caller template's rigid binders. Those
        // binders are mutable only for the caller, but they are already fixed
        // by its specialization key. Ground that context before using it to
        // infer the nested callee's result-only parameters (notably parser
        // transaction helpers whose item type appears in `Fn::Output`).
        let specialized_expected = match (&self.body_instance, expected) {
            (BodyInstanceKey::Specialization(key), Some(expected)) => self
                .templates
                .get(match &key.template {
                    DeclarationKey::Function(name) => name,
                    DeclarationKey::Global(_) => return None,
                })
                .and_then(|template| substitute(expected, &substitutions_for_key(template, key))),
            _ => None,
        };
        let expected = specialized_expected.as_ref().or(expected);
        // Resolution may revisit this syntax under a different contextual
        // callable shape. Clear the previous fact before recording the exact
        // target selected by this attempt.
        self.record_call_effects(source, []);
        if let Some(LocalBinding::DeferredFunctionItem(item)) = self.locals.get(name).cloned() {
            return self.resolve_deferred_function_item(
                source,
                name,
                item,
                args,
                expected,
                requested_receiver_mode,
            );
        }
        if let Some(shape) = self.static_label_shape(name) {
            if args.len() != 1 {
                self.error(format!(
                    "label parameter `{name}` expects one payload argument, but {} were supplied",
                    args.len()
                ));
                return None;
            }
            let actual = self.expression(&args[0], shape.params.first())?;
            if !equivalent_specialization_type(&actual, &shape.params[0])
                && (!self.symbolic_validation || ground(&actual) && ground(&shape.params[0]))
            {
                self.error(format!("label parameter `{name}` has an ambiguous payload"));
                return None;
            }
            return Some(shape.result);
        }
        if let Some(LocalBinding::Type(ProvisionalType::Callable(shape))) =
            self.locals.get(name).cloned()
        {
            if !self.symbolic_validation {
                self.error(format!(
                    "callable local `{name}` has a symbolic shape but no concrete callable identity"
                ));
                return None;
            }
            if args.len() != shape.params.len() {
                self.error(format!(
                    "symbolic callable parameter `{name}` expects {} argument(s), but {} were supplied",
                    shape.params.len(),
                    args.len()
                ));
                return None;
            }
            for (argument, formal) in args.iter().zip(&shape.params) {
                let actual = self.expression(argument, Some(formal))?;
                if !equivalent_specialization_type(&actual, formal)
                    && (!self.symbolic_validation || ground(&actual) && ground(formal))
                {
                    self.error(format!(
                        "symbolic callable parameter `{name}` has an ambiguous argument"
                    ));
                    return None;
                }
            }
            if expected.is_some_and(|expected| {
                self.symbolically_known_type(expected)
                    && ground(expected)
                    && ground(&shape.result)
                    && !equivalent_specialization_type(expected, &shape.result)
            }) && !matches!(
                shape.result,
                ProvisionalType::Predefined(ref result) if result == "Never"
            ) {
                self.error(format!(
                    "symbolic callable parameter `{name}` has an ambiguous result"
                ));
                return None;
            }
            self.record_call_effects(source, shape.effects.iter().cloned());
            return Some(shape.result);
        }
        if let Some(LocalBinding::RecursiveSelf(recursive_self, shape)) =
            self.locals.get(name).cloned()
        {
            let result = shape.result.clone();
            let effects = shape.effects.clone();
            if args.len() != shape.params.len() {
                self.error(format!(
                    "recursive callable `{name}` has an unresolved argument count"
                ));
                return None;
            }
            for (argument, formal) in args.iter().zip(&shape.params) {
                let actual = self.expression(argument, Some(formal))?;
                if !equivalent_specialization_type(&actual, formal) {
                    self.error(format!(
                        "recursive callable `{name}` has an ambiguous argument"
                    ));
                    return None;
                }
            }
            if expected
                .is_some_and(|expected| !equivalent_specialization_type(expected, &shape.result))
                && !matches!(shape.result, ProvisionalType::Predefined(ref name) if name == "Never")
            {
                self.error(format!(
                    "recursive callable `{name}` has an ambiguous result"
                ));
                return None;
            }
            if self.recording || self.active_recursive_self.is_some() {
                let call_site = self.call_site(source)?;
                self.discovery.graph.recursive_self_calls.insert(
                    call_site,
                    RecursiveSelfCall {
                        recursive_self,
                        shape,
                        requested_receiver_mode,
                    },
                );
            }
            self.record_call_effects(source, effects);
            return Some(result);
        }
        if let Some(LocalBinding::ClosureSet(closures)) = self.locals.get(name).cloned() {
            let first = closures.first()?;
            let shape = &first.shape;
            let result = shape.result.clone();
            let effects = shape.effects.clone();
            if args.len() != shape.params.len() {
                self.error(format!(
                    "callable local `{name}` has an unresolved argument count"
                ));
                return None;
            }
            for (argument, formal) in args.iter().zip(&shape.params) {
                let actual = self.expression(argument, Some(formal))?;
                if !equivalent_specialization_type(&actual, formal) {
                    self.error(format!("callable local `{name}` has an ambiguous argument"));
                    return None;
                }
            }
            if expected.is_some_and(|expected| {
                ground(expected)
                    && ground(&shape.result)
                    && !equivalent_specialization_type(expected, &shape.result)
            }) && !expected.is_some_and(contains_projection_placeholder)
                && !matches!(shape.result, ProvisionalType::Predefined(ref name) if name == "Never")
            {
                self.error(format!("callable local `{name}` has an ambiguous result"));
                return None;
            }
            if self.recording {
                let call_site = self.call_site(source)?;
                self.discovery
                    .graph
                    .indirect_call_sets
                    .insert(call_site.clone(), closures);
                if let Some(mode) = requested_receiver_mode {
                    self.discovery
                        .graph
                        .indirect_call_modes
                        .insert(call_site, mode);
                }
            }
            self.record_call_effects(source, effects);
            return Some(result);
        }
        if let Some(LocalBinding::Closure(closure)) = self.locals.get(name).cloned() {
            let shape = &closure.shape;
            let result = shape.result.clone();
            let effects = shape.effects.clone();
            if args.len() != shape.params.len() {
                self.error(format!(
                    "callable local `{name}` has an unresolved argument count"
                ));
                return None;
            }
            for (argument, formal) in args.iter().zip(&shape.params) {
                let actual = self.expression(argument, Some(formal))?;
                if !equivalent_specialization_type(&actual, formal) {
                    self.error(format!("callable local `{name}` has an ambiguous argument"));
                    return None;
                }
            }
            if expected.is_some_and(|expected| {
                ground(expected)
                    && ground(&shape.result)
                    && !equivalent_specialization_type(expected, &shape.result)
            }) && !expected.is_some_and(contains_projection_placeholder)
                && !matches!(
                    shape.result,
                    ProvisionalType::Predefined(ref name) if name == "Never"
                )
            {
                self.error(format!("callable local `{name}` has an ambiguous result"));
                return None;
            }
            if self.recording {
                let call_site = self.call_site(source)?;
                self.discovery
                    .graph
                    .indirect_calls
                    .insert(call_site.clone(), closure.clone());
                if let Some(mode) = requested_receiver_mode {
                    self.discovery
                        .graph
                        .indirect_call_modes
                        .insert(call_site.clone(), mode);
                }
                // Retain the existing scalarized plan until Core indirect-call
                // lowering consumes `indirect_calls`.
                self.discovery
                    .graph
                    .callable_calls
                    .insert(call_site, closure);
            }
            self.record_call_effects(source, effects);
            return Some(result);
        }
        if name.starts_with("$trait_deferred$") {
            if let Some(target) = self.ground_deferred_trait_template(name, args) {
                return self.direct_call(source, &target, args, expected, requested_receiver_mode);
            }
            for argument in args {
                self.expression(argument, None)?;
            }
            // Symbolic validation and genuinely ambiguous ground evidence stay
            // opaque here. Core retains the finite fail-closed fallback for
            // those cases; a uniquely ground generic implementation is routed
            // through the ordinary specialization request path above.
            return Some(
                expected
                    .cloned()
                    .unwrap_or_else(|| ProvisionalType::Predefined("Unit".into())),
            );
        }
        let Some(template) = self.templates.get(name).cloned() else {
            args.iter().for_each(|argument| {
                self.expression(argument, None);
            });
            return None;
        };
        let transports_symbolic_resumption = args.first().is_some_and(|argument| {
            let variable = match &argument.kind {
                ExprKind::Variable(path) => Some(path),
                ExprKind::Move(inner) => match &inner.kind {
                    ExprKind::Variable(path) => Some(path),
                    _ => None,
                },
                _ => None,
            };
            variable.is_some_and(|path| {
                path.len() == 1
                    && matches!(
                        self.locals.get(path[0].as_ref()),
                        Some(LocalBinding::Type(ProvisionalType::Callable(_)))
                    )
            })
        });
        let transports_inline_callable = args.first().is_some_and(|argument| {
            matches!(
                argument.kind,
                ExprKind::Closure { .. } | ExprKind::TypedClosure { .. }
            )
        });
        let transported_exact_closure = args.first().and_then(|argument| {
            let variable = match &argument.kind {
                ExprKind::Variable(path) => Some(path),
                ExprKind::Move(inner) => match &inner.kind {
                    ExprKind::Variable(path) => Some(path),
                    _ => None,
                },
                _ => None,
            }?;
            (variable.len() == 1)
                .then(|| self.locals.get(variable[0].as_ref()))
                .flatten()
                .and_then(|binding| match binding {
                    LocalBinding::Closure(closure) => Some(closure.clone()),
                    _ => None,
                })
        });
        if template.transparent_identity
            && args.len() == 1
            && (transports_symbolic_resumption
                || transports_inline_callable
                || transported_exact_closure.is_some())
        {
            let actual = self.expression(&args[0], expected)?;
            if expected.is_some_and(|expected| expected != &actual) {
                self.error(format!("call to `{name}` has an ambiguous result"));
                return None;
            }
            if self.recording
                && let Some(closure) = transported_exact_closure
                && let Some(site) = self.call_site(source)
            {
                self.discovery.graph.returned_closures.insert(site, closure);
            }
            return Some(actual);
        }
        if args.len() != template.params.len() {
            self.error(format!("call to `{name}` has an unresolved argument count"));
            return None;
        }
        let mut substitutions = BTreeMap::new();
        let mutable_inference = template
            .generic_params
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut closures = BTreeSet::new();
        let mut static_closure_arguments = Vec::new();
        let mut exact_callable_arguments = BTreeMap::<GenericParamKey, Vec<ClosureRequest>>::new();
        if let Some(expected) = expected
            // A monomorphic nested call can provide evidence for inference
            // variables owned by its enclosing call island. Those variables
            // are rigid to this callee, so trying to solve them here would
            // reject before the enclosing contextual-closure check can bind
            // its expected Output to the concrete result we return.
            && (!template.generic_params.is_empty() || ground(expected))
            && !matches!(
                template.result,
                ProvisionalType::Predefined(ref name) if name == "Never"
            )
            && !contains_projection_placeholder(&template.result)
        {
            let mut trial = substitutions.clone();
            if unify_inference(&template.result, expected, &mutable_inference, &mut trial)
                || (!ground(expected)
                    && constrain_contextual_inference(
                        &template.result,
                        expected,
                        &mutable_inference,
                        &mut trial,
                    ))
            {
                substitutions = trial;
            } else if template.generic_params.is_empty() && !self.symbolic_validation {
                self.error(format!("call to `{name}` has an ambiguous result"));
                return None;
            }
        }
        // Seed constraints from every independently synthesizable ordinary
        // argument before checking arguments left-to-right. Without this,
        // `select(Phantom::None, 42)` spuriously depends on argument order:
        // the empty constructor needs `T`, while the later literal fixes it.
        // The real expression walk below still performs all diagnostics and
        // records every discovery edge exactly once.
        for (argument, formal) in args.iter().zip(&template.params) {
            if matches!(formal, ProvisionalType::Callable(_)) {
                if let Some(actual) = self.typed_closure_shape(argument) {
                    let mut trial = substitutions.clone();
                    if bind(formal, &ProvisionalType::Callable(actual), &mut trial) {
                        substitutions = trial;
                    }
                }
                continue;
            }
            if substitute(formal, &substitutions).is_some_and(|ty| ground(&ty)) {
                continue;
            }
            if let Some((actual, false)) = self.obvious_argument_type(argument) {
                let mut trial = substitutions.clone();
                if unify_inference(formal, &actual, &mutable_inference, &mut trial) {
                    substitutions = trial;
                }
            }
        }
        // Static label arguments are independently synthesizable, but their
        // payload equality lives in the Label marker rather than the ordinary
        // parameter type. Apply that equality before walking context-dependent
        // value arguments. This lets `try(value, @function)` pass the
        // function's exact `Result<_, E>` context into `value`, including a
        // generic iterator callback whose only successful arm is `Ok(())`.
        for constraint in &template.marker_constraints {
            if constraint.polarity != GoalPolarity::Positive
                || !self
                    .trait_db
                    .intrinsic_key(IntrinsicRole::Label)
                    .is_some_and(|key| key == &constraint.trait_key)
            {
                continue;
            }
            let constraint_subject = constraint
                .subject_binder
                .clone()
                .map(ProvisionalType::Param)
                .unwrap_or_else(|| constraint.subject.clone());
            let Some(subject) = substitute(&constraint_subject, &substitutions) else {
                continue;
            };
            let [GenericArg::Type(formal_payload)] = constraint.arguments.as_slice() else {
                continue;
            };

            let evidence_payloads = label_payload_type(&subject)
                .cloned()
                .into_iter()
                .chain(
                    self.param_env
                        .matching_argument_lists(
                            constraint.polarity,
                            &constraint.trait_key,
                            &subject,
                        )
                        .into_iter()
                        .filter_map(|arguments| match arguments.as_slice() {
                            [GenericArg::Type(payload)] => Some(payload.clone()),
                            _ => None,
                        }),
                )
                .collect::<Vec<_>>();
            for payload in evidence_payloads {
                let mut trial = substitutions.clone();
                if constrain_contextual_inference(
                    formal_payload,
                    &payload,
                    &mutable_inference,
                    &mut trial,
                ) {
                    substitutions = trial;
                    break;
                }
            }
        }
        // Numeric literals are the weakest available evidence. Apply their
        // language defaults only after exact label payloads have constrained
        // phantom result/error parameters; otherwise `ensure(false, 7,
        // @exit)` would choose `i64` before learning the destination's exact
        // `Result<T, E>` payload.
        for (argument, formal) in args.iter().zip(&template.params) {
            if matches!(formal, ProvisionalType::Callable(_))
                || substitute(formal, &substitutions).is_some_and(|ty| ground(&ty))
            {
                continue;
            }
            if let Some((actual, true)) = self.obvious_argument_type(argument) {
                let mut trial = substitutions.clone();
                if unify_inference(formal, &actual, &mutable_inference, &mut trial) {
                    substitutions = trial;
                }
            }
        }
        for (index, (argument, formal)) in args.iter().zip(&template.params).enumerate() {
            let resolved_formal = substitute_preserving_missing(formal, &substitutions)
                .unwrap_or_else(|| formal.clone());
            let resolved_formal = normalize_projection_placeholders(
                &resolved_formal,
                self.trait_db,
                self.solver_budget,
            )
            .unwrap_or(resolved_formal);
            if let ProvisionalType::Callable(shape) = &resolved_formal {
                let forwarded_name = match &argument.kind {
                    ExprKind::Variable(path) if path.len() == 1 => Some(path[0].as_ref()),
                    ExprKind::Move(inner) => match &inner.kind {
                        ExprKind::Variable(path) if path.len() == 1 => Some(path[0].as_ref()),
                        _ => None,
                    },
                    _ => None,
                };
                let forwarded =
                    forwarded_name.and_then(|name| match self.locals.get(name).cloned() {
                        Some(LocalBinding::Closure(closure)) => Some(closure),
                        _ => None,
                    });
                let symbolic_forwarded = forwarded_name.and_then(|name| {
                    self.locals.get(name).and_then(|binding| match binding {
                        LocalBinding::Type(ProvisionalType::Callable(shape)) => Some(shape.clone()),
                        _ => None,
                    })
                });
                if let Some(actual_shape) = symbolic_forwarded {
                    if !bind(
                        &resolved_formal,
                        &ProvisionalType::Callable(actual_shape.clone()),
                        &mut substitutions,
                    ) {
                        self.error(format!(
                            "call to `{name}` has an ambiguous forwarded callable argument"
                        ));
                        return None;
                    }
                    if let Some(binder) = &template.parameter_binders[index] {
                        let symbolic = self
                            .symbolic_callable_parameter(
                                forwarded_name.expect("symbolic forwarding has a local name"),
                            )
                            .map(ProvisionalType::Param)
                            .map(SpecializationArgument::Type)
                            .unwrap_or_else(|| {
                                SpecializationArgument::Type(ProvisionalType::Callable(
                                    actual_shape,
                                ))
                            });
                        match substitutions.get(binder) {
                            Some(existing) if existing != &symbolic => {
                                self.error(format!(
                                    "call to `{name}` has conflicting symbolic callable evidence"
                                ));
                                return None;
                            }
                            Some(_) => {}
                            None => {
                                substitutions.insert(binder.clone(), symbolic);
                            }
                        }
                    }
                    continue;
                }
                let closure = if let Some(closure) = forwarded {
                    let formal = resolved_formal.clone();
                    let actual = ProvisionalType::Callable(closure.shape.clone());
                    if !bind(&formal, &actual, &mut substitutions) {
                        self.error(format!(
                            "call to `{name}` has an ambiguous forwarded callable argument"
                        ));
                        return None;
                    }
                    closure
                } else {
                    match self.contextual_closure(argument, shape, &mut substitutions)? {
                        PlannedClosure::Exact(closure) => {
                            if self.recording {
                                let body_kind = match argument.kind {
                                    ExprKind::Closure { .. } | ExprKind::TypedClosure { .. } => {
                                        ClosureBodyKind::Explicit
                                    }
                                    ExprKind::Block(_) | ExprKind::ContextBlock(_) => {
                                        ClosureBodyKind::ContextualBlock
                                    }
                                    _ => unreachable!(
                                        "contextual_closure accepted only source closure syntax"
                                    ),
                                };
                                if let Some(site) = self.call_site(argument) {
                                    static_closure_arguments.push((
                                        site,
                                        LateClosurePlan {
                                            request: closure.clone(),
                                            body_kind,
                                            recursive_self: self.active_recursive_self.clone(),
                                        },
                                    ));
                                }
                            }
                            closure
                        }
                        // The call itself must remain on the late path because
                        // an emitted specialization key cannot name the
                        // handler-site callable identity yet.
                        PlannedClosure::Late(_) => return None,
                    }
                };
                if let Some(binder) = template.parameter_binders[index].as_ref().or(match formal {
                    ProvisionalType::Param(binder) => Some(binder),
                    _ => None,
                }) {
                    exact_callable_arguments
                        .entry(binder.clone())
                        .or_default()
                        .push(closure.clone());
                }
                if let Some(binder) = &template.parameter_binders[index] {
                    match substitutions.get(binder) {
                        Some(SpecializationArgument::Closure(
                            _,
                            existing_shape,
                            existing_captures,
                            existing_environment,
                            existing_labels,
                            existing_static,
                        )) if !compatible_sealed_producer_contracts(
                            existing_shape,
                            existing_captures,
                            existing_environment,
                            existing_labels,
                            existing_static,
                            &closure.shape,
                            &closure.captures,
                            &closure.param_env,
                            &closure.active_labels,
                            &closure.static_captures,
                        ) =>
                        {
                            let message = "VM-sealed generic callable transport has incompatible producer signature/effect, receiver mode, capture layout, or lifetime environment";
                            if let Some(site) = self.call_site(source) {
                                self.discovery
                                    .graph
                                    .opaque_closure_sets
                                    .insert(site, message.to_owned());
                            }
                            self.error(message);
                            return None;
                        }
                        Some(SpecializationArgument::Closure(..)) => {
                            // `T` denotes the callable contract, not one source
                            // producer identity. Keep the first producer as the
                            // deterministic specialization representative and
                            // retain every compatible identity in
                            // `exact_callable_arguments` for the sealed set.
                        }
                        Some(_) => {
                            self.error("callable binder has ambiguous closure arguments");
                            return None;
                        }
                        None => {
                            substitutions.insert(
                                binder.clone(),
                                SpecializationArgument::Closure(
                                    closure.site.clone(),
                                    closure.shape.clone(),
                                    closure.captures.clone(),
                                    closure.param_env.clone(),
                                    closure.active_labels.clone(),
                                    closure.static_captures.clone(),
                                ),
                            );
                        }
                    }
                    if self.recording
                        && (template.result_binder.as_ref() == Some(binder)
                            || template.result_nominal_binders.as_ref().is_some_and(
                                |(_, binders)| {
                                    binders
                                        .iter()
                                        .any(|candidate| candidate.as_ref() == Some(binder))
                                },
                            ))
                        && let Some(site) = self.call_site(argument)
                    {
                        self.discovery
                            .graph
                            .closure_values
                            .insert(site, closure.clone());
                    }
                }
                closures.insert(closure);
            } else {
                let contextual_formal = substitute_preserving_missing(formal, &substitutions);
                let contextual_formal = contextual_formal.as_ref().filter(|formal| {
                    self.symbolic_validation
                            || ground(formal)
                            // A nested call can solve its own variables from
                            // the concrete portions of an enclosing symbolic
                            // formal. Its remaining rigid variables are then
                            // solved when the resulting ground type is unified
                            // back into this call below.
                            || matches!(argument.kind, ExprKind::Call(_, _))
                });
                let mut actual = self.expression(argument, contextual_formal).or_else(|| {
                    self.may_use_bidirectional_result_fallback(argument)
                        .then(|| contextual_formal.cloned())
                        .flatten()
                })?;
                // Call-site reference elaboration reborrows a unique handle
                // and may demote it to a shared reference. Discovery must use
                // that same effective argument type or an enclosing generic
                // call can disappear merely because its nested monomorphic
                // argument used `value` instead of `&*value`.
                if let (ProvisionalType::Shared(_), ProvisionalType::Unique(actual_referent)) =
                    (&resolved_formal, &actual)
                {
                    // A unique reference always admits a shared reborrow. Do
                    // not require the referent to be ground before applying
                    // that coercion: a generic formal such as `&Vec<T>` must
                    // still infer `T` from an actual `&mut Vec<u32>`.
                    actual = ProvisionalType::shared((**actual_referent).clone());
                }
                if !unify_inference(formal, &actual, &mutable_inference, &mut substitutions)
                    && !self.symbolic_validation
                {
                    self.error(format!(
                        "call to `{name}` has ambiguous generic arguments at argument {}",
                        index + 1
                    ));
                    return None;
                }
                if matches!(actual, ProvisionalType::Callable(_))
                    && let Some(binder) =
                        template.parameter_binders[index].as_ref().or(match formal {
                            ProvisionalType::Param(binder) => Some(binder),
                            _ => None,
                        })
                    && let Some(mut producers) = self.exact_closure_results(argument)
                {
                    closures.extend(producers.iter().cloned());
                    exact_callable_arguments
                        .entry(binder.clone())
                        .or_default()
                        .append(&mut producers);
                }
            }
        }
        if self.recording {
            for (binder, producers) in &exact_callable_arguments {
                let mut producers = producers.clone();
                producers.sort();
                producers.dedup();
                if producers.len() > 1 && template.result_binder.as_ref() != Some(binder) {
                    let message = format!(
                        "call to `{name}` has ambiguous callable producer bodies for one generic binder"
                    );
                    if let Some(site) = self.call_site(source) {
                        self.discovery
                            .graph
                            .opaque_closure_sets
                            .insert(site, message.clone());
                    }
                    self.error(message);
                    return None;
                }
            }
        }
        // During symbolic validation, a direct recursive call sees the same
        // owner-qualified binders on both sides. Unification correctly treats
        // those as already equal and therefore records no substitution. Seed
        // the identity explicitly so the recursive callee's where constraints
        // remain symbolic and can be discharged by the caller's ParamEnv.
        if self.symbolic_validation && self.owner == template.declaration {
            for key in &template.generic_params {
                substitutions.entry(key.clone()).or_insert_with(|| {
                    SpecializationArgument::Type(ProvisionalType::Param(key.clone()))
                });
            }
        }
        // Forwarded generic callbacks often expose the caller's item binder
        // only through an associated `Fn::Output` equality. Rewalking an
        // already-ground caller specialization can therefore infer a nested
        // callee argument as that caller-owned rigid parameter. Resolve such
        // transitive type arguments through the active specialization before
        // constructing the nested request key.
        // Contextual inference may first relate one of this callee's result
        // variables to a temporary variable owned by an enclosing call. A
        // later callback argument can then solve that enclosing variable to a
        // concrete type. Collapse those call-local chains before constructing
        // the key; otherwise an implementation detail such as `commit`'s `T`
        // leaks into the specialization of its nested `attempt_item` call.
        collapse_type_substitution_chains(&mut substitutions);
        if let BodyInstanceKey::Specialization(current) = &self.body_instance
            && let DeclarationKey::Function(current_name) = &current.template
            && let Some(current_template) = self.templates.get(current_name)
        {
            let current_substitutions = substitutions_for_key(current_template, current);
            for argument in substitutions.values_mut() {
                if let SpecializationArgument::Type(ty) = argument
                    && let Some(grounded) =
                        substitute_preserving_missing(ty, &current_substitutions)
                {
                    *ty = grounded;
                }
            }
        }
        let result = substitute(&template.result, &substitutions).and_then(|result| {
            normalize_projection_placeholders(&result, self.trait_db, self.solver_budget)
        });
        if let (Some(expected), Some(result)) = (expected, result.as_ref())
            && ground(expected)
            && expected != result
            && !matches!(result, ProvisionalType::Predefined(name) if name == "Never")
        {
            self.error(format!("call to `{name}` has an ambiguous result"));
            return None;
        }
        for constraint in &template.marker_constraints {
            let constraint_kind = match constraint.polarity {
                GoalPolarity::Positive => "marker constraint",
                GoalPolarity::Negative => "negative marker constraint",
            };
            let constraint_subject = constraint
                .subject_binder
                .clone()
                .map(ProvisionalType::Param)
                .unwrap_or_else(|| constraint.subject.clone());
            let Some(subject) = substitute(&constraint_subject, &substitutions) else {
                if self.symbolic_validation {
                    // Invalid or fixed alias expansion can erase a generic
                    // binder from the symbolic signature while its declared
                    // marker remains in the template. A concrete call still
                    // has to infer and discharge it; symbolic validation must
                    // not replace the source alias diagnostic with a cascade.
                    continue;
                }
                self.error(format!(
                    "{constraint_kind} `{}` at call to `{name}` is unresolved",
                    self.trait_db.trait_display_name(&constraint.trait_key)
                ));
                return None;
            };
            if self
                .trait_db
                .intrinsic_key(IntrinsicRole::Label)
                .is_some_and(|key| key == &constraint.trait_key)
                && let [GenericArg::Type(formal_payload)] = constraint.arguments.as_slice()
            {
                let evidence_payloads = label_payload_type(&subject)
                    .cloned()
                    .into_iter()
                    .chain(
                        self.param_env
                            .matching_argument_lists(
                                constraint.polarity,
                                &constraint.trait_key,
                                &subject,
                            )
                            .into_iter()
                            .filter_map(|arguments| match arguments.as_slice() {
                                [GenericArg::Type(payload)] => Some(payload.clone()),
                                _ => None,
                            }),
                    )
                    .collect::<Vec<_>>();
                for payload in evidence_payloads {
                    let mut trial = substitutions.clone();
                    if unify_inference(formal_payload, &payload, &mutable_inference, &mut trial) {
                        substitutions = trial;
                        break;
                    }
                }
            }
            let exact_argument =
                Self::exact_constraint_argument(&constraint_subject, &substitutions);
            let Some(arguments) = constraint
                .arguments
                .iter()
                .map(|argument| substitute_generic_arg(argument, &substitutions))
                .collect::<Option<Vec<_>>>()
            else {
                self.error(format!(
                    "{constraint_kind} `{}` arguments at call to `{name}` are unresolved",
                    self.trait_db.trait_display_name(&constraint.trait_key)
                ));
                return None;
            };
            let Some(bindings) = constraint
                .bindings
                .iter()
                .map(|binding| {
                    Some(AssociatedValue {
                        item: binding.item.clone(),
                        arguments: binding
                            .arguments
                            .iter()
                            .map(|argument| substitute_generic_arg(argument, &substitutions))
                            .collect::<Option<Vec<_>>>()?,
                        value: substitute(&binding.value, &substitutions)?,
                    })
                })
                .collect::<Option<Vec<_>>>()
            else {
                self.error(format!(
                    "{constraint_kind} `{}` associated equality at call to `{name}` is unresolved",
                    self.trait_db.trait_display_name(&constraint.trait_key)
                ));
                return None;
            };
            if self
                .trait_db
                .intrinsic_key(IntrinsicRole::Label)
                .is_some_and(|key| key == &constraint.trait_key)
            {
                let concrete_label = constraint.polarity == GoalPolarity::Positive
                    && bindings.is_empty()
                    && label_payload_type(&subject).is_some_and(|payload| {
                        arguments.as_slice() == [GenericArg::Type(payload.clone())]
                    });
                let lexical_label = self.param_env.contains_exact(
                    constraint.polarity,
                    &constraint.trait_key,
                    &subject,
                    &arguments,
                    &bindings,
                );
                let proven = concrete_label || lexical_label;
                if proven {
                    continue;
                }
                self.error(format!(
                    "intrinsic Label constraint for `{subject:?}` does not match its destination payload at call to `{name}`",
                ));
                return None;
            }
            if let Some(proven) =
                self.intrinsic_use_evidence(constraint, &subject, &arguments, exact_argument)
            {
                if proven {
                    continue;
                }
                self.error(format!(
                    "intrinsic Use marker constraint for `{subject:?}` does not contain the requested quantity at call to `{name}`",
                ));
                return None;
            }
            let report = self.trait_db.solve_with_key_detailed_with_budget(
                self.solver_budget,
                &self.param_env,
                constraint.polarity,
                &constraint.trait_key,
                &subject,
                &arguments,
                &bindings,
            );
            let detail = report
                .failure
                .as_ref()
                .map(|failure| format!("; {}", failure.diagnostic_text()))
                .unwrap_or_default();
            let failure = match report.result {
                SolveResult::Proven => None,
                SolveResult::Refuted => Some(format!("is explicitly refuted{detail}")),
                SolveResult::NoEvidence if constraint.polarity == GoalPolarity::Negative => {
                    Some(format!("has no explicit negative evidence{detail}"))
                }
                SolveResult::NoEvidence => Some(format!("has no matching implementation{detail}")),
                SolveResult::Ambiguous => Some(format!("is ambiguous or cyclic{detail}")),
                SolveResult::Overflow => Some(format!("exceeded the solver limit{detail}")),
            };
            if let Some(failure) = failure {
                self.error(format!(
                    "{constraint_kind} `{}` for `{subject:?}` {failure}",
                    self.trait_db.trait_display_name(&constraint.trait_key),
                ));
                return None;
            }
        }
        let call_effects = self.specialized_function_effects(name, &substitutions)?;
        self.record_call_effects(source, call_effects);
        if template.generic_params.is_empty() {
            return result;
        }
        if !self.recording {
            return result;
        }
        let arguments = template
            .generic_params
            .iter()
            .map(|param| substitutions.get(param).cloned())
            .collect::<Option<Vec<_>>>();
        let Some(arguments) = arguments else {
            self.error(format!(
                "call to `{name}` leaves generic parameters unresolved"
            ));
            return None;
        };
        if arguments.iter().any(|argument| match argument {
            SpecializationArgument::Type(ty) => !ground(ty),
            SpecializationArgument::Closure(_, shape, captures, _, _, _) => {
                !shape.params.iter().all(ground)
                    || !ground(&shape.result)
                    || captures.iter().any(|capture| !ground(&capture.ty))
            }
            SpecializationArgument::EffectRow(effects) => effects
                .iter()
                .any(|effect| !effect.arguments.iter().all(ground)),
        }) {
            self.error(format!(
                "call to `{name}` is not fully ground: {arguments:?}"
            ));
            return None;
        }
        let key = SpecializationKey {
            template: template.declaration,
            arguments,
        };
        if self.recording {
            if !self.discovery.graph.requests.contains_key(&key)
                && self.has_non_well_founded_request_growth(&key)
            {
                self.error(
                    "recursive specialization is non-well-founded: a descendant request homeomorphically embeds an ancestor while adding type, callable, const, or effect structure",
                );
                return None;
            }
            self.discovery
                .graph
                .requests
                .entry(key.clone())
                .and_modify(|request| request.closures.extend(closures.clone()))
                .or_insert_with(|| SpecializationRequest {
                    key: key.clone(),
                    closures,
                });
            let call_site = self.call_site(source)?;
            self.discovery
                .graph
                .direct_calls
                .insert(call_site.clone(), key.clone());
            self.discovery
                .graph
                .static_closure_bodies
                .extend(static_closure_arguments);
            if let Some(binder) = &template.result_binder
                && let Some(mut producers) = exact_callable_arguments.get(binder).cloned()
            {
                producers.sort();
                producers.dedup();
                let compatible = producers.first().is_some_and(|first| {
                    producers.iter().all(|producer| {
                        compatible_sealed_producer_contracts(
                            &first.shape,
                            &first.captures,
                            &first.param_env,
                            &first.active_labels,
                            &first.static_captures,
                            &producer.shape,
                            &producer.captures,
                            &producer.param_env,
                            &producer.active_labels,
                            &producer.static_captures,
                        )
                    })
                });
                if compatible {
                    if producers.len() == 1 {
                        self.discovery
                            .graph
                            .returned_closures
                            .insert(call_site.clone(), producers.remove(0));
                    } else {
                        self.discovery
                            .graph
                            .returned_closure_sets
                            .insert(call_site.clone(), producers);
                    }
                } else {
                    let message = "VM-sealed generic callable transport has incompatible producer signature/effect, receiver mode, capture layout, or lifetime environment";
                    self.discovery
                        .graph
                        .opaque_closure_sets
                        .insert(call_site.clone(), message.to_owned());
                    self.error(message);
                }
            } else if let Some(binder) = &template.result_binder
                && let Some(SpecializationArgument::Closure(
                    site,
                    shape,
                    captures,
                    environment,
                    active_labels,
                    static_captures,
                )) = substitutions.get(binder)
            {
                self.discovery.graph.returned_closures.insert(
                    call_site.clone(),
                    ClosureRequest {
                        site: site.clone(),
                        shape: shape.clone(),
                        captures: captures.clone(),
                        param_env: environment.clone(),
                        active_labels: active_labels.clone(),
                        static_captures: static_captures.clone(),
                    },
                );
            }
            if let Some((declaration, binders)) = &template.result_nominal_binders {
                let arguments = binders
                    .iter()
                    .map(|binder| match substitutions.get(binder.as_ref()?)? {
                        SpecializationArgument::Type(ty) => {
                            Some(ClosureTupleField::Type(ty.clone()))
                        }
                        SpecializationArgument::Closure(
                            site,
                            shape,
                            captures,
                            environment,
                            active_labels,
                            static_captures,
                        ) => Some(ClosureTupleField::Closure(ClosureRequest {
                            site: site.clone(),
                            shape: shape.clone(),
                            captures: captures.clone(),
                            param_env: environment.clone(),
                            active_labels: active_labels.clone(),
                            static_captures: static_captures.clone(),
                        })),
                        SpecializationArgument::EffectRow(_) => None,
                    })
                    .collect::<Option<Vec<_>>>();
                if let Some(arguments) = arguments
                    && arguments
                        .iter()
                        .any(|argument| matches!(argument, ClosureTupleField::Closure(_)))
                {
                    self.discovery.graph.returned_closure_nominals.insert(
                        call_site.clone(),
                        ClosureNominalInstance {
                            declaration: declaration.clone(),
                            arguments,
                        },
                    );
                }
            }
            if let Some(parent) = &self.parent {
                self.discovery.graph.edges.insert((parent.clone(), key));
            } else {
                self.discovery.graph.roots.insert((self.owner.clone(), key));
            }
        }
        result
    }

    /// Select a generated generic trait-method wire once lexical evidence has
    /// become ground inside an enclosing specialization. Trait normalization
    /// deliberately lowers every implementation method to an ordinary source
    /// function, so returning its name lets `direct_call` reuse the sole
    /// monomorphization, constraint-solving, recursion, and emission path.
    ///
    /// A symbolic receiver or a non-unique match remains deferred. Coherence
    /// makes one structurally matching ground implementation head sufficient;
    /// the subsequent ordinary call still proves all of its where constraints.
    fn ground_deferred_trait_template(&self, deferred: &str, args: &[Expr]) -> Option<String> {
        let rest = deferred.strip_prefix("$trait_deferred$")?;
        let (trait_name, method) = rest.rsplit_once('$')?;
        let prefix = format!("$trait${trait_name}$");
        let suffix = format!("${method}");
        let actuals = args
            .iter()
            .map(|argument| {
                self.obvious_argument_type(argument)
                    .and_then(|(ty, defaulted)| (!defaulted && ground(&ty)).then_some(ty))
            })
            .collect::<Option<Vec<_>>>()?;
        let mut matches = self
            .templates
            .iter()
            .filter(|(name, template)| {
                name.starts_with(&prefix)
                    && name.ends_with(&suffix)
                    && !template.generic_params.is_empty()
                    && template.params.len() == actuals.len()
            })
            .filter_map(|(name, template)| {
                let mutable = template
                    .generic_params
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<_>>();
                let mut substitutions = BTreeMap::new();
                let compatible = template
                    .params
                    .iter()
                    .zip(&actuals)
                    .all(|(formal, actual)| {
                        let effective_actual = match (formal, actual) {
                            (ProvisionalType::Shared(_), ProvisionalType::Unique(referent)) => {
                                ProvisionalType::shared((**referent).clone())
                            }
                            _ => actual.clone(),
                        };
                        unify_inference(formal, &effective_actual, &mutable, &mut substitutions)
                    });
                let ground_substitutions = substitutions.values().all(|argument| match argument {
                    SpecializationArgument::Type(ty) => ground(ty),
                    SpecializationArgument::Closure(_, shape, captures, _, _, _) => {
                        shape.params.iter().all(ground)
                            && ground(&shape.result)
                            && captures.iter().all(|capture| ground(&capture.ty))
                    }
                    SpecializationArgument::EffectRow(effects) => effects
                        .iter()
                        .all(|effect| effect.arguments.iter().all(ground)),
                });
                (compatible
                    && ground_substitutions
                    && template
                        .generic_params
                        .iter()
                        .all(|param| substitutions.contains_key(param)))
                .then(|| name.clone())
            })
            .collect::<BTreeSet<_>>();
        (matches.len() == 1).then(|| matches.pop_first().unwrap())
    }

    /// Type a long source-defined `handle`/pattern chain without consuming one
    /// Rust stack frame per arm. The ordinary bidirectional path remains in
    /// charge of short chains and unresolved/callable results, where sibling
    /// inference and closure-set recording are material. Once the enclosing
    /// result is ground, every arm has the same complete context and can be
    /// checked independently while retaining its exact pattern refinement.
    fn long_ground_refinement_chain(
        &mut self,
        source: &Expr,
        expected: Option<&ProvisionalType>,
    ) -> Option<Option<ProvisionalType>> {
        let expected = expected.filter(|expected| {
            ground(expected) && !matches!(expected, ProvisionalType::Callable(_))
        })?;

        fn transparent_expression(mut expression: &Expr) -> &Expr {
            loop {
                match &expression.kind {
                    ExprKind::Block(statements) | ExprKind::ContextBlock(statements)
                        if matches!(statements.as_slice(), [Stmt::Expr(_)]) =>
                    {
                        let [Stmt::Expr(value)] = statements.as_slice() else {
                            unreachable!()
                        };
                        expression = value;
                    }
                    _ => return expression,
                }
            }
        }

        fn step(expression: &Expr) -> Option<(&Expr, &crate::ast::Pattern, &Expr, &Expr)> {
            let expression = transparent_expression(expression);
            let ExprKind::Call(callee, arguments) = &expression.kind else {
                return None;
            };
            let ExprKind::Variable(else_path) = &callee.kind else {
                return None;
            };
            if else_path.len() != 1 || else_path[0].as_ref() != "else" {
                return None;
            }
            let [conditional, negative] = arguments.as_slice() else {
                return None;
            };
            let ExprKind::Call(if_callee, if_arguments) = &conditional.kind else {
                return None;
            };
            let ExprKind::Variable(if_path) = &if_callee.kind else {
                return None;
            };
            if if_path.len() != 1 || if_path[0].as_ref() != "if" {
                return None;
            }
            let [condition, positive] = if_arguments.as_slice() else {
                return None;
            };
            let ExprKind::Is { subject, pattern } = &condition.kind else {
                return None;
            };
            Some((subject, pattern, positive, negative))
        }

        let mut cursor = source;
        let mut branches = Vec::new();
        while let Some((subject, pattern, positive, negative)) = step(cursor) {
            branches.push((subject, pattern, positive));
            cursor = negative;
        }
        // Below this size the ordinary path is comfortably stack-safe and
        // retaining one implementation avoids perturbing common programs.
        if branches.len() < 32 {
            return None;
        }

        let saved_locals = self.locals.clone();
        let saved_bindings = self.bindings.clone();
        let saved_active_variants = self.active_variants.clone();
        let mut compatible = true;
        let mut inferred = None;
        for (subject, pattern, positive) in branches {
            self.locals = saved_locals.clone();
            self.bindings = saved_bindings.clone();
            self.active_variants = saved_active_variants.clone();
            let Some(subject_ty) = self.expression(subject, None) else {
                compatible = false;
                continue;
            };
            if let PatternKind::Variant { path, .. } = &pattern.kind
                && path.len() == 2
                && let ExprKind::Unary {
                    op: UnaryOp::Dereference,
                    operand,
                } = &subject.kind
                && let ExprKind::Variable(local) = &operand.kind
                && local.len() == 1
            {
                self.active_variants
                    .insert(local[0].to_string(), path[1].clone());
            }
            self.bind_handler_pattern(pattern, &subject_ty);
            let mut branch = self.expression(positive, Some(expected));
            if self.symbolic_validation || self.may_use_bidirectional_result_fallback(positive) {
                branch = branch.or_else(|| Some(expected.clone()));
            }
            match (&inferred, branch) {
                (None, Some(branch)) => inferred = Some(branch),
                (Some(current), Some(branch))
                    if equivalent_specialization_type(current, &branch) =>
                {
                    if !ground(current) {
                        inferred = Some(branch);
                    }
                }
                (Some(ProvisionalType::Predefined(name)), Some(branch)) if name == "Never" => {
                    inferred = Some(branch);
                }
                (Some(_), Some(ProvisionalType::Predefined(name))) if name == "Never" => {}
                _ => compatible = false,
            }
        }
        self.locals = saved_locals.clone();
        self.bindings = saved_bindings.clone();
        self.active_variants = saved_active_variants.clone();
        let mut final_branch = self.expression(cursor, Some(expected));
        if self.symbolic_validation || self.may_use_bidirectional_result_fallback(cursor) {
            final_branch = final_branch.or_else(|| Some(expected.clone()));
        }
        match (&inferred, final_branch) {
            (None, Some(branch)) => inferred = Some(branch),
            (Some(current), Some(branch)) if equivalent_specialization_type(current, &branch) => {
                if !ground(current) {
                    inferred = Some(branch);
                }
            }
            (Some(ProvisionalType::Predefined(name)), Some(branch)) if name == "Never" => {
                inferred = Some(branch);
            }
            (Some(_), Some(ProvisionalType::Predefined(name))) if name == "Never" => {}
            _ => compatible = false,
        }
        self.locals = saved_locals;
        self.bindings = saved_bindings;
        self.active_variants = saved_active_variants;
        if compatible {
            Some(inferred)
        } else {
            self.error("pattern-refined if branches have incompatible result types");
            Some(None)
        }
    }

    fn expression(
        &mut self,
        source: &Expr,
        expected: Option<&ProvisionalType>,
    ) -> Option<ProvisionalType> {
        stacker::maybe_grow(768 * 1024, 16 * 1024 * 1024, || {
            self.expression_inner(source, expected)
        })
    }

    fn expression_inner(
        &mut self,
        source: &Expr,
        expected: Option<&ProvisionalType>,
    ) -> Option<ProvisionalType> {
        if let Some(result) = self.long_ground_refinement_chain(source, expected) {
            return result;
        }
        match &source.kind {
            ExprKind::Unit => Some(ProvisionalType::Predefined("Unit".into())),
            ExprKind::Int(_) => Some(
                expected
                    .filter(|expected| ground(expected))
                    .cloned()
                    .unwrap_or_else(|| ProvisionalType::Predefined("i64".into())),
            ),
            ExprKind::Float(_) => Some(
                expected
                    .filter(|expected| ground(expected))
                    .cloned()
                    .unwrap_or_else(|| ProvisionalType::Predefined("f64".into())),
            ),
            ExprKind::String(_) => Some(ProvisionalType::Predefined("Text".into())),
            ExprKind::Char(_) => Some(ProvisionalType::Predefined("Char".into())),
            ExprKind::Byte(_) => Some(ProvisionalType::Predefined("u8".into())),
            ExprKind::ByteString(_) => Some(ProvisionalType::Predefined("Bytes".into())),
            ExprKind::Move(operand) => {
                if let ExprKind::Call(callee, args) = &operand.kind
                    && let ExprKind::Variable(path) = &callee.kind
                    && path.len() == 1
                {
                    self.direct_call(operand, path[0].as_ref(), args, expected, Some(2))
                } else {
                    self.expression(operand, expected)
                }
            }
            ExprKind::Variable(path) if path.len() == 1 => {
                let binding = self.locals.get(path[0].as_ref()).cloned();
                if let Some(LocalBinding::Closure(closure)) = &binding {
                    let has_unique_capture = closure
                        .captures
                        .iter()
                        .any(|capture| contains_unique_reference_shape(&capture.ty));
                    let exact_sealed_producer = self
                        .discovery
                        .graph
                        .closure_values
                        .values()
                        .any(|producer| producer == closure);
                    if has_unique_capture && !exact_sealed_producer {
                        self.error(
                            "callable closure containing a captured unique reference escapes without exact compiler-sealed producer evidence",
                        );
                        None
                    } else {
                        Some(ProvisionalType::Callable(closure.shape.clone()))
                    }
                } else {
                    match binding {
                        Some(LocalBinding::Type(ty)) => Some(ty),
                        Some(LocalBinding::RecursiveSelf(recursive_self, _)) => {
                            self.error(format!(
                                "recursive callable `{}` may only be invoked directly; its receiver identity cannot escape during initialization",
                                recursive_self.binding
                            ));
                            None
                        }
                        Some(LocalBinding::ClosureTuple(closures)) => Some(ProvisionalType::Tuple(
                            closures
                                .iter()
                                .map(|field| match field {
                                    ClosureTupleField::Type(ty) => ty.clone(),
                                    ClosureTupleField::Closure(closure) => {
                                        ProvisionalType::Callable(closure.shape.clone())
                                    }
                                    ClosureTupleField::ClosureSet(closures) => {
                                        ProvisionalType::Callable(closures[0].shape.clone())
                                    }
                                })
                                .collect(),
                        )),
                        Some(LocalBinding::ClosureNominal(instance)) => {
                            Some(ProvisionalType::Nominal(NominalInstanceKey {
                                declaration: NominalKey(instance.declaration),
                                arguments: instance
                                    .arguments
                                    .into_iter()
                                    .map(|argument| match argument {
                                        ClosureTupleField::Type(ty) => ty,
                                        ClosureTupleField::Closure(closure) => {
                                            ProvisionalType::Callable(closure.shape)
                                        }
                                        ClosureTupleField::ClosureSet(closures) => {
                                            ProvisionalType::Callable(closures[0].shape.clone())
                                        }
                                    })
                                    .collect(),
                            }))
                        }
                        Some(LocalBinding::DeferredFunctionItem(item)) => {
                            self.error(format!(
                                "generic function item `{}` escapes before a concrete callable shape is proven",
                                item.target
                            ));
                            None
                        }
                        Some(LocalBinding::ClosureSet(closures)) => {
                            let first = closures.first()?;
                            closures
                                .iter()
                                .all(|closure| closure.shape == first.shape)
                                .then(|| ProvisionalType::Callable(first.shape.clone()))
                        }
                        Some(LocalBinding::Closure(_)) | None => None,
                    }
                }
            }
            ExprKind::Variable(path) if path.len() == 2 => {
                self.enum_construction(source, path[0].as_ref(), path[1].as_ref(), &[], expected)
            }
            ExprKind::Call(callee, args) => {
                if let ExprKind::LabelReference(label) = &callee.kind {
                    let destination = self
                        .active_labels
                        .get(label.name.as_ref())
                        .and_then(label_payload_type)
                        .cloned();
                    for argument in args.iter() {
                        self.expression(argument, destination.as_ref());
                    }
                    return None;
                }
                // `if(condition) { positive } else { negative }` remains an
                // ordinary library surface, but a pattern-test condition also
                // carries branch-local binders. Plan that composition as one
                // refinement island so the positive block is typed with those
                // binders and no eager closure capture can leak them.
                if let ExprKind::Variable(else_path) = &callee.kind
                    && else_path.len() == 1
                    && else_path[0].as_ref() == "else"
                    && let [if_expression, negative] = args.as_slice()
                    && let ExprKind::Call(if_callee, if_args) = &if_expression.kind
                    && let ExprKind::Variable(if_path) = &if_callee.kind
                    && if_path.len() == 1
                    && if_path[0].as_ref() == "if"
                    && let [condition, positive] = if_args.as_slice()
                    && let ExprKind::Is { subject, pattern } = &condition.kind
                {
                    let subject_ty = self.expression(subject.as_ref(), None)?;
                    // A finite branch set may mix a fully explicit typed
                    // producer with the concise inferred closure surface. The
                    // explicit sibling is an exact bidirectional context for
                    // the inferred producer; both still pass through ordinary
                    // contextual closure planning and the canonical set ABI
                    // comparison below.
                    let sibling_context = expected.is_none().then(|| {
                        self.explicit_closure_result_shape(positive)
                            .or_else(|| self.explicit_closure_result_shape(negative))
                            .map(|shape| ProvisionalType::Callable(Box::new(shape)))
                    });
                    let sibling_context = sibling_context.flatten();
                    let nominal_context = self.structural_else_nominal_context(positive, negative);
                    let obvious_context = self.structural_else_obvious_context(positive, negative);
                    let numeric_expected = expected.filter(|expected| {
                        matches!(expected, ProvisionalType::Predefined(name)
                            if matches!(name.as_str(),
                                "f32" | "f64"
                                | "i8" | "i16" | "i32" | "i64" | "i128" | "isize"
                                | "u8" | "u16" | "u32" | "u64" | "u128" | "usize"))
                    });
                    let branch_expected = if self.symbolic_validation
                        && expected.is_some_and(|expected| !ground(expected))
                    {
                        expected
                    } else {
                        numeric_expected
                            .or(sibling_context.as_ref())
                            .or(nominal_context.as_ref())
                            .or(obvious_context.as_ref())
                            .or(expected)
                    };
                    let explicit_unit_context = obvious_context.as_ref().is_some_and(|context| {
                        context == &ProvisionalType::Predefined("Unit".into())
                    });
                    let saved_locals = self.locals.clone();
                    let saved_bindings = self.bindings.clone();
                    let saved_active_variants = self.active_variants.clone();
                    // Sibling-driven retry can add information only while the
                    // branch result remains unresolved. A fully ground
                    // expected result already supplies the complete context;
                    // snapshotting the whole accumulated discovery graph for
                    // every exhaustive enum arm is pure overhead.
                    let may_retry_with_sibling =
                        branch_expected.is_none_or(|expected| !ground(expected));
                    let discovery_checkpoint =
                        may_retry_with_sibling.then(|| self.discovery.clone());
                    let solver_checkpoint =
                        may_retry_with_sibling.then(|| self.solver_budget.clone());
                    if let PatternKind::Variant { path, .. } = &pattern.kind
                        && path.len() == 2
                        && let ExprKind::Unary {
                            op: UnaryOp::Dereference,
                            operand,
                        } = &subject.kind
                        && let ExprKind::Variable(local) = &operand.kind
                        && local.len() == 1
                    {
                        self.active_variants
                            .insert(local[0].to_string(), path[1].clone());
                    }
                    self.bind_handler_pattern(pattern.as_ref(), &subject_ty);
                    let mut positive_ty = self.expression(positive, branch_expected);
                    let mut positive_closure =
                        matches!(positive_ty, Some(ProvisionalType::Callable(_)))
                            .then(|| self.exact_closure_result(positive))
                            .flatten();
                    self.locals = saved_locals.clone();
                    self.bindings = saved_bindings.clone();
                    self.active_variants = saved_active_variants.clone();
                    let mut negative_ty =
                        self.expression(negative, branch_expected.or(positive_ty.as_ref()));
                    let mut negative_closure =
                        matches!(negative_ty, Some(ProvisionalType::Callable(_)))
                            .then(|| self.exact_closure_result(negative))
                            .flatten();
                    // A refinement branch can expose a projection whose type is
                    // only usable once the sibling branch fixes the enclosing
                    // generic result (for example `Some(&payload.1)` versus
                    // `None`). Retry the island with that context, discarding
                    // every speculative discovery edge and solver step first.
                    if may_retry_with_sibling
                        && positive_ty.is_none()
                        && let Some(negative_result) = negative_ty.as_ref()
                    {
                        *self.discovery = discovery_checkpoint
                            .expect("unresolved refinement keeps discovery checkpoint");
                        *self.solver_budget = solver_checkpoint
                            .expect("unresolved refinement keeps solver checkpoint");
                        self.locals = saved_locals.clone();
                        self.bindings = saved_bindings.clone();
                        self.active_variants = saved_active_variants.clone();
                        if let PatternKind::Variant { path, .. } = &pattern.kind
                            && path.len() == 2
                            && let ExprKind::Unary {
                                op: UnaryOp::Dereference,
                                operand,
                            } = &subject.kind
                            && let ExprKind::Variable(local) = &operand.kind
                            && local.len() == 1
                        {
                            self.active_variants
                                .insert(local[0].to_string(), path[1].clone());
                        }
                        self.bind_handler_pattern(pattern.as_ref(), &subject_ty);
                        positive_ty =
                            self.expression(positive, branch_expected.or(Some(negative_result)));
                        positive_closure =
                            matches!(positive_ty, Some(ProvisionalType::Callable(_)))
                                .then(|| self.exact_closure_result(positive))
                                .flatten();
                        self.locals = saved_locals;
                        self.active_variants = saved_active_variants;
                        self.bindings = saved_bindings;
                        negative_ty =
                            self.expression(negative, branch_expected.or(positive_ty.as_ref()));
                        negative_closure =
                            matches!(negative_ty, Some(ProvisionalType::Callable(_)))
                                .then(|| self.exact_closure_result(negative))
                                .flatten();
                    }
                    // A bounded trait call may deliberately defer while its
                    // receiver is symbolic, a typed global such as the library
                    // Bool values has no local-expression type of its own, and
                    // a statement block ending in explicit `()` retains that
                    // exact result even when one preceding expression cannot
                    // synthesize its type. In all three cases the enclosing
                    // bidirectional context remains authoritative. Restrict
                    // the concrete fallback to syntactically explicit Unit
                    // tails: using an arbitrary expected nominal here would
                    // conceal conflicting constructor payload inference. A
                    // concrete incompatible `Some` result is never replaced.
                    if self.symbolic_validation
                        || explicit_unit_context
                        || self.may_use_bidirectional_result_fallback(positive)
                    {
                        positive_ty = positive_ty.or_else(|| branch_expected.cloned());
                    }
                    if self.symbolic_validation
                        || explicit_unit_context
                        || self.may_use_bidirectional_result_fallback(negative)
                    {
                        negative_ty = negative_ty.or_else(|| branch_expected.cloned());
                    }
                    if self.recording
                        && let (Some(positive), Some(negative)) =
                            (positive_closure, negative_closure)
                    {
                        if positive == negative {
                            if let Some(site) = self.call_site(source) {
                                self.discovery
                                    .graph
                                    .returned_closures
                                    .insert(site, positive);
                            }
                        } else if positive.shape == negative.shape
                            && positive.param_env == negative.param_env
                            && positive.captures.len() == negative.captures.len()
                            && positive
                                .captures
                                .iter()
                                .zip(&negative.captures)
                                .all(|(left, right)| left.ty == right.ty && left.mode == right.mode)
                        {
                            if let Some(site) = self.call_site(source) {
                                let mut producers = vec![positive, negative];
                                producers.sort();
                                producers.dedup();
                                self.discovery
                                    .graph
                                    .returned_closure_sets
                                    .insert(site, producers);
                            }
                        } else {
                            let message = "finite callable producer set has incompatible signature/effect, receiver mode, capture layout, or lifetime environment";
                            if let Some(site) = self.call_site(source) {
                                self.discovery
                                    .graph
                                    .opaque_closure_sets
                                    .insert(site, message.to_owned());
                            }
                            self.error(message);
                        }
                    }
                    match (positive_ty, negative_ty) {
                        (Some(positive), Some(negative))
                            if equivalent_specialization_type(&positive, &negative) =>
                        {
                            Some(if ground(&positive) {
                                positive
                            } else {
                                negative
                            })
                        }
                        (Some(ProvisionalType::Predefined(name)), Some(negative))
                            if name == "Never" =>
                        {
                            Some(negative)
                        }
                        (Some(positive), Some(ProvisionalType::Predefined(name)))
                            if name == "Never" =>
                        {
                            Some(positive)
                        }
                        _ => {
                            self.error(
                                "pattern-refined if branches have incompatible result types",
                            );
                            None
                        }
                    }
                } else if let ExprKind::Variable(else_path) = &callee.kind
                    && else_path.len() == 1
                    && else_path[0].as_ref() == "else"
                    && let [if_expression, negative] = args.as_slice()
                    && let ExprKind::Call(if_callee, if_args) = &if_expression.kind
                    && let ExprKind::Variable(if_path) = &if_callee.kind
                    && if_path.len() == 1
                    && if_path[0].as_ref() == "if"
                    && let [condition, positive] = if_args.as_slice()
                    && let Some(branch_context) = expected
                        .filter(|expected| ground(expected))
                        .cloned()
                        .or_else(|| self.structural_else_nominal_context(positive, negative))
                        .or_else(|| self.structural_else_obvious_context(positive, negative))
                        .or_else(|| expected.cloned())
                {
                    let enclosing_context = expected.cloned();
                    // The branch condition's concrete Bool representation is
                    // irrelevant to the result island. Still walk it to record
                    // dependencies, but do not abandon branch planning merely
                    // because a generic comparison cannot synthesize its type
                    // without an expected context.
                    self.expression(condition, None);
                    // The exact enclosing Result/Option is authoritative for
                    // a branch whose nested handler or late specialization
                    // cannot independently synthesize a result. Any concrete
                    // incompatible type is still compared below, and genuine
                    // nested errors have already been recorded by the walk.
                    let positive_ty = self
                        .expression(positive, Some(&branch_context))
                        .or_else(|| Some(branch_context.clone()));
                    let negative_ty = self
                        .expression(negative, Some(&branch_context))
                        .or_else(|| Some(branch_context.clone()));
                    let branch_result = if enclosing_context.is_some() {
                        // An enclosing result context is authoritative during
                        // discovery. Walking both branches above records all
                        // dependencies and diagnostics; Core lowering performs
                        // the concrete compatibility check. Re-inferring here
                        // can default a contextual numeric constructor before
                        // its `Option`/`Result` type reaches the branch.
                        Some(branch_context)
                    } else {
                        match (positive_ty, negative_ty) {
                            (Some(positive), Some(negative)) if positive == negative => {
                                Some(positive)
                            }
                            (Some(ProvisionalType::Predefined(name)), Some(negative))
                                if name == "Never" =>
                            {
                                Some(negative)
                            }
                            (Some(positive), Some(ProvisionalType::Predefined(name)))
                                if name == "Never" =>
                            {
                                Some(positive)
                            }
                            _ => {
                                self.error(
                                "structural if/else branches have incompatible Result/Option types",
                            );
                                None
                            }
                        }
                    };
                    if branch_result.is_some()
                        && self.recording
                        && let Some(site) = self.call_site(source)
                    {
                        self.discovery.graph.structural_elses.insert(site);
                    }
                    branch_result
                } else if let ExprKind::Variable(path) = &callee.kind
                    && path.len() == 1
                {
                    self.direct_call(source, path[0].as_ref(), args, expected, None)
                } else if let ExprKind::Move(operand) = &callee.kind
                    && let ExprKind::Variable(path) = &operand.kind
                    && path.len() == 1
                {
                    self.direct_call(source, path[0].as_ref(), args, expected, Some(2))
                } else if let ExprKind::Variable(path) = &callee.kind
                    && path.len() == 2
                {
                    self.enum_construction(
                        source,
                        path[0].as_ref(),
                        path[1].as_ref(),
                        args,
                        expected,
                    )
                } else {
                    self.expression(callee, None);
                    args.iter().for_each(|argument| {
                        self.expression(argument, None);
                    });
                    None
                }
            }
            // Trailing library-control blocks are ContextBlocks until expected
            // callable elaboration. They are still lexical bodies for
            // specialization discovery: nested direct calls must contribute
            // dependency edges exactly like ordinary blocks.
            ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                let saved = self.locals.clone();
                let saved_bindings = self.bindings.clone();
                let mut result = Some(ProvisionalType::Predefined("Unit".into()));
                for (index, statement) in statements.iter().enumerate() {
                    match statement {
                        Stmt::Let { name, value, .. } => {
                            let recursive = recursive_closure_binding(value, name);
                            let mut recursive_plan = None;
                            let saved_recursive_self = self.active_recursive_self.clone();
                            if recursive {
                                let ExprKind::TypedClosure { .. } = &value.kind else {
                                    self.error(format!(
                                        "recursive closure `{name}` needs an explicit typed callable signature"
                                    ));
                                    result = None;
                                    self.bindings.insert(name.clone());
                                    continue;
                                };
                                if let Some(shape) = self.typed_closure_shape(value)
                                    && let Some(site) = self.closure_site(value)
                                {
                                    let recursive_self = RecursiveSelf {
                                        binding: name.clone(),
                                        site,
                                    };
                                    self.locals.insert(
                                        name.clone(),
                                        LocalBinding::RecursiveSelf(
                                            recursive_self.clone(),
                                            shape.clone(),
                                        ),
                                    );
                                    self.bindings.insert(name.clone());
                                    self.active_recursive_self = Some(recursive_self.clone());
                                    recursive_plan = Some((recursive_self, shape));
                                }
                            }
                            let closure_tuple = if let ExprKind::Tuple(values) = &value.kind {
                                let fields = values
                                    .iter()
                                    .map(|value| {
                                        let ExprKind::Variable(path) = &value.kind else {
                                            return None;
                                        };
                                        (path.len() == 1)
                                            .then(|| self.locals.get(path[0].as_ref()))
                                            .flatten()
                                            .and_then(|binding| match binding {
                                                LocalBinding::Closure(closure) => Some(
                                                    ClosureTupleField::Closure(closure.clone()),
                                                ),
                                                LocalBinding::ClosureSet(closures) => Some(
                                                    ClosureTupleField::ClosureSet(closures.clone()),
                                                ),
                                                LocalBinding::Type(ty) => {
                                                    Some(ClosureTupleField::Type(ty.clone()))
                                                }
                                                LocalBinding::ClosureTuple(_) => None,
                                                LocalBinding::ClosureNominal(_) => None,
                                                LocalBinding::RecursiveSelf(_, _) => None,
                                                LocalBinding::DeferredFunctionItem(_) => None,
                                            })
                                    })
                                    .collect::<Option<Vec<_>>>();
                                fields.filter(|fields| {
                                    fields.iter().any(|field| {
                                        matches!(
                                            field,
                                            ClosureTupleField::Closure(_)
                                                | ClosureTupleField::ClosureSet(_)
                                        )
                                    })
                                })
                            } else {
                                None
                            };
                            if let Some(item) = self.deferred_function_item(value) {
                                self.active_recursive_self = saved_recursive_self;
                                self.locals
                                    .insert(name.clone(), LocalBinding::DeferredFunctionItem(item));
                                self.bindings.insert(name.clone());
                                result = None;
                                continue;
                            }
                            let callable = match &value.kind {
                                ExprKind::Closure { .. } => self.value_closure(value, None),
                                ExprKind::TypedClosure { .. } => self.typed_value_closure(value),
                                ExprKind::Variable(path) if path.len() == 1 => {
                                    match self.locals.get(path[0].as_ref()).cloned() {
                                        Some(LocalBinding::Closure(closure)) => Some(closure),
                                        _ => None,
                                    }
                                }
                                _ => None,
                            };
                            self.active_recursive_self = saved_recursive_self;
                            if let Some(closure) = callable {
                                if let Some((recursive_self, _)) = &recursive_plan {
                                    self.discovery
                                        .graph
                                        .recursive_closures
                                        .insert(closure.clone(), recursive_self.clone());
                                }
                                if self.recording
                                    && let Some(site) = self.call_site(value)
                                {
                                    self.discovery.graph.erased_callable_aliases.insert(site);
                                }
                                result = Some(ProvisionalType::Callable(closure.shape.clone()));
                                self.locals
                                    .insert(name.clone(), LocalBinding::Closure(closure));
                                self.bindings.insert(name.clone());
                                continue;
                            }
                            if let Some((recursive_self, shape)) = recursive_plan {
                                // A late callable plan (for example one also
                                // capturing a handler resumption) has already
                                // been recorded by contextual discovery.
                                result = Some(ProvisionalType::Callable(shape.clone()));
                                let late_request = self.call_site(value).and_then(|site| {
                                    self.discovery
                                        .graph
                                        .late_closures
                                        .get(&site)
                                        .map(|plan| plan.request.clone())
                                });
                                if let Some(request) = late_request {
                                    self.locals
                                        .insert(name.clone(), LocalBinding::Closure(request));
                                } else {
                                    self.locals.insert(
                                        name.clone(),
                                        LocalBinding::RecursiveSelf(recursive_self, shape),
                                    );
                                }
                                self.bindings.insert(name.clone());
                                continue;
                            }
                            let binding_expected = self.block_binding_expected_type(
                                name,
                                value,
                                &statements[index + 1..],
                                expected,
                            );
                            result = self.expression(value, binding_expected.as_ref());
                            if let Some(closures) = closure_tuple {
                                if self.recording {
                                    self.discovery.graph.closure_tuples.insert(closures.clone());
                                }
                                self.locals
                                    .insert(name.clone(), LocalBinding::ClosureTuple(closures));
                                self.bindings.insert(name.clone());
                                continue;
                            }
                            if let Some(site) = self.call_site(value)
                                && let Some(closures) = self
                                    .discovery
                                    .graph
                                    .returned_closure_sets
                                    .get(&site)
                                    .cloned()
                            {
                                let shape = closures.first().map(|closure| closure.shape.clone());
                                if let Some(shape) = shape {
                                    result = Some(ProvisionalType::Callable(shape));
                                    self.locals
                                        .insert(name.clone(), LocalBinding::ClosureSet(closures));
                                    self.bindings.insert(name.clone());
                                    continue;
                                }
                            }
                            if let Some(site) = self.call_site(value)
                                && let Some(closure) =
                                    self.discovery.graph.returned_closures.get(&site).cloned()
                            {
                                result = Some(ProvisionalType::Callable(closure.shape.clone()));
                                self.locals
                                    .insert(name.clone(), LocalBinding::Closure(closure));
                                self.bindings.insert(name.clone());
                                continue;
                            }
                            if let Some(site) = self.call_site(value)
                                && let Some(instance) = self
                                    .discovery
                                    .graph
                                    .returned_closure_nominals
                                    .get(&site)
                                    .or_else(|| {
                                        self.discovery
                                            .graph
                                            .closure_nominal_constructions
                                            .get(&site)
                                    })
                                    .cloned()
                            {
                                self.locals
                                    .insert(name.clone(), LocalBinding::ClosureNominal(instance));
                                self.bindings.insert(name.clone());
                                continue;
                            }
                            if let Some(ty) = &result {
                                self.locals
                                    .insert(name.clone(), LocalBinding::Type(ty.clone()));
                            }
                            self.bindings.insert(name.clone());
                        }
                        Stmt::Deconstruct {
                            ty, fields, value, ..
                        } => {
                            let tuple_closures = match &value.kind {
                                ExprKind::Variable(path) if path.len() == 1 => {
                                    match self.locals.get(path[0].as_ref()).cloned() {
                                        Some(LocalBinding::ClosureTuple(closures)) => {
                                            Some(closures)
                                        }
                                        _ => None,
                                    }
                                }
                                _ => None,
                            };
                            let closure_nominal = match &value.kind {
                                ExprKind::Variable(path) if path.len() == 1 => {
                                    match self.locals.get(path[0].as_ref()).cloned() {
                                        Some(LocalBinding::ClosureNominal(instance)) => {
                                            Some(instance)
                                        }
                                        _ => None,
                                    }
                                }
                                ExprKind::Move(operand) => match &operand.kind {
                                    ExprKind::Variable(path) if path.len() == 1 => {
                                        match self.locals.get(path[0].as_ref()).cloned() {
                                            Some(LocalBinding::ClosureNominal(instance)) => {
                                                Some(instance)
                                            }
                                            _ => None,
                                        }
                                    }
                                    _ => None,
                                },
                                _ => None,
                            };
                            let value_ty = self.expression(value, None);
                            if let Some(ty) = ty {
                                let instantiated = value_ty.as_ref().and_then(|value_ty| {
                                    let ProvisionalType::Nominal(instance) = value_ty else {
                                        return None;
                                    };
                                    let template = self.nominal_templates.get(ty)?;
                                    (instance.declaration.0 == *ty
                                        && instance.arguments.len() == template.params.len())
                                    .then(|| {
                                        let substitutions = template
                                            .params
                                            .iter()
                                            .cloned()
                                            .zip(
                                                instance
                                                    .arguments
                                                    .iter()
                                                    .cloned()
                                                    .map(SpecializationArgument::Type),
                                            )
                                            .collect::<BTreeMap<_, _>>();
                                        template
                                            .fields
                                            .iter()
                                            .filter_map(|(name, field)| {
                                                substitute(field, &substitutions)
                                                    .map(|field| (name.clone(), field))
                                            })
                                            .collect::<BTreeMap<_, _>>()
                                    })
                                });
                                if let Some(declared) =
                                    self.struct_fields.get(ty).cloned().or(instantiated)
                                {
                                    let exact_fields =
                                        closure_nominal.as_ref().and_then(|instance| {
                                            let template = self.nominal_templates.get(ty)?;
                                            (instance.declaration == *ty
                                                && instance.arguments.len()
                                                    == template.params.len())
                                            .then(|| {
                                                let arguments = template
                                                    .params
                                                    .iter()
                                                    .cloned()
                                                    .zip(instance.arguments.iter().cloned())
                                                    .collect::<BTreeMap<_, _>>();
                                                template
                                                    .fields
                                                    .iter()
                                                    .filter_map(|(name, field)| {
                                                        let ProvisionalType::Param(param) = field
                                                        else {
                                                            return None;
                                                        };
                                                        arguments.get(param).cloned().map(
                                                            |argument| (name.clone(), argument),
                                                        )
                                                    })
                                                    .collect::<BTreeMap<_, _>>()
                                            })
                                        });
                                    for field in fields {
                                        if let (Some(binding), Some(field_ty)) =
                                            (&field.binding, declared.get(&field.field))
                                        {
                                            let exact = exact_fields
                                                .as_ref()
                                                .and_then(|fields| fields.get(&field.field));
                                            self.locals.insert(
                                                binding.clone(),
                                                match exact {
                                                    Some(ClosureTupleField::Closure(closure)) => {
                                                        LocalBinding::Closure(closure.clone())
                                                    }
                                                    Some(ClosureTupleField::ClosureSet(
                                                        closures,
                                                    )) => {
                                                        LocalBinding::ClosureSet(closures.clone())
                                                    }
                                                    Some(ClosureTupleField::Type(_)) | None => {
                                                        LocalBinding::Type(field_ty.clone())
                                                    }
                                                },
                                            );
                                            self.bindings.insert(binding.clone());
                                        }
                                    }
                                }
                            } else if let Some(ProvisionalType::Tuple(elements)) = value_ty {
                                for field in fields {
                                    let offset = field.field.parse::<usize>().ok();
                                    let index = offset.and_then(|offset| {
                                        if field.from_end {
                                            elements.len().checked_sub(offset)
                                        } else {
                                            Some(offset)
                                        }
                                    });
                                    if let (Some(binding), Some(field_ty)) = (
                                        &field.binding,
                                        index.and_then(|index| elements.get(index)),
                                    ) {
                                        let closure = index
                                            .and_then(|index| tuple_closures.as_ref()?.get(index))
                                            .cloned();
                                        self.locals.insert(
                                            binding.clone(),
                                            match closure {
                                                Some(ClosureTupleField::Closure(closure)) => {
                                                    LocalBinding::Closure(closure)
                                                }
                                                Some(ClosureTupleField::ClosureSet(closures)) => {
                                                    LocalBinding::ClosureSet(closures)
                                                }
                                                Some(ClosureTupleField::Type(_)) | None => {
                                                    LocalBinding::Type(field_ty.clone())
                                                }
                                            },
                                        );
                                        self.bindings.insert(binding.clone());
                                    }
                                }
                            }
                            result = Some(ProvisionalType::Predefined("Unit".into()));
                        }
                        Stmt::Expr(value) => {
                            result = self.expression(
                                value,
                                (index + 1 == statements.len())
                                    .then_some(expected)
                                    .flatten(),
                            );
                        }
                        Stmt::Assign {
                            destination, value, ..
                        } => {
                            // Assignment destinations provide an ordinary
                            // expected-type edge. Discover a dereferenced
                            // reference's concrete referent before walking the
                            // RHS so contextual numeric literals inside lazy
                            // `if`/`else` branches do not default to i64.
                            // This is allocation-independent planning only;
                            // Core retains the language's RHS-before-place
                            // runtime evaluation order.
                            let destination_ty = self.assignment_expected_type(destination);
                            self.expression(value, destination_ty.as_ref());
                            result = Some(ProvisionalType::Predefined("Unit".into()));
                        }
                    }
                }
                let unresolved = self
                    .locals
                    .iter()
                    .filter(|(name, _)| !saved.contains_key(*name))
                    .filter_map(|(_, binding)| match binding {
                        LocalBinding::DeferredFunctionItem(item)
                            if !item.provisionally_called || self.recording =>
                        {
                            Some(item.target.clone())
                        }
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                for target in unresolved {
                    self.error(format!(
                        "generic function item `{target}` escapes before a concrete callable shape is proven"
                    ));
                }
                self.locals = saved;
                self.bindings = saved_bindings;
                result
            }
            ExprKind::Unary { op, operand } => match op {
                UnaryOp::BorrowShared => {
                    let referent = expected.and_then(|expected| match expected {
                        ProvisionalType::Shared(referent) => Some(referent.as_ref()),
                        _ => None,
                    });
                    self.expression(operand, referent)
                        .map(ProvisionalType::shared)
                }
                UnaryOp::BorrowUnique => {
                    let referent = expected.and_then(|expected| match expected {
                        ProvisionalType::Unique(referent) => Some(referent.as_ref()),
                        _ => None,
                    });
                    self.expression(operand, referent)
                        .map(ProvisionalType::unique)
                }
                UnaryOp::Dereference => {
                    let referent_context = expected.cloned().map(ProvisionalType::shared);
                    match self.expression(operand, referent_context.as_ref())? {
                        ProvisionalType::Shared(referent) | ProvisionalType::Unique(referent) => {
                            Some(*referent)
                        }
                        _ => expected.cloned(),
                    }
                }
                UnaryOp::Negate => self.expression(operand, expected),
            },
            ExprKind::Binary {
                lhs,
                rhs,
                op:
                    BinaryOp::Eq
                    | BinaryOp::NotEq
                    | BinaryOp::Lt
                    | BinaryOp::LtEq
                    | BinaryOp::Gt
                    | BinaryOp::GtEq,
            } => {
                let hint = [lhs.as_ref(), rhs.as_ref()]
                    .into_iter()
                    .filter_map(|operand| self.obvious_argument_type(operand))
                    .find_map(|(ty, defaulted)| (!defaulted).then_some(ty));
                let operand = self.expression(lhs, hint.as_ref()).or(hint);
                self.expression(rhs, operand.as_ref());
                Some(ProvisionalType::Nominal(NominalInstanceKey {
                    declaration: NominalKey("Result".into()),
                    arguments: vec![
                        ProvisionalType::Predefined("Unit".into()),
                        ProvisionalType::Predefined("Unit".into()),
                    ],
                }))
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                let ty = expected
                    .cloned()
                    .or_else(|| {
                        self.obvious_argument_type(lhs)
                            .filter(|(_, defaulted)| !defaulted)
                            .map(|(ty, _)| ty)
                    })
                    .or_else(|| {
                        self.obvious_argument_type(rhs)
                            .filter(|(_, defaulted)| !defaulted)
                            .map(|(ty, _)| ty)
                    })
                    .unwrap_or_else(|| ProvisionalType::Predefined("i64".into()));
                self.expression(lhs, Some(&ty));
                self.expression(rhs, Some(&ty));
                Some(ty)
            }
            ExprKind::Struct { name, fields } => {
                if let Some(template) = self.nominal_templates.get(name.as_ref()) {
                    // Keep only the supplied field shapes across recursive
                    // discovery. Large declarations should not be copied for
                    // every construction expression.
                    let params = template.params.clone();
                    if params.is_empty() {
                        let expected_fields = fields
                            .iter()
                            .map(|(field, _)| template.fields.get(field).cloned())
                            .collect::<Vec<_>>();
                        for ((_, value), expected_field) in fields.iter().zip(&expected_fields) {
                            self.expression(value, expected_field.as_ref());
                        }
                        return Some(ProvisionalType::Nominal(NominalInstanceKey::monomorphic(
                            name.to_string(),
                        )));
                    }
                    let selected_fields = template
                        .fields
                        .iter()
                        .filter_map(|(field, formal)| {
                            fields
                                .iter()
                                .find(|(supplied, _)| supplied == field)
                                .map(|(_, value)| (value, formal.clone()))
                        })
                        .collect::<Vec<_>>();
                    let values = selected_fields
                        .iter()
                        .map(|(value, formal)| (*value, formal))
                        .collect::<Vec<_>>();
                    return self
                        .infer_nominal_construction(source, name, &params, &values, expected);
                }
                let declared_fields = self.struct_fields.get(name.as_ref()).cloned();
                fields.iter().for_each(|(field, value)| {
                    let expected_field = declared_fields
                        .as_ref()
                        .and_then(|declared| declared.get(field.as_str()));
                    self.expression(value, expected_field);
                });
                Some(
                    expected
                        .filter(|ty| {
                            matches!(ty, ProvisionalType::Nominal(instance)
                            if instance.declaration.0 == name.as_ref())
                        })
                        .cloned()
                        .unwrap_or_else(|| {
                            ProvisionalType::Nominal(NominalInstanceKey::monomorphic(
                                name.to_string(),
                            ))
                        }),
                )
            }
            ExprKind::Field(subject, field) => {
                let refined_variant = match &subject.kind {
                    ExprKind::Variable(path) if path.len() == 1 => {
                        self.active_variants.get(path[0].as_ref()).cloned()
                    }
                    ExprKind::Unary {
                        op: UnaryOp::Dereference,
                        operand,
                    } => match &operand.kind {
                        ExprKind::Variable(path) if path.len() == 1 => {
                            self.active_variants.get(path[0].as_ref()).cloned()
                        }
                        _ => None,
                    },
                    _ => None,
                };
                let subject = self.expression(subject, None)?;
                let subject = match subject {
                    ProvisionalType::Shared(referent) | ProvisionalType::Unique(referent) => {
                        *referent
                    }
                    subject => subject,
                };
                if let ProvisionalType::Tuple(elements) = &subject
                    && let Ok(index) = field.parse::<usize>()
                {
                    return elements.get(index).cloned().or_else(|| expected.cloned());
                }
                let ProvisionalType::Nominal(instance) = subject else {
                    return expected.cloned();
                };
                if let Some(variant) = refined_variant
                    && let Ok(index) = field.parse::<usize>()
                    && let Some(template) = self.nominal_templates.get(&instance.declaration.0)
                    && let Some(formals) = template.variants.get(&variant)
                    && let Some(formal) = formals.get(index)
                    && template.params.len() == instance.arguments.len()
                {
                    let substitutions = template
                        .params
                        .iter()
                        .cloned()
                        .zip(
                            instance
                                .arguments
                                .iter()
                                .cloned()
                                .map(SpecializationArgument::Type),
                        )
                        .collect();
                    return substitute(formal, &substitutions).or_else(|| expected.cloned());
                }
                if let Some(template) = self.nominal_templates.get(&instance.declaration.0)
                    && let Some(formal) = template.fields.get(field)
                    && template.params.len() == instance.arguments.len()
                {
                    let substitutions = template
                        .params
                        .iter()
                        .cloned()
                        .zip(
                            instance
                                .arguments
                                .iter()
                                .cloned()
                                .map(SpecializationArgument::Type),
                        )
                        .collect();
                    return substitute(formal, &substitutions).or_else(|| expected.cloned());
                }
                self.struct_fields
                    .get(&instance.declaration.0)
                    .and_then(|fields| fields.get(field.as_str()))
                    .cloned()
                    .or_else(|| expected.cloned())
            }
            ExprKind::List(values) => {
                values.iter().for_each(|value| {
                    self.expression(value, None);
                });
                None
            }
            ExprKind::Tuple(values) => {
                let expected = expected.and_then(|expected| match expected {
                    ProvisionalType::Tuple(elements) if elements.len() == values.len() => {
                        Some(elements)
                    }
                    _ => None,
                });
                Some(ProvisionalType::Tuple(
                    values
                        .iter()
                        .enumerate()
                        .map(|(index, value)| {
                            self.expression(value, expected.and_then(|types| types.get(index)))
                        })
                        .collect::<Option<Vec<_>>>()?,
                ))
            }
            ExprKind::Perform {
                effect,
                operation,
                args,
            } => {
                let shape = self.operation_at_for_args(source.span, effect, operation, args);
                for (index, argument) in args.iter().enumerate() {
                    self.expression(
                        argument,
                        shape.as_ref().and_then(|shape| shape.params.get(index)),
                    );
                }
                shape
                    .map(|shape| shape.result)
                    .or_else(|| expected.cloned())
            }
            ExprKind::Handle {
                computation,
                clauses,
            } => {
                let handled_operation = match &computation.kind {
                    ExprKind::Perform {
                        effect,
                        operation,
                        args,
                    } => self
                        .operation_at(computation.span, effect, operation)
                        .filter(|shape| !shape.operation_params.is_empty())
                        .and_then(|_| {
                            self.operation_at_for_args(computation.span, effect, operation, args)
                        })
                        .map(|shape| (effect.to_string(), operation.to_string(), shape)),
                    _ => None,
                };
                let outer_locals = self.locals.clone();
                let outer_bindings = self.bindings.clone();
                let outer_active_variants = self.active_variants.clone();
                // Library boolean control lowers `if (*value is Enum::Case)`
                // through a one-operation handler.  The operation's positive
                // `Result::Ok` clause retains the same variant proof as the
                // structural refinement form; preserving it here lets generic
                // payload projections infer their exact type without turning
                // the clause into an eager/contextual closure.
                let handled_variant_refinement = match &computation.kind {
                    ExprKind::Perform { args, .. } => args.first().and_then(|argument| {
                        let ExprKind::Is { subject, pattern } = &argument.kind else {
                            return None;
                        };
                        let PatternKind::Variant { path, .. } = &pattern.kind else {
                            return None;
                        };
                        let ExprKind::Unary {
                            op: UnaryOp::Dereference,
                            operand,
                        } = &subject.kind
                        else {
                            return None;
                        };
                        let ExprKind::Variable(local) = &operand.kind else {
                            return None;
                        };
                        (local.len() == 1 && path.len() == 2)
                            .then(|| (local[0].to_string(), path[1].clone()))
                    }),
                    _ => None,
                };
                let computation_result = self.expression(computation, expected);
                self.locals = outer_locals.clone();
                self.bindings = outer_bindings.clone();
                self.active_variants = outer_active_variants.clone();
                let branches = clauses
                    .iter()
                    .map(|clause| &clause.body)
                    .collect::<Vec<_>>();
                let structural_handler_result = self.structural_nominal_context(&branches);
                let mut handler_result =
                    expected.cloned().or(structural_handler_result).or_else(|| {
                        computation_result.filter(|candidate| {
                            candidate != &ProvisionalType::Predefined("Never".into())
                        })
                    });
                if handler_result.is_none() {
                    for defaulting in [false, true] {
                        if let Some((candidate, _)) = clauses.iter().find_map(|clause| {
                            self.obvious_argument_type(&clause.body)
                                .filter(|(_, is_default)| *is_default == defaulting)
                        }) {
                            handler_result = Some(candidate);
                            break;
                        }
                    }
                }
                for clause in clauses.iter() {
                    let saved = self.locals.clone();
                    let saved_bindings = self.bindings.clone();
                    let saved_active_variants = self.active_variants.clone();
                    let operation = handled_operation
                        .as_ref()
                        .filter(|(effect, operation, _)| {
                            effect == &clause.effect && operation == &clause.operation
                        })
                        .map(|(_, _, shape)| shape.clone())
                        .or_else(|| {
                            self.operation_at(clause.span, &clause.effect, &clause.operation)
                        });
                    if let Some(operation) = &operation {
                        for (pattern, ty) in clause.patterns.iter().zip(&operation.params) {
                            self.bind_handler_pattern(pattern, ty);
                        }
                    } else {
                        for pattern in &clause.patterns {
                            if let PatternKind::Binding(name) = &pattern.kind {
                                self.bindings.insert(name.clone());
                            }
                        }
                    }
                    if let Some((local, variant)) = &handled_variant_refinement
                        && clause.patterns.first().is_some_and(|pattern| {
                            matches!(&pattern.kind, PatternKind::Variant { path, .. }
                                if path.as_slice() == ["Result", "Ok"])
                        })
                    {
                        self.active_variants.insert(local.clone(), variant.clone());
                    }
                    if let Some(resumption) = &clause.resumption {
                        if let (Some(operation), Some(handler_result)) =
                            (operation.as_ref(), handler_result.as_ref())
                        {
                            self.locals.insert(
                                resumption.clone(),
                                LocalBinding::Type(ProvisionalType::Callable(Box::new(
                                    CallableShape {
                                        params: vec![operation.result.clone()],
                                        result: handler_result.clone(),
                                        effects: vec![],
                                        effect_tail: None,
                                        infer_effects: false,
                                    },
                                ))),
                            );
                        }
                        self.bindings.insert(resumption.clone());
                    }
                    let clause_result = self.expression(&clause.body, handler_result.as_ref());
                    if handler_result.is_none()
                        && let Some(candidate) = clause_result
                        && candidate != ProvisionalType::Predefined("Never".into())
                    {
                        handler_result = Some(candidate);
                    }
                    self.locals = saved;
                    self.bindings = saved_bindings;
                    self.active_variants = saved_active_variants;
                }
                handler_result
            }
            ExprKind::Closure { .. } => {
                let expected = expected.and_then(|expected| match expected {
                    ProvisionalType::Callable(shape) => Some(shape.as_ref()),
                    _ => None,
                });
                self.value_closure(source, expected)
                    .map(|request| ProvisionalType::Callable(request.shape.clone()))
            }
            // A typed anonymous callable never needs contextual inference: its
            // explicit signature is its shape.
            ExprKind::TypedClosure { .. } => self
                .typed_value_closure(source)
                .map(|request| ProvisionalType::Callable(request.shape.clone())),
            ExprKind::LabelDestination { label, ty, body } => {
                let result = ty
                    .as_deref()
                    .and_then(|ty| self.source_type(ty))
                    // An inferred label is an ordinary contextual expression:
                    // its destination payload is the surrounding expected
                    // type, not unconditionally Unit. This matters when a
                    // Result-returning iterator callback uses a local branded
                    // `try`; the callback signature fixes the whole
                    // Result<T, E> even though the label has no annotation.
                    .or_else(|| expected.cloned())
                    .unwrap_or_else(|| ProvisionalType::Predefined("Unit".into()));
                if self.recording
                    && let Some(site) = self.call_site(source)
                {
                    self.discovery
                        .graph
                        .label_results
                        .insert(site, result.clone());
                }
                let label_type = label_provisional_type(&self.owner, label, result.clone());
                let previous = self
                    .active_labels
                    .insert(label.name.to_string(), label_type);
                let body_result = self.expression(body, Some(&result));
                if let Some(previous) = previous {
                    self.active_labels.insert(label.name.to_string(), previous);
                } else {
                    self.active_labels.remove(label.name.as_ref());
                }
                body_result.or(Some(result))
            }
            ExprKind::Is { subject, .. } => {
                self.expression(subject, None);
                Some(ProvisionalType::Nominal(NominalInstanceKey {
                    declaration: NominalKey("Result".into()),
                    arguments: vec![
                        ProvisionalType::Predefined("Unit".into()),
                        ProvisionalType::Predefined("Unit".into()),
                    ],
                }))
            }
            ExprKind::LabelReference(label) => self.active_labels.get(label.name.as_ref()).cloned(),
            ExprKind::Variable(_) => None,
            ExprKind::Resume { resumption, value } => {
                let local = match &resumption.kind {
                    ExprKind::Variable(path) => Some(path),
                    ExprKind::Move(inner) => match &inner.kind {
                        ExprKind::Variable(path) => Some(path),
                        _ => None,
                    },
                    _ => None,
                };
                let shape = match local {
                    Some(path) if path.len() == 1 => {
                        self.locals.get(path[0].as_ref()).and_then(|binding| {
                            let LocalBinding::Type(ProvisionalType::Callable(shape)) = binding
                            else {
                                return None;
                            };
                            Some(shape.clone())
                        })
                    }
                    _ => None,
                };
                self.expression(resumption, None);
                if let Some(value) = value {
                    self.expression(
                        value,
                        shape
                            .as_deref()
                            .and_then(|shape| shape.params.first())
                            .or(expected),
                    );
                }
                shape
                    .map(|shape| shape.result.clone())
                    .or_else(|| expected.cloned())
            }
            ExprKind::Cancel { resumption } => {
                self.expression(resumption, None);
                Some(ProvisionalType::Predefined("Never".into()))
            }
            ExprKind::TailResume { resumption, value } => {
                let local = match &resumption.kind {
                    ExprKind::Variable(path) => Some(path),
                    ExprKind::Move(inner) => match &inner.kind {
                        ExprKind::Variable(path) => Some(path),
                        _ => None,
                    },
                    _ => None,
                };
                let input = match local {
                    Some(path) if path.len() == 1 => {
                        self.locals.get(path[0].as_ref()).and_then(|binding| {
                            let LocalBinding::Type(ProvisionalType::Callable(shape)) = binding
                            else {
                                return None;
                            };
                            shape.params.first().cloned()
                        })
                    }
                    _ => None,
                };
                self.expression(resumption, None);
                if let Some(value) = value {
                    self.expression(value, input.as_ref());
                }
                Some(ProvisionalType::Predefined("Never".into()))
            }
        }
    }
}

pub(crate) fn expression_ordinal_maps(
    root: &Expr,
) -> (BTreeMap<usize, u32>, BTreeMap<(usize, usize), u32>) {
    let mut next = 0;
    let mut ordinals = BTreeMap::new();
    let mut spans = BTreeMap::new();
    let mut ambiguous_spans = BTreeSet::new();
    let _: ControlFlow<()> = visit_expr_preorder(root, |expression| {
        ordinals.insert(std::ptr::from_ref(expression) as usize, next);
        let span = (expression.span.start, expression.span.end);
        if spans.insert(span, next).is_some() {
            ambiguous_spans.insert(span);
        }
        next += 1;
        ControlFlow::Continue(())
    });
    for span in ambiguous_spans {
        spans.remove(&span);
    }
    (ordinals, spans)
}

pub(crate) fn expression_ordinals(root: &Expr) -> BTreeMap<usize, u32> {
    expression_ordinal_maps(root).0
}

fn expression_at_ordinal(root: &Expr, target: u32) -> Option<&Expr> {
    let mut next = 0;
    match visit_expr_preorder(root, |expression| {
        let ordinal = next;
        next += 1;
        if ordinal == target {
            ControlFlow::Break(expression)
        } else {
            ControlFlow::Continue(())
        }
    }) {
        ControlFlow::Break(expression) => Some(expression),
        ControlFlow::Continue(()) => None,
    }
}

pub(crate) fn body_root<'a>(program: &'a Program, owner: &DeclarationKey) -> Option<&'a Expr> {
    match owner {
        DeclarationKey::Function(name) => program
            .functions
            .iter()
            .find(|function| &function.name == name)
            .map(|function| &function.body)
            .or_else(|| {
                let target = name.strip_prefix("$drop$")?;
                program
                    .drops
                    .iter()
                    .find(|declaration| declaration.target == target)
                    .map(|declaration| &declaration.body)
            }),
        DeclarationKey::Global(name) => program
            .globals
            .iter()
            .find(|global| &global.name == name)
            .map(|global| &global.value),
    }
}

pub(crate) fn closure_body<'a>(
    program: &'a Program,
    request: &ClosureRequest,
    kind: ClosureBodyKind,
) -> Option<(Vec<String>, &'a Expr)> {
    let root = body_root(program, &request.site.owner)?;
    let expression = expression_at_ordinal(root, request.site.ordinal)?;
    match (&expression.kind, kind) {
        (ExprKind::Closure { params, body }, ClosureBodyKind::Explicit) => {
            Some((params.iter().map(ToString::to_string).collect(), body))
        }
        (ExprKind::TypedClosure { params, body, .. }, ClosureBodyKind::Explicit) => Some((
            params.iter().map(|param| param.name.clone()).collect(),
            body,
        )),
        (ExprKind::Block(_) | ExprKind::ContextBlock(_), ClosureBodyKind::ContextualBlock) => {
            Some((vec![], expression))
        }
        _ => None,
    }
}

pub(crate) fn substitutions_for_key(
    template: &FunctionTemplate,
    key: &SpecializationKey,
) -> BTreeMap<GenericParamKey, SpecializationArgument> {
    template
        .generic_params
        .iter()
        .cloned()
        .zip(key.arguments.iter().cloned())
        .collect()
}

pub(crate) fn callable_effect_escapes<F>(
    program: &Program,
    function: &crate::ast::Function,
    parameter: &str,
    effect: &crate::compiler_typeck::CallableEffect,
    handler_closes: &F,
) -> bool
where
    F: Fn(&[crate::ast::HandlerClause], &crate::compiler_typeck::CallableEffect) -> bool,
{
    #[derive(Clone, Copy, Debug, Default)]
    struct ValueFlow {
        tracked: bool,
        escapes: bool,
    }

    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    struct Summary {
        escapes: bool,
        returns: bool,
    }

    fn bind_pattern(pattern: &crate::ast::Pattern, locals: &mut BTreeMap<String, bool>) {
        match &pattern.kind {
            PatternKind::Binding(name) => {
                locals.insert(name.clone(), false);
            }
            PatternKind::Variant { fields, .. } => {
                for field in fields {
                    bind_pattern(field, locals);
                }
            }
            PatternKind::Tuple { elements, .. } => {
                for element in elements {
                    bind_pattern(element, locals);
                }
            }
            PatternKind::Struct { fields, .. } => {
                for field in fields {
                    bind_pattern(&field.pattern, locals);
                }
            }
            PatternKind::Wildcard
            | PatternKind::Unit
            | PatternKind::Int(_)
            | PatternKind::Float(_)
            | PatternKind::String(_)
            | PatternKind::Char(_)
            | PatternKind::Byte(_) => {}
        }
    }

    fn visit<F>(
        expression: &Expr,
        effect: &crate::compiler_typeck::CallableEffect,
        handled: bool,
        locals: &mut BTreeMap<String, bool>,
        functions: &BTreeMap<&str, &crate::ast::Function>,
        summaries: &BTreeMap<(&str, usize), Summary>,
        handler_closes: &F,
    ) -> ValueFlow
    where
        F: Fn(&[crate::ast::HandlerClause], &crate::compiler_typeck::CallableEffect) -> bool,
    {
        match &expression.kind {
            ExprKind::Call(callee, arguments) => {
                let callee_flow = visit(
                    callee,
                    effect,
                    handled,
                    locals,
                    functions,
                    summaries,
                    handler_closes,
                );
                let argument_flows = arguments
                    .iter()
                    .map(|argument| {
                        visit(
                            argument,
                            effect,
                            handled,
                            locals,
                            functions,
                            summaries,
                            handler_closes,
                        )
                    })
                    .collect::<Vec<_>>();
                let mut escapes =
                    callee_flow.escapes || argument_flows.iter().any(|argument| argument.escapes);
                let mut tracked = false;

                // Calling the tracked callable performs its row. Merely naming,
                // aliasing, or forwarding it does not.
                if callee_flow.tracked && !handled {
                    escapes = true;
                }

                // A named higher-order call escapes the effect exactly when the
                // corresponding formal's least-fixed-point summary says that it
                // is eventually invoked outside a matching handler.
                if let ExprKind::Variable(path) = &callee.kind
                    && path.len() == 1
                {
                    let name = path[0].as_ref();
                    if !locals.contains_key(name)
                        && let Some(target) = functions.get(name)
                    {
                        for (index, argument) in argument_flows.iter().enumerate() {
                            if argument.tracked {
                                let summary = summaries
                                    .get(&(target.name.as_str(), index))
                                    .copied()
                                    .unwrap_or_default();
                                escapes |= summary.escapes && !handled;
                                tracked |= summary.returns;
                            }
                        }
                    }
                }
                ValueFlow { tracked, escapes }
            }
            ExprKind::Handle {
                computation,
                clauses,
            } => {
                let nested = handled || handler_closes(clauses, effect);
                let computation = visit(
                    computation,
                    effect,
                    nested,
                    &mut locals.clone(),
                    functions,
                    summaries,
                    handler_closes,
                );
                let mut escapes = computation.escapes;
                let mut tracked = computation.tracked;
                for clause in clauses.iter() {
                    let mut clause_locals = locals.clone();
                    for pattern in &clause.patterns {
                        bind_pattern(pattern, &mut clause_locals);
                    }
                    if let Some(resumption) = &clause.resumption {
                        clause_locals.insert(resumption.clone(), false);
                    }
                    let clause = visit(
                        &clause.body,
                        effect,
                        nested,
                        &mut clause_locals,
                        functions,
                        summaries,
                        handler_closes,
                    );
                    escapes |= clause.escapes;
                    tracked |= clause.tracked;
                }
                ValueFlow { tracked, escapes }
            }
            ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                let mut block_locals = locals.clone();
                let mut result = ValueFlow::default();
                for (index, statement) in statements.iter().enumerate() {
                    let last = index + 1 == statements.len();
                    match statement {
                        Stmt::Let { name, value, .. } => {
                            let value = visit(
                                value,
                                effect,
                                handled,
                                &mut block_locals,
                                functions,
                                summaries,
                                handler_closes,
                            );
                            result.escapes |= value.escapes;
                            block_locals.insert(name.clone(), value.tracked);
                            result.tracked = false;
                        }
                        Stmt::Deconstruct { fields, value, .. } => {
                            let value = visit(
                                value,
                                effect,
                                handled,
                                &mut block_locals,
                                functions,
                                summaries,
                                handler_closes,
                            );
                            result.escapes |= value.escapes;
                            for field in fields {
                                if let Some(binding) = &field.binding {
                                    block_locals.insert(binding.clone(), false);
                                }
                            }
                            result.tracked = false;
                        }
                        Stmt::Expr(value) => {
                            let value = visit(
                                value,
                                effect,
                                handled,
                                &mut block_locals,
                                functions,
                                summaries,
                                handler_closes,
                            );
                            result.escapes |= value.escapes;
                            result.tracked = last && value.tracked;
                        }
                        Stmt::Assign {
                            destination, value, ..
                        } => {
                            let value = visit(
                                value,
                                effect,
                                handled,
                                &mut block_locals,
                                functions,
                                summaries,
                                handler_closes,
                            );
                            result.escapes |= value.escapes;
                            match &destination.kind {
                                AssignmentPlaceKind::Local { name, fields }
                                    if fields.is_empty() =>
                                {
                                    block_locals.insert(name.to_string(), value.tracked);
                                }
                                AssignmentPlaceKind::Dereference { reference, .. } => {
                                    let reference = visit(
                                        reference,
                                        effect,
                                        handled,
                                        &mut block_locals,
                                        functions,
                                        summaries,
                                        handler_closes,
                                    );
                                    result.escapes |= reference.escapes;
                                }
                                AssignmentPlaceKind::Local { .. } => {}
                            }
                            result.tracked = false;
                        }
                    }
                }
                result
            }
            ExprKind::List(values) | ExprKind::Tuple(values) => ValueFlow {
                tracked: false,
                escapes: values.iter().any(|value| {
                    visit(
                        value,
                        effect,
                        handled,
                        locals,
                        functions,
                        summaries,
                        handler_closes,
                    )
                    .escapes
                }),
            },
            ExprKind::Struct { fields, .. } => ValueFlow {
                tracked: false,
                escapes: fields.iter().any(|(_, value)| {
                    visit(
                        value,
                        effect,
                        handled,
                        locals,
                        functions,
                        summaries,
                        handler_closes,
                    )
                    .escapes
                }),
            },
            // Constructing a closure is pure, but the value still transports
            // any tracked callable captured by its body. Charge the effect
            // only when a downstream callable summary invokes this closure.
            ExprKind::Closure { params, body } => {
                let mut closure_locals = locals.clone();
                for parameter in params.iter() {
                    closure_locals.insert(parameter.to_string(), false);
                }
                let body = visit(
                    body,
                    effect,
                    handled,
                    &mut closure_locals,
                    functions,
                    summaries,
                    handler_closes,
                );
                ValueFlow {
                    tracked: body.tracked || body.escapes,
                    escapes: false,
                }
            }
            ExprKind::TypedClosure { params, body, .. } => {
                let mut closure_locals = locals.clone();
                for parameter in params.iter() {
                    closure_locals.insert(parameter.name.clone(), false);
                }
                let body = visit(
                    body,
                    effect,
                    handled,
                    &mut closure_locals,
                    functions,
                    summaries,
                    handler_closes,
                );
                ValueFlow {
                    tracked: body.tracked || body.escapes,
                    escapes: false,
                }
            }
            ExprKind::Move(value)
            | ExprKind::Field(value, _)
            | ExprKind::Unary { operand: value, .. } => visit(
                value,
                effect,
                handled,
                locals,
                functions,
                summaries,
                handler_closes,
            ),
            ExprKind::Perform { args, .. } => ValueFlow {
                tracked: false,
                escapes: args.iter().any(|value| {
                    visit(
                        value,
                        effect,
                        handled,
                        locals,
                        functions,
                        summaries,
                        handler_closes,
                    )
                    .escapes
                }),
            },
            ExprKind::Binary { lhs, rhs, .. } => {
                let lhs = visit(
                    lhs,
                    effect,
                    handled,
                    locals,
                    functions,
                    summaries,
                    handler_closes,
                );
                let rhs = visit(
                    rhs,
                    effect,
                    handled,
                    locals,
                    functions,
                    summaries,
                    handler_closes,
                );
                ValueFlow {
                    tracked: false,
                    escapes: lhs.escapes || rhs.escapes,
                }
            }
            ExprKind::LabelDestination { body, .. } => visit(
                body,
                effect,
                handled,
                locals,
                functions,
                summaries,
                handler_closes,
            ),
            ExprKind::Is { subject, .. } => ValueFlow {
                tracked: false,
                escapes: visit(
                    subject,
                    effect,
                    handled,
                    locals,
                    functions,
                    summaries,
                    handler_closes,
                )
                .escapes,
            },
            ExprKind::Variable(path) if path.len() == 1 => ValueFlow {
                tracked: locals.get(path[0].as_ref()).copied().unwrap_or(false),
                escapes: false,
            },
            ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Char(_)
            | ExprKind::Byte(_)
            | ExprKind::ByteString(_)
            | ExprKind::String(_)
            | ExprKind::Variable(_) => ValueFlow::default(),
            ExprKind::LabelReference(_) => ValueFlow::default(),
            ExprKind::Resume { resumption, value } => {
                let resumption = visit(
                    resumption,
                    effect,
                    handled,
                    locals,
                    functions,
                    summaries,
                    handler_closes,
                );
                let mut result = value.as_deref().map_or_else(ValueFlow::default, |value| {
                    visit(
                        value,
                        effect,
                        handled,
                        locals,
                        functions,
                        summaries,
                        handler_closes,
                    )
                });
                result.escapes |= resumption.escapes;
                result
            }
            ExprKind::TailResume { resumption, value } => {
                let mut escapes = visit(
                    resumption,
                    effect,
                    handled,
                    locals,
                    functions,
                    summaries,
                    handler_closes,
                )
                .escapes;
                if let Some(value) = value {
                    escapes |= visit(
                        value,
                        effect,
                        handled,
                        locals,
                        functions,
                        summaries,
                        handler_closes,
                    )
                    .escapes;
                }
                ValueFlow {
                    tracked: false,
                    escapes,
                }
            }
            ExprKind::Cancel { resumption } => ValueFlow {
                tracked: false,
                escapes: visit(
                    resumption,
                    effect,
                    handled,
                    locals,
                    functions,
                    summaries,
                    handler_closes,
                )
                .escapes,
            },
        }
    }

    let functions = program
        .functions
        .iter()
        .map(|function| (function.name.as_str(), function))
        .collect::<BTreeMap<_, _>>();
    let mut summaries = functions
        .values()
        .flat_map(|function| {
            (0..function.params.len())
                .map(move |index| ((function.name.as_str(), index), Summary::default()))
        })
        .collect::<BTreeMap<_, _>>();

    loop {
        let previous = summaries.clone();
        for candidate in functions.values() {
            for (index, parameter) in candidate.params.iter().enumerate() {
                let mut locals = candidate
                    .params
                    .iter()
                    .map(|parameter| (parameter.name.clone(), false))
                    .collect::<BTreeMap<_, _>>();
                locals.insert(parameter.name.clone(), true);
                let escapes = visit(
                    &candidate.body,
                    effect,
                    false,
                    &mut locals,
                    &functions,
                    &previous,
                    handler_closes,
                );
                summaries.insert(
                    (candidate.name.as_str(), index),
                    Summary {
                        escapes: escapes.escapes,
                        returns: escapes.tracked,
                    },
                );
            }
        }
        if summaries == previous {
            break;
        }
    }

    let Some(index) = function
        .params
        .iter()
        .position(|candidate| candidate.name == parameter)
    else {
        return false;
    };
    summaries
        .get(&(function.name.as_str(), index))
        .is_some_and(|summary| summary.escapes)
}

#[cfg(test)]
pub(crate) fn discover(program: &Program) -> Discovery {
    let trait_db = TraitDb::build(program).unwrap_or_default();
    discover_with_traits(program, &trait_db)
}

pub(crate) fn merge_drop_reachable(base: &mut Discovery, discovered: &Discovery) -> bool {
    let mut reachable_keys = discovered
        .graph
        .direct_calls
        .iter()
        .filter(|(site, _)| matches!(site.body, BodyInstanceKey::Drop(_)))
        .map(|(_, key)| key.clone())
        .collect::<BTreeSet<_>>();
    let mut reachable_closures = discovered
        .graph
        .callable_calls
        .iter()
        .filter(|(site, _)| matches!(site.body, BodyInstanceKey::Drop(_)))
        .map(|(_, closure)| closure.clone())
        .collect::<BTreeSet<_>>();
    loop {
        let before = (reachable_keys.len(), reachable_closures.len());
        for (parent, child) in &discovered.graph.edges {
            if reachable_keys.contains(parent) {
                reachable_keys.insert(child.clone());
            }
        }
        for key in reachable_keys.clone() {
            if let Some(request) = discovered.graph.requests.get(&key) {
                reachable_closures.extend(request.closures.iter().cloned());
            }
        }
        for (site, key) in &discovered.graph.direct_calls {
            let body_reachable = match &site.body {
                BodyInstanceKey::Drop(_) => true,
                BodyInstanceKey::Specialization(parent) => reachable_keys.contains(parent),
                BodyInstanceKey::Closure(closure) => reachable_closures.contains(closure),
                BodyInstanceKey::Root(_) => false,
            };
            if body_reachable {
                reachable_keys.insert(key.clone());
            }
        }
        for (site, closure) in &discovered.graph.callable_calls {
            let body_reachable = match &site.body {
                BodyInstanceKey::Drop(_) => true,
                BodyInstanceKey::Specialization(parent) => reachable_keys.contains(parent),
                BodyInstanceKey::Closure(closure) => reachable_closures.contains(closure),
                BodyInstanceKey::Root(_) => false,
            };
            if body_reachable {
                reachable_closures.insert(closure.clone());
            }
        }
        for (site, plan) in &discovered.graph.static_closure_bodies {
            let body_reachable = match &site.body {
                BodyInstanceKey::Drop(_) => true,
                BodyInstanceKey::Specialization(parent) => reachable_keys.contains(parent),
                BodyInstanceKey::Closure(closure) => reachable_closures.contains(closure),
                BodyInstanceKey::Root(_) => false,
            };
            if body_reachable {
                reachable_closures.insert(plan.request.clone());
            }
        }
        if (reachable_keys.len(), reachable_closures.len()) == before {
            break;
        }
    }

    let before = base.clone();
    for key in &reachable_keys {
        if let Some(request) = discovered.graph.requests.get(key) {
            base.graph
                .requests
                .entry(key.clone())
                .and_modify(|existing| {
                    existing.closures.extend(request.closures.iter().cloned());
                })
                .or_insert_with(|| request.clone());
        }
    }
    base.graph.roots.extend(
        discovered
            .graph
            .roots
            .iter()
            .filter(|(_, key)| reachable_keys.contains(key))
            .cloned(),
    );
    base.graph.edges.extend(
        discovered
            .graph
            .edges
            .iter()
            .filter(|(parent, child)| {
                reachable_keys.contains(parent) && reachable_keys.contains(child)
            })
            .cloned(),
    );
    base.graph.direct_calls.extend(
        discovered
            .graph
            .direct_calls
            .iter()
            .filter(|(site, _)| match &site.body {
                BodyInstanceKey::Drop(_) => true,
                BodyInstanceKey::Specialization(key) => reachable_keys.contains(key),
                BodyInstanceKey::Closure(closure) => reachable_closures.contains(closure),
                BodyInstanceKey::Root(_) => false,
            })
            .map(|(site, key)| (site.clone(), key.clone())),
    );
    base.graph.callable_calls.extend(
        discovered
            .graph
            .callable_calls
            .iter()
            .filter(|(site, _)| match &site.body {
                BodyInstanceKey::Drop(_) => true,
                BodyInstanceKey::Specialization(key) => reachable_keys.contains(key),
                BodyInstanceKey::Closure(closure) => reachable_closures.contains(closure),
                BodyInstanceKey::Root(_) => false,
            })
            .map(|(site, closure)| (site.clone(), closure.clone())),
    );
    base.graph.closure_values.extend(
        discovered
            .graph
            .closure_values
            .iter()
            .filter(|(site, _)| match &site.body {
                BodyInstanceKey::Drop(_) => true,
                BodyInstanceKey::Specialization(key) => reachable_keys.contains(key),
                BodyInstanceKey::Closure(closure) => reachable_closures.contains(closure),
                BodyInstanceKey::Root(_) => false,
            })
            .map(|(site, closure)| (site.clone(), closure.clone())),
    );
    base.graph.static_closure_bodies.extend(
        discovered
            .graph
            .static_closure_bodies
            .iter()
            .filter(|(site, _)| match &site.body {
                BodyInstanceKey::Drop(_) => true,
                BodyInstanceKey::Specialization(key) => reachable_keys.contains(key),
                BodyInstanceKey::Closure(closure) => reachable_closures.contains(closure),
                BodyInstanceKey::Root(_) => false,
            })
            .map(|(site, plan)| (site.clone(), plan.clone())),
    );
    base.graph.indirect_calls.extend(
        discovered
            .graph
            .indirect_calls
            .iter()
            .filter(|(site, _)| match &site.body {
                BodyInstanceKey::Drop(_) => true,
                BodyInstanceKey::Specialization(key) => reachable_keys.contains(key),
                BodyInstanceKey::Closure(closure) => reachable_closures.contains(closure),
                BodyInstanceKey::Root(_) => false,
            })
            .map(|(site, closure)| (site.clone(), closure.clone())),
    );
    base.graph.indirect_call_modes.extend(
        discovered
            .graph
            .indirect_call_modes
            .iter()
            .filter(|(site, _)| match &site.body {
                BodyInstanceKey::Drop(_) => true,
                BodyInstanceKey::Specialization(key) => reachable_keys.contains(key),
                BodyInstanceKey::Closure(closure) => reachable_closures.contains(closure),
                BodyInstanceKey::Root(_) => false,
            })
            .map(|(site, mode)| (site.clone(), *mode)),
    );
    base.graph.returned_closures.extend(
        discovered
            .graph
            .returned_closures
            .iter()
            .filter(|(site, _)| match &site.body {
                BodyInstanceKey::Drop(_) => true,
                BodyInstanceKey::Specialization(key) => reachable_keys.contains(key),
                BodyInstanceKey::Closure(closure) => reachable_closures.contains(closure),
                BodyInstanceKey::Root(_) => false,
            })
            .map(|(site, closure)| (site.clone(), closure.clone())),
    );
    base.graph.returned_closure_nominals.extend(
        discovered
            .graph
            .returned_closure_nominals
            .iter()
            .filter(|(site, _)| match &site.body {
                BodyInstanceKey::Drop(_) => true,
                BodyInstanceKey::Specialization(key) => reachable_keys.contains(key),
                BodyInstanceKey::Closure(closure) => reachable_closures.contains(closure),
                BodyInstanceKey::Root(_) => false,
            })
            .map(|(site, instance)| (site.clone(), instance.clone())),
    );
    base.graph
        .closure_tuples
        .extend(discovered.graph.closure_tuples.iter().cloned());
    base.graph.closure_nominal_constructions.extend(
        discovered
            .graph
            .closure_nominal_constructions
            .iter()
            .map(|(site, instance)| (site.clone(), instance.clone())),
    );
    base.graph.late_nominal_constructions.extend(
        discovered
            .graph
            .late_nominal_constructions
            .iter()
            .map(|(site, instance)| (site.clone(), instance.clone())),
    );
    base.graph.erased_callable_aliases.extend(
        discovered
            .graph
            .erased_callable_aliases
            .iter()
            .filter(|site| match &site.body {
                BodyInstanceKey::Drop(_) => true,
                BodyInstanceKey::Specialization(key) => reachable_keys.contains(key),
                BodyInstanceKey::Closure(closure) => reachable_closures.contains(closure),
                BodyInstanceKey::Root(_) => false,
            })
            .cloned(),
    );
    base.graph
        .erased_callable_aliases
        .retain(|site| !base.graph.closure_values.contains_key(site));
    base.graph.label_results.extend(
        discovered
            .graph
            .label_results
            .iter()
            .filter(|(site, _)| match &site.body {
                BodyInstanceKey::Drop(_) => true,
                BodyInstanceKey::Specialization(key) => reachable_keys.contains(key),
                BodyInstanceKey::Closure(closure) => reachable_closures.contains(closure),
                BodyInstanceKey::Root(_) => false,
            })
            .map(|(site, result)| (site.clone(), result.clone())),
    );
    for (site, instance) in
        discovered
            .graph
            .constructions
            .iter()
            .filter(|(site, _)| match &site.body {
                BodyInstanceKey::Drop(_) => true,
                BodyInstanceKey::Specialization(key) => reachable_keys.contains(key),
                BodyInstanceKey::Closure(closure) => reachable_closures.contains(closure),
                BodyInstanceKey::Root(_) => false,
            })
    {
        base.graph
            .constructions
            .insert(site.clone(), instance.clone());
        base.graph.constructed_nominals.insert(instance.clone());
    }
    base.graph.closure_bodies.extend(
        discovered
            .graph
            .closure_bodies
            .iter()
            .filter(|(closure, _)| reachable_closures.contains(*closure))
            .map(|(closure, kind)| (closure.clone(), *kind)),
    );
    base.graph
        .validated_symbolic
        .extend(discovered.graph.validated_symbolic.iter().cloned());
    base.errors.extend(
        discovered
            .errors
            .iter()
            .filter(|error| {
                matches!(&error.owner, DeclarationKey::Function(name) if name.starts_with("$drop$"))
                    || reachable_keys.iter().any(|key| key.template == error.owner)
                    || reachable_closures
                        .iter()
                        .any(|closure| closure.site.owner == error.owner)
            })
            .cloned(),
    );
    *base != before
}

#[cfg(test)]
pub(crate) fn discover_with_traits(program: &Program, trait_db: &TraitDb) -> Discovery {
    discover_with_traits_and_budgets(program, trait_db, &mut BTreeMap::new())
}

#[cfg(test)]
pub(crate) fn discover_with_traits_and_budgets(
    program: &Program,
    trait_db: &TraitDb,
    solver_budgets: &mut BTreeMap<DeclarationKey, SolverBudget>,
) -> Discovery {
    discover_with_traits_and_budgets_from(program, trait_db, solver_budgets, None)
}

pub(crate) fn discover_with_traits_and_budgets_from(
    program: &Program,
    trait_db: &TraitDb,
    solver_budgets: &mut BTreeMap<DeclarationKey, SolverBudget>,
    roots: Option<&BTreeSet<DeclarationKey>>,
) -> Discovery {
    let timing_enabled = std::env::var_os("G1_BOOTSTRAP_TIMINGS").is_some();
    let timing_started = std::time::Instant::now();
    let (templates_by_name, errors) = discover_templates(program, trait_db);
    let nominal_templates = discover_nominal_templates(program);
    let operation_templates = discover_operation_templates(program);
    let functions_by_declaration = program
        .functions
        .iter()
        .map(|function| (DeclarationKey::Function(function.name.clone()), function))
        .collect::<BTreeMap<_, _>>();
    if timing_enabled {
        eprintln!(
            "g1-specialization prepare: total={:.3}s functions={}",
            timing_started.elapsed().as_secs_f64(),
            program.functions.len()
        );
    }
    let function_expression_ordinals = functions_by_declaration
        .iter()
        .map(|(declaration, function)| (declaration.clone(), expression_ordinals(&function.body)))
        .collect::<BTreeMap<_, _>>();
    let struct_fields = program
        .structs
        .iter()
        .filter(|declaration| declaration.generics.is_none())
        .filter_map(|declaration| {
            let fields = declaration
                .fields
                .iter()
                .map(|field| {
                    Some((
                        field.name.clone(),
                        symbolic_type(&field.ty, &BTreeMap::new(), &BTreeMap::new())?,
                    ))
                })
                .collect::<Option<BTreeMap<_, _>>>()?;
            Some((declaration.name.clone(), fields))
        })
        .collect::<BTreeMap<_, _>>();
    let mut discovery = Discovery {
        graph: RequestGraph {
            templates: templates_by_name
                .values()
                .cloned()
                .map(|template| (template.declaration.clone(), template))
                .collect(),
            ..RequestGraph::default()
        },
        errors,
    };
    let mut contextual_validations = BTreeMap::new();
    let mut resolved_call_effects = BTreeMap::new();
    for global in &program.globals {
        let owner = DeclarationKey::Global(global.name.clone());
        let expression_ordinals = expression_ordinals(&global.value);
        let solver_budget = solver_budgets.entry(owner.clone()).or_default();
        let mut walker = Walker {
            program,
            templates: &templates_by_name,
            nominal_templates: &nominal_templates,
            struct_fields: &struct_fields,
            operations: &operation_templates,
            discovery: &mut discovery,
            owner,
            parent: None,
            locals: BTreeMap::new(),
            bindings: BTreeSet::new(),
            active_variants: BTreeMap::new(),
            active_labels: BTreeMap::new(),
            expression_ordinals: &expression_ordinals,
            body_instance: BodyInstanceKey::Root(DeclarationKey::Global(global.name.clone())),
            recording: true,
            trait_db,
            solver_budget,
            param_env: ParamEnv::default(),
            symbolic_validation: false,
            active_recursive_self: None,
            contextual_validations: &mut contextual_validations,
            resolved_call_effects: &mut resolved_call_effects,
        };
        walker.expression(&global.value, None);
    }
    if timing_enabled {
        eprintln!(
            "g1-specialization globals: total={:.3}s",
            timing_started.elapsed().as_secs_f64()
        );
    }
    for function in &program.functions {
        let Some(template) = templates_by_name.get(&function.name) else {
            continue;
        };
        if roots.is_some_and(|roots| !roots.contains(&template.declaration)) {
            continue;
        }
        let symbolic = !template.generic_params.is_empty();
        let declared_param_env = template_param_env(trait_db, template, None)
            .expect("unsubstituted template facts preserve their owner-qualified parameters");
        let solver_budget = solver_budgets
            .entry(template.declaration.clone())
            .or_default();
        let mut root_failure = None;
        let root_constraints_proven = symbolic
            || template.marker_constraints.iter().all(|constraint| {
                let report = trait_db.solve_with_key_detailed_with_budget(
                    solver_budget,
                    &ParamEnv::default(),
                    constraint.polarity,
                    &constraint.trait_key,
                    &constraint.subject,
                    &constraint.arguments,
                    &constraint.bindings,
                );
                if report.result != SolveResult::Proven {
                    root_failure = report.failure.map(|failure| failure.diagnostic_text());
                    false
                } else {
                    true
                }
            });
        if !root_constraints_proven {
            discovery.errors.insert(DiscoveryError {
                owner: template.declaration.clone(),
                message: format!(
                    "monomorphic callable has a where constraint without global evidence{}",
                    root_failure
                        .map(|detail| format!("; {detail}"))
                        .unwrap_or_default()
                ),
            });
        }
        let expression_ordinals = &function_expression_ordinals[&template.declaration];
        let mut walker = Walker {
            program,
            templates: &templates_by_name,
            nominal_templates: &nominal_templates,
            struct_fields: &struct_fields,
            operations: &operation_templates,
            discovery: &mut discovery,
            owner: template.declaration.clone(),
            parent: None,
            locals: function
                .params
                .iter()
                .zip(&template.params)
                .map(|(param, ty)| (param.name.clone(), LocalBinding::Type(ty.clone())))
                .collect(),
            bindings: function
                .params
                .iter()
                .map(|param| param.name.clone())
                .collect(),
            active_variants: BTreeMap::new(),
            active_labels: implicit_function_labels(
                function,
                &template.declaration,
                template.result.clone(),
            ),
            expression_ordinals,
            body_instance: BodyInstanceKey::Root(template.declaration.clone()),
            recording: !symbolic,
            trait_db,
            solver_budget,
            param_env: if root_constraints_proven {
                declared_param_env
            } else {
                ParamEnv::default()
            },
            symbolic_validation: symbolic,
            active_recursive_self: None,
            contextual_validations: &mut contextual_validations,
            resolved_call_effects: &mut resolved_call_effects,
        };
        walker.expression(&function.body, Some(&template.result));
        if symbolic
            && !discovery
                .errors
                .iter()
                .any(|error| error.owner == template.declaration)
        {
            discovery
                .graph
                .validated_symbolic
                .insert(template.declaration.clone());
        }
    }
    if timing_enabled {
        eprintln!(
            "g1-specialization roots: total={:.3}s requests={} closures={}",
            timing_started.elapsed().as_secs_f64(),
            discovery.graph.requests.len(),
            discovery.graph.closure_bodies.len()
        );
    }
    for declaration in program
        .drops
        .iter()
        .filter(|declaration| declaration.generics.is_none())
    {
        let owner = DeclarationKey::Function(format!("$drop${}", declaration.target));
        let expression_ordinals = expression_ordinals(&declaration.body);
        let solver_budget = solver_budgets.entry(owner.clone()).or_default();
        let mut walker = Walker {
            program,
            templates: &templates_by_name,
            nominal_templates: &nominal_templates,
            struct_fields: &struct_fields,
            operations: &operation_templates,
            discovery: &mut discovery,
            owner,
            parent: None,
            locals: BTreeMap::from([(
                "self".into(),
                LocalBinding::Type(ProvisionalType::unique(ProvisionalType::Nominal(
                    NominalInstanceKey::monomorphic(declaration.target.clone()),
                ))),
            )]),
            bindings: BTreeSet::from(["self".into()]),
            active_variants: BTreeMap::new(),
            active_labels: BTreeMap::new(),
            expression_ordinals: &expression_ordinals,
            body_instance: BodyInstanceKey::Drop(declaration.target.clone()),
            recording: true,
            trait_db,
            solver_budget,
            param_env: ParamEnv::default(),
            symbolic_validation: false,
            active_recursive_self: None,
            contextual_validations: &mut contextual_validations,
            resolved_call_effects: &mut resolved_call_effects,
        };
        walker.expression(
            &declaration.body,
            Some(&ProvisionalType::Predefined("Unit".into())),
        );
    }
    let mut processed = BTreeSet::new();
    let mut processed_closures = BTreeSet::new();
    loop {
        let pending_requests = discovery
            .graph
            .requests
            .keys()
            .filter(|key| !processed.contains(*key))
            .cloned()
            .collect::<Vec<_>>();
        for key in pending_requests {
            processed.insert(key.clone());
            let Some(template) = discovery.graph.templates.get(&key.template).cloned() else {
                continue;
            };
            let Some(function) = functions_by_declaration.get(&template.declaration).copied()
            else {
                continue;
            };
            let substitutions = substitutions_for_key(&template, &key);
            let Ok(param_env) = template_param_env(trait_db, &template, Some(&substitutions))
            else {
                discovery.errors.insert(DiscoveryError {
                    owner: template.declaration.clone(),
                    message: "specialized lexical trait environment remains unresolved".into(),
                });
                continue;
            };
            let locals = function
                .params
                .iter()
                .zip(template.params.iter().zip(&template.parameter_binders))
                .filter_map(|(param, (ty, binder))| {
                    if let Some(binder) = binder
                        && let Some(SpecializationArgument::Closure(
                            site,
                            shape,
                            captures,
                            environment,
                            active_labels,
                            static_captures,
                        )) = substitutions.get(binder)
                    {
                        return Some((
                            param.name.clone(),
                            LocalBinding::Closure(ClosureRequest {
                                site: site.clone(),
                                shape: shape.clone(),
                                captures: captures.clone(),
                                param_env: environment.clone(),
                                active_labels: active_labels.clone(),
                                static_captures: static_captures.clone(),
                            }),
                        ));
                    }
                    substitute(ty, &substitutions)
                        .map(|ty| (param.name.clone(), LocalBinding::Type(ty)))
                })
                .collect();
            let expression_ordinals = &function_expression_ordinals[&template.declaration];
            let solver_budget = solver_budgets
                .entry(template.declaration.clone())
                .or_default();
            let mut walker = Walker {
                program,
                templates: &templates_by_name,
                nominal_templates: &nominal_templates,
                struct_fields: &struct_fields,
                operations: &operation_templates,
                discovery: &mut discovery,
                owner: template.declaration.clone(),
                parent: Some(key.clone()),
                locals,
                bindings: function
                    .params
                    .iter()
                    .map(|param| param.name.clone())
                    .collect(),
                active_variants: BTreeMap::new(),
                active_labels: implicit_function_labels(
                    function,
                    &template.declaration,
                    substitute(&template.result, &substitutions)
                        .unwrap_or_else(|| template.result.clone()),
                ),
                expression_ordinals,
                body_instance: BodyInstanceKey::Specialization(key.clone()),
                recording: true,
                trait_db,
                solver_budget,
                param_env,
                symbolic_validation: false,
                active_recursive_self: None,
                contextual_validations: &mut contextual_validations,
                resolved_call_effects: &mut resolved_call_effects,
            };
            let result = substitute(&template.result, &substitutions);
            walker.expression(&function.body, result.as_ref());
        }
        while let Some((closure, body_kind, planned_recursive_self)) = discovery
            .graph
            .closure_bodies
            .iter()
            .find(|(closure, _)| !processed_closures.contains(*closure))
            .map(|(closure, kind)| (closure.clone(), *kind, None))
            .or_else(|| {
                discovery
                    .graph
                    .static_closure_bodies
                    .values()
                    .find(|plan| !processed_closures.contains(&plan.request))
                    .map(|plan| {
                        (
                            plan.request.clone(),
                            plan.body_kind,
                            plan.recursive_self.clone(),
                        )
                    })
            })
        {
            processed_closures.insert(closure.clone());
            let root = body_root(program, &closure.site.owner);
            let Some(root) = root else {
                continue;
            };
            let Some((params, body)) = closure_body(program, &closure, body_kind) else {
                continue;
            };
            let expression_ordinals = expression_ordinals(root);
            let mut locals: BTreeMap<String, LocalBinding> = closure
                .captures
                .iter()
                .map(|capture| (capture.name.clone(), LocalBinding::Type(capture.ty.clone())))
                .chain(
                    params
                        .iter()
                        .zip(&closure.shape.params)
                        .map(|(name, ty)| (name.clone(), LocalBinding::Type(ty.clone()))),
                )
                .collect();
            let recursive_self = discovery
                .graph
                .recursive_closures
                .get(&closure)
                .cloned()
                .or(planned_recursive_self);
            // Static callbacks discovered while walking a specialization are
            // part of that request's ancestry. Preserve the parent edge while
            // rewalking the callback body so homeomorphic-growth detection
            // also covers closure-environment expansion; otherwise a wrapper
            // that captures and re-forwards another callback can manufacture
            // an unbounded sequence of ever-deeper producer identities.
            let parent = discovery
                .graph
                .static_closure_bodies
                .iter()
                .find_map(|(site, plan)| {
                    if plan.request != closure {
                        return None;
                    }
                    match &site.body {
                        BodyInstanceKey::Specialization(parent) => Some(parent.clone()),
                        BodyInstanceKey::Root(_)
                        | BodyInstanceKey::Drop(_)
                        | BodyInstanceKey::Closure(_) => None,
                    }
                });
            if let Some(recursive_self) = &recursive_self {
                locals.insert(
                    recursive_self.binding.clone(),
                    LocalBinding::RecursiveSelf(recursive_self.clone(), closure.shape.clone()),
                );
            }
            let bindings = locals.keys().cloned().collect();
            let param_env = closure.param_env.clone();
            let solver_budget = solver_budgets
                .entry(closure.site.owner.clone())
                .or_default();
            let mut walker = Walker {
                program,
                templates: &templates_by_name,
                nominal_templates: &nominal_templates,
                struct_fields: &struct_fields,
                operations: &operation_templates,
                discovery: &mut discovery,
                owner: closure.site.owner.clone(),
                parent,
                locals,
                bindings,
                active_variants: BTreeMap::new(),
                active_labels: closure.active_labels.clone(),
                expression_ordinals: &expression_ordinals,
                body_instance: BodyInstanceKey::Closure(closure.clone()),
                recording: true,
                trait_db,
                solver_budget,
                param_env,
                symbolic_validation: contains_late_callable_captures(&closure),
                active_recursive_self: recursive_self,
                contextual_validations: &mut contextual_validations,
                resolved_call_effects: &mut resolved_call_effects,
            };
            walker.expression(body, Some(&closure.shape.result));
        }
        let planned_closure_count = discovery
            .graph
            .closure_bodies
            .keys()
            .chain(
                discovery
                    .graph
                    .static_closure_bodies
                    .values()
                    .map(|plan| &plan.request),
            )
            .collect::<BTreeSet<_>>()
            .len();
        if processed.len() == discovery.graph.requests.len()
            && processed_closures.len() == planned_closure_count
        {
            break;
        }
    }
    if timing_enabled {
        eprintln!(
            "g1-specialization fixed-point: total={:.3}s requests={} closures={}",
            timing_started.elapsed().as_secs_f64(),
            discovery.graph.requests.len(),
            processed_closures.len()
        );
    }
    for template in templates_by_name.values() {
        let has_deferred_projection = contains_projection_placeholder(&template.result)
            || template.params.iter().any(contains_projection_placeholder);
        if has_deferred_projection
            && !discovery
                .graph
                .requests
                .keys()
                .any(|request| request.template == template.declaration)
        {
            discovery.errors.insert(DiscoveryError {
                owner: template.declaration.clone(),
                message: "associated projection has ordinary trait evidence but no ground specialization proves a unique associated value".into(),
            });
        }
    }
    discovery
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn substitution_distinguishes_unbound_inputs_from_rigid_value_tails() {
        let local = GenericParamKey {
            owner: DeclarationKey::Function("callee".into()),
            ordinal: 0,
        };
        let caller_rigid = GenericParamKey {
            owner: DeclarationKey::Function("caller".into()),
            ordinal: 0,
        };
        let local_type = ProvisionalType::Param(local.clone());
        let rigid_type = ProvisionalType::Param(caller_rigid.clone());

        assert_eq!(substitute(&rigid_type, &BTreeMap::new()), None);
        assert_eq!(
            substitute(
                &local_type,
                &BTreeMap::from([(
                    local,
                    SpecializationArgument::Type(ProvisionalType::Tuple(vec![rigid_type.clone()])),
                )]),
            ),
            Some(ProvisionalType::Tuple(vec![rigid_type]))
        );
    }

    #[test]
    fn partial_context_retains_outer_rigid_fields_and_constrains_inner_fields() {
        let outer = GenericParamKey {
            owner: DeclarationKey::Function("outer".into()),
            ordinal: 0,
        };
        let inner = GenericParamKey {
            owner: DeclarationKey::Function("inner".into()),
            ordinal: 0,
        };
        let result = |ok, error| {
            ProvisionalType::Nominal(NominalInstanceKey {
                declaration: NominalKey("Result".into()),
                arguments: vec![ok, error],
            })
        };
        let walk_error = ProvisionalType::Nominal(NominalInstanceKey::monomorphic("WalkError"));
        let formal = result(
            ProvisionalType::Predefined("Unit".into()),
            ProvisionalType::Param(inner.clone()),
        );
        let context = result(ProvisionalType::Param(outer.clone()), walk_error.clone());
        let mutable = BTreeSet::from([inner.clone()]);
        let mut substitutions = BTreeMap::new();

        assert!(constrain_contextual_inference(
            &formal,
            &context,
            &mutable,
            &mut substitutions,
        ));
        assert_eq!(
            substitutions.get(&inner),
            Some(&SpecializationArgument::Type(walk_error.clone()))
        );
        assert_eq!(
            substitute_preserving_missing(&context, &substitutions),
            Some(result(ProvisionalType::Param(outer), walk_error))
        );
    }

    #[test]
    fn contextual_inference_defers_a_rigid_outer_variable_until_concrete_evidence() {
        let inner = GenericParamKey {
            owner: DeclarationKey::Function("inner".into()),
            ordinal: 0,
        };
        let outer = GenericParamKey {
            owner: DeclarationKey::Function("outer".into()),
            ordinal: 0,
        };
        let mutable = BTreeSet::from([inner.clone()]);
        let mut substitutions = BTreeMap::new();

        assert!(constrain_contextual_inference(
            &ProvisionalType::Param(inner.clone()),
            &ProvisionalType::Param(outer),
            &mutable,
            &mut substitutions,
        ));
        assert!(!substitutions.contains_key(&inner));

        let integer = ProvisionalType::Predefined("i64".into());
        assert!(unify_inference(
            &ProvisionalType::Param(inner.clone()),
            &integer,
            &mutable,
            &mut substitutions,
        ));
        assert_eq!(
            substitutions.get(&inner),
            Some(&SpecializationArgument::Type(integer))
        );
    }

    #[test]
    fn mutable_unification_flattens_chains_checks_occurs_and_is_order_independent() {
        let owner = DeclarationKey::Function("callee".into());
        let first = GenericParamKey {
            owner: owner.clone(),
            ordinal: 0,
        };
        let second = GenericParamKey { owner, ordinal: 1 };
        let mutable = BTreeSet::from([first.clone(), second.clone()]);
        let integer = ProvisionalType::Predefined("i64".into());
        let mut left_to_right = BTreeMap::new();
        assert!(unify_inference(
            &ProvisionalType::Param(first.clone()),
            &ProvisionalType::Param(second.clone()),
            &mutable,
            &mut left_to_right,
        ));
        assert!(unify_inference(
            &ProvisionalType::Param(first.clone()),
            &integer,
            &mutable,
            &mut left_to_right,
        ));
        let mut right_to_left = BTreeMap::new();
        assert!(unify_inference(
            &ProvisionalType::Param(first.clone()),
            &integer,
            &mutable,
            &mut right_to_left,
        ));
        assert!(unify_inference(
            &ProvisionalType::Param(first.clone()),
            &ProvisionalType::Param(second.clone()),
            &mutable,
            &mut right_to_left,
        ));
        for substitutions in [&left_to_right, &right_to_left] {
            assert_eq!(
                substitute(&ProvisionalType::Param(first.clone()), substitutions),
                Some(integer.clone())
            );
            assert_eq!(
                substitute(&ProvisionalType::Param(second.clone()), substitutions),
                Some(integer.clone())
            );
        }
        assert!(!unify_inference(
            &ProvisionalType::Param(first.clone()),
            &ProvisionalType::Tuple(vec![ProvisionalType::Param(first)]),
            &mutable,
            &mut BTreeMap::new(),
        ));
    }

    fn parse_discovery(source: &str) -> Discovery {
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        discover(&program)
    }

    #[test]
    fn refined_generic_enum_branches_keep_contextual_reference_result_shape() {
        let discovery = parse_discovery(
            "infixr 1 else; enum Choice<A,E>{Ok(A),Err(E)}
             project<'a,A,E>(value:&'a Choice<A,E>)->Choice<&'a A,&'a E>{
                 if(*value is Choice::Ok(_)){Choice::Ok(&value.0)}
                 else {Choice::Err(&value.0)}
             }
             main()->(){()}",
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
    }

    #[test]
    fn ground_refinement_context_preserves_subsequent_generic_call_plans() {
        let discovery = parse_discovery(
            "infixr 1 else;
             enum Result<T,E>{Ok(T),Err(E)}
             struct Vec<T>{slot:T}
             struct HashMap<K,V>{item:V}
             struct FunctionSearch{first_plus_one:u32,count:u32}
             struct ResolutionIndex{
                 functions:HashMap<(usize,u32),FunctionSearch>,
                 callable_by_shell:Vec<Result<u32,()>>
             }
             hash_insert<K,V>(value:&mut HashMap<K,V>,key:K,item:V)->(){()}
             index_callable(index:&mut ResolutionIndex)->(){
                 if(index.callable_by_shell.slot is Result::Err(_)){
                     index.callable_by_shell.slot=Result::Ok(7);()
                 }else{()};
                 hash_insert(
                     &mut index.functions,
                     (3,9),
                     FunctionSearch{first_plus_one:8,count:1}
                 );
                 ()
             }
             main()->(){()}",
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        assert!(
            discovery.graph.direct_calls.iter().any(|(site, target)| {
                site.body
                    == BodyInstanceKey::Root(DeclarationKey::Function("index_callable".into()))
                    && target.template == DeclarationKey::Function("hash_insert".into())
            }),
            "{}",
            discovery.graph.canonical_text()
        );
    }

    #[test]
    fn label_exit_is_never_through_generic_option_reference_refinement() {
        let discovery = parse_discovery(
            "infixr 1 else;
             enum Result<T,E>{Ok(T),Err(E)}
             struct Cell<T>{value:T}
             struct Failure{code:u8}
             maybe_get<'a,T>(
                 value:&'a Cell<T>
             )->Result<&'a T,()>{
                 Result::Ok(&value.value)
             }
             retain<T>(value:T)->T{value}
             accept(value:&u32)->(){()}
             index_callable(
                 value:&Cell<u32>,
                 present:Result<(),()>
             )->Result<(),Failure>{
                 present;
                 let candidate=maybe_get(value);
                 let found=if(candidate is Result::Err(_)){
                     @index_callable(Result::Err(Failure{code:1}))
                 }else{candidate.0};
                 accept(found);
                 retain(found);
                 Result::Ok(())
             }
             main()->(){()}",
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        assert!(
            discovery.graph.direct_calls.iter().any(|(site, target)| {
                site.body
                    == BodyInstanceKey::Root(DeclarationKey::Function("index_callable".into()))
                    && target.template == DeclarationKey::Function("retain".into())
            }),
            "{}",
            discovery.graph.canonical_text()
        );
    }

    #[test]
    fn structural_else_completes_complementary_result_parameters() {
        let discovery = parse_discovery(
            "infixr 1 else; enum Result<T,E>{Ok(T),Err(E)}
             choose<T,E>(flag:Result<(),()>,ok:T,error:E)->Result<T,E>{
                 if(flag){Result::Ok(ok)}else{Result::Err(error)}
             }
             answer()->i64{let selected=choose(Result::Ok(()),42,());
                 if(selected is Result::Ok(_)){selected.0}else{0}}
             main()->(){()}",
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        assert!(
            discovery
                .graph
                .requests
                .keys()
                .any(|request| { request.template == DeclarationKey::Function("choose".into()) })
        );
    }

    #[test]
    fn recursive_specialization_accepts_a_finite_cycle_independent_of_source_order() {
        let first = parse_discovery(
            "first<T>(value:T)->(){second(value)}
             second<T>(value:T)->(){first(value)}
             main()->(){first(())}",
        );
        let reordered = parse_discovery(
            "second<T>(value:T)->(){first(value)}
             first<T>(value:T)->(){second(value)}
             main()->(){first(())}",
        );
        assert!(first.errors.is_empty(), "{:#?}", first.errors);
        assert!(reordered.errors.is_empty(), "{:#?}", reordered.errors);
        assert_eq!(first.graph.requests.len(), 2);
        assert_eq!(
            first.graph.canonical_text(),
            reordered.graph.canonical_text()
        );
        assert_eq!(first.graph.fingerprint(), reordered.graph.fingerprint());
    }

    #[test]
    fn recursive_specialization_rejects_structural_growth_without_a_count_cap() {
        let discovery = parse_discovery(
            "grow<T>(value:T)->(){grow((value,))}
             main()->(){grow(())}",
        );
        assert!(
            discovery.errors.iter().any(|error| error
                .message
                .contains("recursive specialization is non-well-founded")),
            "{:#?}",
            discovery.errors
        );
        assert!(
            discovery.graph.requests.len() <= 2,
            "{:#?}",
            discovery.graph
        );
    }

    #[test]
    fn finite_callable_discovery_is_not_rejected_by_an_arbitrary_request_count() {
        let mut source =
            String::from("invoke<F>(body:F)->i64 where F:Fn<(),Output=i64>{body()} probe()->(){");
        for value in 0..1025 {
            use std::fmt::Write as _;
            write!(source, "invoke({{=>{value}}});").unwrap();
        }
        source.push_str("()} main()->(){probe();()}");
        let discovery = parse_discovery(&source);
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        assert_eq!(discovery.graph.requests.len(), 1025);
    }

    #[test]
    fn refined_enum_branch_context_does_not_accept_mismatched_payloads() {
        let discovery = parse_discovery(
            "infixr 1 else; enum Choice<A,E>{Ok(A),Err(E)}
             bad<'a>(value:&'a Choice<i64,i64>)->Choice<&'a i64,&'a mut i64>{
                 if(*value is Choice::Ok(_)){Choice::Ok(&value.0)}
                 else {Choice::Err(&value.0)}
             }
             main()->(){()}",
        );
        assert!(
            discovery.errors.iter().any(|error| {
                error.message.contains("conflicting type arguments")
                    || error.message.contains("incompatible result types")
            }),
            "{:#?}",
            discovery.errors
        );
    }

    #[test]
    fn sealed_typed_closure_retains_exact_unique_capture_evidence() {
        let discovery = parse_discovery(
            "infixl 30 +;
             retain<T>(value:T)->T{value}
             answer()->i64{
                 let value=40;
                 let borrowed=&mut value;
                 let add=(delta:i64)->i64{*borrowed = *borrowed + delta;*borrowed};
                 let escaped=retain(move add);
                 let first=escaped(1);
                 move escaped(1)
             }
             main()->(){()}",
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        assert!(discovery.graph.closure_values.values().any(|closure| {
            closure
                .captures
                .iter()
                .any(|capture| contains_unique_reference_shape(&capture.ty))
        }));
        assert!(discovery.graph.closure_values.values().any(|closure| {
            closure
                .captures
                .iter()
                .any(|capture| contains_unique_reference_shape(&capture.ty))
                && closure.receiver_mode() == 1
        }));
    }

    #[test]
    fn marker_constraint_records_ground_request() {
        let source = "trait Marker {} struct Box<T> { value: T } impl Marker for i64 {} impl<T> Marker for Box<T> where T: Marker {} id<T>(value: T) -> T where T: Marker { value } boxed() -> Box<i64> { Box { value: 42 } } main() -> { id(42); id(boxed()); () }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let discovery = discover_with_traits(&program, &db);
        assert!(discovery.errors.is_empty(), "{:?}", discovery.errors);
        assert_eq!(discovery.graph.requests.len(), 2);
    }

    #[test]
    fn discovery_preserves_the_aggregate_declaration_solver_budget() {
        let source = "trait Marker {}
            impl Marker for i64 {}
            constrained<T>(value: T) -> T where T: Marker { value }
            caller() -> i64 { constrained(42) }
            main() -> () { () }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let mut budgets = BTreeMap::from([
            (
                DeclarationKey::Function("constrained".into()),
                SolverBudget::exhausted_for_test(),
            ),
            (
                DeclarationKey::Function("caller".into()),
                SolverBudget::exhausted_for_test(),
            ),
        ]);

        let discovery = discover_with_traits_and_budgets(&program, &db, &mut budgets);

        assert!(
            !discovery.errors.is_empty(),
            "an exhausted declaration budget must not be replenished by discovery"
        );
        assert!(
            !discovery.graph.requests.keys().any(|request| {
                request.template == DeclarationKey::Function("constrained".into())
            }),
            "an over-budget declaration must not retain a specialization request"
        );
    }

    #[test]
    fn exact_captureless_callable_proves_zero_use_through_a_generic_bound() {
        let discovery = parse_discovery(
            "discard<F>(body: F) -> () where F: Fn<(), Output=i64>, F: Use<[0,0]> { () }
             use() -> () { discard({ 1 }) }
             main() -> () { () }",
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        assert!(discovery.graph.requests.keys().any(|request| matches!(
            request.arguments.first(),
            Some(SpecializationArgument::Closure(_, _, captures, _, _, _)) if captures.is_empty()
        )));
    }

    #[test]
    fn callable_zero_use_evidence_rejects_a_must_move_capture() {
        let discovery = parse_discovery(
            "struct Ticket { serial: i64 }
             impl Use<[1,1]> for Ticket {}
             discard<F>(body: F) -> () where F: Fn<(), Output=i64>, F: Use<[0,0]> { () }
             bad(ticket: Ticket) -> () { discard({ move ticket; 1 }) }
             main() -> () { () }",
        );
        assert!(
            discovery
                .errors
                .iter()
                .any(|error| error.message.contains("Use")),
            "{:#?}",
            discovery.errors
        );
    }

    #[test]
    fn generic_effect_instance_remains_symbolic_until_callable_specialization() {
        let source = "effect Fail<E> { fail(error:E) -> ! } invoke<E,F>(error:E, body:F)->! / {Fail<E>} where F:Fn<(E),Output=!,Effects={Fail<E>}>{body(error)} selected()->i64{handle {invoke(42,{error=>perform Fail<i64>::fail(error)})}{Fail<i64>::fail(error)=>error}} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let discovery = discover_with_traits(&program, &db);
        assert!(discovery.errors.is_empty(), "{:?}", discovery.errors);
        assert!(discovery.graph.requests.keys().any(|request| {
            request.arguments.iter().any(|argument| {
                matches!(
                    argument,
                    SpecializationArgument::EffectRow(row)
                        if row.iter().any(|effect| !effect.arguments.is_empty())
                )
            }) || request.arguments.iter().any(|argument| {
                matches!(
                    argument,
                    SpecializationArgument::Closure(_, shape, _, _, _, _)
                        if shape.effects.iter().any(|effect| !effect.arguments.is_empty())
                )
            })
        }));
    }

    #[test]
    fn closure_effect_subtraction_is_exact_per_generic_instance() {
        let source = "effect Fail<E>{fail(error:E)->!} probe()->{let delayed={=>handle perform Fail<i64>::fail(1){Fail<Text>::fail(error)=>()}};()} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let function = program
            .functions
            .iter()
            .find(|function| function.name == "probe")
            .unwrap();
        let ExprKind::Block(statements) = &function.body.kind else {
            panic!("probe body is a block")
        };
        let Stmt::Let { value, .. } = &statements[0] else {
            panic!("first statement binds the closure")
        };
        let ExprKind::Closure { body, .. } = &value.kind else {
            panic!("bound value is a closure")
        };
        let resolve = |site, fallback: &str| {
            let syntax = program.effect_path(site)?;
            let TypeSyntaxKind::Application {
                constructor,
                arguments,
                ..
            } = &syntax.kind
            else {
                return Some(crate::compiler_typeck::CallableEffect {
                    declaration: crate::compiler_typeck::ProtocolKey(fallback.to_owned()),
                    arguments: vec![],
                });
            };
            Some(crate::compiler_typeck::CallableEffect {
                declaration: crate::compiler_typeck::ProtocolKey(
                    constructor.simple_name()?.to_owned(),
                ),
                arguments: arguments
                    .iter()
                    .map(|argument| symbolic_type(argument, &BTreeMap::new(), &BTreeMap::new()))
                    .collect::<Option<Vec<_>>>()?,
            })
        };
        let row = direct_closure_effects(body, &resolve, &|_| BTreeSet::new());
        assert_eq!(row.len(), 1);
        let remaining = row.iter().next().unwrap();
        assert_eq!(remaining.declaration.0, "Fail");
        assert_eq!(
            remaining.arguments,
            [ProvisionalType::Predefined("i64".into())]
        );
    }

    #[test]
    fn graph_text_and_fingerprint_are_insertion_order_independent() {
        let owner = DeclarationKey::Function("identity".into());
        let parameter = GenericParamKey {
            owner: owner.clone(),
            ordinal: 0,
        };
        let template = FunctionTemplate {
            declaration: owner.clone(),
            generic_params: vec![parameter.clone()],
            params: vec![ProvisionalType::Param(parameter.clone())],
            parameter_binders: vec![None],
            result_binder: None,
            result_nominal_binders: None,
            result: ProvisionalType::Param(parameter),
            callable_constraints: BTreeMap::new(),
            effectful_callable_binders: BTreeSet::new(),
            marker_constraints: vec![],
            transparent_identity: false,
        };
        let mut first = RequestGraph::default();
        first.templates.insert(owner.clone(), template.clone());
        let mut second = RequestGraph::default();
        second.templates.insert(owner, template);
        assert_eq!(first.canonical_text(), second.canonical_text());
        assert_eq!(first.fingerprint(), second.fingerprint());
    }

    #[test]
    fn emission_plan_preserves_source_ids_without_requests_and_sorts_new_entries() {
        let program = crate::parser::parse(
            crate::lexer::lex("z() -> { () } let middle = 1; a() -> { () }").unwrap(),
        )
        .unwrap();
        let discovery = discover(&program);
        let plan = emission_plan(&program, &discovery, None);
        let sources = plan
            .ordered
            .iter()
            .map(|key| match key {
                EmissionKey::Source { wire_name, .. } => wire_name.as_str(),
                _ => panic!("request-free plan contained a generated entry"),
            })
            .collect::<Vec<_>>();
        assert_eq!(sources, vec!["$global$6d6964646c65", "a", "z"]);
        assert!(
            plan.ordered
                .iter()
                .enumerate()
                .all(|(id, key)| plan.ids[key] == id as u32)
        );

        let requested = parse_discovery(
            "id<T>(value: T) -> T { value }
             apply<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
             use() -> i64 { apply({ id(1) }) }",
        );
        let requested_program = crate::parser::parse(
            crate::lexer::lex(
                "id<T>(value: T) -> T { value }
                 apply<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
                 use() -> i64 { apply({ id(1) }) }",
            )
            .unwrap(),
        )
        .unwrap();
        let plan = emission_plan(&requested_program, &requested, None);
        assert!(matches!(plan.ordered[0], EmissionKey::Source { .. }));
        assert!(plan.ordered.windows(2).all(|pair| pair[0] < pair[1]));
    }

    #[test]
    fn exact_fn_constraint_normalizes_to_a_symbolic_callable_shape() {
        let source =
            "apply<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() } main() -> { () }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let (templates, errors) = discover_templates(&program, &TraitDb::default());
        assert!(errors.is_empty(), "{errors:#?}");
        let template = &templates["apply"];
        assert_eq!(template.generic_params.len(), 2);
        assert!(matches!(
            &template.params[0],
            ProvisionalType::Callable(shape)
                if shape.params.is_empty()
                    && matches!(shape.result, ProvisionalType::Param(_))
        ));
        assert_eq!(
            template.parameter_binders[0],
            Some(template.generic_params[0].clone())
        );
    }

    #[test]
    fn generic_arguments_follow_source_parameter_order_and_scalar_identity() {
        let discovery = parse_discovery(
            "choose<Z, A>(z: Z, a: A) -> Z { z }
             use() -> i32 { choose(1, 2) }",
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        let request = discovery.graph.requests.values().next().unwrap();
        assert_eq!(
            request.key.arguments,
            vec![
                SpecializationArgument::Type(ProvisionalType::Predefined("i32".into())),
                SpecializationArgument::Type(ProvisionalType::Predefined("i64".into())),
            ]
        );
        let template = &discovery.graph.templates[&DeclarationKey::Function("choose".into())];
        assert_eq!(template.generic_params[0].ordinal, 0);
        assert_eq!(template.generic_params[1].ordinal, 1);
    }

    #[test]
    fn contextual_blocks_infer_output_and_same_shape_sites_do_not_merge() {
        let discovery = parse_discovery(
            "apply<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
             use() -> i64 { let first = apply({ 1 }); apply({ 2 }) }",
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        assert_eq!(discovery.graph.requests.len(), 2);
        let sites = discovery
            .graph
            .requests
            .keys()
            .filter_map(|key| match &key.arguments[0] {
                SpecializationArgument::Closure(site, shape, captures, _environment, _, _) => {
                    assert!(shape.params.is_empty());
                    assert!(captures.is_empty());
                    assert_eq!(shape.result, ProvisionalType::Predefined("i64".into()));
                    Some(site.clone())
                }
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(sites.len(), 2);
    }

    #[test]
    fn inferred_label_inside_contextual_closure_keeps_the_callable_result() {
        let discovery = parse_discovery(
            "enum Result<T,E>{Ok(T),Err(E)}
             apply<F>(
                 body:F
             )->Result<i64,()>
             where F:Fn<(),Output=Result<i64,()>>{
                 body()
             }
             use()->Result<i64,()>{
                 apply({@done:{@done(Result::Ok(42))}})
             }",
        );
        let result = ProvisionalType::Nominal(NominalInstanceKey {
            declaration: NominalKey("Result".into()),
            arguments: vec![
                ProvisionalType::Predefined("i64".into()),
                ProvisionalType::Predefined("Unit".into()),
            ],
        });

        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        assert!(
            discovery
                .graph
                .label_results
                .values()
                .any(|inferred| inferred == &result),
            "{}",
            discovery.graph.canonical_text()
        );
        assert!(
            discovery
                .graph
                .label_results
                .values()
                .all(|inferred| inferred != &ProvisionalType::Predefined("Unit".into())),
            "{}",
            discovery.graph.canonical_text()
        );
    }

    #[test]
    fn planned_closure_rewalk_retains_referenced_static_label_destinations() {
        let common = "
            enum Result<T,E>{Ok(T),Err(E)}
            enum Failure{Rejected}
            checked()->Result<(),()>{Result::Err(())}
            apply<F>(body:F)->Result<(),Failure>
            where F:Fn<(),Output=Result<(),Failure>>{body()}
        ";
        let implicit = parse_discovery(&format!(
            "{common}
             outer()->Result<(),Failure>{{
                 apply({{=>{{
                     handle checked(){{
                         Result::Err(_)=>
                             @outer(Result::Err(Failure::Rejected)),
                         Result::Ok(_)=>()
                     }};
                     Result::Ok(())
                 }}}})
             }}"
        ));
        assert!(implicit.errors.is_empty(), "{:#?}", implicit.errors);
        assert!(implicit.graph.closure_bodies.keys().any(|closure| {
            closure.active_labels.contains_key("outer") && closure.active_labels.len() == 1
        }));

        let local_source = format!(
            "{common}
             local()->Result<(),Failure>{{
                 @done: Result<(),Failure>{{
                     apply({{=>{{
                         handle checked(){{
                             Result::Err(_)=>
                                 @done(Result::Err(Failure::Rejected)),
                             Result::Ok(_)=>()
                         }};
                         Result::Ok(())
                     }}}})
                 }}
             }}"
        );
        let local = parse_discovery(&local_source);
        assert!(local.errors.is_empty(), "{:#?}", local.errors);
        assert!(local.graph.closure_bodies.keys().any(|closure| {
            closure.active_labels.contains_key("done") && closure.active_labels.len() == 1
        }));
        let local_program =
            crate::parser::parse(crate::lexer::lex(&local_source).unwrap()).unwrap();
        let plan = emission_plan(&local_program, &local, None);
        assert!(plan.ordered.iter().all(|entry| match entry {
            EmissionKey::Closure(request) => {
                request.active_labels.is_empty() && request.static_captures.is_empty()
            }
            EmissionKey::Specialization(key) => !late_specialization(key),
            EmissionKey::Source { .. } => true,
        }));
    }

    #[test]
    fn large_contextual_dispatch_suffixes_are_validated_once() {
        std::thread::Builder::new()
            .name("large-contextual-dispatch".into())
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let mut dispatch = "()".to_owned();
                for _ in 0..16 {
                    dispatch = format!("apply({{ {dispatch} }})");
                }
                let source = format!(
                    "apply<F, R>(body: F) -> R where F: Fn<(), Output=R> {{ body() }}
                     dispatch()->() {{ {dispatch} }}
                     main()->(){{()}}"
                );
                CONTEXTUAL_VALIDATION_CACHE_HITS.with(|hits| hits.set(0));
                let first = parse_discovery(&source);
                let cache_hits = CONTEXTUAL_VALIDATION_CACHE_HITS.with(Cell::get);
                CONTEXTUAL_VALIDATION_CACHE_HITS.with(|hits| hits.set(0));
                let second = parse_discovery(&source);
                assert!(first.errors.is_empty(), "{:#?}", first.errors);
                assert!(
                    cache_hits >= 14,
                    "nested dispatch should reuse its contextual suffix validations, got {cache_hits}"
                );
                assert_eq!(first.graph.canonical_text(), second.graph.canonical_text());
                assert_eq!(first.graph.fingerprint(), second.graph.fingerprint());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn callable_parameter_direct_calls_and_concrete_dependencies_are_discovered() {
        let discovery = parse_discovery(
            "id<T>(value: T) -> T { value }
             outer<T>(value: T) -> T { id(value) }
             use() -> i64 { outer(1) }",
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        assert_eq!(discovery.graph.requests.len(), 2);
        assert_eq!(discovery.graph.edges.len(), 1);
        let (parent, child) = discovery.graph.edges.iter().next().unwrap();
        assert_eq!(parent.template, DeclarationKey::Function("outer".into()));
        assert_eq!(child.template, DeclarationKey::Function("id".into()));

        let callable = parse_discovery(
            "apply<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
             use() -> i64 { apply({ 1 }) }",
        );
        assert!(callable.errors.is_empty(), "{:#?}", callable.errors);
        assert_eq!(callable.graph.requests.len(), 1);
        let apply_key = callable.graph.requests.keys().next().unwrap().clone();
        assert!(callable.graph.direct_calls.keys().any(|site| matches!(
            &site.body,
            BodyInstanceKey::Root(DeclarationKey::Function(name)) if name == "use"
        )));
        assert!(callable.graph.callable_calls.iter().any(|(site, closure)| {
            matches!(&site.body, BodyInstanceKey::Specialization(key) if key == &apply_key)
                && callable.graph.closure_bodies.contains_key(closure)
        }));
    }

    #[test]
    fn calls_inside_closure_wrappers_have_their_own_stable_body_context() {
        let discovery = parse_discovery(
            "id<T>(value: T) -> T { value }
             apply<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
             use() -> i64 { apply({ id(1) }) }",
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        assert!(discovery.graph.direct_calls.iter().any(|(site, target)| {
            matches!(&site.body, BodyInstanceKey::Closure(_))
                && target.template == DeclarationKey::Function("id".into())
        }));
    }

    #[test]
    fn expected_result_can_ground_a_result_only_generic() {
        let discovery = parse_discovery("make<T>() -> T { 1 } use() -> i32 { make() }");
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        let request = discovery.graph.requests.values().next().unwrap();
        assert_eq!(
            request.key.arguments,
            vec![SpecializationArgument::Type(ProvisionalType::Predefined(
                "i32".into()
            ))]
        );
    }

    #[test]
    fn copy_capture_and_stored_closure_values_are_discovered() {
        let captured = parse_discovery(
            "apply<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
             use() -> i64 { let x = 1; apply({ x }) }",
        );
        assert!(captured.errors.is_empty(), "{:#?}", captured.errors);
        let closure = captured
            .graph
            .requests
            .values()
            .flat_map(|request| &request.closures)
            .next()
            .unwrap();
        assert_eq!(closure.captures.len(), 1);
        assert_eq!(closure.captures[0].name, "x");

        let escaping = parse_discovery("use() -> i64 { let f = { => 1 }; 1 }");
        assert!(escaping.graph.requests.is_empty());
        assert!(escaping.errors.is_empty(), "{:#?}", escaping.errors);
        assert_eq!(escaping.graph.closure_values.len(), 1);
    }

    #[test]
    fn capture_discovery_records_observe_mutate_and_move_environment_access() {
        let discovery = parse_discovery(
            "struct Ticket { marker: i64 }
             apply<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
             use(observed: i64, mutated: i64, moved: Ticket) -> {
                 apply({ => observed });
                 apply({ => { &mut mutated; () } });
                 apply({ => { move moved; () } });
                 ()
             }",
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        let modes = discovery
            .graph
            .requests
            .values()
            .flat_map(|request| &request.closures)
            .flat_map(|closure| &closure.captures)
            .map(|capture| (capture.name.as_str(), capture.mode))
            .collect::<BTreeMap<_, _>>();
        assert_eq!(modes["observed"], CaptureMode::Observe);
        assert_eq!(modes["mutated"], CaptureMode::Mutate);
        assert_eq!(modes["moved"], CaptureMode::Move);
    }

    #[test]
    fn globals_performs_and_handlers_are_traversed_with_effect_metadata_opaque() {
        let discovery = parse_discovery(
            "effect Ask { ask(value: i64) -> i64 }
             id<T>(value: T) -> T { value }
             let answer = id(1);
             use() -> i64 {
                 handle perform Ask::ask(id(2)) {
                     Ask::ask(value) => id(3)
                 }
             }",
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        assert_eq!(discovery.graph.requests.len(), 1);
        assert!(
            discovery
                .graph
                .roots
                .iter()
                .any(|(owner, _)| owner == &DeclarationKey::Global("answer".into()))
        );
        assert!(
            discovery
                .graph
                .roots
                .iter()
                .any(|(owner, _)| owner == &DeclarationKey::Function("use".into()))
        );
    }

    #[test]
    fn handler_resumption_closures_are_deferred_to_late_specialization() {
        let discovery = parse_discovery(
            "effect Stop { stop() -> i64 }
             apply<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
             use() -> i64 {
                 handle perform Stop::stop() {
                     Stop::stop() with k => apply({ k })
                 }
             }",
        );
        assert!(
            discovery.graph.requests.is_empty(),
            "graph={:#?} errors={:#?}",
            discovery.graph,
            discovery.errors
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        let plan = discovery
            .graph
            .late_closures
            .values()
            .next()
            .expect("resumption closure retains a late lowering plan");
        assert_eq!(plan.request.captures.len(), 1);
        assert_eq!(plan.request.captures[0].name, "k");
        assert!(contains_late_callable(&plan.request.captures[0].ty));
        assert_eq!(plan.request.receiver_mode(), 0);
    }

    #[test]
    fn nested_generic_callback_capture_is_static_specialization_evidence() {
        let source = "inner<G>(body: G) where G: Fn<(usize), Output=()> { body(0) }
             outer<F>(body: F) where F: Fn<(usize), Output=()> {
                 inner({ index => body(index) })
             }
             use() -> () { outer({ _ => () }) }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let discovery = discover(&program);
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        let nested = discovery
            .graph
            .closure_bodies
            .keys()
            .find(|request| request.static_captures.contains_key("body"))
            .expect("nested wrapper closure retains the exact outer callback identity");
        assert!(nested.captures.is_empty());
        assert_eq!(nested.static_captures["body"].len(), 1);
        let plan = emission_plan(&program, &discovery, None);
        assert!(plan.ordered.iter().all(|emission| {
            !matches!(emission, EmissionKey::Closure(request) if !request.static_captures.is_empty())
        }));
    }

    #[test]
    fn nested_transaction_call_collapses_temporary_contextual_binders() {
        let attempt_item = GenericParamKey {
            owner: DeclarationKey::Function("attempt_item".into()),
            ordinal: 0,
        };
        let commit = GenericParamKey {
            owner: DeclarationKey::Function("commit".into()),
            ordinal: 0,
        };
        let mut substitutions = BTreeMap::from([
            (
                attempt_item.clone(),
                SpecializationArgument::Type(ProvisionalType::Param(commit.clone())),
            ),
            (
                commit,
                SpecializationArgument::Type(ProvisionalType::Predefined("i64".into())),
            ),
        ]);

        collapse_type_substitution_chains(&mut substitutions);

        assert_eq!(
            substitutions[&attempt_item],
            SpecializationArgument::Type(ProvisionalType::Predefined("i64".into()))
        );
    }

    #[test]
    fn explicit_parameter_closure_retains_callable_aggregate_capture_and_move_receiver() {
        let discovery = parse_discovery(
            "effect Stop { stop() -> i64 }
             use() -> i64 {
                 handle perform Stop::stop() {
                     Stop::stop() with k => {
                         let saved = (move k,);
                         let finish = (value: i64) -> i64 {
                             let (continuation,) = move saved;
                             resume(move continuation, value)
                         };
                         move finish(42)
                     }
                 }
             }",
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        let plan = discovery
            .graph
            .late_closures
            .values()
            .find(|plan| !plan.request.shape.params.is_empty())
            .expect("explicit-parameter resumption closure plan");
        assert_eq!(
            plan.request.shape.params,
            vec![ProvisionalType::Predefined("i64".into())]
        );
        assert_eq!(plan.request.captures.len(), 1);
        assert_eq!(plan.request.captures[0].name, "saved");
        assert!(contains_late_callable(&plan.request.captures[0].ty));
        assert_eq!(plan.request.captures[0].mode, CaptureMode::Move);
        assert_eq!(plan.request.receiver_mode(), 2);
    }

    #[test]
    fn recursive_typed_closure_uses_receiver_identity_without_a_self_capture() {
        let source = "use() -> i64 {
                 let recurse = () -> ! { move recurse() };
                 42
             }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let ExprKind::Block(statements) = &program.functions[0].body.kind else {
            panic!()
        };
        let Stmt::Let { value, .. } = &statements[0] else {
            panic!()
        };
        assert!(recursive_closure_binding(value, "recurse"), "{value:#?}");
        let discovery = discover(&program);
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        let (request, recursive_self) = discovery
            .graph
            .recursive_closures
            .iter()
            .next()
            .unwrap_or_else(|| panic!("recursive closure plan: {discovery:#?}"));
        assert_eq!(recursive_self.binding, "recurse");
        assert_eq!(recursive_self.site, request.site);
        assert!(
            request.captures.is_empty(),
            "self is not an environment field"
        );
        let call = discovery
            .graph
            .recursive_self_calls
            .values()
            .next()
            .expect("recursive self call");
        assert_eq!(&call.recursive_self, recursive_self);
        assert_eq!(call.requested_receiver_mode, Some(2));
    }

    #[test]
    fn recursive_self_cannot_escape_during_closure_initialization() {
        let discovery = parse_discovery(
            "retain<T>(value: T) -> T { value }
             use() -> i64 {
                 let recurse = () -> ! { retain(recurse); move recurse() };
                 42
             }",
        );
        assert!(discovery.errors.iter().any(|error| {
            error
                .message
                .contains("receiver identity cannot escape during initialization")
        }));

        let inferred = parse_discovery(
            "use() -> i64 {
                 let recurse = { => recurse() };
                 42
             }",
        );
        assert!(inferred.errors.iter().any(|error| {
            error
                .message
                .contains("needs an explicit typed callable signature")
        }));

        let shadowed = crate::parser::parse(
            crate::lexer::lex(
                "use() -> i64 {
                     let recurse = (recurse: i64) -> i64 { recurse };
                     42
                 }",
            )
            .unwrap(),
        )
        .unwrap();
        let ExprKind::Block(statements) = &shadowed.functions[0].body.kind else {
            panic!()
        };
        let Stmt::Let { value, .. } = &statements[0] else {
            panic!()
        };
        assert!(!recursive_closure_binding(value, "recurse"));
    }

    #[test]
    fn later_shadow_does_not_constrain_an_earlier_initializer() {
        let discovery = parse_discovery(
            "make() -> i64 { 0 }
             identity<T>(value: T) -> T { value }
             consume(value: i64) -> Text { \"done\" }
             probe() -> Text {
                 let value = make();
                 let kept = identity(value);
                 let value = consume(move kept);
                 move value
             }",
        );
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        assert!(discovery.graph.direct_calls.values().any(|target| {
            matches!(&target.template, DeclarationKey::Function(name) if name == "identity")
        }));
    }

    #[test]
    fn recursive_late_and_generic_specializations_keep_deterministic_self_plans() {
        let late = parse_discovery(
            "effect Stop { stop() -> i64 }
             use() -> i64 {
                 handle perform Stop::stop() {
                     Stop::stop() with k => {
                         let recurse = (value: i64) -> i64 {
                             resume(move k, move recurse(value))
                         };
                         move recurse(42)
                     }
                 }
             }",
        );
        assert!(late.errors.is_empty(), "{:#?}", late.errors);
        let late_plan = late
            .graph
            .late_closures
            .values()
            .next()
            .expect("late recursive plan");
        assert_eq!(
            late_plan
                .recursive_self
                .as_ref()
                .map(|recursive_self| recursive_self.binding.as_str()),
            Some("recurse")
        );
        assert!(!late.graph.recursive_self_calls.is_empty());
        assert!(late.graph.recursive_self_calls.keys().all(|site| matches!(
            &site.body,
            BodyInstanceKey::Closure(request) if request == &late_plan.request
        )));

        let source = "run<T>(value: T) -> T {
                          let recurse = (item: T) -> T { recurse(item) };
                          recurse(value)
                      }
                      use() -> i64 { run(42) }";
        let first = parse_discovery(source);
        let second = parse_discovery(source);
        assert!(first.errors.is_empty(), "{:#?}", first.errors);
        assert_eq!(first.graph.canonical_text(), second.graph.canonical_text());
        assert_eq!(first.graph.fingerprint(), second.graph.fingerprint());
        assert!(!first.graph.recursive_closures.is_empty());
        assert!(!first.graph.recursive_self_calls.is_empty());
    }

    #[test]
    fn multi_argument_callable_shapes_check_arity_result_and_shadowing() {
        let accepted = parse_discovery(
            "apply<F, T, U, R>(left: T, right: U, body: F) -> R
                 where F: Fn<(T, U), Output=R> { body(left, right) }
             use(x: i64) -> i64 { apply(1, 2, { x, y => x }) }",
        );
        assert!(accepted.errors.is_empty(), "{:#?}", accepted.errors);
        assert_eq!(accepted.graph.requests.len(), 1);

        let arity = parse_discovery(
            "apply<F, T, R>(value: T, body: F) -> R
                 where F: Fn<(T), Output=R> { body(value) }
             use() -> i64 { apply(1, { => 2 }) }",
        );
        assert!(arity.graph.requests.is_empty());
        assert!(
            arity
                .errors
                .iter()
                .any(|error| error.message.contains("matching closure"))
        );

        let result = parse_discovery(
            r#"apply<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }
               use() -> i64 { apply({ "wrong" }) }"#,
        );
        assert!(result.graph.requests.is_empty());
        assert!(
            result
                .errors
                .iter()
                .any(|error| error.message.contains("result"))
        );

        let capture = parse_discovery(
            "apply<F, T, R>(value: T, body: F) -> R
                 where F: Fn<(T), Output=R> { body(value) }
             use(x: i64) -> i64 { apply(1, { y => x }) }",
        );
        assert!(capture.errors.is_empty(), "{:#?}", capture.errors);
        let closure = capture
            .graph
            .requests
            .values()
            .flat_map(|request| &request.closures)
            .next()
            .unwrap();
        assert_eq!(closure.captures.len(), 1);
        assert_eq!(closure.captures[0].name, "x");
    }

    #[test]
    fn canonical_discovery_is_declaration_order_independent_and_deduplicated() {
        let first = parse_discovery(
            "id<T>(value: T) -> T { value }
             use() -> i64 { let one = id(1); id(2) }",
        );
        let second = parse_discovery(
            "use() -> i64 { let one = id(1); id(2) }
             id<T>(value: T) -> T { value }",
        );
        assert_eq!(first.graph.requests.len(), 1);
        assert_eq!(first.graph.canonical_text(), second.graph.canonical_text());
        assert_eq!(first.graph.fingerprint(), second.graph.fingerprint());
    }

    #[test]
    fn unsupported_callable_goals_are_internal_discovery_errors() {
        let discovery = parse_discovery(
            "bad<F, R>(body: F) -> R where F: Fn<i64, Output=R> { body() }
             use() -> i64 { bad({ 1 }) }",
        );
        assert!(
            discovery.graph.requests.is_empty(),
            "graph={:#?} errors={:#?}",
            discovery.graph,
            discovery.errors
        );
        assert!(
            discovery
                .errors
                .iter()
                .any(|error| error.message.contains("exact `F: Fn"))
        );
    }

    #[test]
    fn callable_effect_escape_summary_tracks_aliases_handlers_and_forwarding_cycles() {
        let source = r#"
            effect Ask { [1,1] ask() -> i64 }
            effect Partial { [1,1] first() -> i64; [1,1] second() -> i64 }
            alias_invoke<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects={Ask}> {
                let saved = body;
                saved()
            }
            close<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects={Ask}> {
                handle { alias_invoke(body) } {
                    Ask::ask() with k => resume(k, 42)
                }
            }
            forward_close<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects={Ask}> { close(body) }
            cycle_a<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects={Ask}> { cycle_b(body) }
            cycle_b<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects={Ask}> { cycle_a(body) }
            live_cycle_a<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects={Ask}> { live_cycle_b(body) }
            live_cycle_b<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects={Ask}> {
                let ignored = live_cycle_a(body);
                body()
            }
            identity<F>(body: F) -> F
                where F: Fn<(), Output=i64, Effects={Ask}> { body }
            returned_invoke<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects={Ask}> { identity(body)() }
            invoke_wrapper<F>(wrapped: F) -> i64
                where F: Fn<(), Output=i64, Effects={Ask}> { wrapped() }
            captured_wrapper<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects={Ask}> {
                invoke_wrapper({ => body() })
            }
            closure_only<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects={Ask}> {
                let delayed = { => body() };
                42
            }
            partial_handler<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects={Partial}> {
                handle { body() } {
                    Partial::first() with k => resume(k, 42)
                }
            }
            main() -> { () }
        "#;
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let handler_closes =
            |clauses: &[crate::ast::HandlerClause],
             effect: &crate::compiler_typeck::CallableEffect| {
                effect.declaration.0 == "Ask"
                    && clauses
                        .iter()
                        .any(|clause| clause.effect == "Ask" && clause.operation == "ask")
            };
        let escapes = |function: &str, effect: &str| {
            let function = program
                .functions
                .iter()
                .find(|candidate| candidate.name == function)
                .unwrap();
            let effect = crate::compiler_typeck::CallableEffect {
                declaration: crate::compiler_typeck::ProtocolKey(effect.to_owned()),
                arguments: vec![],
            };
            callable_effect_escapes(&program, function, "body", &effect, &handler_closes)
        };

        assert!(escapes("alias_invoke", "Ask"));
        assert!(!escapes("close", "Ask"));
        assert!(!escapes("forward_close", "Ask"));
        assert!(
            !escapes("cycle_a", "Ask") && !escapes("cycle_b", "Ask"),
            "a forwarding-only recursive SCC has the least fixed point `false`"
        );
        assert!(escapes("live_cycle_a", "Ask") && escapes("live_cycle_b", "Ask"));
        assert!(escapes("returned_invoke", "Ask"));
        assert!(escapes("captured_wrapper", "Ask"));
        assert!(!escapes("closure_only", "Ask"));
        assert!(
            escapes("partial_handler", "Partial"),
            "a handler that omits an operation must not close the protocol"
        );
        let discovery = discover(&program);
        let captured = discovery
            .graph
            .templates
            .get(&DeclarationKey::Function("captured_wrapper".into()))
            .unwrap();
        assert_eq!(captured.effectful_callable_binders.len(), 1);
    }

    #[test]
    fn public_compilation_accepts_a_transparent_generic_identity() {
        let source = "id<T>(value: T) -> T { value } main() -> { () }";
        crate::compile_source_to_bytecode("generic.grand", source).unwrap();
    }

    #[test]
    fn stored_zero_argument_closure_retains_value_and_indirect_call_plans() {
        let source = "main()->i64 { let answer = { => 42 }; answer() }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let discovery = discover(&program);
        assert!(discovery.errors.is_empty(), "{:#?}", discovery.errors);
        assert_eq!(discovery.graph.closure_values.len(), 1);
        assert_eq!(discovery.graph.indirect_calls.len(), 1);
        let request = discovery.graph.closure_values.values().next().unwrap();
        assert_eq!(request.receiver_mode(), 0);
        assert!(discovery.graph.closure_bodies.contains_key(request));
        assert!(
            emission_plan(&program, &discovery, None)
                .ordered
                .contains(&EmissionKey::Closure(request.clone()))
        );
    }
}
