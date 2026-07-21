//! Deterministic, allocation-independent specialization request discovery.
//!
//! This phase is intentionally rejection-only: it records requirements that a
//! future generic lowering could satisfy, but never authorizes bytecode emission.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::ast::{
    AssignmentPlaceKind, AssociatedArgumentSyntax, Expr, ExprKind, GenericParamKind, GoalArgument,
    GoalPolarity, PatternKind, Program, Stmt, TypeSyntax, TypeSyntaxKind, UnaryOp,
};
use crate::compiler_traits::{
    AssociatedValue, ConstValue, GenericArg, GenericParameterKind, IntrinsicRole, LifetimeArg,
    ParamEnv, SolveResult, SolverBudget, TraitDb, TraitFact, TraitKey,
};
use crate::compiler_typeck::{
    CallableShape, DeclarationKey, GenericParamKey, NominalInstanceKey, NominalKey, ProvisionalType,
};

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
    ),
}

pub(crate) fn contains_late_callable(ty: &ProvisionalType) -> bool {
    match ty {
        ProvisionalType::Callable(_) => true,
        ProvisionalType::Nominal(instance) => instance.arguments.iter().any(contains_late_callable),
        ProvisionalType::Tuple(elements) => elements.iter().any(contains_late_callable),
        ProvisionalType::Shared(referent) | ProvisionalType::Unique(referent) => {
            contains_late_callable(referent)
        }
        ProvisionalType::Predefined(_) | ProvisionalType::Param(_) => false,
    }
}

fn late_specialization(key: &SpecializationKey) -> bool {
    key.arguments.iter().any(|argument| {
        matches!(argument, SpecializationArgument::Type(ty) if contains_late_callable(ty))
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
        // A first-class shared-reference environment is deliberately
        // single-shot in this bounded slice. Moving the environment into the
        // call exposes its stored reference as an ordinary local, so the
        // existing verifier need not copy a reference value through a borrowed
        // environment (`&&T -> &T`) without provenance evidence.
        if self
            .captures
            .iter()
            .any(|capture| contains_any_reference_shape(&capture.ty))
        {
            return 2;
        }
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

fn contains_any_reference_shape(ty: &ProvisionalType) -> bool {
    match ty {
        ProvisionalType::Shared(_) | ProvisionalType::Unique(_) => true,
        ProvisionalType::Tuple(elements) => elements.iter().any(contains_any_reference_shape),
        ProvisionalType::Nominal(instance) => {
            instance.arguments.iter().any(contains_any_reference_shape)
        }
        ProvisionalType::Callable(shape) => {
            shape.params.iter().any(contains_any_reference_shape)
                || contains_any_reference_shape(&shape.result)
        }
        ProvisionalType::Predefined(_) | ProvisionalType::Param(_) => false,
    }
}

fn contains_late_callable_captures(request: &ClosureRequest) -> bool {
    request
        .captures
        .iter()
        .any(|capture| contains_late_callable(&capture.ty))
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
    pub(crate) callable_calls: BTreeMap<CallSiteKey, ClosureRequest>,
    /// First-class closure construction sites retained as runtime values.
    pub(crate) closure_values: BTreeMap<CallSiteKey, ClosureRequest>,
    /// Calls through a retained closure local rather than a scalarized wrapper.
    pub(crate) indirect_calls: BTreeMap<CallSiteKey, ClosureRequest>,
    /// Explicit receiver mode requested at an indirect call site (`move f()` is owned).
    pub(crate) indirect_call_modes: BTreeMap<CallSiteKey, u32>,
    /// Exact closure identity returned by a specialized callable-valued call.
    pub(crate) returned_closures: BTreeMap<CallSiteKey, ClosureRequest>,
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
    /// closure. Kept outside `ClosureRequest` so legacy compiler construction
    /// sites remain source-compatible until Core consumes the contract.
    pub(crate) recursive_closures: BTreeMap<ClosureRequest, RecursiveSelf>,
    /// Calls which target the current callable receiver rather than a captured
    /// callable value. Core chooses CallSelf versus TailCallSelf from position.
    pub(crate) recursive_self_calls: BTreeMap<CallSiteKey, RecursiveSelfCall>,
    pub(crate) erased_callable_aliases: BTreeSet<CallSiteKey>,
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
        for call in &self.callable_calls {
            writeln!(output, "callable-call {call:?}").unwrap();
        }
        for value in &self.closure_values {
            writeln!(output, "closure-value {value:?}").unwrap();
        }
        for call in &self.indirect_calls {
            writeln!(output, "indirect-call {call:?}").unwrap();
        }
        for mode in &self.indirect_call_modes {
            writeln!(output, "indirect-call-mode {mode:?}").unwrap();
        }
        for returned in &self.returned_closures {
            writeln!(output, "returned-closure {returned:?}").unwrap();
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
            } else if matches!(
                name.as_str(),
                "Unit"
                    | "Text"
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
        TypeSyntaxKind::SharedReference(referent) => {
            symbolic_type(referent, generics, callable_constraints).map(ProvisionalType::shared)
        }
        TypeSyntaxKind::UniqueReference(referent) => {
            symbolic_type(referent, generics, callable_constraints).map(ProvisionalType::unique)
        }
        _ => None,
    }
}

fn const_identity(value: &crate::ast::ConstArgumentValueSyntax) -> Option<ProvisionalType> {
    let name = match value {
        crate::ast::ConstArgumentValueSyntax::U32 { value, .. } => {
            format!("$const$u32${}", u32::try_from(*value).ok()?)
        }
        crate::ast::ConstArgumentValueSyntax::Quantity(quantity) => {
            let lower = u32::try_from(quantity.lower).ok()?;
            let upper = quantity
                .upper
                .map(u32::try_from)
                .transpose()
                .ok()?
                .map_or_else(|| "infinity".to_owned(), |upper| upper.to_string());
            format!("$const$quantity${lower}${upper}")
        }
    };
    Some(ProvisionalType::Predefined(name))
}

/// Enrich the legacy type/lifetime application tree with structural const
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
                    merged.push(const_identity(value)?);
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
        (TypeSyntaxKind::SharedReference(source), ProvisionalType::Shared(target))
        | (TypeSyntaxKind::UniqueReference(source), ProvisionalType::Unique(target)) => {
            **target = symbolic_type_in(program, source, generics, callable_constraints)?;
        }
        _ => {}
    }
    Some(ty)
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
                .map(|param| symbolic_type_in(program, param, generics, &BTreeMap::new()))
                .collect::<Option<Vec<_>>>()?;
            let output_binding = output_binding?;
            let output = output_binding.value.as_type()?;
            let result = symbolic_type_in(program, output, generics, &BTreeMap::new())?;
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
            ExprKind::Block(statements) => {
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
            ExprKind::Labeled { body, .. } | ExprKind::LabelDestination { body, .. } => {
                callable_use_summary(body, aliases, callable_positions, dependencies)
            }
            ExprKind::Leave { value, .. } => value.as_deref().is_some_and(|value| {
                callable_use_summary(value, aliases, callable_positions, dependencies)
            }),
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
            ExprKind::Resume { .. }
            | ExprKind::Cancel { .. }
            | ExprKind::TailResume { .. }
            | ExprKind::ContextBlock(_) => unvalidated_syntax(),
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
                    GenericParamKind::Type | GenericParamKind::Const(_)
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

pub(crate) fn substitute(
    ty: &ProvisionalType,
    substitutions: &BTreeMap<GenericParamKey, SpecializationArgument>,
) -> Option<ProvisionalType> {
    fn resolve_value(
        ty: &ProvisionalType,
        substitutions: &BTreeMap<GenericParamKey, SpecializationArgument>,
        visiting: &mut BTreeSet<GenericParamKey>,
    ) -> Option<ProvisionalType> {
        match ty {
            ProvisionalType::Param(key) => {
                let Some(argument) = substitutions.get(key) else {
                    // Substitution values may terminate in a rigid variable
                    // owned by the generic caller.
                    return Some(ty.clone());
                };
                if !visiting.insert(key.clone()) {
                    return None;
                }
                let resolved = match argument {
                    SpecializationArgument::Type(value) => {
                        resolve_value(value, substitutions, visiting)
                    }
                    SpecializationArgument::Closure(_, shape, _, _) => {
                        Some(ProvisionalType::Callable(shape.clone()))
                    }
                    SpecializationArgument::EffectRow(_) => None,
                };
                visiting.remove(key);
                resolved
            }
            ProvisionalType::Shared(inner) => {
                resolve_value(inner, substitutions, visiting).map(ProvisionalType::shared)
            }
            ProvisionalType::Unique(inner) => {
                resolve_value(inner, substitutions, visiting).map(ProvisionalType::unique)
            }
            ProvisionalType::Tuple(elements) => Some(ProvisionalType::Tuple(
                elements
                    .iter()
                    .map(|element| resolve_value(element, substitutions, visiting))
                    .collect::<Option<Vec<_>>>()?,
            )),
            ProvisionalType::Nominal(instance) => {
                Some(ProvisionalType::Nominal(NominalInstanceKey {
                    declaration: instance.declaration.clone(),
                    arguments: instance
                        .arguments
                        .iter()
                        .map(|argument| resolve_value(argument, substitutions, visiting))
                        .collect::<Option<Vec<_>>>()?,
                }))
            }
            ProvisionalType::Callable(shape) => {
                Some(ProvisionalType::Callable(Box::new(CallableShape {
                    params: shape
                        .params
                        .iter()
                        .map(|param| resolve_value(param, substitutions, visiting))
                        .collect::<Option<Vec<_>>>()?,
                    result: resolve_value(&shape.result, substitutions, visiting)?,
                    effects: shape
                        .effects
                        .iter()
                        .map(|effect| {
                            Some(crate::compiler_typeck::CallableEffect {
                                declaration: effect.declaration.clone(),
                                arguments: effect
                                    .arguments
                                    .iter()
                                    .map(|argument| {
                                        resolve_value(argument, substitutions, visiting)
                                    })
                                    .collect::<Option<Vec<_>>>()?,
                            })
                        })
                        .collect::<Option<Vec<_>>>()?,
                    effect_tail: shape.effect_tail.clone(),
                    infer_effects: shape.infer_effects,
                })))
            }
            ProvisionalType::Predefined(_) => Some(ty.clone()),
        }
    }

    match ty {
        ProvisionalType::Param(key) => match substitutions.get(key)? {
            SpecializationArgument::Type(value) => {
                if value == ty {
                    // Recursive symbolic validation uses the declaration's
                    // canonical binder as both caller-rigid and callee-local.
                    Some(value.clone())
                } else {
                    resolve_value(value, substitutions, &mut BTreeSet::from([key.clone()]))
                }
            }
            SpecializationArgument::Closure(_, shape, _, _) => {
                Some(ProvisionalType::Callable(shape.clone()))
            }
            SpecializationArgument::EffectRow(_) => None,
        },
        ProvisionalType::Shared(referent) => {
            substitute(referent, substitutions).map(ProvisionalType::shared)
        }
        ProvisionalType::Unique(referent) => {
            substitute(referent, substitutions).map(ProvisionalType::unique)
        }
        ProvisionalType::Callable(shape) => {
            Some(ProvisionalType::Callable(Box::new(CallableShape {
                params: shape
                    .params
                    .iter()
                    .map(|param| substitute(param, substitutions))
                    .collect::<Option<Vec<_>>>()?,
                result: substitute(&shape.result, substitutions)?,
                effects: shape
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
                effect_tail: shape.effect_tail.clone(),
                infer_effects: shape.infer_effects,
            })))
        }
        ProvisionalType::Nominal(instance) => Some(ProvisionalType::Nominal(NominalInstanceKey {
            declaration: instance.declaration.clone(),
            arguments: instance
                .arguments
                .iter()
                .map(|argument| substitute(argument, substitutions))
                .collect::<Option<Vec<_>>>()?,
        })),
        ProvisionalType::Tuple(elements) => Some(ProvisionalType::Tuple(
            elements
                .iter()
                .map(|element| substitute(element, substitutions))
                .collect::<Option<Vec<_>>>()?,
        )),
        concrete => Some(concrete.clone()),
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
                SpecializationArgument::Type(ProvisionalType::Predefined(name)) => match kind {
                    crate::ast::ConstKind::U32 => name
                        .strip_prefix("$const$u32$")
                        .and_then(|value| value.parse().ok())
                        .map(ConstValue::U32),
                    crate::ast::ConstKind::Quantity => {
                        let value = name.strip_prefix("$const$quantity$")?;
                        let (lower, upper) = value.split_once('$')?;
                        let lower = lower.parse().ok()?;
                        let upper = (upper != "infinity")
                            .then(|| upper.parse())
                            .transpose()
                            .ok()?;
                        Some(ConstValue::Quantity { lower, upper })
                    }
                },
                _ => None,
            })
            .map(GenericArg::Const),
    }
}

fn ground(ty: &ProvisionalType) -> bool {
    match ty {
        ProvisionalType::Param(_) => false,
        ProvisionalType::Shared(referent) | ProvisionalType::Unique(referent) => ground(referent),
        ProvisionalType::Callable(shape) => {
            shape.params.iter().all(ground)
                && ground(&shape.result)
                && shape
                    .effects
                    .iter()
                    .flat_map(|effect| &effect.arguments)
                    .all(ground)
        }
        ProvisionalType::Nominal(instance) => instance.arguments.iter().all(ground),
        ProvisionalType::Tuple(elements) => elements.iter().all(ground),
        ProvisionalType::Predefined(_) => true,
    }
}

fn supported_capture_shape(ty: &ProvisionalType) -> bool {
    match ty {
        ProvisionalType::Predefined(_) => true,
        ProvisionalType::Nominal(instance) => {
            instance.arguments.iter().all(supported_capture_shape)
        }
        ProvisionalType::Tuple(elements) => elements.iter().all(supported_capture_shape),
        ProvisionalType::Shared(referent) | ProvisionalType::Unique(referent) => {
            supported_capture_shape(referent)
        }
        ProvisionalType::Callable(_) | ProvisionalType::Param(_) => false,
    }
}

fn contains_unique_reference_shape(ty: &ProvisionalType) -> bool {
    match ty {
        ProvisionalType::Unique(_) => true,
        ProvisionalType::Shared(referent) => contains_unique_reference_shape(referent),
        ProvisionalType::Tuple(elements) => elements.iter().any(contains_unique_reference_shape),
        ProvisionalType::Nominal(instance) => instance
            .arguments
            .iter()
            .any(contains_unique_reference_shape),
        ProvisionalType::Callable(shape) => {
            shape.params.iter().any(contains_unique_reference_shape)
                || contains_unique_reference_shape(&shape.result)
        }
        ProvisionalType::Predefined(_) | ProvisionalType::Param(_) => false,
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
            Some(SpecializationArgument::Closure(_, shape, _, _)) => {
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
            && (left.infer_effects || (!right.infer_effects && left.effects.len() == right.effects.len()))
            && left.params.iter().zip(&right.params).all(|(left, right)| bind(left, right, substitutions))
            && bind(&left.result, &right.result, substitutions)
            && (left.infer_effects || left.effects.iter().zip(&right.effects).all(|(left, right)| {
                left.declaration == right.declaration
                    && left.arguments.len() == right.arguments.len()
                    && left.arguments.iter().zip(&right.arguments).all(|(left, right)| {
                        bind(left, right, substitutions)
                    })
            }))),
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
    match ty {
        ProvisionalType::Param(candidate) => {
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
                    SpecializationArgument::Closure(_, shape, _, _) => {
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
        }
        ProvisionalType::Shared(inner) | ProvisionalType::Unique(inner) => {
            inference_occurs(key, inner, substitutions, visiting)
        }
        ProvisionalType::Tuple(elements) => elements
            .iter()
            .any(|ty| inference_occurs(key, ty, substitutions, visiting)),
        ProvisionalType::Nominal(instance) => instance
            .arguments
            .iter()
            .any(|ty| inference_occurs(key, ty, substitutions, visiting)),
        ProvisionalType::Callable(shape) => {
            shape
                .params
                .iter()
                .any(|ty| inference_occurs(key, ty, substitutions, visiting))
                || inference_occurs(key, &shape.result, substitutions, visiting)
                || shape
                    .effects
                    .iter()
                    .flat_map(|effect| &effect.arguments)
                    .any(|ty| inference_occurs(key, ty, substitutions, visiting))
        }
        ProvisionalType::Predefined(_) => false,
    }
}

fn unify_inference(
    left: &ProvisionalType,
    right: &ProvisionalType,
    mutable: &BTreeSet<GenericParamKey>,
    substitutions: &mut BTreeMap<GenericParamKey, SpecializationArgument>,
) -> bool {
    fn resolve(
        ty: &ProvisionalType,
        substitutions: &BTreeMap<GenericParamKey, SpecializationArgument>,
    ) -> ProvisionalType {
        match ty {
            ProvisionalType::Param(key) => match substitutions.get(key) {
                Some(SpecializationArgument::Type(value)) if value != ty => {
                    resolve(value, substitutions)
                }
                Some(SpecializationArgument::Closure(_, shape, _, _)) => {
                    ProvisionalType::Callable(shape.clone())
                }
                _ => ty.clone(),
            },
            _ => ty.clone(),
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
        if let ProvisionalType::Param(key) = &left
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
        return bind_var(key, &right, substitutions);
    }
    if let ProvisionalType::Param(key) = &right
        && mutable.contains(key)
    {
        return bind_var(key, &left, substitutions);
    }
    match (&left, &right) {
        (ProvisionalType::Shared(a), ProvisionalType::Shared(b))
        | (ProvisionalType::Unique(a), ProvisionalType::Unique(b)) => {
            unify_inference(a, b, mutable, substitutions)
        }
        (ProvisionalType::Tuple(a), ProvisionalType::Tuple(b)) if a.len() == b.len() => a
            .iter()
            .zip(b)
            .all(|(a, b)| unify_inference(a, b, mutable, substitutions)),
        (ProvisionalType::Nominal(a), ProvisionalType::Nominal(b))
            if a.declaration == b.declaration && a.arguments.len() == b.arguments.len() =>
        {
            a.arguments
                .iter()
                .zip(&b.arguments)
                .all(|(a, b)| unify_inference(a, b, mutable, substitutions))
        }
        (ProvisionalType::Callable(a), ProvisionalType::Callable(b))
            if a.params.len() == b.params.len() && a.effects == b.effects =>
        {
            a.params
                .iter()
                .zip(&b.params)
                .all(|(a, b)| unify_inference(a, b, mutable, substitutions))
                && unify_inference(&a.result, &b.result, mutable, substitutions)
        }
        _ => false,
    }
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
            ExprKind::Block(statements) => {
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
            ExprKind::Labeled { body, .. } | ExprKind::LabelDestination { body, .. } => {
                visit(body, outer, bound, found, CaptureMode::Observe)
            }
            ExprKind::Leave { value, .. } => {
                if let Some(value) = value {
                    visit(value, outer, bound, found, CaptureMode::Observe);
                }
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
            // The parser's grammar-complete forms are rejected by `validate` or
            // rewritten by `parser::normalize_for_legacy_consumers` before any
            // compiler pass runs; reaching one here is a broken phase invariant.
            ExprKind::LabelReference(_) => {}
            ExprKind::Resume { .. }
            | ExprKind::Cancel { .. }
            | ExprKind::TailResume { .. }
            | ExprKind::ContextBlock(_) => unvalidated_syntax(),
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
/// space. Calls are checked from their generated signatures later; this pass
/// exists to seal an omitted `Fn::Effects` projection without protocol-table
/// allocation identities. A handled protocol is removed only for the body of
/// that handler; final coverage checking remains authoritative in Core lowering.
fn direct_closure_effects(
    expression: &Expr,
    resolve: &impl Fn(crate::span::Span, &str) -> Option<crate::compiler_typeck::CallableEffect>,
) -> BTreeSet<crate::compiler_typeck::CallableEffect> {
    fn visit(
        expression: &Expr,
        resolve: &impl Fn(crate::span::Span, &str) -> Option<crate::compiler_typeck::CallableEffect>,
        output: &mut BTreeSet<crate::compiler_typeck::CallableEffect>,
    ) {
        match &expression.kind {
            ExprKind::Perform { effect, args, .. } => {
                for argument in args.iter() {
                    visit(argument, resolve, output);
                }
                if let Some(effect) = resolve(expression.span, effect) {
                    output.insert(effect);
                }
            }
            ExprKind::Handle {
                computation,
                clauses,
            } => {
                let mut nested = BTreeSet::new();
                visit(computation, resolve, &mut nested);
                for clause in clauses.iter() {
                    if let Some(effect) = resolve(clause.span, &clause.effect) {
                        nested.remove(&effect);
                    }
                    visit(&clause.body, resolve, output);
                }
                output.extend(nested);
            }
            ExprKind::Block(statements) => {
                for statement in statements.iter() {
                    match statement {
                        Stmt::Let { value, .. }
                        | Stmt::Deconstruct { value, .. }
                        | Stmt::Expr(value) => visit(value, resolve, output),
                        Stmt::Assign {
                            destination, value, ..
                        } => {
                            visit(value, resolve, output);
                            if let AssignmentPlaceKind::Dereference { reference, .. } =
                                &destination.kind
                            {
                                visit(reference, resolve, output);
                            }
                        }
                    }
                }
            }
            ExprKind::List(values) | ExprKind::Tuple(values) => {
                for value in values.iter() {
                    visit(value, resolve, output);
                }
            }
            ExprKind::Struct { fields, .. } => {
                for (_, value) in fields.iter() {
                    visit(value, resolve, output);
                }
            }
            ExprKind::Closure { .. } | ExprKind::TypedClosure { .. } => {}
            ExprKind::Move(value)
            | ExprKind::Field(value, _)
            | ExprKind::Unary { operand: value, .. } => visit(value, resolve, output),
            ExprKind::Call(callee, arguments) => {
                visit(callee, resolve, output);
                for argument in arguments.iter() {
                    visit(argument, resolve, output);
                }
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                visit(lhs, resolve, output);
                visit(rhs, resolve, output);
            }
            ExprKind::Labeled { body, .. } | ExprKind::LabelDestination { body, .. } => {
                visit(body, resolve, output)
            }
            ExprKind::Leave { value, .. } => {
                if let Some(value) = value {
                    visit(value, resolve, output);
                }
            }
            ExprKind::Is { subject, .. } => visit(subject, resolve, output),
            ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Char(_)
            | ExprKind::Byte(_)
            | ExprKind::ByteString(_)
            | ExprKind::String(_)
            | ExprKind::Variable(_) => {}
            // The parser's grammar-complete forms are rejected by `validate` or
            // rewritten by `parser::normalize_for_legacy_consumers` before any
            // compiler pass runs; reaching one here is a broken phase invariant.
            ExprKind::LabelReference(_) => {}
            ExprKind::Resume { .. }
            | ExprKind::Cancel { .. }
            | ExprKind::TailResume { .. }
            | ExprKind::ContextBlock(_) => unvalidated_syntax(),
        }
    }
    let mut effects = BTreeSet::new();
    visit(expression, resolve, &mut effects);
    effects
}

#[derive(Clone)]
enum LocalBinding {
    Type(ProvisionalType),
    Closure(ClosureRequest),
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
    provisionally_called: bool,
}

enum PlannedClosure {
    Exact(ClosureRequest),
    Late(ClosureRequest),
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
                let params = operation
                    .params
                    .iter()
                    .map(|param| symbolic_type(&param.ty, &generic_map, &BTreeMap::new()))
                    .collect::<Option<Vec<_>>>()?;
                let result = operation.return_type.as_ref().map_or_else(
                    || Some(ProvisionalType::Predefined("Unit".into())),
                    |ty| symbolic_type(ty, &generic_map, &BTreeMap::new()),
                )?;
                Some((
                    (effect.name.clone(), operation.name.clone()),
                    OperationTemplate {
                        effect_params: effect_params.clone(),
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
    expression_ordinals: &'a BTreeMap<usize, u32>,
    body_instance: BodyInstanceKey,
    recording: bool,
    trait_db: &'a TraitDb,
    solver_budget: &'a mut SolverBudget,
    param_env: ParamEnv,
    symbolic_validation: bool,
    active_recursive_self: Option<RecursiveSelf>,
}

impl<'a> Walker<'a> {
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
        match ty {
            ProvisionalType::Predefined(_) | ProvisionalType::Param(_) => true,
            ProvisionalType::Nominal(instance) => {
                self.nominal_templates
                    .contains_key(instance.declaration.0.as_str())
                    && instance
                        .arguments
                        .iter()
                        .all(|argument| self.symbolically_known_type(argument))
            }
            ProvisionalType::Tuple(elements) => elements
                .iter()
                .all(|element| self.symbolically_known_type(element)),
            ProvisionalType::Shared(referent) | ProvisionalType::Unique(referent) => {
                self.symbolically_known_type(referent)
            }
            ProvisionalType::Callable(shape) => {
                shape
                    .params
                    .iter()
                    .all(|param| self.symbolically_known_type(param))
                    && self.symbolically_known_type(&shape.result)
            }
        }
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
            params: template
                .params
                .iter()
                .map(|param| substitute(param, &substitutions))
                .collect::<Option<Vec<_>>>()?,
            result: substitute(&template.result, &substitutions)?,
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
                                })
                                .collect(),
                        }),
                        false,
                    )),
                    Some(
                        LocalBinding::Closure(_)
                        | LocalBinding::DeferredFunctionItem(_)
                        | LocalBinding::ClosureTuple(_)
                        | LocalBinding::RecursiveSelf(_, _),
                    )
                    | None => None,
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
            PatternKind::Variant { path, fields } if path.len() == 2 => {
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
                if template.params.len() != instance.arguments.len()
                    || formals.len() != fields.len()
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
                    for (field, ty) in fields.iter().zip(&resolved) {
                        self.bind_handler_pattern(field, ty);
                    }
                }
            }
            PatternKind::Tuple { elements, rest } => {
                let ProvisionalType::Tuple(element_types) = ty else {
                    return;
                };
                if elements.len() > element_types.len()
                    || (rest.is_none() && elements.len() != element_types.len())
                {
                    return;
                }
                for (position, element) in elements.iter().enumerate() {
                    let index = match rest {
                        Some(rest) if position >= rest.before => {
                            element_types.len() - (elements.len() - position)
                        }
                        _ => position,
                    };
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
            ProvisionalType::Predefined(name) => match name.as_str() {
                "Never" => (1, Some(1)),
                "Unit" | "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "i8" | "i16" | "i32"
                | "i64" | "i128" | "isize" | "Text" => (0, None),
                _ => return None,
            },
            ProvisionalType::Nominal(instance) => {
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
                selected?
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
            ProvisionalType::Callable(_) | ProvisionalType::Param(_) => return None,
        };
        visiting.remove(subject);
        Some(principal)
    }

    fn intrinsic_use_evidence(
        &self,
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
        let principal = match exact_argument {
            Some(SpecializationArgument::Closure(_, shape, captures, _))
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
            _ => self.principal_use_evidence(subject, &mut BTreeSet::new())?,
        };
        let [GenericArg::Const(ConstValue::Quantity { lower, upper })] = arguments else {
            return Some(false);
        };
        let lower_contained = principal.0 <= *lower;
        let upper_contained = match (principal.1, *upper) {
            (None, _) => true,
            (Some(_), None) => false,
            (Some(principal), Some(requested)) => principal >= requested,
        };
        Some(lower_contained && upper_contained)
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
        if row.tail.is_some() {
            self.error(format!(
                "generic function item `{target}` has an unresolved outward effect-row tail"
            ));
            return None;
        }
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
        effects
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
            .collect()
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
            ExprKind::Block(_) if expected.params.is_empty() => {
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
        let mut late = false;
        for (name, mode) in captured_outer_uses(body, &outer, &params) {
            if let Some(LocalBinding::RecursiveSelf(recursive_self, _)) = self.locals.get(&name)
                && self.active_recursive_self.as_ref() == Some(recursive_self)
            {
                // Recursive calls reuse the current receiver identity. The
                // binding is planning evidence, never an environment field.
                continue;
            }
            let Some(LocalBinding::Type(ty)) = self.locals.get(&name) else {
                self.error(format!(
                    "captureful closure specialization: closure capture `{name}` is not an ordinary typed local"
                ));
                return None;
            };
            let ty = substitute(ty, substitutions).unwrap_or_else(|| ty.clone());
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
        for (name, ty) in params.iter().zip(&expected.params) {
            let ty = substitute(ty, substitutions).unwrap_or_else(|| ty.clone());
            self.locals.insert(name.clone(), LocalBinding::Type(ty));
            self.bindings.insert(name.clone());
        }
        let saved_recording = self.recording;
        self.recording = false;
        let expected_result =
            substitute(&expected.result, substitutions).unwrap_or_else(|| expected.result.clone());
        let actual_result = self.expression(body, Some(&expected_result));
        self.recording = saved_recording;
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
        let inferred_effects =
            direct_closure_effects(body, &|site, effect| self.effect_instance(site, effect));
        if let Some(declared) = &declared {
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
        }
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
            && !inferred_effects.is_subset(&expected_effects)
        {
            let missing = inferred_effects
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
            let residual = inferred_effects
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
            expected_effects.union(&inferred_effects).cloned().collect()
        } else if expected.infer_effects {
            inferred_effects.into_iter().collect()
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
        };
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
                self.discovery.graph.late_closures.insert(
                    call_site,
                    LateClosurePlan {
                        request: request.clone(),
                        body_kind,
                        recursive_self: self.active_recursive_self.clone(),
                    },
                );
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
        // Shared-reference captures carry their concrete origin through the
        // callable value and are checked by ordinary region/return analysis.
        // Unique captures still need per-environment reborrow ownership so a
        // moved callable can release exactly its own loan without aliasing the
        // source reference.
        if let Some(capture) = request
            .captures
            .iter()
            .find(|capture| contains_unique_reference_shape(&capture.ty))
        {
            self.error(format!(
                "typed closure value captures the unique reference `{}`; unique borrowed captures cannot escape into a first-class callable environment",
                capture.name
            ));
            return None;
        }
        if self.recording && !contains_late_callable_captures(&request) {
            let site = self.call_site(expression)?;
            self.discovery
                .graph
                .closure_values
                .insert(site, request.clone());
        }
        (!contains_late_callable_captures(&request)).then_some(request)
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
                effects: direct_closure_effects(body, &|site, effect| {
                    self.effect_instance(site, effect)
                })
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
        for (value, formal) in values {
            let exact_closure = match &value.kind {
                ExprKind::Variable(path) if path.len() == 1 => {
                    match self.locals.get(path[0].as_ref()).cloned() {
                        Some(LocalBinding::Closure(closure)) => Some(closure),
                        _ => None,
                    }
                }
                ExprKind::Move(operand) => match &operand.kind {
                    ExprKind::Variable(path) if path.len() == 1 => {
                        match self.locals.get(path[0].as_ref()).cloned() {
                            Some(LocalBinding::Closure(closure)) => Some(closure),
                            _ => None,
                        }
                    }
                    _ => None,
                },
                _ => None,
            };
            if let (ProvisionalType::Param(param), Some(closure)) = (formal, &exact_closure) {
                substitutions.insert(
                    param.clone(),
                    SpecializationArgument::Closure(
                        closure.site.clone(),
                        closure.shape.clone(),
                        closure.captures.clone(),
                        closure.param_env.clone(),
                    ),
                );
            }
            let contextual = substitute(formal, &substitutions);
            let actual = self.expression(
                value,
                contextual.as_ref().filter(|contextual| ground(contextual)),
            )?;
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
                Some(SpecializationArgument::Closure(_, shape, _, _)) => {
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
                .filter_map(|param| match substitutions.get(param)? {
                    SpecializationArgument::Type(ty) => Some(ClosureTupleField::Type(ty.clone())),
                    SpecializationArgument::Closure(site, shape, captures, environment) => {
                        Some(ClosureTupleField::Closure(ClosureRequest {
                            site: site.clone(),
                            shape: shape.clone(),
                            captures: captures.clone(),
                            param_env: environment.clone(),
                        }))
                    }
                    SpecializationArgument::EffectRow(_) => None,
                })
                .collect::<Vec<_>>();
            let has_closure = exact_arguments
                .iter()
                .any(|argument| matches!(argument, ClosureTupleField::Closure(_)));
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
        let template = self.nominal_templates.get(head)?.clone();
        let fields = template.variants.get(variant)?;
        if fields.len() != args.len() {
            args.iter().for_each(|argument| {
                self.expression(argument, None);
            });
            return None;
        }
        if template.params.is_empty() {
            for (argument, field) in args.iter().zip(fields) {
                self.expression(argument, Some(field));
            }
            return Some(ProvisionalType::Nominal(NominalInstanceKey::monomorphic(
                head.to_owned(),
            )));
        }
        let values = args.iter().zip(fields).collect::<Vec<_>>();
        self.infer_nominal_construction(source, head, &template.params, &values, expected)
    }

    fn direct_call(
        &mut self,
        source: &Expr,
        name: &str,
        args: &[Expr],
        expected: Option<&ProvisionalType>,
        requested_receiver_mode: Option<u32>,
    ) -> Option<ProvisionalType> {
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
                if actual != *formal
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
                    && expected != &shape.result
            }) && !matches!(
                shape.result,
                ProvisionalType::Predefined(ref result) if result == "Never"
            ) {
                self.error(format!(
                    "symbolic callable parameter `{name}` has an ambiguous result"
                ));
                return None;
            }
            return Some(shape.result);
        }
        if let Some(LocalBinding::RecursiveSelf(recursive_self, shape)) =
            self.locals.get(name).cloned()
        {
            let result = shape.result.clone();
            if args.len() != shape.params.len() {
                self.error(format!(
                    "recursive callable `{name}` has an unresolved argument count"
                ));
                return None;
            }
            for (argument, formal) in args.iter().zip(&shape.params) {
                let actual = self.expression(argument, Some(formal))?;
                if actual != *formal {
                    self.error(format!(
                        "recursive callable `{name}` has an ambiguous argument"
                    ));
                    return None;
                }
            }
            if expected.is_some_and(|expected| expected != &shape.result)
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
            return Some(result);
        }
        if let Some(LocalBinding::Closure(closure)) = self.locals.get(name).cloned() {
            let shape = &closure.shape;
            let result = shape.result.clone();
            if args.len() != shape.params.len() {
                self.error(format!(
                    "callable local `{name}` has an unresolved argument count"
                ));
                return None;
            }
            for (argument, formal) in args.iter().zip(&shape.params) {
                let actual = self.expression(argument, Some(formal))?;
                if actual != *formal {
                    self.error(format!("callable local `{name}` has an ambiguous argument"));
                    return None;
                }
            }
            if expected.is_some_and(|expected| expected != &shape.result)
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
            return Some(result);
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
        if template.transparent_identity
            && args.len() == 1
            && (transports_symbolic_resumption || transports_inline_callable)
        {
            let actual = self.expression(&args[0], expected)?;
            if expected.is_some_and(|expected| expected != &actual) {
                self.error(format!("call to `{name}` has an ambiguous result"));
                return None;
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
            && !unify_inference(
                &template.result,
                expected,
                &mutable_inference,
                &mut substitutions,
            )
            && !self.symbolic_validation
        {
            self.error(format!("call to `{name}` has an ambiguous result"));
            return None;
        }
        // Seed constraints from every independently synthesizable ordinary
        // argument before checking arguments left-to-right. Without this,
        // `select(Phantom::None, 42)` spuriously depends on argument order:
        // the empty constructor needs `T`, while the later literal fixes it.
        // The real expression walk below still performs all diagnostics and
        // records every discovery edge exactly once.
        for defaulting in [false, true] {
            for (argument, formal) in args.iter().zip(&template.params) {
                if matches!(formal, ProvisionalType::Callable(_))
                    || substitute(formal, &substitutions).is_some_and(|ty| ground(&ty))
                {
                    continue;
                }
                if let Some((actual, is_default)) = self.obvious_argument_type(argument)
                    && is_default == defaulting
                {
                    let mut trial = substitutions.clone();
                    if unify_inference(formal, &actual, &mutable_inference, &mut trial) {
                        substitutions = trial;
                    }
                }
            }
        }
        for (index, (argument, formal)) in args.iter().zip(&template.params).enumerate() {
            if let ProvisionalType::Callable(shape) = formal {
                let forwarded = match &argument.kind {
                    ExprKind::Variable(path) if path.len() == 1 => {
                        match self.locals.get(path[0].as_ref()).cloned() {
                            Some(LocalBinding::Closure(closure)) => Some(closure),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                let symbolic_forwarded = match &argument.kind {
                    ExprKind::Variable(path) if path.len() == 1 => self
                        .locals
                        .get(path[0].as_ref())
                        .and_then(|binding| match binding {
                            LocalBinding::Type(ProvisionalType::Callable(shape)) => {
                                Some(shape.clone())
                            }
                            _ => None,
                        }),
                    _ => None,
                };
                if let Some(actual_shape) = symbolic_forwarded {
                    if !self.symbolic_validation {
                        self.error(format!(
                            "call to `{name}` forwards a symbolic callable without a concrete identity"
                        ));
                        return None;
                    }
                    if !bind(
                        &ProvisionalType::Callable(shape.clone()),
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
                            .symbolic_callable_parameter(match &argument.kind {
                                ExprKind::Variable(path) if path.len() == 1 => path[0].as_ref(),
                                _ => unreachable!(
                                    "symbolic forwarding was recognized from a variable"
                                ),
                            })
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
                    let formal = ProvisionalType::Callable(shape.clone());
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
                        PlannedClosure::Exact(closure) => closure,
                        // The call itself must remain on the late path because
                        // an emitted specialization key cannot name the
                        // handler-site callable identity yet.
                        PlannedClosure::Late(_) => return None,
                    }
                };
                if let Some(binder) = &template.parameter_binders[index] {
                    match substitutions.get(binder) {
                        Some(existing)
                            if existing
                                != &SpecializationArgument::Closure(
                                    closure.site.clone(),
                                    closure.shape.clone(),
                                    closure.captures.clone(),
                                    closure.param_env.clone(),
                                ) =>
                        {
                            self.error("callable binder has ambiguous closure arguments");
                            return None;
                        }
                        Some(_) => {}
                        None => {
                            substitutions.insert(
                                binder.clone(),
                                SpecializationArgument::Closure(
                                    closure.site.clone(),
                                    closure.shape.clone(),
                                    closure.captures.clone(),
                                    closure.param_env.clone(),
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
                let contextual_formal = substitute(formal, &substitutions);
                let actual = self.expression(
                    argument,
                    contextual_formal.as_ref().filter(|formal| ground(formal)),
                )?;
                if !unify_inference(formal, &actual, &mutable_inference, &mut substitutions)
                    && !self.symbolic_validation
                {
                    self.error(format!("call to `{name}` has ambiguous generic arguments"));
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
        let result = substitute(&template.result, &substitutions);
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
            SpecializationArgument::Closure(_, shape, captures, _) => {
                !shape.params.iter().all(ground)
                    || !ground(&shape.result)
                    || captures.iter().any(|capture| !ground(&capture.ty))
            }
            SpecializationArgument::EffectRow(effects) => effects
                .iter()
                .any(|effect| !effect.arguments.iter().all(ground)),
        }) {
            self.error(format!("call to `{name}` is not fully ground"));
            return None;
        }
        let key = SpecializationKey {
            template: template.declaration,
            arguments,
        };
        if self.recording {
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
            if let Some(binder) = &template.result_binder
                && let Some(SpecializationArgument::Closure(site, shape, captures, environment)) =
                    substitutions.get(binder)
            {
                self.discovery.graph.returned_closures.insert(
                    call_site.clone(),
                    ClosureRequest {
                        site: site.clone(),
                        shape: shape.clone(),
                        captures: captures.clone(),
                        param_env: environment.clone(),
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
                        SpecializationArgument::Closure(site, shape, captures, environment) => {
                            Some(ClosureTupleField::Closure(ClosureRequest {
                                site: site.clone(),
                                shape: shape.clone(),
                                captures: captures.clone(),
                                param_env: environment.clone(),
                            }))
                        }
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

    fn expression(
        &mut self,
        source: &Expr,
        expected: Option<&ProvisionalType>,
    ) -> Option<ProvisionalType> {
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
                    if closure
                        .captures
                        .iter()
                        .any(|capture| contains_unique_reference_shape(&capture.ty))
                    {
                        self.error(
                            "callable closure containing a captured unique reference escapes its direct call context",
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
                        Some(LocalBinding::Closure(_)) | None => None,
                    }
                }
            }
            ExprKind::Variable(path) if path.len() == 2 => {
                self.enum_construction(source, path[0].as_ref(), path[1].as_ref(), &[], expected)
            }
            ExprKind::Call(callee, args) => {
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
                    let saved_locals = self.locals.clone();
                    let saved_bindings = self.bindings.clone();
                    self.bind_handler_pattern(pattern.as_ref(), &subject_ty);
                    let positive_ty = self.expression(positive, expected);
                    self.locals = saved_locals;
                    self.bindings = saved_bindings;
                    let negative_ty = self.expression(negative, expected.or(positive_ty.as_ref()));
                    match (positive_ty, negative_ty) {
                        (Some(positive), Some(negative)) if positive == negative => Some(positive),
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
                } else if let ExprKind::Variable(path) = &callee.kind
                    && path.len() == 1
                    && matches!(path[0].as_ref(), "resume" | "tail")
                    && args.len() == 2
                {
                    let terminal = path[0].as_ref() == "tail";
                    let shape = match &args[0].kind {
                        ExprKind::Variable(path) if path.len() == 1 => {
                            match self.locals.get(path[0].as_ref()) {
                                Some(LocalBinding::Type(ProvisionalType::Callable(shape))) => {
                                    Some(shape.as_ref().clone())
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    };
                    self.expression(&args[0], None);
                    self.expression(
                        &args[1],
                        shape.as_ref().and_then(|shape| shape.params.first()),
                    );
                    if terminal {
                        Some(ProvisionalType::Predefined("Never".into()))
                    } else {
                        shape
                            .map(|shape| shape.result)
                            .or_else(|| expected.cloned())
                    }
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
            ExprKind::Block(statements) => {
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
                                    fields
                                        .iter()
                                        .any(|field| matches!(field, ClosureTupleField::Closure(_)))
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
                            result = self.expression(value, None);
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
                                                    _ => LocalBinding::Type(field_ty.clone()),
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
                                            .and_then(|field| match field {
                                                ClosureTupleField::Closure(closure) => {
                                                    Some(closure.clone())
                                                }
                                                ClosureTupleField::Type(_) => None,
                                            });
                                        self.locals.insert(
                                            binding.clone(),
                                            match closure {
                                                Some(closure) => LocalBinding::Closure(closure),
                                                None => LocalBinding::Type(field_ty.clone()),
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
                            self.expression(value, None);
                            if let AssignmentPlaceKind::Dereference { reference, .. } =
                                &destination.kind
                            {
                                self.expression(reference, None);
                            }
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
                    self.expression(operand, None).map(ProvisionalType::shared)
                }
                UnaryOp::BorrowUnique => {
                    self.expression(operand, None).map(ProvisionalType::unique)
                }
                UnaryOp::Dereference => match self.expression(operand, None)? {
                    ProvisionalType::Shared(referent) | ProvisionalType::Unique(referent) => {
                        Some(*referent)
                    }
                    _ => expected.cloned(),
                },
                UnaryOp::Negate => self.expression(operand, expected),
            },
            ExprKind::Binary { lhs, rhs, .. } => {
                let ty = expected
                    .cloned()
                    .unwrap_or_else(|| ProvisionalType::Predefined("i64".into()));
                self.expression(lhs, Some(&ty));
                self.expression(rhs, Some(&ty));
                Some(ty)
            }
            ExprKind::Struct { name, fields } => {
                if let Some(template) = self.nominal_templates.get(name.as_ref()).cloned() {
                    if template.params.is_empty() {
                        for (field, value) in fields.iter() {
                            self.expression(value, template.fields.get(field));
                        }
                        return Some(ProvisionalType::Nominal(NominalInstanceKey::monomorphic(
                            name.to_string(),
                        )));
                    }
                    let values = template
                        .fields
                        .iter()
                        .filter_map(|(field, formal)| {
                            fields
                                .iter()
                                .find(|(supplied, _)| supplied == field)
                                .map(|(_, value)| (value, formal))
                        })
                        .collect::<Vec<_>>();
                    return self.infer_nominal_construction(
                        source,
                        name,
                        &template.params,
                        &values,
                        expected,
                    );
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
                let subject = self.expression(subject, None)?;
                let subject = match subject {
                    ProvisionalType::Shared(referent) | ProvisionalType::Unique(referent) => {
                        *referent
                    }
                    subject => subject,
                };
                let ProvisionalType::Nominal(instance) = subject else {
                    return expected.cloned();
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
                let shape = self.operation_at(source.span, effect, operation);
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
                let computation_result = self.expression(computation, expected);
                let handler_result = expected.or(computation_result.as_ref());
                for clause in clauses.iter() {
                    let saved = self.locals.clone();
                    let saved_bindings = self.bindings.clone();
                    let operation =
                        self.operation_at(clause.span, &clause.effect, &clause.operation);
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
                    if let Some(resumption) = &clause.resumption {
                        if let (Some(operation), Some(handler_result)) =
                            (operation.as_ref(), handler_result)
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
                    self.expression(&clause.body, handler_result);
                    self.locals = saved;
                    self.bindings = saved_bindings;
                }
                handler_result.cloned()
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
            ExprKind::Labeled { body, .. } | ExprKind::LabelDestination { body, .. } => {
                self.expression(body, expected)
            }
            ExprKind::Leave { value, .. } => {
                if let Some(value) = value {
                    self.expression(value, None);
                }
                None
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
            ExprKind::LabelReference(_) => None,
            ExprKind::Variable(_) => None,
            // The parser's grammar-complete forms are rejected by `validate`
            // or rewritten by `parser::normalize_for_legacy_consumers` before
            // specialization; reaching one is a broken phase invariant.
            ExprKind::Resume { .. }
            | ExprKind::Cancel { .. }
            | ExprKind::TailResume { .. }
            | ExprKind::ContextBlock(_) => unvalidated_syntax(),
        }
    }
}

pub(crate) fn expression_ordinals(root: &Expr) -> BTreeMap<usize, u32> {
    fn visit(expression: &Expr, next: &mut u32, ordinals: &mut BTreeMap<usize, u32>) {
        ordinals.insert(std::ptr::from_ref(expression) as usize, *next);
        *next += 1;
        match &expression.kind {
            ExprKind::Block(statements) => {
                for statement in statements.iter() {
                    match statement {
                        Stmt::Let { value, .. }
                        | Stmt::Deconstruct { value, .. }
                        | Stmt::Expr(value) => {
                            visit(value, next, ordinals);
                        }
                        Stmt::Assign {
                            destination, value, ..
                        } => {
                            visit(value, next, ordinals);
                            if let AssignmentPlaceKind::Dereference { reference, .. } =
                                &destination.kind
                            {
                                visit(reference, next, ordinals);
                            }
                        }
                    }
                }
            }
            ExprKind::List(values) | ExprKind::Tuple(values) => {
                for value in values.iter() {
                    visit(value, next, ordinals);
                }
            }
            ExprKind::Struct { fields, .. } => {
                for (_, value) in fields.iter() {
                    visit(value, next, ordinals);
                }
            }
            ExprKind::Field(subject, _)
            | ExprKind::Move(subject)
            | ExprKind::Unary {
                operand: subject, ..
            } => {
                visit(subject, next, ordinals);
            }
            ExprKind::Call(callee, arguments) => {
                visit(callee, next, ordinals);
                for argument in arguments.iter() {
                    visit(argument, next, ordinals);
                }
            }
            ExprKind::Perform { args, .. } => {
                for argument in args.iter() {
                    visit(argument, next, ordinals);
                }
            }
            ExprKind::Handle {
                computation,
                clauses,
            } => {
                visit(computation, next, ordinals);
                for clause in clauses.iter() {
                    visit(&clause.body, next, ordinals);
                }
            }
            ExprKind::Closure { body, .. } | ExprKind::TypedClosure { body, .. } => {
                visit(body, next, ordinals)
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                visit(lhs, next, ordinals);
                visit(rhs, next, ordinals);
            }
            ExprKind::Labeled { body, .. } | ExprKind::LabelDestination { body, .. } => {
                visit(body, next, ordinals)
            }
            ExprKind::Leave { value, .. } => {
                if let Some(value) = value {
                    visit(value, next, ordinals);
                }
            }
            ExprKind::Is { subject, .. } => visit(subject, next, ordinals),
            ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Char(_)
            | ExprKind::Byte(_)
            | ExprKind::ByteString(_)
            | ExprKind::String(_)
            | ExprKind::Variable(_) => {}
            // The parser's grammar-complete forms are rejected by `validate` or
            // rewritten by `parser::normalize_for_legacy_consumers` before any
            // compiler pass runs; reaching one here is a broken phase invariant.
            ExprKind::LabelReference(_) => {}
            ExprKind::Resume { .. }
            | ExprKind::Cancel { .. }
            | ExprKind::TailResume { .. }
            | ExprKind::ContextBlock(_) => unvalidated_syntax(),
        }
    }

    let mut ordinals = BTreeMap::new();
    visit(root, &mut 0, &mut ordinals);
    ordinals
}

fn expression_at_ordinal(root: &Expr, target: u32) -> Option<&Expr> {
    fn find<'a>(expression: &'a Expr, target: u32, next: &mut u32) -> Option<&'a Expr> {
        let ordinal = *next;
        *next += 1;
        if ordinal == target {
            return Some(expression);
        }
        let mut children = Vec::new();
        match &expression.kind {
            ExprKind::Block(statements) => {
                for statement in statements.iter() {
                    match statement {
                        Stmt::Let { value, .. }
                        | Stmt::Deconstruct { value, .. }
                        | Stmt::Expr(value) => children.push(value),
                        Stmt::Assign {
                            destination, value, ..
                        } => {
                            children.push(value);
                            if let AssignmentPlaceKind::Dereference { reference, .. } =
                                &destination.kind
                            {
                                children.push(reference);
                            }
                        }
                    }
                }
            }
            ExprKind::List(values) | ExprKind::Tuple(values) => children.extend(values.iter()),
            ExprKind::Struct { fields, .. } => {
                children.extend(fields.iter().map(|(_, value)| value));
            }
            ExprKind::Field(subject, _)
            | ExprKind::Move(subject)
            | ExprKind::Unary {
                operand: subject, ..
            } => {
                children.push(subject);
            }
            ExprKind::Call(callee, arguments) => {
                children.push(callee);
                children.extend(arguments.iter());
            }
            ExprKind::Perform { args, .. } => children.extend(args.iter()),
            ExprKind::Handle {
                computation,
                clauses,
            } => {
                children.push(computation);
                children.extend(clauses.iter().map(|clause| &clause.body));
            }
            ExprKind::Closure { body, .. } | ExprKind::TypedClosure { body, .. } => {
                children.push(body)
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                children.push(lhs);
                children.push(rhs);
            }
            ExprKind::Labeled { body, .. } | ExprKind::LabelDestination { body, .. } => {
                children.push(body)
            }
            ExprKind::Leave { value, .. } => children.extend(value.iter().map(AsRef::as_ref)),
            ExprKind::Is { subject, .. } => children.push(subject),
            ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Char(_)
            | ExprKind::Byte(_)
            | ExprKind::ByteString(_)
            | ExprKind::String(_)
            | ExprKind::Variable(_) => {}
            // The parser's grammar-complete forms are rejected by `validate` or
            // rewritten by `parser::normalize_for_legacy_consumers` before any
            // compiler pass runs; reaching one here is a broken phase invariant.
            ExprKind::LabelReference(_) => {}
            ExprKind::Resume { .. }
            | ExprKind::Cancel { .. }
            | ExprKind::TailResume { .. }
            | ExprKind::ContextBlock(_) => unvalidated_syntax(),
        }
        children
            .into_iter()
            .find_map(|child| find(child, target, next))
    }
    find(root, target, &mut 0)
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
        (ExprKind::Block(_), ClosureBodyKind::ContextualBlock) => Some((vec![], expression)),
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
            ExprKind::Block(statements) => {
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
            // Constructing a closure is pure. Its body belongs to a separate
            // callable summary and must not be charged until that value is
            // actually invoked.
            ExprKind::Closure { .. } | ExprKind::TypedClosure { .. } => ValueFlow::default(),
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
            ExprKind::Labeled { body, .. } | ExprKind::LabelDestination { body, .. } => visit(
                body,
                effect,
                handled,
                locals,
                functions,
                summaries,
                handler_closes,
            ),
            ExprKind::Leave { value, .. } => {
                value.as_deref().map_or_else(ValueFlow::default, |value| {
                    visit(
                        value,
                        effect,
                        handled,
                        locals,
                        functions,
                        summaries,
                        handler_closes,
                    )
                })
            }
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
            ExprKind::Resume { .. }
            | ExprKind::Cancel { .. }
            | ExprKind::TailResume { .. }
            | ExprKind::ContextBlock(_) => unvalidated_syntax(),
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

pub(crate) fn discover_with_traits_and_budgets(
    program: &Program,
    trait_db: &TraitDb,
    solver_budgets: &mut BTreeMap<DeclarationKey, SolverBudget>,
) -> Discovery {
    let (templates_by_name, errors) = discover_templates(program, trait_db);
    let nominal_templates = discover_nominal_templates(program);
    let operation_templates = discover_operation_templates(program);
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
            expression_ordinals: &expression_ordinals,
            body_instance: BodyInstanceKey::Root(DeclarationKey::Global(global.name.clone())),
            recording: true,
            trait_db,
            solver_budget,
            param_env: ParamEnv::default(),
            symbolic_validation: false,
            active_recursive_self: None,
        };
        walker.expression(&global.value, None);
    }
    for function in &program.functions {
        let Some(template) = templates_by_name.get(&function.name) else {
            continue;
        };
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
        let expression_ordinals = expression_ordinals(&function.body);
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
            expression_ordinals: &expression_ordinals,
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
        };
        walker.expression(&function.body, Some(&template.result));
        drop(walker);
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
            expression_ordinals: &expression_ordinals,
            body_instance: BodyInstanceKey::Drop(declaration.target.clone()),
            recording: true,
            trait_db,
            solver_budget,
            param_env: ParamEnv::default(),
            symbolic_validation: false,
            active_recursive_self: None,
        };
        walker.expression(
            &declaration.body,
            Some(&ProvisionalType::Predefined("Unit".into())),
        );
    }
    let mut processed = BTreeSet::new();
    let mut processed_closures = BTreeSet::new();
    loop {
        while let Some(key) = discovery
            .graph
            .requests
            .keys()
            .find(|key| !processed.contains(*key))
            .cloned()
        {
            if discovery.graph.requests.len() > 1024 {
                discovery.errors.insert(DiscoveryError {
                    owner: key.template.clone(),
                    message: "specialization request growth exceeded the closed discovery limit"
                        .into(),
                });
                break;
            }
            processed.insert(key.clone());
            let Some(template) = discovery.graph.templates.get(&key.template).cloned() else {
                continue;
            };
            let Some(function) = program.functions.iter().find(|function| {
                DeclarationKey::Function(function.name.clone()) == template.declaration
            }) else {
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
                        )) = substitutions.get(binder)
                    {
                        return Some((
                            param.name.clone(),
                            LocalBinding::Closure(ClosureRequest {
                                site: site.clone(),
                                shape: shape.clone(),
                                captures: captures.clone(),
                                param_env: environment.clone(),
                            }),
                        ));
                    }
                    substitute(ty, &substitutions)
                        .map(|ty| (param.name.clone(), LocalBinding::Type(ty)))
                })
                .collect();
            let expression_ordinals = expression_ordinals(&function.body);
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
                expression_ordinals: &expression_ordinals,
                body_instance: BodyInstanceKey::Specialization(key.clone()),
                recording: true,
                trait_db,
                solver_budget,
                param_env,
                symbolic_validation: false,
                active_recursive_self: None,
            };
            let result = substitute(&template.result, &substitutions);
            walker.expression(&function.body, result.as_ref());
        }
        while let Some((closure, body_kind)) = discovery
            .graph
            .closure_bodies
            .iter()
            .find(|(closure, _)| !processed_closures.contains(*closure))
            .map(|(closure, kind)| (closure.clone(), *kind))
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
            let recursive_self = discovery.graph.recursive_closures.get(&closure).cloned();
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
                parent: None,
                locals,
                bindings,
                expression_ordinals: &expression_ordinals,
                body_instance: BodyInstanceKey::Closure(closure.clone()),
                recording: true,
                trait_db,
                solver_budget,
                param_env,
                symbolic_validation: false,
                active_recursive_self: recursive_self,
            };
            walker.expression(body, Some(&closure.shape.result));
        }
        if processed.len() == discovery.graph.requests.len()
            && processed_closures.len() == discovery.graph.closure_bodies.len()
        {
            break;
        }
        if discovery.graph.requests.len() > 1024 {
            break;
        }
    }
    discovery
}

/// The parser's grammar-complete forms (labels, `is`, typed anonymous
/// callables, float/char/byte literals, structural resumptions, contextual
/// blocks) are rejected by `validate` or rewritten by
/// `parser::normalize_for_legacy_consumers` before compilation begins, so no
/// compiler pass can receive them.
fn unvalidated_syntax<T>() -> T {
    unreachable!("grammar-complete syntax is rejected or rewritten before lowering")
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn marker_constraint_records_ground_request() {
        let source = "trait Marker {} struct Box<T> { value: T } impl Marker for i64 {} impl<T> Marker for Box<T> where T: Marker {} id<T>(value: T) -> T where T: Marker { value } boxed() -> Box<i64> { Box { value: 42 } } main() -> { id(42); id(boxed()); () }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let discovery = discover_with_traits(&program, &db);
        assert!(discovery.errors.is_empty(), "{:?}", discovery.errors);
        assert_eq!(discovery.graph.requests.len(), 2);
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
            Some(SpecializationArgument::Closure(_, _, captures, _)) if captures.is_empty()
        )));
    }

    #[test]
    fn callable_zero_use_evidence_rejects_a_must_move_capture() {
        let discovery = parse_discovery(
            "struct Ticket { serial: i64 }
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
                    SpecializationArgument::Closure(_, shape, _, _)
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
        let row = direct_closure_effects(body, &resolve);
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
                SpecializationArgument::Closure(site, shape, captures, _environment) => {
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
        assert!(!escapes("closure_only", "Ask"));
        assert!(
            escapes("partial_handler", "Partial"),
            "a handler that omits an operation must not close the protocol"
        );
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
