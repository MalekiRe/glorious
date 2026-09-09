//! Source-independent, body-derived control contracts.
//!
//! Alternatives describe *ordered executions*, not a set of possibly mentioned
//! callbacks. Normal edges past a symbolic invocation require its matching
//! `InvocationReturned` guard. The other edge remains `UnresolvedInvocation`:
//! an ordinary `Fn(..) -> !` never acquires label authority from its result type.
//! Consumers must resolve these edges before claiming an invocation cannot exit.
//! Missing bodies, recursive expansion, resource limits and unsupported Core
//! remain explicit unknowns. This product grants no ownership or lowering proof
//! by itself, and is intentionally not serializable yet.

use crate::{
    CallableBrand, CallableSignature, CoreId, CoreKind, CorePattern, DefKey, Digest,
    EffectInstance, ElaboratedInterface, GenericArgument, LabelBrand, Type, TypedBody,
};
use std::{collections::BTreeMap, sync::Arc};

#[derive(Clone, Copy)]
pub struct ControlBody<'a> {
    pub body: &'a TypedBody,
    pub signature: &'a CallableSignature,
    pub interface: &'a ElaboratedInterface,
}

#[derive(Clone, Copy, Debug)]
pub struct ControlSummaryLimits {
    pub max_call_depth: usize,
    pub max_steps: usize,
    pub max_alternatives: usize,
}
impl Default for ControlSummaryLimits {
    fn default() -> Self {
        Self {
            max_call_depth: 32,
            max_steps: 100_000,
            max_alternatives: 1024,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ControlLocation {
    pub callable: CallableBrand,
    pub expression: CoreId,
    /// Distinguishes repeated evaluations of one arena node, including a
    /// shared Core subgraph. Aliasing an evaluated value does not mint one.
    pub occurrence: u64,
}
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ControlSite {
    pub location: ControlLocation,
    /// Outer to inner call sites. Separate evaluations of the same helper
    /// therefore never share produced-result or lexical-label identities.
    pub calls: Vec<ControlLocation>,
}
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ControlOrigin {
    Parameter(u32),
    Capture(u32),
    Produced(ControlSite),
    Field {
        base: Box<ControlOrigin>,
        index: u32,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ControlLabelTarget {
    Symbolic(ControlOrigin),
    Lexical {
        brand: LabelBrand,
        /// Minted by entering the label, not by reading its capability.
        /// Re-entering one arena node in the same callable is generative too.
        activation: ControlSite,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ControlValue {
    pub origin: ControlOrigin,
    pub ty: Type,
    pub shape: ControlValueShape,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ControlValueShape {
    Unknown,
    Literal(String),
    Tuple(Vec<ControlValue>),
    Array(Vec<ControlValue>),
    Record {
        definition: DefKey,
        fields: Vec<ControlValue>,
    },
    Enum {
        definition: DefKey,
        variant: u32,
        fields: Vec<ControlValue>,
    },
    Callable {
        brand: CallableBrand,
        /// Substitution in the defining body's generic namespace. `None`
        /// retains that namespace when summarizing an embedded closure alone.
        generic_arguments: Option<Vec<GenericArgument>>,
        captures: Vec<ControlValue>,
    },
    /// Taking a reference to an unavailable implementation is still a pure
    /// value operation. Its unknown control behavior matters only if invoked.
    OpaqueCallable,
    Label(ControlLabelTarget),
    Borrow(Box<ControlValue>),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ControlGuard {
    /// Binders are erased to `Any`; nominal definition and variant indices
    /// come exclusively from validated structural Core, never source names.
    Pattern {
        subject: ControlOrigin,
        pattern: CorePattern,
        matches: bool,
    },
    InvocationReturned(ControlSite),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ControlEvent {
    Invoke {
        site: ControlSite,
        callee: ControlValue,
        arguments: Vec<ControlValue>,
    },
    Transfer {
        site: ControlSite,
        target: ControlLabelTarget,
        value: ControlValue,
    },
    Perform {
        site: ControlSite,
        effect: EffectInstance,
        operation: u32,
        arguments: Vec<ControlValue>,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ControlUnknown {
    InvalidCore(DefKey),
    InvalidContract(DefKey),
    MissingBody(CallableBrand),
    RecursiveCall(CallableBrand),
    OpaqueCall,
    Unsupported(&'static str),
    Limit,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ControlOutcome {
    Return(ControlValue),
    LabelExit {
        target: ControlLabelTarget,
        value: ControlValue,
    },
    TerminalOperation {
        effect: EffectInstance,
        operation: u32,
    },
    /// The non-normal edge of a formal callback invocation. Its normal edge
    /// (if the result permits one) carries `InvocationReturned` at this site.
    UnresolvedInvocation(ControlSite),
    Cancellation,
    Divergence,
    Unknown(ControlUnknown),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ControlAlternative {
    pub guards: Vec<ControlGuard>,
    pub events: Vec<ControlEvent>,
    pub outcome: ControlOutcome,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ControlBodyIdentity {
    pub definition: DefKey,
    pub body: Digest,
    pub contract: Digest,
}
#[derive(Clone)]
struct Seal {
    identity: ControlBodyIdentity,
    // The semantic fingerprint deliberately ignores arena allocation. Sites
    // do not: retain its exact shape as well, so a summary cannot be attached
    // to a reallocated arena and accidentally retarget a guard.
    body: Arc<TypedBody>,
    interface: Arc<ElaboratedInterface>,
    valid: Result<(), ControlUnknown>,
}
impl std::fmt::Debug for Seal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Seal")
            .field("identity", &self.identity)
            .field("valid", &self.valid)
            .finish_non_exhaustive()
    }
}
#[derive(Clone, Debug)]
pub struct CallableControlSummary {
    callable: CallableBrand,
    identity: ControlBodyIdentity,
    dependencies: BTreeMap<DefKey, Arc<Seal>>,
    alternatives: Vec<ControlAlternative>,
}
impl CallableControlSummary {
    pub fn callable(&self) -> CallableBrand {
        self.callable
    }
    pub fn identity(&self) -> ControlBodyIdentity {
        self.identity
    }
    pub fn alternatives(&self) -> &[ControlAlternative] {
        &self.alternatives
    }
    pub fn dependencies(&self) -> impl Iterator<Item = ControlBodyIdentity> + '_ {
        self.dependencies.values().map(|seal| seal.identity)
    }
    /// All depended-on bodies, contracts and arena identities must still be
    /// present. Private seals prevent callers from fabricating this evidence.
    pub fn matches(&self, bodies: &BTreeMap<DefKey, ControlBody<'_>>) -> bool {
        self.dependencies.iter().all(|(key, seal)| {
            bodies.get(key).is_some_and(|input| {
                seal.valid.is_ok()
                    && same_body(input.body, &seal.body)
                    && input.body.semantic_fingerprint() == seal.identity.body
                    && crate::signature::host_contract_fingerprint(*key, input.signature)
                        == seal.identity.contract
                    && input.body.diagnostics.is_empty()
                    && !input.body.recovered
                    && same_interface(input.interface, &seal.interface)
            })
        })
    }
    pub fn is_complete(&self) -> bool {
        !self.alternatives.iter().any(|path| {
            matches!(
                path.outcome,
                ControlOutcome::Unknown(_) | ControlOutcome::UnresolvedInvocation(_)
            )
        })
    }
    pub fn only_returns_normally(&self) -> bool {
        !self.alternatives.is_empty()
            && self.is_complete()
            && self
                .alternatives
                .iter()
                .all(|path| matches!(path.outcome, ControlOutcome::Return(_)))
    }
}
#[derive(Clone, Debug, Default)]
pub struct ControlSummarySet {
    summaries: BTreeMap<CallableBrand, CallableControlSummary>,
}
impl ControlSummarySet {
    pub fn get(&self, callable: CallableBrand) -> Option<&CallableControlSummary> {
        self.summaries.get(&callable)
    }
    pub fn iter(&self) -> impl Iterator<Item = (CallableBrand, &CallableControlSummary)> {
        self.summaries
            .iter()
            .map(|(brand, summary)| (*brand, summary))
    }
}

#[derive(Clone)]
struct Frame {
    callable: CallableBrand,
    owner: DefKey,
    calls: Vec<ControlLocation>,
    generic_arguments: Option<Vec<GenericArgument>>,
    occurrence: u64,
    labels: BTreeMap<LabelBrand, ControlLabelTarget>,
}
impl Frame {
    fn site(&self, expression: CoreId) -> ControlSite {
        ControlSite {
            location: ControlLocation {
                callable: self.callable,
                expression,
                occurrence: self.occurrence,
            },
            calls: self.calls.clone(),
        }
    }
    fn argument(&self, argument: GenericArgument) -> GenericArgument {
        self.generic_arguments.as_ref().map_or_else(
            || argument.clone(),
            |arguments| {
                crate::signature::substitute_trait_generic_argument(argument.clone(), arguments)
            },
        )
    }
    fn ty(&self, ty: Type) -> Type {
        match self.argument(GenericArgument::Type(ty)) {
            GenericArgument::Type(ty) => ty,
            _ => unreachable!(),
        }
    }
    fn pattern(&self, mut pattern: CorePattern) -> CorePattern {
        match &mut pattern {
            CorePattern::Tuple(fields) => {
                for field in fields {
                    *field = self.pattern(field.clone());
                }
            }
            CorePattern::Array {
                element, elements, ..
            } => {
                *element = self.ty(element.clone());
                for field in elements {
                    *field = self.pattern(field.clone());
                }
            }
            CorePattern::Record {
                field_types,
                fields,
                ..
            }
            | CorePattern::Enum {
                field_types,
                fields,
                ..
            } => {
                for ty in field_types {
                    *ty = self.ty(ty.clone());
                }
                for field in fields {
                    field.ty = self.ty(field.ty.clone());
                    field.pattern = self.pattern(field.pattern.clone());
                }
            }
            _ => {}
        }
        pattern
    }
}
#[derive(Clone)]
struct State {
    locals: BTreeMap<String, ControlValue>,
    guards: Vec<ControlGuard>,
    events: Vec<ControlEvent>,
    outcome: ControlOutcome,
}
impl State {
    fn running(&self) -> bool {
        matches!(self.outcome, ControlOutcome::Return(_))
    }
    fn value(&self) -> ControlValue {
        match &self.outcome {
            ControlOutcome::Return(value) => value.clone(),
            _ => unreachable!(),
        }
    }
    fn stop(mut self, reason: ControlUnknown) -> Self {
        self.outcome = ControlOutcome::Unknown(reason);
        self
    }
    fn limit_witness(mut self) -> Self {
        // A truncated suffix may contain several unrelated guarded paths.
        // Retaining one path's conditions would let specialization discard
        // this witness while other omitted paths remained executable.
        self.locals.clear();
        self.guards.clear();
        self.events.clear();
        self.outcome = ControlOutcome::Unknown(ControlUnknown::Limit);
        self
    }
    fn guard(&mut self, guard: ControlGuard) -> bool {
        if let ControlGuard::Pattern {
            subject,
            pattern,
            matches,
        } = &guard
        {
            if self.guards.iter().any(|old| {
                matches!(old, ControlGuard::Pattern {
                subject: old_subject, pattern: old_pattern, matches: old_matches
            } if old_subject == subject && old_pattern == pattern && old_matches != matches)
            }) {
                return false;
            }
        }
        if !self.guards.contains(&guard) {
            self.guards.push(guard);
        }
        true
    }
}

pub fn derive_control_summaries(
    bodies: &BTreeMap<DefKey, ControlBody<'_>>,
    limits: ControlSummaryLimits,
) -> ControlSummarySet {
    let mut interfaces = BTreeMap::new();
    let seals: BTreeMap<_, _> = bodies.iter().map(|(key, input)| {
        let (interface, solver) = interfaces.entry(input.interface as *const ElaboratedInterface as usize)
            .or_insert_with(|| (Arc::new(input.interface.clone()), crate::TraitSolver::new(input.interface)));
        let mut solver = solver.fresh_query();
        solver.assume_callable_contract(input.signature);
        solver.set_associated_bindings(input.signature.where_associated_type_bindings.clone(),
            input.signature.where_associated_effect_bindings.clone());
        let result_valid = input.body.expressions.get(input.body.root.0 as usize).is_some_and(|expr|
            solver.fresh_query().callable_abi_erasure_proven(&input.signature.result, &expr.ty));
        let valid = if input.body.recovered || !input.body.diagnostics.is_empty() || !input.body.validate().is_empty()
            || !input.interface.diagnostics.is_empty()
            || !input.body.validate_projection_obligations_in_environment(input.interface, &input.signature.where_bounds,
                &input.signature.where_outlives, solver).is_empty() {
            Err(ControlUnknown::InvalidCore(*key))
        } else if matches!(input.interface.definitions.get(key), Some(crate::ElaboratedHeader::Callable(declared)) if declared != input.signature)
            || input.body.parameters.iter().map(|(_, ty)| ty).ne(input.signature.parameters.iter())
            || input.body.safety != input.signature.safety
            || !result_valid {
            Err(ControlUnknown::InvalidContract(*key))
        } else { Ok(()) };
        let interface = interface.clone();
        (*key, Arc::new(Seal {
            identity: ControlBodyIdentity { definition: *key, body: input.body.semantic_fingerprint(),
                contract: crate::signature::host_contract_fingerprint(*key, input.signature) },
            body: Arc::new(input.body.clone()), interface, valid,
        }))
    }).collect();
    let mut output = ControlSummarySet::default();
    for (owner, input) in bodies {
        let mut roots = vec![(
            CallableBrand::Named(*owner),
            input.body.root,
            input.body.parameters.clone(),
            vec![],
        )];
        for expr in &input.body.expressions {
            if let CoreKind::Closure {
                environment,
                parameters,
                body,
                ..
            } = &expr.kind
            {
                roots.push((
                    CallableBrand::Closure(environment.brand),
                    *body,
                    parameters.clone(),
                    environment
                        .captures
                        .iter()
                        .map(|capture| (capture.name.clone(), capture.ty.clone()))
                        .collect(),
                ));
            }
        }
        for (callable, root, parameters, captures) in roots {
            let frame = Frame {
                callable,
                owner: *owner,
                calls: vec![],
                generic_arguments: None,
                occurrence: 0,
                labels: BTreeMap::new(),
            };
            let mut locals = BTreeMap::new();
            for (index, (name, ty)) in captures.iter().enumerate() {
                locals.insert(
                    name.clone(),
                    input_value(
                        ControlOrigin::Capture(index as u32),
                        ty.clone(),
                        input.signature,
                    ),
                );
            }
            for (index, (name, ty)) in parameters.iter().enumerate() {
                locals.insert(
                    name.clone(),
                    input_value(
                        ControlOrigin::Parameter(index as u32),
                        ty.clone(),
                        input.signature,
                    ),
                );
            }
            let initial = State {
                locals,
                guards: vec![],
                events: vec![],
                outcome: ControlOutcome::Return(unknown(&frame, root, Type::Unit)),
            };
            let mut analyzer = Analyzer {
                bodies,
                seals: &seals,
                limits,
                steps: 0,
                evaluating: vec![],
                stack: vec![callable],
                dependencies: BTreeMap::from([(*owner, seals[owner].clone())]),
            };
            let states = match &seals[owner].valid {
                Ok(()) => analyzer.eval(&frame, root, initial),
                Err(reason) => vec![initial.stop(reason.clone())],
            };
            let alternatives = states
                .into_iter()
                .map(|state| ControlAlternative {
                    guards: state.guards,
                    events: state.events,
                    outcome: state.outcome,
                })
                .collect();
            output.summaries.insert(
                callable,
                CallableControlSummary {
                    callable,
                    identity: seals[owner].identity,
                    dependencies: analyzer.dependencies,
                    alternatives,
                },
            );
        }
    }
    output
}

fn input_value(origin: ControlOrigin, ty: Type, signature: &CallableSignature) -> ControlValue {
    let label = signature.where_bounds.iter().any(|(subject, relation)| {
        *subject == ty
            && crate::signature::is_intrinsic_label_trait(relation)
            && matches!(
                relation.arguments.as_slice(),
                [crate::GenericArgument::Type(_)]
            )
    });
    ControlValue {
        shape: if label {
            ControlValueShape::Label(ControlLabelTarget::Symbolic(origin.clone()))
        } else {
            ControlValueShape::Unknown
        },
        origin,
        ty,
    }
}
fn same_interface(left: &ElaboratedInterface, right: &ElaboratedInterface) -> bool {
    left.definitions == right.definitions
        && left.generic_defaults == right.generic_defaults
        && left.pattern_values == right.pattern_values
        && left.inherent_self_types == right.inherent_self_types
        && left.host_imports == right.host_imports
        && left.diagnostics == right.diagnostics
}
fn same_body(left: &TypedBody, right: &TypedBody) -> bool {
    left.root == right.root
        && left.parameters == right.parameters
        && left.safety == right.safety
        && left.unsafe_scopes == right.unsafe_scopes
        && left.unsafe_implementations == right.unsafe_implementations
        && left.recovered == right.recovered
        && left.diagnostics == right.diagnostics
        && left
            .expressions
            .iter()
            .map(|expr| (&expr.kind, &expr.ty))
            .eq(right.expressions.iter().map(|expr| (&expr.kind, &expr.ty)))
}
fn unknown(frame: &Frame, id: CoreId, ty: Type) -> ControlValue {
    ControlValue {
        origin: ControlOrigin::Produced(frame.site(id)),
        ty,
        shape: ControlValueShape::Unknown,
    }
}

struct Analyzer<'a, 'b> {
    bodies: &'a BTreeMap<DefKey, ControlBody<'b>>,
    seals: &'a BTreeMap<DefKey, Arc<Seal>>,
    limits: ControlSummaryLimits,
    steps: usize,
    stack: Vec<CallableBrand>,
    evaluating: Vec<(CallableBrand, CoreId, Vec<ControlLocation>)>,
    dependencies: BTreeMap<DefKey, Arc<Seal>>,
}
impl Analyzer<'_, '_> {
    fn cap(&self, mut states: Vec<State>) -> Vec<State> {
        if states.len() > self.limits.max_alternatives.max(1) {
            let witness = states.pop().unwrap().limit_witness();
            states.truncate(self.limits.max_alternatives.saturating_sub(1));
            states.push(witness);
        }
        states
    }
    fn eval(&mut self, frame: &Frame, id: CoreId, state: State) -> Vec<State> {
        if !state.running() {
            return vec![state];
        }
        self.steps += 1;
        if self.steps > self.limits.max_steps {
            return vec![state.stop(ControlUnknown::Limit)];
        }
        let site = (frame.callable, id, frame.calls.clone());
        if self.evaluating.contains(&site) {
            return vec![state.stop(ControlUnknown::InvalidCore(frame.owner))];
        }
        if self.evaluating.len() >= 512 {
            return vec![state.stop(ControlUnknown::Limit)];
        }
        self.evaluating.push(site);
        let mut evaluation = frame.clone();
        evaluation.occurrence = self.steps as u64;
        let output = self.eval_inner(&evaluation, id, state);
        self.evaluating.pop();
        output
    }
    fn eval_inner(&mut self, frame: &Frame, id: CoreId, mut state: State) -> Vec<State> {
        let Some(mut expr) = self.bodies[&frame.owner]
            .body
            .expressions
            .get(id.0 as usize)
            .cloned()
        else {
            return vec![state.stop(ControlUnknown::InvalidCore(frame.owner))];
        };
        expr.ty = frame.ty(expr.ty);
        let mut result = unknown(frame, id, expr.ty.clone());
        match expr.kind {
            CoreKind::Literal(value) => result.shape = ControlValueShape::Literal(value),
            CoreKind::ConstValue(_) => {}
            CoreKind::Local(name) => {
                return match state.locals.get(&name).cloned() {
                    Some(value) => {
                        state.outcome = ControlOutcome::Return(value);
                        vec![state]
                    }
                    None => vec![state.stop(ControlUnknown::InvalidCore(frame.owner))],
                };
            }
            CoreKind::Function {
                definition,
                arguments,
                host_import: None,
            } => {
                result.shape = ControlValueShape::Callable {
                    brand: CallableBrand::Named(definition),
                    generic_arguments: Some(
                        arguments
                            .into_iter()
                            .map(|argument| frame.argument(argument))
                            .collect(),
                    ),
                    captures: vec![],
                }
            }
            CoreKind::TraitMethod {
                method,
                trait_arguments,
                method_arguments,
                deferred: None,
                ..
            } if trait_arguments.is_empty() && method_arguments.is_empty() => {
                result.shape = ControlValueShape::Callable {
                    brand: CallableBrand::Named(method),
                    generic_arguments: Some(vec![]),
                    captures: vec![],
                }
            }
            CoreKind::LabelValue { brand } => {
                let Some(target) = frame.labels.get(&brand) else {
                    return vec![state.stop(ControlUnknown::InvalidCore(frame.owner))];
                };
                result.shape = ControlValueShape::Label(target.clone());
            }
            CoreKind::Closure { environment, .. } => {
                let Some(captures) = environment
                    .captures
                    .iter()
                    .map(|capture| state.locals.get(&capture.name).cloned())
                    .collect::<Option<Vec<_>>>()
                else {
                    return vec![state.stop(ControlUnknown::InvalidCore(frame.owner))];
                };
                result.shape = ControlValueShape::Callable {
                    brand: CallableBrand::Closure(environment.brand),
                    generic_arguments: frame.generic_arguments.clone(),
                    captures,
                };
            }
            CoreKind::Tuple(ids) | CoreKind::Array(ids) => {
                let array = matches!(
                    self.bodies[&frame.owner].body.expressions[id.0 as usize].kind,
                    CoreKind::Array(_)
                );
                return self
                    .values(frame, &ids, state)
                    .into_iter()
                    .map(|(mut state, values)| {
                        if state.running() {
                            let mut result = result.clone();
                            result.shape = if array {
                                ControlValueShape::Array(values)
                            } else {
                                ControlValueShape::Tuple(values)
                            };
                            state.outcome = ControlOutcome::Return(result);
                        }
                        state
                    })
                    .collect();
            }
            CoreKind::Record { definition, fields }
            | CoreKind::Enum {
                definition, fields, ..
            } => {
                let variant = match self.bodies[&frame.owner].body.expressions[id.0 as usize].kind {
                    CoreKind::Enum { variant, .. } => Some(variant),
                    _ => None,
                };
                return self
                    .values(frame, &fields, state)
                    .into_iter()
                    .map(|(mut state, fields)| {
                        if state.running() {
                            let mut result = result.clone();
                            result.shape = match variant {
                                Some(variant) => ControlValueShape::Enum {
                                    definition,
                                    variant,
                                    fields,
                                },
                                None => ControlValueShape::Record { definition, fields },
                            };
                            state.outcome = ControlOutcome::Return(result);
                        }
                        state
                    })
                    .collect();
            }
            CoreKind::Field { base, index, .. } => {
                return self
                    .eval(frame, base, state)
                    .into_iter()
                    .map(|mut state| {
                        if state.running() {
                            state.outcome =
                                ControlOutcome::Return(project(&state.value(), index, &expr.ty));
                        }
                        state
                    })
                    .collect();
            }
            CoreKind::Let { name, value } => {
                return self
                    .eval(frame, value, state)
                    .into_iter()
                    .map(|mut state| {
                        if state.running() {
                            state.locals.insert(name.clone(), state.value());
                            state.outcome = ControlOutcome::Return(result.clone());
                        }
                        state
                    })
                    .collect();
            }
            CoreKind::Block(ids) => {
                let old = state.locals.clone();
                state.outcome = ControlOutcome::Return(result);
                let mut states = vec![state];
                for item in ids {
                    states = states
                        .into_iter()
                        .flat_map(|state| self.eval(frame, item, state))
                        .collect();
                    states = self.cap(states);
                }
                for state in &mut states {
                    // Local shadowing is scoped. Mutation is conservatively unsupported below.
                    state.locals = old.clone();
                }
                return states;
            }
            CoreKind::Move(value) => return self.eval(frame, value, state),
            CoreKind::Borrow { value, .. } => {
                return self
                    .eval(frame, value, state)
                    .into_iter()
                    .map(|mut state| {
                        if state.running() {
                            let mut result = result.clone();
                            result.shape = ControlValueShape::Borrow(Box::new(state.value()));
                            state.outcome = ControlOutcome::Return(result);
                        }
                        state
                    })
                    .collect();
            }
            CoreKind::Deref(value) => {
                return self
                    .eval(frame, value, state)
                    .into_iter()
                    .map(|mut state| {
                        if state.running() {
                            if let ControlValueShape::Borrow(value) = state.value().shape {
                                state.outcome = ControlOutcome::Return(*value);
                            } else {
                                return state
                                    .stop(ControlUnknown::Unsupported("opaque dereference"));
                            }
                        }
                        state
                    })
                    .collect();
            }
            CoreKind::Transfer { brand, value } => {
                let Some(target) = frame.labels.get(&brand).cloned() else {
                    return vec![state.stop(ControlUnknown::InvalidCore(frame.owner))];
                };
                return self
                    .eval(frame, value, state)
                    .into_iter()
                    .map(|mut state| {
                        if state.running() {
                            let value = state.value();
                            state.events.push(ControlEvent::Transfer {
                                site: frame.site(id),
                                target: target.clone(),
                                value: value.clone(),
                            });
                            state.outcome = ControlOutcome::LabelExit {
                                target: target.clone(),
                                value,
                            };
                        }
                        state
                    })
                    .collect();
            }
            CoreKind::Label { brand, body } => {
                let target = ControlLabelTarget::Lexical {
                    brand,
                    activation: frame.site(id),
                };
                let mut scoped = frame.clone();
                scoped.labels.insert(brand, target.clone());
                return self
                    .eval(&scoped, body, state)
                    .into_iter()
                    .map(|mut state| {
                        if let ControlOutcome::LabelExit {
                            target: actual,
                            value,
                        } = &state.outcome
                        {
                            if *actual == target {
                                state.outcome = ControlOutcome::Return(value.clone());
                            }
                        }
                        state
                    })
                    .collect();
            }
            CoreKind::Call {
                callee, arguments, ..
            } => {
                let mut output = vec![];
                for state in self.eval(frame, callee, state) {
                    if !state.running() {
                        output.push(state);
                        continue;
                    }
                    let callee = state.value();
                    for (state, arguments) in self.values(frame, &arguments, state) {
                        if state.running() {
                            output.extend(self.invoke(
                                frame,
                                id,
                                callee.clone(),
                                arguments,
                                expr.ty.clone(),
                                state,
                            ));
                        } else {
                            output.push(state);
                        }
                    }
                }
                return self.cap(output);
            }
            CoreKind::Completion {
                computation,
                clauses,
                refinement_test: None,
                ..
            } => {
                let mut output = vec![];
                let rows = clauses
                    .iter()
                    .map(|clause| std::slice::from_ref(&clause.pattern))
                    .collect::<Vec<_>>();
                let total = crate::core::core_pattern_rows_exhaustive(
                    self.bodies[&frame.owner].interface,
                    &[
                        self.bodies[&frame.owner].body.expressions[computation.0 as usize]
                            .ty
                            .clone(),
                    ],
                    &rows,
                );
                for state in self.eval(frame, computation, state) {
                    if !state.running() {
                        output.push(state);
                        continue;
                    }
                    let value = state.value();
                    let old = state.locals.clone();
                    let mut remaining = Some(state);
                    for clause in &clauses {
                        let Some(mut next) = remaining.take() else {
                            break;
                        };
                        if clause.refinement.is_some() {
                            output.push(
                                next.stop(ControlUnknown::Unsupported("refinement completion")),
                            );
                            break;
                        }
                        let instantiated = frame.pattern(clause.pattern.clone());
                        let decision = match_pattern(&value, &instantiated);
                        let pattern = erase_binders(&instantiated);
                        if decision != Some(false) {
                            let mut branch = next.clone();
                            if decision == Some(true)
                                || branch.guard(ControlGuard::Pattern {
                                    subject: value.origin.clone(),
                                    pattern: pattern.clone(),
                                    matches: true,
                                })
                            {
                                bind_pattern(&value, &instantiated, &mut branch.locals);
                                for mut branch in self.eval(frame, clause.body, branch) {
                                    branch.locals = old.clone();
                                    output.push(branch);
                                }
                            }
                        }
                        if decision == Some(true) {
                            break;
                        }
                        if decision == Some(false)
                            || next.guard(ControlGuard::Pattern {
                                subject: value.origin.clone(),
                                pattern,
                                matches: false,
                            })
                        {
                            remaining = Some(next);
                        }
                    }
                    if let Some(state) = remaining {
                        if !total {
                            output.push(
                                state.stop(ControlUnknown::Unsupported("uncovered completion")),
                            );
                        }
                    }
                }
                return self.cap(output);
            }
            CoreKind::Perform {
                mut effect,
                operation,
                arguments,
                terminal,
                ..
            } => {
                effect.arguments = effect
                    .arguments
                    .into_iter()
                    .map(|argument| frame.argument(argument))
                    .collect();
                return self
                    .values(frame, &arguments, state)
                    .into_iter()
                    .map(|(mut state, arguments)| {
                        if state.running() {
                            state.events.push(ControlEvent::Perform {
                                site: frame.site(id),
                                effect: effect.clone(),
                                operation,
                                arguments,
                            });
                            state.outcome = if terminal {
                                ControlOutcome::TerminalOperation {
                                    effect: effect.clone(),
                                    operation,
                                }
                            } else {
                                ControlOutcome::Unknown(ControlUnknown::Unsupported(
                                    "resumable operation",
                                ))
                            };
                        }
                        state
                    })
                    .collect();
            }
            CoreKind::Constant {
                definition,
                arguments,
            } => {
                return self.invoke(
                    frame,
                    id,
                    ControlValue {
                        shape: ControlValueShape::Callable {
                            brand: CallableBrand::Named(definition),
                            generic_arguments: Some(
                                arguments
                                    .into_iter()
                                    .map(|argument| frame.argument(argument))
                                    .collect(),
                            ),
                            captures: vec![],
                        },
                        ..result
                    },
                    vec![],
                    expr.ty,
                    state,
                );
            }
            CoreKind::Assign { .. } => {
                return vec![state.stop(ControlUnknown::Unsupported("mutation"))];
            }
            CoreKind::Handle { .. } => {
                return vec![state.stop(ControlUnknown::Unsupported("operation handler"))];
            }
            CoreKind::IntrinsicCall { .. } => {
                return vec![state.stop(ControlUnknown::Unsupported("primitive control contract"))];
            }
            CoreKind::PatternTest { .. } | CoreKind::Completion { .. } => {
                return vec![state.stop(ControlUnknown::Unsupported("refinement decision"))];
            }
            CoreKind::ReleaseAvailable(_) => {
                return vec![state.stop(ControlUnknown::Unsupported("availability cleanup"))];
            }
            CoreKind::Resumption { .. } => {
                return vec![state.stop(ControlUnknown::Unsupported("resumption"))];
            }
            CoreKind::Function { .. } | CoreKind::TraitMethod { .. } => {
                result.shape = ControlValueShape::OpaqueCallable
            }
            CoreKind::Error => return vec![state.stop(ControlUnknown::InvalidCore(frame.owner))],
        }
        state.outcome = ControlOutcome::Return(result);
        vec![state]
    }
    fn values(
        &mut self,
        frame: &Frame,
        ids: &[CoreId],
        state: State,
    ) -> Vec<(State, Vec<ControlValue>)> {
        let mut states = vec![(state, vec![])];
        for id in ids {
            let mut next = vec![];
            for (state, values) in states {
                if !state.running() {
                    next.push((state, values));
                    continue;
                }
                for state in self.eval(frame, *id, state) {
                    let mut values = values.clone();
                    if state.running() {
                        values.push(state.value());
                    }
                    next.push((state, values));
                }
            }
            if next.len() > self.limits.max_alternatives.max(1) {
                let (state, _) = next.pop().unwrap();
                next.truncate(self.limits.max_alternatives.saturating_sub(1));
                next.push((state.limit_witness(), vec![]));
            }
            states = next;
        }
        states
    }
    fn invoke(
        &mut self,
        frame: &Frame,
        id: CoreId,
        mut callee: ControlValue,
        arguments: Vec<ControlValue>,
        result_ty: Type,
        mut state: State,
    ) -> Vec<State> {
        while let ControlValueShape::Borrow(value) = callee.shape {
            callee = *value;
        }
        let site = frame.site(id);
        state.events.push(ControlEvent::Invoke {
            site: site.clone(),
            callee: callee.clone(),
            arguments: arguments.clone(),
        });
        match &callee.shape {
            ControlValueShape::Label(target) => {
                let [value] = arguments.as_slice() else {
                    return vec![state.stop(ControlUnknown::InvalidCore(frame.owner))];
                };
                state.outcome = ControlOutcome::LabelExit {
                    target: target.clone(),
                    value: value.clone(),
                };
                vec![state]
            }
            ControlValueShape::Callable {
                brand,
                generic_arguments,
                captures,
            } => {
                if self.stack.contains(brand) {
                    return vec![state.stop(ControlUnknown::RecursiveCall(*brand))];
                }
                if self.stack.len() >= self.limits.max_call_depth {
                    return vec![state.stop(ControlUnknown::Limit)];
                }
                let (owner, closure) = match brand {
                    CallableBrand::Named(owner) => (*owner, None),
                    CallableBrand::Closure(environment) => (environment.owner, Some(*environment)),
                    _ => return vec![state.stop(ControlUnknown::MissingBody(*brand))],
                };
                let Some(input) = self.bodies.get(&owner) else {
                    return vec![state.stop(ControlUnknown::MissingBody(*brand))];
                };
                self.dependencies.insert(owner, self.seals[&owner].clone());
                if let Err(reason) = &self.seals[&owner].valid {
                    return vec![state.stop(reason.clone())];
                }
                if let Some(arguments) = generic_arguments {
                    let valid =
                        arguments.len() == input.signature.generic_kinds.len()
                            && arguments.iter().zip(&input.signature.generic_kinds).all(
                                |(argument, kind)| match (argument, kind) {
                                    (GenericArgument::Type(_), crate::GenericKind::Type)
                                    | (
                                        GenericArgument::Lifetime(_),
                                        crate::GenericKind::Lifetime,
                                    )
                                    | (
                                        GenericArgument::EffectRow(_),
                                        crate::GenericKind::EffectRow,
                                    ) => true,
                                    (_, crate::GenericKind::Const(kind)) => {
                                        crate::types::generic_argument_matches_const_kind(
                                            argument, *kind,
                                        )
                                    }
                                    _ => false,
                                },
                            );
                    if !valid {
                        return vec![state.stop(ControlUnknown::InvalidContract(owner))];
                    }
                }
                let (root, parameters, capture_names) = if let Some(environment) = closure {
                    let Some((root, parameters, names)) =
                        input
                            .body
                            .expressions
                            .iter()
                            .find_map(|expr| match &expr.kind {
                                CoreKind::Closure {
                                    environment: actual,
                                    parameters,
                                    body,
                                    ..
                                } if actual.brand == environment => Some((
                                    *body,
                                    parameters.clone(),
                                    actual
                                        .captures
                                        .iter()
                                        .map(|capture| capture.name.clone())
                                        .collect::<Vec<_>>(),
                                )),
                                _ => None,
                            })
                    else {
                        return vec![state.stop(ControlUnknown::MissingBody(*brand))];
                    };
                    (root, parameters, names)
                } else {
                    (input.body.root, input.body.parameters.clone(), vec![])
                };
                if parameters.len() != arguments.len() || capture_names.len() != captures.len() {
                    return vec![state.stop(ControlUnknown::InvalidContract(owner))];
                }
                let old = std::mem::take(&mut state.locals);
                for (name, value) in capture_names.iter().zip(captures) {
                    state.locals.insert(name.clone(), value.clone());
                }
                for ((name, _), value) in parameters.iter().zip(arguments) {
                    state.locals.insert(name.clone(), value);
                }
                let mut calls = frame.calls.clone();
                calls.push(site.location);
                let child = Frame {
                    callable: *brand,
                    owner,
                    calls,
                    generic_arguments: generic_arguments.clone(),
                    occurrence: 0,
                    labels: BTreeMap::new(),
                };
                self.stack.push(*brand);
                let mut output = self.eval(&child, root, state);
                self.stack.pop();
                for state in &mut output {
                    state.locals = old.clone();
                }
                output
            }
            ControlValueShape::Unknown
                if matches!(
                    callee.origin,
                    ControlOrigin::Parameter(_)
                        | ControlOrigin::Capture(_)
                        | ControlOrigin::Field { .. }
                ) =>
            {
                let mut non_normal = state.clone();
                non_normal.outcome = ControlOutcome::UnresolvedInvocation(site.clone());
                if result_ty == Type::Never {
                    return vec![non_normal];
                }
                state.guards.push(ControlGuard::InvocationReturned(site));
                state.outcome = ControlOutcome::Return(unknown(frame, id, result_ty));
                vec![non_normal, state]
            }
            _ => vec![state.stop(ControlUnknown::OpaqueCall)],
        }
    }
}

fn project(value: &ControlValue, index: u32, ty: &Type) -> ControlValue {
    let fields = match &value.shape {
        ControlValueShape::Tuple(fields)
        | ControlValueShape::Array(fields)
        | ControlValueShape::Record { fields, .. }
        | ControlValueShape::Enum { fields, .. } => Some(fields),
        _ => None,
    };
    fields
        .and_then(|fields| fields.get(index as usize))
        .cloned()
        .unwrap_or_else(|| ControlValue {
            origin: ControlOrigin::Field {
                base: Box::new(value.origin.clone()),
                index,
            },
            ty: ty.clone(),
            shape: ControlValueShape::Unknown,
        })
}
fn erase_binders(pattern: &CorePattern) -> CorePattern {
    let mut pattern = pattern.clone();
    match &mut pattern {
        CorePattern::Bind { .. } => pattern = CorePattern::Any,
        CorePattern::Tuple(fields) => {
            for field in fields {
                *field = erase_binders(field);
            }
        }
        CorePattern::Array { elements, .. } => {
            for element in elements {
                *element = erase_binders(element);
            }
        }
        CorePattern::Record { fields, .. } | CorePattern::Enum { fields, .. } => {
            for field in fields {
                field.pattern = erase_binders(&field.pattern);
            }
        }
        _ => {}
    }
    pattern
}
fn match_pattern(value: &ControlValue, pattern: &CorePattern) -> Option<bool> {
    fn all(values: impl Iterator<Item = Option<bool>>) -> Option<bool> {
        let mut known = true;
        for value in values {
            match value {
                Some(false) => return Some(false),
                None => known = false,
                _ => {}
            }
        }
        known.then_some(true)
    }
    match pattern {
        CorePattern::Any | CorePattern::Bind { .. } => Some(true),
        CorePattern::Literal(expected) => {
            if let ControlValueShape::Literal(actual) = &value.shape {
                literal_matches(&value.ty, actual, expected)
            } else {
                None
            }
        }
        CorePattern::Tuple(patterns) => {
            if let ControlValueShape::Tuple(values) = &value.shape {
                if patterns.len() != values.len() {
                    Some(false)
                } else {
                    all(values
                        .iter()
                        .zip(patterns)
                        .map(|(value, pattern)| match_pattern(value, pattern)))
                }
            } else {
                None
            }
        }
        CorePattern::Record {
            definition, fields, ..
        }
        | CorePattern::Enum {
            definition, fields, ..
        } => {
            let (actual, variant) = match &value.shape {
                ControlValueShape::Record { definition, .. } => (*definition, None),
                ControlValueShape::Enum {
                    definition,
                    variant,
                    ..
                } => (*definition, Some(*variant)),
                _ => return None,
            };
            let expected = match pattern {
                CorePattern::Enum { variant, .. } => Some(*variant),
                _ => None,
            };
            if *definition != actual || expected != variant {
                return Some(false);
            }
            all(fields.iter().map(|field| {
                match_pattern(&project(value, field.index, &field.ty), &field.pattern)
            }))
        }
        CorePattern::Array { elements, rest, .. } => {
            if let ControlValueShape::Array(values) = &value.shape {
                if values.len() < elements.len()
                    || (rest.is_none() && values.len() != elements.len())
                {
                    return Some(false);
                }
                if crate::pattern::ArrayPatternRest::length(*rest, elements.len())
                    != Some(values.len())
                {
                    return Some(false);
                }
                all(elements.iter().enumerate().map(|(index, pattern)| {
                    match_pattern(
                        &values[crate::pattern::ArrayPatternRest::index(*rest, index)],
                        pattern,
                    )
                }))
            } else {
                None
            }
        }
        CorePattern::Error => None,
    }
}
fn literal_matches(ty: &Type, actual: &str, expected: &str) -> Option<bool> {
    use crate::ScalarType;
    let Type::Scalar(scalar) = ty else {
        return None;
    };
    Some(match scalar {
        ScalarType::Bool => match (actual, expected) {
            ("true" | "false", "true" | "false") => actual == expected,
            _ => return None,
        },
        ScalarType::F32 => {
            crate::mir::canonical_f32_bits(crate::mir::parse_f32_literal(actual).ok()?.to_bits())
                == crate::mir::canonical_f32_bits(
                    crate::mir::parse_f32_literal(expected).ok()?.to_bits(),
                )
        }
        ScalarType::F64 => {
            crate::mir::canonical_f64_bits(crate::mir::parse_f64_literal(actual).ok()?.to_bits())
                == crate::mir::canonical_f64_bits(
                    crate::mir::parse_f64_literal(expected).ok()?.to_bits(),
                )
        }
        ScalarType::Char => {
            crate::mir::parse_char_literal(actual).ok()?
                == crate::mir::parse_char_literal(expected).ok()?
        }
        ScalarType::Text => {
            crate::mir::parse_text_literal(actual).ok()?
                == crate::mir::parse_text_literal(expected).ok()?
        }
        ScalarType::Bytes => {
            crate::mir::parse_byte_literal(actual).ok()?
                == crate::mir::parse_byte_literal(expected).ok()?
        }
        scalar => {
            crate::mir::normalized_integer_literal(actual, *scalar).ok()?
                == crate::mir::normalized_integer_literal(expected, *scalar).ok()?
        }
    })
}
fn bind_pattern(
    value: &ControlValue,
    pattern: &CorePattern,
    locals: &mut BTreeMap<String, ControlValue>,
) {
    match pattern {
        CorePattern::Bind { name } => {
            locals.insert(name.clone(), value.clone());
        }
        CorePattern::Tuple(fields) => {
            for (index, field) in fields.iter().enumerate() {
                let ty = match &value.ty {
                    Type::Tuple(types) => types.get(index).cloned().unwrap_or(Type::Error),
                    _ => Type::Error,
                };
                bind_pattern(&project(value, index as u32, &ty), field, locals);
            }
        }
        CorePattern::Record { fields, .. } | CorePattern::Enum { fields, .. } => {
            for field in fields {
                bind_pattern(
                    &project(value, field.index, &field.ty),
                    &field.pattern,
                    locals,
                );
            }
        }
        CorePattern::Array {
            elements,
            element,
            rest,
        } => {
            for (index, field) in elements.iter().enumerate() {
                let index = crate::pattern::ArrayPatternRest::index(*rest, index);
                bind_pattern(&project(value, index as u32, element), field, locals);
            }
        }
        _ => {}
    }
}
