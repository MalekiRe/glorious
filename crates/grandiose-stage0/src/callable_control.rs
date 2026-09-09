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

#[cfg(test)]
mod tests;
mod payloads;
pub(crate) use payloads::{InvocationPayload, ResolvedPayload, resolve_payload};

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
    /// No complete invocation observation exists for the requested site.
    UnobservedCall,
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

/// Read-only invocation coverage. Presence of alternatives is not itself a
/// completeness proof: opaque or deferred invocations retain unknown outcomes.
/// Unknown coverage is unconditional and must not be discarded by specializing
/// guards from some separately observed execution of the same source call.
#[derive(Clone, Debug)]
pub enum ControlCallCoverage<'a> {
    Alternatives(&'a [ControlAlternative]),
    Unknown(ControlUnknown),
}
impl ControlCallCoverage<'_> {
    pub fn is_complete(&self) -> bool {
        matches!(self, Self::Alternatives(paths) if !paths.is_empty() && paths.iter().all(|path|
            !matches!(path.outcome, ControlOutcome::Unknown(_) | ControlOutcome::UnresolvedInvocation(_))))
    }
    pub fn only_returns_normally(&self) -> bool {
        self.is_complete()
            && matches!(self, Self::Alternatives(paths) if paths.iter()
            .all(|path| matches!(path.outcome, ControlOutcome::Return(_))))
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct CallContext {
    callable: CallableBrand,
    expression: CoreId,
    calls: Vec<ControlLocation>,
}
impl From<&ControlSite> for CallContext {
    fn from(site: &ControlSite) -> Self {
        Self {
            callable: site.location.callable,
            expression: site.location.expression,
            calls: site.calls.clone(),
        }
    }
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
    calls: BTreeMap<ControlSite, Vec<ControlAlternative>>,
    call_gaps: BTreeMap<CallContext, ControlUnknown>,
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
    /// Invocation observations, captured before the caller's suffix or any
    /// enclosing label rejoins. The iterator includes only observed sites;
    /// absence is unknown, never evidence that a source call cannot exit.
    /// Use `call` (as this iterator does) rather than bypassing coverage gaps.
    pub fn calls(&self) -> impl Iterator<Item = (&ControlSite, ControlCallCoverage<'_>)> {
        self.calls.keys().map(|site| (site, self.call(site)))
    }
    pub fn call(&self, site: &ControlSite) -> ControlCallCoverage<'_> {
        if let Some(reason) = self.call_gaps.get(&CallContext::from(site)) {
            return ControlCallCoverage::Unknown(reason.clone());
        }
        self.calls.get(site).map_or(
            ControlCallCoverage::Unknown(ControlUnknown::UnobservedCall),
            |paths| ControlCallCoverage::Alternatives(paths),
        )
    }
    pub fn dependencies(&self) -> impl Iterator<Item = ControlBodyIdentity> + '_ {
        self.dependencies.values().map(|seal| seal.identity)
    }
    /// All depended-on bodies, contracts and arena identities must still be
    /// present. Private seals prevent callers from fabricating this evidence.
    pub fn matches(&self, bodies: &BTreeMap<DefKey, ControlBody<'_>>) -> bool {
        self.dependencies.iter().all(|(key, seal)| {
            bodies.get(key).is_some_and(|input| {
                self.matches_body(*key, input.body)
                    && crate::signature::host_contract_fingerprint(*key, input.signature)
                        == seal.identity.contract
                    && input.body.diagnostics.is_empty()
                    && !input.body.recovered
                    && same_interface(input.interface, &seal.interface)
            })
        })
    }
    /// Local half of binding an already batch-validated summary set to a
    /// subsequent ownership request. This does not replace full `matches`.
    pub(crate) fn matches_body(&self, definition: DefKey, body: &TypedBody) -> bool {
        self.dependencies.get(&definition).is_some_and(|seal| {
            seal.valid.is_ok()
                && same_body(body, &seal.body)
                && body.semantic_fingerprint() == seal.identity.body
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

    /// Validate dependency seals once for the frozen analysis batch. A local
    /// body match alone cannot validate a helper whose implementation changed.
    pub(crate) fn bind<'a>(
        &'a self,
        bodies: &BTreeMap<DefKey, ControlBody<'_>>,
    ) -> Result<BoundControlSummaries<'a>, ControlUnknown> {
        let mut checked = std::collections::BTreeSet::new();
        let mut interfaces = std::collections::BTreeSet::new();
        for summary in self.summaries.values() {
            for (key, seal) in &summary.dependencies {
                if !checked.insert(*key) { continue; }
                let Some(input) = bodies.get(key) else {
                    return Err(ControlUnknown::MissingBody(CallableBrand::Named(*key)));
                };
                let interface_matches = !interfaces.insert((input.interface as *const ElaboratedInterface,
                    Arc::as_ptr(&seal.interface))) || same_interface(input.interface, &seal.interface);
                if !same_body(input.body, &seal.body)
                    || crate::signature::host_contract_fingerprint(*key, input.signature) != seal.identity.contract
                    || !interface_matches {
                    return Err(ControlUnknown::InvalidContract(*key));
                }
            }
        }
        Ok(BoundControlSummaries { summaries: self })
    }
}

/// May-outcomes, conditional on reaching an invocation after its strict
/// operands. Projecting guards to a union is conservative; this grants no
/// exact invocation count, mutation ordering, or branch-correlation proof.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct InvocationControl {
    pub normal: bool,
    pub labels: std::collections::BTreeSet<LabelBrand>,
    pub outer_transfer: bool,
    pub terminal_operation: bool,
    pub cancellation: bool,
    pub divergence: bool,
    pub unknown: bool,
    pub transfers: Vec<InvocationTransfer>,
    pub returns: Vec<InvocationPayload>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct InvocationTransfer {
    /// None denotes a label supplied from outside this independently checked
    /// body. It is not an invented local destination.
    pub target: Option<LabelBrand>,
    pub payload: InvocationPayload,
}

impl InvocationControl {
    fn include(&mut self, outcome: &ControlOutcome, callable: CallableBrand, payload: Option<InvocationPayload>) {
        match outcome {
            ControlOutcome::Return(_) => {
                self.normal = true;
                self.returns.push(payload.expect("return payload projection"));
            }
            ControlOutcome::LabelExit { target: ControlLabelTarget::Lexical { brand, activation }, .. }
                if activation.calls.is_empty() && activation.location.callable == callable => {
                    self.labels.insert(*brand);
                    self.transfers.push(InvocationTransfer { target: Some(*brand), payload: payload.expect("label payload projection") });
                }
            ControlOutcome::LabelExit { .. } => {
                self.outer_transfer = true;
                self.transfers.push(InvocationTransfer { target: None, payload: payload.expect("label payload projection") });
            }
            ControlOutcome::TerminalOperation { .. } => self.terminal_operation = true,
            ControlOutcome::Cancellation => self.cancellation = true,
            ControlOutcome::Divergence => self.divergence = true,
            ControlOutcome::UnresolvedInvocation(_) | ControlOutcome::Unknown(_) => self.unknown = true,
        }
    }
}

pub(crate) struct BoundControlSummaries<'a> {
    summaries: &'a ControlSummarySet,
}

#[derive(Clone, Debug)]
pub(crate) struct BodyInvocationControl {
    body: Arc<TypedBody>,
    calls: BTreeMap<CoreId, InvocationControl>,
}

impl BodyInvocationControl {
    pub(crate) fn matches(&self, body: &TypedBody) -> bool { same_body(body, &self.body) }
    pub(crate) fn get(&self, id: CoreId) -> Option<&InvocationControl> { self.calls.get(&id) }
}

impl BoundControlSummaries<'_> {
    pub(crate) fn body(&self, owner: DefKey) -> Option<BodyInvocationControl> {
        let root = self.summaries.get(CallableBrand::Named(owner))?;
        let seal = root.dependencies.get(&owner)?;
        if seal.valid.is_err() { return None; }
        let body = seal.body.clone();
        let mut calls = BTreeMap::<CoreId, InvocationControl>::new();
        for (callable, summary) in self.summaries.iter().filter(|(_, summary)| summary.identity.definition == owner) {
            for (site, coverage) in summary.calls() {
                // Expanded helper/closure activations have their own frame.
                // Only standalone observations belong to this arena's owners.
                if !site.calls.is_empty() || site.location.callable != callable { continue; }
                let control = calls.entry(site.location.expression).or_default();
                match coverage {
                    ControlCallCoverage::Alternatives(paths) if !paths.is_empty() => {
                        for path in paths {
                            let payload = if let ControlOutcome::LabelExit { value, .. } | ControlOutcome::Return(value) = &path.outcome {
                                let inputs = path.events.iter().find_map(|event| match event {
                                    ControlEvent::Invoke { site: actual, callee, arguments } if actual == site => Some((callee, arguments)),
                                    _ => None,
                                });
                                Some(match inputs {
                                    Some((callee, arguments)) => self.observed_payload(value, callee, arguments),
                                    None => InvocationPayload::unknown(value.ty.clone()),
                                })
                            } else { None };
                            control.include(&path.outcome, callable, payload);
                        }
                    }
                    _ => control.unknown = true,
                }
            }
        }
        // A gap in an enclosing execution does not invalidate a callee's
        // independently checked abstract contract. Compose that contract only
        // at statically selected calls and only with positively known label
        // operands. This is conditional on *reaching the invocation*, not a
        // fabricated observation of the preceding computation or its guards.
        for (index, expression) in body.expressions.iter().enumerate() {
            let id = CoreId(index as u32);
            if calls.get(&id).is_some_and(|control| !control.unknown) { continue; }
            if let Some(control) = self.declared_call_control(&body, expression) {
                calls.insert(id, control);
            }
        }
        Some(BodyInvocationControl { body, calls })
    }

    fn declared_call_control(&self, body: &TypedBody, expression: &crate::CoreExpr) -> Option<InvocationControl> {
        let CoreKind::Call { callee, arguments, .. } = &expression.kind else { return None; };
        let definition = match &body.expression(*callee).kind {
            CoreKind::Function { definition, host_import: None, .. } => *definition,
            CoreKind::TraitMethod { method, deferred: None, .. } => *method,
            _ => return None,
        };
        let summary = self.summaries.get(CallableBrand::Named(definition))?;
        let substitutions = summary.dependencies.get(&definition).and_then(|seal|
            crate::callable_declarations::selected_template(&seal.interface, body.expression(*callee)))
            .map(|template| template.arguments);
        let mut control = InvocationControl::default();
        if summary.alternatives.is_empty() { control.unknown = true; }
        for path in &summary.alternatives {
            match &path.outcome {
                ControlOutcome::LabelExit { target: ControlLabelTarget::Symbolic(ControlOrigin::Parameter(parameter)), value } => {
                    match arguments.get(*parameter as usize).map(|argument| &body.expression(*argument).kind) {
                        Some(CoreKind::LabelValue { brand }) => {
                            control.labels.insert(*brand);
                            let mut payload = payloads::declared_payload(value);
                            if let Some(arguments) = &substitutions { payload.instantiate_types(arguments); }
                            control.transfers.push(InvocationTransfer {
                                target: Some(*brand), payload,
                            });
                        }
                        // An unknown/aliased operand is not proof that the
                        // symbolic target leaves this caller's local labels.
                        _ => control.unknown = true,
                    }
                }
                ControlOutcome::LabelExit { .. } => control.unknown = true,
                ControlOutcome::Return(value) => {
                    let mut payload = payloads::declared_payload(value);
                    if let Some(arguments) = &substitutions { payload.instantiate_types(arguments); }
                    control.include(&path.outcome, CallableBrand::Named(definition), Some(payload));
                }
                outcome => control.include(outcome, CallableBrand::Named(definition), None),
            }
        }
        Some(control)
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
    fn alternative(&self) -> ControlAlternative {
        ControlAlternative {
            guards: self.guards.clone(),
            events: self.events.clone(),
            outcome: self.outcome.clone(),
        }
    }
    fn running(&self) -> bool {
        matches!(self.outcome, ControlOutcome::Return(_))
    }
    fn coverage_gap(&self) -> Option<ControlUnknown> {
        match &self.outcome {
            ControlOutcome::Unknown(reason) => Some(reason.clone()),
            // A callback may invoke a local label capability it was given.
            // It then never returns to its call site, but execution rejoins
            // after that label. Until the actual callback resolves this edge,
            // skipped caller continuations are not proved unreachable.
            ControlOutcome::UnresolvedInvocation(_) => Some(ControlUnknown::Unsupported(
                "unresolved invocation continuation",
            )),
            // Reserved for future cleanup/cancellation modeling. Do not let an
            // unmodeled cancellation silently prove a continuation absent.
            ControlOutcome::Cancellation => {
                Some(ControlUnknown::Unsupported("cancellation continuation"))
            }
            // Exact local label transfers are caught by `Label`. A terminal
            // operation cannot resume this suffix: any intervening handler is
            // stopped as unknown before its computation is evaluated.
            ControlOutcome::Return(_)
            | ControlOutcome::LabelExit { .. }
            | ControlOutcome::TerminalOperation { .. }
            | ControlOutcome::Divergence => None,
        }
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
    derive_control_summaries_with_check(bodies, limits, &mut |_, _| Ok::<_, std::convert::Infallible>(()))
        .unwrap_or_else(|never| match never {})
}

pub(crate) fn derive_control_summaries_with_check<E>(
    bodies: &BTreeMap<DefKey, ControlBody<'_>>,
    limits: ControlSummaryLimits,
    check: &mut impl FnMut(DefKey, u64) -> Result<(), E>,
) -> Result<ControlSummarySet, E> {
    let mut interfaces = BTreeMap::new();
    let mut seals = BTreeMap::new();
    for (key, input) in bodies {
        check(*key, input.body.expressions.len() as u64 + 1)?;
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
        seals.insert(*key, Arc::new(Seal {
            identity: ControlBodyIdentity { definition: *key, body: input.body.semantic_fingerprint(),
                contract: crate::signature::host_contract_fingerprint(*key, input.signature) },
            body: Arc::new(input.body.clone()), interface, valid,
        }));
    }
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
            check(*owner, 0)?;
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
                calls: BTreeMap::new(),
                call_gaps: BTreeMap::new(),
            };
            let states = match &seals[owner].valid {
                Ok(()) => analyzer.eval(&frame, root, initial),
                Err(reason) => vec![initial.stop(reason.clone())],
            };
            check(*owner, analyzer.steps as u64 + 1)?;
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
                    calls: analyzer.calls,
                    call_gaps: analyzer.call_gaps,
                },
            );
        }
    }
    Ok(output)
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
    calls: BTreeMap<ControlSite, Vec<ControlAlternative>>,
    call_gaps: BTreeMap<CallContext, ControlUnknown>,
}
impl Analyzer<'_, '_> {
    fn record_call(&mut self, site: ControlSite, states: &[State]) {
        let paths = self.calls.entry(site).or_default();
        paths.extend(states.iter().map(State::alternative));
        if paths.len() > self.limits.max_alternatives.max(1) {
            paths.truncate(self.limits.max_alternatives.saturating_sub(1));
            paths.push(ControlAlternative {
                guards: vec![],
                events: vec![],
                outcome: ControlOutcome::Unknown(ControlUnknown::Limit),
            });
        }
    }
    fn call_gap(&mut self, frame: &Frame, id: CoreId, reason: &ControlUnknown) {
        self.call_gaps
            .entry(CallContext {
                callable: frame.callable,
                expression: id,
                calls: frame.calls.clone(),
            })
            .or_insert_with(|| reason.clone());
    }
    /// Mark only an unvisited suffix/subtree. Retrospectively tainting a whole
    /// enclosing block would erase valid observations before a later unknown.
    fn unvisited(&mut self, frame: &Frame, id: CoreId, reason: &ControlUnknown) {
        let mut pending = vec![id];
        let mut seen = std::collections::BTreeSet::new();
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            let Some(expr) = self.bodies[&frame.owner]
                .body
                .expressions
                .get(id.0 as usize)
            else {
                continue;
            };
            let children = unvisited_children(&expr.kind);
            if matches!(expr.kind, CoreKind::Call { .. } | CoreKind::Constant { .. }) {
                self.call_gap(frame, id, reason);
            }
            pending.extend(children);
        }
    }
    fn stop_unvisited(
        &mut self,
        frame: &Frame,
        id: CoreId,
        state: State,
        reason: ControlUnknown,
    ) -> Vec<State> {
        self.unvisited(frame, id, &reason);
        vec![state.stop(reason)]
    }
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
            if let Some(reason) = state.coverage_gap() {
                self.unvisited(frame, id, &reason);
            }
            return vec![state];
        }
        self.steps += 1;
        if self.steps > self.limits.max_steps {
            return self.stop_unvisited(frame, id, state, ControlUnknown::Limit);
        }
        let site = (frame.callable, id, frame.calls.clone());
        if self.evaluating.contains(&site) {
            return self.stop_unvisited(frame, id, state, ControlUnknown::InvalidCore(frame.owner));
        }
        if self.evaluating.len() >= 512 {
            return self.stop_unvisited(frame, id, state, ControlUnknown::Limit);
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
                evidence,
                method,
                trait_arguments,
                method_arguments,
                deferred: None,
            } => {
                let selected = crate::CoreExpr {
                    kind: CoreKind::TraitMethod {
                        evidence, method,
                        trait_arguments: trait_arguments.into_iter().map(|value| frame.argument(value)).collect(),
                        method_arguments: method_arguments.into_iter().map(|value| frame.argument(value)).collect(),
                        deferred: None,
                    },
                    ty: expr.ty.clone(), span: expr.span,
                };
                result.shape = match crate::callable_declarations::selected_template(
                    self.bodies[&frame.owner].interface, &selected,
                ) {
                    Some(template) => ControlValueShape::Callable {
                        brand: CallableBrand::Named(method), generic_arguments: Some(template.arguments), captures: vec![],
                    },
                    None => ControlValueShape::OpaqueCallable,
                };
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
                        if let Some(reason) = state.coverage_gap() {
                            self.call_gap(frame, id, &reason);
                            for argument in &arguments {
                                self.unvisited(frame, *argument, &reason);
                            }
                        }
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
                            if let Some(reason) = state.coverage_gap() {
                                self.call_gap(frame, id, &reason);
                            }
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
                        if let Some(reason) = state.coverage_gap() {
                            for clause in &clauses {
                                self.unvisited(frame, clause.body, &reason);
                            }
                        }
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
                            for clause in &clauses {
                                self.unvisited(
                                    frame,
                                    clause.body,
                                    &ControlUnknown::Unsupported("refinement completion"),
                                );
                            }
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
                return self.stop_unvisited(
                    frame,
                    id,
                    state,
                    ControlUnknown::Unsupported("mutation"),
                );
            }
            CoreKind::Handle { .. } => {
                return self.stop_unvisited(
                    frame,
                    id,
                    state,
                    ControlUnknown::Unsupported("operation handler"),
                );
            }
            CoreKind::IntrinsicCall { .. } => {
                return self.stop_unvisited(
                    frame,
                    id,
                    state,
                    ControlUnknown::Unsupported("primitive control contract"),
                );
            }
            CoreKind::PatternTest { .. } | CoreKind::Completion { .. } => {
                return self.stop_unvisited(
                    frame,
                    id,
                    state,
                    ControlUnknown::Unsupported("refinement decision"),
                );
            }
            CoreKind::ReleaseAvailable(_) => {
                return self.stop_unvisited(
                    frame,
                    id,
                    state,
                    ControlUnknown::Unsupported("availability cleanup"),
                );
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
                    if let Some(reason) = state.coverage_gap() {
                        self.unvisited(frame, *id, &reason);
                    }
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
        callee: ControlValue,
        arguments: Vec<ControlValue>,
        result_ty: Type,
        state: State,
    ) -> Vec<State> {
        let output = self.invoke_inner(frame, id, callee, arguments, result_ty, state);
        self.record_call(frame.site(id), &output);
        output
    }
    fn invoke_inner(
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

/// Children that may execute while evaluating this expression in the current
/// callable. Merely constructing a closure does not run its body, and handler
/// clause bodies belong to their own callable namespaces.
fn unvisited_children(kind: &CoreKind) -> Vec<CoreId> {
    match kind {
        CoreKind::Tuple(values) | CoreKind::Array(values) | CoreKind::Block(values) => {
            values.clone()
        }
        CoreKind::Record { fields, .. } | CoreKind::Enum { fields, .. } => fields.clone(),
        CoreKind::Field { base, .. }
        | CoreKind::PatternTest { subject: base, .. }
        | CoreKind::Borrow { value: base, .. }
        | CoreKind::Deref(base)
        | CoreKind::Move(base)
        | CoreKind::ReleaseAvailable(base) => vec![*base],
        CoreKind::Let { value, .. }
        | CoreKind::Label { body: value, .. }
        | CoreKind::Transfer { value, .. } => vec![*value],
        CoreKind::Assign { place, value } => {
            let mut children = vec![*value];
            let mut place = place;
            loop {
                match place {
                    crate::CorePlace::Field { base, .. } => place = base,
                    crate::CorePlace::Deref { reference, .. } => {
                        children.push(*reference);
                        break;
                    }
                    _ => break,
                }
            }
            children
        }
        CoreKind::Call {
            callee, arguments, ..
        } => std::iter::once(*callee)
            .chain(arguments.iter().copied())
            .collect(),
        CoreKind::Perform { arguments, .. } | CoreKind::IntrinsicCall { arguments, .. } => {
            arguments.clone()
        }
        CoreKind::Handle { computation, .. } => vec![*computation],
        CoreKind::Completion {
            computation,
            clauses,
            ..
        } => std::iter::once(*computation)
            .chain(clauses.iter().map(|clause| clause.body))
            .collect(),
        CoreKind::Closure { .. }
        | CoreKind::Literal(_)
        | CoreKind::ConstValue(_)
        | CoreKind::Local(_)
        | CoreKind::Resumption { .. }
        | CoreKind::Function { .. }
        | CoreKind::TraitMethod { .. }
        | CoreKind::Constant { .. }
        | CoreKind::LabelValue { .. }
        | CoreKind::Error => vec![],
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
