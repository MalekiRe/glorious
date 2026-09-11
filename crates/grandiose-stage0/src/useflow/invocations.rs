//! Invocation input/result bindings and execution of checked callable bodies.
//! This reuses the quantity solver, with the original capability keys, rather
//! than deriving invocation counts from the control producer's may-outcomes.
use super::*;
use crate::CallableBrand;
use crate::callable_control::{PayloadInputs, ResolvedPayload, resolve_payload};
use crate::resident_invocations::{CapturedInputs, Operand};

#[derive(Clone, Copy)]
pub(crate) struct UseBody<'a> {
    pub body: &'a TypedBody,
    pub flow: &'a PlaceFlow,
}
pub(crate) type UseBodies<'a> = BTreeMap<crate::DefKey, UseBody<'a>>;

struct Inputs;
impl PayloadInputs for Inputs {
    type Value = Binding;
    fn project(&self, value: &Binding, path: &[u32]) -> Option<Binding> {
        let Some((field, rest)) = path.split_first() else {
            return Some(value.clone());
        };
        if *field == crate::core::REFERENCE_PATH_DEREF {
            return self.project(value, rest);
        }
        match value {
            Binding::Aggregate(fields) => self.project(fields.get(field)?, rest),
            Binding::Choice(choices) => Some(Binding::choice(
                choices
                    .iter()
                    .map(|value| self.project(value, path))
                    .collect::<Option<Vec<_>>>()?,
            )),
            _ => None,
        }
    }
    fn captures(&self, callable: &Operand<Binding>) -> CapturedInputs<Binding> {
        let Binding::Closure(closure) = &callable.value else {
            return CapturedInputs {
                operands: vec![],
                unresolved: true,
            };
        };
        CapturedInputs {
            operands: closure
                .resident_types
                .iter()
                .map(|(name, ty)| Operand {
                    ty: ty.clone(),
                    value: closure
                        .captures
                        .get(name)
                        .cloned()
                        .unwrap_or(Binding::Other),
                })
                .collect(),
            unresolved: false,
        }
    }
    fn reborrow(&self, value: &Binding, fields: &[u32]) -> Option<Binding> {
        self.project(value, fields)
    }
}

impl Binding {
    pub(super) fn choice(mut choices: Vec<Self>) -> Self {
        if choices.len() == 1 {
            choices.pop().unwrap()
        } else if choices.is_empty() {
            Self::Other
        } else {
            Self::Choice(choices)
        }
    }
    pub(super) fn has_capability(&self) -> bool {
        match self {
            Self::Contract(_) => true,
            Self::Closure(closure) => closure.captures.values().any(Self::has_capability),
            Self::Aggregate(fields) => fields.values().any(Self::has_capability),
            Self::Choice(choices) => choices.iter().any(Self::has_capability),
            Self::GlobalCallable | Self::Other => false,
        }
    }
}

impl<'a> Analyzer<'a> {
    fn use_body(&self, owner: crate::DefKey) -> Option<UseBody<'a>> {
        self.bodies
            .and_then(|bodies| bodies.get(&owner))
            .copied()
            .or_else(|| {
                // Standalone local closure analysis still uses its own frozen
                // arena. Foreign constructors require the complete registry.
                self.body_flow
                    .closure_flows()
                    .keys()
                    .any(|brand| brand.owner == owner)
                    .then_some(UseBody {
                        body: self.body,
                        flow: self.body_flow,
                    })
            })
    }

    fn payload_binding(&mut self, payload: ResolvedPayload<Binding>, span: Span) -> Binding {
        match payload {
            ResolvedPayload::Inputs { values, .. } => Binding::choice(values),
            ResolvedPayload::Aggregate(fields) | ResolvedPayload::Variant(fields) => Binding::Aggregate(
                fields
                    .into_iter()
                    .enumerate()
                    .map(|(index, field)| (index as u32, self.payload_binding(field, span)))
                    .collect(),
            ),
            ResolvedPayload::Unknown(_) => Binding::Other,
            ResolvedPayload::Callable {
                ty,
                constructor,
                captures,
            } => {
                let captures = captures
                    .into_iter()
                    .map(|(ty, payload)| (ty, self.payload_binding(payload, span)))
                    .collect::<Vec<_>>();
                let Some(source) = self.use_body(constructor.brand().owner) else {
                    if captures.iter().any(|(_, binding)| binding.has_capability()) {
                        self.error(
                            span,
                            "G5013",
                            "returned callable capability has no checked defining body",
                        );
                    }
                    return Binding::Other;
                };
                if !constructor.matches_body(source.body)
                    || !source.flow.diagnostics.is_empty()
                    || source.flow.continuations_for(source.body).is_err()
                {
                    self.error(
                        span,
                        "G5013",
                        "returned callable capability has stale or invalid body evidence",
                    );
                    return Binding::Other;
                }
                let Some((parameters, environment, body)) = source
                    .body
                    .expressions
                    .iter()
                    .find_map(|expr| match &expr.kind {
                        CoreKind::Closure {
                            parameters,
                            environment,
                            body,
                            ..
                        } if environment.brand == constructor.brand() => {
                            Some((parameters, environment, *body))
                        }
                        _ => None,
                    })
                else {
                    self.error(
                        span,
                        "G5013",
                        "returned callable constructor is absent from its checked body",
                    );
                    return Binding::Other;
                };
                if captures.len() != environment.captures.len() {
                    self.error(
                        span,
                        "G5013",
                        "returned callable capture relation does not match its constructor",
                    );
                    return Binding::Other;
                }
                Binding::Closure(ClosureValue {
                    environment: environment.brand,
                    body,
                    parameters: parameters.clone(),
                    invocation: callable_invocation(&ty).unwrap_or(Quantity::ONCE),
                    resident_types: environment
                        .captures
                        .iter()
                        .zip(&captures)
                        .map(|(capture, (ty, _))| (capture.name.clone(), ty.clone()))
                        .collect(),
                    captures: environment
                        .captures
                        .iter()
                        .zip(captures)
                        .map(|(capture, (_, binding))| (capture.name.clone(), binding))
                        .collect(),
                })
            }
        }
    }

    /// Evaluate one quantity frame. All arena-indexed caches and loan facts
    /// belong to that frame; capability keys and their obligations belong to
    /// the calling analysis and survive the boundary.
    fn run_frame(
        &mut self,
        source: UseBody<'a>,
        identity: CallableBrand,
        root: CoreId,
        mut environment: Environment,
        span: Span,
    ) -> (Summary, Binding) {
        if self.active_frames.contains(&identity)
            || self.active_frames.len() >= 64
            || self.frame_steps >= 4096
        {
            self.error(
                span,
                "G5013",
                "callable capability execution requires an unavailable finite quantity proof",
            );
            return (Summary::default(), Binding::Other);
        }
        let Ok(continuations) = source.flow.continuations_for(source.body) else {
            self.error(
                span,
                "G5013",
                "callable quantity frame has stale continuation evidence",
            );
            return (Summary::default(), Binding::Other);
        };
        let ownership = match identity {
            CallableBrand::Closure(brand) => source.flow.closure_flows().get(&brand),
            CallableBrand::Named(_) => Some(source.flow),
            CallableBrand::HandlerClause { .. } | CallableBrand::Continuation { .. } => None,
        };
        let Some(ownership) = ownership.filter(|flow| flow.diagnostics.is_empty()) else {
            self.error(
                span,
                "G5013",
                "callable quantity frame has no valid ownership product",
            );
            return (Summary::default(), Binding::Other);
        };
        self.active_frames.push(identity);
        self.frame_steps += 1;
        let saved = (
            self.body,
            self.body_flow,
            self.ownership,
            self.continuations,
            std::mem::take(&mut self.projected_contracts),
            std::mem::take(&mut self.closure_values),
            std::mem::take(&mut self.result_values),
        );
        self.body = source.body;
        self.body_flow = source.flow;
        self.ownership = ownership;
        self.continuations = continuations;
        let summary = self.expression(root, &mut environment);
        let result = self.binding_for_value(root, &environment);
        (
            self.body,
            self.body_flow,
            self.ownership,
            self.continuations,
            self.projected_contracts,
            self.closure_values,
            self.result_values,
        ) = saved;
        self.active_frames.pop();
        (summary, result)
    }

    pub(super) fn run_closure(
        &mut self,
        closure: ClosureValue,
        arguments: &[Binding],
        span: Span,
    ) -> (Summary, Binding) {
        let Some(source) = self.use_body(closure.environment.owner) else {
            self.error(
                span,
                "G5013",
                "callable capability has no checked invocation body",
            );
            return (Summary::default(), Binding::Other);
        };
        let mut environment = Environment {
            bindings: closure.captures,
        };
        for (index, (name, _)) in closure.parameters.iter().enumerate() {
            environment.bindings.insert(
                name.clone(),
                arguments.get(index).cloned().unwrap_or(Binding::Other),
            );
        }
        let enclosing = self.take_escapes();
        let (summary, result) = self.run_frame(
            source,
            CallableBrand::Closure(closure.environment),
            closure.body,
            environment,
            span,
        );
        let escapes = self.take_escapes();
        self.escapes = enclosing;
        let escapes = self.scale_escapes(span, escapes, closure.invocation);
        self.sequence_escapes(span, escapes);
        (self.repeat(span, summary, closure.invocation), result)
    }

    pub(super) fn checked_body_call(
        &mut self,
        id: CoreId,
        callable: &Binding,
        arguments: &[Binding],
        span: Span,
    ) -> Option<(Summary, Binding)> {
        let control = self.continuations.invocation(id)?.clone();
        let results = control
            .returns
            .iter()
            .map(|payload| resolve_payload(payload, callable, arguments, &Inputs))
            .collect::<Vec<_>>();
        let result = Binding::choice(
            results
                .into_iter()
                .map(|payload| self.payload_binding(payload, span))
                .collect(),
        );
        let produces_capability = result.has_capability();
        if !produces_capability && !arguments.iter().any(Binding::has_capability) {
            return None;
        }
        let Some((definition, source)) = control
            .declared_function
            .and_then(|definition| self.use_body(definition).map(|source| (definition, source)))
        else {
            // An unknown consumer still uses the declared outgoing contract.
            // Only a retained producer result requires its defining body here.
            if !produces_capability { return None; }
            self.error(
                span,
                "G5013",
                "returned capability requires a checked quantity execution for its producer",
            );
            return Some((Summary::default(), result));
        };
        let environment = Environment {
            bindings: source
                .body
                .parameters
                .iter()
                .enumerate()
                .map(|(index, (name, _))| {
                    (
                        name.clone(),
                        arguments.get(index).cloned().unwrap_or(Binding::Other),
                    )
                })
                .collect(),
        };
        Some(self.run_frame(
            source,
            CallableBrand::Named(definition),
            source.body.root,
            environment,
            span,
        ))
    }

    pub(super) fn branch_bindings(
        &mut self,
        choices: &[Binding],
        span: Span,
        mut run: impl FnMut(&mut Self, &Binding) -> Summary,
    ) -> Summary {
        let enclosing = self.take_escapes();
        let mut summary = None::<Summary>;
        let mut escapes = None::<EscapeSummary>;
        for binding in choices {
            let branch = run(self, binding);
            summary = Some(match summary {
                Some(previous) => previous.branch_hull(branch),
                None => branch,
            });
            let next = self.take_escapes();
            escapes = Some(match escapes {
                Some(previous) => previous.branch_hull(next),
                None => next,
            });
        }
        self.escapes = enclosing;
        self.sequence_escapes(span, escapes.unwrap_or_default());
        summary.unwrap_or_default()
    }
}
