//! Ordinary owner disposition and suspension obligations, separate from
//! callable invocation quantities.
//!
//! `moved_places` is a may-move fact: a move on either predecessor makes a
//! later read invalid. Minimum use needs the dual proof, so retain distinct
//! disposition alternatives until a scope ends. A move on one predecessor
//! must never discharge the owner which remains on another predecessor.

use super::*;

#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct MinimumDisposition {
    transferred: BTreeSet<Projection>,
    /// Opening a constructor consumes its shell, not omitted residents.
    /// An enum opening also seals the selected payload variant on this path.
    opened: BTreeMap<Projection, Option<u32>>,
}

impl MinimumDisposition {
    pub(super) fn retain_owners(&mut self, owners: &BTreeSet<String>) {
        self.transferred.retain(|place| owners.contains(&place.root));
        self.opened.retain(|place, _| owners.contains(&place.root));
    }
}

#[derive(Clone)]
pub(super) struct MinimumBinding {
    ty: Type,
    span: Span,
    scope: SourceStorageScopeId,
}

#[derive(Clone)]
pub(super) struct HandlerFrame {
    pub(super) computation: CoreId,
    pub(super) clauses: Vec<crate::core::CoreHandlerClause>,
    /// None is an unobserved/unsupported input relation, not an empty payload.
    pub(super) payloads: Vec<Option<Vec<PatternBindingTransfer>>>,
    operations: Vec<(crate::EffectInstance, u32, Quantity)>,
    retained: BTreeSet<String>,
    cancellations: Vec<(crate::EffectInstance, u32, Vec<MinimumDisposition>)>,
}

/// A generic call's cancellation requirement, with owner-relative paths.
/// Local storage identities do not become generic interface parameters.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct MinimumSuspension {
    call: CoreId,
    effects: crate::EffectRow,
    ty: Type,
    transferred: BTreeSet<Vec<u32>>,
    opened: BTreeMap<Vec<u32>, Option<u32>>,
    /// Innermost matching handler wins after effect argument substitution.
    handlers: Vec<(Vec<(crate::EffectInstance, u32, Quantity)>, bool)>,
    owner: String,
    span: Span,
}

#[derive(Clone, Debug)]
pub(crate) struct DischargedMinimum {
    input: Option<crate::Digest>,
    definition: crate::DefKey,
    instance: crate::Digest,
    requirements: Vec<MinimumSuspension>,
}

impl DischargedMinimum {
    pub(crate) fn matches(&self, flow: &PlaceFlow, definition: crate::DefKey, instance: &crate::InstanceKey) -> bool {
        self.input == flow.resource_input && self.definition == definition
            && self.instance == instance.fingerprint() && self.requirements == flow.minimum_suspensions
    }
}

impl PlaceFlow {
    /// Instantiate the retained disposition, not the original Core body.
    /// A closed instance must exclude cancellation/replay or prove each
    /// residual resident permits disposal/copying by the same ownership rule.
    pub(crate) fn discharge_minimum(
        &self, definition: crate::DefKey, instance: &crate::InstanceKey,
        arguments: &[crate::GenericArgument], signatures: &ElaboratedInterface,
    ) -> Result<DischargedMinimum, FlowDiagnostic> {
        let mut solver = crate::TraitSolver::new(signatures);
        for requirement in &self.minimum_suspensions {
            let failure = |detail: String| FlowDiagnostic {
                code: "G5024", span: requirement.span,
                message: format!("owner `{}` retains a conditional minimum-use obligation at call {}: {detail}",
                    requirement.owner, requirement.call.0),
            };
            let row = crate::service::normalize_materialized_effect_row(
                &crate::service::specialize_effect_row(&requirement.effects, arguments), &mut solver, 0)
                .map_err(|error| failure(format!("effect row could not be closed: {error}")))?;
            if !row.tails.is_empty() || !row.projections.is_empty() {
                return Err(failure("effect row remains unknown".into()));
            }
            let mut handlers = Vec::new();
            for (operations, retained) in &requirement.handlers {
                let mut closed = Vec::new();
                for (effect, operation, usage) in operations {
                    let effect = crate::service::normalize_materialized_effect_row(
                        &crate::service::specialize_effect_row(&crate::EffectRow::closed_instances([effect.clone()]), arguments),
                        &mut solver, 0).map_err(|error| failure(format!("handler effect could not be closed: {error}")))?;
                    if !effect.tails.is_empty() || !effect.projections.is_empty() || effect.effects.len() != 1 {
                        return Err(failure("handler effect is not one closed operation family".into()));
                    }
                    closed.push((effect.effects.first().unwrap().clone(), *operation, *usage));
                }
                handlers.push((closed, *retained));
            }
            let mut can_abandon = false;
            let mut can_repeat = false;
            for effect in &row.effects {
                let Some(crate::ElaboratedHeader::Effect(header)) = signatures.definitions.get(&effect.definition) else {
                    return Err(failure("effect declaration is missing".into()));
                };
                for (operation, declaration) in header.operations.iter().enumerate() {
                    let (usage, retained) = handlers.iter().rev().find_map(|(operations, retained)| {
                        operations.iter().find(|(handled, selected, _)| handled == effect && *selected == operation as u32)
                            .map(|(_, _, usage)| (*usage, *retained))
                    }).unwrap_or((if declaration.terminal { Quantity::ZERO } else { declaration.resumption }, false));
                    can_abandon |= !usage.requires_positive_use() && !retained;
                    can_repeat |= usage.upper.is_none_or(|upper| upper > 1);
                }
            }
            if !can_abandon && !can_repeat { continue; }
            let ty = crate::service::normalize_materialized_type(
                &crate::service::specialize_type(&requirement.ty, arguments), &mut solver)
                .map_err(|error| failure(format!("owner type could not be closed: {error}")))?;
            let state = MinimumDisposition {
                transferred: requirement.transferred.iter().map(|fields| Projection { root: String::new(), fields: fields.clone() }).collect(),
                opened: requirement.opened.iter().map(|(fields, variant)| (Projection { root: String::new(), fields: fields.clone() }, *variant)).collect(),
            };
            let context = MinimumContext { signatures: Some(signatures), solver: Some(&solver), lexical_bounds: &[], delegate_callables: false };
            let root = Projection { root: String::new(), fields: vec![] };
            if can_abandon && context.minimum_pending(&ty, &root, &state, 0, Quantity::ZERO) {
                return Err(failure("this effect instantiation may cancel a retained owner that does not permit zero use".into()));
            }
            if can_repeat && context.minimum_pending(&ty, &root, &state, 0, Quantity::UNRESTRICTED) {
                return Err(failure("this effect instantiation may replay a retained owner that does not permit copying".into()));
            }
        }
        Ok(DischargedMinimum { input: self.resource_input, definition, instance: instance.fingerprint(),
            requirements: self.minimum_suspensions.clone() })
    }
}

impl Analyzer<'_> {
    pub(super) fn minimum_handler_completes_normally(
        &self,
        value: CoreId,
        clauses: &[crate::core::CoreHandlerClause],
    ) -> bool {
        if self.continuations.is_abrupt(value) {
            return false;
        }
        match &self.body.expression(value).kind {
            CoreKind::Perform {
                effect, operation, ..
            } => !clauses.iter().any(|clause| {
                clause.effect == *effect
                    && clause.operation == *operation
                    && matches!(
                        clause.resumption,
                        crate::core::CoreHandlerResumption::Discard { .. }
                            | crate::core::CoreHandlerResumption::Terminal
                    )
            }),
            CoreKind::Block(values) | CoreKind::Tuple(values) | CoreKind::Array(values) => values
                .iter()
                .all(|value| self.minimum_handler_completes_normally(*value, clauses)),
            CoreKind::Let { value, .. } => self.minimum_handler_completes_normally(*value, clauses),
            CoreKind::Call {
                callee, arguments, ..
            } => std::iter::once(callee)
                .chain(arguments)
                .all(|value| self.minimum_handler_completes_normally(*value, clauses)),
            CoreKind::Completion {
                computation,
                clauses: arms,
                ..
            } => {
                self.minimum_handler_completes_normally(*computation, clauses)
                    && arms
                        .iter()
                        .any(|arm| self.minimum_handler_completes_normally(arm.body, clauses))
            }
            _ => true,
        }
    }

    pub(super) fn enter_handler_frame(&mut self, computation: CoreId, clauses: &[crate::core::CoreHandlerClause]) {
        let operations = clauses
            .iter()
            .map(|clause| {
                let usage = match clause.resumption {
                    crate::core::CoreHandlerResumption::Discard { .. }
                    | crate::core::CoreHandlerResumption::Terminal => Quantity::ZERO,
                    crate::core::CoreHandlerResumption::Explicit { quantity, .. } => quantity,
                    crate::core::CoreHandlerResumption::Tail { .. } => Quantity::ONCE,
                };
                (clause.effect.clone(), clause.operation, usage)
            })
            .collect();
        self.handler_frames.push(HandlerFrame {
            computation,
            clauses: clauses.to_vec(),
            payloads: vec![None; clauses.len()],
            operations,
            retained: self.minimum_bindings.keys().cloned().collect(),
            cancellations: vec![],
        });
    }

    pub(super) fn minimum_clause_inputs(
        &self,
        handler: &HandlerFrame,
        clause: &crate::core::CoreHandlerClause,
        completed: &[MinimumDisposition],
    ) -> Vec<MinimumDisposition> {
        let cancelled = handler
            .cancellations
            .iter()
            .filter(|(effect, operation, _)| {
                effect == &clause.effect && *operation == clause.operation
            })
            .flat_map(|(_, _, states)| states.iter().cloned())
            .collect::<Vec<_>>();
        if cancelled.is_empty() {
            return completed.to_vec();
        }
        if matches!(
            clause.resumption,
            crate::core::CoreHandlerResumption::Discard { .. }
                | crate::core::CoreHandlerResumption::Terminal
        ) {
            cancelled
        } else {
            completed
                .iter()
                .cloned()
                .chain(cancelled)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect()
        }
    }

    pub(super) fn check_minimum_suspension(
        &mut self,
        effect: &crate::EffectInstance,
        operation: u32,
        span: Span,
    ) {
        let handler = self.handler_frames.iter().rev().find(|handler| {
            handler
                .operations
                .iter()
                .any(|(handled, selected, _)| handled == effect && *selected == operation)
        });
        let can_cancel = handler.map_or_else(
            || {
                self.signatures
                    .and_then(|signatures| signatures.definitions.get(&effect.definition))
                    .and_then(|header| match header {
                        crate::ElaboratedHeader::Effect(effect) => {
                            effect.operations.get(operation as usize)
                        }
                        _ => None,
                    })
                    .is_some_and(|operation| !operation.resumption.requires_positive_use())
            },
            |handler| {
                handler
                    .operations
                    .iter()
                    .any(|(handled, selected, usage)| {
                        handled == effect && *selected == operation && !usage.requires_positive_use()
                    })
            },
        );
        if !can_cancel {
            return;
        }
        let abandoned = self
            .minimum_bindings
            .keys()
            .filter(|owner| handler.is_none_or(|handler| !handler.retained.contains(*owner)))
            .cloned()
            .collect::<BTreeSet<_>>();
        self.check_minimum_scope(&abandoned, span);
        if let Some(handler) = self.handler_frames.iter_mut().rev().find(|handler| {
            handler
                .operations
                .iter()
                .any(|(handled, selected, _)| handled == effect && *selected == operation)
        }) {
            let states = self
                .minimum_states
                .iter()
                .cloned()
                .map(|mut state| {
                    state
                        .transferred
                        .retain(|place| handler.retained.contains(&place.root));
                    state
                        .opened
                        .retain(|place, _| handler.retained.contains(&place.root));
                    state
                })
                .collect();
            handler
                .cancellations
                .push((effect.clone(), operation, states));
        }
    }

    pub(super) fn minimum_owned_by_callable_lane(&self, ty: &Type) -> bool {
        callable_lane(ty, self.lexical_bounds)
    }

    pub(super) fn check_minimum_call_suspensions(&mut self, call: CoreId, span: Span) {
        // Consume the shared body's execution proof, not the declaration's
        // permission row, when complete coverage excludes all performances.
        // Label/outer-transfer dispositions are still checked independently.
        if self.continuations.invocation(call).is_some_and(|control| control.without_performance()) {
            return;
        }
        let CoreKind::Call { invocation, .. } = &self.body.expression(call).kind else { unreachable!() };
        let effects = invocation.effects.clone();
        if !effects.tails.is_empty() || !effects.projections.is_empty() {
            // An open row is a conditional contract, not permission to lose
            // an owner. Preserve each guarded residual state for the closed
            // instance to discharge before any executable is admitted.
            for (owner, binding) in &self.minimum_bindings {
                for state in &self.minimum_states {
                    let place = Projection { root: owner.clone(), fields: vec![] };
                    if !self.minimum_pending(&binding.ty, &place, state, 0)
                        && !self.minimum_replay_pending(&binding.ty, &place, state) { continue; }
                    let requirement = MinimumSuspension {
                        call, effects: effects.clone(), ty: binding.ty.clone(), span: binding.span, owner: owner.clone(),
                        transferred: state.transferred.iter().filter(|place| place.root == *owner)
                            .map(|place| place.fields.clone()).collect(),
                        opened: state.opened.iter().filter(|(place, _)| place.root == *owner)
                            .map(|(place, variant)| (place.fields.clone(), *variant)).collect(),
                        handlers: self.handler_frames.iter().map(|handler|
                            (handler.operations.clone(), handler.retained.contains(owner))).collect(),
                    };
                    if !self.minimum_suspensions.contains(&requirement) { self.minimum_suspensions.push(requirement); }
                }
            }
        }
        for effect in &effects.effects {
            let operations = self
                .signatures
                .and_then(|signatures| signatures.definitions.get(&effect.definition))
                .and_then(|header| match header {
                    crate::ElaboratedHeader::Effect(effect) => Some(effect.operations.len()),
                    _ => None,
                })
                .unwrap_or(0);
            for operation in 0..operations {
                self.check_minimum_suspension(effect, operation as u32, span);
            }
        }
    }

    pub(super) fn minimum_definitely_aborts(&self, id: CoreId) -> bool {
        let Some(abort) = self.abort_primitive else {
            return false;
        };
        match &self.body.expression(id).kind {
            CoreKind::Call {
                callee, arguments, ..
            } => {
                matches!(self.body.expression(*callee).kind,
                CoreKind::Function { definition, .. } if definition == abort)
                    && arguments
                        .iter()
                        .all(|argument| !self.continuations.is_abrupt(*argument))
            }
            CoreKind::Block(values) => values
                .iter()
                .find(|value| self.continuations.is_abrupt(**value))
                .is_some_and(|value| self.minimum_definitely_aborts(*value)),
            CoreKind::Let { value, .. } | CoreKind::Transfer { value, .. } => {
                self.minimum_definitely_aborts(*value)
            }
            _ => false,
        }
    }

    fn minimum_context(&self) -> MinimumContext<'_> {
        let solver = self.signatures.map(|signatures| self.ownership_solver.get_or_init(|| {
            self.frozen_solver.map_or_else(
                || crate::TraitSolver::new(signatures),
                crate::TraitSolver::fresh_query,
            )
        }));
        MinimumContext { signatures: self.signatures, solver, lexical_bounds: self.lexical_bounds, delegate_callables: true }
    }

    fn minimum_pending(&self, ty: &Type, place: &Projection, state: &MinimumDisposition, depth: usize) -> bool {
        self.minimum_context().minimum_pending(ty, place, state, depth, Quantity::ZERO)
    }

    fn minimum_replay_pending(&self, ty: &Type, place: &Projection, state: &MinimumDisposition) -> bool {
        // Borrowed storage and known callable invocation are owned by their
        // existing loan/environment lanes. Ordinary affine owners still need
        // copying permission when an open effect row is instantiated to replay.
        !matches!(ty, Type::Reference { .. })
            && self.minimum_context().minimum_pending(ty, place, state, 0, Quantity::UNRESTRICTED)
    }
}

fn callable_lane(ty: &Type, bounds: &[(Type, crate::ElaboratedTraitReference)]) -> bool {
    matches!(ty, Type::Callable { .. }) || bounds.iter().any(|(subject, relation)| {
        subject == ty && (crate::signature::is_intrinsic_callable_trait(relation)
            || crate::signature::is_intrinsic_label_trait(relation))
    })
}

/// Shared disposition rule at source checking and concrete instantiation.
/// Neither consumer reconstructs ownership transitions from another body walk.
struct MinimumContext<'a> {
    signatures: Option<&'a ElaboratedInterface>,
    solver: Option<&'a crate::TraitSolver>,
    lexical_bounds: &'a [(Type, crate::ElaboratedTraitReference)],
    delegate_callables: bool,
}

impl MinimumContext<'_> {
    fn minimum_quantity(&self, ty: &Type) -> Option<Quantity> {
        let signatures = self.signatures?;
        let solver = self.solver?;
        signatures
            .principal_use_interval_with_solver(ty, solver)
            .or_else(|| {
                signatures.principal_use_interval_with_bounds_and_solver(
                    ty,
                    self.lexical_bounds,
                    solver,
                )
            })
    }

    fn minimum_pending(
        &self,
        ty: &Type,
        place: &Projection,
        state: &MinimumDisposition,
        depth: usize,
        permission: Quantity,
    ) -> bool {
        if state
            .transferred
            .iter()
            .any(|moved| moved.root == place.root && place.fields.starts_with(&moved.fields))
        {
            return false;
        }
        if matches!(ty, Type::Projection { .. })
            && depth < 96
            && self.signatures.is_some()
        {
            let Some(solver) = self.solver else { return true; };
            if let Ok(normalized) = solver.fresh_query().normalize_type(ty.clone())
                && normalized != *ty
            {
                return self.minimum_pending(&normalized, place, state, depth + 1, permission);
            }
        }
        // Invoking a callable (including a field) has its own After/environment
        // calculus in UseFlow; it is not an ordinary nominal shell obligation.
        if (self.delegate_callables && callable_lane(ty, self.lexical_bounds))
            || self
                .minimum_quantity(ty)
                .is_some_and(|q| q.contains(permission))
        {
            return false;
        }
        if depth >= 96 {
            return true;
        }
        let field_pending = |index: u32, ty: &Type| {
            let mut field = place.clone();
            field.fields.push(index);
            self.minimum_pending(ty, &field, state, depth + 1, permission)
        };
        match ty {
            Type::Tuple(fields) => fields
                .iter()
                .enumerate()
                .any(|(index, ty)| field_pending(index as u32, ty)),
            Type::FixedArray { element, .. } => {
                let Some(length) = ty.fixed_array_length() else {
                    return true;
                };
                if length == 0
                    || !self.minimum_pending(
                        element,
                        &Projection {
                            root: String::new(),
                            fields: vec![],
                        },
                        &MinimumDisposition::default(),
                        depth + 1,
                        permission,
                    )
                {
                    return false;
                }
                // Proof metadata is sparse even for a huge or zero-byte array.
                // An untouched index still carries its element obligation.
                let indices = state
                    .transferred
                    .iter()
                    .chain(state.opened.keys())
                    .filter(|field| {
                        field.root == place.root && field.fields.starts_with(&place.fields)
                    })
                    .filter_map(|field| field.fields.get(place.fields.len()).copied())
                    .filter(|index| u64::from(*index) < length)
                    .collect::<BTreeSet<_>>();
                indices.len() as u64 != length
                    || indices
                        .into_iter()
                        .any(|index| field_pending(index, element))
            }
            Type::Array(element) => {
                self.minimum_pending(element, place, &MinimumDisposition::default(), depth + 1, permission)
            }
            Type::Nominal {
                definition,
                arguments,
            } => {
                let Some(signatures) = self.signatures else {
                    return false;
                };
                let Some(solver) = self.solver else { return true; };
                let opening = state.opened.get(place);
                if solver.has_manual_use_for(*definition) && opening.is_none() {
                    return true;
                }
                let Some(crate::ElaboratedHeader::Nominal { layout, .. }) =
                    signatures.definitions.get(definition)
                else {
                    // Compiler binding packs have an explicit sealed layout.
                    return crate::refinement::binding_pack_fields(ty).map_or(true, |fields| {
                        fields
                            .iter()
                            .enumerate()
                            .any(|(index, ty)| field_pending(index as u32, ty))
                    });
                };
                let Some(layouts) = crate::mir::instantiate_nominal_copy_layout(layout, arguments)
                else {
                    return true;
                };
                if let Some(Some(variant)) = opening {
                    return layouts.get(*variant as usize).map_or(true, |fields| {
                        fields
                            .iter()
                            .enumerate()
                            .any(|(index, ty)| field_pending(index as u32, ty))
                    });
                }
                layouts.iter().any(|fields| {
                    fields
                        .iter()
                        .enumerate()
                        .any(|(index, ty)| field_pending(index as u32, ty))
                })
            }
            // Unknown generic evidence cannot authorize zero use. Forwarding
            // the whole value remains legal and retains that same obligation.
            Type::Generic(_) | Type::Projection { .. } => true,
            Type::Error | Type::Infer(_) | Type::Never => false,
            _ => true,
        }
    }

}

impl Analyzer<'_> {
    pub(super) fn record_minimum_binding(&mut self, owner: &str, ty: &Type, span: Span) {
        if self.signatures.is_none() {
            return;
        }
        let place = Projection {
            root: owner.to_owned(),
            fields: vec![],
        };
        if self.minimum_pending(ty, &place, &MinimumDisposition::default(), 0)
            || self.minimum_replay_pending(ty, &place, &MinimumDisposition::default()) {
            self.minimum_bindings.insert(
                owner.to_owned(),
                MinimumBinding {
                    ty: ty.clone(),
                    span,
                    scope: *self
                        .active_storage_scopes
                        .last()
                        .expect("active minimum-use storage scope"),
                },
            );
        }
    }

    pub(super) fn retain_minimum_operand(&mut self, value: CoreId) -> String {
        let owner = self.fresh_binding(&format!("<strict-operand-{}>", value.0));
        self.record_minimum_binding(
            &owner,
            &self.body.expression(value).ty.clone(),
            self.body.expression(value).span,
        );
        owner
    }

    pub(super) fn minimum_transfer(&mut self, place: &Projection) {
        if !self.minimum_bindings.contains_key(&place.root) {
            return;
        }
        for state in &mut self.minimum_states {
            state
                .transferred
                .retain(|field| !place.is_strict_ancestor_of(field));
            if !state
                .transferred
                .iter()
                .any(|field| field.root == place.root && place.fields.starts_with(&field.fields))
            {
                state.transferred.insert(place.clone());
            }
        }
    }

    pub(super) fn check_minimum_scope(&mut self, locals: &BTreeSet<String>, _span: Span) {
        let failures = self
            .minimum_bindings
            .iter()
            .filter(|(owner, _)| locals.contains(*owner))
            .filter(|(owner, binding)| {
                self.minimum_states.iter().any(|state| {
                    self.minimum_pending(
                        &binding.ty,
                        &Projection {
                            root: (*owner).clone(),
                            fields: vec![],
                        },
                        state,
                        0,
                    )
                })
            })
            .map(|(owner, binding)| (owner.clone(), binding.span))
            .collect::<Vec<_>>();
        for (owner, initialized) in failures {
            self.error(initialized, "G5024", format!("owner `{owner}` requires a transfer or authorized deconstruction on every scope-exit path; destruction is zero use"));
        }
    }

    pub(super) fn release_minimum_owners(&mut self, locals: &BTreeSet<String>) {
        self.minimum_bindings
            .retain(|owner, _| !locals.contains(owner));
        for state in &mut self.minimum_states {
            state
                .transferred
                .retain(|place| !locals.contains(&place.root));
            state
                .opened
                .retain(|place, _| !locals.contains(&place.root));
        }
    }

    pub(super) fn end_minimum_scope(&mut self, scope: SourceStorageScopeId, span: Span) {
        let locals = self
            .minimum_bindings
            .iter()
            .filter(|(_, binding)| binding.scope == scope)
            .map(|(owner, _)| owner.clone())
            .collect();
        self.check_minimum_scope(&locals, span);
        self.release_minimum_owners(&locals);
    }

    pub(super) fn check_minimum_discard(&mut self, ty: &Type, span: Span) {
        if self.signatures.is_some()
            && self.minimum_pending(
                ty,
                &Projection {
                    root: String::new(),
                    fields: vec![],
                },
                &MinimumDisposition::default(),
                0,
            )
        {
            self.error(span, "G5024", "discarded value requires zero-use permission; moving through a local or helper does not discharge its returned owner".into());
        }
    }

    pub(super) fn check_minimum_assignment(&mut self, place: &Projection, ty: &Type, span: Span) {
        if self.minimum_states.iter().any(|state| {
            state
                .opened
                .keys()
                .any(|opened| opened.is_strict_ancestor_of(place))
        }) {
            self.error(
                span,
                "G5001",
                format!(
                    "cannot assign through deconstructed owner `{}`",
                    place.display()
                ),
            );
        }
        if self.minimum_bindings.contains_key(&place.root)
            && self
                .minimum_states
                .iter()
                .any(|state| self.minimum_pending(ty, place, state, 0))
        {
            self.error(
                span,
                "G5024",
                format!(
                    "assignment would destroy the outstanding minimum-use owner `{}`",
                    place.display()
                ),
            );
        }
        for state in &mut self.minimum_states {
            state.transferred.retain(|field| {
                field.root != place.root || !field.fields.starts_with(&place.fields)
            });
            state.opened.retain(|field, _| {
                field.root != place.root || !field.fields.starts_with(&place.fields)
            });
        }
    }

    pub(super) fn minimum_shell_available(&mut self, place: &Projection, span: Span) -> bool {
        if self
            .minimum_states
            .iter()
            .any(|state| state.opened.keys().any(|opened| opened.overlaps(place)))
        {
            self.error(
                span,
                "G5001",
                format!("use of deconstructed owner `{}`", place.display()),
            );
            false
        } else {
            true
        }
    }

    pub(super) fn join_minimum_exits(&mut self, exits: Vec<Vec<MinimumDisposition>>, span: Span) {
        let states = exits.into_iter().flatten().collect::<BTreeSet<_>>();
        if states.len() > 512 {
            self.error(
                span,
                "G5024",
                "minimum-use control alternatives exceed their finite proof budget".into(),
            );
            self.minimum_states = vec![MinimumDisposition::default()];
        } else {
            self.minimum_states = states.into_iter().collect();
        }
    }

    pub(super) fn open_minimum_pattern(
        &mut self,
        value: CoreId,
        place: Option<Projection>,
        pattern: &CorePattern,
        span: Span,
    ) {
        let ty = self.body.expression(value).ty.clone();
        if matches!(ty, Type::Reference { .. }) || self.projected_dereference(value).is_some() {
            return;
        }
        self.open_minimum_pattern_at(place.as_ref(), &ty, pattern, span);
    }

    pub(super) fn open_minimum_payload_patterns(
        &mut self,
        clause: &crate::core::CoreHandlerClause,
    ) {
        if self.minimum_definitely_aborts(clause.body) {
            return;
        }
        for (ty, pattern) in clause.payload_types.iter().zip(&clause.patterns) {
            if !matches!(ty, Type::Reference { .. }) {
                self.open_minimum_pattern_at(None, ty, pattern, clause.span);
            }
        }
    }

    fn open_minimum_pattern_at(
        &mut self,
        place: Option<&Projection>,
        ty: &Type,
        pattern: &CorePattern,
        span: Span,
    ) {
        let mut fields = Vec::<(u32, Type, &CorePattern)>::new();
        let variant = match pattern {
            CorePattern::Any => {
                self.check_minimum_discard(ty, span);
                return;
            }
            CorePattern::Bind { .. } | CorePattern::Literal(_) | CorePattern::Error => return,
            CorePattern::Tuple(patterns) => {
                let Type::Tuple(types) = ty else {
                    return;
                };
                fields.extend(
                    patterns
                        .iter()
                        .zip(types)
                        .enumerate()
                        .map(|(index, (pattern, ty))| (index as u32, ty.clone(), pattern)),
                );
                None
            }
            CorePattern::Array {
                element,
                elements,
                rest,
            } => {
                if rest.is_some_and(|rest| rest.omitted != 0) {
                    self.check_minimum_discard(element, span);
                }
                fields.extend(elements.iter().enumerate().map(|(index, pattern)| {
                    (
                        crate::pattern::ArrayPatternRest::index(*rest, index) as u32,
                        element.clone(),
                        pattern,
                    )
                }));
                None
            }
            CorePattern::Record {
                fields: patterns, ..
            }
            | CorePattern::Enum {
                fields: patterns, ..
            } => {
                fields.extend(
                    patterns
                        .iter()
                        .map(|field| (field.index, field.ty.clone(), &field.pattern)),
                );
                let variant = match pattern {
                    CorePattern::Enum { variant, .. } => Some(*variant),
                    _ => None,
                };
                if let Type::Nominal {
                    definition,
                    arguments,
                } = ty
                    && let Some(crate::ElaboratedHeader::Nominal { layout, .. }) = self
                        .signatures
                        .and_then(|signatures| signatures.definitions.get(definition))
                    && let Some(layouts) =
                        crate::mir::instantiate_nominal_copy_layout(layout, arguments)
                    && let Some(types) = layouts.get(variant.unwrap_or(0) as usize)
                {
                    for (index, ty) in types.iter().enumerate() {
                        if !patterns.iter().any(|field| field.index as usize == index) {
                            self.check_minimum_discard(ty, span);
                        }
                    }
                }
                variant
            }
        };
        for (index, ty, pattern) in fields {
            let field = place.map(|place| {
                let mut field = place.clone();
                field.fields.push(index);
                field
            });
            self.open_minimum_pattern_at(field.as_ref(), &ty, pattern, span);
        }
        let empty = match pattern {
            CorePattern::Record { field_count, .. } | CorePattern::Enum { field_count, .. } => {
                *field_count == 0
            }
            CorePattern::Tuple(fields) => fields.is_empty(),
            CorePattern::Array { elements, rest, .. } => {
                crate::pattern::ArrayPatternRest::length(*rest, elements.len()) == Some(0)
            }
            _ => false,
        };
        if empty
            && !self.is_duplicable(ty)
            && let Some(place) = place
        {
            self.move_projection(place.clone(), span);
        } else if let Some(place) =
            place.filter(|place| self.minimum_bindings.contains_key(&place.root))
        {
            for state in &mut self.minimum_states {
                state.opened.insert(place.clone(), variant);
            }
        }
    }
}
