//! Branded ownership continuations. A lexical exit is not an ordinary branch
//! result: its move and minimum-use state belongs to its own destination.

use super::*;

pub(super) struct LabelBoundary {
    pub id: CoreId,
    pub brand: crate::LabelBrand,
    pub incoming: BTreeMap<String, LocalState>,
    pub retained: BTreeSet<String>,
    pub exits: Vec<ContinuationState>,
}

impl Analyzer<'_> {
    pub(super) fn apply_invocation_control(
        &mut self,
        call: CoreId,
        owner: Option<&str>,
        span: Span,
    ) {
        let CoreKind::Call {
            callee, arguments, reference_shape, ..
        } = self.body.expression(call).kind.clone()
        else {
            return;
        };
        let result_ty = self.body.expression(call).ty.clone();
        let Some(control) = self.continuations.invocation(call).cloned() else {
            self.reject_opaque_reference_result(reference_shape, &result_ty, span, "call");
            return;
        };
        let callable = invocations::Value::callable(callee, owner);
        let arguments = arguments
            .iter()
            .map(|id| invocations::Value::core(*id))
            .collect::<Vec<_>>();
        let empty = ElaboratedInterface::default();
        let returned = control.resolve_returns(&result_ty, self.signatures.unwrap_or(&empty), &callable, &arguments, self);
        if !returned.references.is_complete() {
            self.reject_opaque_reference_result(reference_shape, &result_ty, span, "call");
        }
        // Partial observations cannot suppress a normal path or authorize
        // disposal. They can still add positively observed result origins.
        if control.unknown || control.terminal_operation || control.cancellation {
            self.preserve_invocation_returns(call, returned.payloads);
            return;
        }
        let incoming = self.capture_continuation();
        for target in control.labels {
            self.restore_continuation(&incoming);
            if let Some(id) = self
                .label_continuations
                .iter()
                .rev()
                .find(|label| label.brand == target)
                .map(|label| label.id)
            {
                let result = Self::result_owner(id);
                for transfer in control
                    .transfers
                    .iter()
                    .filter(|transfer| transfer.target == Some(target))
                {
                    let payload = crate::callable_control::resolve_payload(
                        &transfer.payload,
                        &callable,
                        &arguments,
                        self,
                    );
                    self.record_payload_origins(&result, payload, call);
                }
                self.pending_results.insert(id);
            }
            self.record_label_continuation(target, span);
        }
        self.restore_continuation(&incoming);
        if control.normal {
            self.preserve_invocation_returns(call, returned.payloads);
        }
        if control.outer_transfer {
            let abandoned = self.minimum_bindings.keys().cloned().collect();
            self.check_minimum_scope(&abandoned, span);
        }
        if !control.normal {
            self.minimum_states.clear();
            self.normal_continuation = false;
        }
    }

    fn preserve_invocation_returns(
        &mut self,
        call: CoreId,
        returns: Vec<crate::callable_control::ResolvedPayload<invocations::Value>>,
    ) {
        if returns.is_empty() { return; }
        // Snapshot the declared result before installing an additional
        // body-derived root: a partial input projection must not mask it.
        self.preserve_expression_result(call, call);
        let result = Self::result_owner(call);
        for payload in returns {
            self.record_known_payload_origins(&result, payload, call);
        }
        if self.reference_origins.keys().chain(self.logical.origins.keys())
            .any(|key| key == &result || key.starts_with(&(result.clone() + "."))) {
            self.pending_results.insert(call);
        }
    }

    pub(super) fn enter_label_continuation(&mut self, id: CoreId, brand: crate::LabelBrand) {
        self.label_continuations.push(LabelBoundary {
            id,
            brand,
            incoming: self.states.clone(),
            // Strict operands are protected owners even when they have no
            // source local and therefore no ordinary LocalState entry.
            retained: self
                .states
                .keys()
                .chain(self.minimum_bindings.keys())
                .cloned()
                .collect(),
            exits: vec![],
        });
    }

    pub(super) fn record_label_continuation(&mut self, brand: crate::LabelBrand, span: Span) {
        let target = self
            .label_continuations
            .iter()
            .rposition(|label| label.brand == brand);
        let retained = target
            .map(|index| self.label_continuations[index].retained.clone())
            .unwrap_or_default();
        // These owners are abandoned by this edge, not by the later lexical
        // suffix. Check them before ordinary scope teardown removes their
        // binding records, and before any sibling arm can consume a value.
        let abandoned = self
            .minimum_bindings
            .keys()
            .filter(|owner| !retained.contains(*owner))
            .cloned()
            .collect();
        self.check_minimum_scope(&abandoned, span);
        if let Some(index) = target {
            let mut state = self.capture_continuation();
            state.states.retain(|owner, _| retained.contains(owner));
            for disposition in &mut state.minimum {
                disposition.retain_owners(&retained);
            }
            self.label_continuations[index].exits.push(state);
        }
        self.minimum_states.clear();
        self.normal_continuation = false;
    }

    pub(super) fn finish_label_continuation(&mut self, brand: crate::LabelBrand, span: Span) {
        let mut label = self
            .label_continuations
            .pop()
            .expect("active lexical label continuation");
        assert_eq!(
            label.brand, brand,
            "label continuation stack preserves generative identity"
        );
        if self.normal_continuation {
            label.exits.push(self.capture_continuation());
        }
        self.normal_continuation = !label.exits.is_empty();
        if self.normal_continuation {
            self.join_continuation_states(&label.exits, &label.incoming, span);
        }
    }

    pub(super) fn join_continuation_states(
        &mut self,
        exits: &[ContinuationState],
        incoming: &BTreeMap<String, LocalState>,
        span: Span,
    ) {
        self.states = join_handler_exits(
            &exits
                .iter()
                .map(|exit| exit.states.clone())
                .collect::<Vec<_>>(),
        );
        self.projection_loans = join_handler_projection_loans(exits, incoming);
        self.moved_places = join_handler_moves(exits, incoming);
        self.join_reborrow_facts(exits, incoming);
        self.open_referent_holes = join_handler_referent_holes(exits, incoming);
        self.join_minimum_exits(
            exits.iter().map(|exit| exit.minimum.clone()).collect(),
            span,
        );
    }
}
