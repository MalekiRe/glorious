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
        let Some(control) = self.continuations.invocation(call).cloned() else {
            return;
        };
        // Partial observations cannot suppress a normal path or authorize
        // disposal. Keep the existing conservative state when coverage is open.
        if control.unknown || control.terminal_operation || control.cancellation {
            return;
        }
        let CoreKind::Call {
            callee, arguments, ..
        } = &self.body.expression(call).kind
        else {
            return;
        };
        let callable = invocations::Value::callable(*callee, owner);
        let arguments = arguments
            .iter()
            .map(|id| invocations::Value::core(*id))
            .collect::<Vec<_>>();
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
        if control.outer_transfer {
            let abandoned = self.minimum_bindings.keys().cloned().collect();
            self.check_minimum_scope(&abandoned, span);
        }
        if !control.normal {
            self.minimum_states.clear();
            self.normal_continuation = false;
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
