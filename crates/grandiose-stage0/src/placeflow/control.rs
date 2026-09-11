//! Branded ownership continuations. A lexical exit is not an ordinary branch
//! result: its move and minimum-use state belongs to its own destination.

use super::*;

#[derive(Clone)]
pub(super) struct LabelBoundary {
    pub id: CoreId,
    pub brand: crate::LabelBrand,
    pub incoming: BTreeMap<String, LocalState>,
    pub retained: BTreeSet<String>,
    pub exits: Vec<ContinuationState>,
}

impl Analyzer<'_> {
    pub(super) fn resolve_invocation_returns(&self, call: CoreId, callable: &invocations::Value,
        arguments: &[invocations::EvaluatedOperand])
        -> Option<crate::callable_control::ResolvedReturns<invocations::Value>> {
        let control = self.continuations.invocation(call)?;
        let arguments = arguments.iter().map(|input| input.operand.value.clone()).collect::<Vec<_>>();
        let empty = ElaboratedInterface::default();
        Some(control.resolve_returns(&self.body.expression(call).ty, self.signatures.unwrap_or(&empty),
            callable, &arguments, self))
    }

    pub(super) fn apply_invocation_control(
        &mut self,
        call: CoreId,
        callable: &invocations::Value,
        arguments: &[invocations::EvaluatedOperand],
        span: Span,
        returned: Option<crate::callable_control::ResolvedReturns<invocations::Value>>,
    ) {
        let reference_shape = match self.body.expression(call).kind.clone() {
            CoreKind::Call { reference_shape, .. } => reference_shape,
            CoreKind::Constant { .. } => {
                let empty = ElaboratedInterface::default();
                let (_, shape) = crate::callable_declarations::value_reference_contract(
                    self.signatures.unwrap_or(&empty), &self.body.expression(call).ty);
                shape
            }
            _ => return,
        };
        let result_ty = self.body.expression(call).ty.clone();
        let Some(control) = self.continuations.invocation(call).cloned() else {
            self.reject_opaque_reference_result(reference_shape, &result_ty, span, "call");
            return;
        };
        let returned = returned.or_else(|| self.resolve_invocation_returns(call, callable, arguments))
            .expect("selected invocation control");
        let arguments = arguments
            .iter()
            .map(|input| input.operand.value.clone())
            .collect::<Vec<_>>();
        if !returned.references.is_complete() {
            self.reject_opaque_reference_result(reference_shape, &result_ty, span, "call");
        }
        let represented_paths = returned.references.paths().map(<[u32]>::to_vec).collect::<Vec<_>>();
        let empty_paths = returned.references.empty_paths().map(<[u32]>::to_vec).collect::<Vec<_>>();
        // Partial observations cannot suppress a normal path or authorize
        // disposal. They can still add positively observed result origins.
        if control.unknown || control.terminal_operation || control.cancellation {
            self.preserve_invocation_returns(call, returned.payloads, &represented_paths, &empty_paths);
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
                        callable,
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
            self.preserve_invocation_returns(call, returned.payloads, &represented_paths, &empty_paths);
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
        represented_paths: &[Vec<u32>],
        empty_paths: &[Vec<u32>],
    ) {
        if returns.is_empty() { return; }
        // The input consumer has already published the declared result.
        // Additional body-derived roots must not mask its lifetime debt.
        let result = Self::result_owner(call);
        let observed = format!("<invocation-return-{}>", call.0);
        for payload in returns {
            self.record_known_payload_origins(&observed, payload, call);
        }
        let snapshots = self.reference_origins.iter()
            .filter(|(key, _)| *key == &observed || key.starts_with(&(observed.clone() + ".")))
            .map(|(key, origins)| (format!("{result}{}", &key[observed.len()..]), origins.clone()))
            .collect::<Vec<_>>();
        for (destination, origins) in snapshots {
            for loan in origins.loans {
                self.install_reference_alias(&destination, loan, call);
            }
        }
        // The shared return relation proves which leaves occur on every
        // normal alternative. It does not prove their storage identities:
        // an unknown input target remains unknown in the projected snapshot.
        for path in represented_paths {
            let source = projection_key(&observed, path);
            let destination = projection_key(&result, path);
            let targets = self.reference_origins.get(&source).and_then(|origins| origins.targets.clone())
                .map(|targets| targets.into_iter().map(|loan| ProjectionLoan {
                    owner: Some(destination.clone()), ..loan
                }).collect());
            let result = self.reference_origins.entry(destination).or_default();
            result.targets = targets;
            result.reference_free = false;
        }
        for path in empty_paths {
            let result = self.reference_origins.entry(projection_key(&result, path)).or_default();
            result.targets = Some(BTreeSet::new());
            result.reference_free = true;
        }
        let logical = self.logical.origins.iter()
            .filter(|(key, _)| *key == &observed || key.starts_with(&(observed.clone() + ".")))
            .map(|(key, regions)| (format!("{result}{}", &key[observed.len()..]), regions.clone()))
            .collect::<Vec<_>>();
        for (key, regions) in logical {
            self.logical.origins.entry(key).or_default().extend(regions);
        }
        let under_observed = |owner: &str| owner == observed || owner.starts_with(&(observed.clone() + "."));
        self.projection_loans.retain(|loan| !loan.owner.as_ref().is_some_and(|owner| under_observed(owner)));
        self.reference_origins.retain(|owner, _| !under_observed(owner));
        // Retain the temporary's ancestry transitively in the installed
        // aliases, but no temporary resident survives result publication.
        let ancestry = self.reborrow_parents.clone();
        for parents in self.reborrow_parents.values_mut() {
            let temporary = parents.iter().filter(|owner| under_observed(owner)).cloned().collect::<Vec<_>>();
            for owner in temporary {
                parents.remove(&owner);
                if let Some(ancestors) = ancestry.get(&owner) { parents.extend(ancestors.iter().cloned()); }
            }
        }
        self.reborrow_parents.retain(|owner, _| !under_observed(owner));
        self.logical.origins.retain(|owner, _| !under_observed(owner));
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
