//! Mandatory transfer admission is a semantic proof, not an optimizer hint.
use super::*;

impl Elaborator<'_> {
    pub(super) fn tail_call(&mut self, call: ExprId, expected: Option<Type>, span: Span) -> CoreId {
        let call = self.expression_expected(call, expected);
        let CoreKind::Call {
            callee, ..
        } = self.expressions[call.0 as usize].kind.clone()
        else {
            return self.fail(span, "G4400", "mandatory `tail` requires a callable invocation, not a constructor or machine operation");
        };
        if !matches!(
            self.expressions[callee.0 as usize].kind,
            CoreKind::Function {
                host_import: None,
                ..
            } | CoreKind::TraitMethod { .. }
        ) {
            self.error(span, "G4404", "mandatory `tail` has no proven transfer convention for this receiver or external ABI");
        }
        // Transfer provenance depends on evaluated values, not just their
        // types. EscapeFlow checks the frozen call after NLL, including
        // incoming borrows, aggregate assignments, and branch joins.
        if let CoreKind::Call { mandatory_tail, .. } = &mut self.expressions[call.0 as usize].kind {
            *mandatory_tail = true;
        }
        self.expressions[call.0 as usize].span = span;
        call
    }
}

// This is deliberately a structural proof. Unknown generic/opaque residents
// need a provenance proof; absence of a visible Reference node is not one.
pub(crate) fn tail_owned_type(
    signatures: &ElaboratedInterface,
    ty: &Type,
    active: &mut Vec<(DefKey, Vec<GenericArgument>)>,
) -> bool {
    match ty {
        Type::Unit | Type::Scalar(_) | Type::ConstInteger(_) | Type::ConstQuantity(_) => true,
        Type::Tuple(fields) => fields
            .iter()
            .all(|field| tail_owned_type(signatures, field, active)),
        Type::Array(element) | Type::FixedArray { element, .. } | Type::StaticData { element, .. } => {
            tail_owned_type(signatures, element, active)
        }
        Type::Nominal {
            definition,
            arguments,
        } => {
            let key = (*definition, arguments.clone());
            if active.contains(&key) {
                return true;
            }
            // A recursive generic definition can expand without repeating a
            // concrete instance. Exhausted structural proof is not admission.
            if active.len() >= 128 {
                return false;
            }
            active.push(key);
            let safe = match signatures.definitions.get(definition) {
                Some(ElaboratedHeader::Nominal { layout, .. }) => {
                    crate::mir::instantiate_nominal_copy_layout(layout, arguments).is_some_and(
                        |variants| {
                            variants
                                .iter()
                                .flatten()
                                .all(|field| tail_owned_type(signatures, field, active))
                        },
                    )
                }
                _ => false,
            };
            active.pop();
            safe
        }
        _ => false,
    }
}

/// Lexical control captures are not ordinary captured locals. An empty
/// closure environment therefore does not prove that its code is independent
/// of the activation that created it. Labels introduced by the invocation
/// itself are harmless; a reference to any other brand retains its owner.
pub(crate) fn has_outer_label_dependency(body: &TypedBody, root: CoreId) -> bool {
    let mut declared = std::collections::BTreeSet::new();
    let mut referenced = std::collections::BTreeSet::new();
    let mut seen = std::collections::BTreeSet::new();
    let mut pending = vec![root];
    while let Some(id) = pending.pop() {
        if !seen.insert(id) { continue; }
        let Some(expression) = body.expressions.get(id.0 as usize) else { return true; };
        match expression.kind {
            CoreKind::Label { brand, .. } => { declared.insert(brand); }
            CoreKind::LabelValue { brand } | CoreKind::Transfer { brand, .. } => { referenced.insert(brand); }
            _ => {}
        }
        pending.extend(core_children(&expression.kind));
    }
    !referenced.is_subset(&declared)
}

impl TypedBody {
    pub(super) fn validate_mandatory_tails(&self, diagnostics: &mut Vec<CoreDiagnostic>) {
        if !self.expressions.iter().any(|expression| {
            matches!(
                expression.kind,
                CoreKind::Call {
                    mandatory_tail: true,
                    ..
                }
            )
        }) {
            return;
        }
        // Context is part of the traversal key: sharing an expression cannot
        // authorize a non-tail use from a different, valid tail occurrence.
        let mut seen = std::collections::BTreeSet::new();
        let mut pending = vec![(self.root, true, false, self.root)];
        while let Some((id, final_position, retained_control, result)) = pending.pop() {
            if !seen.insert((id, final_position, retained_control, result)) {
                continue;
            }
            let Some(expression) = self.expressions.get(id.0 as usize) else {
                continue;
            };
            if let CoreKind::Call {
                mandatory_tail: true,
                callee,
                ..
            } = &expression.kind
            {
                let blocking = if !final_position {
                    Some((
                        "G4401",
                        "mandatory `tail` has reachable following work or a required result transformation",
                    ))
                } else if retained_control {
                    Some((
                        "G4402",
                        "mandatory `tail` retains an active label, handler, or captured environment without a discharge/fusion proof",
                    ))
                } else if self
                    .expressions
                    .get(result.0 as usize)
                    .is_none_or(|root| root.ty != expression.ty)
                {
                    Some((
                        "G4405",
                        "mandatory `tail` result does not match the current activation's result destination",
                    ))
                } else if self
                    .expressions
                    .get(callee.0 as usize)
                    .is_none_or(|callee| {
                        !matches!(
                            callee.kind,
                            CoreKind::Function {
                                host_import: None,
                                ..
                            } | CoreKind::TraitMethod { .. }
                        )
                    })
                {
                    Some((
                        "G4404",
                        "mandatory `tail` receiver has no proven activation-transfer ABI",
                    ))
                } else {
                    None
                };
                if let Some((code, message)) = blocking {
                    diagnostics.push(CoreDiagnostic {
                        code,
                        span: expression.span,
                        message: message.into(),
                    });
                }
            }
            match &expression.kind {
                CoreKind::Block(values) => {
                    for (index, value) in values.iter().enumerate() {
                        pending.push((
                            *value,
                            final_position && index + 1 == values.len(),
                            retained_control,
                            result,
                        ));
                    }
                }
                CoreKind::Closure {
                    body, environment, ..
                } => {
                    pending.push((*body, true, !environment.captures.is_empty()
                        || has_outer_label_dependency(self, *body), *body));
                }
                CoreKind::Completion {
                    computation,
                    clauses,
                    handles_operations,
                    ..
                } => {
                    pending.push((*computation, false, retained_control, result));
                    for clause in clauses {
                        pending.push((
                            clause.body,
                            final_position,
                            retained_control || *handles_operations,
                            result,
                        ));
                    }
                }
                CoreKind::Label { body, .. } => {
                    // A final lexical label is only a result rejoin, not a
                    // retained handler or continuation. The transfer already
                    // proves the activation result type, ends the complete
                    // source-storage scope, and never returns to this rejoin.
                    // EscapeFlow separately proves that no transferred value
                    // carries the label capability (including in a closure).
                    pending.push((*body, final_position, retained_control, result));
                }
                CoreKind::Handle { .. } => {
                    pending.extend(
                        core_children(&expression.kind)
                            .into_iter()
                            .map(|child| (child, final_position, true, result)),
                    );
                }
                _ => pending.extend(
                    core_children(&expression.kind)
                        .into_iter()
                        .map(|child| (child, false, retained_control, result)),
                ),
            }
        }
    }
}
