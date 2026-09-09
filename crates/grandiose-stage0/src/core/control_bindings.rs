//! Validate declared lexical control identities. This checks Core binders and
//! references, not a value/alias analysis: once a continuation is copied or
//! moved into an ordinary binding, later reads use ordinary Core value edges.

use super::*;
use std::collections::{BTreeMap, BTreeSet};

type Scope = BTreeMap<String, (ResumptionId, Type)>;

pub(super) fn validate(body: &TypedBody, diagnostics: &mut Vec<CoreDiagnostic>) {
    if !body.expressions.iter().any(|expression|
        matches!(expression.kind, CoreKind::Handle { .. } | CoreKind::Resumption { .. })) {
        return;
    }
    let mut identities = BTreeMap::new();
    for (index, expression) in body.expressions.iter().enumerate() {
        let CoreKind::Handle { clauses, .. } = &expression.kind else { continue; };
        for (clause_index, clause) in clauses.iter().enumerate() {
            if !matches!(clause.brand, CallableBrand::HandlerClause { handler, .. } if handler == CoreId(index as u32)) {
                error(diagnostics, clause.span, "handler clause identity does not name its enclosing Core handler");
            }
            if let CoreHandlerResumption::Explicit { id, .. } = clause.resumption {
                if identities.insert(id, (index, clause_index)).is_some() {
                    error(diagnostics, clause.span, "distinct handler binders reuse one resumption identity");
                }
                if clause.continuation.is_none() {
                    error(diagnostics, clause.span, "explicit resumption binder has no continuation contract");
                }
            }
        }
    }
    visit(body, body.root, &mut Scope::new(), &mut BTreeSet::new(), &mut BTreeMap::new(), diagnostics);
}

fn error(diagnostics: &mut Vec<CoreDiagnostic>, span: Span, message: &str) {
    diagnostics.push(CoreDiagnostic { code: "G4183", span, message: message.into() });
}

fn visit(body: &TypedBody, id: CoreId, scope: &mut Scope, active: &mut BTreeSet<CoreId>,
    checked: &mut BTreeMap<CoreId, Vec<(Scope, Scope)>>, diagnostics: &mut Vec<CoreDiagnostic>) {
    let Some(expression) = body.expressions.get(id.0 as usize) else { return; };
    if let Some((_, output)) = checked.get(&id).into_iter().flatten().find(|(input, _)| input == scope) {
        *scope = output.clone();
        return;
    }
    if !active.insert(id) {
        error(diagnostics, expression.span, "cyclic Core cannot establish lexical control binding");
        return;
    }
    let input = scope.clone();
    match &expression.kind {
        CoreKind::Resumption { id: identity, name } => {
            if scope.get(name) != Some(&(*identity, expression.ty.clone())) {
                error(diagnostics, expression.span, "resumption use does not match its active lexical binder and contract");
            }
        }
        CoreKind::Let { name, value } => {
            visit(body, *value, scope, active, checked, diagnostics);
            // An alias is an ordinary resident value, not another binder for
            // the generative continuation. Shadowing ends the old spelling.
            scope.remove(name);
        }
        CoreKind::Block(values) => {
            let mut child = scope.clone();
            for value in values { visit(body, *value, &mut child, active, checked, diagnostics); }
        }
        CoreKind::Closure { body: root, .. } => {
            // A resident closure has no ambient handler activation. Pending
            // control fusion must discharge such a dependency explicitly.
            visit(body, *root, &mut Scope::new(), active, checked, diagnostics);
        }
        CoreKind::Handle { computation, clauses } => {
            visit(body, *computation, &mut scope.clone(), active, checked, diagnostics);
            for clause in clauses {
                let mut child = scope.clone();
                for (name, _) in &clause.bindings { child.remove(name); }
                if let CoreHandlerResumption::Explicit { id, name, .. } = &clause.resumption
                    && let Some(contract) = &clause.continuation {
                    child.insert(name.clone(), (*id, contract.callable_type()));
                }
                visit(body, clause.body, &mut child, active, checked, diagnostics);
            }
        }
        CoreKind::Completion { computation, clauses, .. } => {
            visit(body, *computation, &mut scope.clone(), active, checked, diagnostics);
            for clause in clauses {
                let mut child = scope.clone();
                for (name, _) in &clause.bindings { child.remove(name); }
                visit(body, clause.body, &mut child, active, checked, diagnostics);
            }
        }
        _ => for child in core_children(&expression.kind) {
            visit(body, child, scope, active, checked, diagnostics);
        },
    }
    active.remove(&id);
    checked.entry(id).or_default().push((input, scope.clone()));
}
