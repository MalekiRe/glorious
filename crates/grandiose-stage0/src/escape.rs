//! Lifetime escape and outlives validation over frozen Typed Core.
//!
//! [`crate::placeflow::PlaceFlow`] establishes when a loan is live inside a
//! body.  This pass answers the complementary boundary question: may a value
//! that still contains that loan leave the body (or cross a suspension
//! boundary)?  It deliberately works on Typed Core rather than source syntax,
//! so aliases, aggregates, closure environments, handler exits, and
//! completion exits all use the same provenance model.

use crate::{
    core::{
        CallReferenceOrigin, CallReferenceShape, CoreId, CoreKind, CorePlace, EnvironmentBrand,
        TypedBody,
    },
    placeflow::{PlaceFlow, strict_expression_abrupt},
    source::Span,
    types::{EffectRow, GenericArgument, Type},
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EscapeDiagnostic {
    pub code: &'static str,
    pub span: Span,
    pub message: String,
}

/// Frozen diagnostics from the body-outlives boundary.
#[derive(Clone, Debug, Default)]
pub struct EscapeFlow {
    pub diagnostics: Vec<EscapeDiagnostic>,
}

impl EscapeFlow {
    /// Check returned values and suspension payloads. `flow` is intentionally
    /// an input to this phase: its NLL/reborrow facts establish that this is a
    /// post-loan boundary, rather than a second lexical borrow checker.
    pub fn analyze(body: &TypedBody, flow: &PlaceFlow) -> Self {
        let mut analyzer = Analyzer {
            body,
            // A direct borrow must already have entered the ownership flow.
            // Retaining these roots lets us fail closed if Core ever grows a
            // reference-producing operation without teaching PlaceFlow about
            // it first.
            loan_roots: flow
                .events
                .iter()
                .filter_map(|event| match &event.kind {
                    crate::placeflow::FlowEventKind::BorrowShared(root)
                    | crate::placeflow::FlowEventKind::BorrowUnique(root)
                    | crate::placeflow::FlowEventKind::Reborrow(root) => Some(root.clone()),
                    _ => None,
                })
                .collect(),
            values: BTreeMap::new(),
            diagnostics: vec![],
        };
        // Parameters may carry references through structural aggregates. They
        // originate outside this body, but their shape must still be present
        // so a later assignment of `&local` into (for example) `slot.0`
        // replaces that exact projection rather than disappearing from the
        // boundary provenance model.
        for (name, ty) in &body.parameters {
            analyzer.values.insert(name.clone(), parameter_value(ty));
        }
        let root = analyzer.value(body.root);
        analyzer.report_return_escape(&root, body.expression(body.root).span);
        analyzer
            .diagnostics
            .sort_by_key(|diagnostic| diagnostic.span.start);
        analyzer.diagnostics.dedup_by(|left, right| {
            left.code == right.code && left.span == right.span && left.message == right.message
        });
        Self {
            diagnostics: analyzer.diagnostics,
        }
    }
}

/// Provenance that matters at an outlives boundary.  Scalars and normal
/// nominal values are omitted; only borrowed storage and closures that carry
/// one of those borrows can make a body-local region escape.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Value {
    None,
    /// A reference supplied by the caller. It may be returned or carried
    /// across suspension, but can be overwritten by a body-local borrow in
    /// an aggregate projection.
    ExternalBorrowed,
    Borrowed {
        root: String,
    },
    Aggregate(Vec<Value>),
    Closure {
        environment: EnvironmentBrand,
        captures: Vec<Capture>,
    },
    Joined(Vec<Value>),
}

fn parameter_value(ty: &Type) -> Value {
    match ty {
        Type::Reference { .. } => Value::ExternalBorrowed,
        Type::Tuple(values) => Value::Aggregate(values.iter().map(parameter_value).collect()),
        // Array length is not retained in `Type`, and nominal field layouts
        // intentionally remain interface-owned. Preserve the sound subset
        // whose projection layout is explicit in frozen Core.
        Type::Array(_) | Type::Nominal { .. } | Type::Projection { .. } => Value::None,
        Type::Callable { .. }
        | Type::Generic(_)
        | Type::Infer(_)
        | Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Error => Value::None,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Capture {
    /// A reference value whose backing place is body-local.
    Borrowed {
        root: String,
        environment: EnvironmentBrand,
    },
}

struct Analyzer<'a> {
    body: &'a TypedBody,
    loan_roots: BTreeSet<String>,
    values: BTreeMap<String, Value>,
    diagnostics: Vec<EscapeDiagnostic>,
}

impl Analyzer<'_> {
    fn value(&mut self, id: CoreId) -> Value {
        let expression = self.body.expression(id).clone();
        match expression.kind {
            CoreKind::Literal(_)
            | CoreKind::Resumption { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant { .. }
            | CoreKind::Error
            | CoreKind::PatternTest { .. }
            | CoreKind::Unary { .. }
            | CoreKind::Binary { .. } => Value::None,
            CoreKind::Local(name) => self.values.get(&name).cloned().unwrap_or(Value::None),
            CoreKind::Borrow { value, .. } => self.borrowed_value(value),
            CoreKind::Deref(value) => {
                self.value(value);
                Value::None
            }
            CoreKind::Move(value) => self.value(value),
            CoreKind::Tuple(values) | CoreKind::Array(values) => {
                Value::Aggregate(self.strict_values(values))
            }
            CoreKind::Record { fields, .. } | CoreKind::Enum { fields, .. } => {
                Value::Aggregate(self.strict_values(fields))
            }
            CoreKind::Field { base, index, .. } => match self.value(base) {
                Value::Aggregate(fields) => {
                    fields.get(index as usize).cloned().unwrap_or(Value::None)
                }
                Value::Joined(values) => Value::Joined(
                    values
                        .into_iter()
                        .map(|value| match value {
                            Value::Aggregate(fields) => {
                                fields.get(index as usize).cloned().unwrap_or(Value::None)
                            }
                            _ => Value::None,
                        })
                        .collect(),
                ),
                _ => Value::None,
            },
            CoreKind::Let { name, value } => {
                let evaluated = self.value(value);
                if strict_expression_abrupt(self.body, value) {
                    return Value::None;
                }
                self.values.insert(name, evaluated);
                Value::None
            }
            CoreKind::Label { body, .. } | CoreKind::Transfer { value: body, .. } => {
                self.value(body)
            }
            CoreKind::Assign { place, value } => {
                let evaluated = self.value(value);
                if strict_expression_abrupt(self.body, value) {
                    return Value::None;
                }
                self.assign(place, evaluated, expression.span);
                Value::None
            }
            CoreKind::Block(values) => {
                let mut result = Value::None;
                for value in values {
                    result = self.value(value);
                    if strict_expression_abrupt(self.body, value) {
                        break;
                    }
                }
                result
            }
            CoreKind::Closure {
                callable,
                environment,
                ..
            } => {
                let runs_in_matches = environment.runs_in.sealed
                    && environment.runs_in.environment == environment.brand
                    && environment.runs_in.callable == callable
                    && environment.runs_in.post_states == environment.post_states
                    && matches!(
                        &expression.ty,
                        Type::Callable { effects, .. } if environment.runs_in.effects == *effects
                    );
                if !runs_in_matches {
                    self.error(
                        expression.span,
                        "G5014",
                        "closure with invalid RunsIn evidence cannot cross an escape boundary",
                    );
                    return Value::None;
                }
                Value::Closure {
                    environment: environment.brand,
                    captures: environment
                        .captures
                        .into_iter()
                        .flat_map(|capture| {
                            let value = self
                                .values
                                .get(&capture.name)
                                .cloned()
                                .unwrap_or(Value::None);
                            // Moving a reference into a callable changes the
                            // owner of the reference slot, not the provenance of
                            // its backing place.  Treat move captures exactly as
                            // borrowed captures at this outlives boundary: a
                            // returned callable, aggregate, or effect payload
                            // must still carry every backing root.  PlaceFlow
                            // separately records the move/reborrow and keeps the
                            // loan live for the callable environment.
                            borrowed_roots(&value)
                                .into_iter()
                                .map(|root| Capture::Borrowed {
                                    root,
                                    environment: environment.brand,
                                })
                                .collect::<Vec<_>>()
                        })
                        .collect(),
                }
            }
            CoreKind::Call {
                callee,
                arguments,
                reference_origin,
                reference_shape,
                ..
            } => {
                // A call result is a boundary value in its own right. The
                // frozen Core contract names the caller argument whose region
                // it forwards, so relaying `&local` through a helper cannot
                // erase a later return/suspension/drop-check obligation.
                self.value(callee);
                if strict_expression_abrupt(self.body, callee) {
                    return Value::None;
                }
                let values = self.strict_values(arguments);
                if strict_expression_abrupt(self.body, id) {
                    return Value::None;
                }
                self.reference_result_value(
                    &reference_origin,
                    reference_shape,
                    &expression.ty,
                    values,
                    expression.span,
                    "call",
                )
            }
            CoreKind::Perform { .. } => self
                .performed_value(id)
                .map(|(_, _, _, value)| value)
                .unwrap_or(Value::None),
            CoreKind::Handle {
                computation,
                clauses,
            } => {
                // Capture the evaluated payload once, before the dynamic arm
                // split.  This gives every matching handler binder the exact
                // borrowed/external value that crossed the suspension rather
                // than re-evaluating argument Core in each arm.
                let performed = self.performed_value(computation);
                let computation = performed
                    .as_ref()
                    .map(|(_, _, _, value)| value.clone())
                    .unwrap_or_else(|| self.value(computation));
                let incoming = self.values.clone();
                // A handler may complete normally without selecting an
                // operation arm, so the computation is one of its dynamic
                // exits alongside every matching clause.
                let mut exits = vec![computation.clone()];
                for clause in clauses {
                    self.values = incoming.clone();
                    if let Some((effect, operation, payloads, _)) = &performed
                        && *effect == clause.effect
                        && *operation == clause.operation
                    {
                        for (pattern, payload) in clause.patterns.iter().zip(payloads) {
                            self.bind_pattern_value(pattern, payload.clone());
                        }
                    } else {
                        for (name, _) in &clause.bindings {
                            self.values.remove(name);
                        }
                    }
                    if let crate::core::CoreHandlerResumption::Explicit { name, .. } =
                        clause.resumption
                    {
                        self.values.remove(&name);
                    }
                    exits.push(self.value(clause.body));
                }
                self.values = incoming;
                join(exits)
            }
            CoreKind::Completion {
                computation,
                clauses,
            } => {
                let computation = self.value(computation);
                let incoming = self.values.clone();
                let mut exits = vec![computation.clone()];
                for clause in clauses {
                    self.values = incoming.clone();
                    self.bind_pattern_value(&clause.pattern, computation.clone());
                    // A boolean completion pattern alone cannot carry a
                    // reference, but a positive refinement can.  Its subject
                    // and projection plan are frozen Core facts, so bind it
                    // from the original aggregate rather than treating the
                    // arm-local name as an unconstrained scalar.  This keeps
                    // aggregate references visible at both return and effect
                    // suspension boundaries.
                    if let Some(refinement) = &clause.refinement {
                        let subject = self.value(refinement.subject);
                        self.bind_pattern_value(&refinement.pattern, subject);
                    }
                    exits.push(self.value(clause.body));
                }
                self.values = incoming;
                join(exits)
            }
        }
    }

    /// Reconstruct the escaped value shape from the same immutable region map
    /// used by the place flow.  Both function calls and performed operations
    /// are callable boundaries; keeping this single implementation prevents a
    /// handled/resumed effect result from dropping a body-local borrow.
    fn reference_result_value(
        &mut self,
        origin: &CallReferenceOrigin,
        shape: CallReferenceShape,
        result_ty: &Type,
        values: Vec<Value>,
        span: Span,
        boundary: &str,
    ) -> Value {
        match origin {
            CallReferenceOrigin::None => Value::None,
            CallReferenceOrigin::External => Value::ExternalBorrowed,
            CallReferenceOrigin::Paths(paths) => {
                let mut result = Value::None;
                for path in paths {
                    let Some(argument) = values.get(path.argument as usize) else {
                        self.error(
                            span,
                            "G5023",
                            format!("reference-valued {boundary} names an argument outside its frozen arity"),
                        );
                        continue;
                    };
                    let Some(value) = value_at_path(argument, &path.argument_fields) else {
                        self.error(
                            span,
                            "G5023",
                            format!("reference-valued {boundary} forwards an argument without structural provenance"),
                        );
                        continue;
                    };
                    if !put_value_at_path(&mut result, &path.result_fields, value) {
                        self.error(
                            span,
                            "G5023",
                            format!(
                                "reference-valued {boundary} has contradictory frozen result paths"
                            ),
                        );
                    }
                }
                result
            }
            CallReferenceOrigin::Opaque => {
                if matches!(shape, CallReferenceShape::OpaquePotentiallyReference)
                    && !contains_open_type_parameter(result_ty)
                {
                    self.error(
                        span,
                        "G5023",
                        format!(
                            "reference-valued {boundary} has no frozen caller-region provenance"
                        ),
                    );
                }
                Value::None
            }
        }
    }

    /// Evaluate strict children in source order through their first abrupt
    /// exit.  The predicate comes from PlaceFlow's shared control classifier,
    /// so unreachable aggregate fields and arguments cannot publish later
    /// reference-escape facts.
    fn strict_values(&mut self, values: Vec<CoreId>) -> Vec<Value> {
        let mut evaluated = Vec::with_capacity(values.len());
        for value in values {
            evaluated.push(self.value(value));
            if strict_expression_abrupt(self.body, value) {
                break;
            }
        }
        evaluated
    }

    /// Evaluate a direct operation exactly once and retain both its payload
    /// values and frozen result provenance for the enclosing handler.
    fn performed_value(
        &mut self,
        id: CoreId,
    ) -> Option<(crate::EffectInstance, u32, Vec<Value>, Value)> {
        let expression = self.body.expression(id).clone();
        let CoreKind::Perform {
            effect,
            operation,
            arguments,
            reference_origin,
            reference_shape,
            ..
        } = expression.kind
        else {
            return None;
        };
        let values = self.strict_values(arguments);
        if strict_expression_abrupt(self.body, id) {
            return None;
        }
        for value in &values {
            self.report_suspension_escape(value, expression.span);
        }
        let result = self.reference_result_value(
            &reference_origin,
            reference_shape,
            &expression.ty,
            values.clone(),
            expression.span,
            "effect operation",
        );
        Some((effect, operation, values, result))
    }

    fn bind_pattern_value(&mut self, pattern: &crate::core::CorePattern, value: Value) {
        match pattern {
            crate::core::CorePattern::Bind { name } => {
                self.values.insert(name.clone(), value);
            }
            crate::core::CorePattern::Tuple(patterns) => {
                for (index, pattern) in patterns.iter().enumerate() {
                    let child = value_at_path(&value, &[index as u32]).unwrap_or(Value::None);
                    self.bind_pattern_value(pattern, child);
                }
            }
            crate::core::CorePattern::Array { elements, .. } => {
                for (index, pattern) in elements.iter().enumerate() {
                    let child = value_at_path(&value, &[index as u32]).unwrap_or(Value::None);
                    self.bind_pattern_value(pattern, child);
                }
            }
            crate::core::CorePattern::Record { fields, .. }
            | crate::core::CorePattern::Enum { fields, .. } => {
                for field in fields {
                    let child = value_at_path(&value, &[field.index]).unwrap_or(Value::None);
                    self.bind_pattern_value(&field.pattern, child);
                }
            }
            crate::core::CorePattern::Any
            | crate::core::CorePattern::Literal(_)
            | crate::core::CorePattern::Error => {}
        }
    }

    fn borrowed_value(&mut self, id: CoreId) -> Value {
        // Reborrowing through a reference supplied by the caller must remain
        // caller-owned.  `place_root` intentionally has no body-local root
        // for `&*external`; treating that absence as a temporary would reject
        // a valid reborrow merely because the reference first travelled
        // through an enum/array/refinement aggregate.
        let external_reborrow = match self.body.expression(id).kind.clone() {
            CoreKind::Deref(reference) => {
                matches!(self.value(reference), Value::ExternalBorrowed)
            }
            _ => false,
        };
        let Some(root) = self.place_root(id) else {
            if external_reborrow {
                return Value::ExternalBorrowed;
            }
            self.error(
                self.body.expression(id).span,
                "G5013",
                "reference to a temporary cannot outlive the body that created it",
            );
            return Value::None;
        };
        // Every Core borrow of a stable place should have a matching
        // PlaceFlow event. Keep this fail-closed until a future region source
        // explicitly teaches both passes about a new kind of loan.
        if !self.loan_roots.contains(&root) {
            self.error(
                self.body.expression(id).span,
                "G5016",
                format!("reference to `{root}` has no frozen NLL loan fact"),
            );
        }
        Value::Borrowed { root }
    }

    fn place_root(&mut self, id: CoreId) -> Option<String> {
        match &self.body.expression(id).kind {
            CoreKind::Local(name) => Some(name.clone()),
            CoreKind::Field { base, .. } => self.place_root(*base),
            // Reborrowing `&*parent` retains the parent loan's origin; the
            // dereference is a place projection, not a body-local temporary.
            CoreKind::Deref(reference) => match &self.body.expression(*reference).kind {
                CoreKind::Local(_) | CoreKind::Field { .. } => {
                    let value = self.value(*reference);
                    let mut roots = borrowed_roots(&value).into_iter();
                    let root = roots.next()?;
                    roots.next().is_none().then_some(root)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn assign(&mut self, place: CorePlace, value: Value, span: Span) {
        if self.place_targets_external_storage(&place) {
            self.report_external_store_escape(&value, span);
        }
        match place {
            CorePlace::Local { name, .. } => {
                self.values.insert(name, value);
            }
            CorePlace::Field { ref base, .. } => {
                if let Some(name) = base.root_local().map(|(name, _)| name.to_owned()) {
                    let entry = self.values.entry(name).or_insert(Value::None);
                    let mut path = vec![];
                    collect_field_path(&place, &mut path);
                    if !assign_field_path(entry, &path, value) {
                        self.error(
                            span,
                            "G5021",
                            "aggregate projection assignment has no sealed structural provenance path",
                        );
                    }
                }
            }
            CorePlace::Deref { reference, .. } => {
                self.value(reference);
            }
            CorePlace::Error => {}
        }
    }

    /// Whether this assignment reaches storage supplied by the caller. Field
    /// projections preserve their base, so `slot.field = &local` must carry
    /// the same destruction/outlives obligation as `*slot = &local`.
    fn place_targets_external_storage(&mut self, place: &CorePlace) -> bool {
        match place {
            CorePlace::Local { .. } | CorePlace::Error => false,
            CorePlace::Field { base, .. } => self.place_targets_external_storage(base),
            CorePlace::Deref { reference, .. } => {
                value_contains_external_reference(&self.value(*reference))
            }
        }
    }

    fn report_return_escape(&mut self, value: &Value, span: Span) {
        let mut emitted = BTreeSet::new();
        for root in borrowed_roots(value) {
            if emitted.insert(("reference", root.clone())) {
                self.error(
                    span,
                    "G5013",
                    format!(
                        "reference backed by body-local place `{root}` escapes the function result"
                    ),
                );
            }
        }
        for capture in closure_captures(value) {
            let (code, message) = match capture {
                Capture::Borrowed { root, environment } => (
                    "G5014",
                    format!(
                        "escaping closure environment {:?} captures a reference backed by body-local place `{root}`",
                        environment
                    ),
                ),
            };
            if emitted.insert(("closure", message.clone())) {
                self.error(span, code, message);
            }
        }
    }

    fn report_suspension_escape(&mut self, value: &Value, span: Span) {
        for root in borrowed_roots(value) {
            self.error(
                span,
                "G5015",
                format!("effect payload carries reference to body-local place `{root}` across a suspension boundary"),
            );
        }
        for Capture::Borrowed { root, environment } in closure_captures(value) {
            self.error(
                span,
                "G5015",
                format!("effect payload carries closure environment {environment:?} borrowing body-local place `{root}` across a suspension boundary"),
            );
        }
    }

    fn report_external_store_escape(&mut self, value: &Value, span: Span) {
        let mut emitted = BTreeSet::new();
        for root in borrowed_roots(value) {
            if emitted.insert(("reference", root.clone())) {
                self.error(
                    span,
                    "G5022",
                    format!(
                        "assignment through caller-owned reference stores a borrow of body-local place `{root}` past this body's destruction"
                    ),
                );
            }
        }
        for Capture::Borrowed { root, environment } in closure_captures(value) {
            let message = format!(
                "assignment through caller-owned reference stores closure environment {environment:?} borrowing body-local place `{root}` past this body's destruction"
            );
            if emitted.insert(("closure", message.clone())) {
                self.error(span, "G5022", message);
            }
        }
    }

    fn error(&mut self, span: Span, code: &'static str, message: impl Into<String>) {
        self.diagnostics.push(EscapeDiagnostic {
            code,
            span,
            message: message.into(),
        });
    }
}

/// Extract outer-to-inner structural projections from frozen Core. Unlike a
/// source spelling, every segment carries a checked layout arity.
fn collect_field_path(place: &CorePlace, path: &mut Vec<(u32, u32)>) {
    if let CorePlace::Field {
        base,
        index,
        field_count,
        ..
    } = place
    {
        collect_field_path(base, path);
        path.push((*index, *field_count));
    }
}

/// Materialize only the structural shells proved by Core and replace the
/// terminal projection. Any contradiction with an existing aggregate shape
/// is rejected instead of erasing a body-local borrow from escape analysis.
fn assign_field_path(value: &mut Value, path: &[(u32, u32)], replacement: Value) -> bool {
    let mut current = value;
    for (position, (index, field_count)) in path.iter().enumerate() {
        if *index >= *field_count {
            return false;
        }
        if matches!(current, Value::None) {
            *current = Value::Aggregate(vec![Value::None; *field_count as usize]);
        }
        let Value::Aggregate(fields) = current else {
            return false;
        };
        if fields.len() != *field_count as usize {
            return false;
        }
        let field = &mut fields[*index as usize];
        if position + 1 == path.len() {
            *field = replacement;
            return true;
        }
        current = field;
    }
    false
}

fn value_at_path(value: &Value, path: &[u32]) -> Option<Value> {
    let mut value = value;
    for field in path {
        let Value::Aggregate(fields) = value else {
            return None;
        };
        value = fields.get(*field as usize)?;
    }
    Some(value.clone())
}

fn put_value_at_path(target: &mut Value, path: &[u32], replacement: Value) -> bool {
    if path.is_empty() {
        if !matches!(target, Value::None) {
            return false;
        }
        *target = replacement;
        return true;
    }
    let required = path[0] as usize + 1;
    if matches!(target, Value::None) {
        *target = Value::Aggregate(vec![Value::None; required]);
    }
    let Value::Aggregate(fields) = target else {
        return false;
    };
    if fields.len() < required {
        fields.resize(required, Value::None);
    }
    put_value_at_path(&mut fields[path[0] as usize], &path[1..], replacement)
}

fn join(mut values: Vec<Value>) -> Value {
    match values.len() {
        0 => Value::None,
        1 => values.pop().expect("one value"),
        _ => Value::Joined(values),
    }
}

fn borrowed_roots(value: &Value) -> BTreeSet<String> {
    let mut roots = BTreeSet::new();
    collect_borrowed_roots(value, &mut roots);
    roots
}

fn collect_borrowed_roots(value: &Value, roots: &mut BTreeSet<String>) {
    match value {
        Value::Borrowed { root } => {
            roots.insert(root.clone());
        }
        Value::Aggregate(values) | Value::Joined(values) => {
            for value in values {
                collect_borrowed_roots(value, roots);
            }
        }
        Value::Closure { .. } | Value::None | Value::ExternalBorrowed => {}
    }
}

/// See the matching PlaceFlow helper. An open type parameter is checked at
/// the concrete instantiation boundary; it cannot by itself identify a
/// body-local backing place in this generic declaration.
fn contains_open_type_parameter(value: &Type) -> bool {
    match value {
        Type::Generic(_) => true,
        Type::Tuple(values) => values.iter().any(contains_open_type_parameter),
        Type::Array(value)
        | Type::Reference {
            referent: value, ..
        } => contains_open_type_parameter(value),
        Type::Nominal { arguments, .. } => arguments
            .iter()
            .any(generic_argument_contains_open_type_parameter),
        Type::Callable {
            parameters, result, ..
        } => {
            parameters.iter().any(contains_open_type_parameter)
                || contains_open_type_parameter(result)
        }
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            contains_open_type_parameter(subject)
                || trait_arguments
                    .iter()
                    .any(generic_argument_contains_open_type_parameter)
                || item_arguments
                    .iter()
                    .any(generic_argument_contains_open_type_parameter)
        }
        Type::Infer(_)
        | Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Error => false,
    }
}

fn generic_argument_contains_open_type_parameter(value: &GenericArgument) -> bool {
    match value {
        GenericArgument::Type(value) => contains_open_type_parameter(value),
        GenericArgument::EffectRow(row) => effect_row_contains_open_type_parameter(row),
        GenericArgument::ConstProjection {
            subject,
            trait_arguments,
            ..
        } => {
            contains_open_type_parameter(subject)
                || trait_arguments
                    .iter()
                    .any(generic_argument_contains_open_type_parameter)
        }
        GenericArgument::Lifetime(_)
        | GenericArgument::ConstU32(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstU32Expr(_)
        | GenericArgument::ConstInfer { .. } => false,
    }
}

fn effect_row_contains_open_type_parameter(row: &EffectRow) -> bool {
    row.effects.iter().any(|effect| {
        effect
            .arguments
            .iter()
            .any(generic_argument_contains_open_type_parameter)
    }) || row.projections.iter().any(|projection| {
        contains_open_type_parameter(&projection.subject)
            || projection
                .trait_arguments
                .iter()
                .any(generic_argument_contains_open_type_parameter)
            || projection
                .item_arguments
                .iter()
                .any(generic_argument_contains_open_type_parameter)
    })
}

/// A reference coming from a parameter may name caller-owned storage. Joins
/// are conservative: if any dynamic predecessor exposes external storage, a
/// body-local borrow cannot safely be written through the merged receiver.
fn value_contains_external_reference(value: &Value) -> bool {
    match value {
        Value::ExternalBorrowed => true,
        Value::Aggregate(values) | Value::Joined(values) => {
            values.iter().any(value_contains_external_reference)
        }
        Value::None | Value::Borrowed { .. } | Value::Closure { .. } => false,
    }
}

fn closure_captures(value: &Value) -> Vec<Capture> {
    let mut captures = vec![];
    collect_closure_captures(value, &mut captures);
    captures.sort_by_key(|capture| format!("{capture:?}"));
    captures.dedup();
    captures
}

fn collect_closure_captures(value: &Value, captures: &mut Vec<Capture>) {
    match value {
        Value::Closure {
            captures: values, ..
        } => captures.extend(values.clone()),
        Value::Aggregate(values) | Value::Joined(values) => {
            for value in values {
                collect_closure_captures(value, captures);
            }
        }
        Value::None | Value::ExternalBorrowed | Value::Borrowed { .. } => {}
    }
}
