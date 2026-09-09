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
        Self::analyze_with_interface(body, flow, &crate::ElaboratedInterface::default())
    }

    /// Layouts establish frame independence for owned nominal residents;
    /// value provenance establishes it for incoming borrowed residents.
    pub fn analyze_with_interface(
        body: &TypedBody, flow: &PlaceFlow, signatures: &crate::ElaboratedInterface,
    ) -> Self {
        let mut analyzer = Analyzer {
            body,
            signatures,
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
            values: ValueEnvironment::default(),
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
    /// Proven resident without any frame-relative component. Unlike `None`,
    /// this is positive transfer evidence, never absence of a known loan.
    FrameIndependent,
    /// A reference supplied by the caller. It may be returned or carried
    /// across suspension, but can be overwritten by a body-local borrow in
    /// an aggregate projection.
    ExternalBorrowed,
    Borrowed {
        root: String,
        storage: Option<u64>,
        fields: Vec<u32>,
    },
    Aggregate(Vec<Value>),
    /// A call's homogeneous array result keeps one reference relation per
    /// element shape, plus only the concretely overwritten resident slots.
    Array {
        length: Option<u64>,
        element: Box<Value>,
        fields: BTreeMap<u32, Value>,
    },
    /// A known constructor may lack a resident path present in another
    /// variant. That absence is not unknown reference provenance.
    Variant(Vec<Value>),
    Closure {
        environment: EnvironmentBrand,
        captures: Vec<Capture>,
        frame_independent: bool,
    },
    Joined(Vec<Value>),
}

/// A reference targets a storage identity, not the latest binding with the
/// same source spelling. Keep retired residents available when a short-lived
/// carrier is shadowed or leaves scope, so reading one of its stored caller
/// references cannot silently select the replacement binding's provenance.
#[derive(Clone, Default)]
struct ValueEnvironment {
    bindings: BTreeMap<String, u64>,
    residents: BTreeMap<u64, Value>,
    next: u64,
}

impl ValueEnvironment {
    fn define(&mut self, name: String, value: Value) {
        let identity = self.next;
        self.next += 1;
        self.bindings.insert(name, identity);
        self.residents.insert(identity, value);
    }
    fn insert(&mut self, name: String, value: Value) {
        if let Some(identity) = self.bindings.get(&name) {
            self.residents.insert(*identity, value);
        } else { self.define(name, value); }
    }
    fn get(&self, name: &str) -> Option<&Value> {
        self.residents.get(self.bindings.get(name)?)
    }
    fn get_mut(&mut self, name: &str) -> Option<&mut Value> {
        self.residents.get_mut(self.bindings.get(name)?)
    }
    fn remove(&mut self, name: &str) { self.bindings.remove(name); }
}

fn parameter_value(ty: &Type) -> Value {
    match ty {
        Type::Reference { .. } => Value::ExternalBorrowed,
        Type::Tuple(values) => Value::Aggregate(values.iter().map(parameter_value).collect()),
        // Nominal layouts are interface-owned and cannot be reopened here,
        // but every reference nested in a parameter still originates outside
        // the callee. Treat the opaque parameter as an external structural
        // carrier; frozen path forwarding can then retain that fact without
        // inventing a body-local loan (for example `Str -> Result<Str, E>`).
        Type::Nominal { .. } | Type::Projection { .. } => Value::ExternalBorrowed,
        // Homogeneous products retain external provenance without expanding
        // potentially enormous element counts into analysis metadata.
        Type::Array(_) | Type::FixedArray { .. } | Type::StaticData { .. } | Type::RawPointer { .. } => Value::ExternalBorrowed,
        Type::Callable { .. }
        | Type::Generic(_)
        | Type::Infer(_)
        | Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstInteger(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Error => Value::FrameIndependent,
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
    signatures: &'a crate::ElaboratedInterface,
    loan_roots: BTreeSet<String>,
    values: ValueEnvironment,
    diagnostics: Vec<EscapeDiagnostic>,
}

impl Analyzer<'_> {
    fn value(&mut self, id: CoreId) -> Value {
        let expression = self.body.expression(id).clone();
        let value = match expression.kind {
            CoreKind::ConstValue(_) => Value::None,
            CoreKind::Literal(_)
            | CoreKind::Resumption { .. }
            | CoreKind::LabelValue { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant { .. }
            | CoreKind::Error
            | CoreKind::PatternTest { .. }
            | CoreKind::IntrinsicCall { .. } => Value::None,
            CoreKind::Local(name) => self.values.get(&name).cloned().unwrap_or(Value::None),
            CoreKind::Borrow { value, .. } if strict_expression_abrupt(self.body, value) => {
                self.value(value);
                Value::None
            }
            CoreKind::Borrow { value, .. } => {
                let base = crate::placeflow::borrowed_place_base(self.body, value);
                if self.has_frozen_loan_root(&crate::placeflow::borrowed_temporary_root(base)) {
                    // Borrowing does not skip the rvalue's strict evaluation:
                    // nested calls, assignments and suspension still occur.
                    let resident = self.value(base);
                    self.values.insert(crate::placeflow::borrowed_temporary_root(base), resident);
                }
                self.borrowed_value(value)
            }
            CoreKind::Deref(value) => {
                // Loading an incoming reference-bearing value preserves its
                // caller-owned reference leaves. Do not fabricate external
                // provenance for a local/unknown reference: those require a
                // structural account of the referenced storage.
                let value = self.value(value);
                self.reference_path_value(&value, &[crate::core::REFERENCE_PATH_DEREF]).unwrap_or(Value::None)
            }
            CoreKind::Move(value) => self.value(value),
            CoreKind::ReleaseAvailable(value) => {
                self.value(value);
                Value::None
            }
            CoreKind::Tuple(values) | CoreKind::Array(values) => {
                Value::Aggregate(self.strict_values(values))
            }
            CoreKind::Record { fields, .. } => {
                Value::Aggregate(self.strict_values(fields))
            }
            CoreKind::Enum { fields, .. } => Value::Variant(self.strict_values(fields)),
            CoreKind::Field { base, index, .. } =>
                value_at_path(&self.value(base), &[index]).unwrap_or(Value::None),
            CoreKind::Let { name, value } => {
                let evaluated = self.value(value);
                if strict_expression_abrupt(self.body, value) {
                    return Value::None;
                }
                self.values.define(name, evaluated);
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
                let incoming = self.values.clone();
                let mut bindings = BTreeSet::new();
                let mut result = Value::None;
                for value in values {
                    if let CoreKind::Let { name, .. } = &self.body.expression(value).kind {
                        bindings.insert(name.clone());
                    }
                    result = self.value(value);
                    if strict_expression_abrupt(self.body, value) {
                        break;
                    }
                }
                restore_bindings(&mut self.values, &incoming, bindings);
                result
            }
            CoreKind::Closure {
                callable,
                parameters,
                environment,
                body,
            } => {
                let runs_in_matches = environment.runs_in.sealed
                    && environment.runs_in.environment == environment.brand
                    && environment.runs_in.callable == callable
                    && environment.runs_in.post_states == environment.post_states
                    && matches!(
                        &expression.ty,
                        Type::Callable { lifetime_binders, effects, .. }
                            if environment.runs_in.effects
                                == if *lifetime_binders == 0 {
                                    effects.clone()
                                } else {
                                    crate::core::open_hrtb_callable_body_effect_row(
                                        effects.clone(),
                                        0,
                                    )
                                }
                    );
                if !runs_in_matches {
                    self.error(
                        expression.span,
                        "G5014",
                        "closure with invalid RunsIn evidence cannot cross an escape boundary",
                    );
                    return Value::None;
                }
                // A closure can create its escaping borrow only when it is
                // invoked: `() -> &i64 { callback(&local) }` captures the
                // local *place*, not an already-borrowed value.  Evaluate
                // the frozen body in an isolated invocation environment to
                // retain that result provenance without leaking its local
                // bindings or writes into the enclosing creation site.
                let outer_values = self.values.clone();
                for (name, ty) in &parameters {
                    self.values.define(name.clone(), parameter_value(ty));
                }
                let returned = self.value(body);
                self.values = outer_values;

                let frame_independent = borrowed_roots(&returned).is_empty()
                    && !crate::core::tail::has_outer_label_dependency(self.body, body)
                    && environment.captures.iter().all(|capture| {
                        matches!(capture.mode, crate::core::CaptureMode::Copy | crate::core::CaptureMode::Move)
                            && self.values.get(&capture.name).is_some_and(frame_independent_value)
                    });
                let mut captures = environment
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
                    .collect::<Vec<_>>();
                captures.extend(borrowed_roots(&returned).into_iter().map(|root| {
                    Capture::Borrowed {
                        root,
                        environment: environment.brand,
                    }
                }));
                captures.sort_by_key(|capture| format!("{capture:?}"));
                captures.dedup();
                Value::Closure {
                    environment: environment.brand,
                    captures,
                    frame_independent,
                }
            }
            CoreKind::Call {
                callee,
                arguments,
                reference_origin,
                reference_shape,
                mandatory_tail,
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
                let values = self.strict_values(arguments.clone());
                if mandatory_tail {
                    for (argument, value) in arguments.iter().zip(&values) {
                        if !frame_independent_value(value)
                            && !crate::core::tail::tail_owned_type(self.signatures,
                                &self.body.expression(*argument).ty, &mut vec![]) {
                            self.error(self.body.expression(*argument).span, "G4403",
                                "mandatory `tail` argument may retain a reference, pointer, or callable environment dependent on the ending frame; its transfer provenance is not proven");
                        }
                    }
                }
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
                let mut environments = vec![incoming.clone()];
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
                    restore_bindings(&mut self.values, &incoming,
                        clause.bindings.iter().map(|(name, _)| name.clone()));
                    if !strict_expression_abrupt(self.body, clause.body) {
                        environments.push(self.values.clone());
                    }
                }
                self.values = joined_environments(&incoming, environments);
                join(exits)
            }
            CoreKind::Completion {
                computation,
                clauses,
                refinement_test,
                ..
            } => {
                let subject = computation;
                let computation = self.value(computation);
                let incoming = self.values.clone();
                // Core admits a Completion only after its pattern matrix has
                // proved it exhaustive. Unlike an effect handler, normal
                // completion therefore cannot fall through with the original
                // subject as its result. Keeping that impossible exit made a
                // temporary `Option<&T>` look like the enclosing function's
                // return value even when every arm consumed the reference.
                let mut exits = Vec::with_capacity(clauses.len());
                let mut environments = Vec::with_capacity(clauses.len());
                for (index, clause) in clauses.into_iter().enumerate() {
                    self.values = incoming.clone();
                    self.bind_pattern_value(&clause.pattern, computation.clone());
                    if index == 0 && refinement_test.is_some() {
                        let mut types = vec![];
                        let _ = crate::core::collect_pattern_binding_types(&clause.pattern,
                            &self.body.expression(subject).ty, &mut types);
                        for (name, ty) in types {
                            if crate::core::refinement_binding_type(ty.clone()) != ty {
                                let borrowed = self.borrowed_value(subject);
                                self.values.insert(name, borrowed);
                            }
                        }
                    }
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
                        let mut types = vec![];
                        let _ = crate::core::collect_pattern_binding_types(&refinement.pattern,
                            &self.body.expression(refinement.subject).ty, &mut types);
                        for (name, ty) in types {
                            if crate::core::refinement_binding_type(ty.clone()) != ty {
                                let borrowed = self.borrowed_value(refinement.subject);
                                self.values.insert(name, borrowed);
                            }
                        }
                    }
                    exits.push(self.value(clause.body));
                    let mut bindings = BTreeSet::new();
                    pattern_bindings(&clause.pattern, &mut bindings);
                    if let Some(refinement) = &clause.refinement {
                        pattern_bindings(&refinement.pattern, &mut bindings);
                    }
                    restore_bindings(&mut self.values, &incoming, bindings);
                    if !strict_expression_abrupt(self.body, clause.body) {
                        environments.push(self.values.clone());
                    }
                }
                self.values = joined_environments(&incoming, environments);
                join(exits)
            }
        };
        if matches!(value, Value::None)
            && crate::core::tail::tail_owned_type(self.signatures, &expression.ty, &mut vec![]) {
            Value::FrameIndependent
        } else {
            value
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
            // The raw-reference contract supplies validity independently of
            // local loans. Its selected lifetime is still checked by Core.
            CallReferenceOrigin::Unsafe => Value::ExternalBorrowed,
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
                    let Some(value) = self.reference_path_value(argument, &path.argument_fields) else {
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
                seal_array_extents(self.signatures, result_ty, &mut result);
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

    fn reference_path_value(&self, value: &Value, path: &[u32]) -> Option<Value> {
        let Some(deref) = path.iter().position(|field| *field == crate::core::REFERENCE_PATH_DEREF) else {
            return value_at_path(value, path);
        };
        let reference = value_at_path(value, &path[..deref])?;
        let resident = match reference {
            Value::ExternalBorrowed => Value::ExternalBorrowed,
            Value::Borrowed { storage, fields, .. } => value_at_path(self.values.residents.get(&storage?)?, &fields)?,
            Value::Joined(values) => return values.iter().map(|value|
                self.reference_path_value(value, &path[deref..])).collect::<Option<Vec<_>>>().map(join),
            _ => return None,
        };
        self.reference_path_value(&resident, &path[deref + 1..])
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
                self.values.define(name.clone(), value);
            }
            crate::core::CorePattern::Tuple(patterns) => {
                for (index, pattern) in patterns.iter().enumerate() {
                    let child = value_at_path(&value, &[index as u32]).unwrap_or(Value::None);
                    self.bind_pattern_value(pattern, child);
                }
            }
            crate::core::CorePattern::Array { elements, rest, .. } => {
                for (index, pattern) in elements.iter().enumerate() {
                    let index = crate::pattern::ArrayPatternRest::index(*rest, index);
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
        if let Some(value) = self.reborrowed_value(id) {
            for root in borrowed_roots(&value) {
                if !self.has_frozen_loan_root(&root) {
                    self.error(self.body.expression(id).span, "G5016",
                        format!("reference to `{root}` has no frozen NLL loan fact"));
                }
            }
            return value;
        }
        let mut fields = vec![];
        let mut projected = id;
        while let CoreKind::Field { base, index, .. } = self.body.expression(projected).kind {
            fields.push(index);
            projected = base;
        }
        fields.reverse();
        // Reborrowing through a reference supplied by the caller must remain
        // caller-owned.  `place_root` intentionally has no body-local root
        // for `&*external`; treating that absence as a temporary would reject
        // a valid reborrow merely because the reference first travelled
        // through an enum/array/refinement aggregate.
        let external_reborrow = self.reborrowed_from_external(id);
        let Some(root) = self.place_root(id) else {
            if external_reborrow {
                return Value::ExternalBorrowed;
            }
            let root = crate::placeflow::borrowed_temporary_root(crate::placeflow::borrowed_place_base(self.body, id));
            if self.has_frozen_loan_root(&root) {
                // A real local storage owner, not an external/static loan.
                // Return, suspension and mandatory-tail checks still reject
                // any value that carries this root across its boundary.
                let storage = self.values.bindings.get(&root).copied();
                return Value::Borrowed { root, storage, fields };
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
        if !self.has_frozen_loan_root(&root) {
            self.error(
                self.body.expression(id).span,
                "G5016",
                format!("reference to `{root}` has no frozen NLL loan fact"),
            );
        }
        let storage = self.values.bindings.get(&root).copied();
        Value::Borrowed { root, storage, fields }
    }

    fn has_frozen_loan_root(&self, spelling: &str) -> bool {
        self.loan_roots.iter().any(|root| {
            root == spelling
                || root
                    .strip_prefix(spelling)
                    .and_then(|suffix| suffix.strip_prefix('#'))
                    .is_some_and(|suffix| !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit()))
        })
    }

    /// A projected enum/record payload still belongs to the incoming loan.
    /// Field nodes sit between `&value.0` and the underlying `Deref(value)`,
    /// so checking only the immediate Core node mistakes a valid reborrow for
    /// a fresh temporary at the escape boundary.
    fn reborrowed_from_external(&mut self, id: CoreId) -> bool {
        match self.body.expression(id).kind.clone() {
            CoreKind::Field { base, .. } => self.reborrowed_from_external(base),
            CoreKind::Deref(reference) => matches!(self.value(reference), Value::ExternalBorrowed),
            _ => false,
        }
    }

    fn reborrowed_value(&mut self, id: CoreId) -> Option<Value> {
        match self.body.expression(id).kind.clone() {
            CoreKind::Field { base, index, .. } => self.reborrowed_value(base).map(|value| {
                fn project(value: Value, index: u32) -> Value {
                    match value {
                        Value::Borrowed { root, storage, mut fields } => { fields.push(index); Value::Borrowed { root, storage, fields } }
                        Value::Joined(values) => join(values.into_iter().map(|value| project(value, index)).collect()),
                        value => value,
                    }
                }
                project(value, index)
            }),
            CoreKind::Deref(reference) => {
                let value = self.value(reference);
                (!matches!(value, Value::None)).then_some(value)
            }
            _ => None,
        }
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
        // Replacing a statically scalar resident cannot change any stored
        // reference path. Still evaluate its reference operand below: an
        // opaque generic carrier must not suppress computed-place effects.
        let scalar_resident = matches!(place.ty(), Type::Scalar(_) | Type::Unit | Type::Never);
        if self.place_targets_external_storage(&place) {
            self.report_external_store_escape(&value, span);
        }
        match place {
            CorePlace::Local { name, .. } => {
                self.values.insert(name, value);
            }
            CorePlace::Field { ref base, .. } => {
                if let Some(name) = base.root_local().map(|(name, _)| name.to_owned()) {
                    if self.values.get(&name).is_none() { self.values.insert(name.clone(), Value::None); }
                    let entry = self.values.get_mut(&name).expect("assignment has a resident");
                    let mut path = vec![];
                    collect_field_path(&place, &mut path);
                    if !assign_field_path(entry, &path, value) {
                        self.error(
                            span,
                            "G5021",
                            "aggregate projection assignment has no sealed structural provenance path",
                        );
                    }
                } else {
                    let mut base = &place;
                    let mut fields = vec![];
                    while let CorePlace::Field { base: parent, index, .. } = base {
                        fields.push(*index);
                        base = parent;
                    }
                    if let CorePlace::Deref { reference, .. } = base {
                        fields.reverse();
                        let reference = self.value(*reference);
                        if !scalar_resident { self.assign_reference_resident(reference, &fields, value, span); }
                    }
                }
            }
            CorePlace::Deref { reference, .. } => {
                let reference = self.value(reference);
                if !scalar_resident { self.assign_reference_resident(reference, &[], value, span); }
            }
            CorePlace::Error => {}
        }
    }

    fn assign_reference_resident(&mut self, reference: Value, projected: &[u32], value: Value, span: Span) {
        fn targets(reference: Value, projected: &[u32], result: &mut BTreeSet<(u64, Vec<u32>)>) {
            match reference {
                Value::Borrowed { storage: Some(storage), mut fields, .. } => {
                    fields.extend_from_slice(projected);
                    result.insert((storage, fields));
                }
                Value::Joined(values) => for value in values { targets(value, projected, result); },
                _ => {},
            }
        }
        let mut destinations = BTreeSet::new();
        targets(reference, projected, &mut destinations);
        let exact = destinations.len() == 1;
        for (storage, fields) in destinations {
            let Some(resident) = self.values.residents.get_mut(&storage) else { continue; };
            let replacement = if exact { value.clone() }
                else { join(vec![value_at_path(resident, &fields).unwrap_or(Value::None), value.clone()]) };
            if !replace_resident_path(resident, &fields, replacement) {
                self.error(span, "G5021", "reference projection assignment has no sealed resident provenance path");
            }
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
    if let Value::Joined(values) = value {
        for value in values.iter_mut() {
            if !assign_field_path(value, path, replacement.clone()) { return false; }
        }
        *value = join(std::mem::take(values));
        return true;
    }
    let mut current = value;
    for (position, (index, field_count)) in path.iter().enumerate() {
        if *index >= *field_count {
            return false;
        }
        if matches!(current, Value::None) {
            *current = Value::Aggregate(vec![Value::None; *field_count as usize]);
        }
        if matches!(current, Value::FrameIndependent) {
            *current = Value::Aggregate(vec![Value::FrameIndependent; *field_count as usize]);
        }
        // A nominal parameter's private layout is opaque to escape analysis,
        // but its source-level projection path is already sealed by Core.
        // Opening that one path must retain the caller-owned provenance of
        // untouched leaves: otherwise `slot.inner.value = &local` would be
        // rejected as an unmodelled aggregate write before the returned local
        // borrow can be diagnosed. The replacement leaf below overwrites the
        // relevant external marker with its precise body-local provenance.
        if matches!(current, Value::ExternalBorrowed) {
            *current = Value::Aggregate(vec![Value::ExternalBorrowed; *field_count as usize]);
        }
        if let Value::Array { length, element, fields } = current {
            if length.is_some_and(|length| length != u64::from(*field_count)) { return false; }
            *length = Some(u64::from(*field_count));
            let field = fields.entry(*index).or_insert_with(|| (**element).clone());
            if position + 1 == path.len() { *field = replacement; return true; }
            current = field;
            continue;
        }
        let (Value::Aggregate(fields) | Value::Variant(fields)) = current else {
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
    value_at_variant_path(value, path, false)
}

fn replace_resident_path(target: &mut Value, path: &[u32], replacement: Value) -> bool {
    let Some((field, tail)) = path.split_first() else { *target = replacement; return true; };
    if let Value::Joined(values) = target {
        return values.iter_mut().all(|value| replace_resident_path(value, path, replacement.clone()));
    }
    if let Value::Array { length, element, fields } = target {
        if length.is_some_and(|length| u64::from(*field) >= length) { return false; }
        let target = fields.entry(*field).or_insert_with(|| (**element).clone());
        return replace_resident_path(target, tail, replacement);
    }
    let (Value::Aggregate(fields) | Value::Variant(fields)) = target else { return false; };
    let Some(target) = fields.get_mut(*field as usize) else { return false; };
    replace_resident_path(target, tail, replacement)
}

fn value_at_variant_path(value: &Value, path: &[u32], known_variant: bool) -> Option<Value> {
    if let Value::Joined(values) = value {
        return values.iter().map(|value| value_at_variant_path(value, path, known_variant))
            .collect::<Option<Vec<_>>>().map(join);
    }
    // `ExternalBorrowed` is the sealed marker for a call whose *every*
    // reference leaf is static/external.  A later source-level library call
    // may forward one nested reference leaf (for example, `Str::as_bytes`
    // forwards the backing reference inside a `Str`).  Its nominal layout is
    // deliberately unavailable to this pass, but every such leaf remains
    // external, so it is sound to preserve that fact through any frozen
    // structural path.
    if matches!(value, Value::ExternalBorrowed) {
        return Some(Value::ExternalBorrowed);
    }
    let Some((field, tail)) = path.split_first() else { return Some(value.clone()); };
    if let Value::Array { length, element, fields } = value {
        if *field == crate::core::REFERENCE_PATH_ARRAY_ELEMENT {
            return array_values(*length, element, fields)
                .map(|value| value_at_variant_path(value, tail, known_variant))
                .collect::<Option<Vec<_>>>().map(join);
        }
        if length.is_some_and(|length| u64::from(*field) >= length) { return None; }
        return value_at_variant_path(fields.get(field).unwrap_or(element), tail, known_variant);
    }
    let (fields, known_variant) = match value {
        Value::Aggregate(fields) => (fields, known_variant),
        Value::Variant(fields) => (fields, true),
        _ => return None,
    };
    if *field == crate::core::REFERENCE_PATH_ARRAY_ELEMENT {
        return fields.iter().map(|value| value_at_variant_path(value, tail, known_variant))
            .collect::<Option<Vec<_>>>().map(join);
    }
    let Some(next) = fields.get(*field as usize) else {
        return known_variant.then_some(Value::None);
    };
    value_at_variant_path(next, tail, known_variant)
}

fn put_value_at_path(target: &mut Value, path: &[u32], replacement: Value) -> bool {
    if path.is_empty() {
        // One result leaf can borrow from any of several contract inputs.
        // Preserve their union so no local source vanishes at an escape.
        if matches!(target, Value::None) { *target = replacement; }
        else if *target != replacement {
            *target = join(vec![std::mem::replace(target, Value::None), replacement]);
        }
        return true;
    }
    if path[0] == crate::core::REFERENCE_PATH_ARRAY_ELEMENT {
        if matches!(target, Value::None) {
            *target = Value::Array { length: None, element: Box::new(Value::None), fields: BTreeMap::new() };
        }
        let Value::Array { element, fields, .. } = target else { return false; };
        return put_value_at_path(element, &path[1..], replacement.clone())
            && fields.values_mut().all(|value| put_value_at_path(value, &path[1..], replacement.clone()));
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

fn array_values<'a>(length: Option<u64>, element: &'a Value, fields: &'a BTreeMap<u32, Value>)
    -> impl Iterator<Item = &'a Value>
{
    (!length.is_some_and(|length| length == fields.len() as u64)).then_some(element)
        .into_iter().chain(fields.values())
}

fn seal_array_extents(signatures: &crate::ElaboratedInterface, ty: &Type, value: &mut Value) {
    match (ty, value) {
        (Type::FixedArray { element: ty, length }, Value::Array { length: extent, element, .. }) => {
            *extent = Type::FixedArray { element: ty.clone(), length: length.clone() }.fixed_array_length();
            seal_array_extents(signatures, ty, element);
        }
        (Type::Tuple(types), Value::Aggregate(fields)) => {
            for (ty, value) in types.iter().zip(fields) { seal_array_extents(signatures, ty, value); }
        }
        (Type::Nominal { definition, arguments }, Value::Aggregate(fields)) => {
            let Some(crate::ElaboratedHeader::Nominal {
                layout: crate::signature::ElaboratedNominalLayout::Struct(types)
                    | crate::signature::ElaboratedNominalLayout::TupleStruct(types), ..
            }) = signatures.definitions.get(definition) else { return; };
            for (ty, value) in types.iter().zip(fields) {
                if let Ok(ty) = crate::core::instantiate_nominal_field_type(&ty.ty, arguments) {
                    seal_array_extents(signatures, &ty, value);
                }
            }
        }
        _ => {}
    }
}

fn restore_bindings(
    values: &mut ValueEnvironment, incoming: &ValueEnvironment,
    bindings: impl IntoIterator<Item = String>,
) {
    for name in bindings {
        if let Some(identity) = incoming.bindings.get(&name) { values.bindings.insert(name, *identity); }
        else { values.remove(&name); }
    }
}

fn pattern_bindings(pattern: &crate::core::CorePattern, names: &mut BTreeSet<String>) {
    use crate::core::CorePattern;
    match pattern {
        CorePattern::Bind { name } => { names.insert(name.clone()); }
        CorePattern::Tuple(patterns) | CorePattern::Array { elements: patterns, .. } => {
            for pattern in patterns { pattern_bindings(pattern, names); }
        }
        CorePattern::Record { fields, .. } | CorePattern::Enum { fields, .. } => {
            for field in fields { pattern_bindings(&field.pattern, names); }
        }
        CorePattern::Any | CorePattern::Literal(_) | CorePattern::Error => {}
    }
}

fn joined_environments(
    incoming: &ValueEnvironment, exits: Vec<ValueEnvironment>,
) -> ValueEnvironment {
    if exits.is_empty() { return incoming.clone(); }
    let identities = exits.iter().flat_map(|exit| exit.residents.keys().copied()).collect::<BTreeSet<_>>();
    ValueEnvironment {
        bindings: incoming.bindings.clone(),
        next: exits.iter().map(|exit| exit.next).max().unwrap_or(incoming.next),
        residents: identities.into_iter().map(|identity| (identity, join(exits.iter()
            .filter_map(|exit| exit.residents.get(&identity).cloned()).collect()))).collect(),
    }
}

fn join(incoming: Vec<Value>) -> Value {
    fn flatten(values: Vec<Value>, output: &mut Vec<Value>) {
        for value in values {
            if let Value::Joined(values) = value { flatten(values, output); }
            else if !output.contains(&value) { output.push(value); }
        }
    }
    let mut values = vec![];
    flatten(incoming, &mut values);
    // Keep aggregate joins field-wise. Repeated conditional assignments
    // must not materialize the Cartesian product of every earlier branch.
    if values.len() > 1 && let Value::Aggregate(first) = &values[0] {
        let count = first.len();
        if values.iter().all(|value| matches!(value, Value::Aggregate(fields) if fields.len() == count)) {
            return Value::Aggregate((0..count).map(|index| join(values.iter().map(|value| {
                let Value::Aggregate(fields) = value else { unreachable!() };
                fields[index].clone()
            }).collect())).collect());
        }
    }
    match values.len() {
        0 => Value::None,
        1 => values.pop().expect("one value"),
        _ => Value::Joined(values),
    }
}

fn frame_independent_value(value: &Value) -> bool {
    match value {
        Value::FrameIndependent | Value::ExternalBorrowed => true,
        Value::Aggregate(values) | Value::Variant(values) | Value::Joined(values) => {
            values.iter().all(frame_independent_value)
        }
        Value::Array { length, element, fields } =>
            array_values(*length, element, fields).all(frame_independent_value),
        Value::Closure { frame_independent, .. } => *frame_independent,
        Value::None | Value::Borrowed { .. } => false,
    }
}

fn borrowed_roots(value: &Value) -> BTreeSet<String> {
    let mut roots = BTreeSet::new();
    collect_borrowed_roots(value, &mut roots);
    roots
}

fn collect_borrowed_roots(value: &Value, roots: &mut BTreeSet<String>) {
    match value {
        Value::Borrowed { root, .. } => {
            roots.insert(root.clone());
        }
        Value::Aggregate(values) | Value::Variant(values) | Value::Joined(values) => {
            for value in values {
                collect_borrowed_roots(value, roots);
            }
        }
        Value::Array { length, element, fields } => {
            for value in array_values(*length, element, fields) { collect_borrowed_roots(value, roots); }
        }
        Value::Closure { .. } | Value::None | Value::FrameIndependent | Value::ExternalBorrowed => {}
    }
}

/// See the matching PlaceFlow helper. An open type parameter is checked at
/// the concrete instantiation boundary; it cannot by itself identify a
/// body-local backing place in this generic declaration.
fn contains_open_type_parameter(value: &Type) -> bool {
    match value {
        Type::FixedArray { element, length } => contains_open_type_parameter(element)
            || generic_argument_contains_open_type_parameter(length),
        Type::Generic(_) => true,
        Type::Tuple(values) => values.iter().any(contains_open_type_parameter),
        Type::Array(value)
        | Type::StaticData { element: value, .. }
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
        // A raw pointer has no resident/borrowed pointee to defer to a later
        // ownership instantiation. Its type arguments still participate in
        // type identity and specialization, independently of this loan walk.
        | Type::RawPointer { .. }
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstInteger(_)
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
        | GenericArgument::ConstInteger(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstIntegerExpr(_)
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
        Value::Aggregate(values) | Value::Variant(values) | Value::Joined(values) => {
            values.iter().any(value_contains_external_reference)
        }
        Value::Array { length, element, fields } =>
            array_values(*length, element, fields).any(value_contains_external_reference),
        Value::None | Value::FrameIndependent | Value::Borrowed { .. } | Value::Closure { .. } => false,
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
        Value::Aggregate(values) | Value::Variant(values) | Value::Joined(values) => {
            for value in values {
                collect_closure_captures(value, captures);
            }
        }
        Value::Array { length, element, fields } => {
            for value in array_values(*length, element, fields) { collect_closure_captures(value, captures); }
        }
        Value::None | Value::FrameIndependent | Value::ExternalBorrowed | Value::Borrowed { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn symbolic_array_provenance_keeps_union_and_sparse_replacement_obligations() {
        use super::*;
        let a = Value::Borrowed { root: "a".into(), storage: None, fields: vec![] };
        let b = Value::Borrowed { root: "b".into(), storage: None, fields: vec![] };
        let wildcard = crate::core::REFERENCE_PATH_ARRAY_ELEMENT;
        let source = Value::Aggregate(vec![a.clone(), b.clone()]);
        let forwarded = value_at_path(&source, &[wildcard]).unwrap();
        assert_eq!(borrowed_roots(&forwarded), BTreeSet::from(["a".into(), "b".into()]));
        let mut result = Value::None;
        assert!(put_value_at_path(&mut result, &[wildcard, 0], forwarded));
        let reference = Type::Reference { mutability: crate::Mutability::Shared,
            lifetime: crate::Lifetime::Elided, referent: Box::new(Type::Scalar(crate::ScalarType::I64)) };
        seal_array_extents(&crate::ElaboratedInterface::default(),
            &Type::fixed_array(Type::Tuple(vec![reference]), 2), &mut result);
        assert_eq!(borrowed_roots(&value_at_path(&result, &[0, 0]).unwrap()), borrowed_roots(&source));
        assert!(value_at_path(&result, &[2, 0]).is_none());
        assert!(assign_field_path(&mut result, &[(0, 2), (0, 1)], Value::ExternalBorrowed));
        assert!(borrowed_roots(&value_at_path(&result, &[0, 0]).unwrap()).is_empty());
        assert_eq!(borrowed_roots(&result), borrowed_roots(&source));
        assert!(assign_field_path(&mut result, &[(1, 2), (0, 1)], Value::ExternalBorrowed));
        assert!(borrowed_roots(&result).is_empty(), "every initialized slot was replaced");
        let Value::Array { fields, .. } = result else { panic!("symbolic array"); };
        assert_eq!(fields.len(), 2);
        let huge = Value::Array { length: Some(u64::MAX), element: Box::new(a), fields: BTreeMap::new() };
        assert_eq!(borrowed_roots(&value_at_path(&huge, &[17]).unwrap()), BTreeSet::from(["a".into()]));
    }

    #[test]
    fn provenance_joins_are_idempotent_and_keep_aggregate_choices_field_wise() {
        use super::*;
        let a = Value::Borrowed { root: "a".into(), storage: None, fields: vec![] };
        let b = Value::Borrowed { root: "b".into(), storage: None, fields: vec![] };
        let mut value = Value::Aggregate(vec![a.clone(), Value::ExternalBorrowed]);
        for _ in 0..100 {
            value = join(vec![value.clone(), value.clone()]);
        }
        assert_eq!(value, Value::Aggregate(vec![a.clone(), Value::ExternalBorrowed]));
        let joined = join(vec![value, Value::Aggregate(vec![b.clone(), Value::ExternalBorrowed])]);
        assert_eq!(joined, Value::Aggregate(vec![join(vec![a, b]), Value::ExternalBorrowed]));
        assert!(!frame_independent_value(&joined));
    }

    use super::*;

    #[test]
    fn variant_provenance_keeps_present_loans_and_only_omits_absent_residents() {
        let loan = Value::Borrowed { root: "owner".into(), storage: None, fields: vec![] };
        let yes = Value::Variant(vec![Value::Aggregate(vec![loan.clone()])]);
        let no = Value::Variant(vec![Value::Aggregate(vec![])]);
        let selected = value_at_path(&join(vec![yes, no]), &[0, 0]).unwrap();
        assert_eq!(borrowed_roots(&selected), BTreeSet::from(["owner".into()]));
        assert_eq!(value_at_path(&Value::Aggregate(vec![]), &[0]), None);
        assert_eq!(value_at_path(&Value::Variant(vec![Value::None]), &[0, 0]), None);
        let unknown = join(vec![Value::Aggregate(vec![loan]), Value::None]);
        assert_eq!(value_at_path(&unknown, &[0]), None);
    }
}
