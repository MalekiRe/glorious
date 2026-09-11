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
    placeflow::PlaceFlow,
    source::Span,
    types::{EffectRow, GenericArgument, Type},
};
use std::collections::{BTreeMap, BTreeSet};
mod invocations;
mod control;
use control::{ControlBrand, value_controls};

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
    control_input: Option<crate::Digest>,
    control_captures: BTreeMap<EnvironmentBrand, BTreeSet<ControlBrand>>,
}

/// Request-local capture obligations from the existing lifetime analysis.
/// A body seal travels with the entries; consumers cannot supply an unbound
/// set of constructor names as lifetime authority.
#[derive(Default)]
pub(crate) struct ControlCaptures {
    bodies: BTreeMap<crate::DefKey, (crate::Digest, BTreeSet<EnvironmentBrand>)>,
}

impl ControlCaptures {
    pub(crate) fn include(&mut self, owner: crate::DefKey, body: &TypedBody, escapes: &EscapeFlow) -> Result<(), &'static str> {
        let captures = escapes.resumption_captures(body)?;
        self.bodies.insert(owner, (body.semantic_fingerprint(), captures));
        Ok(())
    }

    pub(crate) fn bind(&self, owner: crate::DefKey, body: &TypedBody) -> Result<bool, &'static str> {
        let (input, captures) = self.bodies.get(&owner).ok_or("missing source control lifetime product")?;
        if *input != body.semantic_fingerprint() { return Err("stale source control lifetime product"); }
        Ok(!captures.is_empty())
    }

    pub(crate) fn contains(&self, environment: EnvironmentBrand) -> bool {
        self.bodies.values().any(|(_, captures)| captures.contains(&environment))
    }
}

impl EscapeFlow {
    fn resumption_captures(&self, body: &TypedBody) -> Result<BTreeSet<EnvironmentBrand>, &'static str> {
        if self.control_input != Some(body.semantic_fingerprint()) || !self.diagnostics.is_empty() {
            return Err("control lifetime product does not match admitted source Core");
        }
        Ok(self.control_captures.iter().filter_map(|(environment, controls)|
            controls.iter().any(|brand| matches!(brand, ControlBrand::Resumption(_))).then_some(*environment)).collect())
    }

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
        let continuations = match flow.continuations_for(body) {
            Ok(facts) => facts,
            Err(error) => return Self { diagnostics: vec![EscapeDiagnostic {
                code: error.code, span: error.span, message: error.message,
            }], ..Self::default() },
        };
        // This phase requires an admitted loan product. A rejected borrow
        // deliberately has no checked access; interpreting that as an
        // executed call operand would manufacture unrelated provenance gaps.
        // Retain the actual failure, and publish no control-lifetime proof.
        if !flow.diagnostics.is_empty() {
            return Self { diagnostics: flow.diagnostics.iter().map(|error| EscapeDiagnostic {
                code: error.code, span: error.span, message: error.message.clone(),
            }).collect(), ..Self::default() };
        }
        let mut analyzer = Analyzer {
            body,
            continuations,
            signatures,
            closure_flows: flow.closure_flows(),
            loan_flow: flow,
            values: ValueEnvironment::default(),
            labels: vec![],
            handler_inputs: vec![],
            control_captures: BTreeMap::new(),
            diagnostics: vec![],
        };
        // Parameters may carry references through structural aggregates. They
        // originate outside this body, but their shape must still be present
        // so a later assignment of `&local` into (for example) `slot.0`
        // replaces that exact projection rather than disappearing from the
        // boundary provenance model.
        for (name, ty) in &body.parameters {
            let value = analyzer.seed_logical_value(format!("<parameter-{name}>"), ty, parameter_value(ty));
            analyzer.values.insert(name.clone(), value);
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
            control_input: Some(body.semantic_fingerprint()),
            control_captures: analyzer.control_captures,
        }
    }
}

/// Provenance that matters at an outlives boundary.  Scalars and normal
/// nominal values are omitted; only borrowed storage and closures that carry
/// one of those borrows can make a body-local region escape.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Value {
    None,
    /// A represented value/projection proved to contain no reference. This
    /// is stronger than an unknown footprint or a caller-owned generic value.
    ReferenceFree,
    /// A label or resumption is not an empty scalar footprint. Its generative
    /// destination must remain live through aliases and captured residents.
    Control(ControlBrand),
    /// Proven resident without any frame-relative component. Unlike `None`,
    /// this is positive transfer evidence, never absence of a known loan.
    FrameIndependent,
    /// A reference supplied by the caller. It may be returned or carried
    /// across suspension, but can be overwritten by a body-local borrow in
    /// an aggregate projection.
    ExternalBorrowed,
    /// A reference snapshot keeps validity, physical targets and declared
    /// resident contents distinct. The shared invocation relation may prove
    /// validity on every normal return without erasing any loan dependencies.
    Reference {
        dependencies: Box<Value>,
        /// Complete possible referents, independently of retained region debt.
        /// None is unknown, not a reference to every retained dependency.
        targets: Option<Box<Value>>,
        /// Declared reference-containing resident snapshot. This does not
        /// authorize addressing or replacing any retained loan's storage.
        contents: Option<Box<Value>>,
        authenticated: bool,
    },
    Region(BTreeSet<crate::placeflow::regions::Region>),
    Borrowed {
        root: String,
        storage: Option<u64>,
        fields: Vec<u32>,
        capture_path: Vec<crate::resident_invocations::CaptureProjection>,
    },
    Aggregate(Vec<Value>),
    /// An opaque physical aggregate with explicit projected updates. The
    /// fallback describes every untouched field, without inventing an arity,
    /// array extent, or inactive variant. Paths still require typed authority.
    Projected {
        fallback: Box<Value>,
        fields: BTreeMap<u32, Value>,
    },
    /// Type/lifetime-argument residents are not physical fields. Keep their
    /// provenance beside the physical shape without fabricating an address
    /// or allocating a vector indexed by a reserved path component.
    Logical {
        physical: Box<Value>,
        arguments: BTreeMap<u32, Value>,
    },
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
    /// A closed enum can expose incompatible layouts at the same payload
    /// position, for example Result<[&T; N], Vec<&T>>. Keep both provenance
    /// shapes without claiming that either is a field of the other.
    Alternatives(Vec<Value>),
    Closure {
        environment: EnvironmentBrand,
        captures: Vec<Capture>,
        resident_captures: Vec<crate::resident_invocations::Operand<Value>>,
        frame_independent: bool,
        regions: BTreeSet<crate::placeflow::regions::Region>,
        controls: BTreeSet<ControlBrand>,
    },
    /// An opaque factory result carries selected input snapshots without
    /// inventing a physical environment field or a compiler-owned brand.
    CallableResident {
        footprint: Box<Value>,
        resident_captures: Vec<crate::resident_invocations::Operand<Value>>,
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
    regions: crate::placeflow::regions::RegionGraph<Value>,
}

/// A result travels with the storage snapshot of the same continuation.
/// Normal branches and exact label transfers share this representation;
/// a definitely terminal branch contributes neither a normal value nor state.
struct ValueExit {
    value: Value,
    environment: ValueEnvironment,
}

/// Evaluating an operation's strict prefix is distinct from invoking it, and
/// an invoked terminal operation has a payload but no ordinary result.
enum PerformedValue {
    PrefixExit,
    Invoked {
        effect: crate::EffectInstance,
        operation: u32,
        payloads: Vec<Value>,
        result: Option<Value>,
    },
}

struct LabelBoundary {
    brand: crate::LabelBrand,
    exits: Vec<ValueExit>,
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

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Capture {
    /// A retained body-local dependency: either the borrowed capture slot or
    /// a backing place reached through its contents (including nested closures).
    Borrowed {
        root: String,
        environment: EnvironmentBrand,
    },
}

/// A rigid type parameter was fixed outside this activation. A checked value
/// of that type cannot acquire this activation's local region by constructing
/// a new reference or closure: doing so would require changing the rigid type.
/// It can still contain unknown references and control capabilities belonging
/// to its caller. This is boundary independence, not reference absence,
/// referent identity, addressability or permission to discard the value.
fn type_proven_value(signatures: &crate::ElaboratedInterface, ty: &Type) -> Option<Value> {
    if matches!(ty, Type::Generic(_)) {
        Some(Value::FrameIndependent)
    } else if crate::core::tail::tail_owned_type(signatures, ty, &mut vec![]) {
        Some(Value::ReferenceFree)
    } else {
        None
    }
}

struct Analyzer<'a> {
    closure_flows: &'a BTreeMap<EnvironmentBrand, PlaceFlow>,
    body: &'a TypedBody,
    continuations: &'a crate::core_continuations::CoreContinuations,
    signatures: &'a crate::ElaboratedInterface,
    loan_flow: &'a PlaceFlow,
    values: ValueEnvironment,
    labels: Vec<LabelBoundary>,
    handler_inputs: Vec<HandlerInputs>,
    control_captures: BTreeMap<EnvironmentBrand, BTreeSet<ControlBrand>>,
    diagnostics: Vec<EscapeDiagnostic>,
}

struct HandlerInputs {
    computation: CoreId,
    payloads: Vec<(crate::EffectInstance, u32, Value)>,
}

impl Analyzer<'_> {
    fn seed_logical_value(&mut self, site: String, ty: &Type, mut value: Value) -> Value {
        let mut leaves = vec![];
        let _ = crate::core::reference_leaf_paths(self.signatures, ty, &mut vec![], &mut leaves);
        leaves.extend(crate::placeflow::regions::callable_paths(self.signatures, ty, false));
        if !leaves.iter().any(|(path, _)| crate::core::reference_path_is_logical(path)) { return value; }
        let external = matches!(value, Value::ExternalBorrowed);
        // Logical generic residents augment the parameter's physical
        // provenance. An incomplete nominal/variant layout cannot erase the
        // caller-owned physical carrier while installing its logical slots.
        for (path, _) in leaves {
            if !crate::core::reference_path_is_logical(&path) { continue; }
            let resident = if external { Value::ExternalBorrowed }
                else { value_at_path(&value, &path).unwrap_or(Value::None) };
            let mut regions = logical_regions(&resident);
            if regions.is_empty() {
                regions.insert(crate::placeflow::regions::Region { site: site.clone(), path: path.clone() });
            } else if matches!(resident, Value::Region(_)) { continue; }
            self.values.regions.connect(&regions);
            self.values.regions.insert(regions.first().expect("one logical origin").clone(), resident, merge_region_values);
            let replacement = Value::Region(regions);
            if !replace_resident_path(&mut value, &path, replacement.clone())
                && !put_value_at_path(&mut value, &path, replacement.clone()) {
                let mut alternative = Value::None;
                if put_value_at_path(&mut alternative, &path, replacement) {
                    value = Value::Alternatives(vec![value, alternative]);
                }
            }
        }
        seal_array_extents(self.signatures, ty, &mut value);
        value
    }

    fn resolved_value(&self, value: &Value) -> Value {
        Self::resolved_value_in(value, &self.values)
    }

    fn resolved_value_in(value: &Value, values: &ValueEnvironment) -> Value {
        // None here denotes a dependency backedge, not an unknown value. A
        // cyclic union must retain its grounded evidence exactly once; using
        // Value::None for the backedge invents an unresolved alternative.
        // A cycle with no grounded evidence still resolves to unknown below.
        fn resolve(value: &Value, graph: &crate::placeflow::regions::RegionGraph<Value>, active: &mut BTreeSet<crate::placeflow::regions::Region>) -> Option<Value> {
            Some(match value {
                Value::Region(regions) => {
                    let fresh = graph.reachable(regions).difference(active).cloned().collect::<BTreeSet<_>>();
                    if fresh.is_empty() { return None; }
                    active.extend(fresh.iter().cloned());
                    let values = fresh.iter().filter_map(|region| match graph.get(region) {
                        Some(value) => resolve(value, graph, active),
                        // Missing input is unknown even if a different node
                        // in the same connected component has known contents.
                        None => Some(Value::None),
                    }).collect::<Vec<_>>();
                    for region in fresh { active.remove(&region); }
                    if values.is_empty() { return None; }
                    join(values)
                }
                Value::Aggregate(values) => Value::Aggregate(values.iter().map(|value| resolve(value, graph, active).unwrap_or(Value::None)).collect()),
                Value::Variant(values) => Value::Variant(values.iter().map(|value| resolve(value, graph, active).unwrap_or(Value::None)).collect()),
                Value::Alternatives(values) => Value::Alternatives(values.iter().map(|value| resolve(value, graph, active).unwrap_or(Value::None)).collect()),
                Value::Joined(values) => {
                    let values = values.iter().filter_map(|value| resolve(value, graph, active)).collect::<Vec<_>>();
                    if values.is_empty() { return None; }
                    join(values)
                }
                Value::Reference { dependencies, targets, contents, authenticated } => Value::Reference {
                    dependencies: Box::new(resolve(dependencies, graph, active).unwrap_or(Value::None)),
                    targets: targets.as_ref().map(|targets| Box::new(resolve(targets, graph, active).unwrap_or(Value::None))),
                    contents: contents.as_ref().map(|contents| Box::new(resolve(contents, graph, active).unwrap_or(Value::None))),
                    authenticated: *authenticated,
                },
                Value::Array { length, element, fields } => Value::Array { length: *length,
                    element: Box::new(resolve(element, graph, active).unwrap_or(Value::None)),
                    fields: fields.iter().map(|(index, value)| (*index, resolve(value, graph, active).unwrap_or(Value::None))).collect() },
                Value::Projected { fallback, fields } => Value::Projected {
                    fallback: Box::new(resolve(fallback, graph, active).unwrap_or(Value::None)),
                    fields: fields.iter().map(|(index, value)| (*index, resolve(value, graph, active).unwrap_or(Value::None))).collect() },
                Value::Logical { physical, arguments } => Value::Logical { physical: Box::new(resolve(physical, graph, active).unwrap_or(Value::None)),
                    arguments: arguments.iter().map(|(index, value)| (*index, resolve(value, graph, active).unwrap_or(Value::None))).collect() },
                Value::Closure { environment, captures, resident_captures, frame_independent, regions, controls } => {
                    let possible = resolve(&Value::Region(regions.clone()), graph, active).unwrap_or(Value::None);
                    let roots = capture_dependency_roots(&possible);
                    let mut captures = captures.clone();
                    captures.extend(roots.iter().cloned().map(|root| Capture::Borrowed { root, environment: *environment }));
                    let controls = controls.iter().copied().chain(value_controls(&possible)).collect::<BTreeSet<_>>();
                    Value::Closure { environment: *environment, captures,
                        resident_captures: resident_captures.clone(),
                        frame_independent: *frame_independent && roots.is_empty() && controls.is_empty(),
                        regions: BTreeSet::new(), controls }
                }
                Value::CallableResident { footprint, resident_captures } => Value::CallableResident {
                    footprint: Box::new(resolve(footprint, graph, active).unwrap_or(Value::None)), resident_captures: resident_captures.clone(),
                },
                value => value.clone(),
            })
        }
        resolve(value, &values.regions, &mut BTreeSet::new()).unwrap_or(Value::None)
    }

    fn value(&mut self, id: CoreId) -> Value {
        let expression = self.body.expression(id).clone();
        let value = match expression.kind {
            CoreKind::ConstValue(_) => Value::None,
            CoreKind::Literal(_)
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Error
            | CoreKind::PatternTest { .. }
            | CoreKind::IntrinsicCall { .. } => Value::None,
            CoreKind::Constant { .. } => {
                self.record_invocation_exits(id, &Value::None, &[], expression.span);
                if self.continuations.is_abrupt(id) { return Value::None; }
                let (origin, shape) = crate::callable_declarations::value_reference_contract(self.signatures, &expression.ty);
                self.invocation_result_value(id, &Value::None, vec![], origin, shape)
            }
            CoreKind::Resumption { id, .. } => Value::Control(ControlBrand::Resumption(id)),
            CoreKind::LabelValue { .. } => Value::Control(ControlBrand::Label(self.continuations.label_reference(id)
                .expect("a bound label dependency product retains each label value's brand"))),
            CoreKind::Local(name) => self.values.get(&name).cloned().unwrap_or(Value::None),
            CoreKind::Borrow { value, .. } if self.continuations.is_abrupt(value) => {
                self.value(value);
                Value::None
            }
            CoreKind::Borrow { .. } => {
                let Some(access) = self.loan_flow.checked_borrow(id) else {
                    self.error(expression.span, "G5016", "borrow has no checked access in its frozen callable loan product");
                    return Value::None;
                };
                if let Some(base) = access.temporary {
                    // Borrowing does not skip the rvalue's strict evaluation:
                    // nested calls, assignments and suspension still occur.
                    let resident = self.value(base);
                    self.values.insert(crate::placeflow::borrowed_temporary_root(base), resident);
                }
                self.borrowed_value(access)
            }
            CoreKind::Deref(value) => {
                // Loading an incoming reference-bearing value preserves its
                // caller-owned reference leaves. Do not fabricate external
                // provenance for a local/unknown reference: those require a
                // structural account of the referenced storage.
                let value = self.value(value);
                match self.reference_path_value(&value, &[crate::core::REFERENCE_PATH_DEREF]) {
                    Some(resident) => resident,
                    None if crate::core::tail::tail_owned_type(self.signatures, &expression.ty, &mut vec![]) => Value::FrameIndependent,
                    None => {
                        self.error(expression.span, "G5023", "reference-containing load has unresolved referent storage");
                        join(vec![Value::None, value])
                    }
                }
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
            CoreKind::Let { name, value, .. } => {
                let evaluated = self.value(value);
                if self.continuations.is_abrupt(value) {
                    return Value::None;
                }
                self.values.define(name, evaluated);
                Value::None
            }
            CoreKind::Label { brand, body } => {
                let incoming = self.values.clone();
                self.labels.push(LabelBoundary { brand, exits: vec![] });
                let normal = self.value(body);
                let mut label = self.labels.pop().expect("active escape label");
                assert_eq!(label.brand, brand);
                label.exits.extend(self.normal_exit(body, normal));
                let result = self.join_exits(&incoming, label.exits);
                self.report_control_scope_escape(ControlBrand::Label(brand), &result, &incoming, expression.span);
                result
            }
            CoreKind::Transfer { brand, value } => {
                let payload = self.value(value);
                if !self.continuations.is_abrupt(value) { self.record_label_exit(brand, payload, expression.span); }
                Value::None
            }
            CoreKind::Assign { place, value } => {
                let evaluated = self.value(value);
                if self.continuations.is_abrupt(value) {
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
                    if self.continuations.is_abrupt(value) {
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
                use crate::capture_formation::{CaptureAction, CaptureFormation, CaptureSource};
                if crate::core::capture_environment_error(callable, &environment, &expression.ty).is_some() {
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
                let outer_labels = std::mem::take(&mut self.labels);
                // Captured destinations remain lexical inputs while this
                // isolated invocation is inspected. Its exits must not run
                // at formation or masquerade as ordinary function returns.
                let mut controls = self.continuations.lexical_label_inputs(body)
                    .expect("bound closure dependencies cover every Core body").iter().copied()
                    .map(ControlBrand::Label).collect::<BTreeSet<_>>();
                for capture in &environment.captures {
                    for action in CaptureFormation::new(capture).actions() {
                        if matches!(action, CaptureAction::RetainContents)
                            && let Some(value) = self.values.get(&capture.name) {
                            controls.extend(value_controls(&self.resolved_value(value)));
                        }
                    }
                }
                self.control_captures.entry(environment.brand).or_default().extend(&controls);
                self.labels = outer_labels.iter().filter(|label| controls.contains(&ControlBrand::Label(label.brand)))
                    .map(|label| LabelBoundary { brand: label.brand, exits: vec![] }).collect();
                let Some(flow) = self.closure_flows.get(&environment.brand) else {
                    self.error(expression.span, "G5016", "closure body has no frozen callable loan product");
                    self.labels = outer_labels;
                    return Value::None;
                };
                let outer_loan_flow = std::mem::replace(&mut self.loan_flow, flow);
                for (name, ty) in &parameters {
                    self.values.define(name.clone(), parameter_value(ty));
                }
                let returned = self.value(body);
                let returned_snapshot = self.resolved_value(&returned);
                self.values = outer_values;
                self.labels = outer_labels;
                self.loan_flow = outer_loan_flow;

                // Formation does not execute the body or insert hypothetical
                // external arguments into captured storage. Invocation applies
                // the shared relation using its real explicit/captured inputs.
                let frame_independent = capture_dependency_roots(&returned_snapshot).is_empty()
                    && self.continuations.label_independent(body)
                    && environment.captures.iter().all(|capture| {
                        !matches!(CaptureFormation::new(capture).source(), CaptureSource::Borrow(_))
                            && self.values.get(&capture.name).is_some_and(|value| frame_independent_value(&self.resolved_value(value)))
                    });
                let regions = environment.captures.iter().flat_map(|capture|
                    self.values.get(&capture.name).into_iter().flat_map(contained_regions))
                    .chain(contained_regions(&returned_snapshot)).collect();
                let resident_captures = environment.captures.iter().map(|capture| {
                    let formation = CaptureFormation::new(capture);
                    let value = match formation.source() {
                        CaptureSource::Borrow(_) => Value::Borrowed { root: capture.name.clone(),
                            storage: self.values.bindings.get(&capture.name).copied(), fields: vec![], capture_path: vec![] },
                        CaptureSource::Copy | CaptureSource::Move => self.values.get(&capture.name).cloned().unwrap_or(Value::None),
                    };
                    crate::resident_invocations::Operand { ty: formation.resident_type(), value }
                }).collect();
                let mut captures = environment
                    .captures
                    .into_iter()
                    .flat_map(|capture| {
                        let value = self
                            .values
                            .get(&capture.name)
                            .cloned()
                            .unwrap_or(Value::None);
                        let mut roots = BTreeSet::new();
                        for action in CaptureFormation::new(&capture).actions() {
                            match action {
                                CaptureAction::RetainContents => {
                                    let value = self.resolved_value(&value);
                                    roots.extend(capture_dependency_roots(&value));
                                }
                                CaptureAction::Source(CaptureSource::Borrow(_)) => { roots.insert(capture.name.clone()); }
                                CaptureAction::Source(CaptureSource::Copy | CaptureSource::Move) => {}
                            }
                        }
                        roots
                            .into_iter()
                            .map(|root| Capture::Borrowed {
                                root,
                                environment: environment.brand,
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                captures.extend(capture_dependency_roots(&returned_snapshot).into_iter().map(|root| {
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
                    resident_captures,
                    frame_independent,
                    regions,
                    controls,
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
                let callable = self.value(callee);
                if self.continuations.is_abrupt(callee) {
                    return Value::None;
                }
                let values = self.strict_values(arguments.clone());
                if values.len() == arguments.len() && arguments.iter().all(|argument| !self.continuations.is_abrupt(*argument)) {
                    self.record_invocation_stores(id, callee, callable.clone(), &arguments, &values, expression.span);
                    self.record_invocation_exits(id, &callable, &values, expression.span);
                    self.record_handler_inputs(id, &callable, &values, expression.span);
                }
                if mandatory_tail {
                    for (argument, value) in arguments.iter().zip(&values) {
                        if !frame_independent_value(&self.resolved_value(value))
                            && !crate::core::tail::tail_owned_type(self.signatures,
                                &self.body.expression(*argument).ty, &mut vec![]) {
                            self.error(self.body.expression(*argument).span, "G4403",
                                "mandatory `tail` argument may retain a reference, pointer, or callable environment dependent on the ending frame; its transfer provenance is not proven");
                        }
                    }
                }
                if self.continuations.is_abrupt(id) {
                    return Value::None;
                }
                self.invocation_result_value(id, &callable, values, reference_origin, reference_shape)
            }
            CoreKind::Perform { .. } => match self.performed_value(id) {
                Some(PerformedValue::Invoked { result, .. }) => result.unwrap_or(Value::None),
                Some(PerformedValue::PrefixExit) => Value::None,
                None => unreachable!("a performed Core node has an operation evaluation"),
            },
            CoreKind::Handle {
                computation,
                clauses,
            } => {
                // Capture the evaluated payload once, before the dynamic arm
                // split.  This gives every matching handler binder the exact
                // borrowed/external value that crossed the suspension rather
                // than re-evaluating argument Core in each arm.
                self.handler_inputs.push(HandlerInputs { computation, payloads: vec![] });
                let performed = self.performed_value(computation);
                let computed = match &performed {
                    Some(PerformedValue::Invoked { result, .. }) => result.clone().unwrap_or(Value::None),
                    Some(PerformedValue::PrefixExit) => Value::None,
                    None => self.value(computation),
                };
                let invoked = self.handler_inputs.pop().expect("protected computation inputs");
                let incoming = self.values.clone();
                // A handler may complete normally without selecting an
                // operation arm, so the computation is one of its dynamic
                // exits alongside every matching clause.
                let mut exits: Vec<_> = self.normal_exit(computation, computed).into_iter().collect();
                for clause in clauses {
                    self.values = incoming.clone();
                    if let Some(PerformedValue::Invoked { effect, operation, payloads, .. }) = &performed
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
                        let payloads = invoked.payloads.iter().filter(|(effect, operation, _)|
                            *effect == clause.effect && *operation == clause.operation)
                            .map(|(_, _, value)| value.clone()).collect::<Vec<_>>();
                        if !payloads.is_empty() {
                            let payload = join(payloads);
                            for (index, pattern) in clause.patterns.iter().enumerate() {
                                self.bind_pattern_value(pattern,
                                    value_at_path(&payload, &[index as u32]).unwrap_or(Value::None));
                            }
                        }
                    }
                    let resumption = if let crate::core::CoreHandlerResumption::Explicit { id, name, .. } = &clause.resumption {
                        self.values.define(name.clone(), Value::Control(ControlBrand::Resumption(*id)));
                        Some((*id, name.clone()))
                    } else { None };
                    let result = self.value(clause.body);
                    if let Some((id, name)) = resumption {
                        self.report_control_scope_escape(ControlBrand::Resumption(id), &result, &incoming, clause.span);
                        restore_bindings(&mut self.values, &incoming, [name]);
                    }
                    restore_bindings(&mut self.values, &incoming,
                        clause.bindings.iter().map(|(name, _)| name.clone()));
                    exits.extend(self.normal_exit(clause.body, result));
                }
                self.join_exits(&incoming, exits)
            }
            CoreKind::Completion {
                computation,
                clauses,
                refinement_test,
                ..
            } => {
                let subject = computation;
                let computation = self.value(computation);
                // Completion patterns run only after their strict subject
                // returns. Transfers already retained their own exit snapshots.
                if self.continuations.is_abrupt(subject) { return Value::None; }
                let incoming = self.values.clone();
                // Core admits a Completion only after its pattern matrix has
                // proved it exhaustive. Unlike an effect handler, normal
                // completion therefore cannot fall through with the original
                // subject as its result. Keeping that impossible exit made a
                // temporary `Option<&T>` look like the enclosing function's
                // return value even when every arm consumed the reference.
                let mut exits = Vec::with_capacity(clauses.len());
                for (index, clause) in clauses.into_iter().enumerate() {
                    self.values = incoming.clone();
                    self.bind_pattern_value(&clause.pattern, computation.clone());
                    if index == 0 && let Some(refinement) = &refinement_test {
                        let mut types = vec![];
                        let _ = crate::core::collect_pattern_binding_types(&clause.pattern,
                            &self.body.expression(subject).ty, &mut types);
                        for (name, ty) in types {
                            if crate::core::refinement_binding_type(ty.clone()) != ty {
                                let borrowed = self.refinement_borrowed_value(refinement.brand, &name, expression.span);
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
                                let borrowed = self.refinement_borrowed_value(refinement.environment.brand, &name, expression.span);
                                self.values.insert(name, borrowed);
                            }
                        }
                    }
                    let result = self.value(clause.body);
                    let mut bindings = BTreeSet::new();
                    pattern_bindings(&clause.pattern, &mut bindings);
                    if let Some(refinement) = &clause.refinement {
                        pattern_bindings(&refinement.pattern, &mut bindings);
                    }
                    restore_bindings(&mut self.values, &incoming, bindings);
                    exits.extend(self.normal_exit(clause.body, result));
                }
                self.join_exits(&incoming, exits)
            }
        };
        let value = if matches!(value, Value::None) {
            type_proven_value(self.signatures, &expression.ty).unwrap_or(value)
        } else { value };
        self.seed_logical_value(format!("<expression-{}>", id.0), &expression.ty, value)
    }

    fn normal_exit(&self, expression: CoreId, value: Value) -> Option<ValueExit> {
        // Unknown continuation coverage retains a possible normal result.
        // Only the bound shared continuation product can exclude this edge.
        (!self.continuations.is_abrupt(expression)).then(|| ValueExit {
            value, environment: self.values.clone(),
        })
    }

    fn join_exits(&mut self, incoming: &ValueEnvironment, exits: Vec<ValueExit>) -> Value {
        let (values, environments) = exits.into_iter()
            .map(|exit| (exit.value, exit.environment)).unzip();
        self.values = joined_environments(incoming, environments);
        join(values)
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
        references_complete: bool,
        span: Span,
        boundary: &str,
    ) -> Value {
        if origin.is_deferred() && !references_complete
            && matches!(shape, CallReferenceShape::OpaquePotentiallyReference)
            && !contains_open_type_parameter(result_ty) {
            self.error(span, "G5023", format!("reference-valued {boundary} has no complete frozen caller-region provenance"));
        }
        match origin {
            CallReferenceOrigin::None => type_proven_value(self.signatures, result_ty).unwrap_or(Value::None),
            CallReferenceOrigin::External => Value::ExternalBorrowed,
            // The raw-reference contract supplies validity independently of
            // local loans. Its selected lifetime is still checked by Core.
            CallReferenceOrigin::Unsafe => Value::ExternalBorrowed,
            CallReferenceOrigin::Paths(paths) | CallReferenceOrigin::Partial(paths) => {
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
                    let value = declared_reference(value);
                    let mut updated = result.clone();
                    if put_value_at_path(&mut updated, &path.result_fields, value.clone()) {
                        result = updated;
                    } else if type_has_variant_layout(self.signatures, result_ty, &mut BTreeSet::new()) {
                        let mut alternative = Value::None;
                        if put_value_at_path(&mut alternative, &path.result_fields, value) {
                            match &mut result {
                                Value::Alternatives(values) => values.push(alternative),
                                _ => result = Value::Alternatives(vec![result, alternative]),
                            }
                        } else {
                            self.error(span, "G5023", format!("reference-valued {boundary} has contradictory frozen result paths"));
                        }
                    } else {
                        self.error(span, "G5023", format!("reference-valued {boundary} has contradictory frozen result paths"));
                    }
                }
                seal_array_extents(self.signatures, result_ty, &mut result);
                result
            }
            CallReferenceOrigin::Opaque => type_proven_value(self.signatures, result_ty).unwrap_or(Value::None),
        }
    }

    /// Ordinary calls and evaluated top-level values consume the same bound
    /// normal-result relation; neither reconstructs an initializer's Core.
    fn invocation_result_value(&mut self, id: CoreId, callable: &Value, values: Vec<Value>,
        reference_origin: CallReferenceOrigin, reference_shape: CallReferenceShape) -> Value {
        let expression = self.body.expression(id);
        let resolved = self.continuations.invocation(id).map(|control|
            control.resolve_returns(&expression.ty, self.signatures, callable, &values, self));
        let mut callable_values = BTreeMap::<Vec<u32>, (Vec<Value>, Vec<crate::resident_invocations::Operand<Value>>)>::new();
        if let CoreKind::Call { callee, arguments, .. } = &expression.kind {
            let empty = BTreeSet::new();
            let noncapturing = resolved.as_ref().map_or(&empty, |result| &result.noncapturing_callables);
            for path in crate::placeflow::regions::callable_result_paths(self.signatures,
                self.body.expression(*callee), noncapturing) {
                let (Some(value), Some(argument)) = (values.get(path.argument as usize), arguments.get(path.argument as usize)) else { continue; };
                let Some(value) = self.reference_path_value(value, &path.argument_fields) else { continue; };
                let mut inputs = vec![];
                let _ = crate::core::input_reference_leaf_paths(self.signatures, &self.body.expression(*argument).ty, &mut inputs);
                let (footprint, captures) = callable_values.entry(path.result_fields).or_default();
                if let Some((_, ty)) = inputs.into_iter().find(|(fields, _)| crate::core::reference_path_matches(fields, &path.argument_fields)) {
                    captures.push(crate::resident_invocations::Operand { ty, value: value.clone() });
                }
                footprint.push(value);
            }
        }
        let references_complete = resolved.as_ref().is_some_and(|result| result.references.is_complete());
        let reference_paths = resolved.as_ref().into_iter().flat_map(|result| result.references.paths())
            .map(<[u32]>::to_vec).collect::<Vec<_>>();
        let empty_paths = resolved.as_ref().into_iter().flat_map(|result| result.references.empty_paths())
            .map(<[u32]>::to_vec).collect::<Vec<_>>();
        let returned = resolved.into_iter().flat_map(|result| result.payloads).filter_map(|payload|
            control::known_payload(payload, &self.values, &mut self.control_captures, self.signatures)).collect::<Vec<_>>();
        let targets = reference_paths.iter().map(|path| {
            let targets = (!returned.is_empty()).then(|| returned.iter().map(|value|
                reference_targets(&value_at_path(value, path)?)).collect::<Option<Vec<_>>>()).flatten().map(join);
            (path.clone(), targets)
        }).collect::<Vec<_>>();
        let mut result = if matches!(reference_origin, CallReferenceOrigin::Opaque) && references_complete { None }
            else { Some(self.reference_result_value(&reference_origin, reference_shape, &expression.ty,
                values, references_complete, expression.span, "call")) };
        for (path, (footprint, resident_captures)) in callable_values {
            let value = if resident_captures.is_empty() { join(footprint) }
                else { Value::CallableResident { footprint: Box::new(join(footprint)), resident_captures } };
            put_value_at_path(result.get_or_insert(Value::None), &path, value);
        }
        let mut result = join(result.into_iter().chain(returned).collect());
        for (path, targets) in targets {
            if !map_reference_path(&mut result, &path, &mut |value|
                authenticated_reference_with_targets(value, targets.clone())) {
                self.error(expression.span, "G5023", "authenticated invocation reference contradicts its retained result shape");
            }
        }
        for path in empty_paths {
            // Complete absence removes no declared lifetime debt. A sparse
            // reference-free contribution is a represented empty target.
            if !map_reference_path(&mut result, &path, &mut |value|
                if matches!(value, Value::None | Value::ReferenceFree) { Value::ReferenceFree }
                else { Value::Reference { dependencies: Box::new(value), targets: Some(Box::new(Value::ReferenceFree)), contents: None, authenticated: false } }) {
                self.error(expression.span, "G5023", "absent invocation reference contradicts its retained result shape");
            }
        }
        seal_array_extents(self.signatures, &expression.ty, &mut result);
        result
    }

    fn reference_path_value(&self, value: &Value, path: &[u32]) -> Option<Value> {
        Self::reference_path_value_in(value, path, &self.values)
    }

    fn reference_path_value_in(value: &Value, path: &[u32], values: &ValueEnvironment) -> Option<Value> {
        let Some(deref) = path.iter().position(|field| *field == crate::core::REFERENCE_PATH_DEREF) else {
            return value_at_path(value, path);
        };
        let reference = Self::resolved_value_in(&value_at_path(value, &path[..deref])?, values);
        let resident = match reference {
            Value::Logical { physical, .. } => return Self::reference_path_value_in(&physical, &path[deref..], values),
            Value::Reference { targets, contents, .. } => {
                if let Some(value) = targets.as_ref().and_then(|targets| Self::reference_path_value_in(targets, &path[deref..], values)) {
                    // Outside-frame is a storage class, not knowledge of
                    // every reference subsequently stored in that storage.
                    // A declared inner local loan must not disappear merely
                    // because the outer handle can point outside this frame.
                    if targets.as_ref().is_some_and(|targets| value_contains_external_reference(targets))
                        && let Some(contents) = contents {
                        return Some(join(vec![value, Self::reference_path_value_in(&contents, &path[deref + 1..], values)?]));
                    }
                    return Some(value);
                }
                return Self::reference_path_value_in(&*contents?, &path[deref + 1..], values);
            }
            Value::ExternalBorrowed => Value::ExternalBorrowed,
            Value::ReferenceFree => Value::ReferenceFree,
            Value::Borrowed { storage, fields, capture_path, .. } => {
                let owner = value_at_path(values.residents.get(&storage?)?, &fields)?;
                invocations::capture_value_at_path(&owner, &capture_path)?
            }
            Value::Joined(alternatives) | Value::Alternatives(alternatives) => return alternatives.iter().map(|value|
                Self::reference_path_value_in(value, &path[deref..], values)).collect::<Option<Vec<_>>>().map(join),
            _ => return None,
        };
        Self::reference_path_value_in(&resident, &path[deref + 1..], values)
    }

    /// Evaluate strict children in source order through their first abrupt
    /// exit.  The predicate comes from PlaceFlow's shared control classifier,
    /// so unreachable aggregate fields and arguments cannot publish later
    /// reference-escape facts.
    fn strict_values(&mut self, values: Vec<CoreId>) -> Vec<Value> {
        let mut evaluated = Vec::with_capacity(values.len());
        for value in values {
            evaluated.push(self.value(value));
            if self.continuations.is_abrupt(value) {
                break;
            }
        }
        evaluated
    }

    /// Evaluate a direct operation exactly once and retain both its payload
    /// values and frozen result provenance for the enclosing handler. `None`
    /// means this is not an operation, not that an operation failed to return.
    fn performed_value(
        &mut self,
        id: CoreId,
    ) -> Option<PerformedValue> {
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
        let invoked = arguments.iter().all(|argument| !self.continuations.is_abrupt(*argument));
        let values = self.strict_values(arguments);
        if !invoked {
            return Some(PerformedValue::PrefixExit);
        }
        for value in &values {
            self.report_suspension_escape(value, expression.span);
        }
        let result = (!self.continuations.is_abrupt(id)).then(|| self.reference_result_value(
            &reference_origin,
            reference_shape,
            &expression.ty,
            values.clone(),
            false,
            expression.span,
            "effect operation",
        ));
        Some(PerformedValue::Invoked { effect, operation, payloads: values, result })
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

    fn refinement_borrowed_value(&mut self, brand: crate::core::RefinementBrand, name: &str, span: Span) -> Value {
        let Some(access) = self.loan_flow.checked_refinement_borrow(brand, name) else {
            self.error(span, "G5016", "refinement borrow has no checked access in its frozen callable loan product");
            return Value::None;
        };
        self.borrowed_value(access)
    }

    fn borrowed_value(&mut self, access: crate::placeflow::CheckedBorrow) -> Value {
        let value = self.borrowed_subject_value(access.subject, access.temporary);
        project_borrowed_referent(value, &access.fields)
    }

    fn borrowed_subject_value(&mut self, id: CoreId, temporary: Option<CoreId>) -> Value {
        if let Some(value) = self.reborrowed_value(id) {
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
            if let Some(base) = temporary {
                let root = crate::placeflow::borrowed_temporary_root(base);
                // A real local storage owner, not an external/static loan.
                // Return, suspension and mandatory-tail checks still reject
                // any value that carries this root across its boundary.
                let storage = self.values.bindings.get(&root).copied();
                return Value::Borrowed { root, storage, fields, capture_path: vec![] };
            }
            self.error(
                self.body.expression(id).span,
                "G5013",
                "reference to a temporary cannot outlive the body that created it",
            );
            return Value::None;
        };
        let storage = self.values.bindings.get(&root).copied();
        Value::Borrowed { root, storage, fields, capture_path: vec![] }
    }

    /// A projected enum/record payload still belongs to the incoming loan.
    /// Field nodes sit between `&value.0` and the underlying `Deref(value)`,
    /// so checking only the immediate Core node mistakes a valid reborrow for
    /// a fresh temporary at the escape boundary.
    fn reborrowed_from_external(&mut self, id: CoreId) -> bool {
        match self.body.expression(id).kind.clone() {
            CoreKind::Field { base, .. } => self.reborrowed_from_external(base),
            CoreKind::Deref(reference) => {
                let value = self.value(reference);
                matches!(self.resolved_value(&value), Value::ExternalBorrowed)
            }
            _ => false,
        }
    }

    fn reborrowed_value(&mut self, id: CoreId) -> Option<Value> {
        match self.body.expression(id).kind.clone() {
            CoreKind::Field { base, index, .. } => self.reborrowed_value(base).map(|value| {
                project_borrowed_referent(value, &[index])
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
            CoreKind::Local(name) | CoreKind::Resumption { name, .. } => Some(name.clone()),
            CoreKind::Field { base, .. } => self.place_root(*base),
            // Reborrowing `&*parent` retains the parent loan's origin; the
            // dereference is a place projection, not a body-local temporary.
            CoreKind::Deref(reference) => match &self.body.expression(*reference).kind {
                CoreKind::Local(_) | CoreKind::Field { .. } => {
                    let value = self.value(*reference);
                    let mut roots = borrowed_roots(&self.resolved_value(&value)).into_iter();
                    let root = roots.next()?;
                    roots.next().is_none().then_some(root)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn assign(&mut self, place: CorePlace, value: Value, span: Span) {
        let resident_type = place.ty();
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
                        self.assign_reference_resident(reference, &fields, value, &resident_type, span);
                    }
                }
            }
            CorePlace::Deref { reference, .. } => {
                let reference = self.value(reference);
                self.assign_reference_resident(reference, &[], value, &resident_type, span);
            }
            CorePlace::Error => {}
        }
    }

    fn assign_reference_resident(&mut self, reference: Value, projected: &[u32], value: Value, ty: &Type, span: Span) {
        self.update_reference_resident(reference, projected, value, ty, span, true);
    }

    fn update_reference_resident(&mut self, reference: Value, projected: &[u32], value: Value, ty: &Type, span: Span, assignment: bool) {
        fn targets(reference: Value, projected: &[u32], result: &mut BTreeSet<(u64, Vec<u32>, Vec<crate::resident_invocations::CaptureProjection>)>) -> Option<bool> {
            match reference {
                Value::Borrowed { storage: Some(storage), mut fields, mut capture_path, .. } => {
                    if let Some(capture) = capture_path.last_mut() { capture.fields.extend_from_slice(projected); }
                    else { fields.extend_from_slice(projected); }
                    result.insert((storage, fields, capture_path));
                    Some(true)
                }
                Value::Joined(values) | Value::Alternatives(values) => {
                    let mut complete = (!values.is_empty()).then_some(true);
                    for value in values {
                        let incoming = targets(value, projected, result);
                        complete = complete.zip(incoming).map(|(left, right)| left && right);
                    }
                    complete
                }
                Value::Reference { targets: Some(referents), .. } => targets(*referents, projected, result),
                Value::Logical { physical, .. } => targets(*physical, projected, result),
                Value::ExternalBorrowed => Some(false),
                Value::ReferenceFree => Some(true),
                _ => None,
            }
        }
        let mut destinations = BTreeSet::new();
        let coverage = targets(self.resolved_value(&reference), projected, &mut destinations);
        if coverage.is_none() && !crate::core::tail::tail_owned_type(self.signatures, ty, &mut vec![]) {
            self.error(span, "G5021", "reference-containing assignment has unresolved referent storage");
        }
        let exact = assignment && coverage == Some(true) && destinations.len() == 1;
        for (storage, fields, capture_path) in destinations {
            let Some(resident) = self.values.residents.get_mut(&storage) else { continue; };
            if !capture_path.is_empty() {
                if !invocations::replace_capture_value_at_path(resident, &fields, &capture_path, value.clone(), exact, !assignment)
                    && !crate::core::tail::tail_owned_type(self.signatures, ty, &mut vec![]) {
                    self.error(span, "G5021", "capture storage assignment lacks its sealed resident projection");
                }
                continue;
            }
            if !assignment {
                if !weak_reference_write_path(resident, &fields, value.clone()) {
                    self.error(span, "G5021", "invocation write contradicts its declared resident path");
                }
                continue;
            }
            let replacement = if exact { value.clone() }
                else { join(vec![value_at_path(resident, &fields).unwrap_or(Value::None), value.clone()]) };
            if !replace_resident_path(resident, &fields, replacement)
                && !crate::core::tail::tail_owned_type(self.signatures, ty, &mut vec![]) {
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
                let value = self.value(*reference);
                let resolved = self.resolved_value(&value);
                value_contains_external_reference(&reference_targets(&resolved).unwrap_or(resolved))
            }
        }
    }

    fn report_return_escape(&mut self, value: &Value, span: Span) {
        let resolved = self.resolved_value(value);
        let value = &resolved;
        self.report_control_value_escape(value, span, "the callable result");
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
        let resolved = self.resolved_value(value);
        let value = &resolved;
        self.report_control_value_escape(value, span, "a runtime effect payload");
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
        let resolved = self.resolved_value(value);
        let value = &resolved;
        self.report_control_value_escape(value, span, "caller-owned storage");
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
    if let Value::Alternatives(values) = value {
        let mut assigned = false;
        for value in values {
            let mut updated = value.clone();
            if assign_field_path(&mut updated, path, replacement.clone()) { *value = updated; assigned = true; }
        }
        return assigned;
    }
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
        while let Value::Logical { physical, .. } = current { current = physical; }
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
        if let Value::Projected { fallback, fields } = current {
            if fields.keys().any(|field| *field >= *field_count) { return false; }
            *current = Value::Aggregate((0..*field_count)
                .map(|field| fields.get(&field).unwrap_or(fallback).clone()).collect());
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

/// Reborrowing selects referents, not retained loan/region dependencies.
/// Keep the logical graph live so a later store remains visible through the
/// projected reference. Explicit, refinement and invocation borrows share it.
fn project_borrowed_referent(value: Value, fields: &[u32]) -> Value {
    if fields.is_empty() { return value; }
    match value {
        Value::Reference { dependencies, targets, contents, authenticated } => Value::Reference {
            dependencies, targets: targets.map(|targets| Box::new(project_borrowed_referent(*targets, fields))),
            contents: contents.and_then(|contents| value_at_path(&contents, fields)).map(Box::new), authenticated,
        },
        Value::Borrowed { root, storage, fields: mut prefix, mut capture_path } => {
            if let Some(capture) = capture_path.last_mut() { capture.fields.extend_from_slice(fields); }
            else { prefix.extend_from_slice(fields); }
            Value::Borrowed { root, storage, fields: prefix, capture_path }
        }
        Value::Joined(values) => join(values.into_iter().map(|value| project_borrowed_referent(value, fields)).collect()),
        Value::Alternatives(values) => Value::Alternatives(values.into_iter().map(|value| project_borrowed_referent(value, fields)).collect()),
        Value::Logical { physical, arguments } => Value::Logical {
            physical: Box::new(project_borrowed_referent(*physical, fields)), arguments,
        },
        value => value,
    }
}

#[cfg(test)]
fn authenticated_reference(value: Value) -> Value {
    let targets = reference_targets(&value);
    authenticated_reference_with_targets(value, targets)
}

fn reference_targets(value: &Value) -> Option<Value> {
    match value {
        Value::Reference { targets, .. } => targets.as_deref().cloned(),
        Value::Borrowed { .. } | Value::ExternalBorrowed | Value::ReferenceFree => Some(value.clone()),
        Value::Logical { physical, .. } => reference_targets(physical),
        Value::Joined(values) | Value::Alternatives(values) if !values.is_empty() =>
            values.iter().map(reference_targets).collect::<Option<Vec<_>>>().map(join),
        _ => None,
    }
}

fn declared_reference(value: Value) -> Value {
    if matches!(value, Value::ReferenceFree) { return value; }
    fn entirely_external(value: &Value) -> bool {
        match value {
            Value::ExternalBorrowed => true,
            Value::ReferenceFree => true,
            Value::Reference { targets: Some(targets), .. } => entirely_external(targets),
            Value::Joined(values) | Value::Alternatives(values) =>
                !values.is_empty() && values.iter().all(entirely_external),
            _ => false,
        }
    }
    // Outside-this-frame is a storage class, not an exact caller address.
    // A declaration forwarding only external referents preserves that class;
    // any local, absent or unknown alternative still loses target coverage.
    let targets = entirely_external(&value).then(|| Box::new(Value::ExternalBorrowed));
    Value::Reference { dependencies: Box::new(value), targets, contents: None, authenticated: false }
}

fn authenticated_reference_with_targets(value: Value, targets: Option<Value>) -> Value {
    let contents = declared_reference_contents(&value);
    if matches!(value, Value::ReferenceFree) { return value; }
    // Repeated forwarding preserves one proof wrapper and the complete loan
    // union instead of nesting a new wrapper around each earlier invocation.
    fn dependencies(value: Value) -> Value {
        match value {
            Value::Reference { dependencies: value, .. } => dependencies(*value),
            Value::Joined(values) => join(values.into_iter().map(dependencies).collect()),
            value => value,
        }
    }
    Value::Reference { dependencies: Box::new(dependencies(value)), targets: targets.map(Box::new), contents: contents.map(Box::new), authenticated: true }
}

fn declared_reference_contents(value: &Value) -> Option<Value> {
    match value {
        Value::Reference { contents, .. } => contents.as_deref().cloned(),
        Value::Logical { physical, .. } => declared_reference_contents(physical),
        Value::Joined(values) | Value::Alternatives(values) if !values.is_empty() =>
            values.iter().map(declared_reference_contents).collect::<Option<Vec<_>>>().map(join),
        _ => None,
    }
}

/// Apply a path authenticated by the bound invocation product to this result
/// snapshot. Sparse declaration footprints are not alternative runtime values:
/// a missing shell may retain unknown dependencies while the actual reference
/// leaf has separately been proved on every normal result. No loan is removed.
#[cfg(test)]
fn authenticate_reference_path(value: &mut Value, path: &[u32]) -> bool {
    map_reference_path(value, path, &mut authenticated_reference)
}

fn map_reference_path(value: &mut Value, path: &[u32], transform: &mut impl FnMut(Value) -> Value) -> bool {
    if matches!(value, Value::ReferenceFree) { return true; }
    let Some((field, tail)) = path.split_first() else {
        *value = transform(std::mem::replace(value, Value::None));
        return true;
    };
    match value {
        Value::Joined(values) | Value::Alternatives(values) =>
            return values.iter_mut().all(|value| map_reference_path(value, path, transform)),
        Value::ExternalBorrowed => return true,
        _ => {},
    }
    if *field == crate::core::REFERENCE_PATH_LOGICAL_ARGUMENT {
        let Some((argument, tail)) = tail.split_first() else { return false; };
        if !matches!(value, Value::Logical { .. }) {
            *value = Value::Logical { physical: Box::new(std::mem::replace(value, Value::None)), arguments: BTreeMap::new() };
        }
        let Value::Logical { arguments, .. } = value else { unreachable!() };
        return map_reference_path(arguments.entry(*argument).or_insert(Value::None), tail, transform);
    }
    if let Value::Logical { physical, .. } = value {
        return map_reference_path(physical, path, transform);
    }
    if *field == crate::core::REFERENCE_PATH_ARRAY_ELEMENT {
        if matches!(value, Value::None) {
            *value = Value::Array { length: None, element: Box::new(Value::None), fields: BTreeMap::new() };
        }
        return match value {
            Value::Array { element, fields, .. } => map_reference_path(element, tail, transform)
                && fields.values_mut().all(|value| map_reference_path(value, tail, transform)),
            Value::Projected { fallback, fields } => map_reference_path(fallback, tail, transform)
                && fields.values_mut().all(|value| map_reference_path(value, tail, transform)),
            Value::Aggregate(values) => values.iter_mut().all(|value| map_reference_path(value, tail, transform)),
            _ => false,
        };
    }
    if *field == crate::core::REFERENCE_PATH_DEREF { return false; }
    if let Value::Projected { fallback, fields } = value {
        return map_reference_path(fields.entry(*field).or_insert_with(|| (**fallback).clone()), tail, transform);
    }
    if matches!(value, Value::None) { *value = Value::Aggregate(vec![]); }
    let Value::Aggregate(fields) = value else {
        if let Value::Variant(fields) = value {
            return fields.get_mut(*field as usize).is_none_or(|value| map_reference_path(value, tail, transform));
        }
        return false;
    };
    fields.resize(fields.len().max(*field as usize + 1), Value::None);
    map_reference_path(&mut fields[*field as usize], tail, transform)
}

fn replace_resident_path(target: &mut Value, path: &[u32], replacement: Value) -> bool {
    if let Value::Alternatives(values) = target {
        let mut assigned = false;
        for value in values {
            let mut updated = value.clone();
            if replace_resident_path(&mut updated, path, replacement.clone()) { *value = updated; assigned = true; }
        }
        return assigned;
    }
    let Some((field, tail)) = path.split_first() else { *target = replacement; return true; };
    if let Value::Joined(values) = target {
        return values.iter_mut().all(|value| replace_resident_path(value, path, replacement.clone()));
    }
    if *field == crate::core::REFERENCE_PATH_LOGICAL_ARGUMENT {
        let Some((argument, tail)) = tail.split_first() else { return false; };
        if !matches!(target, Value::Logical { .. }) {
            let physical = Box::new(std::mem::replace(target, Value::None));
            *target = Value::Logical { physical, arguments: BTreeMap::new() };
        }
        let Value::Logical { arguments, .. } = target else { unreachable!() };
        return replace_resident_path(arguments.entry(*argument).or_insert(Value::None), tail, replacement);
    }
    if let Value::Logical { physical, .. } = target {
        return replace_resident_path(physical, path, replacement);
    }
    if matches!(*field, crate::core::REFERENCE_PATH_ARRAY_ELEMENT | crate::core::REFERENCE_PATH_DEREF) { return false; }
    if matches!(target, Value::ExternalBorrowed | Value::FrameIndependent) {
        // A typed projection of an opaque incoming carrier must preserve the
        // provenance of its untouched fields. Do not create a second sparse
        // alternative whose invented holes contaminate the same parameter.
        *target = Value::Projected {
            fallback: Box::new(std::mem::replace(target, Value::None)),
            fields: BTreeMap::new(),
        };
    }
    if let Value::Projected { fallback, fields } = target {
        return replace_resident_path(fields.entry(*field).or_insert_with(|| (**fallback).clone()), tail, replacement);
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

/// Apply a declaration-authorized possible write, rather than asserting that
/// this projection exists in the current runtime variant. Its callee may
/// replace the enclosing variant, so the resident becomes a joined projection
/// footprint. Ordinary source assignments still use strict replacement above.
/// At the written leaf, preserve every debt and revoke exact target evidence.
fn weak_reference_write_path(target: &mut Value, path: &[u32], source: Value) -> bool {
    fn write(target: &mut Value, path: &[u32], source: Value, mut variant: bool) -> bool {
        let Some((field, tail)) = path.split_first() else {
            *target = declared_reference(join(vec![std::mem::replace(target, Value::None), source]));
            return true;
        };
        if matches!(target, Value::ExternalBorrowed) {
            *target = Value::Projected { fallback: Box::new(Value::ExternalBorrowed), fields: BTreeMap::new() };
        }
        match target {
            Value::Logical { physical, .. } => return write(physical, path, source, variant),
            Value::Joined(values) | Value::Alternatives(values) =>
                return values.iter_mut().all(|value| write(value, path, source.clone(), variant)),
            _ => {},
        }
        if matches!(*field, crate::core::REFERENCE_PATH_LOGICAL_ARGUMENT | crate::core::REFERENCE_PATH_DEREF) { return false; }
        if let Value::Variant(fields) = target {
            // The old tag no longer proves an absent field. Existing payload
            // debts survive in the same structural snapshot.
            *target = Value::Aggregate(std::mem::take(fields));
            variant = true;
        }
        if *field == crate::core::REFERENCE_PATH_ARRAY_ELEMENT {
            if matches!(target, Value::None | Value::ReferenceFree) {
                *target = Value::Array { length: None, element: Box::new(std::mem::replace(target, Value::None)), fields: BTreeMap::new() };
            }
            return match target {
                Value::Array { element, fields, .. } => write(element, tail, source.clone(), variant)
                    && fields.values_mut().all(|value| write(value, tail, source.clone(), variant)),
                Value::Projected { fallback, fields } => write(fallback, tail, source.clone(), variant)
                    && fields.values_mut().all(|value| write(value, tail, source.clone(), variant)),
                Value::Aggregate(fields) => fields.iter_mut().all(|value| write(value, tail, source.clone(), variant)),
                _ => false,
            };
        }
        if let Value::Array { length, element, fields } = target {
            if length.is_some_and(|length| u64::from(*field) >= length) { return false; }
            return write(fields.entry(*field).or_insert_with(|| (**element).clone()), tail, source, variant);
        }
        if let Value::Projected { fallback, fields } = target {
            return write(fields.entry(*field).or_insert_with(|| (**fallback).clone()), tail, source, variant);
        }
        if matches!(target, Value::None | Value::ReferenceFree) {
            variant = matches!(target, Value::ReferenceFree);
            *target = Value::Aggregate(vec![]);
        }
        let Value::Aggregate(fields) = target else { return false; };
        fields.resize(fields.len().max(*field as usize + 1), if variant { Value::ReferenceFree } else { Value::None });
        write(&mut fields[*field as usize], tail, source, variant)
    }
    write(target, path, source, false)
}

fn value_at_variant_path(value: &Value, path: &[u32], known_variant: bool) -> Option<Value> {
    if matches!(value, Value::ReferenceFree) { return Some(Value::ReferenceFree); }
    if let Value::Alternatives(values) = value {
        // A choice does not itself prove a variant constructor, and an
        // unrepresented alternative cannot disappear from path coverage.
        return values.iter().map(|value| value_at_variant_path(value, path, known_variant))
            .collect::<Option<Vec<_>>>().map(join);
    }
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
    if let Value::Logical { physical, arguments } = value {
        if *field == crate::core::REFERENCE_PATH_LOGICAL_ARGUMENT {
            let (argument, tail) = tail.split_first()?;
            return value_at_variant_path(arguments.get(argument).unwrap_or(&Value::None), tail, known_variant);
        }
        return value_at_variant_path(physical, path, known_variant);
    }
    // A represented constructor has no extra logical debt before its region
    // is connected to incoming residents. Its evaluated physical fields still
    // carry every borrow. Keep that empty contribution distinct from unknown
    // provenance; neither establishes a reference's validity or referent.
    // An independently frame-owned generic carrier preserves only that weaker
    // boundary proof. An unresolved value still contributes unknown evidence.
    if crate::core::reference_path_is_logical(path)
        && (matches!(value, Value::None | Value::FrameIndependent)
            || *field == crate::core::REFERENCE_PATH_LOGICAL_ARGUMENT) {
        return Some(match value {
            Value::Aggregate(_) | Value::Variant(_) => Value::ReferenceFree,
            Value::FrameIndependent => Value::FrameIndependent,
            _ => Value::None,
        });
    }
    if let Value::Projected { fallback, fields } = value {
        if *field == crate::core::REFERENCE_PATH_ARRAY_ELEMENT {
            return projected_values(fallback, fields)
                .map(|value| value_at_variant_path(value, tail, known_variant))
                .collect::<Option<Vec<_>>>().map(join);
        }
        if *field == crate::core::REFERENCE_PATH_DEREF { return None; }
        return value_at_variant_path(fields.get(field).unwrap_or(fallback), tail, known_variant);
    }
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
        return known_variant.then_some(Value::ReferenceFree);
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
    if path[0] == crate::core::REFERENCE_PATH_LOGICAL_ARGUMENT {
        let Some((argument, tail)) = path[1..].split_first() else { return false; };
        if !matches!(target, Value::Logical { .. }) {
            let physical = Box::new(std::mem::replace(target, Value::None));
            *target = Value::Logical { physical, arguments: BTreeMap::new() };
        }
        let Value::Logical { arguments, .. } = target else { unreachable!() };
        return put_value_at_path(arguments.entry(*argument).or_insert(Value::None), tail, replacement);
    }
    if let Value::Logical { physical, .. } = target { return put_value_at_path(physical, path, replacement); }
    if path[0] == crate::core::REFERENCE_PATH_DEREF {
        if let Value::Joined(values) | Value::Alternatives(values) = target {
            return values.iter_mut().all(|value| put_value_at_path(value, path, replacement.clone()));
        }
        if !matches!(target, Value::Reference { .. }) {
            *target = declared_reference(std::mem::replace(target, Value::None));
        }
        let Value::Reference { dependencies, contents, .. } = target else { return false; };
        // Loaded residents retain their own lifetime debts. The containing
        // reference must also retain those debts before any load occurs.
        **dependencies = join(vec![(**dependencies).clone(), replacement.clone()]);
        return put_value_at_path(contents.get_or_insert_with(|| Box::new(Value::None)), &path[1..], replacement);
    }
    if let Value::Projected { fallback, fields } = target {
        if path[0] == crate::core::REFERENCE_PATH_ARRAY_ELEMENT {
            return put_value_at_path(fallback, &path[1..], replacement.clone())
                && fields.values_mut().all(|value| put_value_at_path(value, &path[1..], replacement.clone()));
        }
        if path[0] == crate::core::REFERENCE_PATH_DEREF { return false; }
        return put_value_at_path(fields.entry(path[0]).or_insert_with(|| (**fallback).clone()), &path[1..], replacement);
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

fn projected_values<'a>(fallback: &'a Value, fields: &'a BTreeMap<u32, Value>) -> impl Iterator<Item = &'a Value> {
    std::iter::once(fallback).chain(fields.values())
}

fn array_values<'a>(length: Option<u64>, element: &'a Value, fields: &'a BTreeMap<u32, Value>)
    -> impl Iterator<Item = &'a Value>
{
    (!length.is_some_and(|length| length == fields.len() as u64)).then_some(element)
        .into_iter().chain(fields.values())
}

fn seal_array_extents(signatures: &crate::ElaboratedInterface, ty: &Type, value: &mut Value) {
    if let Value::Alternatives(values) | Value::Joined(values) = value {
        for value in values { seal_array_extents(signatures, ty, value); }
        return;
    }
    if let Value::Logical { physical, arguments: residents } = value {
        if let Type::Nominal { arguments, .. } = ty {
            for (index, resident) in residents {
                if let Some(GenericArgument::Type(ty)) = arguments.get(*index as usize) {
                    seal_array_extents(signatures, ty, resident);
                }
            }
        }
        seal_array_extents(signatures, ty, physical);
        return;
    }
    if let (Type::FixedArray { .. }, Value::Projected { fallback, fields }) = (ty, &mut *value) {
        *value = Value::Array { length: ty.fixed_array_length(),
            element: std::mem::replace(fallback, Box::new(Value::None)), fields: std::mem::take(fields) };
    }
    match (ty, value) {
        (Type::FixedArray { element: ty, length }, Value::Array { length: extent, element, fields }) => {
            *extent = Type::FixedArray { element: ty.clone(), length: length.clone() }.fixed_array_length();
            seal_array_extents(signatures, ty, element);
            for value in fields.values_mut() { seal_array_extents(signatures, ty, value); }
        }
        (Type::Tuple(types), Value::Aggregate(fields)) => {
            for (ty, value) in types.iter().zip(fields) { seal_array_extents(signatures, ty, value); }
        }
        (Type::Nominal { definition, arguments }, Value::Aggregate(fields)) => {
            let Ok(types) = signatures.instantiate_struct_fields_generic(*definition, arguments) else { return; };
            for (ty, value) in types.iter().zip(fields) {
                seal_array_extents(signatures, &ty.ty, value);
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
    let mut regions = incoming.regions.clone();
    for exit in &exits { regions.merge_from(&exit.regions, merge_region_values); }
    ValueEnvironment {
        bindings: incoming.bindings.clone(),
        next: exits.iter().map(|exit| exit.next).max().unwrap_or(incoming.next),
        residents: identities.into_iter().map(|identity| (identity, join(exits.iter()
            .filter_map(|exit| exit.residents.get(&identity).cloned()).collect()))).collect(),
        regions,
    }
}

fn merge_region_values(target: &mut Value, incoming: Value) {
    if *target != incoming { *target = join(vec![std::mem::replace(target, Value::None), incoming]); }
}

fn logical_regions(value: &Value) -> BTreeSet<crate::placeflow::regions::Region> {
    match value {
        Value::Reference { dependencies, .. } => logical_regions(dependencies),
        Value::Region(regions) => regions.clone(),
        Value::Aggregate(values) | Value::Variant(values) | Value::Alternatives(values) | Value::Joined(values) =>
            values.iter().flat_map(logical_regions).collect(),
        Value::Logical { physical, arguments } => logical_regions(physical).into_iter()
            .chain(arguments.values().flat_map(logical_regions)).collect(),
        Value::Array { length, element, fields } => array_values(*length, element, fields).flat_map(logical_regions).collect(),
        Value::Projected { fallback, fields } => projected_values(fallback, fields).flat_map(logical_regions).collect(),
        _ => BTreeSet::new(),
    }
}

/// Captured owner regions remain live dependencies, not aliases of the
/// callable's own resident slot. Only an actual store connects their contents.
fn contained_regions(value: &Value) -> BTreeSet<crate::placeflow::regions::Region> {
    match value {
        Value::Reference { dependencies, .. } => contained_regions(dependencies),
        Value::Closure { regions, .. } => regions.clone(),
        Value::CallableResident { footprint, resident_captures } => contained_regions(footprint).into_iter()
            .chain(resident_captures.iter().flat_map(|operand| contained_regions(&operand.value))).collect(),
        Value::Aggregate(values) | Value::Variant(values) | Value::Alternatives(values) | Value::Joined(values) =>
            values.iter().flat_map(contained_regions).collect(),
        Value::Logical { physical, arguments } => contained_regions(physical).into_iter()
            .chain(arguments.values().flat_map(contained_regions)).collect(),
        Value::Array { length, element, fields } => array_values(*length, element, fields).flat_map(contained_regions).collect(),
        Value::Projected { fallback, fields } => projected_values(fallback, fields).flat_map(contained_regions).collect(),
        _ => logical_regions(value),
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

fn type_has_variant_layout(signatures: &crate::ElaboratedInterface, ty: &Type, active: &mut BTreeSet<crate::DefKey>) -> bool {
    match ty {
        Type::Tuple(fields) => fields.iter().any(|field| type_has_variant_layout(signatures, field, active)),
        Type::FixedArray { element, .. } => type_has_variant_layout(signatures, element, active),
        Type::Nominal { definition, arguments } if active.insert(*definition) => {
            let has = match signatures.definitions.get(definition) {
                Some(crate::ElaboratedHeader::Nominal { layout: crate::ElaboratedNominalLayout::Enum(_), .. }) => true,
                Some(crate::ElaboratedHeader::Nominal { layout: crate::ElaboratedNominalLayout::Struct(_)
                    | crate::ElaboratedNominalLayout::TupleStruct(_), .. }) => signatures
                        .instantiate_struct_fields_generic(*definition, arguments).is_ok_and(|fields|
                            fields.iter().any(|field| type_has_variant_layout(signatures, &field.ty, active))),
                _ => false,
            };
            active.remove(definition);
            has
        }
        _ => false,
    }
}

fn frame_independent_value(value: &Value) -> bool {
    match value {
        Value::Reference { dependencies, .. } => frame_independent_value(dependencies),
        Value::Region(_) => unreachable!("logical region must be resolved before checking a boundary"),
        Value::ReferenceFree | Value::FrameIndependent | Value::ExternalBorrowed => true,
        Value::Aggregate(values) | Value::Variant(values) | Value::Alternatives(values) | Value::Joined(values) => {
            values.iter().all(frame_independent_value)
        }
        Value::Array { length, element, fields } =>
            array_values(*length, element, fields).all(frame_independent_value),
        Value::Projected { fallback, fields } => projected_values(fallback, fields).all(frame_independent_value),
        Value::Logical { physical, arguments } => frame_independent_value(physical)
            && arguments.values().all(frame_independent_value),
        Value::Closure { frame_independent, controls, .. } => *frame_independent && controls.is_empty(),
        Value::CallableResident { footprint, .. } => frame_independent_value(footprint),
        Value::None | Value::Control(_) | Value::Borrowed { .. } => false,
    }
}

fn borrowed_roots(value: &Value) -> BTreeSet<String> {
    let mut roots = BTreeSet::new();
    collect_borrowed_roots(value, &mut roots);
    roots
}

/// Capturing a value retains both its physical loans and dependencies already
/// carried by nested callable environments, including inside aggregates.
fn capture_dependency_roots(value: &Value) -> BTreeSet<String> {
    let mut roots = borrowed_roots(value);
    roots.extend(closure_captures(value).into_iter().map(|capture| match capture {
        Capture::Borrowed { root, .. } => root,
    }));
    roots
}

fn collect_borrowed_roots(value: &Value, roots: &mut BTreeSet<String>) {
    match value {
        Value::Reference { dependencies, .. } => collect_borrowed_roots(dependencies, roots),
        Value::Region(_) => unreachable!("logical region must be resolved before checking a boundary"),
        Value::Borrowed { root, .. } => {
            roots.insert(root.clone());
        }
        Value::Aggregate(values) | Value::Variant(values) | Value::Alternatives(values) | Value::Joined(values) => {
            for value in values {
                collect_borrowed_roots(value, roots);
            }
        }
        Value::Array { length, element, fields } => {
            for value in array_values(*length, element, fields) { collect_borrowed_roots(value, roots); }
        }
        Value::Projected { fallback, fields } => {
            for value in projected_values(fallback, fields) { collect_borrowed_roots(value, roots); }
        }
        Value::Logical { physical, arguments } => {
            collect_borrowed_roots(physical, roots);
            for value in arguments.values() { collect_borrowed_roots(value, roots); }
        }
        Value::CallableResident { footprint, .. } => collect_borrowed_roots(footprint, roots),
        Value::Closure { .. } | Value::None | Value::ReferenceFree | Value::Control(_) | Value::FrameIndependent | Value::ExternalBorrowed => {}
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
        Value::Reference { dependencies, .. } => value_contains_external_reference(dependencies),
        Value::Region(_) => unreachable!("logical region must be resolved before checking a boundary"),
        Value::ExternalBorrowed => true,
        Value::Aggregate(values) | Value::Variant(values) | Value::Alternatives(values) | Value::Joined(values) => {
            values.iter().any(value_contains_external_reference)
        }
        Value::Array { length, element, fields } =>
            array_values(*length, element, fields).any(value_contains_external_reference),
        Value::Projected { fallback, fields } => projected_values(fallback, fields).any(value_contains_external_reference),
        Value::Logical { physical, arguments } => value_contains_external_reference(physical)
            || arguments.values().any(value_contains_external_reference),
        Value::CallableResident { footprint, .. } => value_contains_external_reference(footprint),
        Value::None | Value::ReferenceFree | Value::Control(_) | Value::FrameIndependent | Value::Borrowed { .. } | Value::Closure { .. } => false,
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
        Value::Reference { dependencies, .. } => collect_closure_captures(dependencies, captures),
        Value::Region(_) => unreachable!("logical region must be resolved before checking a boundary"),
        Value::Closure {
            captures: values, ..
        } => captures.extend(values.clone()),
        Value::CallableResident { footprint, .. } => collect_closure_captures(footprint, captures),
        Value::Aggregate(values) | Value::Variant(values) | Value::Alternatives(values) | Value::Joined(values) => {
            for value in values {
                collect_closure_captures(value, captures);
            }
        }
        Value::Array { length, element, fields } => {
            for value in array_values(*length, element, fields) { collect_closure_captures(value, captures); }
        }
        Value::Projected { fallback, fields } => {
            for value in projected_values(fallback, fields) { collect_closure_captures(value, captures); }
        }
        Value::Logical { physical, arguments } => {
            collect_closure_captures(physical, captures);
            for value in arguments.values() { collect_closure_captures(value, captures); }
        }
        Value::None | Value::ReferenceFree | Value::Control(_) | Value::FrameIndependent | Value::ExternalBorrowed | Value::Borrowed { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn declared_resident_contents_keep_debt_without_creating_a_storage_target() {
        use super::*;
        let loan = |name: &str| Value::Borrowed { root: name.into(), storage: Some(1), fields: vec![], capture_path: vec![] };
        let mut value = declared_reference(loan("carrier"));
        let resident = declared_reference(loan("resident"));
        assert!(put_value_at_path(&mut value, &[crate::core::REFERENCE_PATH_DEREF, 0], resident.clone()));
        assert_eq!(declared_reference_contents(&value), Some(Value::Aggregate(vec![resident])));
        assert_eq!(borrowed_roots(&value), BTreeSet::from(["carrier".into(), "resident".into()]));
        assert!(!frame_independent_value(&value));
        assert!(reference_targets(&value).is_none());
        let authenticated = authenticated_reference(value.clone());
        assert_eq!(declared_reference_contents(&authenticated), declared_reference_contents(&value));
        assert!(reference_targets(&authenticated).is_none());
        assert!(declared_reference_contents(&join(vec![value, Value::None])).is_none());

        let mut external = declared_reference(Value::ExternalBorrowed);
        assert!(put_value_at_path(&mut external, &[crate::core::REFERENCE_PATH_DEREF], loan("local")));
        assert_eq!(reference_targets(&external), Some(Value::ExternalBorrowed));
        assert_eq!(borrowed_roots(&external), BTreeSet::from(["local".into()]));
        assert!(!frame_independent_value(&external));
        let deref = [crate::core::REFERENCE_PATH_DEREF];
        let loaded = Analyzer::reference_path_value_in(&external, &deref, &ValueEnvironment::default()).unwrap();
        assert_eq!(borrowed_roots(&loaded), BTreeSet::from(["local".into()]));
        assert!(!frame_independent_value(&loaded), "an outside-frame address cannot erase an inner local debt");

        let mut values = ValueEnvironment::default();
        values.residents.insert(1, Value::ExternalBorrowed);
        let exact = Value::Reference { dependencies: Box::new(loan("slot")),
            targets: Some(Box::new(loan("slot"))), contents: Some(Box::new(loan("old"))), authenticated: true };
        let loaded = Analyzer::reference_path_value_in(&exact, &deref, &values).unwrap();
        assert_eq!(loaded, Value::ExternalBorrowed,
            "an exact live slot must be read after replacement, not from an old declaration snapshot");
    }

    #[test]
    fn logical_region_cycles_retain_grounded_evidence_and_reject_missing_contents() {
        use super::*;
        let region = |index| crate::placeflow::regions::Region { site: "cycle".into(), path: vec![index] };
        let first = region(0);
        let second = region(1);
        let missing = region(2);
        let reference = |region: &crate::placeflow::regions::Region| Value::Region([region.clone()].into());
        let mut values = ValueEnvironment::default();
        values.regions.connect(&[first.clone(), second.clone()].into());
        values.regions.insert(first.clone(), reference(&second), merge_region_values);
        values.regions.insert(second.clone(), reference(&first), merge_region_values);
        assert_eq!(Analyzer::resolved_value_in(&reference(&first), &values), Value::None,
            "a cycle without grounded contents cannot prove absence or independence");
        values.regions.insert(first.clone(), Value::ExternalBorrowed, merge_region_values);
        assert_eq!(Analyzer::resolved_value_in(&reference(&second), &values), Value::ExternalBorrowed);

        let mut incomplete = values.clone();
        incomplete.regions.connect(&[first.clone(), missing].into());
        let incomplete = Analyzer::resolved_value_in(&reference(&first), &incomplete);
        assert!(!frame_independent_value(&incomplete));
        assert!(!invocations::reference_is_known(&incomplete));

        let local = Value::Borrowed { root: "later".into(), storage: Some(1), fields: vec![], capture_path: vec![] };
        values.regions.insert(second, local, merge_region_values);
        let resolved = Analyzer::resolved_value_in(&reference(&first), &values);
        assert!(!frame_independent_value(&resolved));
        assert_eq!(borrowed_roots(&resolved), BTreeSet::from(["later".into()]));
    }

    #[test]
    fn logical_constructor_debt_is_empty_without_erasing_physical_or_later_loans() {
        use super::*;
        let path = [crate::core::REFERENCE_PATH_LOGICAL_ARGUMENT, 0];
        let local = Value::Borrowed { root: "local".into(), storage: Some(1), fields: vec![], capture_path: vec![] };
        let constructed = Value::Variant(vec![local.clone()]);
        let empty = value_at_path(&constructed, &path).unwrap();
        assert_eq!(empty, Value::ReferenceFree);
        assert!(!invocations::reference_is_known(&empty));
        assert!(!frame_independent_value(&constructed));
        assert_eq!(borrowed_roots(&constructed), BTreeSet::from(["local".into()]));
        assert_eq!(value_at_path(&Value::None, &path), Some(Value::None));
        assert_eq!(value_at_path(&Value::FrameIndependent, &path), Some(Value::FrameIndependent));

        let region = crate::placeflow::regions::Region { site: "constructor".into(), path: path.to_vec() };
        let mut values = ValueEnvironment::default();
        values.regions.insert(region.clone(), empty, merge_region_values);
        let debt = Value::Region([region.clone()].into());
        assert!(frame_independent_value(&Analyzer::resolved_value_in(&debt, &values)));
        values.regions.insert(region, local, merge_region_values);
        let debt = Analyzer::resolved_value_in(&debt, &values);
        assert!(!frame_independent_value(&debt));
        assert_eq!(borrowed_roots(&debt), BTreeSet::from(["local".into()]));
    }

    #[test]
    fn projected_incoming_carriers_keep_their_fallback_and_logical_replacements() {
        use super::*;
        let logical = crate::core::REFERENCE_PATH_LOGICAL_ARGUMENT;
        let local = Value::Borrowed { root: "local".into(), storage: Some(1), fields: vec![], capture_path: vec![] };
        let mut value = Value::ExternalBorrowed;
        assert!(replace_resident_path(&mut value, &[2, 3, logical, 0], Value::ExternalBorrowed));
        assert!(frame_independent_value(&value));
        assert_eq!(value_at_path(&value, &[2, 0]), Some(Value::ExternalBorrowed));
        assert_eq!(value_at_path(&value, &[4]), Some(Value::ExternalBorrowed));
        assert!(replace_resident_path(&mut value, &[2, 3, logical, 0], local));
        assert!(!frame_independent_value(&value));
        assert_eq!(borrowed_roots(&value), BTreeSet::from(["local".into()]));
        assert_eq!(value_at_path(&value, &[2, 0]), Some(Value::ExternalBorrowed));
        assert!(replace_resident_path(&mut value, &[2, 3, logical, 0], Value::None));
        assert!(!frame_independent_value(&value), "unknown replacement cannot retain the earlier proof");
    }

    #[test]
    fn rigid_generic_independence_does_not_authenticate_reference_contents() {
        use super::*;
        let signatures = crate::ElaboratedInterface::default();
        let generic = type_proven_value(&signatures, &Type::Generic(0)).unwrap();
        assert_eq!(generic, Value::FrameIndependent);
        assert!(frame_independent_value(&generic));
        assert!(!invocations::reference_is_empty(&generic));
        assert!(!invocations::reference_is_known(&generic));
        assert!(reference_targets(&generic).is_none());
        assert!(type_proven_value(&signatures, &Type::Infer(crate::types::InferVar(0))).is_none());
        let reference = Type::Reference { mutability: crate::Mutability::Shared,
            lifetime: crate::Lifetime::Generic(0), referent: Box::new(Type::Generic(1)) };
        assert!(type_proven_value(&signatures, &reference).is_none());
        assert!(!frame_independent_value(&join(vec![generic, Value::None])));
    }

    #[test]
    fn reborrow_projection_retains_logical_debt_and_future_region_contents() {
        use super::*;
        let region = crate::placeflow::regions::Region { site: "resident".into(), path: vec![] };
        let loan = |name: &str| Value::Borrowed { root: name.into(), storage: Some(1), fields: vec![], capture_path: vec![] };
        let original = Value::Logical {
            physical: Box::new(Value::Reference { dependencies: Box::new(loan("carrier")),
                targets: Some(Box::new(loan("target"))), contents: None, authenticated: true }),
            arguments: [(0, Value::Region([region.clone()].into()))].into(),
        };
        assert_eq!(project_borrowed_referent(original.clone(), &[]), original);
        let projected = project_borrowed_referent(original, &[1, 2]);
        assert_eq!(logical_regions(&projected), BTreeSet::from([region.clone()]));
        let targets = reference_targets(&projected).unwrap();
        assert!(matches!(targets, Value::Borrowed { fields, .. } if fields == [1, 2]));
        let mut values = ValueEnvironment::default();
        values.regions.insert(region, loan("later"), merge_region_values);
        let resolved = Analyzer::resolved_value_in(&projected, &values);
        assert_eq!(borrowed_roots(&resolved), BTreeSet::from(["carrier".into(), "later".into()]));
    }

    #[test]
    fn declared_reference_writes_revoke_variant_absence_without_erasing_debt() {
        use super::*;
        let empty = Value::Variant(vec![Value::Aggregate(vec![])]);
        let mut resident = Value::Aggregate(vec![empty.clone()]);
        assert!(weak_reference_write_path(&mut resident, &[0, 0, 0], Value::ExternalBorrowed));
        let value = value_at_path(&resident, &[0, 0, 0]).unwrap();
        assert!(!invocations::reference_is_empty(&value));
        assert!(invocations::reference_is_known(&value));
        assert_eq!(reference_targets(&value), Some(Value::ExternalBorrowed));
        let local = Value::Borrowed { root: "local".into(), storage: Some(1), fields: vec![], capture_path: vec![] };
        assert!(weak_reference_write_path(&mut resident, &[0, 0, 0], local));
        let value = value_at_path(&resident, &[0, 0, 0]).unwrap();
        assert_eq!(borrowed_roots(&value), BTreeSet::from(["local".into()]));
        assert!(reference_targets(&value).is_none(), "a possible local replacement revokes the old external target");
        assert!(weak_reference_write_path(&mut resident, &[0, 0, 0], Value::None));
        let value = value_at_path(&resident, &[0, 0, 0]).unwrap();
        assert!(!invocations::reference_is_known(&value), "unknown incoming provenance cannot authenticate the slot");
        assert_eq!(borrowed_roots(&value), BTreeSet::from(["local".into()]));
        let mut strict = empty;
        assert!(!replace_resident_path(&mut strict, &[0, 0], Value::ExternalBorrowed),
            "source assignment does not acquire declaration may-write permission");
        let mut external = Value::ExternalBorrowed;
        let local = Value::Borrowed { root: "replacement".into(), storage: Some(2), fields: vec![], capture_path: vec![] };
        assert!(weak_reference_write_path(&mut external, &[1, 0], local));
        let updated = value_at_path(&external, &[1, 0]).unwrap();
        assert!(invocations::reference_is_known(&updated));
        assert_eq!(borrowed_roots(&updated), BTreeSet::from(["replacement".into()]));
        assert!(invocations::reference_is_known(&value_at_path(&external, &[0]).unwrap()));
        assert!(borrowed_roots(&value_at_path(&external, &[0]).unwrap()).is_empty());
        assert!(invocations::reference_is_known(&value_at_path(&external, &[2, 3]).unwrap()));
        assert!(borrowed_roots(&value_at_path(&external, &[2, 3]).unwrap()).is_empty());
        assert!(!frame_independent_value(&external));
        assert!(assign_field_path(&mut external, &[(1, 3), (0, 1)], Value::ExternalBorrowed));
        assert!(borrowed_roots(&external).is_empty(), "strong replacement retires the old projected debt");
        assert!(frame_independent_value(&external));
    }

    #[test]
    fn opaque_projected_writes_preserve_wildcards_and_typed_array_extent() {
        use super::*;
        let local = Value::Borrowed { root: "local".into(), storage: Some(1), fields: vec![], capture_path: vec![] };
        let mut value = Value::ExternalBorrowed;
        assert!(weak_reference_write_path(&mut value, &[1], local.clone()));
        assert!(weak_reference_write_path(&mut value, &[crate::core::REFERENCE_PATH_ARRAY_ELEMENT], Value::ExternalBorrowed));
        assert_eq!(borrowed_roots(&value_at_path(&value, &[1]).unwrap()), BTreeSet::from(["local".into()]));
        assert!(borrowed_roots(&value_at_path(&value, &[3]).unwrap()).is_empty());
        seal_array_extents(&crate::ElaboratedInterface::default(), &Type::fixed_array(Type::Unit, 4), &mut value);
        assert!(value_at_path(&value, &[4]).is_none());
        for index in 0..4 { assert!(replace_resident_path(&mut value, &[index], Value::ExternalBorrowed)); }
        assert!(borrowed_roots(&value).is_empty());
        assert!(frame_independent_value(&value));
        let mut unknown = Value::Projected { fallback: Box::new(Value::None), fields: [(0, local)].into() };
        assert!(weak_reference_write_path(&mut unknown, &[1], Value::ExternalBorrowed));
        assert!(!invocations::reference_is_known(&value_at_path(&unknown, &[1]).unwrap()));
        assert_eq!(borrowed_roots(&unknown), BTreeSet::from(["local".into()]));
    }

    #[test]
    fn reference_absence_is_stronger_than_unknown_or_frame_independence() {
        use super::*;
        assert!(invocations::reference_is_empty(&Value::ReferenceFree));
        assert!(!invocations::reference_is_known(&Value::ReferenceFree));
        assert!(!invocations::reference_is_empty(&Value::None));
        assert!(!invocations::reference_is_empty(&Value::FrameIndependent));
        let local = Value::Borrowed { root: "local".into(), storage: Some(1), fields: vec![], capture_path: vec![] };
        let value = join(vec![Value::ReferenceFree, local]);
        assert!(!invocations::reference_is_empty(&value));
        assert_eq!(borrowed_roots(&value), BTreeSet::from(["local".into()]));
    }

    #[test]
    fn authenticated_referent_targets_do_not_replace_lifetime_dependencies() {
        use super::*;
        let backing = Value::Borrowed { root: "backing".into(), storage: Some(1), fields: vec![], capture_path: vec![] };
        let carrier = Value::Borrowed { root: "carrier".into(), storage: Some(2), fields: vec![], capture_path: vec![] };
        let reference = authenticated_reference_with_targets(join(vec![backing.clone(), carrier]), Some(backing.clone()));
        assert_eq!(reference_targets(&reference), Some(backing));
        assert_eq!(borrowed_roots(&reference), BTreeSet::from(["backing".into(), "carrier".into()]));
        assert!(invocations::reference_is_known(&reference));
        let unknown = authenticated_reference_with_targets(reference.clone(), None);
        assert!(invocations::reference_is_known(&unknown));
        assert!(reference_targets(&unknown).is_none());
        assert!(reference_targets(&join(vec![reference, unknown])).is_none());
    }

    #[test]
    fn declaration_targets_preserve_only_proved_external_storage_classes() {
        let external = declared_reference(Value::ExternalBorrowed);
        assert_eq!(reference_targets(&declared_reference(external.clone())), Some(Value::ExternalBorrowed));
        let local = Value::Borrowed { root: "carrier".into(), storage: Some(1), fields: vec![], capture_path: vec![] };
        let mixed = declared_reference(join(vec![external.clone(), local]));
        assert!(reference_targets(&mixed).is_none());
        assert_eq!(borrowed_roots(&mixed), BTreeSet::from(["carrier".into()]));
        assert!(reference_targets(&declared_reference(join(vec![external, Value::None]))).is_none());
    }

    #[test]
    fn reference_authentication_retains_all_escape_debt_and_is_invalidated_by_replacement() {
        use super::*;
        let local = Value::Borrowed { root: "local".into(), storage: None, fields: vec![], capture_path: vec![] };
        let mut result = join(vec![Value::Aggregate(vec![Value::None, local]),
            Value::Aggregate(vec![Value::None, Value::ExternalBorrowed])]);
        assert!(authenticate_reference_path(&mut result, &[1]));
        let reference = value_at_path(&result, &[1]).unwrap();
        assert!(invocations::reference_is_known(&reference));
        assert_eq!(borrowed_roots(&reference), BTreeSet::from(["local".into()]));
        assert!(value_contains_external_reference(&reference));
        assert!(!frame_independent_value(&reference));
        assert!(!invocations::reference_is_known(&value_at_path(&result, &[0]).unwrap()));
        assert!(!invocations::reference_is_known(&join(vec![reference, Value::None])),
            "a separate unknown return alternative must invalidate authentication");
        assert!(replace_resident_path(&mut result, &[1], Value::None));
        assert!(!invocations::reference_is_known(&value_at_path(&result, &[1]).unwrap()),
            "replacing a handle cannot retain the old reference's proof");
    }

    #[test]
    fn reference_authentication_keeps_sparse_array_loans_and_logical_regions() {
        use super::*;
        let region = crate::placeflow::regions::Region { site: "logical".into(), path: vec![0] };
        let a = Value::Borrowed { root: "a".into(), storage: None, fields: vec![], capture_path: vec![] };
        let b = Value::Borrowed { root: "b".into(), storage: None, fields: vec![], capture_path: vec![] };
        let mut value = Value::Array { length: Some(4), element: Box::new(join(vec![a, Value::Region([region.clone()].into())])),
            fields: [(2, b)].into() };
        assert!(authenticate_reference_path(&mut value, &[crate::core::REFERENCE_PATH_ARRAY_ELEMENT]));
        assert_eq!(contained_regions(&value), BTreeSet::from([region]));
        let value = Analyzer::resolved_value_in(&value, &ValueEnvironment::default());
        assert_eq!(borrowed_roots(&value), BTreeSet::from(["a".into(), "b".into()]));
        assert!(invocations::reference_is_known(&value_at_path(&value, &[0]).unwrap()));
        assert!(invocations::reference_is_known(&value_at_path(&value, &[2]).unwrap()));
        assert!(!frame_independent_value(&value));
    }

    #[test]
    fn callable_containment_is_not_aliasing_of_the_captured_owner_region() {
        use super::*;
        let region = crate::placeflow::regions::Region { site: "slot".into(), path: vec![1] };
        let value = Value::CallableResident {
            footprint: Box::new(Value::Region(BTreeSet::from([region.clone()]))), resident_captures: vec![],
        };
        assert!(logical_regions(&value).is_empty());
        assert_eq!(contained_regions(&value), BTreeSet::from([region]));
        let value = Value::CallableResident {
            footprint: Box::new(Value::Borrowed { root: "a".into(), storage: Some(0), fields: vec![], capture_path: vec![] }), resident_captures: vec![],
        };
        assert_eq!(borrowed_roots(&value), BTreeSet::from(["a".into()]));
        assert!(!frame_independent_value(&value));
        assert!(value_at_path(&value, &[0]).is_none(), "capture snapshots are not addressable fields");
    }

    #[test]
    fn symbolic_array_provenance_keeps_union_and_sparse_replacement_obligations() {
        use super::*;
        let a = Value::Borrowed { root: "a".into(), storage: None, fields: vec![], capture_path: vec![] };
        let b = Value::Borrowed { root: "b".into(), storage: None, fields: vec![], capture_path: vec![] };
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
        let a = Value::Borrowed { root: "a".into(), storage: None, fields: vec![], capture_path: vec![] };
        let b = Value::Borrowed { root: "b".into(), storage: None, fields: vec![], capture_path: vec![] };
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
        let loan = Value::Borrowed { root: "owner".into(), storage: None, fields: vec![], capture_path: vec![] };
        let yes = Value::Variant(vec![Value::Aggregate(vec![loan.clone()])]);
        let no = Value::Variant(vec![Value::Aggregate(vec![])]);
        let selected = value_at_path(&join(vec![yes.clone(), no.clone()]), &[0, 0]).unwrap();
        assert_eq!(borrowed_roots(&selected), BTreeSet::from(["owner".into()]));
        let choice = Value::Alternatives(vec![yes.clone(), no]);
        assert_eq!(borrowed_roots(&value_at_path(&choice, &[0, 0]).unwrap()), BTreeSet::from(["owner".into()]));
        assert_eq!(value_at_path(&Value::Alternatives(vec![yes, Value::None]), &[0, 0]), None);
        assert_eq!(value_at_path(&Value::Alternatives(vec![Value::Aggregate(vec![])]), &[0]), None);
        assert_eq!(value_at_path(&Value::Aggregate(vec![]), &[0]), None);
        assert_eq!(value_at_path(&Value::Variant(vec![Value::None]), &[0, 0]), None);
        let unknown = join(vec![Value::Aggregate(vec![loan]), Value::None]);
        assert_eq!(value_at_path(&unknown, &[0]), None);
    }
}
