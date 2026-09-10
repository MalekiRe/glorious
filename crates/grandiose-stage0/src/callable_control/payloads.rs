//! Payload projections of the same body-derived invocation alternatives.
//! These are relations to evaluated inputs, not a second evaluation of Core.
use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct InvocationPayload {
    pub ty: Type,
    pub source: PayloadSource,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum PayloadSource {
    Argument {
        index: u32,
        path: Vec<u32>,
    },
    Capture {
        receiver_path: Vec<u32>,
        callable_ty: Type,
        resident_ty: Type,
        path: Vec<u32>,
    },
    Aggregate(Vec<InvocationPayload>),
    /// A returned constructor retains typed capture inputs, not addressable
    /// aggregate fields. Its code authority is sealed to the defining body.
    Callable { constructor: ClosureControl, captures: Vec<InvocationPayload> },
    /// Address-preserving projection of an existing input loan, distinct
    /// from reading the reference's contents or borrowing an owned input.
    Reborrow { input: Box<InvocationPayload>, fields: Vec<u32> },
    /// Borrow storage owned by an evaluated borrowed receiver. The receiver
    /// retains its lifetime and permissions; the selected capture supplies the
    /// referent's resident contents. Neither is a forwarded capture value.
    BorrowCapture {
        receiver_path: Vec<u32>,
        callable_ty: Type,
        resident_ty: Type,
        fields: Vec<u32>,
    },
    /// The value is not represented by an input relation. Consumers require
    /// an independent type/provenance proof; this is never an empty footprint.
    Unknown,
}

impl InvocationPayload {
    /// Constructor identities positively retained by this result relation.
    /// Absence here is not proof that an unknown result has no environment.
    pub(crate) fn constructors(&self, result: &mut std::collections::BTreeSet<EnvironmentBrand>) {
        match &self.source {
            PayloadSource::Callable { constructor, captures } => {
                result.insert(constructor.brand());
                for capture in captures { capture.constructors(result); }
            }
            PayloadSource::Aggregate(fields) => {
                for field in fields { field.constructors(result); }
            }
            PayloadSource::Reborrow { input, .. } => input.constructors(result),
            _ => {}
        }
    }
    pub(super) fn unknown(ty: Type) -> Self {
        Self {
            ty,
            source: PayloadSource::Unknown,
        }
    }

    pub(super) fn instantiate_types(&mut self, arguments: &[GenericArgument]) {
        let GenericArgument::Type(ty) = crate::signature::substitute_trait_generic_argument(
            GenericArgument::Type(self.ty.clone()),
            arguments,
        ) else {
            unreachable!("payload type substitution");
        };
        self.ty = ty;
        if let PayloadSource::Aggregate(fields) | PayloadSource::Callable { captures: fields, .. } = &mut self.source {
            for field in fields {
                field.instantiate_types(arguments);
            }
        }
        if let PayloadSource::Reborrow { input, .. } = &mut self.source {
            input.instantiate_types(arguments);
        }
        if let PayloadSource::Capture { callable_ty, resident_ty, .. }
            | PayloadSource::BorrowCapture { callable_ty, resident_ty, .. } = &mut self.source {
            for ty in [callable_ty, resident_ty] {
                let GenericArgument::Type(instantiated) = crate::signature::substitute_trait_generic_argument(
                    GenericArgument::Type(ty.clone()), arguments) else { unreachable!("capture payload type substitution"); };
                *ty = instantiated;
            }
        }
    }
}

pub(crate) enum ResolvedPayload<V> {
    Inputs { ty: Type, values: Vec<V> },
    Aggregate(Vec<ResolvedPayload<V>>),
    Callable { ty: Type, constructor: ClosureControl, captures: Vec<(Type, ResolvedPayload<V>)> },
    Unknown(Type),
}

pub(crate) trait PayloadInputs {
    type Value: Clone;
    fn project(&self, value: &Self::Value, path: &[u32]) -> Option<Self::Value>;
    fn captures(&self, callable: &crate::resident_invocations::Operand<Self::Value>)
        -> crate::resident_invocations::CapturedInputs<Self::Value>;
    /// Project the referent of a frozen reference snapshot without reading
    /// that referent's contents or creating a new caller-owned storage slot.
    fn reborrow(&self, reference: &Self::Value, fields: &[u32]) -> Option<Self::Value>;
    fn borrow_capture(&self, _receiver: &Self::Value,
        _projection: crate::resident_invocations::CaptureProjection, _unique: bool) -> Option<Self::Value> { None }
}

/// A storage-domain projection is not itself evidence that a reference has
/// provenance. Resource consumers must authenticate the projected leaf in
/// their existing loan/storage snapshot before it can settle a result gap.
pub(crate) trait ReferenceInputs: PayloadInputs {
    fn reference_known(&self, value: &Self::Value) -> bool;
}

pub(crate) struct ResolvedReturns<V> {
    pub payloads: Vec<ResolvedPayload<V>>,
    pub references_complete: bool,
}

impl InvocationControl {
    /// Resolve normal results once, retaining positive dependencies even when
    /// coverage is incomplete. Only complete invocation coverage AND every
    /// non-static result leaf's authenticated projection discharge an opaque
    /// declared reference contract. No return observations is not an absence
    /// proof. Captures and explicit parameters obey the same rule.
    pub(crate) fn resolve_returns<D: ReferenceInputs>(
        &self, result: &Type, signatures: &ElaboratedInterface,
        callable: &D::Value, arguments: &[D::Value], domain: &D,
    ) -> ResolvedReturns<D::Value> {
        let payloads = self.returns.iter()
            .map(|payload| resolve_payload(payload, callable, arguments, domain))
            .collect::<Vec<_>>();
        let mut leaves = vec![];
        let shape_known = crate::core::reference_leaf_paths(signatures, result, &mut vec![], &mut leaves).is_ok();
        fn known<D: ReferenceInputs>(payload: &ResolvedPayload<D::Value>, path: &[u32],
            signatures: &ElaboratedInterface, domain: &D) -> bool {
            match payload {
                ResolvedPayload::Inputs { ty, values } => {
                    let mut input_leaves = vec![];
                    let _ = crate::core::reference_leaf_paths(signatures, ty, &mut vec![], &mut input_leaves);
                    // Result coverage is checked independently below. A
                    // positively represented input leaf can authenticate
                    // this projection even when another input field is open.
                    input_leaves.iter().any(|(fields, _)| fields == path)
                        && !values.is_empty() && values.iter().all(|value|
                            domain.project(value, path).is_some_and(|value| domain.reference_known(&value)))
                }
                ResolvedPayload::Aggregate(fields) => path.split_first().is_some_and(|(index, rest)|
                    fields.get(*index as usize).is_some_and(|field| known(field, rest, signatures, domain))),
                ResolvedPayload::Callable { .. } | ResolvedPayload::Unknown(_) => false,
            }
        }
        let references_complete = !self.unknown && self.normal && !payloads.is_empty() && shape_known
            && payloads.iter().all(|payload| leaves.iter().all(|(path, ty)|
                matches!(ty, Type::Reference { lifetime: crate::Lifetime::Static, .. }) || known(payload, path, signatures, domain)));
        ResolvedReturns { payloads, references_complete }
    }
}

/// Instantiate one payload relation over a consumer's evaluated snapshots.
/// Explicit and captured inputs use the same readonly projection interface as
/// invocation stores. Missing projections remain unknown, not empty values.
pub(crate) fn resolve_payload<D: PayloadInputs>(
    payload: &InvocationPayload,
    callable: &D::Value,
    arguments: &[D::Value],
    domain: &D,
) -> ResolvedPayload<D::Value> {
    use crate::resident_invocations::Operand;
    let values = match &payload.source {
        PayloadSource::Argument { index, path } => arguments
            .get(*index as usize)
            .and_then(|value| domain.project(value, path))
            .map(|value| vec![value]),
        PayloadSource::Capture {
            receiver_path,
            callable_ty,
            resident_ty,
            path,
        } => domain.project(callable, receiver_path).and_then(|value| {
            let captures = domain.captures(&Operand {
                ty: callable_ty.clone(),
                value,
            });
            if captures.unresolved {
                return None;
            }
            let key = crate::types::canonical_type_encoding(resident_ty);
            let mut values = vec![];
            for operand in captures.operands {
                if crate::types::canonical_type_encoding(&operand.ty) == key {
                    values.push(domain.project(&operand.value, path)?);
                }
            }
            (!values.is_empty()).then_some(values)
        }),
        PayloadSource::Aggregate(fields) => {
            return ResolvedPayload::Aggregate(
                fields
                    .iter()
                    .map(|field| resolve_payload(field, callable, arguments, domain))
                    .collect(),
            );
        }
        PayloadSource::Reborrow { input, fields } => {
            match resolve_payload(input, callable, arguments, domain) {
                ResolvedPayload::Inputs { values, .. } => values.iter()
                    .map(|value| domain.reborrow(value, fields)).collect::<Option<Vec<_>>>(),
                _ => None,
            }
        }
        PayloadSource::BorrowCapture { receiver_path, callable_ty, resident_ty, fields } => {
            let Type::Reference { mutability, .. } = &payload.ty else {
                return ResolvedPayload::Unknown(payload.ty.clone());
            };
            let receiver = domain.project(callable, receiver_path);
            receiver.and_then(|receiver| {
                let resident = domain.project(&receiver, &[crate::core::REFERENCE_PATH_DEREF])?;
                let captures = domain.captures(&Operand { ty: callable_ty.clone(), value: resident });
                let projection = crate::resident_invocations::CaptureProjection::new(resident_ty, fields);
                if captures.unresolved || !captures.operands.iter().any(|capture| projection.matches(&capture.ty)) { return None; }
                domain.borrow_capture(&receiver, projection, *mutability == crate::Mutability::Unique).map(|value| vec![value])
            })
        }
        PayloadSource::Callable { constructor, captures } => {
            return ResolvedPayload::Callable { ty: payload.ty.clone(), constructor: constructor.clone(),
                captures: captures.iter().map(|capture| (capture.ty.clone(), resolve_payload(capture, callable, arguments, domain))).collect() };
        }
        PayloadSource::Unknown => None,
    };
    match values {
        Some(values) => ResolvedPayload::Inputs {
            ty: payload.ty.clone(),
            values,
        },
        None => ResolvedPayload::Unknown(payload.ty.clone()),
    }
}

fn origin_path(origin: &ControlOrigin, base: &ControlOrigin) -> Option<Vec<u32>> {
    let mut current = origin;
    let mut path = vec![];
    loop {
        if current == base {
            path.reverse();
            return Some(path);
        }
        let ControlOrigin::Field { base, index } = current else {
            return None;
        };
        path.push(*index);
        current = base;
    }
}

fn storage_path(target: &ControlValue, input: &ControlValue) -> Option<Vec<u32>> {
    let mut target = target.storage.as_ref()?;
    let input = input.storage.as_ref()?;
    let mut fields = vec![];
    loop {
        if target == input { fields.reverse(); return Some(fields); }
        let ControlStorage::Field { base, index } = target else { return None; };
        fields.push(*index); target = base;
    }
}

fn value_path(origin: &ControlOrigin, input: &ControlValue) -> Option<Vec<u32>> {
    let mut pending = vec![(input, vec![])];
    while let Some((value, prefix)) = pending.pop() {
        if let Some(suffix) = origin_path(origin, &value.origin) {
            return Some(prefix.into_iter().chain(suffix).collect());
        }
        match &value.shape {
            ControlValueShape::Tuple(fields)
            | ControlValueShape::Array(fields)
            | ControlValueShape::Record { fields, .. }
            | ControlValueShape::Enum { fields, .. } => {
                for (index, field) in fields.iter().enumerate() {
                    let mut path = prefix.clone();
                    path.push(index as u32);
                    pending.push((field, path));
                }
            }
            ControlValueShape::Borrow(value) => {
                let mut path = prefix;
                path.push(crate::core::REFERENCE_PATH_DEREF);
                pending.push((value, path));
            }
            _ => {}
        }
    }
    None
}

/// Locate an existing reference whose referent structurally owns the new
/// borrow's place. This traverses the shared abstract value, never Core.
fn reborrow_path(value: &ControlValue, input: &ControlValue) -> Option<(Vec<u32>, Vec<u32>, Type)> {
    let ControlValueShape::Borrow(target) = &value.shape else { return None; };
    let mut pending = vec![(input, vec![])];
    while let Some((input, path)) = pending.pop() {
        match &input.shape {
            ControlValueShape::Borrow(referent) => {
                if let Some(fields) = storage_path(target, referent) {
                    return Some((path, fields, input.ty.clone()));
                }
                let mut path = path;
                path.push(crate::core::REFERENCE_PATH_DEREF);
                pending.push((referent, path));
            }
            ControlValueShape::Tuple(fields) | ControlValueShape::Array(fields)
            | ControlValueShape::Record { fields, .. } | ControlValueShape::Enum { fields, .. } => {
                for (index, field) in fields.iter().enumerate() {
                    let mut path = path.clone(); path.push(index as u32);
                    pending.push((field, path));
                }
            }
            _ => {}
        }
    }
    None
}

impl BoundControlSummaries<'_> {
fn construct_payload(&self, value: &ControlValue,
    derive: &impl Fn(&ControlValue) -> InvocationPayload) -> InvocationPayload {
    let source = match &value.shape {
        ControlValueShape::Tuple(fields) | ControlValueShape::Array(fields) =>
            PayloadSource::Aggregate(fields.iter().map(derive).collect()),
        ControlValueShape::Callable { brand: CallableBrand::Closure(brand), .. } => {
            let selected = self.staged_body(brand.owner).and_then(|body|
                body.expressions.iter().enumerate().find(|(_, expression)|
                    matches!(&expression.kind, CoreKind::Closure { environment, .. } if environment.brand == *brand)));
            match selected.and_then(|(index, _)| self.closure_constructor(brand.owner, CoreId(index as u32)))
                .zip(self.capture_inputs(value)) {
                Some((constructor, captures)) => PayloadSource::Callable { constructor,
                    captures: captures.into_iter().map(|capture| {
                        // Borrowed formation retains the factory's own slot;
                        // its address is not an incoming caller reference.
                        if capture.contents.is_empty() { derive(&capture.value) }
                        else { InvocationPayload::unknown(capture.resident_ty) }
                    }).collect() },
                None => PayloadSource::Unknown,
            }
        }
        // Nominal logical residents need not equal physical fields.
        _ => PayloadSource::Unknown,
    };
    InvocationPayload { ty: value.ty.clone(), source }
}

}

struct CapturedInput {
    value: ControlValue,
    resident_ty: Type,
    contents: Vec<u32>,
}

impl BoundControlSummaries<'_> {
    pub(super) fn observed_payload(
        &self,
        value: &ControlValue,
        callee: &ControlValue,
        arguments: &[ControlValue],
    ) -> InvocationPayload {
        let (callable, receiver_path) = callee.invocation_receiver();
        // Missing receiver captures cannot establish a capture projection.
        // Explicit argument dependencies can still be retained positively.
        let captures = self.capture_inputs(callable).unwrap_or_default();
        self.input_payload(value, arguments, &captures, &receiver_path, &callable.ty)
    }

    pub(super) fn contract_payload(
        &self,
        value: &ControlValue,
        summary: &super::CallableControlSummary,
        receiver_path: &[u32],
        callable_ty: &Type,
    ) -> InvocationPayload {
        let captures = match summary.callable {
            CallableBrand::Closure(brand) =>
                self.capture_input_values(brand, &summary.inputs.captures, None).unwrap_or_default(),
            CallableBrand::Named(_) => vec![],
            CallableBrand::HandlerClause { .. } | CallableBrand::Continuation { .. } =>
                return InvocationPayload::unknown(value.ty.clone()),
        };
        self.input_payload(value, &summary.inputs.parameters, &captures, receiver_path, callable_ty)
    }

    fn input_payload(
        &self,
        value: &ControlValue,
        arguments: &[ControlValue],
        captures: &[CapturedInput],
        receiver_path: &[u32],
        callable_ty: &Type,
    ) -> InvocationPayload {
        fn derive(
            bound: &BoundControlSummaries<'_>,
            value: &ControlValue,
            arguments: &[ControlValue],
            captures: &[CapturedInput],
            receiver_path: &[u32],
            callable_ty: &Type,
        ) -> InvocationPayload {
            for (index, argument) in arguments.iter().enumerate() {
                if let Some(path) = value_path(&value.origin, argument) {
                    return InvocationPayload {
                        ty: value.ty.clone(),
                        source: PayloadSource::Argument {
                            index: index as u32,
                            path,
                        },
                    };
                }
                if let Some((path, fields, ty)) = reborrow_path(value, argument) {
                    return InvocationPayload { ty: value.ty.clone(), source: PayloadSource::Reborrow {
                        input: Box::new(InvocationPayload { ty, source: PayloadSource::Argument { index: index as u32, path } }), fields,
                    } };
                }
            }
            for capture in captures {
                if let Some(fields) = value_path(&value.origin, &capture.value) {
                    let path = capture.contents.iter().chain(&fields).copied().collect();
                    return InvocationPayload {
                        ty: value.ty.clone(),
                        source: PayloadSource::Capture {
                            receiver_path: receiver_path.to_vec(),
                            callable_ty: callable_ty.clone(),
                            resident_ty: capture.resident_ty.clone(),
                            path,
                        },
                    };
                }
                let borrowed_resident = if capture.contents.last() == Some(&crate::core::REFERENCE_PATH_DEREF) {
                    if let ControlValueShape::Borrow(target) = &value.shape {
                        storage_path(target, &capture.value).map(|fields|
                            (capture.contents[..capture.contents.len() - 1].to_vec(), fields, capture.resident_ty.clone()))
                    } else { None }
                } else { None };
                let relation = borrowed_resident.or_else(|| reborrow_path(value, &capture.value)
                    .map(|(path, fields, ty)| (capture.contents.iter().chain(&path).copied().collect(), fields, ty)));
                if let Some((path, fields, ty)) = relation {
                    return InvocationPayload { ty: value.ty.clone(), source: PayloadSource::Reborrow {
                        input: Box::new(InvocationPayload { ty, source: PayloadSource::Capture {
                            receiver_path: receiver_path.to_vec(), callable_ty: callable_ty.clone(),
                            resident_ty: capture.resident_ty.clone(), path,
                        } }), fields,
                    } };
                }
                if capture.contents.is_empty()
                    && let ControlValueShape::Borrow(target) = &value.shape
                    && let Some(fields) = storage_path(target, &capture.value)
                    && let Some((_, receiver)) = receiver_path.split_last()
                {
                    return InvocationPayload { ty: value.ty.clone(), source: PayloadSource::BorrowCapture {
                        receiver_path: receiver.to_vec(), callable_ty: callable_ty.clone(),
                        resident_ty: capture.resident_ty.clone(), fields,
                    } };
                }
            }
            bound.construct_payload(value, &|value| {
                derive(bound, value, arguments, captures, receiver_path, callable_ty)
            })
        }
        derive(self, value, arguments, captures, receiver_path, callable_ty)
    }

    fn capture_inputs(&self, callable: &ControlValue) -> Option<Vec<CapturedInput>> {
        let ControlValueShape::Callable {
            brand: CallableBrand::Closure(brand),
            captures,
            generic_arguments,
            ..
        } = &callable.shape
        else {
            return None;
        };
        self.capture_input_values(*brand, captures, generic_arguments.as_deref())
    }

    fn capture_input_values(
        &self,
        brand: super::EnvironmentBrand,
        captures: &[ControlValue],
        generic_arguments: Option<&[GenericArgument]>,
    ) -> Option<Vec<CapturedInput>> {
        let Some(summary) = self.summaries.get(CallableBrand::Named(brand.owner)) else {
            return None;
        };
        let Some(seal) = summary.dependencies.get(&brand.owner) else {
            return None;
        };
        let Some(environment) =
            seal.body
                .expressions
                .iter()
                .find_map(|expression| match &expression.kind {
                    CoreKind::Closure { environment, .. } if environment.brand == brand => {
                        Some(environment)
                    }
                    _ => None,
                })
        else {
            return None;
        };
        if environment.captures.len() != captures.len() {
            return None;
        }
        Some(environment
            .captures
            .iter()
            .zip(captures)
            .map(|(capture, value)| {
                let formation = crate::capture_formation::CaptureFormation::new(capture);
                let mut resident_ty = formation.resident_type();
                if let Some(arguments) = generic_arguments {
                    let GenericArgument::Type(ty) =
                        crate::signature::substitute_trait_generic_argument(
                            GenericArgument::Type(resident_ty),
                            arguments,
                        )
                    else {
                        unreachable!("type substitution");
                    };
                    resident_ty = ty;
                }
                CapturedInput {
                    value: value.clone(),
                    resident_ty,
                    contents: formation.contents_path().to_vec(),
                }
            })
            .collect())
    }
}
