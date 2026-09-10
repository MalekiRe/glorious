//! Correctness-required structural control fusion.
//!
//! Input: a sealed staged Core batch and exact callee selections from the
//! shared invocation relation. Output: ordinary Core, independently validated
//! before fresh ownership, escape, quantity and cleanup derivation. This pass
//! neither discovers invocation targets nor edits an already-derived ledger.
//! Captured resident inputs are formed at the original constructor; invocation
//! projects that same storage. Lexical proof inputs remain label values until
//! escape checking and the checked runtime representation pass erase them.

use super::*;
use crate::callable_control::{BoundControlSummaries, ClosureControl, ControlLabelTarget, FusionTarget};
use crate::capture_formation::{CaptureFormation, CaptureSource};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone)]
struct Frame {
    owner: DefKey,
    callable: CallableBrand,
    proof_root: CallableBrand,
    calls: Vec<(CallableBrand, CoreId)>,
    arguments: Option<Vec<GenericArgument>>,
    locals: BTreeMap<String, Input>,
    resumptions: BTreeMap<ResumptionId, (ResumptionId, String, Type)>,
    labels: BTreeMap<LabelBrand, LabelBrand>,
    environments: BTreeMap<EnvironmentBrand, EnvironmentBrand>,
    refinements: BTreeMap<RefinementBrand, RefinementBrand>,
    replacements: Vec<(Type, Type)>,
    nodes: BTreeMap<CoreId, CoreId>,
    invocations: std::sync::Arc<crate::callable_control::BodyInvocationControl>,
}

type Activation = (Vec<(CallableBrand, CoreId)>, CallableBrand, CoreId);

/// One value in the transformation, with its checked source contract and its
/// chosen representation. Keeping these together is essential: projecting a
/// physical tuple must not erase which branded callable it implements.
struct Value {
    physical: CoreExpr,
    contract: ValueContract,
}

#[derive(Clone)]
struct Input {
    place: CorePlace,
    contract: ValueContract,
}

/// The source contract and its positively constructed control representation
/// travel together through values and storage inputs. An erased callable type
/// alone cannot select a constructor, and joining two constructors must not
/// forget that the joined value still owns their tagged representation.
#[derive(Clone, Debug, Eq, PartialEq)]
struct ValueContract {
    ty: Type,
    representation: Representation,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Representation {
    Ordinary,
    Callable(BTreeSet<usize>),
    Fields(Vec<Representation>),
    Reference(Box<Representation>),
}

impl ValueContract {
    fn ordinary(ty: Type) -> Self { Self { ty, representation: Representation::Ordinary } }
}

impl Representation {
    fn fields(fields: Vec<Self>) -> Self {
        if fields.iter().all(|field| *field == Self::Ordinary) { Self::Ordinary } else { Self::Fields(fields) }
    }
    fn reference(value: Self) -> Self {
        if value == Self::Ordinary { Self::Ordinary } else { Self::Reference(Box::new(value)) }
    }
    fn field(&self, index: u32) -> Self {
        match self { Self::Fields(fields) => fields.get(index as usize).cloned().unwrap_or(Self::Ordinary), _ => Self::Ordinary }
    }
    fn join(&self, other: &Self) -> Option<Self> {
        Some(match (self, other) {
            (Self::Ordinary, Self::Ordinary) => Self::Ordinary,
            (Self::Callable(left), Self::Callable(right)) => Self::Callable(left.union(right).copied().collect()),
            (Self::Fields(left), Self::Fields(right)) if left.len() == right.len() =>
                Self::Fields(left.iter().zip(right).map(|(left, right)| left.join(right)).collect::<Option<_>>()?),
            (Self::Reference(left), Self::Reference(right)) => Self::Reference(Box::new(left.join(right)?)),
            _ => return None,
        })
    }

    fn include_at(&mut self, fields: &[u32], replacement: &Self) -> Option<()> {
        let Some((field, rest)) = fields.split_first() else {
            *self = self.join(replacement)?;
            return Some(());
        };
        match self {
            Self::Fields(values) => values.get_mut(*field as usize)?.include_at(rest, replacement),
            Self::Ordinary if *replacement == Self::Ordinary => Some(()),
            _ => None,
        }
    }
}

#[cfg(test)]
mod representation_tests {
    use super::*;

    #[test]
    fn control_representation_joins_preserve_choices_without_inventing_authority() {
        let first = Representation::Callable([0].into());
        let second = Representation::Callable([1].into());
        assert_eq!(first.join(&second), Some(Representation::Callable([0, 1].into())));
        assert_eq!(first.join(&Representation::Ordinary), None);
        let left = Representation::fields(vec![Representation::Ordinary, Representation::reference(first)]);
        let right = Representation::fields(vec![Representation::Ordinary, Representation::reference(second)]);
        let joined = left.join(&right).unwrap();
        assert_eq!(joined.field(1), Representation::reference(Representation::Callable([0, 1].into())));
        assert_eq!(joined.field(0), Representation::Ordinary);
    }
}

struct ControlEnvironment {
    constructor: ClosureControl,
    semantic: Type,
    resident: Type,
    arguments: Option<Vec<GenericArgument>>,
    labels: BTreeMap<LabelBrand, LabelBrand>,
    captures: Vec<ValueContract>,
}

enum Selected {
    Observed(FusionTarget),
    Environment(usize),
    Label(LabelBrand),
    Dispatch(Vec<usize>),
}

pub(crate) fn transform(
    owner: DefKey,
    control: &BoundControlSummaries<'_>,
    control_captures: &crate::escape::ControlCaptures,
) -> Result<Option<TypedBody>, CoreDiagnostic> {
    let source = control.staged_body(owner).ok_or_else(|| diagnostic(invalid_typed_core_span(),
        "control fusion requires a sealed source body"))?;
    let dependencies = control.lexical_dependencies(owner)
        .ok_or_else(|| diagnostic(source.expression(source.root).span, "control fusion lacks a sealed lexical dependency product"))?;
    let pending = dependencies.pending_closures(source.root)
        .map_err(|reason| diagnostic(source.expression(source.root).span, format!("invalid lexical control scope: {reason:?}")))?;
    let captured_control = control_captures.bind(owner, source)
        .map_err(|error| diagnostic(source.expression(source.root).span, error))?;
    if pending.is_empty() && !captured_control
        && !source.expressions.iter().any(|expr|
        matches!(expr.kind, CoreKind::Closure { .. }) && contains_label(&expr.ty)) {
        return Ok(None);
    }
    control.fusion_body(owner).map_err(|reason| diagnostic(source.expression(source.root).span,
        format!("required control fusion lacks a checked invocation contract: {reason:?}")))?;
    if !source.validate_for_control_fusion().is_empty() {
        return Err(diagnostic(source.expression(source.root).span, "control fusion requires validated staged Core"));
    }
    let mut pass = Fusion {
        owner, control, control_captures, output: TypedBody { expressions: vec![], unsafe_scopes: BTreeSet::new(),
            ..source.clone() }, next: 0, active: BTreeMap::new(), stack: vec![CallableBrand::Named(owner)],
        values: vec![], environments: vec![], label_results: BTreeMap::new(),
    };
    let mut frame = pass.frame(owner, CallableBrand::Named(owner), None, vec![], vec![])?;
    frame.locals.extend(source.parameters.iter().map(|(name, ty)| (name.clone(), Input {
        place: CorePlace::Local { name: name.clone(), ty: ty.clone() }, contract: ValueContract::ordinary(ty.clone()),
    })));
    pass.output.root = pass.expression(source.root, &mut frame)?;
    pass.output.expressions = pass.values.into_iter().map(|value| value.physical).collect();
    let errors = pass.output.validate();
    if let Some(error) = errors.into_iter().next() {
        return Err(diagnostic(error.span, format!("structural control fusion did not produce valid Core: {}", error.message)));
    }
    Ok(Some(pass.output))
}

fn diagnostic(span: Span, message: impl Into<String>) -> CoreDiagnostic {
    CoreDiagnostic { code: "G4179", span, message: message.into() }
}

fn contains_label(ty: &Type) -> bool {
    if crate::types::label::payload(ty).is_some() { return true; }
    match ty {
        Type::Tuple(values) => values.iter().any(contains_label),
        Type::Array(value) | Type::FixedArray { element: value, .. }
        | Type::Reference { referent: value, .. } => contains_label(value),
        Type::Callable { parameters, result, contract, .. } => parameters.iter().any(contains_label)
            || contains_label(result) || contract.captures.iter().any(contains_label),
        Type::Nominal { arguments, .. } => arguments.iter().any(|argument| matches!(argument,
            GenericArgument::Type(ty) if contains_label(ty))),
        _ => false,
    }
}

struct Fusion<'a> {
    control_captures: &'a crate::escape::ControlCaptures,
    owner: DefKey,
    control: &'a BoundControlSummaries<'a>,
    output: TypedBody,
    next: u32,
    active: BTreeMap<Activation, LabelBrand>,
    stack: Vec<CallableBrand>,
    values: Vec<Value>,
    environments: Vec<ControlEnvironment>,
    label_results: BTreeMap<LabelBrand, Vec<(ValueContract, Type)>>,
}

impl Fusion<'_> {
    fn source(&self, owner: DefKey) -> &TypedBody {
        self.control.fusion_body(owner).expect("expanded source bodies have sealed control contracts")
    }
    fn fresh(&mut self) -> u32 { let next = self.next; self.next += 1; next }
    fn name(&mut self, original: &str) -> String { format!("$fusion.{}.{}", self.fresh(), original) }
    fn alloc(&mut self, kind: CoreKind, ty: Type, span: Span) -> CoreId {
        let id = CoreId(self.values.len() as u32);
        self.values.push(Value { contract: ValueContract::ordinary(ty.clone()), physical: CoreExpr { kind, ty, span } });
        id
    }
    fn physical_expression(&self, id: CoreId) -> &CoreExpr { &self.values[id.0 as usize].physical }
    fn contract(&self, id: CoreId) -> &ValueContract { &self.values[id.0 as usize].contract }
    fn semantic(&self, id: CoreId) -> &Type { &self.contract(id).ty }
    fn with_semantic(&mut self, id: CoreId, ty: Type) -> CoreId { self.values[id.0 as usize].contract.ty = ty; id }
    fn with_contract(&mut self, id: CoreId, contract: ValueContract) -> CoreId { self.values[id.0 as usize].contract = contract; id }
    fn label_result(&mut self, brand: LabelBrand, value: CoreId) {
        let physical = self.physical_expression(value).ty.clone();
        if physical == Type::Never { return; }
        let contract = self.contract(value).clone();
        self.label_results.get_mut(&brand).expect("a fused transfer has an active lexical binder").push((contract, physical));
    }
    fn join_layout(&self, expected: Type, results: &[(ValueContract, Type)], span: Span) -> Result<(ValueContract, Type), CoreDiagnostic> {
        let live = results.iter().filter(|(_, physical)| *physical != Type::Never).collect::<Vec<_>>();
        let Some((first_semantic, first_physical)) = live.first().copied() else {
            return Ok((ValueContract::ordinary(expected.clone()), self.physical(expected)));
        };
        if live.iter().all(|(_, physical)| physical == first_physical) {
            let semantic = if live.iter().all(|(semantic, _)| semantic.ty == first_semantic.ty) { first_semantic.ty.clone() } else { expected };
            let representation = live.iter().skip(1).try_fold(first_semantic.representation.clone(), |joined, (contract, _)|
                joined.join(&contract.representation)).ok_or_else(|| diagnostic(span,
                    "control result alternatives do not share a complete representation proof"))?;
            Ok((ValueContract { ty: semantic, representation }, first_physical.clone()))
        } else if live.iter().any(|(semantic, physical)| semantic.ty != *physical) {
            Err(diagnostic(span, "control result alternatives have incompatible environment representations"))
        } else {
            // Unchanged source representations retain their already checked
            // directional lifetime/ABI join. No constructor identity survives
            // a join that did not establish that identity for every arm.
            Ok((ValueContract::ordinary(expected.clone()), self.physical(expected)))
        }
    }
    fn frame(&mut self, owner: DefKey, callable: CallableBrand, arguments: Option<Vec<GenericArgument>>,
        calls: Vec<(CallableBrand, CoreId)>, replacements: Vec<(Type, Type)>) -> Result<Frame, CoreDiagnostic> {
        let mut frame = Frame { owner, callable, proof_root: CallableBrand::Named(self.owner), calls, arguments,
            locals: BTreeMap::new(), resumptions: BTreeMap::new(), labels: BTreeMap::new(), environments: BTreeMap::new(),
            refinements: BTreeMap::new(), replacements, nodes: BTreeMap::new(),
            invocations: std::sync::Arc::new(self.control.body(owner).ok_or_else(||
                diagnostic(invalid_typed_core_span(), "control expansion requires bound invocation results"))?) };
        // Allocate one hygienic identity namespace per expansion. References
        // are remapped mechanically; only the existing binders create brands.
        let input = self.control.fusion_body(owner).map_err(|reason| diagnostic(invalid_typed_core_span(),
            format!("control expansion requires a sealed source body: {reason:?}")))?;
        self.control_captures.bind(owner, input)
            .map_err(|error| diagnostic(input.expression(input.root).span, error))?;
        for expression in &input.expressions {
            match &expression.kind {
                CoreKind::Closure { environment, .. } => {
                    let brand = EnvironmentBrand { owner: self.owner, callable: CallableId(self.fresh()) };
                    frame.environments.insert(environment.brand, brand);
                    let captures = environment.captures.iter().map(|capture| self.semantic_type(
                        &frame, CaptureFormation::new(capture).resident_type())).collect::<Vec<_>>();
                    for after in [false, true] {
                        frame.replacements.insert(0, (generated_environment_type(environment.brand, after, &captures),
                            generated_environment_type(brand, after, &captures)));
                    }
                }
                CoreKind::PatternTest { refinement, .. } | CoreKind::Completion { refinement_test: Some(refinement), .. } => {
                    let brand = RefinementBrand { owner: self.owner, refinement: self.fresh() };
                    frame.refinements.insert(refinement.brand, brand);
                    let mut mapped = refinement.clone();
                    mapped.brand = brand;
                    for key in &mut mapped.binding_keys { key.environment = brand; }
                    for positive in [false, true] {
                        if let (Ok(old), Ok(new)) = (refinement.binding_pack_type(positive, Lifetime::Elided),
                            mapped.binding_pack_type(positive, Lifetime::Elided)) {
                            // The pack's region remains outside the branded
                            // environment; replace just that environment term.
                            if let (Type::Nominal { arguments: old, .. }, Type::Nominal { arguments: new, .. }) = (old, new)
                                && let (GenericArgument::Type(old), GenericArgument::Type(new)) = (&old[1], &new[1]) {
                                frame.replacements.push((old.clone(), new.clone()));
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(frame)
    }
    fn rename(&self, frame: &Frame, value: GenericArgument) -> GenericArgument {
        crate::types::CallableContract::replace_value_types(value, &frame.replacements, 0)
    }
    fn argument(&self, frame: &Frame, value: GenericArgument) -> GenericArgument {
        let value = frame.arguments.as_ref().map_or_else(|| value.clone(), |arguments|
            crate::signature::substitute_trait_generic_argument(value.clone(), arguments));
        self.rename(frame, value)
    }
    fn semantic_type(&self, frame: &Frame, ty: Type) -> Type {
        let GenericArgument::Type(ty) = self.argument(frame, GenericArgument::Type(ty)) else { unreachable!() }; ty
    }
    fn physical(&self, ty: Type) -> Type {
        let GenericArgument::Type(ty) = crate::types::CallableContract::replace_value_types(
            GenericArgument::Type(ty), &self.environments.iter().filter(|environment| environment.constructor.nominal_type()).map(|environment|
                (environment.semantic.clone(), environment.resident.clone())).collect::<Vec<_>>(), 0) else { unreachable!() };
        // An exact named code reference with a label-valued ABI is a proof
        // selection, not independently callable storage. Its invocation must
        // be expanded below; an unresolved consumer is rejected.
        if let Type::Callable { contract, .. } = &ty
            && contract.environment.as_deref() == Some(&Type::Unit) && contains_label(&ty) { Type::Unit }
        else { ty }
    }
    fn ty(&self, frame: &Frame, ty: Type) -> Type { self.physical(self.semantic_type(frame, ty)) }
    fn resident_type(&self, contract: &ValueContract) -> Type {
        match (&contract.ty, &contract.representation) {
            (_, Representation::Ordinary) => self.physical(contract.ty.clone()),
            (_, Representation::Callable(constructors)) => constructors.first()
                .map(|index| self.environments[*index].resident.clone()).unwrap_or(Type::Error),
            (Type::Tuple(fields), Representation::Fields(values)) if fields.len() == values.len() =>
                Type::Tuple(fields.iter().zip(values).map(|(ty, representation)| self.resident_type(
                    &ValueContract { ty: ty.clone(), representation: representation.clone() })).collect()),
            (Type::Reference { mutability, lifetime, referent }, Representation::Reference(value)) =>
                Type::Reference { mutability: *mutability, lifetime: lifetime.clone(), referent: Box::new(self.resident_type(
                    &ValueContract { ty: (**referent).clone(), representation: (**value).clone() })) },
            // Unsupported logical layouts cannot acquire a physical callable
            // representation merely because one of their fields has a type.
            _ => Type::Error,
        }
    }

    fn include_storage(&self, frame: &mut Frame, updates: &BTreeMap<String, Input>, span: Span) -> Result<(), CoreDiagnostic> {
        for (name, input) in &mut frame.locals {
            let Some(updated) = updates.get(name).filter(|updated| updated.place == input.place) else { continue; };
            input.contract.representation = input.contract.representation.join(&updated.contract.representation)
                .ok_or_else(|| diagnostic(span, "storage alternatives have incompatible control representation proofs"))?;
        }
        Ok(())
    }

    fn assigned_representation(&self, source: &CorePlace, replacement: &ValueContract,
        frame: &mut Frame, span: Span) -> Result<(), CoreDiagnostic> {
        let mut source = source;
        let mut fields = vec![];
        while let CorePlace::Field { base, index, .. } = source { fields.push(*index); source = base; }
        fields.reverse();
        let CorePlace::Local { name, .. } = source else {
            return if replacement.representation == Representation::Ordinary { Ok(()) } else {
                Err(diagnostic(span, "control representation replacement requires a represented owning storage input"))
            };
        };
        let Some(input) = frame.locals.get_mut(name) else { return Err(diagnostic(span, "control assignment lost its storage input")); };
        if !matches!(input.place, CorePlace::Local { .. }) && replacement.representation != Representation::Ordinary {
            return Err(diagnostic(span, "control representation replacement through captured or borrowed storage is not represented"));
        }
        // Retain all represented tags that may still reach this storage at a
        // label rejoin. This is a conservative layout union, not a strong
        // update or an independent ownership/alias proof.
        input.contract.representation.include_at(&fields, &replacement.representation)
            .ok_or_else(|| diagnostic(span, "assigned control value has no compatible storage representation proof"))
    }
    fn resident_place(&mut self, place: CorePlace, span: Span) -> CoreId {
        let ty = place.ty();
        let kind = match place {
            CorePlace::Local { name, .. } => CoreKind::Local(name),
            CorePlace::Field { base, index, field_count, .. } => CoreKind::Field { base: self.resident_place(*base, span), index, field_count },
            CorePlace::Deref { reference, .. } => CoreKind::Deref(reference),
            CorePlace::Error => CoreKind::Error,
        };
        self.alloc(kind, ty, span)
    }
    fn resident(&mut self, input: Input, span: Span) -> CoreId {
        let value = self.resident_place(input.place, span);
        self.with_contract(value, input.contract)
    }
    fn bind(&mut self, original: &str, value: CoreId, span: Span, prefix: &mut Vec<CoreId>) -> Input {
        let name = self.name(original);
        let ty = self.physical_expression(value).ty.clone();
        let contract = self.contract(value).clone();
        prefix.push(self.alloc(CoreKind::Let { name: name.clone(), value }, Type::Unit, span));
        Input { place: CorePlace::Local { name, ty }, contract }
    }
    fn target(&self, target: &ControlLabelTarget, span: Span) -> Result<LabelBrand, CoreDiagnostic> {
        let ControlLabelTarget::Lexical { activation, .. } = target else {
            return Err(diagnostic(span, "control fusion cannot resolve a symbolic lexical destination"));
        };
        let key = (activation.calls.iter().map(|site| (site.callable, site.expression)).collect(),
            activation.location.callable, activation.location.expression);
        self.active.get(&key).copied().ok_or_else(|| diagnostic(span,
            "label-bearing callable is invoked outside its destination activation"))
    }
    fn represented_target(&self, contract: &ValueContract) -> Option<Selected> {
        let mut ty = &contract.ty;
        let mut representation = &contract.representation;
        while let Type::Reference { referent, .. } = ty {
            ty = referent;
            representation = match representation { Representation::Reference(value) => value, _ => &Representation::Ordinary };
        }
        let environments = match representation {
            Representation::Callable(environments) => environments.iter().copied().collect::<Vec<_>>(),
            _ => vec![],
        };
        if let [index] = environments.as_slice() {
            return Some(Selected::Environment(*index));
        }
        if !environments.is_empty() { return Some(Selected::Dispatch(environments)); }
        // Label's invariant nominal brand is semantic authority, not a
        // structural Fn refinement. Only a positively active fresh binder
        // with that exact type may supply the destination.
        self.active.values().copied().find(|brand| crate::types::label::matches_brand(ty, *brand)).map(Selected::Label)
    }
    fn expression(&mut self, id: CoreId, frame: &mut Frame) -> Result<CoreId, CoreDiagnostic> {
        let unsafe_scope = self.source(frame.owner).unsafe_scopes.contains(&id);
        let expression = self.source(frame.owner).expression(id);
        let source_type = self.semantic_type(frame, expression.ty.clone());
        let preserves_input = matches!(expression.kind, CoreKind::Local(_) | CoreKind::Block(_) | CoreKind::Call { .. }
            | CoreKind::Tuple(_) | CoreKind::Field { .. } | CoreKind::Move(_) | CoreKind::Borrow { .. }
            | CoreKind::Deref(_) | CoreKind::Closure { .. } | CoreKind::Label { .. }
            | CoreKind::Completion { .. } | CoreKind::Handle { .. });
        let result = self.expression_inner(id, frame)?;
        if !preserves_input { self.with_semantic(result, source_type); }
        if unsafe_scope { self.output.unsafe_scopes.insert(result); }
        frame.nodes.insert(id, result);
        Ok(result)
    }
    fn expression_inner(&mut self, id: CoreId, frame: &mut Frame) -> Result<CoreId, CoreDiagnostic> {
        if self.values.len() > 100_000 { return Err(diagnostic(
            self.source(frame.owner).expression(id).span, "structural control fusion exceeded its expansion budget")); }
        let source = self.control.fusion_body(frame.owner).map_err(|reason| diagnostic(invalid_typed_core_span(), format!("missing expansion body: {reason:?}")))?;
        let expression = source.expression(id).clone();
        let span = expression.span;
        let ty = self.ty(frame, expression.ty.clone());
        let kind = match expression.kind {
            CoreKind::Local(name) => {
                let place = frame.locals.get(&name).cloned().ok_or_else(|| diagnostic(span, format!("unbound fusion input `{name}`")))?;
                return Ok(self.resident(place, span));
            }
            CoreKind::Let { name, value } => {
                let value = self.expression(value, frame)?;
                let fresh = self.name(&name);
                frame.locals.insert(name, Input { place: CorePlace::Local { name: fresh.clone(), ty: self.physical_expression(value).ty.clone() },
                    contract: self.contract(value).clone() });
                CoreKind::Let { name: fresh, value }
            }
            CoreKind::Block(values) => {
                let locals = frame.locals.clone();
                let values = self.expressions(values, frame)?;
                let updates = std::mem::replace(&mut frame.locals, locals);
                self.include_storage(frame, &updates, span)?;
                let result = values.last().map(|id| self.physical_expression(*id).ty.clone()).unwrap_or(Type::Unit);
                let semantic = values.last().map(|id| self.contract(*id).clone()).unwrap_or_else(|| ValueContract::ordinary(Type::Unit));
                let result = self.alloc(CoreKind::Block(values), result, span);
                return Ok(self.with_contract(result, semantic));
            }
            CoreKind::Label { brand, body } => {
                let fresh = LabelBrand { owner: self.owner, label: self.fresh() };
                let old = frame.labels.insert(brand, fresh);
                let before = frame.replacements.len();
                let identity = |brand| {
                    let Type::Nominal { arguments, .. } = crate::types::label::new(brand, Type::Unit) else { unreachable!() };
                    let GenericArgument::Type(identity) = arguments[0].clone() else { unreachable!() }; identity
                };
                frame.replacements.push((identity(brand), identity(fresh)));
                let key = (frame.calls.clone(), frame.callable, id);
                let previous = self.active.insert(key.clone(), fresh);
                self.label_results.insert(fresh, vec![]);
                let body = self.expression(body, frame)?;
                self.label_result(fresh, body);
                let results = self.label_results.remove(&fresh).unwrap();
                let (semantic, physical) = self.join_layout(self.semantic_type(frame, expression.ty), &results, span)?;
                if self.values.iter().any(|value| matches!(value.physical.kind, CoreKind::LabelValue { brand } if brand == fresh)
                    && crate::types::label::payload(&value.physical.ty) != Some(&physical)) {
                    return Err(diagnostic(span, "a first-class label payload requires a stable fused result representation"));
                }
                if let Some(previous) = previous { self.active.insert(key, previous); } else { self.active.remove(&key); }
                frame.replacements.truncate(before);
                if let Some(old) = old { frame.labels.insert(brand, old); } else { frame.labels.remove(&brand); }
                let result = self.alloc(CoreKind::Label { brand: fresh, body }, physical, span);
                return Ok(self.with_contract(result, semantic));
            }
            CoreKind::LabelValue { brand } => CoreKind::LabelValue { brand: *frame.labels.get(&brand)
                .ok_or_else(|| diagnostic(span, "label proof has no active fused destination"))? },
            CoreKind::Transfer { brand, value } => {
                let brand = *frame.labels.get(&brand).ok_or_else(|| diagnostic(span, "transfer has no active fused destination"))?;
                let value = self.expression(value, frame)?;
                self.label_result(brand, value);
                CoreKind::Transfer { brand, value }
            }
            CoreKind::Call { callee, arguments, mandatory_tail, reference_contract, reference_origin, reference_shape } => {
                if mandatory_tail && !frame.calls.is_empty() {
                    return Err(diagnostic(span, "expanded mandatory tail invocation requires a fused activation-cleanup contract"));
                }
                let mut selected_expression = source.expression(callee).clone();
                self.static_arguments(&mut selected_expression.kind, frame);
                let observed = self.control.fusion_target(frame.proof_root, &frame.calls, frame.callable, id)
                    .or_else(|| self.control.declared_fusion_target(frame.owner, &selected_expression));
                // Evaluate callee formation, then every explicit input, before
                // installing any parameter or executing the expanded body.
                let value = self.expression(callee, frame)?;
                let values = self.expressions(arguments.clone(), frame)?;
                let target = self.represented_target(self.contract(value)).or_else(|| observed.map(Selected::Observed));
                let mut returned_constructors = BTreeSet::new();
                if let Some(control) = frame.invocations.get(id) {
                    for payload in &control.returns { payload.constructors(&mut returned_constructors); }
                }
                let needed = returned_constructors.into_iter().any(|brand| self.control_captures.contains(brand))
                    || self.physical_expression(value).ty != self.semantic_type(frame, source.expression(callee).ty.clone())
                    || contains_label(&self.semantic_type(frame, source.expression(callee).ty.clone()))
                    || arguments.iter().any(|id| contains_label(&self.semantic_type(frame, source.expression(*id).ty.clone())))
                    || ty != self.semantic_type(frame, expression.ty.clone())
                    || values.iter().zip(&arguments).any(|(value, id)| self.physical_expression(*value).ty != self.semantic_type(frame, source.expression(*id).ty.clone()));
                if needed {
                    if mandatory_tail { return Err(diagnostic(span,
                        "label-bearing mandatory tail invocation requires a fused activation-cleanup contract")); }
                    let target = target.ok_or_else(|| diagnostic(span, "label-bearing invocation has no complete exact callee selection"))?;
                    return self.invoke(id, frame, target, value, values, span);
                }
                let result = self.alloc(CoreKind::Call { callee: value, arguments: values, mandatory_tail, reference_contract, reference_origin, reference_shape }, ty, span);
                return Ok(self.with_semantic(result, self.semantic_type(frame, expression.ty)));
            }
            CoreKind::Closure { callable, parameters, environment, body } => {
                return self.closure(id, frame, callable, parameters, environment, body, expression.ty, span);
            }
            CoreKind::Function { definition, arguments, host_import } => {
                if ty == Type::Unit && expression.ty != Type::Unit {
                    CoreKind::Tuple(vec![])
                } else if matches!(ty, Type::Callable { .. }) {
                    CoreKind::Function { definition, arguments: arguments.into_iter().map(|value| self.argument(frame, value)).collect(), host_import }
                } else { return Err(diagnostic(span, "ordinary code pointer cannot inhabit a fused closure environment")); }
            }
            CoreKind::TraitMethod { .. } | CoreKind::Constant { .. } => {
                let mut kind = expression.kind;
                self.static_arguments(&mut kind, frame);
                if ty == Type::Unit && expression.ty != Type::Unit && matches!(kind, CoreKind::TraitMethod { .. }) { CoreKind::Tuple(vec![]) } else { kind }
            }
            CoreKind::ConstValue(value) => CoreKind::ConstValue(self.argument(frame, value)),
            CoreKind::Tuple(values) => {
                let values = self.expressions(values, frame)?;
                let ty = if values.is_empty() { ty } else {
                    Type::Tuple(values.iter().map(|id| self.physical_expression(*id).ty.clone()).collect())
                };
                let semantic = if values.is_empty() { self.semantic_type(frame, expression.ty) } else {
                    Type::Tuple(values.iter().map(|id| self.semantic(*id).clone()).collect())
                };
                let representation = Representation::fields(values.iter().map(|id| self.contract(*id).representation.clone()).collect());
                let result = self.alloc(CoreKind::Tuple(values), ty, span);
                return Ok(self.with_contract(result, ValueContract { ty: semantic, representation }));
            }
            CoreKind::Array(values) => CoreKind::Array(self.expressions(values, frame)?),
            CoreKind::Record { definition, fields } => CoreKind::Record { definition, fields: self.expressions(fields, frame)? },
            CoreKind::Enum { definition, variant, fields } => CoreKind::Enum { definition, variant, fields: self.expressions(fields, frame)? },
            CoreKind::Field { base, index, field_count } => {
                let base = self.expression(base, frame)?;
                let ty = if let Type::Tuple(fields) = &self.physical_expression(base).ty { fields.get(index as usize).cloned().unwrap_or(ty) } else { ty };
                let semantic = if let Type::Tuple(fields) = self.semantic(base) {
                    fields.get(index as usize).cloned().unwrap_or_else(|| self.semantic_type(frame, expression.ty.clone()))
                } else { self.semantic_type(frame, expression.ty) };
                let representation = self.contract(base).representation.field(index);
                let result = self.alloc(CoreKind::Field { base, index, field_count }, ty, span);
                return Ok(self.with_contract(result, ValueContract { ty: semantic, representation }));
            }
            CoreKind::Assign { place, value } => {
                let value = self.expression(value, frame)?;
                let source_ty = self.semantic_type(frame, place.ty());
                let target = self.place(place.clone(), frame)?;
                if (target.ty() != source_ty || self.physical_expression(value).ty != *self.semantic(value))
                    && target.ty() != self.physical_expression(value).ty {
                    return Err(diagnostic(span, "assigned control environments do not share a checked resident layout"));
                }
                self.assigned_representation(&place, self.contract(value), frame, span)?;
                CoreKind::Assign { place: target, value }
            }
            CoreKind::Borrow { unique, value } => {
                let value = self.expression(value, frame)?;
                let Type::Reference { lifetime, mutability, .. } = ty else { return Err(diagnostic(span, "borrow lacks its frozen reference type")); };
                let ty = Type::Reference { lifetime, mutability, referent: Box::new(self.physical_expression(value).ty.clone()) };
                let semantic = Type::Reference { lifetime, mutability, referent: Box::new(self.semantic(value).clone()) };
                let representation = Representation::reference(self.contract(value).representation.clone());
                let result = self.alloc(CoreKind::Borrow { unique, value }, ty, span);
                return Ok(self.with_contract(result, ValueContract { ty: semantic, representation }));
            }
            CoreKind::Deref(value) => {
                let value = self.expression(value, frame)?;
                let Type::Reference { referent, .. } = self.physical_expression(value).ty.clone() else { return Err(diagnostic(span, "dereference lost its resident reference")); };
                let Type::Reference { referent: semantic, .. } = self.semantic(value).clone() else { return Err(diagnostic(span, "dereference lost its source reference contract")); };
                let representation = match &self.contract(value).representation {
                    Representation::Reference(value) => (**value).clone(), _ => Representation::Ordinary,
                };
                let result = self.alloc(CoreKind::Deref(value), *referent, span);
                return Ok(self.with_contract(result, ValueContract { ty: *semantic, representation }));
            }
            CoreKind::Move(value) => {
                let value = self.expression(value, frame)?;
                let result = self.alloc(CoreKind::Move(value), self.physical_expression(value).ty.clone(), span);
                return Ok(self.with_contract(result, self.contract(value).clone()));
            }
            CoreKind::ReleaseAvailable(value) => CoreKind::ReleaseAvailable(self.expression(value, frame)?),
            CoreKind::IntrinsicCall { operator, arguments } => CoreKind::IntrinsicCall { operator, arguments: self.expressions(arguments, frame)? },
            CoreKind::PatternTest { subject, pattern, refinement } => {
                let subject = self.expression(subject, frame)?;
                CoreKind::PatternTest { subject, pattern: self.pattern(pattern, frame, Some(self.contract(subject).clone())), refinement: self.refinement(refinement, frame) }
            }
            CoreKind::Completion { computation, clauses, refinement_test, handles_operations } => {
                let computation = self.expression(computation, frame)?;
                let mut output = vec![];
                let mut updates = vec![];
                for mut clause in clauses {
                    let locals = frame.locals.clone();
                    clause.pattern = self.pattern(clause.pattern, frame, Some(self.contract(computation).clone()));
                    clause.bindings = self.bindings(clause.bindings, frame);
                    if let Some(ref mut refinement) = clause.refinement {
                        refinement.environment = self.refinement(refinement.environment.clone(), frame);
                        refinement.pattern = self.pattern(refinement.pattern.clone(), frame, Some(self.contract(computation).clone()));
                        refinement.subject = *frame.nodes.get(&refinement.subject).ok_or_else(|| diagnostic(span,
                            "refinement metadata lost its once-evaluated subject"))?;
                    }
                    clause.body = self.expression(clause.body, frame)?;
                    updates.push(std::mem::replace(&mut frame.locals, locals));
                    output.push(clause);
                }
                for update in &updates { self.include_storage(frame, update, span)?; }
                let results = output.iter().map(|clause| (self.contract(clause.body).clone(), self.physical_expression(clause.body).ty.clone())).collect::<Vec<_>>();
                let (semantic, physical) = self.join_layout(self.semantic_type(frame, expression.ty), &results, span)?;
                let refinement_test = refinement_test.map(|value| self.refinement(value, frame));
                let result = self.alloc(CoreKind::Completion { computation, clauses: output, refinement_test, handles_operations }, physical, span);
                return Ok(self.with_contract(result, semantic));
            }
            CoreKind::Perform { effect, operation, operation_arguments, payload_types, arguments, terminal, reference_contract, reference_origin, reference_shape } => CoreKind::Perform {
                effect: self.effect(effect, frame), operation, payload_types: payload_types.into_iter().map(|ty| self.ty(frame, ty)).collect(),
                operation_arguments: operation_arguments.into_iter().map(|argument| self.argument(frame, argument)).collect(),
                arguments: self.expressions(arguments, frame)?, terminal, reference_contract, reference_origin, reference_shape,
            },
            CoreKind::Handle { computation, clauses } => {
                // Reserve the delimiter before composing either side. Its
                // clauses and continuations name this exact output binder;
                // repeated expansions never share a source handler identity.
                let handler = self.alloc(CoreKind::Error, ty.clone(), span);
                let computation = self.expression(computation, frame)?;
                let mut output = vec![];
                let mut results = vec![(self.contract(computation).clone(), self.physical_expression(computation).ty.clone())];
                for (index, mut clause) in clauses.into_iter().enumerate() {
                    let mut child = frame.clone();
                    clause.brand = CallableBrand::HandlerClause { owner: self.owner, handler, clause: index as u32 };
                    clause.effect = self.effect(clause.effect, &child);
                    clause.operation_arguments = clause.operation_arguments.into_iter().map(|argument| self.argument(&child, argument)).collect();
                    clause.payload_types = clause.payload_types.into_iter().map(|ty| self.ty(&child, ty)).collect();
                    clause.patterns = clause.patterns.into_iter().map(|pattern| self.pattern(pattern, &mut child, None)).collect();
                    clause.bindings = self.bindings(clause.bindings, &mut child);
                    if let Some(contract) = &mut clause.continuation {
                        contract.brand = CallableBrand::Continuation { owner: self.owner, handler, clause: index as u32 };
                        contract.parameter = self.ty(&child, contract.parameter.clone());
                        contract.result = self.ty(&child, contract.result.clone());
                        let GenericArgument::EffectRow(effects) = self.argument(&child, GenericArgument::EffectRow(contract.effects.clone())) else { unreachable!() };
                        contract.effects = effects;
                    }
                    if let CoreHandlerResumption::Explicit { id: original, name, .. } = &mut clause.resumption {
                        let contract = clause.continuation.as_ref().ok_or_else(|| diagnostic(clause.span,
                            "expanded resumption has no checked continuation contract"))?;
                        let fresh = ResumptionId(self.fresh());
                        let fresh_name = self.name(name);
                        let ty = contract.callable_type();
                        child.resumptions.insert(*original, (fresh, fresh_name.clone(), ty.clone()));
                        child.locals.insert(name.clone(), Input {
                            place: CorePlace::Local { name: fresh_name.clone(), ty: ty.clone() }, contract: ValueContract::ordinary(ty),
                        });
                        *original = fresh;
                        *name = fresh_name;
                    }
                    clause.body = self.expression(clause.body, &mut child)?;
                    if !matches!(clause.resumption, CoreHandlerResumption::Tail { .. }) {
                        results.push((self.contract(clause.body).clone(), self.physical_expression(clause.body).ty.clone()));
                    }
                    output.push(clause);
                }
                let (semantic, physical) = self.join_layout(self.semantic_type(frame, expression.ty), &results, span)?;
                // The continuation may return through a surrounding normal
                // completion transform rather than this protected region.
                // Do not silently alter that already-bound callable ABI.
                if physical != ty && output.iter().any(|clause| clause.continuation.is_some()) {
                    return Err(diagnostic(span, "handler result representation changed after binding its resumption ABI"));
                }
                self.values[handler.0 as usize] = Value { contract: semantic, physical: CoreExpr {
                    kind: CoreKind::Handle { computation, clauses: output }, ty: physical, span,
                } };
                return Ok(handler);
            }
            CoreKind::Resumption { id, .. } => {
                let (id, name, contract) = frame.resumptions.get(&id).cloned().ok_or_else(|| diagnostic(span,
                    "resumption has no active expanded lexical binder"))?;
                if contract != ty { return Err(diagnostic(span, "expanded resumption differs from its bound continuation ABI")); }
                CoreKind::Resumption { id, name }
            }
            CoreKind::Literal(value) => CoreKind::Literal(value),
            CoreKind::Error => return Err(diagnostic(span, "recovered Core cannot enter control fusion")),
        };
        let result = self.alloc(kind, ty, span);
        Ok(result)
    }
    fn expressions(&mut self, values: Vec<CoreId>, frame: &mut Frame) -> Result<Vec<CoreId>, CoreDiagnostic> {
        values.into_iter().map(|value| self.expression(value, frame)).collect()
    }
    fn static_arguments(&self, kind: &mut CoreKind, frame: &Frame) {
        match kind {
            CoreKind::Function { arguments, .. } | CoreKind::Constant { arguments, .. } => {
                *arguments = arguments.iter().cloned().map(|value| self.argument(frame, value)).collect();
            }
            CoreKind::TraitMethod { trait_arguments, method_arguments, deferred, .. } => {
                *trait_arguments = trait_arguments.iter().cloned().map(|value| self.argument(frame, value)).collect();
                *method_arguments = method_arguments.iter().cloned().map(|value| self.argument(frame, value)).collect();
                if let Some(deferred) = deferred {
                    deferred.subject = self.semantic_type(frame, deferred.subject.clone());
                    deferred.relation.arguments = deferred.relation.arguments.iter().cloned().map(|value| self.argument(frame, value)).collect();
                }
            }
            _ => {}
        }
    }
    fn place(&mut self, place: CorePlace, frame: &mut Frame) -> Result<CorePlace, CoreDiagnostic> {
        Ok(match place {
            CorePlace::Local { name, ty } => frame.locals.get(&name).map(|input| input.place.clone()).unwrap_or(CorePlace::Local { name, ty: self.ty(frame, ty) }),
            CorePlace::Field { base, index, field_count, ty } => CorePlace::Field { base: Box::new(self.place(*base, frame)?), index, field_count, ty: self.ty(frame, ty) },
            CorePlace::Deref { reference, ty, unique } => CorePlace::Deref { reference: self.expression(reference, frame)?, ty: self.ty(frame, ty), unique },
            CorePlace::Error => CorePlace::Error,
        })
    }
    fn bindings(&mut self, bindings: Vec<(String, Type)>, frame: &mut Frame) -> Vec<(String, Type)> {
        bindings.into_iter().map(|(name, ty)| {
            let semantic = self.semantic_type(frame, ty.clone());
            let fresh = match frame.locals.get(&name) {
                Some(Input { place: CorePlace::Local { name, .. }, .. }) => name.clone(),
                _ => self.name(&name),
            };
            let representation = frame.locals.get(&name).map(|input| input.contract.representation.clone()).unwrap_or(Representation::Ordinary);
            let contract = ValueContract { ty: semantic, representation };
            let ty = self.resident_type(&contract);
            frame.locals.insert(name, Input { place: CorePlace::Local { name: fresh.clone(), ty: ty.clone() }, contract });
            (fresh, ty)
        }).collect()
    }
    fn pattern(&mut self, pattern: CorePattern, frame: &mut Frame, subject: Option<ValueContract>) -> CorePattern {
        match pattern {
            CorePattern::Bind { name } => {
                let fresh = self.name(&name);
                let contract = subject.unwrap_or_else(|| ValueContract::ordinary(Type::Unit));
                let ty = self.resident_type(&contract);
                frame.locals.insert(name, Input { place: CorePlace::Local { name: fresh.clone(), ty }, contract });
                CorePattern::Bind { name: fresh }
            }
            CorePattern::Tuple(values) => CorePattern::Tuple(values.into_iter().enumerate().map(|(index, value)| {
                let field = subject.as_ref().and_then(|subject| match &subject.ty {
                    Type::Tuple(fields) => fields.get(index).map(|ty| ValueContract { ty: ty.clone(), representation: subject.representation.field(index as u32) }),
                    _ => None,
                });
                self.pattern(value, frame, field)
            }).collect()),
            CorePattern::Array { element, elements, rest } => CorePattern::Array { element: self.ty(frame, element.clone()),
                elements: elements.into_iter().enumerate().map(|(index, value)| self.pattern(value, frame,
                    subject.as_ref().map(|subject| ValueContract { ty: self.semantic_type(frame, element.clone()),
                        representation: subject.representation.field(index as u32) }))).collect(), rest },
            mut value @ (CorePattern::Record { .. } | CorePattern::Enum { .. }) => {
                let (field_types, fields) = match &mut value {
                    CorePattern::Record { field_types, fields, .. } | CorePattern::Enum { field_types, fields, .. } => (field_types, fields),
                    _ => unreachable!(),
                };
                for ty in field_types { *ty = self.ty(frame, ty.clone()); }
                for (index, field) in fields.iter_mut().enumerate() {
                    let contract = subject.as_ref().map(|subject| ValueContract { ty: self.semantic_type(frame, field.ty.clone()),
                        representation: subject.representation.field(index as u32) });
                    field.ty = contract.as_ref().map(|contract| self.resident_type(contract)).unwrap_or_else(|| self.ty(frame, field.ty.clone()));
                    field.pattern = self.pattern(field.pattern.clone(), frame, contract);
                }
                value
            }
            value => value,
        }
    }
    fn refinement(&mut self, mut value: RefinementEnvironment, frame: &mut Frame) -> RefinementEnvironment {
        value.brand = frame.refinements.get(&value.brand).copied().unwrap_or(value.brand);
        for key in &mut value.binding_keys { key.environment = value.brand; }
        value.subject = value.subject.map(|name| match frame.locals.get(&name) {
            Some(Input { place: CorePlace::Local { name, .. }, .. }) => name.clone(), _ => name,
        });
        value.binding_types = self.bindings(value.binding_types, frame);
        value.bindings = value.binding_types.iter().map(|(name, _)| name.clone()).collect();
        value
    }
    fn effect(&self, mut effect: EffectInstance, frame: &Frame) -> EffectInstance {
        effect.arguments = effect.arguments.into_iter().map(|value| self.argument(frame, value)).collect(); effect
    }
    fn closure(&mut self, id: CoreId, frame: &mut Frame, _callable: CallableId, parameters: Vec<(String, Type)>,
        mut environment: CaptureEnvironment, body: CoreId, source_ty: Type, span: Span) -> Result<CoreId, CoreDiagnostic> {
        let constructor = self.control.closure_constructor(frame.owner, id)
            .ok_or_else(|| diagnostic(span, "closure formation lacks a sealed control contract"))?;
        let free = constructor.labels();
        let semantic_ty = self.semantic_type(frame, source_ty);
        let transformed_capture = environment.captures.iter().any(|capture|
            contains_label(&self.semantic_type(frame, capture.ty.clone()))
                || frame.locals.get(&capture.name).is_some_and(|input|
                    input.place.ty() != input.contract.ty || input.contract.representation != Representation::Ordinary));
        if !free.is_empty() || transformed_capture || self.control_captures.contains(environment.brand) {
            let tag = self.alloc(CoreKind::Literal(self.environments.len().to_string()), Type::Scalar(ScalarType::I64), span);
            let mut fields = vec![tag];
            let mut captures = vec![];
            for capture in &environment.captures {
                let place = frame.locals.get(&capture.name).cloned().ok_or_else(|| diagnostic(span, "missing closure formation storage"))?;
                let value = self.resident(place, span);
                let ty = self.physical_expression(value).ty.clone();
                captures.push(self.contract(value).clone());
                fields.push(match CaptureFormation::new(capture).source() {
                    CaptureSource::Copy => value,
                    CaptureSource::Move => self.alloc(CoreKind::Move(value), ty, span),
                    CaptureSource::Borrow(mutability) => self.alloc(CoreKind::Borrow { unique: mutability == Mutability::Unique, value },
                        Type::Reference { mutability, lifetime: Lifetime::Elided, referent: Box::new(ty) }, span),
                });
            }
            for brand in free {
                let target = frame.labels.get(brand).copied().ok_or_else(|| diagnostic(span, "closure captures an inactive label"))?;
                let payload = self.source(frame.owner).expressions.iter().find_map(|expression| match expression.kind {
                    CoreKind::Label { brand: actual, .. } if actual == *brand => Some(self.ty(frame, expression.ty.clone())), _ => None,
                }).ok_or_else(|| diagnostic(span, "lexical label has no payload contract"))?;
                fields.push(self.alloc(CoreKind::LabelValue { brand: target }, crate::types::label::new(target, payload), span));
            }
            let physical = Type::Tuple(fields.iter().map(|id| self.physical_expression(*id).ty.clone()).collect());
            if constructor.nominal_type() && self.environments.iter().any(|old| old.semantic == semantic_ty && old.resident != physical) {
                return Err(diagnostic(span, "alternative control environments require a common checked resident layout"));
            }
            let labels = free.iter().map(|brand| (*brand, frame.labels[brand])).collect();
            let representation = Representation::Callable([self.environments.len()].into());
            self.environments.push(ControlEnvironment { constructor, semantic: semantic_ty.clone(), resident: physical.clone(),
                arguments: frame.arguments.clone(), labels, captures });
            let result = self.alloc(CoreKind::Tuple(fields), physical, span);
            return Ok(self.with_contract(result, ValueContract { ty: semantic_ty, representation }));
        }
        let outer = frame.clone();
        let mut child = frame.clone();
        child.callable = CallableBrand::Closure(environment.brand);
        child.proof_root = child.callable;
        child.calls.clear();
        child.nodes.clear();
        child.locals.clear();
        child.resumptions.clear();
        for capture in &mut environment.captures {
            let Some(input @ Input { place: CorePlace::Local { name, ty }, .. }) = outer.locals.get(&capture.name) else {
                return Err(diagnostic(span, "resident nested closure requires a projected capture formation contract"));
            };
            child.locals.insert(capture.name.clone(), input.clone());
            capture.name = name.clone(); capture.ty = ty.clone();
        }
        let parameters = self.bindings(parameters, &mut child);
        let body = self.expression(body, &mut child)?;
        environment.brand = frame.environments[&environment.brand];
        environment.post_states = environment.captures.iter().map(|capture| CapturePostState { name: capture.name.clone(), mode: capture.mode }).collect();
        environment.runs_in.environment = environment.brand;
        environment.runs_in.callable = environment.brand.callable;
        environment.runs_in.post_states = environment.post_states.clone();
        let GenericArgument::EffectRow(effects) = self.argument(frame, GenericArgument::EffectRow(environment.runs_in.effects.clone())) else { unreachable!() };
        environment.runs_in.effects = effects;
        Ok(self.alloc(CoreKind::Closure { callable: environment.brand.callable, parameters, environment, body }, semantic_ty, span))
    }
    fn invoke(&mut self, id: CoreId, parent: &mut Frame, target: Selected, callee: CoreId,
        arguments: Vec<CoreId>, span: Span) -> Result<CoreId, CoreDiagnostic> {
        let mut prefix = vec![];
        let receiver = self.bind("callee", callee, span, &mut prefix);
        let values = arguments.into_iter().map(|value| self.bind("argument", value, span, &mut prefix)).collect::<Vec<_>>();
        let target = match target {
            Selected::Observed(FusionTarget::Label(target)) => Selected::Label(self.target(&target, span)?),
            target => target,
        };
        match target {
            Selected::Dispatch(environments) => {
                let mut environment = receiver.place.clone();
                while let Type::Reference { referent, mutability, .. } = environment.ty() {
                    let reference = self.resident_place(environment, span);
                    environment = CorePlace::Deref { reference, ty: *referent, unique: mutability == Mutability::Unique };
                }
                let Type::Tuple(fields) = environment.ty() else { return Err(diagnostic(span,
                    "control dispatch requires a represented closure value, not an opaque callable")); };
                if fields.first() != Some(&Type::Scalar(ScalarType::I64)) || environments.iter().any(|index|
                    self.environments[*index].resident != environment.ty()) {
                    return Err(diagnostic(span, "control dispatch does not match its sealed environment layouts"));
                }
                let tag = self.resident_place(CorePlace::Field { base: Box::new(environment), index: 0,
                    field_count: fields.len() as u32, ty: Type::Scalar(ScalarType::I64) }, span);
                let mut clauses = vec![];
                let last = environments.len().saturating_sub(1);
                for (position, index) in environments.into_iter().enumerate() {
                    let callee = self.resident(receiver.clone(), span);
                    let arguments = values.iter().map(|input| self.resident(input.clone(), span)).collect();
                    let body = self.invoke(id, parent, Selected::Environment(index), callee, arguments, span)?;
                    clauses.push(CoreCompletionClause { pattern: if position == last { CorePattern::Any }
                        else { CorePattern::Literal(index.to_string()) }, bindings: vec![], refinement: None, body, span });
                }
                let expected = self.semantic_type(parent, self.source(parent.owner).expression(id).ty.clone());
                let results = clauses.iter().map(|clause| (self.contract(clause.body).clone(), self.physical_expression(clause.body).ty.clone())).collect::<Vec<_>>();
                let (semantic, physical) = self.join_layout(expected, &results, span)?;
                let dispatch = self.alloc(CoreKind::Completion { computation: tag, clauses,
                    refinement_test: None, handles_operations: false }, physical, span);
                self.with_contract(dispatch, semantic);
                prefix.push(dispatch);
            }
            Selected::Label(brand) => {
                let [value] = values.as_slice() else { return Err(diagnostic(span, "label fusion requires exactly one payload")); };
                let value = self.resident(value.clone(), span);
                self.label_result(brand, value);
                prefix.push(self.alloc(CoreKind::Transfer { brand, value }, Type::Never, span));
            }
            target => {
                let (brand, generic_arguments, labels, capture_types) = match target {
                    Selected::Environment(index) => {
                        let environment = &self.environments[index];
                        (CallableBrand::Closure(environment.constructor.brand()), environment.arguments.clone(), environment.labels.clone(), Some(environment.captures.clone()))
                    }
                    Selected::Observed(FusionTarget::Callable { brand, generic_arguments, labels }) => {
                        let labels = labels.into_iter().map(|(brand, target)| self.target(&target, span).map(|target| (brand, target)))
                            .collect::<Result<BTreeMap<_, _>, _>>()?;
                        (brand, generic_arguments, labels, None)
                    }
                    _ => unreachable!("label selections were normalized above"),
                };
                if labels.values().any(|brand| !self.active.values().any(|active| active == brand)) {
                    return Err(diagnostic(span, "label-bearing environment outlived its active lexical destination"));
                }
                if self.stack.contains(&brand) || self.stack.len() >= 32 {
                    return Err(diagnostic(span, "recursive label-bearing invocation requires a finite structural fusion proof"));
                }
                let (owner, closure) = match brand {
                    CallableBrand::Named(owner) => (owner, None),
                    CallableBrand::Closure(environment) => (environment.owner, Some(environment)),
                    _ => return Err(diagnostic(span, "unsupported control callable boundary")),
                };
                let input = self.control.fusion_body(owner).map_err(|reason| diagnostic(span,
                    format!("selected control callable body is unavailable: {reason:?}")))?;
                let (root, parameters, captures) = if let Some(closure) = closure {
                    input.expressions.iter().find_map(|expression| match &expression.kind {
                        CoreKind::Closure { environment, parameters, body, .. } if environment.brand == closure => Some((*body, parameters.clone(), environment.captures.clone())),
                        _ => None,
                    }).ok_or_else(|| diagnostic(span, "selected closure environment is absent"))?
                } else { (input.root, input.parameters.clone(), vec![]) };
                if parameters.len() != values.len() { return Err(diagnostic(span, "expanded invocation input arity mismatch")); }
                let mut calls = parent.calls.clone(); calls.push((parent.callable, id));
                let arguments = generic_arguments.map(|values| values.into_iter().map(|value| self.rename(parent, value)).collect());
                let mut child = self.frame(owner, brand, arguments, calls, parent.replacements.clone())?;
                child.proof_root = parent.proof_root;
                child.labels = labels;
                if !captures.is_empty() {
                    let mut environment = receiver.place.clone();
                    while let Type::Reference { referent, mutability, .. } = environment.ty() {
                        let reference = self.resident_place(environment, span);
                        environment = CorePlace::Deref { reference, ty: *referent, unique: mutability == Mutability::Unique };
                    }
                    let Type::Tuple(fields) = environment.ty() else { return Err(diagnostic(span, "expanded capture environment has no checked resident tuple")); };
                    if fields.len() < captures.len() + 1 { return Err(diagnostic(span, "expanded capture layout is incomplete")); }
                    for (index, capture) in captures.iter().enumerate() {
                        let field = index + 1;
                        let mut place = CorePlace::Field { base: Box::new(environment.clone()), index: field as u32, field_count: fields.len() as u32, ty: fields[field].clone() };
                        if let CaptureSource::Borrow(mutability) = CaptureFormation::new(capture).source() {
                            let reference = self.resident_place(place, span);
                            let Type::Reference { referent, .. } = fields[field].clone() else { return Err(diagnostic(span, "borrowed capture lost its resident reference")); };
                            place = CorePlace::Deref { reference, ty: *referent, unique: mutability == Mutability::Unique };
                        }
                        let contract = capture_types.as_ref().and_then(|types| types.get(index)).cloned()
                            .unwrap_or_else(|| ValueContract::ordinary(self.semantic_type(&child, capture.ty.clone())));
                        child.locals.insert(capture.name.clone(), Input { place, contract });
                    }
                }
                for ((name, _), value) in parameters.into_iter().zip(values) { child.locals.insert(name, value); }
                self.output.unsafe_implementations.extend(&input.unsafe_implementations);
                self.stack.push(brand);
                let value = self.expression(root, &mut child)?;
                if input.safety == crate::Safety::Unsafe { self.output.unsafe_scopes.insert(value); }
                self.stack.pop();
                prefix.push(value);
            }
        }
        let last = *prefix.last().expect("expanded invocation has a result or transfer");
        let result = self.physical_expression(last).ty.clone();
        let semantic = self.contract(last).clone();
        let result = self.alloc(CoreKind::Block(prefix), result, span);
        Ok(self.with_contract(result, semantic))
    }
}
