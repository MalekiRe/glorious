//! Delimited control is composed here, independently of source nesting.
//! Dynamic edges retain their owner; they are not interchangeable with CFG
//! jumps. Place operands identify storage without introducing an owner read.
use super::*;
use crate::core::{CaptureEnvironment, CoreHandlerResumption, CorePattern, DeferredTraitMethod};
use crate::evaluation_mir::{EvaluationInstruction, EvaluationPlace};
use crate::{EffectInstance, LabelBrand, Mutability, ScalarType};

fn pattern_is_irrefutable(pattern: &CorePattern) -> bool {
    match pattern {
        CorePattern::Any | CorePattern::Bind { .. } => true,
        CorePattern::Tuple(fields) => fields.iter().all(pattern_is_irrefutable),
        CorePattern::Record { fields, .. } => fields.iter().all(|field| pattern_is_irrefutable(&field.pattern)),
        CorePattern::Array { .. } | CorePattern::Enum { .. } | CorePattern::Literal(_) | CorePattern::Error => false,
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ControlLabelId(pub u32);
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ControlHandlerId(pub u32);
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ControlClosureId(pub u32);

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ControlPlace {
    Local(ControlValue),
    Temporary(ControlValue),
    Field { base: Box<Self>, index: u32, field_count: u32, ty: Type },
    Deref { reference: ControlValue, ty: Type },
}
impl ControlPlace {
    pub fn root(&self) -> ControlValue {
        match self {
            Self::Local(value) | Self::Temporary(value) => *value,
            Self::Deref { reference, .. } => *reference,
            Self::Field { base, .. } => base.root(),
        }
    }
    fn ty<'a>(&'a self, body: &'a ControlMir) -> Result<&'a Type, ControlError> {
        match self {
            Self::Local(value) | Self::Temporary(value) => body.ty(*value),
            Self::Field { ty, .. } | Self::Deref { ty, .. } => Ok(ty),
        }
    }
}

impl ControlMir {
    pub(super) fn validate_payload_acceptance(&self) -> Result<(), ControlError> {
        let invalid = || ControlError::Invalid("handler payload acceptance does not follow its complete pattern gate".into());
        for (handler_id, handler) in self.handlers.iter().enumerate() {
            for (clause_id, clause) in handler.clauses.iter().enumerate() {
                let mut current = clause.entry;
                if clause.patterns.len() != clause.payloads.len() { return Err(invalid()); }
                for (pattern, payload) in clause.patterns.iter().zip(&clause.payloads) {
                    if pattern_is_irrefutable(pattern) { continue; }
                    let block = self.blocks.get(current.0 as usize).ok_or_else(invalid)?;
                    let [test] = block.instructions.as_slice() else { return Err(invalid()); };
                    if !matches!(&test.operation, ControlOperation::Capability(ControlCapabilityOperation::Test { subject, pattern: actual })
                        if subject == payload && actual == pattern) { return Err(invalid()); }
                    let ControlTerminator::SwitchBool { condition, on_true, on_false } = &block.terminator else { return Err(invalid()); };
                    if *condition != test.destination || !on_true.arguments.is_empty() || !on_false.arguments.is_empty() { return Err(invalid()); }
                    let rejected = self.blocks.get(on_false.target.0 as usize).ok_or_else(invalid)?;
                    if !rejected.instructions.is_empty() || !matches!(rejected.terminator,
                        ControlTerminator::Transfer(ControlTransfer::Forward { handler, clause })
                            if handler.0 as usize == handler_id && clause as usize == clause_id) { return Err(invalid()); }
                    current = on_true.target;
                }
                if current != clause.accepted || self.blocks.get(current.0 as usize).is_none() { return Err(invalid()); }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ControlLabel {
    pub brand: LabelBrand,
    pub scope: ControlScopeId,
    pub target: ControlBlockId,
    pub result: ControlValue,
    /// Lexically retained handler clauses, outermost first. A clause body
    /// retains its selected handler and the lower-priority clauses below it;
    /// higher-priority clauses are suspended with the protected computation.
    pub handler_prefix: Vec<(ControlHandlerId, u32)>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ControlHandlerClause {
    pub effect: EffectInstance,
    pub operation: u32,
    pub patterns: Vec<CorePattern>,
    pub payloads: Vec<ControlValue>,
    pub resumption: CoreHandlerResumption,
    pub contract: Option<crate::CoreHandlerContinuationContract>,
    pub entry: ControlBlockId,
    /// First block after every payload pattern has accepted. Until this
    /// boundary the packet is observable but may only be forwarded intact.
    pub accepted: ControlBlockId,
    pub token: Option<ControlValue>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ControlHandler {
    pub scope: ControlScopeId,
    pub clauses: Vec<ControlHandlerClause>,
    pub target: ControlBlockId,
    pub result: ControlValue,
}

/// Validate the frozen lexical prefix independently of the composing stack.
/// Each active delimiter contributes its installed reverse-order clause
/// suffix, and each delimiter appears only once in the prefix.
pub(crate) fn valid_label_handler_prefix(label: &ControlLabel, handlers: &[ControlHandler]) -> bool {
    let mut seen = BTreeSet::new();
    let mut previous = None;
    for &(handler, clause) in &label.handler_prefix {
        let Some(owner) = handlers.get(handler.0 as usize) else { return false; };
        if clause as usize >= owner.clauses.len() { return false; }
        match previous {
            Some((last_handler, last_clause)) if last_handler == handler => {
                if last_clause != clause + 1 { return false; }
            }
            _ => {
                if !seen.insert(handler) || clause as usize + 1 != owner.clauses.len() { return false; }
            }
        }
        previous = Some((handler, clause));
    }
    true
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ControlClosure {
    pub environment: CaptureEnvironment,
    pub body: Box<ControlMir>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ControlCapabilityOperation {
    HostFunction { definition: DefKey, arguments: Vec<GenericArgument>, import: crate::signature::HostImport },
    TraitMethod { evidence: DefKey, method: DefKey, trait_arguments: Vec<GenericArgument>, method_arguments: Vec<GenericArgument>, deferred: Option<DeferredTraitMethod> },
    Constant { definition: DefKey, arguments: Vec<GenericArgument> },
    Record { definition: DefKey, fields: Vec<ControlValue> },
    Enum { definition: DefKey, variant: u32, fields: Vec<ControlValue> },
    Project { base: ControlValue, index: u32, field_count: u32 },
    Test { subject: ControlValue, pattern: CorePattern },
    Borrow { place: ControlPlace, unique: bool },
    ReadReference(ControlValue),
    ReadPlace(ControlPlace),
    Move(ControlPlace),
    Assign { place: ControlPlace, value: ControlValue },
    Label(ControlLabelId),
    Resumption { handler: ControlHandlerId, clause: u32 },
    Closure { closure: ControlClosureId, captures: Vec<ControlValue> },
}
impl ControlCapabilityOperation {
    pub(super) fn inputs(&self) -> Vec<ControlValue> {
        match self {
            Self::Record { fields, .. } | Self::Enum { fields, .. } => fields.clone(),
            Self::Project { base, .. } => vec![*base],
            Self::Test { subject, .. } => vec![*subject],
            Self::Borrow { place, .. } | Self::Move(place) | Self::ReadPlace(place) => vec![place.root()],
            Self::ReadReference(value) => vec![*value],
            Self::Assign { place, value } => vec![*value, place.root()],
            Self::Closure { captures, .. } => captures.clone(),
            _ => vec![],
        }
    }
    pub(super) fn validate(&self, body: &ControlMir, result: &Type) -> Result<bool, ControlError> {
        Ok(match self {
            Self::Test { .. } => result == &Type::Scalar(ScalarType::Bool),
            Self::Borrow { place, unique } => matches!(result, Type::Reference { mutability, referent, .. }
                if (*mutability == Mutability::Unique) == *unique && referent.as_ref() == place.ty(body)?),
            Self::ReadReference(value) => matches!(body.ty(*value)?, Type::Reference { referent, .. } if referent.as_ref() == result),
            Self::Move(place) | Self::ReadPlace(place) => place.ty(body)? == result,
            Self::Assign { place, value } => result == &Type::Unit && place.ty(body)? == body.ty(*value)?,
            Self::Label(id) => body.labels.get(id.0 as usize).is_some() && matches!(result, Type::Callable { result, .. } if **result == Type::Never),
            Self::Resumption { handler, clause } => body.handlers.get(handler.0 as usize)
                .and_then(|handler| handler.clauses.get(*clause as usize)).is_some()
                && matches!(result, Type::Callable { .. }),
            Self::Closure { closure, captures } => body.closures.get(closure.0 as usize)
                .is_some_and(|closure| closure.environment.captures.len() == captures.len()) && matches!(result, Type::Callable { .. }),
            Self::HostFunction { .. } | Self::TraitMethod { .. } => matches!(result, Type::Callable { .. }),
            Self::Project { index, field_count, .. } => index < field_count,
            Self::Record { .. } | Self::Enum { .. } | Self::Constant { .. } => !matches!(result, Type::Error | Type::Infer(_)),
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ControlTransfer {
    Leave { label: ControlLabelId, edge: ControlEdge },
    EnterHandler { handler: ControlHandlerId, computation: ControlEdge, clauses: Vec<ControlEdge> },
    CompleteHandler { handler: ControlHandlerId, value: ControlValue, edge: ControlEdge },
    FinishClause { handler: ControlHandlerId, clause: u32, value: ControlValue, edge: ControlEdge },
    TailResume { handler: ControlHandlerId, clause: u32, value: ControlValue },
    Forward { handler: ControlHandlerId, clause: u32 },
    Perform { effect: EffectInstance, operation: u32, arguments: Vec<ControlValue>,
        payload_types: Vec<Type>, result: ControlValue, contract: EvaluationCallContract,
        continuation: Option<ControlBlockId> },
}
impl ControlTransfer {
    pub(super) fn edges(&self) -> Vec<ControlEdge> {
        match self {
            Self::Leave { edge, .. } | Self::CompleteHandler { edge, .. } | Self::FinishClause { edge, .. } => vec![edge.clone()],
            Self::EnterHandler { computation, clauses, .. } => std::iter::once(computation.clone()).chain(clauses.clone()).collect(),
            Self::Perform { result, continuation: Some(target), .. } => vec![ControlEdge { target: *target, arguments: vec![*result] }],
            _ => vec![],
        }
    }
    pub(super) fn inputs(&self) -> Vec<ControlValue> {
        match self {
            Self::Leave { edge, .. } => edge.arguments.clone(),
            Self::CompleteHandler { value, .. } | Self::FinishClause { value, .. } | Self::TailResume { value, .. } => vec![*value],
            Self::Perform { arguments, .. } => arguments.clone(),
            Self::EnterHandler { computation, .. } => computation.arguments.clone(),
            Self::Forward { .. } => vec![],
        }
    }
}

impl ControlMir {
    pub fn labels(&self) -> &[ControlLabel] { &self.labels }
    pub fn handlers(&self) -> &[ControlHandler] { &self.handlers }
    pub fn closures(&self) -> &[ControlClosure] { &self.closures }
    pub fn parameters(&self) -> &[ControlValue] { &self.parameters }
}

impl Builder<'_> {
    fn arm_scope(&mut self, region: EvaluationRegionId, parent: ControlScopeId) -> Result<ControlScopeId, ControlError> {
        let scope = ControlScopeId(u32::try_from(self.result.scopes.len())
            .map_err(|_| ControlError::Invalid("scope arena exhausted".into()))?);
        self.result.scopes.push(ControlScope { parent: Some(parent),
            source: self.evaluation.regions()[region.0 as usize].source, unsafe_scope: false, bindings: vec![],
        });
        Ok(scope)
    }
    fn finish_arm_scope(&mut self, scope: ControlScopeId, block: ControlBlockId, value: ControlValue,
        source: CoreId, span: Span) -> Result<ControlValue, ControlError> {
        let result = self.value(self.result.ty(value)?.clone(), source, span)?;
        self.emit(block, scope, result, ControlOperation::EndScope { scope, value, transferred: None });
        Ok(result)
    }
    fn forward_result_type(&mut self, block: ControlBlockId, scope: ControlScopeId,
        value: ControlValue, expected: &Type) -> Result<ControlValue, ControlError> {
        let actual = self.result.ty(value)?;
        if actual == expected { return Ok(value); }
        if !call_type_matches(expected, actual) {
            return Err(ControlError::Invalid("result forwarding changes its runtime value shape".into()));
        }
        // Core checked the directional lifetime contract. Materialize its
        // representation-preserving forwarding before the CFG join, keeping
        // every later edge's type equality exact and its ownership transfer
        // explicit (a static Slice entering a caller-region result is one
        // example). This does not duplicate the incoming value.
        let source = self.result.values[value.0 as usize].clone();
        let result = self.value(expected.clone(), source.source, source.span)?;
        self.emit(block, scope, result, ControlOperation::Forward(value));
        Ok(result)
    }
    fn place(&self, place: &EvaluationPlace, names: &BTreeMap<String, ControlValue>) -> Result<ControlPlace, ControlError> {
        let lookup = |value| self.mapped.get(&value).copied().ok_or_else(|| ControlError::Invalid("missing place operand".into()));
        Ok(match place {
            EvaluationPlace::Local { name, .. } => ControlPlace::Local(*names.get(name)
                .ok_or_else(|| ControlError::Invalid(format!("unbound place {name}")))?),
            EvaluationPlace::Temporary { value, .. } => ControlPlace::Temporary(lookup(*value)?),
            EvaluationPlace::Field { base, index, field_count, ty } => ControlPlace::Field {
                base: Box::new(self.place(base, names)?), index: *index, field_count: *field_count, ty: ty.clone(),
            },
            EvaluationPlace::Deref { reference, ty } => ControlPlace::Deref { reference: lookup(*reference)?, ty: ty.clone() },
        })
    }
    fn transfer(&mut self, block: ControlBlockId, transfer: ControlTransfer) {
        self.result.blocks[block.0 as usize].terminator = ControlTerminator::Transfer(transfer);
    }
    fn edge(&mut self, from: ControlBlockId, to: ControlBlockId, value: ControlValue) {
        self.result.blocks[from.0 as usize].terminator = ControlTerminator::Goto(ControlEdge { target: to, arguments: vec![value] });
    }
    fn bind_pattern(&mut self, pattern: &CorePattern, subject: ControlValue, block: ControlBlockId,
        scope: ControlScopeId, names: &mut BTreeMap<String, ControlValue>, types: &[(String, Type)],
        source: CoreId, span: Span) -> Result<(), ControlError> {
        let place = match (pattern, self.result.ty(subject)?) {
            (CorePattern::Tuple(_) | CorePattern::Record { .. } | CorePattern::Enum { .. } | CorePattern::Array { .. },
                Type::Reference { referent, .. }) => ControlPlace::Deref { reference: subject, ty: (**referent).clone() },
            _ => ControlPlace::Local(subject),
        };
        self.bind_place_pattern(pattern, place, block, scope, names, types, source, span)
    }
    fn bind_place_pattern(&mut self, pattern: &CorePattern, place: ControlPlace, block: ControlBlockId,
        scope: ControlScopeId, names: &mut BTreeMap<String, ControlValue>, types: &[(String, Type)],
        source: CoreId, span: Span) -> Result<(), ControlError> {
        fn borrowed(place: &ControlPlace) -> bool {
            match place {
                ControlPlace::Deref { .. } => true,
                ControlPlace::Field { base, .. } => borrowed(base),
                _ => false,
            }
        }
        let empty_constructor = match pattern {
            CorePattern::Record { field_count, .. } | CorePattern::Enum { field_count, .. } => *field_count == 0,
            CorePattern::Tuple(fields) => fields.is_empty(),
            CorePattern::Array { elements, rest, .. } => crate::pattern::ArrayPatternRest::length(*rest, elements.len()) == Some(0),
            _ => false,
        };
        if empty_constructor && !borrowed(&place) {
            // Opening an owned empty constructor is a real use. In particular,
            // an affine/linear zero-sized field must leave a logical move hole
            // in its parent even though it introduces no payload binders.
            let consumed = self.value(place.ty(&self.result)?.clone(), source, span)?;
            self.emit(block, scope, consumed, ControlOperation::Capability(ControlCapabilityOperation::Move(place)));
            return Ok(());
        }
        match pattern {
            CorePattern::Bind { name } => {
                let ty = types.iter().find(|(binding, _)| binding == name).map(|(_, ty)| ty.clone())
                    .ok_or_else(|| ControlError::Invalid("pattern binder lost its frozen type".into()))?;
                let actual = place.ty(&self.result)?;
                let operation = if &ty == actual {
                    ControlCapabilityOperation::ReadPlace(place)
                } else if let Type::Reference { mutability, referent, .. } = &ty
                    && referent.as_ref() == actual {
                    ControlCapabilityOperation::Borrow { place, unique: *mutability == Mutability::Unique }
                } else {
                    return Err(ControlError::Invalid(format!("pattern binder type mismatch: {ty:?} against {actual:?}")));
                };
                let binding = self.value(ty, source, span)?;
                self.emit(block, scope, binding, ControlOperation::Capability(operation));
                self.result.scopes[scope.0 as usize].bindings.push(binding);
                names.insert(name.clone(), binding);
            }
            CorePattern::Tuple(patterns) => {
                let Type::Tuple(types_of_fields) = place.ty(&self.result)?.clone() else { return Err(ControlError::Invalid("tuple pattern on non-tuple".into())); };
                for (index, (pattern, ty)) in patterns.iter().zip(types_of_fields).enumerate() {
                    self.bind_place_pattern(pattern, ControlPlace::Field { base: Box::new(place.clone()),
                        index: index as u32, field_count: patterns.len() as u32, ty,
                    }, block, scope, names, types, source, span)?;
                }
            }
            CorePattern::Record { fields, field_count, .. } | CorePattern::Enum { fields, field_count, .. } => {
                for field in fields {
                    self.bind_place_pattern(&field.pattern, ControlPlace::Field { base: Box::new(place.clone()),
                        index: field.index, field_count: *field_count, ty: field.ty.clone(),
                    }, block, scope, names, types, source, span)?;
                }
            }
            CorePattern::Array { element, elements, rest } => {
                for (index, pattern) in elements.iter().enumerate() {
                    self.bind_place_pattern(pattern, ControlPlace::Field { base: Box::new(place.clone()),
                        index: crate::pattern::ArrayPatternRest::index(*rest, index) as u32,
                        field_count: crate::pattern::ArrayPatternRest::length(*rest, elements.len()).ok_or_else(|| ControlError::Invalid("invalid array remainder".into()))? as u32, ty: element.clone(),
                    }, block, scope, names, types, source, span)?;
                }
            }
            CorePattern::Any | CorePattern::Literal(_) => {},
            CorePattern::Error => return Err(ControlError::Invalid("error pattern".into())),
        }
        Ok(())
    }
    pub(super) fn compose_capability(&mut self, instruction: &EvaluationInstruction, destination: ControlValue,
        operands: &[ControlValue], block: &mut ControlBlockId, scope: ControlScopeId,
        names: &BTreeMap<String, ControlValue>) -> Result<bool, ControlError> {
        use ControlCapabilityOperation as Op;
        let operation = match &instruction.operation {
            EvalOp::Function { definition, arguments, host_import: Some(import) } => Op::HostFunction {
                definition: *definition, arguments: arguments.clone(), import: import.clone(),
            },
            EvalOp::TraitMethod { evidence, method, trait_arguments, method_arguments, deferred } => Op::TraitMethod {
                evidence: *evidence, method: *method, trait_arguments: trait_arguments.clone(), method_arguments: method_arguments.clone(), deferred: deferred.clone(),
            },
            EvalOp::Constant { definition, arguments } => Op::Constant { definition: *definition, arguments: arguments.clone() },
            EvalOp::Record(definition) => Op::Record { definition: *definition, fields: operands.to_vec() },
            EvalOp::Enum { definition, variant } => Op::Enum { definition: *definition, variant: *variant, fields: operands.to_vec() },
            EvalOp::Field { index, field_count } => Op::Project { base: operands[0], index: *index, field_count: *field_count },
            EvalOp::PatternTest { pattern, .. } => Op::Test { subject: operands[0], pattern: pattern.clone() },
            EvalOp::Assign => {
                let EvaluationOperand::Place(place) = &instruction.operands[1] else { return Err(ControlError::Invalid("assignment lacks place".into())); };
                Op::Assign { value: operands[0], place: self.place(place, names)? }
            },
            EvalOp::Deref => Op::ReadReference(operands[0]),
            EvalOp::Borrow { unique } => {
                let EvaluationOperand::Place(place) = &instruction.operands[0] else { return Err(ControlError::Invalid("borrow lacks place".into())); };
                let lowered = self.place(place, names)?;
                let mut base = place;
                while let EvaluationPlace::Field { base: parent, .. } = base { base = parent; }
                if let EvaluationPlace::Temporary { source, .. } = base {
                    self.result.source_bindings.insert(crate::placeflow::PlaceBindingOrigin::Temporary {
                        expression: *source,
                    }, lowered.root());
                }
                Op::Borrow { place: lowered, unique: *unique }
            }
            EvalOp::Move => Op::Move(match &instruction.operands[0] {
                EvaluationOperand::Place(place) => self.place(place, names)?,
                EvaluationOperand::Value(_) => ControlPlace::Temporary(operands[0]),
            }),
            EvalOp::LabelValue(brand) => {
                let value = *self.active_label_values.get(brand)
                    .ok_or_else(|| ControlError::Invalid("label capability outside delimiter".into()))?;
                self.emit(*block, scope, destination, ControlOperation::Read(value));
                return Ok(true);
            }
            EvalOp::Resumption { name, .. } => {
                let value = *names.get(name).or_else(|| self.active_resumptions.get(name))
                    .ok_or_else(|| ControlError::Invalid(format!("resumption {name} outside clause")))?;
                self.emit(*block, scope, destination, ControlOperation::Read(value));
                return Ok(true);
            }
            EvalOp::Label { brand, body } => {
                let target = self.block(vec![destination])?;
                let label = ControlLabelId(self.result.labels.len() as u32);
                self.result.labels.push(ControlLabel { brand: *brand, scope, target, result: destination, handler_prefix: self.active_handler_clauses.clone() });
                let previous = self.active_labels.insert(*brand, label);
                // Capture the lexical destination at delimiter entry, before
                // any nested handlers are installed. Each use observes that
                // same capability; minting at its use site would capture a
                // clause's handler depth and give one brand multiple scopes.
                let capability_type = self.evaluation.regions().iter()
                    .flat_map(|region| &region.instructions)
                    .find(|instruction| matches!(instruction.operation, EvalOp::LabelValue(candidate) if candidate == *brand))
                    .map(|instruction| instruction.ty.clone());
                let previous_value = if let Some(ty) = capability_type {
                    let value = self.value(ty, instruction.source, instruction.span)?;
                    self.emit(*block, scope, value, ControlOperation::Capability(Op::Label(label)));
                    self.active_label_values.insert(*brand, value)
                } else { None };
                let (exit, value) = self.region(*body, *block, names, Some(scope))?;
                if let Some(previous) = previous { self.active_labels.insert(*brand, previous); }
                else { self.active_labels.remove(brand); }
                if let Some(previous) = previous_value { self.active_label_values.insert(*brand, previous); }
                else { self.active_label_values.remove(brand); }
                if let Some(exit) = exit {
                    let value = self.forward_result_type(exit, scope, value, &instruction.ty)?;
                    self.edge(exit, target, value);
                }
                *block = target;
                return Ok(true);
            }
            EvalOp::Transfer(brand) => {
                let label = *self.active_labels.get(brand).ok_or_else(|| ControlError::Invalid("leave outside label".into()))?;
                self.transfer(*block, ControlTransfer::Leave { label, edge: ControlEdge {
                    target: self.result.labels[label.0 as usize].target, arguments: operands.to_vec(),
                }});
                return Ok(true);
            }
            EvalOp::Perform { effect, operation, payload_types, terminal, contract } => {
                let continuation = if *terminal { None } else { Some(self.block(vec![destination])?) };
                self.transfer(*block, ControlTransfer::Perform { effect: effect.clone(), operation: *operation,
                    arguments: operands.to_vec(), payload_types: payload_types.clone(), result: destination, contract: contract.clone(), continuation });
                if let Some(next) = continuation { *block = next; }
                return Ok(true);
            }
            EvalOp::Completion { computation, arms, handles_operations } => {
                let completion_scope = self.arm_scope(*computation, scope)?;
                let (exit, subject) = self.region(*computation, *block, names, Some(completion_scope))?;
                let Some(mut test_block) = exit else { return Ok(true); };
                let result = self.value(instruction.ty.clone(), instruction.source, instruction.span)?;
                self.result.values[result.0 as usize].scope = Some(completion_scope);
                let join = self.block(vec![result])?;
                // Full-control operation arms produce the handler result,
                // not a normal-completion subject. Follow value identity
                // through scope forwarding, then route those clause exits
                // directly to this completion's result continuation.
                let mut origin = subject;
                loop {
                    let forwarded = self.result.blocks.iter().flat_map(|block| &block.instructions)
                        .find(|instruction| instruction.destination == origin)
                        .and_then(|instruction| match instruction.operation {
                            ControlOperation::Forward(value) | ControlOperation::EndScope { value, .. } => Some(value), _ => None,
                        });
                    match forwarded { Some(value) => origin = value, None => break }
                }
                let completion_handler = if *handles_operations {
                    let handler_index = self.result.handlers.iter().position(|handler| handler.result == origin)
                        .ok_or_else(|| ControlError::Invalid("completion lost its associated operation handler".into()))?;
                    self.result.handlers[handler_index].target = join;
                    self.result.handlers[handler_index].result = result;
                    // Tail-only and cancellation-only delimiters have no
                    // returning continuation whose ABI includes completion.
                    // Keep their existing early delimiter exit, including
                    // completion arms which leave rather than return.
                    let returns_to_clause = self.result.handlers[handler_index].clauses.iter()
                        .any(|clause| matches!(clause.resumption, CoreHandlerResumption::Explicit { .. }));
                    for block in &mut self.result.blocks {
                        if let ControlTerminator::Transfer(ControlTransfer::FinishClause { handler, edge, .. }) = &mut block.terminator
                            && handler.0 as usize == handler_index { edge.target = join; }
                        if returns_to_clause && let ControlTerminator::Transfer(ControlTransfer::CompleteHandler { handler, edge, .. }) = &block.terminator
                            && handler.0 as usize == handler_index {
                            // The protected result still needs its source completion
                            // transformation before it can return to a resumption.
                            block.terminator = ControlTerminator::Goto(edge.clone());
                        }
                    }
                    returns_to_clause.then_some(ControlHandlerId(handler_index as u32))
                } else { None };
                for (clause_index, arm) in arms.iter().enumerate() {
                    let arm_scope = self.arm_scope(arm.region, completion_scope)?;
                    let selected = self.block(vec![])?;
                    let rejected = self.block(vec![])?;
                    let condition = self.value(Type::Scalar(ScalarType::Bool), instruction.source, arm.span)?;
                    self.emit(test_block, completion_scope, condition, ControlOperation::Capability(Op::Test { subject, pattern: arm.pattern.clone() }));
                    self.result.blocks[test_block.0 as usize].terminator = ControlTerminator::SwitchBool {
                        condition, on_true: ControlEdge { target: selected, arguments: vec![] },
                        on_false: ControlEdge { target: rejected, arguments: vec![] },
                    };
                    let mut bindings = names.clone();
                    self.bind_pattern(&arm.pattern, subject, selected, arm_scope, &mut bindings, &arm.bindings, instruction.source, arm.span)?;
                    if let Some(refinement) = &arm.refinement {
                        let value = *self.proven_subjects.get(&refinement.subject).ok_or_else(|| ControlError::Invalid("refinement lost once-evaluated subject".into()))?;
                        self.bind_pattern(&refinement.pattern, value, selected, arm_scope, &mut bindings, &arm.bindings, instruction.source, arm.span)?;
                    }
                    for (binder, (name, _)) in arm.bindings.iter().enumerate() {
                        let value = *bindings.get(name).ok_or_else(|| ControlError::Invalid("missing completion binding".into()))?;
                        self.result.source_bindings.insert(crate::placeflow::PlaceBindingOrigin::CompletionBinder {
                            completion: instruction.source, clause: clause_index as u32, binder: binder as u32,
                        }, value);
                    }
                    let (exit, result) = self.region(arm.region, selected, &bindings, Some(arm_scope))?;
                    if let Some(exit) = exit {
                        let result = self.finish_arm_scope(arm_scope, exit, result, instruction.source, arm.span)?;
                        let result = self.forward_result_type(exit, completion_scope, result, &instruction.ty)?;
                        if let Some(handler) = completion_handler {
                            self.transfer(exit, ControlTransfer::CompleteHandler {
                                handler, value: result,
                                edge: ControlEdge { target: join, arguments: vec![result] },
                            });
                        } else {
                            self.edge(exit, join, result);
                        }
                    }
                    test_block = rejected;
                }
                self.emit(join, completion_scope, destination, ControlOperation::EndScope {
                    scope: completion_scope, value: result, transferred: None,
                });
                *block = join;
                return Ok(true);
            }
            EvalOp::Handle { computation, arms } => {
                let handler = ControlHandlerId(self.result.handlers.len() as u32);
                let target = self.block(vec![destination])?;
                self.result.handlers.push(ControlHandler { scope, target, result: destination, clauses: vec![] });
                let computation_entry = self.block(vec![])?;
                let mut clause_edges = vec![];
                // Reserve every entry before composing bodies, so nested
                // handlers cannot change this delimiter's clause identity.
                for arm in arms {
                    let payloads = arm.payload_types.iter().map(|ty| self.value(ty.clone(), instruction.source, arm.span)).collect::<Result<Vec<_>, _>>()?;
                    let entry = self.block(payloads.clone())?;
                    clause_edges.push(ControlEdge { target: entry, arguments: payloads.clone() });
                    self.result.handlers[handler.0 as usize].clauses.push(ControlHandlerClause {
                        effect: arm.effect.clone(), operation: arm.operation, patterns: arm.patterns.clone(), payloads,
                        resumption: arm.resumption.clone(), contract: arm.continuation.clone(), entry, accepted: entry, token: None,
                    });
                }
                self.transfer(*block, ControlTransfer::EnterHandler { handler,
                    computation: ControlEdge { target: computation_entry, arguments: vec![] }, clauses: clause_edges });
                let outer_handlers = self.active_handler_clauses.clone();
                self.active_handler_clauses.extend((0..arms.len() as u32).rev().map(|clause| (handler, clause)));
                let (exit, value) = self.region(*computation, computation_entry, names, Some(scope))?;
                self.active_handler_clauses = outer_handlers.clone();
                if let Some(exit) = exit { self.transfer(exit, ControlTransfer::CompleteHandler {
                    handler, value, edge: ControlEdge { target, arguments: vec![value] },
                }); }
                for (index, arm) in arms.iter().enumerate() {
                    self.active_handler_clauses = outer_handlers.clone();
                    self.active_handler_clauses.extend((index as u32..arms.len() as u32).rev().map(|clause| (handler, clause)));
                    let arm_scope = self.arm_scope(arm.region, scope)?;
                    let clause = self.result.handlers[handler.0 as usize].clauses[index].clone();
                    for payload in &clause.payloads { self.result.values[payload.0 as usize].scope = Some(arm_scope); }
                    let mut bindings = names.clone();
                    let mut selected = clause.entry;
                    for (pattern, payload) in arm.patterns.iter().zip(&clause.payloads) {
                        if !pattern_is_irrefutable(pattern) {
                            let condition = self.value(Type::Scalar(ScalarType::Bool), instruction.source, arm.span)?;
                            self.emit(selected, scope, condition, ControlOperation::Capability(Op::Test { subject: *payload, pattern: pattern.clone() }));
                            let matched = self.block(vec![])?;
                            let rejected = self.block(vec![])?;
                            self.result.blocks[selected.0 as usize].terminator = ControlTerminator::SwitchBool {
                                condition, on_true: ControlEdge { target: matched, arguments: vec![] },
                                on_false: ControlEdge { target: rejected, arguments: vec![] },
                            };
                            self.transfer(rejected, ControlTransfer::Forward { handler, clause: index as u32 });
                            selected = matched;
                        }
                    }
                    // Rejection forwards the untouched payload vector. No
                    // binding may consume a field until every payload test
                    // in this clause has succeeded.
                    self.result.handlers[handler.0 as usize].clauses[index].accepted = selected;
                    for (pattern, payload) in arm.patterns.iter().zip(&clause.payloads) {
                        self.bind_pattern(pattern, *payload, selected, arm_scope, &mut bindings, &arm.bindings, instruction.source, arm.span)?;
                    }
                    for (binder, (name, _)) in arm.bindings.iter().enumerate() {
                        let value = *bindings.get(name).ok_or_else(|| ControlError::Invalid("missing handler binding".into()))?;
                        self.result.source_bindings.insert(crate::placeflow::PlaceBindingOrigin::HandlerBinder {
                            handle: instruction.source, clause: index as u32, binder: binder as u32,
                        }, value);
                    }
                    let saved_resumptions = self.active_resumptions.clone();
                    if let CoreHandlerResumption::Explicit { name, .. } = &arm.resumption {
                        let contract = arm.continuation.as_ref().ok_or_else(|| ControlError::Invalid("explicit resumption lacks contract".into()))?;
                        let token = self.value(Type::Callable { contract: Default::default(), safety: Safety::Safe, lifetime_binders: 0,
                            parameters: vec![contract.parameter.clone()], result: Box::new(contract.result.clone()),
                            effects: contract.effects.clone(), invocation: contract.invocation }, instruction.source, arm.span)?;
                        self.emit(selected, arm_scope, token, ControlOperation::Capability(Op::Resumption { handler, clause: index as u32 }));
                        self.result.handlers[handler.0 as usize].clauses[index].token = Some(token);
                        self.active_resumptions.insert(name.clone(), token);
                        bindings.insert(name.clone(), token);
                        self.result.source_bindings.insert(crate::placeflow::PlaceBindingOrigin::HandlerResumption {
                            handle: instruction.source, clause: index as u32,
                        }, token);
                    }
                    let (exit, value) = self.region(arm.region, selected, &bindings, Some(arm_scope))?;
                    self.active_handler_clauses = outer_handlers.clone();
                    self.active_resumptions = saved_resumptions;
                    if let Some(exit) = exit {
                        let value = self.finish_arm_scope(arm_scope, exit, value, instruction.source, arm.span)?;
                        self.transfer(exit, match arm.resumption {
                            CoreHandlerResumption::Tail { .. } => ControlTransfer::TailResume { handler, clause: index as u32, value },
                            _ => ControlTransfer::FinishClause { handler, clause: index as u32, value, edge: ControlEdge { target, arguments: vec![value] } },
                        });
                    }
                }
                *block = target;
                return Ok(true);
            }
            EvalOp::Closure { environment, parameters, body, .. } => {
                let Type::Callable { safety, .. } = &instruction.ty else {
                    return Err(ControlError::Invalid("closure lacks its frozen callable safety contract".into()));
                };
                let mut captures = vec![];
                let mut child_names = BTreeMap::new();
                let mut child = Builder { evaluation: self.evaluation, result: ControlMir {
                    definition: crate::mir::lifted_callable_definition(environment.brand),
                    safety: *safety, unsafe_execution: self.result.unsafe_execution,
                    parameters: vec![], values: vec![], scopes: vec![], entry: ControlBlockId(0), blocks: vec![],
                    labels: vec![], handlers: vec![], closures: vec![],
                    source_bindings: BTreeMap::new(),
                }, mapped: BTreeMap::new(), active_labels: BTreeMap::new(), active_label_values: BTreeMap::new(), active_resumptions: BTreeMap::new(), active_handler_clauses: vec![], proven_subjects: BTreeMap::new() };
                for capture in &environment.captures {
                    captures.push(*names.get(&capture.name).ok_or_else(|| ControlError::Invalid(format!("missing capture {}", capture.name)))?);
                    let value = child.value(capture.ty.clone(), instruction.source, instruction.span)?;
                    child.result.parameters.push(value);
                    child.result.source_bindings.insert(crate::placeflow::PlaceBindingOrigin::Parameter {
                        index: child.result.parameters.len() as u32 - 1,
                    }, value);
                    child_names.insert(capture.name.clone(), value);
                }
                for (name, ty) in parameters {
                    let value = child.value(ty.clone(), instruction.source, instruction.span)?;
                    child.result.parameters.push(value);
                    child.result.source_bindings.insert(crate::placeflow::PlaceBindingOrigin::Parameter {
                        index: child.result.parameters.len() as u32 - 1,
                    }, value);
                    child_names.insert(name.clone(), value);
                }
                let entry = child.block(child.result.parameters.clone())?;
                let (exit, result) = child.region(*body, entry, &child_names, None)?;
                if let Some(exit) = exit { child.result.blocks[exit.0 as usize].terminator = ControlTerminator::Return(result); }
                child.result.validate()?;
                let closure = ControlClosureId(self.result.closures.len() as u32);
                self.result.closures.push(ControlClosure { environment: environment.clone(), body: Box::new(child.result) });
                Op::Closure { closure, captures }
            }
            _ => return Ok(false),
        };
        self.emit(*block, scope, destination, ControlOperation::Capability(operation));
        Ok(true)
    }
}
