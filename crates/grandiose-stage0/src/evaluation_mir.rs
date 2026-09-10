//! Evaluation MIR: ordered operations and deferred regions, before CFG and
//! ownership elaboration. Core IDs below are provenance/proof references only;
//! executable dependencies use this language's value, place and region IDs.
//!
//! Production lowering composes these regions into Control MIR, then elaborates
//! Ownership MIR before entering the existing concrete specialization/ABI path.

use std::collections::{BTreeMap, BTreeSet};

#[cfg(test)]
mod const_value_tests {
    use super::*;
    use crate::{ConstKind, CoreExpr, Digest, FileKey, PlaceFlow, ScalarType};

    #[test]
    fn const_values_are_kind_checked_at_each_mutable_ir_boundary() {
        let body = TypedBody {
            safety: crate::Safety::Safe, unsafe_scopes: Default::default(),
            unsafe_implementations: Default::default(), body_regions: Default::default(), parameters: vec![],
            expressions: vec![CoreExpr {
                kind: CoreKind::ConstValue(GenericArgument::ConstInteger(42u32.into())),
                ty: Type::Scalar(ScalarType::U32),
                span: Span { file: FileKey(Digest::of_bytes(b"const-value-boundary")), start: 0, end: 1 },
            }], root: CoreId(0), diagnostics: vec![], recovered: false,
        };
        let evaluation = EvaluationMir::lower(DefKey(Digest::of_bytes(b"const-value-owner")), &body).unwrap();
        let mut forged = evaluation.clone();
        forged.regions.iter_mut().flat_map(|region| &mut region.instructions)
            .find(|instruction| matches!(instruction.operation, EvaluationOperation::ConstValue(_)))
            .unwrap().ty = Type::Scalar(ScalarType::Usize);
        assert!(forged.validate().is_err());

        let control = crate::control_mir::ControlMir::lower(&evaluation).unwrap();
        let mut forged = control.clone();
        let instruction = forged.blocks.iter_mut().flat_map(|block| &mut block.instructions)
            .find(|instruction| matches!(instruction.operation, crate::control_mir::ControlOperation::ConstValue(_))).unwrap();
        instruction.operation = crate::control_mir::ControlOperation::ConstValue(
            GenericArgument::ConstGeneric { index: 0, kind: ConstKind::Usize });
        assert!(forged.validate().is_err());

        let ownership = crate::ownership_mir::OwnershipMir::lower(control, &PlaceFlow::analyze(&body), None).unwrap();
        let mut forged = ownership.clone();
        let instruction = forged.blocks.iter_mut().flat_map(|block| &mut block.instructions)
            .find(|instruction| matches!(instruction.operation, crate::ownership_mir::OwnershipOperation::Compute(
                crate::ownership_mir::OwnershipComputation::ConstValue(_)))).unwrap();
        instruction.operation = crate::ownership_mir::OwnershipOperation::Compute(
            crate::ownership_mir::OwnershipComputation::ConstValue(GenericArgument::ConstGeneric { index: 0, kind: ConstKind::Usize }));
        assert!(forged.validate().is_err());
    }
}

use crate::core::{
    CallReferenceOrigin, CallReferenceShape, CallableBrand, CallableId, CaptureEnvironment,
    CoreHandlerContinuationContract, CoreHandlerResumption, CoreId, CoreKind, CorePattern,
    CorePlace, CoreRefinementBranch, DeferredTraitMethod, LabelBrand, RefinementEnvironment,
    ResumptionId,
};
use crate::signature::HostImport;
use crate::{DefKey, EffectInstance, GenericArgument, Safety, Span, Type, TypedBody};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct EvaluationValue(pub u32);
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct EvaluationRegionId(pub u32);

/// A place is not a loaded owner. Evaluating a dereference's reference is
/// explicit, but projecting or borrowing the place does not consume its root.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EvaluationPlace {
    Resumption {
        id: ResumptionId,
        name: String,
        ty: Type,
    },
    Local {
        name: String,
        ty: Type,
    },
    Temporary {
        source: CoreId,
        value: EvaluationValue,
        ty: Type,
    },
    Field {
        base: Box<Self>,
        index: u32,
        field_count: u32,
        ty: Type,
    },
    Deref {
        reference: EvaluationValue,
        ty: Type,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EvaluationOperand {
    Value(EvaluationValue),
    Place(EvaluationPlace),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EvaluationCallContract {
    pub mandatory_tail: bool,
    /// The receiver was evaluated as an invocation-only view before arguments.
    pub prepared_receiver: bool,
    pub reference_contract: CallReferenceOrigin,
    pub reference_origin: CallReferenceOrigin,
    pub reference_shape: CallReferenceShape,
}

/// Metadata is a frozen semantic contract, not an executable Core subtree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EvaluationHandlerArm {
    pub brand: CallableBrand,
    pub effect: EffectInstance,
    pub operation: u32,
    pub payload_types: Vec<Type>,
    pub patterns: Vec<CorePattern>,
    pub bindings: Vec<(String, Type)>,
    pub resumption: CoreHandlerResumption,
    pub continuation: Option<CoreHandlerContinuationContract>,
    pub terminal: bool,
    pub span: Span,
    pub region: EvaluationRegionId,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EvaluationCompletionArm {
    pub pattern: CorePattern,
    pub bindings: Vec<(String, Type)>,
    /// Source identity here is proof provenance for the once-evaluated test,
    /// never an instruction to evaluate the subject again in this arm.
    pub refinement: Option<CoreRefinementBranch>,
    pub span: Span,
    pub region: EvaluationRegionId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EvaluationOperation {
    /// Evaluate the callable resident without source Copy or ownership transfer.
    /// Only the associated invocation may consume this temporary view.
    PrepareInvocation,
    Literal(String),
    ConstValue(GenericArgument),
    ReadLocal(String),
    Resumption {
        id: ResumptionId,
        name: String,
    },
    Function {
        definition: DefKey,
        arguments: Vec<GenericArgument>,
        host_import: Option<HostImport>,
    },
    TraitMethod {
        evidence: DefKey,
        method: DefKey,
        trait_arguments: Vec<GenericArgument>,
        method_arguments: Vec<GenericArgument>,
        deferred: Option<DeferredTraitMethod>,
    },
    Constant {
        definition: DefKey,
        arguments: Vec<GenericArgument>,
    },
    Tuple,
    Array,
    Record(DefKey),
    Enum {
        definition: DefKey,
        variant: u32,
    },
    Field {
        index: u32,
        field_count: u32,
    },
    PatternTest {
        pattern: CorePattern,
        refinement: RefinementEnvironment,
    },
    Bind(String),
    /// Dispose of a statement result at this point, before evaluating the
    /// next statement. Ownership MIR selects the actual destruction action.
    Discard,
    /// Checked abandonment of a pending environment. This consumes the
    /// witness through ownership disposal; it is never a unit constant.
    ReleaseAvailable,
    Assign,
    Borrow {
        unique: bool,
    },
    Deref,
    Move,
    Call(EvaluationCallContract),
    Perform {
        effect: EffectInstance,
        operation: u32,
        payload_types: Vec<Type>,
        terminal: bool,
        contract: EvaluationCallContract,
    },
    Intrinsic(String),
    /// Only the left operand is strict; the right is evaluated conditionally.
    LazyBoolean {
        conjunction: bool,
        right: EvaluationRegionId,
    },
    Scope(EvaluationRegionId),
    Label {
        brand: LabelBrand,
        body: EvaluationRegionId,
    },
    LabelValue(LabelBrand),
    Transfer(LabelBrand),
    Closure {
        callable: CallableId,
        parameters: Vec<(String, Type)>,
        environment: CaptureEnvironment,
        body: EvaluationRegionId,
    },
    Handle {
        computation: EvaluationRegionId,
        arms: Vec<EvaluationHandlerArm>,
    },
    Completion {
        computation: EvaluationRegionId,
        arms: Vec<EvaluationCompletionArm>,
        handles_operations: bool,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EvaluationInstruction {
    pub value: EvaluationValue,
    pub source: CoreId,
    pub span: Span,
    pub ty: Type,
    pub operation: EvaluationOperation,
    /// In execution order; places contribute only their reference evaluation.
    pub operands: Vec<EvaluationOperand>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EvaluationExit {
    Yield(EvaluationValue),
    /// No later instruction or enclosing strict operation can execute.
    Diverge(EvaluationValue),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EvaluationRegion {
    pub source: CoreId,
    pub unsafe_scope: bool,
    pub instructions: Vec<EvaluationInstruction>,
    pub exit: EvaluationExit,
}

/// Frozen phase product. Mutable builder state cannot be published as a body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EvaluationMir {
    definition: DefKey,
    safety: Safety,
    parameters: Vec<(String, Type)>,
    unsafe_implementations: BTreeSet<DefKey>,
    entry: EvaluationRegionId,
    regions: Vec<EvaluationRegion>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EvaluationError(pub String);

impl EvaluationMir {
    pub fn lower(definition: DefKey, body: &TypedBody) -> Result<Self, EvaluationError> {
        Self::lower_checked(definition, body, None)
    }

    pub(crate) fn lower_with_continuations(
        definition: DefKey, body: &TypedBody,
        facts: &crate::core_continuations::CoreContinuations,
    ) -> Result<Self, EvaluationError> {
        facts.bind(body).map_err(|error| EvaluationError(error.message))?;
        Self::lower_checked(definition, body, Some(facts))
    }

    fn lower_checked(definition: DefKey, body: &TypedBody,
        facts: Option<&crate::core_continuations::CoreContinuations>,
    ) -> Result<Self, EvaluationError> {
        if body.recovered || !body.diagnostics.is_empty() {
            return Err(EvaluationError(
                "cannot normalize recovered or diagnosed Core".into(),
            ));
        }
        if let Some(error) = body.validate().first() {
            return Err(EvaluationError(format!("invalid Core: {}", error.message)));
        }
        let mut builder = Builder {
            body,
            facts,
            regions: vec![],
            next_value: 0,
            active: BTreeSet::new(),
        };
        let entry = builder.region(body.root)?;
        let result = Self {
            definition,
            safety: body.safety,
            parameters: body.parameters.clone(),
            unsafe_implementations: body.unsafe_implementations.clone(),
            entry,
            regions: builder.regions,
        };
        result.validate()?;
        Ok(result)
    }

    pub fn definition(&self) -> DefKey {
        self.definition
    }
    pub fn safety(&self) -> Safety {
        self.safety
    }
    pub fn parameters(&self) -> &[(String, Type)] {
        &self.parameters
    }
    pub fn unsafe_implementations(&self) -> &BTreeSet<DefKey> {
        &self.unsafe_implementations
    }
    pub fn entry(&self) -> EvaluationRegionId {
        self.entry
    }
    pub fn regions(&self) -> &[EvaluationRegion] {
        &self.regions
    }

    /// Independently reject scheduling errors, multiply owned regions, escaped
    /// temporaries and unreachable suffixes. Type/quantity/control validators
    /// in subsequent languages additionally check their respective contracts.
    pub fn validate(&self) -> Result<(), EvaluationError> {
        type Resumptions = std::collections::BTreeMap<String, (ResumptionId, Type)>;
        let mut pending = vec![(self.entry, Resumptions::new())];
        let mut regions = BTreeSet::new();
        let mut values = BTreeSet::new();
        let mut resumption_binders = std::collections::BTreeMap::new();
        while let Some((id, mut resumptions)) = pending.pop() {
            let region = self
                .regions
                .get(id.0 as usize)
                .ok_or_else(|| EvaluationError("invalid region reference".into()))?;
            if !regions.insert(id) {
                return Err(EvaluationError(
                    "region has multiple owners or a cycle".into(),
                ));
            }
            let mut available = BTreeSet::new();
            for (index, instruction) in region.instructions.iter().enumerate() {
                instruction.validate_shape()?;
                if instruction.operation == EvaluationOperation::ReleaseAvailable {
                    let [EvaluationOperand::Value(operand)] = instruction.operands.as_slice()
                        else { unreachable!("validated release arity"); };
                    let witness = region.instructions[..index].iter().find(|value| value.value == *operand);
                    if !witness.is_some_and(|value| matches!(&value.ty,
                        Type::Nominal { definition, arguments }
                        if *definition == crate::intrinsic_available_type_definition()
                            && matches!(arguments.as_slice(), [GenericArgument::Lifetime(_), GenericArgument::Type(_)]))) {
                        return Err(EvaluationError("release operand is not an availability witness".into()));
                    }
                }
                if let EvaluationOperation::Completion { computation, handles_operations: true, .. } = &instruction.operation
                    && !self.regions.get(computation.0 as usize).is_some_and(|region| {
                        let result = match region.exit { EvaluationExit::Yield(value) | EvaluationExit::Diverge(value) => value };
                        region.instructions.iter().any(|instruction|
                            instruction.value == result && matches!(instruction.operation, EvaluationOperation::Handle { .. }))
                    })
                {
                    return Err(EvaluationError("completion is not attached to its direct operation handler".into()));
                }
                for operand in &instruction.operands {
                    if let EvaluationOperand::Place(place) = operand {
                        let mut root = place;
                        while let EvaluationPlace::Field { base, .. } = root { root = base; }
                        if let EvaluationPlace::Resumption { id, name, ty } = root
                            && resumptions.get(name) != Some(&(*id, ty.clone())) {
                            return Err(EvaluationError("resumption place differs from its active lexical binder and contract".into()));
                        }
                    }
                    let mut dependencies = vec![];
                    operand.dependencies(&mut dependencies);
                    if dependencies.iter().any(|value| !available.contains(value)) {
                        return Err(EvaluationError(
                            "operand is not an earlier value in its region".into(),
                        ));
                    }
                }
                if !values.insert(instruction.value) {
                    return Err(EvaluationError("value has multiple definitions".into()));
                }
                available.insert(instruction.value);
                match &instruction.operation {
                    EvaluationOperation::Resumption { id, name } => {
                        if resumptions.get(name) != Some(&(*id, instruction.ty.clone())) {
                            return Err(EvaluationError("resumption differs from its active lexical binder and contract".into()));
                        }
                    }
                    EvaluationOperation::Bind(name) => { resumptions.remove(name); }
                    EvaluationOperation::Closure { body, .. } => pending.push((*body, Resumptions::new())),
                    EvaluationOperation::Handle { computation, arms } => {
                        pending.push((*computation, resumptions.clone()));
                        for (index, arm) in arms.iter().enumerate() {
                            let crate::CallableBrand::HandlerClause { owner, handler, clause } = arm.brand else {
                                return Err(EvaluationError("handler arm has no lexical clause identity".into()));
                            };
                            if handler != instruction.source || clause != index as u32
                                || arm.continuation.as_ref().is_some_and(|contract|
                                    contract.brand != crate::CallableBrand::Continuation { owner, handler, clause }) {
                                return Err(EvaluationError("handler arm or continuation names a different delimiter".into()));
                            }
                            let mut child = resumptions.clone();
                            for (name, _) in &arm.bindings { child.remove(name); }
                            if let CoreHandlerResumption::Explicit { id, name, .. } = &arm.resumption {
                                let contract = arm.continuation.as_ref().ok_or_else(||
                                    EvaluationError("resumption binder has no continuation contract".into()))?;
                                if resumption_binders.insert(*id, arm.brand).is_some_and(|brand| brand != arm.brand) {
                                    return Err(EvaluationError("distinct handler binders share a resumption identity".into()));
                                }
                                child.insert(name.clone(), (*id, contract.callable_type()));
                            }
                            pending.push((arm.region, child));
                        }
                    }
                    EvaluationOperation::Completion { computation, arms, .. } => {
                        pending.push((*computation, resumptions.clone()));
                        for arm in arms {
                            let mut child = resumptions.clone();
                            for (name, _) in &arm.bindings { child.remove(name); }
                            pending.push((arm.region, child));
                        }
                    }
                    operation => {
                        let mut children = vec![];
                        operation.regions(&mut children);
                        pending.extend(children.into_iter().map(|child| (child, resumptions.clone())));
                    }
                }
                if instruction.is_terminal() && index + 1 != region.instructions.len() {
                    return Err(EvaluationError(
                        "instruction after terminal evaluation".into(),
                    ));
                }
            }
            let Some(last) = region.instructions.last() else {
                return Err(EvaluationError("region has no result".into()));
            };
            let (value, diverges) = match region.exit {
                EvaluationExit::Yield(value) => (value, false),
                EvaluationExit::Diverge(value) => (value, true),
            };
            if !available.contains(&value)
                || diverges != last.is_terminal()
                || (diverges && value != last.value)
            {
                return Err(EvaluationError(
                    "region exit disagrees with its evaluation sequence".into(),
                ));
            }
        }
        if regions.len() != self.regions.len() {
            return Err(EvaluationError("orphan evaluation region".into()));
        }
        Ok(())
    }
}

impl EvaluationOperand {
    fn dependencies(&self, result: &mut Vec<EvaluationValue>) {
        match self {
            Self::Value(value) => result.push(*value),
            Self::Place(place) => place.dependencies(result),
        }
    }
}
impl EvaluationPlace {
    fn dependencies(&self, result: &mut Vec<EvaluationValue>) {
        match self {
            Self::Local { .. } | Self::Resumption { .. } => {}
            Self::Temporary { value, .. } => result.push(*value),
            Self::Field { base, .. } => base.dependencies(result),
            Self::Deref { reference, .. } => result.push(*reference),
        }
    }
}
impl EvaluationInstruction {
    fn is_terminal(&self) -> bool {
        self.ty == Type::Never || matches!(&self.operation,
            EvaluationOperation::Call(contract) if contract.mandatory_tail)
    }
    fn validate_shape(&self) -> Result<(), EvaluationError> {
        use EvaluationOperation as Op;
        let values = self
            .operands
            .iter()
            .all(|operand| matches!(operand, EvaluationOperand::Value(_)));
        let arity = self.operands.len();
        let valid = match &self.operation {
            Op::ConstValue(argument) => arity == 0
                && crate::types::integer_const_argument_type(argument).as_ref() == Some(&self.ty)
                && crate::types::is_canonical_generic_argument_identity(argument),
            Op::Literal(_)
            | Op::ReadLocal(_)
            | Op::Resumption { .. }
            | Op::Function { .. }
            | Op::TraitMethod { .. }
            | Op::Constant { .. }
            | Op::Scope(_)
            | Op::Label { .. }
            | Op::LabelValue(_)
            | Op::Closure { .. }
            | Op::Handle { .. }
            | Op::Completion { .. } => arity == 0,
            Op::Tuple | Op::Array | Op::Record(_) | Op::Enum { .. } | Op::Intrinsic(_) => values,
            Op::Field { index, field_count } => values && arity == 1 && index < field_count,
            Op::PatternTest { .. }
            | Op::Bind(_)
            | Op::Discard
            | Op::Deref
            | Op::LazyBoolean { .. } => values && arity == 1,
            Op::ReleaseAvailable => values && arity == 1 && self.ty == Type::Unit,
            Op::Transfer(_) => values && arity == 1 && self.ty == Type::Never,
            Op::Move => arity == 1,
            Op::Borrow { .. } | Op::PrepareInvocation => matches!(&self.operands[..], [EvaluationOperand::Place(_)]),
            Op::Assign => matches!(
                &self.operands[..],
                [EvaluationOperand::Value(_), EvaluationOperand::Place(_)]
            ),
            Op::Call(_) => values && arity >= 1,
            Op::Perform {
                payload_types,
                terminal,
                ..
            } => values && arity == payload_types.len() && (!terminal || self.ty == Type::Never),
        };
        if valid {
            Ok(())
        } else {
            Err(EvaluationError(
                "operation has invalid operands or terminal contract".into(),
            ))
        }
    }
}
impl EvaluationOperation {
    fn regions(&self, result: &mut Vec<EvaluationRegionId>) {
        match self {
            Self::Scope(body) | Self::Label { body, .. } | Self::Closure { body, .. } => {
                result.push(*body)
            }
            Self::LazyBoolean { right, .. } => result.push(*right),
            Self::Handle { computation, arms } => {
                result.push(*computation);
                result.extend(arms.iter().map(|arm| arm.region));
            }
            Self::Completion { computation, arms, .. } => {
                result.push(*computation);
                result.extend(arms.iter().map(|arm| arm.region));
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Digest, FileKey};

    fn fixture() -> EvaluationMir {
        let identity = Digest::of_bytes(b"evaluation-validation");
        EvaluationMir {
            definition: DefKey(identity),
            safety: Safety::Safe,
            parameters: vec![],
            unsafe_implementations: BTreeSet::new(),
            entry: EvaluationRegionId(0),
            regions: vec![EvaluationRegion {
                source: CoreId(0),
                unsafe_scope: false,
                instructions: vec![EvaluationInstruction {
                    value: EvaluationValue(0),
                    source: CoreId(0),
                    span: Span {
                        file: FileKey(identity),
                        start: 0,
                        end: 1,
                    },
                    ty: Type::Unit,
                    operation: EvaluationOperation::Tuple,
                    operands: vec![],
                }],
                exit: EvaluationExit::Yield(EvaluationValue(0)),
            }],
        }
    }

    #[test]
    fn handler_resumption_identity_is_checked_at_the_receiving_boundary() {
        let mut mir = fixture();
        let identity = ResumptionId(7);
        let contract = CoreHandlerContinuationContract {
            brand: crate::CallableBrand::Continuation { owner: mir.definition, handler: CoreId(0), clause: 0 },
            parameter: Type::Unit, result: Type::Unit, effects: crate::EffectRow::empty(),
            invocation: crate::Quantity::AFFINE,
        };
        let mut computation = mir.regions[0].clone();
        computation.instructions[0].value = EvaluationValue(1);
        computation.exit = EvaluationExit::Yield(EvaluationValue(1));
        let mut arm = mir.regions[0].clone();
        let mut reference = arm.instructions[0].clone();
        reference.value = EvaluationValue(2);
        reference.ty = contract.callable_type();
        reference.operation = EvaluationOperation::Resumption { id: identity, name: "resume".into() };
        arm.instructions[0].value = EvaluationValue(3);
        arm.instructions.insert(0, reference);
        arm.exit = EvaluationExit::Yield(EvaluationValue(3));
        mir.regions[0].instructions[0].operation = EvaluationOperation::Handle {
            computation: EvaluationRegionId(1), arms: vec![EvaluationHandlerArm {
                brand: crate::CallableBrand::HandlerClause { owner: mir.definition, handler: CoreId(0), clause: 0 },
                effect: EffectInstance { definition: mir.definition, arguments: vec![] }, operation: 0,
                payload_types: vec![], patterns: vec![], bindings: vec![],
                resumption: CoreHandlerResumption::Explicit { id: identity, name: "resume".into(), quantity: crate::Quantity::AFFINE },
                continuation: Some(contract), terminal: false,
                span: mir.regions[0].instructions[0].span, region: EvaluationRegionId(2),
            }],
        };
        mir.regions.extend([computation, arm]);
        mir.validate().unwrap();
        let mut borrowed = mir.clone();
        let reference = &mut borrowed.regions[2].instructions[0];
        let ty = reference.ty.clone();
        reference.operation = EvaluationOperation::Borrow { unique: false };
        reference.ty = Type::Reference { mutability: crate::Mutability::Shared,
            lifetime: crate::Lifetime::Elided, referent: Box::new(ty.clone()) };
        reference.operands = vec![EvaluationOperand::Place(EvaluationPlace::Resumption {
            id: identity, name: "resume".into(), ty,
        })];
        borrowed.validate().unwrap();
        for mutation in 0..3 {
            let mut forged = borrowed.clone();
            let EvaluationOperand::Place(EvaluationPlace::Resumption { id, name, ty }) =
                &mut forged.regions[2].instructions[0].operands[0] else { panic!() };
            match mutation {
                0 => *id = ResumptionId(8),
                1 => *name = "different".into(),
                _ => *ty = Type::Unit,
            }
            assert!(forged.validate().is_err());
            assert!(crate::control_mir::ControlMir::lower(&forged).is_err());
        }
        for mutation in 0..5 {
            let mut forged = mir.clone();
            match mutation {
                0 => {
                    let EvaluationOperation::Resumption { id, .. } = &mut forged.regions[2].instructions[0].operation else { panic!() };
                    *id = ResumptionId(8);
                }
                1 => {
                    let EvaluationOperation::Handle { arms, .. } = &mut forged.regions[0].instructions[0].operation else { panic!() };
                    let CoreHandlerResumption::Explicit { name, .. } = &mut arms[0].resumption else { panic!() };
                    *name = "different".into();
                }
                2 => {
                    let EvaluationOperation::Handle { arms, .. } = &mut forged.regions[0].instructions[0].operation else { panic!() };
                    arms[0].continuation.as_mut().unwrap().parameter = Type::Never;
                }
                3 => {
                    let EvaluationOperation::Handle { arms, .. } = &mut forged.regions[0].instructions[0].operation else { panic!() };
                    arms[0].brand = crate::CallableBrand::HandlerClause { owner: mir.definition, handler: CoreId(99), clause: 0 };
                }
                4 => {
                    let mut reference = forged.regions[2].instructions.remove(0);
                    reference.value = EvaluationValue(4);
                    forged.regions[1].instructions.insert(0, reference);
                }
                _ => unreachable!(),
            }
            assert!(forged.validate().is_err(), "forged handler mutation {mutation} was accepted");
            assert!(crate::control_mir::ControlMir::lower(&forged).is_err());
        }
    }

    #[test]
    fn validator_rejects_use_before_definition() {
        let mut mir = fixture();
        mir.regions[0].instructions[0]
            .operands
            .push(EvaluationOperand::Value(EvaluationValue(0)));
        assert!(mir.validate().unwrap_err().0.contains("earlier value"));
    }

    #[test]
    fn validator_rejects_duplicate_value_definitions() {
        let mut mir = fixture();
        let instruction = mir.regions[0].instructions[0].clone();
        mir.regions[0].instructions.push(instruction);
        assert!(
            mir.validate()
                .unwrap_err()
                .0
                .contains("multiple definitions")
        );
    }

    #[test]
    fn validator_rejects_orphan_or_cyclic_regions() {
        let mut mir = fixture();
        mir.regions.push(mir.regions[0].clone());
        assert!(mir.validate().unwrap_err().0.contains("orphan"));
        mir.regions.pop();
        mir.regions[0].instructions[0].operation =
            EvaluationOperation::Scope(EvaluationRegionId(0));
        assert!(mir.validate().unwrap_err().0.contains("cycle"));
    }

    #[test]
    fn validator_rejects_escaped_region_temporaries() {
        let mut mir = fixture();
        let mut child = mir.regions[0].clone();
        child.instructions[0].value = EvaluationValue(1);
        child.instructions[0]
            .operands
            .push(EvaluationOperand::Value(EvaluationValue(0)));
        child.exit = EvaluationExit::Yield(EvaluationValue(1));
        mir.regions.push(child);
        mir.regions[0].instructions[0].operation =
            EvaluationOperation::Scope(EvaluationRegionId(1));
        assert!(mir.validate().unwrap_err().0.contains("earlier value"));
    }

    #[test]
    fn validator_rejects_forged_exit_and_unreachable_suffix() {
        let mut mir = fixture();
        mir.regions[0].exit = EvaluationExit::Diverge(EvaluationValue(0));
        assert!(mir.validate().unwrap_err().0.contains("exit disagrees"));
        mir.regions[0].instructions[0].ty = Type::Never;
        assert!(mir.validate().is_ok());
        let mut suffix = mir.regions[0].instructions[0].clone();
        suffix.value = EvaluationValue(1);
        suffix.ty = Type::Unit;
        mir.regions[0].instructions.push(suffix);
        assert!(mir.validate().unwrap_err().0.contains("after terminal"));
    }

    #[test]
    fn validator_rejects_value_in_borrow_place_position() {
        let mut mir = fixture();
        mir.regions[0].instructions[0].operation = EvaluationOperation::Borrow { unique: false };
        mir.regions[0].instructions[0]
            .operands
            .push(EvaluationOperand::Value(EvaluationValue(0)));
        assert!(mir.validate().unwrap_err().0.contains("invalid operands"));
    }

    #[test]
    fn normalizer_rejects_cyclic_core_without_recursing_forever() {
        let mut core = TypedBody {
            safety: Safety::Safe,
            unsafe_scopes: BTreeSet::new(),
            unsafe_implementations: BTreeSet::new(),
            body_regions: Default::default(),
            parameters: vec![],
            expressions: vec![],
            root: CoreId(0),
            diagnostics: vec![],
            recovered: false,
        };
        core.expressions.push(crate::CoreExpr {
            kind: CoreKind::Block(vec![CoreId(0)]),
            ty: Type::Unit,
            span: fixture().regions[0].instructions[0].span,
        });
        assert!(EvaluationMir::lower(fixture().definition, &core).is_err());
    }
}

struct Builder<'a> {
    body: &'a TypedBody,
    facts: Option<&'a crate::core_continuations::CoreContinuations>,
    regions: Vec<EvaluationRegion>,
    next_value: u32,
    active: BTreeSet<CoreId>,
}
#[derive(Default)]
struct Sequence {
    instructions: Vec<EvaluationInstruction>,
    values: BTreeMap<CoreId, EvaluationValue>,
    terminal: Option<EvaluationValue>,
}

impl Builder<'_> {
    fn region(&mut self, source: CoreId) -> Result<EvaluationRegionId, EvaluationError> {
        self.region_with_observation(source, false)
    }

    fn borrowed_pattern_subject(&self, mut source: CoreId) -> bool {
        // Keep malformed cyclic Core bounded; the ordinary expression walk
        // subsequently reports the cycle through its active-expression set.
        for _ in 0..self.body.expressions.len() {
            match self.body.expression(source).kind {
                CoreKind::Field { base, .. } => source = base,
                CoreKind::Deref(_) => return true,
                _ => return false,
            }
        }
        false
    }

    fn region_with_observation(&mut self, source: CoreId, observational: bool) -> Result<EvaluationRegionId, EvaluationError> {
        let mut sequence = Sequence::default();
        let subject_ty = self.body.expression(source).ty.clone();
        let observation = if observational
            && crate::core::refinement_binding_type(subject_ty.clone()) != subject_ty {
            self.expression_place(source, &mut sequence)?
        } else { None };
        let value = if let Some(place) = observation {
            // An observational dispatch on an existing owner must not first
            // materialize a consuming ReadLocal/Project temporary. Dispatch
            // and binding projections operate through this ordinary borrow.
            self.emit(source, crate::core::refinement_binding_type(subject_ty),
                EvaluationOperation::Borrow { unique: false },
                vec![EvaluationOperand::Place(place)], &mut sequence)?
        } else if let CoreKind::Block(items) = &self.body.expression(source).kind {
            let items = items.clone();
            let mut value = None;
            let count = items.len();
            for (index, item) in items.into_iter().enumerate() {
                value = Some(self.expression(item, &mut sequence)?);
                if sequence.terminal.is_some() {
                    break;
                }
                if index + 1 < count {
                    let statement = value.expect("evaluated statement");
                    self.emit(
                        item,
                        Type::Unit,
                        EvaluationOperation::Discard,
                        vec![EvaluationOperand::Value(statement)],
                        &mut sequence,
                    )?;
                    // Synthetic disposal is an effect, not a new meaning for
                    // the original expression's once-evaluated value.
                    sequence.values.insert(item, statement);
                }
            }
            match value {
                Some(value) => value,
                None => self.emit(
                    source,
                    Type::Unit,
                    EvaluationOperation::Tuple,
                    vec![],
                    &mut sequence,
                )?,
            }
        } else {
            self.expression(source, &mut sequence)?
        };
        let id = EvaluationRegionId(
            u32::try_from(self.regions.len())
                .map_err(|_| EvaluationError("region arena exhausted".into()))?,
        );
        self.regions.push(EvaluationRegion {
            source,
            unsafe_scope: self.body.unsafe_scopes.contains(&source),
            instructions: sequence.instructions,
            exit: sequence
                .terminal
                .map_or(EvaluationExit::Yield(value), EvaluationExit::Diverge),
        });
        Ok(id)
    }

    fn emit(
        &mut self,
        source: CoreId,
        ty: Type,
        operation: EvaluationOperation,
        operands: Vec<EvaluationOperand>,
        sequence: &mut Sequence,
    ) -> Result<EvaluationValue, EvaluationError> {
        if let Some(value) = sequence.terminal {
            return Ok(value);
        }
        let value = EvaluationValue(self.next_value);
        self.next_value = self
            .next_value
            .checked_add(1)
            .ok_or_else(|| EvaluationError("value arena exhausted".into()))?;
        if ty == Type::Never || matches!(&operation, EvaluationOperation::Call(contract) if contract.mandatory_tail) {
            sequence.terminal = Some(value);
        }
        let caches_expression = !matches!(operation, EvaluationOperation::PrepareInvocation);
        sequence.instructions.push(EvaluationInstruction {
            value,
            source,
            span: self.body.expression(source).span,
            ty,
            operation,
            operands,
        });
        // A prepared receiver belongs to this call, not to the Core value's
        // ordinary expression cache. Shared Core operands can still be read
        // or transferred normally at another occurrence.
        if caches_expression { sequence.values.insert(source, value); }
        Ok(value)
    }

    fn values(
        &mut self,
        ids: &[CoreId],
        sequence: &mut Sequence,
    ) -> Result<Vec<EvaluationOperand>, EvaluationError> {
        let mut result = vec![];
        for id in ids {
            result.push(EvaluationOperand::Value(self.expression(*id, sequence)?));
            if sequence.terminal.is_some() {
                break;
            }
        }
        Ok(result)
    }

    fn place(
        &mut self,
        place: &CorePlace,
        sequence: &mut Sequence,
    ) -> Result<EvaluationPlace, EvaluationError> {
        Ok(match place {
            CorePlace::Local { name, ty } => EvaluationPlace::Local {
                name: name.clone(),
                ty: ty.clone(),
            },
            CorePlace::Field {
                base,
                index,
                field_count,
                ty,
            } => EvaluationPlace::Field {
                base: Box::new(self.place(base, sequence)?),
                index: *index,
                field_count: *field_count,
                ty: ty.clone(),
            },
            CorePlace::Deref { reference, ty, .. } => EvaluationPlace::Deref {
                reference: self.expression(*reference, sequence)?,
                ty: ty.clone(),
            },
            CorePlace::Error => return Err(EvaluationError("invalid assignment place".into())),
        })
    }

    fn expression_place(
        &mut self,
        id: CoreId,
        sequence: &mut Sequence,
    ) -> Result<Option<EvaluationPlace>, EvaluationError> {
        let expression = self.body.expression(id);
        Ok(match &expression.kind {
            CoreKind::Resumption { id, name } => Some(EvaluationPlace::Resumption {
                id: *id, name: name.clone(), ty: expression.ty.clone(),
            }),
            CoreKind::Local(name) => Some(EvaluationPlace::Local {
                name: name.clone(),
                ty: expression.ty.clone(),
            }),
            CoreKind::Field {
                base,
                index,
                field_count,
            } => self
                .expression_place(*base, sequence)?
                .map(|base| EvaluationPlace::Field {
                    base: Box::new(base),
                    index: *index,
                    field_count: *field_count,
                    ty: expression.ty.clone(),
                }),
            CoreKind::Deref(reference) => Some(EvaluationPlace::Deref {
                reference: self.expression(*reference, sequence)?,
                ty: expression.ty.clone(),
            }),
            _ => None,
        })
    }

    fn borrowed_place(&mut self, id: CoreId, sequence: &mut Sequence) -> Result<EvaluationPlace, EvaluationError> {
        if let CoreKind::Field { base, index, field_count } = self.body.expression(id).kind {
            // Borrow the field in its complete temporary owner. Evaluating
            // the projection as an owned value would move the field out and
            // change both the owner's destruction and the loan's lifetime.
            return Ok(EvaluationPlace::Field {
                base: Box::new(self.borrowed_place(base, sequence)?), index, field_count,
                ty: self.body.expression(id).ty.clone(),
            });
        }
        Ok(match self.expression_place(id, sequence)? {
            Some(place) => place,
            None => EvaluationPlace::Temporary {
                source: id, value: self.expression(id, sequence)?,
                ty: self.body.expression(id).ty.clone(),
            },
        })
    }

    fn expression(
        &mut self,
        source: CoreId,
        sequence: &mut Sequence,
    ) -> Result<EvaluationValue, EvaluationError> {
        if let Some(value) = sequence.terminal {
            return Ok(value);
        }
        if let Some(value) = sequence.values.get(&source) {
            return Ok(*value);
        }
        if !self.active.insert(source) {
            return Err(EvaluationError("cyclic Core evaluation graph".into()));
        }
        let result = self.expression_inner(source, sequence);
        self.active.remove(&source);
        result
    }

    fn expression_inner(
        &mut self,
        source: CoreId,
        sequence: &mut Sequence,
    ) -> Result<EvaluationValue, EvaluationError> {
        let expression = self.body.expression(source).clone();
        let mut ty = expression.ty;
        let mut operands = vec![];
        use EvaluationOperation as Op;
        let operation = match expression.kind {
            CoreKind::Literal(value) => Op::Literal(value),
            CoreKind::ConstValue(value) => Op::ConstValue(value),
            CoreKind::Local(name) => Op::ReadLocal(name),
            CoreKind::Resumption { id, name } => Op::Resumption { id, name },
            CoreKind::Function {
                definition,
                arguments,
                host_import,
            } => Op::Function {
                definition,
                arguments,
                host_import,
            },
            CoreKind::TraitMethod {
                evidence,
                method,
                trait_arguments,
                method_arguments,
                deferred,
            } => Op::TraitMethod {
                evidence,
                method,
                trait_arguments,
                method_arguments,
                deferred,
            },
            CoreKind::Constant {
                definition,
                arguments,
            } => Op::Constant {
                definition,
                arguments,
            },
            CoreKind::Tuple(items) => {
                operands = self.values(&items, sequence)?;
                Op::Tuple
            }
            CoreKind::Array(items) => {
                operands = self.values(&items, sequence)?;
                Op::Array
            }
            CoreKind::Record { definition, fields } => {
                operands = self.values(&fields, sequence)?;
                Op::Record(definition)
            }
            CoreKind::Enum {
                definition,
                variant,
                fields,
            } => {
                operands = self.values(&fields, sequence)?;
                Op::Enum {
                    definition,
                    variant,
                }
            }
            CoreKind::Field {
                base,
                index,
                field_count,
            } => {
                operands = self.values(&[base], sequence)?;
                Op::Field { index, field_count }
            }
            CoreKind::PatternTest {
                subject,
                pattern,
                refinement,
            } => {
                operands = self.values(&[subject], sequence)?;
                Op::PatternTest {
                    pattern,
                    refinement,
                }
            }
            CoreKind::Let { name, value } => {
                operands = self.values(&[value], sequence)?;
                Op::Bind(name)
            }
            CoreKind::Assign { place, value } => {
                // The language's assignment contract evaluates the RHS before
                // the target reference, matching Core/PlaceFlow and legacy MIR.
                operands = self.values(&[value], sequence)?;
                if sequence.terminal.is_none() {
                    operands.push(EvaluationOperand::Place(self.place(&place, sequence)?));
                }
                Op::Assign
            }
            CoreKind::Borrow { unique, value } => {
                let place = self.borrowed_place(value, sequence)?;
                operands.push(EvaluationOperand::Place(place));
                Op::Borrow { unique }
            }
            CoreKind::Move(value) => {
                operands.push(match self.expression_place(value, sequence)? {
                    Some(place) => EvaluationOperand::Place(place),
                    None => EvaluationOperand::Value(self.expression(value, sequence)?),
                });
                Op::Move
            }
            CoreKind::Deref(value) => {
                operands = self.values(&[value], sequence)?;
                Op::Deref
            }
            CoreKind::Call {
                callee,
                arguments,
                invocation,
                reference_contract,
                reference_origin,
                reference_shape,
                mandatory_tail,
            } => {
                if matches!(&invocation.declaration, Type::Callable { result, .. } if **result == Type::Never)
                {
                    ty = Type::Never;
                }
                let direct_label = !mandatory_tail && arguments.len() == 1
                    && self.facts.and_then(|facts| facts.invocation(source))
                        .and_then(|invocation| invocation.direct_label()).is_some();
                let prepared_receiver = !direct_label && matches!(self.body.expression(callee).kind,
                    CoreKind::Local(_) | CoreKind::Resumption { .. } | CoreKind::Field { .. } | CoreKind::Deref(_));
                operands = if prepared_receiver {
                    let place = self.borrowed_place(callee, sequence)?;
                    let value = self.emit(callee, self.body.expression(callee).ty.clone(),
                        Op::PrepareInvocation, vec![EvaluationOperand::Place(place)], sequence)?;
                    vec![EvaluationOperand::Value(value)]
                } else { self.values(&[callee], sequence)? };
                if sequence.terminal.is_none() {
                    operands.extend(self.values(&arguments, sequence)?);
                }
                if !mandatory_tail && arguments.len() == 1
                    && let Some(brand) = self.facts.and_then(|facts| facts.invocation(source))
                        .and_then(|invocation| invocation.direct_label())
                    && sequence.terminal.is_none() {
                    // Strict callee and payload evaluation has already been
                    // emitted. Only the invocation is replaced; a helper's
                    // body-derived exit is not evidence that its callee is a label.
                    operands.remove(0);
                    ty = Type::Never;
                    Op::Transfer(brand)
                } else {
                    Op::Call(EvaluationCallContract {
                        mandatory_tail,
                        prepared_receiver,
                        reference_contract,
                        reference_origin,
                        reference_shape,
                    })
                }
            }
            CoreKind::Perform {
                effect,
                operation,
                operation_arguments: _,
                payload_types,
                arguments,
                terminal,
                reference_contract,
                reference_origin,
                reference_shape,
            } => {
                operands = self.values(&arguments, sequence)?;
                if terminal {
                    ty = Type::Never;
                }
                Op::Perform {
                    effect,
                    operation,
                    payload_types,
                    terminal,
                    contract: EvaluationCallContract {
                        mandatory_tail: false,
                        prepared_receiver: false,
                        reference_contract,
                        reference_origin,
                        reference_shape,
                    },
                }
            }
            CoreKind::IntrinsicCall {
                operator,
                arguments,
            } => {
                if matches!(operator.as_str(), "and" | "or") && arguments.len() == 2 {
                    operands = self.values(&arguments[..1], sequence)?;
                    if let Some(value) = sequence.terminal {
                        return Ok(value);
                    }
                    Op::LazyBoolean {
                        conjunction: operator == "and",
                        right: self.region(arguments[1])?,
                    }
                } else {
                    operands = self.values(&arguments, sequence)?;
                    Op::Intrinsic(operator)
                }
            }
            CoreKind::ReleaseAvailable(value) => {
                operands = self.values(&[value], sequence)?;
                Op::ReleaseAvailable
            }
            CoreKind::Block(_) => {
                let region = self.region(source)?;
                if matches!(
                    self.regions[region.0 as usize].exit,
                    EvaluationExit::Diverge(_)
                ) {
                    ty = Type::Never;
                }
                Op::Scope(region)
            }
            CoreKind::Label { brand, body } => Op::Label {
                brand,
                body: self.region(body)?,
            },
            CoreKind::LabelValue { brand } => Op::LabelValue(brand),
            CoreKind::Transfer { brand, value } => {
                operands = self.values(&[value], sequence)?;
                ty = Type::Never;
                Op::Transfer(brand)
            }
            CoreKind::Closure {
                callable,
                parameters,
                environment,
                body,
            } => Op::Closure {
                callable,
                parameters,
                environment,
                body: self.region(body)?,
            },
            CoreKind::Handle {
                computation,
                clauses,
            } => {
                let computation = self.region(computation)?;
                let mut arms = vec![];
                for contract in clauses {
                    arms.push(EvaluationHandlerArm {
                        region: self.region(contract.body)?,
                        brand: contract.brand,
                        effect: contract.effect,
                        operation: contract.operation,
                        payload_types: contract.payload_types,
                        patterns: contract.patterns,
                        bindings: contract.bindings,
                        resumption: contract.resumption,
                        continuation: contract.continuation,
                        terminal: contract.terminal,
                        span: contract.span,
                    });
                }
                Op::Handle { computation, arms }
            }
            CoreKind::Completion {
                computation,
                clauses,
                handles_operations,
                refinement_test,
                ..
            } => {
                // A tag-only completion through borrowed storage observes
                // that storage just like `is`; an empty selected constructor
                // must not turn the projected view into an owned shell.
                let observational = refinement_test.is_some() || self.borrowed_pattern_subject(computation);
                let computation = self.region_with_observation(computation, observational)?;
                let mut arms = vec![];
                for contract in clauses {
                    arms.push(EvaluationCompletionArm {
                        region: self.region(contract.body)?,
                        pattern: contract.pattern,
                        bindings: contract.bindings,
                        refinement: contract.refinement,
                        span: contract.span,
                    });
                }
                Op::Completion { computation, arms, handles_operations }
            }
            CoreKind::Error => {
                return Err(EvaluationError("Core error has no evaluation form".into()));
            }
        };
        self.emit(source, ty, operation, operands, sequence)
    }
}
