//! Evaluation MIR: ordered operations and deferred regions, before CFG and
//! ownership elaboration. Core IDs below are provenance/proof references only;
//! executable dependencies use this language's value, place and region IDs.
//!
//! This first migration product is deliberately separate from legacy MIR.
//! It does not claim that legacy code generation consumes these regions yet.

use std::collections::{BTreeMap, BTreeSet};

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
    Local {
        name: String,
        ty: Type,
    },
    Temporary {
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
    Literal(String),
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
        let mut pending = vec![self.entry];
        let mut regions = BTreeSet::new();
        let mut values = BTreeSet::new();
        while let Some(id) = pending.pop() {
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
                for operand in &instruction.operands {
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
                instruction.operation.regions(&mut pending);
                if instruction.ty == Type::Never && index + 1 != region.instructions.len() {
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
                || diverges != (last.ty == Type::Never)
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
            Self::Local { .. } => {}
            Self::Temporary { value, .. } => result.push(*value),
            Self::Field { base, .. } => base.dependencies(result),
            Self::Deref { reference, .. } => result.push(*reference),
        }
    }
}
impl EvaluationInstruction {
    fn validate_shape(&self) -> Result<(), EvaluationError> {
        use EvaluationOperation as Op;
        let values = self
            .operands
            .iter()
            .all(|operand| matches!(operand, EvaluationOperand::Value(_)));
        let arity = self.operands.len();
        let valid = match &self.operation {
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
            Op::PatternTest { .. } | Op::Bind(_) | Op::Deref | Op::LazyBoolean { .. } => {
                values && arity == 1
            }
            Op::Transfer(_) => values && arity == 1 && self.ty == Type::Never,
            Op::Move => arity == 1,
            Op::Borrow { .. } => matches!(&self.operands[..], [EvaluationOperand::Place(_)]),
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
            Self::Completion { computation, arms } => {
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
        let mut sequence = Sequence::default();
        let value = if let CoreKind::Block(items) = &self.body.expression(source).kind {
            let items = items.clone();
            let mut value = None;
            for item in items {
                value = Some(self.expression(item, &mut sequence)?);
                if sequence.terminal.is_some() {
                    break;
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
        if ty == Type::Never {
            sequence.terminal = Some(value);
        }
        sequence.instructions.push(EvaluationInstruction {
            value,
            source,
            span: self.body.expression(source).span,
            ty,
            operation,
            operands,
        });
        sequence.values.insert(source, value);
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
                let place = match self.expression_place(value, sequence)? {
                    Some(place) => place,
                    None => EvaluationPlace::Temporary {
                        value: self.expression(value, sequence)?,
                        ty: self.body.expression(value).ty.clone(),
                    },
                };
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
                reference_contract,
                reference_origin,
                reference_shape,
            } => {
                if matches!(&self.body.expression(callee).ty, Type::Callable { result, .. } if **result == Type::Never)
                {
                    ty = Type::Never;
                }
                operands = self.values(&[callee], sequence)?;
                if sequence.terminal.is_none() {
                    operands.extend(self.values(&arguments, sequence)?);
                }
                Op::Call(EvaluationCallContract {
                    reference_contract,
                    reference_origin,
                    reference_shape,
                })
            }
            CoreKind::Perform {
                effect,
                operation,
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
            } => {
                let computation = self.region(computation)?;
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
                Op::Completion { computation, arms }
            }
            CoreKind::Error => {
                return Err(EvaluationError("Core error has no evaluation form".into()));
            }
        };
        self.emit(source, ty, operation, operands, sequence)
    }
}
