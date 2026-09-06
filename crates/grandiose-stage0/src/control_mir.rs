//! Control MIR: explicit CFG and return continuations, consuming Evaluation
//! MIR rather than rediscovering enclosing source-expression shapes.
//!
//! Migration is operation-based. Unsupported control capabilities leave the
//! legacy pipeline in charge until their typed transition is implemented;
//! they are never erased into ordinary jumps or ordinary function returns.

use crate::evaluation_mir::{
    EvaluationCallContract, EvaluationExit, EvaluationMir, EvaluationOperand,
    EvaluationOperation as EvalOp, EvaluationRegionId, EvaluationValue,
};
use crate::{CoreId, DefKey, GenericArgument, Safety, Span, Type};
use std::collections::{BTreeMap, BTreeSet};

mod legacy_bridge;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ControlValue(pub u32);
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ControlBlockId(pub u32);
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ControlScopeId(pub u32);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ControlValueDecl {
    pub ty: Type,
    pub source: CoreId,
    pub span: Span,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ControlScope {
    pub parent: Option<ControlScopeId>,
    pub source: CoreId,
    pub unsafe_scope: bool,
    pub bindings: Vec<ControlValue>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ControlOperation {
    Literal(String),
    Unit,
    /// Value flow; Ownership MIR decides whether this copies or transfers an
    /// owner. Control construction must not assert duplicability.
    Forward(ControlValue),
    Function {
        definition: DefKey,
        arguments: Vec<GenericArgument>,
    },
    Intrinsic {
        operator: String,
        arguments: Vec<ControlValue>,
    },
    Tuple(Vec<ControlValue>),
    Array(Vec<ControlValue>),
    /// Abstract destruction intent, not an eagerly selected Drop function.
    Discard(ControlValue),
    /// Forward the result before disposing of this lexical scope's owners.
    EndScope {
        scope: ControlScopeId,
        value: ControlValue,
        transferred: Option<ControlValue>,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ControlInstruction {
    pub scope: ControlScopeId,
    pub destination: ControlValue,
    pub operation: ControlOperation,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ControlEdge {
    pub target: ControlBlockId,
    pub arguments: Vec<ControlValue>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ControlTerminator {
    Goto(ControlEdge),
    SwitchBool {
        condition: ControlValue,
        on_true: ControlEdge,
        on_false: ControlEdge,
    },
    /// The result is defined at the normal-return block parameter, not before
    /// the call. A bottom call has no normal return continuation.
    Invoke {
        callee: ControlValue,
        arguments: Vec<ControlValue>,
        result: ControlValue,
        contract: EvaluationCallContract,
        continuation: Option<ControlBlockId>,
    },
    Return(ControlValue),
    Unreachable,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ControlBlock {
    pub parameters: Vec<ControlValue>,
    pub instructions: Vec<ControlInstruction>,
    pub terminator: ControlTerminator,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ControlError {
    Invalid(String),
    NotMigrated(&'static str),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ControlMir {
    definition: DefKey,
    safety: Safety,
    unsafe_execution: bool,
    parameters: Vec<ControlValue>,
    values: Vec<ControlValueDecl>,
    scopes: Vec<ControlScope>,
    entry: ControlBlockId,
    blocks: Vec<ControlBlock>,
}

impl ControlMir {
    pub fn definition(&self) -> DefKey {
        self.definition
    }
    pub fn entry(&self) -> ControlBlockId {
        self.entry
    }
    pub fn blocks(&self) -> &[ControlBlock] {
        &self.blocks
    }
    pub fn values(&self) -> &[ControlValueDecl] {
        &self.values
    }
    pub fn scopes(&self) -> &[ControlScope] {
        &self.scopes
    }

    pub fn lower(evaluation: &EvaluationMir) -> Result<Self, ControlError> {
        evaluation
            .validate()
            .map_err(|error| ControlError::Invalid(error.0))?;
        // Capability transitions are deliberately not ordinary expression
        // instructions. The migration gate is independent of source nesting.
        for region in evaluation.regions() {
            for instruction in &region.instructions {
                if !matches!(
                    &instruction.operation,
                    EvalOp::Literal(_)
                        | EvalOp::ReadLocal(_)
                        | EvalOp::Bind(_)
                        | EvalOp::Discard
                        | EvalOp::Intrinsic(_)
                        | EvalOp::Tuple
                        | EvalOp::Array
                        | EvalOp::Call(_)
                        | EvalOp::Function {
                            host_import: None,
                            ..
                        }
                        | EvalOp::Scope(_)
                        | EvalOp::LazyBoolean { .. }
                ) {
                    return Err(ControlError::NotMigrated(
                        "control capability or value operation",
                    ));
                }
            }
        }
        let root = &evaluation.regions()[evaluation.entry().0 as usize];
        let span = root.instructions[0].span;
        let mut builder = Builder {
            evaluation,
            result: Self {
                definition: evaluation.definition(),
                safety: evaluation.safety(),
                unsafe_execution: !evaluation.unsafe_implementations().is_empty()
                    || evaluation
                        .regions()
                        .iter()
                        .any(|region| region.unsafe_scope),
                parameters: vec![],
                values: vec![],
                scopes: vec![],
                entry: ControlBlockId(0),
                blocks: vec![],
            },
            mapped: BTreeMap::new(),
        };
        let mut names = BTreeMap::new();
        for (name, ty) in evaluation.parameters() {
            let value = builder.value(ty.clone(), CoreId(u32::MAX), span)?;
            builder.result.parameters.push(value);
            names.insert(name.clone(), value);
        }
        let entry = builder.block(builder.result.parameters.clone())?;
        let (exit, value) = builder.region(evaluation.entry(), entry, &names, None)?;
        if let Some(exit) = exit {
            builder.result.blocks[exit.0 as usize].terminator = ControlTerminator::Return(value);
        }
        builder.result.validate()?;
        Ok(builder.result)
    }

    /// Validate CFG typing and definite availability independently of the
    /// normalizer. Ownership, replay and cleanup obligations belong to later
    /// phase products and are not inferred from this structural proof.
    pub fn validate(&self) -> Result<(), ControlError> {
        let invalid = |message: &str| ControlError::Invalid(message.into());
        if self.blocks.get(self.entry.0 as usize).is_none() {
            return Err(invalid("missing entry block"));
        }
        let mut definitions = BTreeSet::new();
        for (index, scope) in self.scopes.iter().enumerate() {
            if scope
                .parent
                .is_some_and(|parent| parent.0 as usize >= index)
                || scope
                    .bindings
                    .iter()
                    .any(|value| self.values.get(value.0 as usize).is_none())
            {
                return Err(invalid("invalid lexical scope"));
            }
        }
        for block in &self.blocks {
            for value in block.parameters.iter().copied().chain(
                block
                    .instructions
                    .iter()
                    .map(|instruction| instruction.destination),
            ) {
                if self.values.get(value.0 as usize).is_none() || !definitions.insert(value) {
                    return Err(invalid("invalid or duplicate value definition"));
                }
            }
            for instruction in &block.instructions {
                if self.scopes.get(instruction.scope.0 as usize).is_none() {
                    return Err(invalid("missing instruction scope"));
                }
                self.validate_operation(instruction)?;
            }
            for edge in block.terminator.edges() {
                self.validate_edge(&edge)?;
            }
            match &block.terminator {
                ControlTerminator::SwitchBool { condition, .. } => {
                    if self.ty(*condition)? != &Type::Scalar(crate::ScalarType::Bool) {
                        return Err(invalid("branch condition is not Bool"));
                    }
                }
                ControlTerminator::Invoke {
                    callee,
                    arguments,
                    result,
                    continuation,
                    ..
                } => {
                    let Type::Callable {
                        parameters,
                        result: result_ty,
                        ..
                    } = self.ty(*callee)?
                    else {
                        return Err(invalid("invoke requires callable value"));
                    };
                    if parameters.len() != arguments.len()
                        || parameters
                            .iter()
                            .zip(arguments)
                            .any(|(ty, value)| self.ty(*value).ok() != Some(ty))
                        || self.ty(*result)? != result_ty.as_ref()
                        || continuation.is_none() != (**result_ty == Type::Never)
                    {
                        return Err(invalid("invoke boundary disagrees with callable contract"));
                    }
                    if let Some(target) = continuation {
                        if self.blocks[target.0 as usize].parameters != vec![*result] {
                            return Err(invalid(
                                "call result is not its return continuation parameter",
                            ));
                        }
                    } else if !definitions.insert(*result) {
                        return Err(invalid("duplicate terminal call result"));
                    }
                }
                _ => {}
            }
        }
        if self.blocks[self.entry.0 as usize].parameters != self.parameters {
            return Err(invalid("entry ABI parameters disagree"));
        }
        // Forward must-definition analysis. Start non-entry blocks at top;
        // intersection over reachable predecessors then monotonically removes
        // definitions unavailable on any incoming path.
        let mut reachable = BTreeSet::new();
        let mut pending = vec![self.entry];
        while let Some(id) = pending.pop() {
            if reachable.insert(id) {
                pending.extend(
                    self.blocks[id.0 as usize]
                        .terminator
                        .edges()
                        .into_iter()
                        .map(|edge| edge.target),
                );
            }
        }
        let mut incoming = vec![definitions.clone(); self.blocks.len()];
        incoming[self.entry.0 as usize] = BTreeSet::new();
        loop {
            let mut changed = false;
            for id in &reachable {
                let block = &self.blocks[id.0 as usize];
                let mut available = incoming[id.0 as usize].clone();
                available.extend(block.parameters.iter().copied());
                available.extend(
                    block
                        .instructions
                        .iter()
                        .map(|instruction| instruction.destination),
                );
                for edge in block.terminator.edges() {
                    let next = incoming[edge.target.0 as usize]
                        .intersection(&available)
                        .copied()
                        .collect();
                    if next != incoming[edge.target.0 as usize] {
                        incoming[edge.target.0 as usize] = next;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        for id in reachable {
            let block = &self.blocks[id.0 as usize];
            let mut available = incoming[id.0 as usize].clone();
            available.extend(block.parameters.iter().copied());
            for instruction in &block.instructions {
                if instruction
                    .operation
                    .inputs()
                    .iter()
                    .any(|value| !available.contains(value))
                {
                    return Err(invalid("instruction uses an unavailable value"));
                }
                available.insert(instruction.destination);
            }
            if block
                .terminator
                .inputs()
                .iter()
                .any(|value| !available.contains(value))
            {
                return Err(invalid("terminator uses an unavailable value"));
            }
        }
        Ok(())
    }

    fn ty(&self, value: ControlValue) -> Result<&Type, ControlError> {
        self.values
            .get(value.0 as usize)
            .map(|value| &value.ty)
            .ok_or_else(|| ControlError::Invalid("missing value".into()))
    }
    fn validate_edge(&self, edge: &ControlEdge) -> Result<(), ControlError> {
        let target = self
            .blocks
            .get(edge.target.0 as usize)
            .ok_or_else(|| ControlError::Invalid("missing edge target".into()))?;
        if edge.arguments.len() != target.parameters.len()
            || edge
                .arguments
                .iter()
                .zip(&target.parameters)
                .any(|(argument, parameter)| self.ty(*argument).ok() != self.ty(*parameter).ok())
        {
            return Err(ControlError::Invalid(
                "edge argument types disagree with parameters".into(),
            ));
        }
        Ok(())
    }
    fn validate_operation(&self, instruction: &ControlInstruction) -> Result<(), ControlError> {
        let ty = self.ty(instruction.destination)?;
        for input in instruction.operation.inputs() {
            self.ty(input)?;
        }
        let valid = match &instruction.operation {
            ControlOperation::Unit | ControlOperation::Discard(_) => ty == &Type::Unit,
            ControlOperation::Forward(value) => ty == self.ty(*value)?,
            ControlOperation::EndScope {
                scope,
                value,
                transferred,
            } => {
                self.scopes.get(scope.0 as usize).is_some()
                    && transferred.is_none_or(|value| self.values.get(value.0 as usize).is_some())
                    && ty == self.ty(*value)?
            }
            ControlOperation::Tuple(values) => {
                if values.is_empty() && ty == &Type::Unit {
                    true
                } else {
                    matches!(ty, Type::Tuple(fields) if fields.len() == values.len() && fields.iter().zip(values).all(|(ty, value)| self.ty(*value).ok() == Some(ty)))
                }
            }
            ControlOperation::Array(values) => {
                matches!(ty, Type::Array(element) if values.iter().all(|value| self.ty(*value).ok() == Some(element.as_ref())))
            }
            ControlOperation::Function { .. } => matches!(ty, Type::Callable { .. }),
            ControlOperation::Literal(_) => {
                !matches!(ty, Type::Never | Type::Error | Type::Infer(_))
            }
            ControlOperation::Intrinsic { arguments, .. } => !arguments.is_empty(),
        };
        if valid {
            Ok(())
        } else {
            Err(ControlError::Invalid(
                "operation result contract disagrees".into(),
            ))
        }
    }
}

impl ControlOperation {
    fn inputs(&self) -> Vec<ControlValue> {
        match self {
            Self::Forward(value) | Self::Discard(value) | Self::EndScope { value, .. } => {
                vec![*value]
            }
            Self::Intrinsic { arguments, .. } | Self::Tuple(arguments) | Self::Array(arguments) => {
                arguments.clone()
            }
            _ => vec![],
        }
    }
}
impl ControlTerminator {
    fn edges(&self) -> Vec<ControlEdge> {
        match self {
            Self::Goto(edge) => vec![edge.clone()],
            Self::SwitchBool {
                on_true, on_false, ..
            } => vec![on_true.clone(), on_false.clone()],
            Self::Invoke {
                result,
                continuation: Some(target),
                ..
            } => vec![ControlEdge {
                target: *target,
                arguments: vec![*result],
            }],
            _ => vec![],
        }
    }
    fn inputs(&self) -> Vec<ControlValue> {
        match self {
            Self::Goto(edge) => edge.arguments.clone(),
            Self::SwitchBool {
                condition,
                on_true,
                on_false,
            } => {
                let mut values = vec![*condition];
                values.extend(&on_true.arguments);
                values.extend(&on_false.arguments);
                values
            }
            Self::Invoke {
                callee, arguments, ..
            } => {
                let mut values = vec![*callee];
                values.extend(arguments);
                values
            }
            Self::Return(value) => vec![*value],
            Self::Unreachable => vec![],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Digest, FileKey, ScalarType};

    fn fixture() -> ControlMir {
        let digest = Digest::of_bytes(b"control-validator");
        let span = Span {
            file: FileKey(digest),
            start: 0,
            end: 1,
        };
        let values = (0..5)
            .map(|index| ControlValueDecl {
                ty: Type::Scalar(if index == 0 {
                    ScalarType::Bool
                } else {
                    ScalarType::I64
                }),
                source: CoreId(index),
                span,
            })
            .collect();
        let instruction = |destination, text: &str| ControlInstruction {
            scope: ControlScopeId(0),
            destination: ControlValue(destination),
            operation: ControlOperation::Literal(text.into()),
        };
        let edge = |target, values: Vec<u32>| ControlEdge {
            target: ControlBlockId(target),
            arguments: values.into_iter().map(ControlValue).collect(),
        };
        let mir = ControlMir {
            definition: DefKey(digest),
            safety: Safety::Safe,
            unsafe_execution: false,
            parameters: vec![],
            values,
            scopes: vec![ControlScope {
                parent: None,
                source: CoreId(0),
                unsafe_scope: false,
                bindings: vec![],
            }],
            entry: ControlBlockId(0),
            blocks: vec![
                ControlBlock {
                    parameters: vec![],
                    instructions: vec![instruction(0, "true"), instruction(1, "1")],
                    terminator: ControlTerminator::SwitchBool {
                        condition: ControlValue(0),
                        on_true: edge(1, vec![]),
                        on_false: edge(2, vec![]),
                    },
                },
                ControlBlock {
                    parameters: vec![],
                    instructions: vec![instruction(2, "2")],
                    terminator: ControlTerminator::Goto(edge(3, vec![2])),
                },
                ControlBlock {
                    parameters: vec![],
                    instructions: vec![instruction(3, "3")],
                    terminator: ControlTerminator::Goto(edge(3, vec![3])),
                },
                ControlBlock {
                    parameters: vec![ControlValue(4)],
                    instructions: vec![],
                    terminator: ControlTerminator::Return(ControlValue(4)),
                },
            ],
        };
        mir.validate().unwrap();
        mir
    }

    #[test]
    fn rejects_phi_argument_type_mismatch() {
        let mut mir = fixture();
        let ControlTerminator::Goto(edge) = &mut mir.blocks[1].terminator else {
            unreachable!()
        };
        edge.arguments[0] = ControlValue(0);
        assert!(
            matches!(mir.validate(), Err(ControlError::Invalid(message)) if message.contains("edge argument types"))
        );
    }

    #[test]
    fn rejects_value_available_only_in_the_other_branch() {
        let mut mir = fixture();
        mir.blocks[2].instructions[0].operation = ControlOperation::Forward(ControlValue(2));
        assert!(
            matches!(mir.validate(), Err(ControlError::Invalid(message)) if message.contains("unavailable value"))
        );
    }

    #[test]
    fn rejects_non_boolean_branch_and_missing_targets() {
        let mut mir = fixture();
        let ControlTerminator::SwitchBool { condition, .. } = &mut mir.blocks[0].terminator else {
            unreachable!()
        };
        *condition = ControlValue(1);
        assert!(
            matches!(mir.validate(), Err(ControlError::Invalid(message)) if message.contains("not Bool"))
        );
        let ControlTerminator::SwitchBool {
            condition, on_true, ..
        } = &mut mir.blocks[0].terminator
        else {
            unreachable!()
        };
        *condition = ControlValue(0);
        on_true.target = ControlBlockId(99);
        assert!(
            matches!(mir.validate(), Err(ControlError::Invalid(message)) if message.contains("missing edge target"))
        );
    }

    #[test]
    fn rejects_duplicate_parameter_and_instruction_definitions() {
        let mut mir = fixture();
        mir.blocks[3].parameters[0] = ControlValue(2);
        assert!(
            matches!(mir.validate(), Err(ControlError::Invalid(message)) if message.contains("duplicate value definition"))
        );
    }

    #[test]
    fn normal_return_value_is_unavailable_before_invocation() {
        let mut mir = fixture();
        mir.values.push(ControlValueDecl {
            ty: Type::Callable {
                safety: Safety::Safe,
                lifetime_binders: 0,
                parameters: vec![],
                result: Box::new(Type::Scalar(ScalarType::I64)),
                effects: crate::EffectRow::empty(),
                invocation: crate::Quantity::ONCE,
            },
            source: CoreId(5),
            span: mir.values[0].span,
        });
        mir.values.push(ControlValueDecl {
            ty: Type::Scalar(ScalarType::I64),
            source: CoreId(6),
            span: mir.values[0].span,
        });
        mir.blocks[0].instructions.push(ControlInstruction {
            scope: ControlScopeId(0),
            destination: ControlValue(5),
            operation: ControlOperation::Function {
                definition: mir.definition,
                arguments: vec![],
            },
        });
        mir.blocks[0].terminator = ControlTerminator::Invoke {
            callee: ControlValue(5),
            arguments: vec![],
            result: ControlValue(6),
            contract: EvaluationCallContract {
                reference_contract: crate::CallReferenceOrigin::None,
                reference_origin: crate::CallReferenceOrigin::None,
                reference_shape: crate::CallReferenceShape::None,
            },
            continuation: Some(ControlBlockId(1)),
        };
        mir.blocks[1].parameters.push(ControlValue(6));
        mir.validate().unwrap();
        mir.blocks[0].instructions[1].operation = ControlOperation::Forward(ControlValue(6));
        assert!(
            matches!(mir.validate(), Err(ControlError::Invalid(message)) if message.contains("unavailable value"))
        );
    }
}

struct Builder<'a> {
    evaluation: &'a EvaluationMir,
    result: ControlMir,
    mapped: BTreeMap<EvaluationValue, ControlValue>,
}
impl Builder<'_> {
    fn value(
        &mut self,
        ty: Type,
        source: CoreId,
        span: Span,
    ) -> Result<ControlValue, ControlError> {
        let id = ControlValue(
            u32::try_from(self.result.values.len())
                .map_err(|_| ControlError::Invalid("value arena exhausted".into()))?,
        );
        self.result
            .values
            .push(ControlValueDecl { ty, source, span });
        Ok(id)
    }
    fn block(&mut self, parameters: Vec<ControlValue>) -> Result<ControlBlockId, ControlError> {
        let id = ControlBlockId(
            u32::try_from(self.result.blocks.len())
                .map_err(|_| ControlError::Invalid("block arena exhausted".into()))?,
        );
        self.result.blocks.push(ControlBlock {
            parameters,
            instructions: vec![],
            terminator: ControlTerminator::Unreachable,
        });
        Ok(id)
    }
    fn operands(&self, operands: &[EvaluationOperand]) -> Result<Vec<ControlValue>, ControlError> {
        operands
            .iter()
            .map(|operand| match operand {
                EvaluationOperand::Value(value) => {
                    self.mapped.get(value).copied().ok_or_else(|| {
                        ControlError::Invalid("evaluation dependency was not composed".into())
                    })
                }
                EvaluationOperand::Place(_) => Err(ControlError::NotMigrated("place ownership")),
            })
            .collect()
    }
    fn emit(
        &mut self,
        block: ControlBlockId,
        scope: ControlScopeId,
        destination: ControlValue,
        operation: ControlOperation,
    ) {
        self.result.blocks[block.0 as usize]
            .instructions
            .push(ControlInstruction {
                scope,
                destination,
                operation,
            });
    }
    fn region(
        &mut self,
        id: EvaluationRegionId,
        mut block: ControlBlockId,
        outer: &BTreeMap<String, ControlValue>,
        parent: Option<ControlScopeId>,
    ) -> Result<(Option<ControlBlockId>, ControlValue), ControlError> {
        let region = self.evaluation.regions()[id.0 as usize].clone();
        let exit_value = match region.exit {
            EvaluationExit::Yield(value) | EvaluationExit::Diverge(value) => value,
        };
        let transferred_name = region
            .instructions
            .iter()
            .find(|instruction| instruction.value == exit_value)
            .and_then(|instruction| match &instruction.operation {
                EvalOp::ReadLocal(name) => Some(name.clone()),
                _ => None,
            });
        let scope = ControlScopeId(
            u32::try_from(self.result.scopes.len())
                .map_err(|_| ControlError::Invalid("scope arena exhausted".into()))?,
        );
        self.result.scopes.push(ControlScope {
            parent,
            source: region.source,
            unsafe_scope: region.unsafe_scope,
            bindings: vec![],
        });
        let mut names = outer.clone();
        for instruction in region.instructions {
            let operands = self.operands(&instruction.operands)?;
            // Allocate actual binding storage before its Unit statement result;
            // this retains the source binding origin used by ownership import.
            if let EvalOp::Bind(name) = &instruction.operation {
                let source = operands[0];
                let binding = self.value(
                    self.result.ty(source)?.clone(),
                    instruction.source,
                    instruction.span,
                )?;
                self.emit(block, scope, binding, ControlOperation::Forward(source));
                self.result.scopes[scope.0 as usize].bindings.push(binding);
                names.insert(name.clone(), binding);
            }
            let destination =
                self.value(instruction.ty.clone(), instruction.source, instruction.span)?;
            self.mapped.insert(instruction.value, destination);
            let operation = match instruction.operation {
                EvalOp::Literal(value) => ControlOperation::Literal(value),
                EvalOp::ReadLocal(name) => ControlOperation::Forward(
                    *names
                        .get(&name)
                        .ok_or_else(|| ControlError::Invalid(format!("unbound local {name}")))?,
                ),
                EvalOp::Bind(_) => ControlOperation::Unit,
                EvalOp::Discard => ControlOperation::Discard(operands[0]),
                EvalOp::Tuple => ControlOperation::Tuple(operands),
                EvalOp::Array => ControlOperation::Array(operands),
                EvalOp::Intrinsic(operator) => ControlOperation::Intrinsic {
                    operator,
                    arguments: operands,
                },
                EvalOp::Function {
                    definition,
                    arguments,
                    host_import: None,
                } => ControlOperation::Function {
                    definition,
                    arguments,
                },
                EvalOp::Scope(child) => {
                    let (exit, value) = self.region(child, block, &names, Some(scope))?;
                    let Some(exit) = exit else {
                        return Ok((None, value));
                    };
                    block = exit;
                    ControlOperation::Forward(value)
                }
                EvalOp::LazyBoolean { conjunction, right } => {
                    let right_entry = self.block(vec![])?;
                    let join = self.block(vec![destination])?;
                    let (right_exit, right_value) =
                        self.region(right, right_entry, &names, Some(scope))?;
                    if let Some(exit) = right_exit {
                        self.result.blocks[exit.0 as usize].terminator =
                            ControlTerminator::Goto(ControlEdge {
                                target: join,
                                arguments: vec![right_value],
                            });
                    }
                    let selected = ControlEdge {
                        target: right_entry,
                        arguments: vec![],
                    };
                    let skipped = ControlEdge {
                        target: join,
                        arguments: vec![operands[0]],
                    };
                    let (on_true, on_false) = if conjunction {
                        (selected, skipped)
                    } else {
                        (skipped, selected)
                    };
                    self.result.blocks[block.0 as usize].terminator =
                        ControlTerminator::SwitchBool {
                            condition: operands[0],
                            on_true,
                            on_false,
                        };
                    block = join;
                    continue;
                }
                EvalOp::Call(contract) => {
                    let continuation = if instruction.ty == Type::Never {
                        None
                    } else {
                        Some(self.block(vec![destination])?)
                    };
                    self.result.blocks[block.0 as usize].terminator = ControlTerminator::Invoke {
                        callee: operands[0],
                        arguments: operands[1..].to_vec(),
                        result: destination,
                        contract,
                        continuation,
                    };
                    let Some(next) = continuation else {
                        return Ok((None, destination));
                    };
                    block = next;
                    continue;
                }
                _ => {
                    return Err(ControlError::NotMigrated(
                        "control capability or value operation",
                    ));
                }
            };
            self.emit(block, scope, destination, operation);
        }
        let value = match region.exit {
            EvaluationExit::Yield(value) | EvaluationExit::Diverge(value) => self.mapped[&value],
        };
        if matches!(region.exit, EvaluationExit::Diverge(_)) {
            return Ok((None, value));
        }
        let decl = self.result.values[value.0 as usize].clone();
        let result = self.value(decl.ty, region.source, decl.span)?;
        self.emit(
            block,
            scope,
            result,
            ControlOperation::EndScope {
                scope,
                value,
                transferred: transferred_name.and_then(|name| names.get(&name).copied()),
            },
        );
        Ok((Some(block), result))
    }
}
