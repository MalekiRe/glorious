//! Temporary phase adapter into the existing ownership/destruction pipeline.
//! Its admission is by operation and representation contract, never by an
//! enclosing source-expression pattern. No Core body is available here.

use super::*;
use crate::{
    MirBlock, MirBlockId, MirControlTables, MirFunction, MirInstruction, MirLocal, MirLocalDecl,
    MirScopeId, MirTerminator, PrimitiveRole, ScalarType,
};

fn plain(ty: &Type) -> bool {
    match ty {
        Type::Unit | Type::Never | Type::Scalar(_) => true,
        Type::Tuple(fields) => fields.iter().all(plain),
        _ => false,
    }
}

impl ControlMir {
    pub(crate) fn is_legacy_value_domain(evaluation: &EvaluationMir) -> bool {
        evaluation.parameters().iter().all(|(_, ty)| plain(ty))
            && evaluation.regions().iter().all(|region| {
                region.instructions.iter().all(|instruction| {
                    plain(&instruction.ty) || matches!(instruction.ty, Type::Callable { .. })
                })
            })
    }
    /// Emit the migrated value domain. `None` means the adapter has not yet
    /// acquired this ownership/representation contract, not malformed Core.
    /// All source-owner phases still run on the returned legacy MIR body.
    pub(crate) fn emit_legacy_values(
        &self,
        declared_result: Type,
        primitives: Option<&BTreeMap<DefKey, PrimitiveRole>>,
        retain_destruction: bool,
    ) -> Option<MirFunction> {
        if !plain(&declared_result)
            || self
                .parameters
                .iter()
                .any(|value| !plain(&self.values[value.0 as usize].ty))
        {
            return None;
        }
        let mut functions = BTreeMap::new();
        for block in &self.blocks {
            for instruction in &block.instructions {
                if let ControlOperation::Function {
                    definition,
                    arguments,
                } = &instruction.operation
                {
                    if primitives.is_some_and(|primitives| primitives.contains_key(definition)) {
                        return None;
                    }
                    functions.insert(instruction.destination, (*definition, arguments.clone()));
                }
            }
        }
        // Function identities are immutable symbolic values. Propagate them
        // across lexical aliases without creating an owned closure object.
        loop {
            let mut changed = false;
            for block in &self.blocks {
                for instruction in &block.instructions {
                    if let ControlOperation::Forward(source)
                    | ControlOperation::EndScope { value: source, .. } = instruction.operation
                        && let Some(function) = functions.get(&source).cloned()
                        && !functions.contains_key(&instruction.destination)
                    {
                        functions.insert(instruction.destination, function);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        if self.values.iter().enumerate().any(|(index, value)| {
            !plain(&value.ty) && !functions.contains_key(&ControlValue(index as u32))
        }) {
            return None;
        }
        let mut locals: Vec<_> = self
            .values
            .iter()
            .map(|value| MirLocalDecl {
                ty: value.ty.clone(),
                source: value.source,
            })
            .collect();
        let local = |value: ControlValue| MirLocal(value.0);
        let mut blocks = vec![];
        for block in &self.blocks {
            let mut instructions = vec![];
            for instruction in &block.instructions {
                let dst = local(instruction.destination);
                let ty = &self.values[instruction.destination.0 as usize].ty;
                let operation = match &instruction.operation {
                    ControlOperation::Unit => MirInstruction::ConstUnit { dst },
                    ControlOperation::Discard(value) => {
                        if retain_destruction {
                            instructions.push(MirInstruction::Drop {
                                local: local(*value),
                            });
                        }
                        MirInstruction::ConstUnit { dst }
                    }
                    ControlOperation::Forward(value) => MirInstruction::Copy {
                        dst,
                        src: local(*value),
                    },
                    ControlOperation::EndScope {
                        scope,
                        value,
                        transferred,
                    } => {
                        instructions.push(MirInstruction::Copy {
                            dst,
                            src: local(*value),
                        });
                        if retain_destruction {
                            for binding in self.scopes[scope.0 as usize].bindings.iter().rev() {
                                if Some(*binding) != *transferred {
                                    instructions.push(MirInstruction::Drop {
                                        local: local(*binding),
                                    });
                                }
                            }
                        }
                        continue;
                    }
                    ControlOperation::Function {
                        definition,
                        arguments,
                    } => MirInstruction::MakeCallable {
                        dst,
                        callee: *definition,
                        captures: vec![],
                        generic_arguments: arguments.clone(),
                        trait_instance: None,
                        environment: None,
                    },
                    ControlOperation::Literal(text) => match ty {
                        Type::Unit => MirInstruction::ConstUnit { dst },
                        Type::Scalar(ScalarType::Bool)
                            if matches!(text.as_str(), "true" | "false") =>
                        {
                            MirInstruction::ConstBool {
                                dst,
                                value: text == "true",
                            }
                        }
                        Type::Scalar(ScalarType::Char) => MirInstruction::ConstChar {
                            dst,
                            value: crate::mir::parse_char_literal(text).ok()?,
                        },
                        Type::Scalar(ScalarType::Text) => MirInstruction::ConstText {
                            dst,
                            value: crate::mir::parse_text_literal(text).ok()?,
                        },
                        Type::Scalar(ScalarType::Bytes) => return None,
                        Type::Scalar(scalar) => {
                            crate::mir::materialize_numeric_literal(dst, text, *scalar).ok()?
                        }
                        _ => return None,
                    },
                    ControlOperation::Tuple(values) if values.is_empty() && ty == &Type::Unit => {
                        MirInstruction::ConstUnit { dst }
                    }
                    ControlOperation::Tuple(values) => MirInstruction::MakeTuple {
                        dst,
                        fields: values.iter().copied().map(local).collect(),
                    },
                    ControlOperation::Intrinsic {
                        operator,
                        arguments,
                    } => {
                        let types = arguments
                            .iter()
                            .map(|value| &self.values[value.0 as usize].ty)
                            .collect::<Vec<_>>();
                        let arguments = arguments.iter().copied().map(local).collect::<Vec<_>>();
                        match (
                            operator.as_str(),
                            arguments.as_slice(),
                            types.as_slice(),
                            ty,
                        ) {
                            (
                                "+",
                                [value],
                                [Type::Scalar(ScalarType::I64)],
                                Type::Scalar(ScalarType::I64),
                            ) => MirInstruction::Copy { dst, src: *value },
                            (
                                "!",
                                [value],
                                [Type::Scalar(ScalarType::Bool)],
                                Type::Scalar(ScalarType::Bool),
                            ) => MirInstruction::NotBool { dst, value: *value },
                            (
                                "-",
                                [value],
                                [Type::Scalar(ScalarType::I64)],
                                Type::Scalar(ScalarType::I64),
                            ) => {
                                let zero = MirLocal(u32::try_from(locals.len()).ok()?);
                                locals.push(MirLocalDecl {
                                    ty: Type::Scalar(ScalarType::I64),
                                    source: self.values[instruction.destination.0 as usize].source,
                                });
                                instructions.push(MirInstruction::ConstI64 {
                                    dst: zero,
                                    value: 0,
                                });
                                MirInstruction::SubI64 {
                                    dst,
                                    left: zero,
                                    right: *value,
                                }
                            }
                            (
                                operator,
                                [left, right],
                                [Type::Scalar(ScalarType::I64), Type::Scalar(ScalarType::I64)],
                                result,
                            ) => {
                                let (left, right) = (*left, *right);
                                match (operator, result) {
                                    ("+", Type::Scalar(ScalarType::I64)) => {
                                        MirInstruction::AddI64 { dst, left, right }
                                    }
                                    ("-", Type::Scalar(ScalarType::I64)) => {
                                        MirInstruction::SubI64 { dst, left, right }
                                    }
                                    ("*", Type::Scalar(ScalarType::I64)) => {
                                        MirInstruction::MulI64 { dst, left, right }
                                    }
                                    ("/", Type::Scalar(ScalarType::I64)) => {
                                        MirInstruction::DivI64 { dst, left, right }
                                    }
                                    ("%", Type::Scalar(ScalarType::I64)) => {
                                        MirInstruction::RemI64 { dst, left, right }
                                    }
                                    ("==", Type::Scalar(ScalarType::Bool)) => {
                                        MirInstruction::EqI64 { dst, left, right }
                                    }
                                    ("!=", Type::Scalar(ScalarType::Bool)) => {
                                        MirInstruction::NeI64 { dst, left, right }
                                    }
                                    ("<", Type::Scalar(ScalarType::Bool)) => {
                                        MirInstruction::LtI64 { dst, left, right }
                                    }
                                    ("<=", Type::Scalar(ScalarType::Bool)) => {
                                        MirInstruction::LeI64 { dst, left, right }
                                    }
                                    (">", Type::Scalar(ScalarType::Bool)) => {
                                        MirInstruction::GtI64 { dst, left, right }
                                    }
                                    (">=", Type::Scalar(ScalarType::Bool)) => {
                                        MirInstruction::GeI64 { dst, left, right }
                                    }
                                    _ => return None,
                                }
                            }
                            (
                                operator,
                                [left, right],
                                [
                                    Type::Scalar(ScalarType::Bool),
                                    Type::Scalar(ScalarType::Bool),
                                ],
                                Type::Scalar(ScalarType::Bool),
                            ) => {
                                let (left, right) = (*left, *right);
                                match operator {
                                    "==" => MirInstruction::EqBool { dst, left, right },
                                    "!=" => MirInstruction::NeBool { dst, left, right },
                                    _ => return None,
                                }
                            }
                            _ => return None,
                        }
                    }
                    ControlOperation::Array(_) => return None,
                };
                instructions.push(operation);
            }
            let terminator = match &block.terminator {
                ControlTerminator::Goto(edge) => MirTerminator::Goto {
                    target: MirBlockId(edge.target.0),
                    arguments: edge.arguments.iter().copied().map(local).collect(),
                },
                ControlTerminator::SwitchBool {
                    condition,
                    on_true,
                    on_false,
                } => MirTerminator::SwitchBool {
                    condition: local(*condition),
                    then_target: MirBlockId(on_true.target.0),
                    then_arguments: on_true.arguments.iter().copied().map(local).collect(),
                    else_target: MirBlockId(on_false.target.0),
                    else_arguments: on_false.arguments.iter().copied().map(local).collect(),
                },
                ControlTerminator::Invoke {
                    callee,
                    arguments,
                    result,
                    continuation,
                    ..
                } => {
                    let (callee, generic_arguments) = functions.get(callee)?;
                    instructions.push(MirInstruction::Call {
                        dst: local(*result),
                        callee: *callee,
                        generic_arguments: generic_arguments.clone(),
                        trait_instance: None,
                        arguments: arguments.iter().copied().map(local).collect(),
                    });
                    match continuation {
                        Some(target) => MirTerminator::Goto {
                            target: MirBlockId(target.0),
                            arguments: vec![local(*result)],
                        },
                        None => MirTerminator::Unreachable,
                    }
                }
                ControlTerminator::Return(value) => MirTerminator::Return {
                    value: local(*value),
                },
                ControlTerminator::Unreachable => MirTerminator::Unreachable,
            };
            blocks.push(MirBlock {
                scope: MirScopeId::ROOT,
                parameters: block.parameters.iter().copied().map(local).collect(),
                instructions,
                terminator,
            });
        }
        // Legacy MIR's function ABI is separate from block parameters.
        blocks[self.entry.0 as usize].parameters.clear();
        Some(MirFunction {
            safety: self.safety,
            unsafe_execution: self.unsafe_execution,
            definition: self.definition,
            nominal_copy_descriptors: vec![],
            captures: 0,
            parameters: self.parameters.iter().copied().map(local).collect(),
            locals,
            result: declared_result,
            control: MirControlTables::default(),
            entry: MirBlockId(self.entry.0),
            blocks,
        })
    }
}
