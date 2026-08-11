//! Fail-closed LLVM lowering for the first scalar-and-value-aggregate `.grbc` AOT slice.
//!
//! This is intentionally an artifact boundary, not a second source compiler:
//! callers hand it encoded bytecode, which is decoded and verified before a
//! single LLVM instruction is emitted.  It does not construct a [`Vm`] or use
//! any interpreter entry point.  The supported surface is deliberately small
//! (direct scalar/value-aggregate functions with ordinary control flow); every other valid G1 instruction
//! remains an explicit lowering error until it has a native ABI.

use std::{error::Error, fmt};

use grandiose_vm::{
    load_verified, verify::VerifiedArtifact, Artifact, Constant, Function, Instruction, Primitive,
    Type, TypeId, UNIT,
};

/// Error emitted when verified bytecode has no defined ABI in the scalar AOT
/// subset.  `Unsupported` is a success of verification, not permission to
/// execute through the VM.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArtifactLlvmError {
    Load(String),
    MissingEntry,
    UnsupportedType {
        function: u32,
        ty: TypeId,
    },
    UnsupportedInstruction {
        function: u32,
        instruction: u32,
        opcode: &'static str,
    },
    UnsupportedPrimitive {
        function: u32,
        instruction: u32,
        primitive: Primitive,
    },
}

impl fmt::Display for ArtifactLlvmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Load(error) => write!(f, "artifact decode or verification failed: {error}"),
            Self::MissingEntry => f.write_str("artifact has no entry function"),
            Self::UnsupportedType { function, ty } => {
                write!(f, "function {function} uses unsupported scalar-AOT type {ty}")
            }
            Self::UnsupportedInstruction { function, instruction, opcode } => write!(
                f,
                "function {function}, instruction {instruction}: scalar AOT does not support {opcode}"
            ),
            Self::UnsupportedPrimitive { function, instruction, primitive } => write!(
                f,
                "function {function}, instruction {instruction}: scalar AOT does not support primitive {primitive:?}"
            ),
        }
    }
}

impl Error for ArtifactLlvmError {}

/// Decode and verify an encoded G1 artifact, then emit its scalar AOT LLVM IR.
///
/// This is the public artifact-to-native boundary.  A malformed artifact never
/// reaches lowering, and a verified-but-unsupported artifact never falls back
/// to the register VM.
pub fn emit_artifact_llvm_ir(bytes: &[u8]) -> Result<String, ArtifactLlvmError> {
    let artifact =
        load_verified(bytes).map_err(|error| ArtifactLlvmError::Load(error.to_string()))?;
    emit_verified_artifact_llvm_ir(&artifact)
}

/// Emit LLVM IR from an already-verified artifact.  This only inspects its
/// immutable compatibility image; it does not instantiate a VM.
pub fn emit_verified_artifact_llvm_ir(
    verified: &VerifiedArtifact,
) -> Result<String, ArtifactLlvmError> {
    let artifact = verified.artifact();
    let entry = artifact
        .entry_function
        .ok_or(ArtifactLlvmError::MissingEntry)?;
    let mut output =
        String::from("; Grandiose verified .grbc AOT\nsource_filename = \"grandiose.grbc\"\n\n");
    for (function_id, function) in artifact.functions.iter().enumerate() {
        emit_function(&mut output, artifact, function_id as u32, function)?;
        output.push('\n');
    }
    let entry_function = artifact
        .functions
        .get(entry as usize)
        .expect("the verifier checked entry_function");
    let arguments = entry_function
        .params
        .iter()
        .map(|ty| {
            Ok(format!(
                "{} zeroinitializer",
                llvm_type(artifact, entry, *ty)?
            ))
        })
        .collect::<Result<Vec<_>, ArtifactLlvmError>>()?
        .join(", ");
    output.push_str("define i32 @main() {\nentry:\n");
    if llvm_type(artifact, entry, entry_function.return_type)? == "void" {
        output.push_str(&format!("  call void @grbc_fn_{entry}({arguments})\n"));
    } else {
        output.push_str(&format!(
            "  %entry = call {} @grbc_fn_{entry}({arguments})\n",
            llvm_type(artifact, entry, entry_function.return_type)?
        ));
    }
    output.push_str("  ret i32 0\n}\n");
    Ok(output)
}

fn emit_function(
    output: &mut String,
    artifact: &Artifact,
    function_id: u32,
    function: &Function,
) -> Result<(), ArtifactLlvmError> {
    if function.receiver_mode.is_some() || !function.outward_protocols.is_empty() {
        return Err(unsupported(function_id, 0, "receiver/effect function"));
    }
    let result = llvm_type(artifact, function_id, function.return_type)?;
    let parameters = function
        .params
        .iter()
        .enumerate()
        .map(|(index, ty)| {
            Ok(format!(
                "{} %arg{index}",
                llvm_type(artifact, function_id, *ty)?
            ))
        })
        .collect::<Result<Vec<_>, ArtifactLlvmError>>()?
        .join(", ");
    output.push_str(&format!(
        "define {result} @grbc_fn_{function_id}({parameters}) {{\nentry:\n"
    ));

    // G1 registers can be assigned independently on branch arms and then read
    // after their join.  Entry-block scalar slots preserve that virtual-register
    // semantics without fabricating phi ownership at this artifact boundary;
    // LLVM's O3 mem2reg pass can eliminate the trivial allocas afterwards.
    let register_types = function
        .register_types
        .iter()
        .copied()
        .map(|ty| llvm_type(artifact, function_id, ty))
        .collect::<Result<Vec<_>, _>>()?;
    for (register, llvm_ty) in register_types.iter().enumerate() {
        if llvm_ty != "void" {
            output.push_str(&format!("  %slot{register} = alloca {llvm_ty}\n"));
        }
    }
    for (index, ty) in function.params.iter().enumerate() {
        // The verifier establishes this positional ABI; still refuse a type
        // that this narrow backend does not understand.
        let llvm_ty = llvm_type(artifact, function_id, *ty)?;
        if llvm_ty != "void" {
            output.push_str(&format!(
                "  store {llvm_ty} %arg{index}, ptr %slot{}\n",
                index + 1
            ));
        }
    }
    output.push_str("  br label %bb0\n");
    let start = function.code_start as usize;
    let end = start + function.code_len as usize;
    let mut temporary = 0;
    for (offset, instruction) in artifact.code[start..end].iter().enumerate() {
        let instruction_id = offset as u32;
        output.push_str(&format!("bb{instruction_id}:\n"));
        match instruction {
            // This subset admits only plain scalar/value aggregates, so their
            // ownership bookkeeping has no native destructor or allocation to
            // perform. The verifier has already validated the consuming use.
            Instruction::Nop | Instruction::Drop { .. } | Instruction::Deconstruct { .. } => {
                emit_fallthrough(output, function, function_id, instruction_id)?;
            }
            Instruction::Const { dst, constant } => {
                let constant = artifact
                    .constants
                    .get(*constant as usize)
                    .ok_or_else(|| unsupported(function_id, instruction_id, "invalid constant"))?;
                let ty = *function
                    .register_types
                    .get(*dst as usize)
                    .ok_or_else(|| unsupported(function_id, instruction_id, "invalid register"))?;
                emit_store(
                    output,
                    &register_types,
                    function_id,
                    instruction_id,
                    *dst,
                    &llvm_constant(artifact, function_id, ty, constant)?,
                )?;
                emit_fallthrough(output, function, function_id, instruction_id)?;
            }
            Instruction::Move { dst, src } | Instruction::Copy { dst, src } => {
                let value = emit_load(
                    output,
                    &register_types,
                    function_id,
                    instruction_id,
                    *src,
                    &mut temporary,
                )?;
                emit_store(
                    output,
                    &register_types,
                    function_id,
                    instruction_id,
                    *dst,
                    &value,
                )?;
                emit_fallthrough(output, function, function_id, instruction_id)?;
            }
            Instruction::Primitive { dst, op, args } => {
                let ty = *function
                    .register_types
                    .get(*dst as usize)
                    .ok_or_else(|| unsupported(function_id, instruction_id, "invalid register"))?;
                let llvm_ty = llvm_type(artifact, function_id, ty)?;
                let args = args
                    .iter()
                    .map(|register_id| {
                        emit_load(
                            output,
                            &register_types,
                            function_id,
                            instruction_id,
                            *register_id,
                            &mut temporary,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let name = format!("%v{temporary}");
                temporary += 1;
                let operation = scalar_primitive(*op, &llvm_ty, &args).ok_or(
                    ArtifactLlvmError::UnsupportedPrimitive {
                        function: function_id,
                        instruction: instruction_id,
                        primitive: *op,
                    },
                )?;
                output.push_str(&format!("  {name} = {operation}\n"));
                emit_store(
                    output,
                    &register_types,
                    function_id,
                    instruction_id,
                    *dst,
                    &name,
                )?;
                emit_fallthrough(output, function, function_id, instruction_id)?;
            }
            Instruction::Return { src } => match (result.as_str(), src) {
                ("void", _) => output.push_str("  ret void\n"),
                (_, Some(src)) => {
                    let value = emit_load(
                        output,
                        &register_types,
                        function_id,
                        instruction_id,
                        *src,
                        &mut temporary,
                    )?;
                    output.push_str(&format!("  ret {result} {value}\n"));
                }
                _ => return Err(unsupported(function_id, instruction_id, "return shape")),
            },
            Instruction::Construct {
                dst,
                ty,
                variant,
                fields,
            } => {
                if variant.is_some() {
                    return Err(unsupported(function_id, instruction_id, "enum construct"));
                }
                let destination_ty = *function
                    .register_types
                    .get(*dst as usize)
                    .ok_or_else(|| unsupported(function_id, instruction_id, "invalid register"))?;
                if destination_ty != *ty {
                    return Err(unsupported(
                        function_id,
                        instruction_id,
                        "construct destination type",
                    ));
                }
                let field_types = aggregate_fields(artifact, function_id, *ty)?;
                if field_types.len() != fields.len() {
                    return Err(unsupported(function_id, instruction_id, "construct arity"));
                }
                let aggregate_ty =
                    register_type(&register_types, function_id, instruction_id, *dst)?;
                let mut value = "undef".to_owned();
                for (field, (register, field_ty)) in fields.iter().zip(field_types).enumerate() {
                    let source_ty =
                        *function
                            .register_types
                            .get(*register as usize)
                            .ok_or_else(|| {
                                unsupported(function_id, instruction_id, "invalid register")
                            })?;
                    if source_ty != field_ty {
                        return Err(unsupported(
                            function_id,
                            instruction_id,
                            "construct field type",
                        ));
                    }
                    let field_value = emit_load(
                        output,
                        &register_types,
                        function_id,
                        instruction_id,
                        *register,
                        &mut temporary,
                    )?;
                    let name = format!("%v{temporary}");
                    temporary += 1;
                    output.push_str(&format!(
                        "  {name} = insertvalue {aggregate_ty} {value}, {} {field_value}, {field}\n",
                        llvm_type(artifact, function_id, field_ty)?,
                    ));
                    value = name;
                }
                emit_store(
                    output,
                    &register_types,
                    function_id,
                    instruction_id,
                    *dst,
                    &value,
                )?;
                emit_fallthrough(output, function, function_id, instruction_id)?;
            }
            Instruction::ProjectMove { dst, src, field }
            | Instruction::ProjectCopy { dst, src, field } => {
                let source_ty = *function
                    .register_types
                    .get(*src as usize)
                    .ok_or_else(|| unsupported(function_id, instruction_id, "invalid register"))?;
                let field_types = aggregate_fields(artifact, function_id, source_ty)?;
                let field_ty = *field_types
                    .get(*field as usize)
                    .ok_or_else(|| unsupported(function_id, instruction_id, "aggregate field"))?;
                let destination_ty = *function
                    .register_types
                    .get(*dst as usize)
                    .ok_or_else(|| unsupported(function_id, instruction_id, "invalid register"))?;
                if destination_ty != field_ty {
                    return Err(unsupported(
                        function_id,
                        instruction_id,
                        "projection destination type",
                    ));
                }
                let aggregate_ty =
                    register_type(&register_types, function_id, instruction_id, *src)?;
                let aggregate = emit_load(
                    output,
                    &register_types,
                    function_id,
                    instruction_id,
                    *src,
                    &mut temporary,
                )?;
                let name = format!("%v{temporary}");
                temporary += 1;
                output.push_str(&format!(
                    "  {name} = extractvalue {aggregate_ty} {aggregate}, {field}\n"
                ));
                emit_store(
                    output,
                    &register_types,
                    function_id,
                    instruction_id,
                    *dst,
                    &name,
                )?;
                emit_fallthrough(output, function, function_id, instruction_id)?;
            }
            Instruction::Jump { target } => {
                check_target(function, function_id, instruction_id, *target)?;
                output.push_str(&format!("  br label %bb{target}\n"));
            }
            Instruction::Switch {
                discr,
                cases,
                otherwise,
            } => {
                let discr_ty = register_type(&register_types, function_id, instruction_id, *discr)?;
                if discr_ty == "void" {
                    return Err(unsupported(
                        function_id,
                        instruction_id,
                        "unit switch discriminator",
                    ));
                }
                check_target(function, function_id, instruction_id, *otherwise)?;
                let value = emit_load(
                    output,
                    &register_types,
                    function_id,
                    instruction_id,
                    *discr,
                    &mut temporary,
                )?;
                output.push_str(&format!(
                    "  switch {discr_ty} {value}, label %bb{otherwise} [\n"
                ));
                for (constant, target) in cases {
                    check_target(function, function_id, instruction_id, *target)?;
                    let constant = artifact.constants.get(*constant as usize).ok_or_else(|| {
                        unsupported(function_id, instruction_id, "invalid switch constant")
                    })?;
                    let ty = *function
                        .register_types
                        .get(*discr as usize)
                        .ok_or_else(|| {
                            unsupported(function_id, instruction_id, "invalid register")
                        })?;
                    output.push_str(&format!(
                        "    {discr_ty} {}, label %bb{target}\n",
                        llvm_constant(artifact, function_id, ty, constant)?
                    ));
                }
                output.push_str("  ]\n");
            }
            Instruction::Call {
                dst,
                function: callee,
                args,
            } => {
                let callee_function = artifact
                    .functions
                    .get(*callee as usize)
                    .ok_or_else(|| unsupported(function_id, instruction_id, "invalid callee"))?;
                if callee_function.receiver_mode.is_some()
                    || !callee_function.outward_protocols.is_empty()
                {
                    return Err(unsupported(
                        function_id,
                        instruction_id,
                        "receiver/effect call",
                    ));
                }
                if args.len() != callee_function.params.len() {
                    return Err(unsupported(function_id, instruction_id, "call arity"));
                }
                let mut arguments = Vec::with_capacity(args.len());
                for (index, register) in args.iter().enumerate() {
                    let ty = llvm_type(artifact, function_id, callee_function.params[index])?;
                    let value = emit_load(
                        output,
                        &register_types,
                        function_id,
                        instruction_id,
                        *register,
                        &mut temporary,
                    )?;
                    arguments.push(format!("{ty} {value}"));
                }
                let arguments = arguments.join(", ");
                let callee_result = llvm_type(artifact, function_id, callee_function.return_type)?;
                match (dst, callee_result.as_str()) {
                    (Some(_), "void") => {
                        return Err(unsupported(
                            function_id,
                            instruction_id,
                            "unit call destination",
                        ))
                    }
                    (Some(dst), _) => {
                        let name = format!("%v{temporary}");
                        temporary += 1;
                        output.push_str(&format!(
                            "  {name} = call {callee_result} @grbc_fn_{callee}({arguments})\n"
                        ));
                        emit_store(
                            output,
                            &register_types,
                            function_id,
                            instruction_id,
                            *dst,
                            &name,
                        )?;
                    }
                    (None, "void") => {
                        output.push_str(&format!("  call void @grbc_fn_{callee}({arguments})\n"))
                    }
                    (None, _) => {
                        return Err(unsupported(function_id, instruction_id, "call destination"))
                    }
                }
                emit_fallthrough(output, function, function_id, instruction_id)?;
            }
            instruction => {
                return Err(unsupported(
                    function_id,
                    instruction_id,
                    instruction_name(instruction),
                ))
            }
        }
    }
    output.push_str("}\n");
    Ok(())
}

fn register_type<'a>(
    register_types: &'a [String],
    function: u32,
    instruction: u32,
    register: u32,
) -> Result<&'a str, ArtifactLlvmError> {
    register_types
        .get(register as usize)
        .map(String::as_str)
        .ok_or_else(|| unsupported(function, instruction, "unavailable register"))
}

fn emit_load(
    output: &mut String,
    register_types: &[String],
    function: u32,
    instruction: u32,
    register: u32,
    temporary: &mut u32,
) -> Result<String, ArtifactLlvmError> {
    let ty = register_type(register_types, function, instruction, register)?;
    if ty == "void" {
        return Ok("zeroinitializer".into());
    }
    let name = format!("%v{temporary}");
    *temporary += 1;
    output.push_str(&format!("  {name} = load {ty}, ptr %slot{register}\n"));
    Ok(name)
}

fn emit_store(
    output: &mut String,
    register_types: &[String],
    function: u32,
    instruction: u32,
    register: u32,
    value: &str,
) -> Result<(), ArtifactLlvmError> {
    let ty = register_type(register_types, function, instruction, register)?;
    if ty != "void" {
        output.push_str(&format!("  store {ty} {value}, ptr %slot{register}\n"));
    }
    Ok(())
}

fn emit_fallthrough(
    output: &mut String,
    function: &Function,
    function_id: u32,
    instruction: u32,
) -> Result<(), ArtifactLlvmError> {
    let target = instruction
        .checked_add(1)
        .filter(|target| *target < function.code_len)
        .ok_or_else(|| unsupported(function_id, instruction, "function fallthrough"))?;
    output.push_str(&format!("  br label %bb{target}\n"));
    Ok(())
}

fn check_target(
    function: &Function,
    function_id: u32,
    instruction: u32,
    target: u32,
) -> Result<(), ArtifactLlvmError> {
    (target < function.code_len)
        .then_some(())
        .ok_or_else(|| unsupported(function_id, instruction, "invalid branch target"))
}

fn unsupported(function: u32, instruction: u32, opcode: &'static str) -> ArtifactLlvmError {
    ArtifactLlvmError::UnsupportedInstruction {
        function,
        instruction,
        opcode,
    }
}

fn llvm_type(artifact: &Artifact, function: u32, ty: TypeId) -> Result<String, ArtifactLlvmError> {
    match artifact.types.get(ty as usize).map(Type::representation) {
        Some(Type::Unit) => Ok("void".into()),
        Some(Type::U8 | Type::I8) => Ok("i8".into()),
        Some(Type::U16 | Type::I16) => Ok("i16".into()),
        Some(Type::U32 | Type::I32 | Type::Char) => Ok("i32".into()),
        Some(Type::U64 | Type::I64 | Type::Usize | Type::Isize) => Ok("i64".into()),
        Some(Type::U128 | Type::I128) => Ok("i128".into()),
        Some(Type::F32) => Ok("float".into()),
        Some(Type::F64) => Ok("double".into()),
        Some(Type::Tuple { fields, .. }) => llvm_aggregate_type(artifact, function, fields),
        Some(Type::Struct { fields, .. }) => llvm_aggregate_type(
            artifact,
            function,
            &fields.iter().map(|field| field.ty).collect::<Vec<_>>(),
        ),
        _ => Err(ArtifactLlvmError::UnsupportedType { function, ty }),
    }
}

fn llvm_aggregate_type(
    artifact: &Artifact,
    function: u32,
    fields: &[TypeId],
) -> Result<String, ArtifactLlvmError> {
    let fields = fields
        .iter()
        .map(|field| llvm_type(artifact, function, *field))
        .collect::<Result<Vec<_>, _>>()?;
    if fields.iter().any(|field| field == "void") {
        return Err(ArtifactLlvmError::UnsupportedType { function, ty: UNIT });
    }
    Ok(format!("{{ {} }}", fields.join(", ")))
}

fn aggregate_fields(
    artifact: &Artifact,
    function: u32,
    ty: TypeId,
) -> Result<Vec<TypeId>, ArtifactLlvmError> {
    match artifact.types.get(ty as usize).map(Type::representation) {
        Some(Type::Tuple { fields, .. }) => Ok(fields.clone()),
        Some(Type::Struct { fields, .. }) => Ok(fields.iter().map(|field| field.ty).collect()),
        _ => Err(ArtifactLlvmError::UnsupportedType { function, ty }),
    }
}

fn llvm_constant(
    _artifact: &Artifact,
    function: u32,
    ty: TypeId,
    constant: &Constant,
) -> Result<String, ArtifactLlvmError> {
    let value = match constant {
        Constant::Unit if ty == UNIT => "zeroinitializer".into(),
        Constant::U8(value) => value.to_string(),
        Constant::U16(value) => value.to_string(),
        Constant::U32(value) => value.to_string(),
        Constant::U64(value) => value.to_string(),
        Constant::U128(value) => value.to_string(),
        Constant::I8(value) => value.to_string(),
        Constant::I16(value) => value.to_string(),
        Constant::I32(value) => value.to_string(),
        Constant::I64(value) => value.to_string(),
        Constant::I128(value) => value.to_string(),
        Constant::Usize(value) => value.to_string(),
        Constant::Isize(value) => value.to_string(),
        Constant::Char(value) => (*value as u32).to_string(),
        Constant::F32(value) => format!("{value:e}"),
        Constant::F64(value) => format!("{value:e}"),
        _ => return Err(ArtifactLlvmError::UnsupportedType { function, ty }),
    };
    Ok(value)
}

fn scalar_primitive(op: Primitive, ty: &str, args: &[String]) -> Option<String> {
    let binary =
        |opcode| (args.len() == 2).then(|| format!("{opcode} {ty} {}, {}", args[0], args[1]));
    match op {
        Primitive::IntWrappingAdd => binary("add"),
        Primitive::IntWrappingSub => binary("sub"),
        Primitive::IntWrappingMul => binary("mul"),
        Primitive::IntBitAnd => binary("and"),
        Primitive::IntBitOr => binary("or"),
        Primitive::IntBitXor => binary("xor"),
        Primitive::IntBitNot if args.len() == 1 => Some(format!("xor {ty} {}, -1", args[0])),
        _ => None,
    }
}

fn instruction_name(instruction: &Instruction) -> &'static str {
    match instruction {
        Instruction::Jump { .. } => "Jump",
        Instruction::Switch { .. } => "Switch",
        Instruction::Call { .. } => "Call",
        Instruction::TailCall { .. } => "TailCall",
        Instruction::BorrowShared { .. } => "BorrowShared",
        Instruction::BorrowUnique { .. } => "BorrowUnique",
        Instruction::Construct { .. } => "Construct",
        Instruction::Abort { .. } => "Abort",
        Instruction::Unreachable => "Unreachable",
        _ => "non-scalar instruction",
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, process::Command};

    use grandiose_vm::bytecode::Field;
    use grandiose_vm::{
        verify::with_generated_cleanup_plans, Artifact, Constant, Function, Instruction, Primitive,
        Type, I64, UNIT,
    };

    use super::*;

    fn scalar_program() -> Artifact {
        let mut artifact = with_generated_cleanup_plans(Artifact {
            entry_function: Some(0),
            constants: vec![
                Constant::Unit,
                Constant::I64(20),
                Constant::I64(22),
                Constant::I64(42),
                Constant::I64(0),
            ],
            functions: vec![
                Function {
                    name: "main".into(),
                    flags: 0,
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, UNIT],
                    code_start: 0,
                    code_len: 3,
                    label_slot_count: 0,
                },
                Function {
                    name: "scalar".into(),
                    flags: 0,
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, I64, I64, UNIT],
                    code_start: 3,
                    code_len: 8,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Call {
                    dst: None,
                    function: 1,
                    args: vec![],
                },
                Instruction::Return { src: Some(1) },
                Instruction::Const {
                    dst: 1,
                    constant: 1,
                },
                Instruction::Const {
                    dst: 2,
                    constant: 2,
                },
                Instruction::Primitive {
                    dst: 3,
                    op: Primitive::IntWrappingAdd,
                    args: vec![1, 2],
                },
                Instruction::Const {
                    dst: 4,
                    constant: 0,
                },
                Instruction::Switch {
                    discr: 3,
                    cases: vec![(3, 5)],
                    otherwise: 6,
                },
                Instruction::Jump { target: 7 },
                Instruction::Jump { target: 7 },
                Instruction::Return { src: Some(4) },
            ],
            ..Artifact::default()
        })
        .unwrap();
        artifact.canonicalize_constants();
        artifact
    }

    #[test]
    fn verified_scalar_grbc_emits_parseable_llvm_without_vm_execution() {
        let bytes = scalar_program().encode();
        let ir = emit_artifact_llvm_ir(&bytes).unwrap();
        assert!(ir.contains("define void @grbc_fn_1()"));
        assert!(ir.contains("call void @grbc_fn_1()"));
        assert!(ir.contains("add i64"));
        assert!(ir.contains("switch i64"));
        assert!(ir.contains("br label %bb7"));
        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("scalar.ll");
        let object = directory.path().join("scalar.o");
        fs::write(&source, ir).unwrap();
        let status = Command::new("clang")
            .args(["-x", "ir", "-c"])
            .arg(&source)
            .arg("-o")
            .arg(&object)
            .status()
            .unwrap();
        assert!(status.success());
        assert!(object.is_file());
    }

    #[test]
    fn verified_unsupported_instruction_fails_closed() {
        let mut artifact = scalar_program();
        artifact.code[5] = Instruction::TailCall {
            function: 1,
            args: vec![],
        };
        // Rebuild verifier cleanups after mutating the hand-built artifact.
        let artifact = with_generated_cleanup_plans(artifact).unwrap();
        let error = emit_artifact_llvm_ir(&artifact.encode()).unwrap_err();
        assert!(matches!(
            error,
            ArtifactLlvmError::UnsupportedInstruction {
                opcode: "TailCall",
                ..
            }
        ));
    }

    #[test]
    fn verified_tuple_and_nominal_values_emit_parseable_llvm_without_vm_execution() {
        let tuple = 19;
        let record = 20;
        let mut artifact = Artifact {
            entry_function: Some(0),
            constants: vec![Constant::Unit, Constant::I64(20), Constant::I64(22)],
            functions: vec![
                Function {
                    name: "main".into(),
                    flags: 0,
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, UNIT, I64],
                    code_start: 0,
                    code_len: 4,
                    label_slot_count: 0,
                },
                Function {
                    name: "aggregate".into(),
                    flags: 0,
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, I64, tuple, record, I64],
                    code_start: 4,
                    code_len: 8,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Call {
                    dst: Some(2),
                    function: 1,
                    args: vec![],
                },
                Instruction::Drop { register: 2 },
                Instruction::Return { src: Some(1) },
                Instruction::Const {
                    dst: 1,
                    constant: 1,
                },
                Instruction::Const {
                    dst: 2,
                    constant: 2,
                },
                Instruction::Construct {
                    dst: 3,
                    ty: tuple,
                    variant: None,
                    fields: vec![1, 2],
                },
                Instruction::ProjectCopy {
                    dst: 5,
                    src: 3,
                    field: 1,
                },
                Instruction::ProjectMove {
                    dst: 1,
                    src: 3,
                    field: 0,
                },
                Instruction::Construct {
                    dst: 4,
                    ty: record,
                    variant: None,
                    fields: vec![1, 5],
                },
                Instruction::ProjectMove {
                    dst: 5,
                    src: 4,
                    field: 0,
                },
                Instruction::Return { src: Some(5) },
            ],
            ..Artifact::default()
        };
        assert_eq!(artifact.types.len(), tuple as usize);
        artifact.types.push(Type::Tuple {
            fields: vec![I64, I64],
            copy: true,
        });
        artifact.types.push(Type::Struct {
            name: "Pair".into(),
            fields: vec![
                Field {
                    name: "left".into(),
                    ty: I64,
                },
                Field {
                    name: "right".into(),
                    ty: I64,
                },
            ],
            copy: true,
        });
        let artifact = with_generated_cleanup_plans(artifact).unwrap();
        let ir = emit_artifact_llvm_ir(&artifact.encode()).unwrap();
        assert!(ir.contains("insertvalue { i64, i64 }"));
        assert!(ir.contains("extractvalue { i64, i64 }"));
        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("aggregate.ll");
        let object = directory.path().join("aggregate.o");
        fs::write(&source, ir).unwrap();
        let status = Command::new("clang")
            .args(["-x", "ir", "-c"])
            .arg(&source)
            .arg("-o")
            .arg(&object)
            .status()
            .unwrap();
        assert!(status.success());
        assert!(object.is_file());
    }
}
