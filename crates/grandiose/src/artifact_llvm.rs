//! Fail-closed LLVM lowering for the first scalar `.grbc` AOT slice.
//!
//! This is intentionally an artifact boundary, not a second source compiler:
//! callers hand it encoded bytecode, which is decoded and verified before a
//! single LLVM instruction is emitted.  It does not construct a [`Vm`] or use
//! any interpreter entry point.  The supported surface is deliberately small
//! (straight-line direct scalar functions); every other valid G1 instruction
//! remains an explicit lowering error until it has a native ABI.

use std::{collections::BTreeMap, error::Error, fmt};

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
    let mut output = String::from(
        "; Grandiose verified .grbc scalar AOT\nsource_filename = \"grandiose.grbc\"\n\n",
    );
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

    let mut registers = BTreeMap::new();
    for (index, ty) in function.params.iter().enumerate() {
        registers.insert((index + 1) as u32, format!("%arg{index}"));
        // The verifier establishes this positional ABI; still refuse a type
        // that this narrow backend does not understand.
        llvm_type(artifact, function_id, *ty)?;
    }
    let start = function.code_start as usize;
    let end = start + function.code_len as usize;
    for (offset, instruction) in artifact.code[start..end].iter().enumerate() {
        let instruction_id = offset as u32;
        match instruction {
            Instruction::Nop | Instruction::Drop { .. } => {}
            Instruction::Const { dst, constant } => {
                let constant = artifact
                    .constants
                    .get(*constant as usize)
                    .ok_or_else(|| unsupported(function_id, instruction_id, "invalid constant"))?;
                let ty = *function
                    .register_types
                    .get(*dst as usize)
                    .ok_or_else(|| unsupported(function_id, instruction_id, "invalid register"))?;
                registers.insert(*dst, llvm_constant(artifact, function_id, ty, constant)?);
            }
            Instruction::Move { dst, src } | Instruction::Copy { dst, src } => {
                let value = register(&registers, function_id, instruction_id, *src)?;
                registers.insert(*dst, value.to_owned());
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
                        register(&registers, function_id, instruction_id, *register_id)
                            .map(str::to_owned)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let name = format!("%r{dst}");
                let operation = scalar_primitive(*op, &llvm_ty, &args).ok_or(
                    ArtifactLlvmError::UnsupportedPrimitive {
                        function: function_id,
                        instruction: instruction_id,
                        primitive: *op,
                    },
                )?;
                output.push_str(&format!("  {name} = {operation}\n"));
                registers.insert(*dst, name);
            }
            Instruction::Return { src } => match (result, src) {
                ("void", _) => output.push_str("  ret void\n"),
                (_, Some(src)) => output.push_str(&format!(
                    "  ret {result} {}\n",
                    register(&registers, function_id, instruction_id, *src)?
                )),
                _ => return Err(unsupported(function_id, instruction_id, "return shape")),
            },
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

fn register<'a>(
    registers: &'a BTreeMap<u32, String>,
    function: u32,
    instruction: u32,
    register: u32,
) -> Result<&'a str, ArtifactLlvmError> {
    registers
        .get(&register)
        .map(String::as_str)
        .ok_or_else(|| unsupported(function, instruction, "unavailable register"))
}

fn unsupported(function: u32, instruction: u32, opcode: &'static str) -> ArtifactLlvmError {
    ArtifactLlvmError::UnsupportedInstruction {
        function,
        instruction,
        opcode,
    }
}

fn llvm_type(
    artifact: &Artifact,
    function: u32,
    ty: TypeId,
) -> Result<&'static str, ArtifactLlvmError> {
    match artifact.types.get(ty as usize).map(Type::representation) {
        Some(Type::Unit) => Ok("void"),
        Some(Type::U8 | Type::I8) => Ok("i8"),
        Some(Type::U16 | Type::I16) => Ok("i16"),
        Some(Type::U32 | Type::I32 | Type::Char) => Ok("i32"),
        Some(Type::U64 | Type::I64 | Type::Usize | Type::Isize) => Ok("i64"),
        Some(Type::U128 | Type::I128) => Ok("i128"),
        Some(Type::F32) => Ok("float"),
        Some(Type::F64) => Ok("double"),
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

    use grandiose_vm::{
        verify::with_generated_cleanup_plans, Artifact, Constant, Function, Instruction, Primitive,
        I64, UNIT,
    };

    use super::*;

    fn scalar_program() -> Artifact {
        with_generated_cleanup_plans(Artifact {
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
                    register_types: vec![UNIT, UNIT],
                    code_start: 0,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    name: "scalar".into(),
                    flags: 0,
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, I64, I64],
                    code_start: 2,
                    code_len: 4,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
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
                Instruction::Return { src: Some(3) },
            ],
            ..Artifact::default()
        })
        .unwrap()
    }

    #[test]
    fn verified_scalar_grbc_emits_parseable_llvm_without_vm_execution() {
        let bytes = scalar_program().encode();
        let ir = emit_artifact_llvm_ir(&bytes).unwrap();
        assert!(ir.contains("define i64 @grbc_fn_1()"));
        assert!(ir.contains("add i64 20, 22"));
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
        artifact.code.insert(5, Instruction::Jump { target: 4 });
        artifact.functions[1].code_len = 5;
        // Rebuild verifier cleanups after mutating the hand-built artifact.
        let artifact = with_generated_cleanup_plans(artifact).unwrap();
        let error = emit_artifact_llvm_ir(&artifact.encode()).unwrap_err();
        assert!(matches!(
            error,
            ArtifactLlvmError::UnsupportedInstruction { opcode: "Jump", .. }
        ));
    }
}
