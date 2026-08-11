//! Fail-closed LLVM lowering for the first scalar-and-value-aggregate `.grbc` AOT slice.
//!
//! This is intentionally an artifact boundary, not a second source compiler:
//! callers hand it encoded bytecode, which is decoded and verified before a
//! single LLVM instruction is emitted.  It does not construct a [`Vm`] or use
//! any interpreter entry point.  The supported surface is deliberately small
//! (direct scalar/value-aggregate functions with ordinary control flow); every other valid G1 instruction
//! remains an explicit lowering error until it has a native ABI.

use std::{collections::BTreeSet, error::Error, fmt};

use grandiose_vm::{
    load_verified, verify::VerifiedArtifact, Artifact, Constant, Function, Instruction, Primitive,
    Type, TypeId, BYTES, TEXT, UNIT,
};
use grandiose_vm::bytecode::{Import, Signature};

use crate::{
    llvm_backend::default_target_triple,
    llvm_runtime_abi::{pointer_width_for_target, runtime_fault_declaration},
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
    // Artifact lowering has no runtime-consuming opcode yet.  It still emits
    // the canonical declaration so all LLVM producers agree on the exact ABI
    // which future, independently verified slices must use.  The declaration
    // alone neither calls the runtime nor authorizes a VM fallback.
    let target_triple = default_target_triple();
    let pointer_width = pointer_width_for_target(&target_triple);
    let mut output =
        String::from("; Grandiose verified .grbc AOT\nsource_filename = \"grandiose.grbc\"\n");
    output.push_str(&runtime_fault_declaration(pointer_width));
    emit_host_import_declarations(&mut output, artifact);
    emit_runtime_literals(&mut output, artifact, pointer_width);
    output.push_str("\n\n");
    // An artifact can retain helper functions which are unreachable from its
    // entry point.  They have no native observable behavior, and rejecting a
    // supported program merely because an unused helper needs a later ABI
    // slice makes this boundary less useful than necessary.  Emit the exact
    // static closure of entry instead.  Every function reference we can
    // represent is followed conservatively; dynamic calls remain rejected by
    // `emit_function`, so this never makes an executable depend on a VM
    // fallback or an undefined native symbol.
    let reachable = reachable_functions(artifact, entry)?;
    for (function_id, function) in artifact.functions.iter().enumerate() {
        if reachable.contains(&(function_id as u32)) {
            emit_function(&mut output, artifact, function_id as u32, function)?;
            output.push('\n');
        }
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
    if artifact
        .imports
        .iter()
        .any(|import| matches!(frozen_host_import(artifact, import), Some(FrozenHostImport::ProcessArgsGet)))
    {
        output.push_str("define i32 @main(i32 %argc, ptr %argv) {\nentry:\n  call void @g1_host_process_init(i32 %argc, ptr %argv)\n");
    } else {
        output.push_str("define i32 @main() {\nentry:\n");
    }
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

fn reachable_functions(
    artifact: &Artifact,
    entry: u32,
) -> Result<BTreeSet<u32>, ArtifactLlvmError> {
    let mut reachable = BTreeSet::new();
    let mut pending = vec![entry];
    while let Some(function_id) = pending.pop() {
        if !reachable.insert(function_id) {
            continue;
        }
        let function = artifact
            .functions
            .get(function_id as usize)
            .ok_or_else(|| unsupported(function_id, 0, "invalid function"))?;
        let start = function.code_start as usize;
        let end = start
            .checked_add(function.code_len as usize)
            .ok_or_else(|| unsupported(function_id, 0, "invalid function code range"))?;
        let code = artifact
            .code
            .get(start..end)
            .ok_or_else(|| unsupported(function_id, 0, "invalid function code range"))?;
        for instruction in code {
            match instruction {
                Instruction::Call { function, .. }
                | Instruction::TailCall { function, .. }
                | Instruction::CallKnownReceiver { function, .. }
                | Instruction::TailCallKnownReceiver { function, .. }
                | Instruction::MakeCallable { function, .. } => pending.push(*function),
                Instruction::MakeHandlerShared { functions, .. } => {
                    pending.extend(functions.iter().copied())
                }
                _ => {}
            }
        }
    }
    if let Some(invalid) = reachable
        .iter()
        .copied()
        .find(|function_id| *function_id as usize >= artifact.functions.len())
    {
        return Err(unsupported(invalid, 0, "invalid referenced function"));
    }
    Ok(reachable)
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
                let constant_id = *constant;
                let constant = artifact
                    .constants
                    .get(constant_id as usize)
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
                    &llvm_constant(artifact, function_id, ty, constant_id, constant)?,
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
                let field_types = match variant {
                    Some(variant) => enum_variant_fields(artifact, function_id, *ty, *variant)?,
                    None => aggregate_fields(artifact, function_id, *ty)?,
                };
                if field_types.len() != fields.len() {
                    return Err(unsupported(function_id, instruction_id, "construct arity"));
                }
                let aggregate_ty = register_type(&register_types, function_id, instruction_id, *dst)?;
                let mut value = "undef".to_owned();
                if let Some(variant) = variant {
                    let name = format!("%v{temporary}");
                    temporary += 1;
                    // The only enum ABI admitted by this first slice has no
                    // payload fields: its complete native value is an i32 tag.
                    // `enum_variant_fields` enforces that before this point.
                    output.push_str(&format!(
                        "  {name} = insertvalue {aggregate_ty} {value}, i32 {variant}, 0\n"
                    ));
                    value = name;
                }
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
                    // Unit has no LLVM value representation. A payload made
                    // exclusively of unit fields is nevertheless observable
                    // only through its enum tag, so the compact tag-only enum
                    // ABI intentionally omits those zero-sized fields.
                    if variant.is_some() && field_ty == UNIT {
                        continue;
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
                let destination_ty = *function
                    .register_types
                    .get(*dst as usize)
                    .ok_or_else(|| unsupported(function_id, instruction_id, "invalid register"))?;
                // Once a preceding tag check has selected a unit-only enum
                // variant, projecting its unit payload has no runtime bits to
                // extract. The verifier still owns the path-sensitive variant
                // proof; this ABI slice merely preserves the resulting Unit.
                if destination_ty == UNIT
                    && enum_has_unit_field(artifact, source_ty, *field)
                {
                    emit_fallthrough(output, function, function_id, instruction_id)?;
                    continue;
                }
                let field_types = aggregate_fields(artifact, function_id, source_ty)?;
                let field_ty = *field_types
                    .get(*field as usize)
                    .ok_or_else(|| unsupported(function_id, instruction_id, "aggregate field"))?;
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
            Instruction::EnumTag { dst, src } => {
                let source_ty = *function
                    .register_types
                    .get(*src as usize)
                    .ok_or_else(|| unsupported(function_id, instruction_id, "invalid register"))?;
                enum_variant_fields_for_type(artifact, function_id, source_ty)?;
                let destination_ty = *function
                    .register_types
                    .get(*dst as usize)
                    .ok_or_else(|| unsupported(function_id, instruction_id, "invalid register"))?;
                if llvm_type(artifact, function_id, destination_ty)? != "i32" {
                    return Err(unsupported(function_id, instruction_id, "enum tag destination type"));
                }
                let aggregate_ty = register_type(&register_types, function_id, instruction_id, *src)?;
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
                    "  {name} = extractvalue {aggregate_ty} {aggregate}, 0\n"
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
                    let constant_id = *constant;
                    let constant = artifact.constants.get(constant_id as usize).ok_or_else(|| {
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
                        llvm_constant(artifact, function_id, ty, constant_id, constant)?
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
            Instruction::TailCall {
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
                        "receiver/effect tail call",
                    ));
                }
                if args.len() != callee_function.params.len() {
                    return Err(unsupported(function_id, instruction_id, "tail call arity"));
                }
                let callee_result = llvm_type(artifact, function_id, callee_function.return_type)?;
                if callee_result != result {
                    return Err(unsupported(function_id, instruction_id, "tail call result"));
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
                if result == "void" {
                    output.push_str(&format!("  tail call void @grbc_fn_{callee}({arguments})\n"));
                    output.push_str("  ret void\n");
                } else {
                    let name = format!("%v{temporary}");
                    output.push_str(&format!(
                        "  {name} = tail call {result} @grbc_fn_{callee}({arguments})\n"
                    ));
                    output.push_str(&format!("  ret {result} {name}\n"));
                }
            }
            Instruction::HostCall { dst, import, args } => {
                emit_host_call(
                    output,
                    artifact,
                    &register_types,
                    function,
                    function_id,
                    instruction_id,
                    *dst,
                    *import,
                    args,
                    &mut temporary,
                )?;
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
        // This slice admits Text only as an immutable literal passed to the
        // host diagnostic ABI.  It is exactly the `G1Bytes *` representation
        // in native_host_runtime.c; Bytes and dynamic Text still have no
        // artifact AOT allocation/ownership ABI and remain rejected.
        Some(Type::Text | Type::Bytes) => Ok("ptr".into()),
        Some(Type::Array { element }) if *element == TEXT => Ok("ptr".into()),
        Some(Type::Tuple { fields, .. }) => llvm_aggregate_type(artifact, function, fields),
        Some(Type::Struct { fields, .. }) => llvm_aggregate_type(
            artifact,
            function,
            &fields.iter().map(|field| field.ty).collect::<Vec<_>>(),
        ),
        Some(Type::Enum { variants, .. }) if enum_has_only_unit_payloads(variants) => {
            // A fieldless (or unit-only) enum is represented solely by its
            // deterministic G1 variant index. Payloads with a runtime value
            // stay fail-closed until their full tagged-union ABI is specified.
            Ok("{ i32 }".into())
        }
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

fn enum_variant_fields(
    artifact: &Artifact,
    function: u32,
    ty: TypeId,
    variant: u32,
) -> Result<Vec<TypeId>, ArtifactLlvmError> {
    let variants = enum_variant_fields_for_type(artifact, function, ty)?;
    variants
        .get(variant as usize)
        .cloned()
        .ok_or(ArtifactLlvmError::UnsupportedType { function, ty })
}

/// Validate the intentionally narrow, tag-only enum ABI and return its
/// variant field lists (all empty). Keeping this separate makes `Construct`
/// and `EnumTag` agree on exactly the same native representation.
fn enum_variant_fields_for_type(
    artifact: &Artifact,
    function: u32,
    ty: TypeId,
) -> Result<Vec<Vec<TypeId>>, ArtifactLlvmError> {
    match artifact.types.get(ty as usize).map(Type::representation) {
        Some(Type::Enum { variants, .. }) if enum_has_only_unit_payloads(variants) => {
            Ok(variants
                .iter()
                .map(|variant| variant.fields.iter().map(|field| field.ty).collect())
                .collect())
        }
        _ => Err(ArtifactLlvmError::UnsupportedType { function, ty }),
    }
}

fn enum_has_only_unit_payloads(variants: &[grandiose_vm::bytecode::EnumVariant]) -> bool {
    variants
        .iter()
        .all(|variant| variant.fields.iter().all(|field| field.ty == UNIT))
}

fn enum_has_unit_field(artifact: &Artifact, ty: TypeId, field: u32) -> bool {
    match artifact.types.get(ty as usize).map(Type::representation) {
        Some(Type::Enum { variants, .. }) if enum_has_only_unit_payloads(variants) => variants
            .iter()
            .all(|variant| variant.fields.get(field as usize).is_some_and(|value| value.ty == UNIT)),
        _ => false,
    }
}

fn llvm_constant(
    _artifact: &Artifact,
    function: u32,
    ty: TypeId,
    constant_id: u32,
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
        Constant::Text(_) if ty == TEXT => format!("@g1.artifact.bytes.{constant_id}"),
        _ => return Err(ArtifactLlvmError::UnsupportedType { function, ty }),
    };
    Ok(value)
}

/// Emit the immutable `G1Bytes` literals used by the sole host-call ABI slice.
/// The layout is intentionally byte-for-byte the source LLVM backend's
/// `%g1.bytes`: signed reference count, target-width length, then data.  A
/// count of -1 makes the static literal immortal, which is the only ownership
/// behavior this artifact slice needs.
fn emit_runtime_literals(output: &mut String, artifact: &Artifact, pointer_width: u16) {
    let texts = artifact
        .constants
        .iter()
        .enumerate()
        .filter_map(|(index, constant)| match constant {
            Constant::Text(text) => Some((index, text.as_bytes())),
            _ => None,
        })
        .collect::<Vec<_>>();
    if texts.is_empty() {
        return;
    }
    output.push_str(&format!("\n%g1.bytes = type {{ i64, i{pointer_width}, [0 x i8] }}\n"));
    for (index, bytes) in texts {
        let escaped = bytes
            .iter()
            .map(|byte| format!("\\{byte:02X}"))
            .collect::<String>();
        output.push_str(&format!(
            "@g1.artifact.bytes.{index} = private constant {{ i64, i{pointer_width}, [{} x i8] }} {{ i64 -1, i{pointer_width} {}, [{} x i8] c\"{escaped}\" }}, align 8\n",
            bytes.len(),
            bytes.len(),
            bytes.len(),
        ));
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum FrozenHostImport {
    ProcessArgsGet,
    FsRead,
    FsWrite,
    DiagnosticWrite,
}

/// Recognize exactly the four G1 imports emitted by the self-host production
/// manifest.  The artifact's spelling, full signature, and trap bit are all
/// part of this ABI; a lookalike import is never given a native symbol.
fn frozen_host_import(artifact: &Artifact, import: &Import) -> Option<FrozenHostImport> {
    let plain = |params, result| {
        import.signature
            == Signature { params, result, outward_protocols: vec![] }
            && import.may_trap
    };
    if import.capability == "process.args"
        && import.symbol == "get"
        && plain(vec![], import.signature.result)
        && matches!(
            artifact.types.get(import.signature.result as usize).map(Type::representation),
            Some(Type::Array { element }) if *element == TEXT
        )
    {
        Some(FrozenHostImport::ProcessArgsGet)
    } else if import.capability == "fs.read"
        && import.symbol == "read"
        && plain(vec![TEXT], BYTES)
    {
        Some(FrozenHostImport::FsRead)
    } else if import.capability == "fs.write"
        && import.symbol == "write"
        && plain(vec![TEXT, BYTES], UNIT)
    {
        Some(FrozenHostImport::FsWrite)
    } else if import.capability == "diagnostic"
        && import.symbol == "write"
        && plain(vec![TEXT], UNIT)
    {
        Some(FrozenHostImport::DiagnosticWrite)
    } else {
        None
    }
}

fn emit_host_import_declarations(output: &mut String, artifact: &Artifact) {
    let imports = artifact
        .imports
        .iter()
        .filter_map(|import| frozen_host_import(artifact, import))
        .collect::<BTreeSet<_>>();
    if imports.is_empty() {
        return;
    }
    output.push_str("\ndeclare void @g1_host_fault(i32) cold noreturn\n");
    for import in imports {
        match import {
            FrozenHostImport::ProcessArgsGet => output.push_str(
                "declare void @g1_host_process_init(i32, ptr)\ndeclare ptr @g1_host_process_args_get()\n",
            ),
            FrozenHostImport::FsRead => output.push_str("declare ptr @g1_host_fs_read(ptr)\n"),
            FrozenHostImport::FsWrite => output.push_str("declare i32 @g1_host_fs_write(ptr, ptr)\n"),
            FrozenHostImport::DiagnosticWrite => {
                output.push_str("declare i32 @g1_host_diagnostic_write(ptr)\n")
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_host_call(
    output: &mut String,
    artifact: &Artifact,
    register_types: &[String],
    function: &Function,
    function_id: u32,
    instruction_id: u32,
    dst: Option<u32>,
    import: u32,
    args: &[u32],
    temporary: &mut u32,
) -> Result<(), ArtifactLlvmError> {
    let import = artifact
        .imports
        .get(import as usize)
        .ok_or_else(|| unsupported(function_id, instruction_id, "invalid host import"))?;
    let role = frozen_host_import(artifact, import)
        .ok_or_else(|| unsupported(function_id, instruction_id, "unsupported host import"))?;
    let mut argument = |index: usize, expected: TypeId, label: &'static str| {
        let register = *args
            .get(index)
            .ok_or_else(|| unsupported(function_id, instruction_id, label))?;
        let ty = *function
            .register_types
            .get(register as usize)
            .ok_or_else(|| unsupported(function_id, instruction_id, "invalid register"))?;
        if ty != expected {
            return Err(unsupported(function_id, instruction_id, label));
        }
        emit_load(output, register_types, function_id, instruction_id, register, temporary)
    };
    let destination = |expected: TypeId, label: &'static str| {
        let register = dst.ok_or_else(|| unsupported(function_id, instruction_id, label))?;
        let ty = *function
            .register_types
            .get(register as usize)
            .ok_or_else(|| unsupported(function_id, instruction_id, "invalid register"))?;
        (ty == expected)
            .then_some(register)
            .ok_or_else(|| unsupported(function_id, instruction_id, label))
    };
    let unit_destination = |label: &'static str| -> Result<(), ArtifactLlvmError> {
        if let Some(register) = dst {
            let ty = *function
                .register_types
                .get(register as usize)
                .ok_or_else(|| unsupported(function_id, instruction_id, "invalid register"))?;
            if ty != UNIT {
                return Err(unsupported(function_id, instruction_id, label));
            }
        }
        Ok(())
    };
    match role {
        FrozenHostImport::ProcessArgsGet => {
            if !args.is_empty() {
                return Err(unsupported(function_id, instruction_id, "process.args arity"));
            }
            let destination = destination(import.signature.result, "process.args result")?;
            let value = format!("%v{temporary}");
            *temporary += 1;
            output.push_str(&format!("  {value} = call ptr @g1_host_process_args_get()\n"));
            emit_host_fault_if_null(output, function_id, instruction_id, temporary, &value, 1);
            emit_store(output, register_types, function_id, instruction_id, destination, &value)
        }
        FrozenHostImport::FsRead => {
            if args.len() != 1 {
                return Err(unsupported(function_id, instruction_id, "fs.read arity"));
            }
            let path = argument(0, TEXT, "fs.read path type")?;
            let destination = destination(BYTES, "fs.read result")?;
            let value = format!("%v{temporary}");
            *temporary += 1;
            output.push_str(&format!("  {value} = call ptr @g1_host_fs_read(ptr {path})\n"));
            emit_host_fault_if_null(output, function_id, instruction_id, temporary, &value, 2);
            emit_store(output, register_types, function_id, instruction_id, destination, &value)
        }
        FrozenHostImport::FsWrite => {
            if args.len() != 2 {
                return Err(unsupported(function_id, instruction_id, "fs.write arity"));
            }
            let path = argument(0, TEXT, "fs.write path type")?;
            let bytes = argument(1, BYTES, "fs.write bytes type")?;
            unit_destination("fs.write destination type")?;
            emit_host_status_call(output, function_id, instruction_id, temporary,
                &format!("call i32 @g1_host_fs_write(ptr {path}, ptr {bytes})"), 3);
            Ok(())
        }
        FrozenHostImport::DiagnosticWrite => {
            if args.len() != 1 {
                return Err(unsupported(function_id, instruction_id, "diagnostic.write arity"));
            }
            let text = argument(0, TEXT, "diagnostic.write text type")?;
            unit_destination("diagnostic.write destination type")?;
            emit_host_status_call(output, function_id, instruction_id, temporary,
                &format!("call i32 @g1_host_diagnostic_write(ptr {text})"), 4);
            Ok(())
        }
    }
}

fn emit_host_fault_if_null(output: &mut String, function: u32, instruction: u32, temporary: &mut u32, value: &str, fault_code: u32) {
    let failed = format!("%v{temporary}");
    *temporary += 1;
    output.push_str(&format!("  {failed} = icmp eq ptr {value}, null\n"));
    emit_host_fault_branch(output, function, instruction, &failed, fault_code);
}

fn emit_host_status_call(output: &mut String, function: u32, instruction: u32, temporary: &mut u32, call: &str, fault_code: u32) {
    let status = format!("%v{temporary}");
    *temporary += 1;
    output.push_str(&format!("  {status} = {call}\n"));
    let failed = format!("%v{temporary}");
    *temporary += 1;
    output.push_str(&format!("  {failed} = icmp ne i32 {status}, 0\n"));
    emit_host_fault_branch(output, function, instruction, &failed, fault_code);
}

fn emit_host_fault_branch(output: &mut String, function: u32, instruction: u32, failed: &str, fault_code: u32) {
    let fault = format!("host.fault.{function}.{instruction}");
    let continuation = format!("host.cont.{function}.{instruction}");
    output.push_str(&format!(
        "  br i1 {failed}, label %{fault}, label %{continuation}\n{fault}:\n  call void @g1_host_fault(i32 {fault_code})\n  unreachable\n{continuation}:\n"
    ));
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

    use grandiose_vm::bytecode::{EnumVariant, Field, Import, Signature};
    use grandiose_vm::{
        verify::with_generated_cleanup_plans, Artifact, Constant, Function, Instruction, Primitive,
        Type, BYTES, I64, TEXT, U32, UNIT,
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
    fn verified_direct_tail_call_emits_llvm_without_vm_execution() {
        let mut artifact = scalar_program();
        artifact.code[5] = Instruction::TailCall {
            function: 1,
            args: vec![],
        };
        // Rebuild verifier cleanups after mutating the hand-built artifact.
        let artifact = with_generated_cleanup_plans(artifact).unwrap();
        let ir = emit_artifact_llvm_ir(&artifact.encode()).unwrap();
        assert!(ir.contains("tail call void @grbc_fn_1()"));
        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("tail.ll");
        let object = directory.path().join("tail.o");
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
    fn unreachable_unsupported_helpers_do_not_block_entry_closure_lowering() {
        let mut artifact = scalar_program();
        let dead_start = artifact.code.len() as u32;
        artifact.functions.push(Function {
            name: "dead_tail_helper".into(),
            flags: 0,
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT],
            code_start: dead_start,
            code_len: 1,
            label_slot_count: 0,
        });
        artifact.code.push(Instruction::TailCall {
            function: 0,
            args: vec![],
        });
        let artifact = with_generated_cleanup_plans(artifact).unwrap();
        let ir = emit_artifact_llvm_ir(&artifact.encode()).unwrap();
        assert!(ir.contains("define void @grbc_fn_0()"));
        assert!(ir.contains("define void @grbc_fn_1()"));
        assert!(!ir.contains("@grbc_fn_2"));
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

    #[test]
    fn verified_fieldless_enum_construct_and_tag_emit_parseable_llvm_without_vm_execution() {
        let choice = 19;
        let mut artifact = Artifact {
            entry_function: Some(0),
            constants: vec![],
            functions: vec![
                Function {
                    name: "main".into(),
                    flags: 0,
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT],
                    code_start: 0,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    name: "enum_tag".into(),
                    flags: 0,
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, choice, U32],
                    code_start: 2,
                    code_len: 4,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Call { dst: None, function: 1, args: vec![] },
                Instruction::Return { src: None },
                Instruction::Construct { dst: 1, ty: choice, variant: Some(1), fields: vec![] },
                Instruction::EnumTag { dst: 2, src: 1 },
                Instruction::Deconstruct { src: 1 },
                Instruction::Return { src: None },
            ],
            ..Artifact::default()
        };
        assert_eq!(artifact.types.len(), choice as usize);
        artifact.types.push(Type::Enum {
            name: "Choice".into(),
            variants: vec![
                EnumVariant { name: "No".into(), fields: vec![] },
                EnumVariant { name: "Yes".into(), fields: vec![] },
            ],
            copy: true,
        });
        let artifact = with_generated_cleanup_plans(artifact).unwrap();
        let ir = emit_artifact_llvm_ir(&artifact.encode()).unwrap();
        assert!(ir.contains("insertvalue { i32 } undef, i32 1, 0"));
        assert!(ir.contains("extractvalue { i32 }"));
        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("enum.ll");
        let object = directory.path().join("enum.o");
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
    fn verified_unit_payload_enum_uses_the_tag_only_abi_without_vm_execution() {
        let result = 19;
        let mut artifact = Artifact {
            entry_function: Some(0),
            constants: vec![Constant::Unit, Constant::U32(0), Constant::U32(1)],
            functions: vec![
                Function {
                    name: "main".into(),
                    flags: 0,
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, result, U32, UNIT],
                    code_start: 0,
                    code_len: 13,
                    label_slot_count: 0,
                },
                Function {
                    name: "result_unit".into(),
                    flags: 0,
                    params: vec![],
                    return_type: result,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, UNIT, result],
                    code_start: 13,
                    code_len: 3,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Call { dst: Some(1), function: 1, args: vec![] },
                Instruction::EnumTag { dst: 2, src: 1 },
                Instruction::Switch {
                    discr: 2,
                    cases: vec![(1, 3), (2, 8)],
                    otherwise: 3,
                },
                Instruction::Drop { register: 2 },
                Instruction::ProjectMove { dst: 3, src: 1, field: 0 },
                Instruction::Deconstruct { src: 1 },
                Instruction::Drop { register: 3 },
                Instruction::Return { src: None },
                Instruction::Drop { register: 2 },
                Instruction::ProjectMove { dst: 3, src: 1, field: 0 },
                Instruction::Deconstruct { src: 1 },
                Instruction::Drop { register: 3 },
                Instruction::Return { src: None },
                Instruction::Const { dst: 1, constant: 0 },
                Instruction::Construct {
                    dst: 2,
                    ty: result,
                    variant: Some(1),
                    fields: vec![1],
                },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        };
        assert_eq!(artifact.types.len(), result as usize);
        artifact.types.push(Type::Enum {
            name: "ResultUnit".into(),
            variants: vec![
                EnumVariant {
                    name: "Ok".into(),
                    fields: vec![Field { name: "value".into(), ty: UNIT }],
                },
                EnumVariant {
                    name: "Err".into(),
                    fields: vec![Field { name: "error".into(), ty: UNIT }],
                },
            ],
            copy: true,
        });
        let artifact = with_generated_cleanup_plans(artifact).unwrap();
        let ir = emit_artifact_llvm_ir(&artifact.encode()).unwrap();
        assert!(ir.contains("define { i32 } @grbc_fn_1()"));
        assert!(ir.contains("insertvalue { i32 } undef, i32 1, 0"));
        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("unit-payload-enum.ll");
        let object = directory.path().join("unit-payload-enum.o");
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
    fn verified_artifact_uses_the_same_runtime_fault_abi_as_source_llvm() {
        let artifact = with_generated_cleanup_plans(Artifact {
            entry_function: Some(0),
            functions: vec![Function {
                name: "main".into(),
                flags: 0,
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT],
                code_start: 0,
                code_len: 1,
                label_slot_count: 0,
            }],
            code: vec![Instruction::Return { src: None }],
            ..Artifact::default()
        })
        .unwrap();
        let ir = emit_artifact_llvm_ir(&artifact.encode()).unwrap();
        let pointer_width = if cfg!(target_pointer_width = "32") { 32 } else { 64 };
        assert!(ir.contains(&format!(
            "declare void @g1_runtime_fault(i32, i32, i32, ptr, i{pointer_width}) cold noreturn"
        )));
    }

    #[test]
    fn verified_diagnostic_write_text_literal_uses_the_native_host_abi_without_vm_execution() {
        let artifact = with_generated_cleanup_plans(Artifact {
            entry_function: Some(0),
            // CORE_G1 | HOST_ABI_G1.  The verifier owns these feature bits;
            // hand-built fixture artifacts spell the frozen wire value.
            required_features: 1 | (1 << 5),
            constants: vec![Constant::Text("artifact host ABI\\n".into())],
            imports: vec![Import {
                capability: "diagnostic".into(),
                symbol: "write".into(),
                signature: Signature {
                    params: vec![TEXT],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                may_trap: true,
            }],
            functions: vec![Function {
                name: "main".into(),
                flags: 0,
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, TEXT, UNIT],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::HostCall {
                    dst: Some(2),
                    import: 0,
                    args: vec![1],
                },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        })
        .unwrap();
        let ir = emit_artifact_llvm_ir(&artifact.encode()).unwrap();
        assert!(ir.contains("%g1.bytes = type { i64, i64, [0 x i8] }"));
        assert!(ir.contains("@g1.artifact.bytes.0 = private constant"));
        assert!(ir.contains("declare i32 @g1_host_diagnostic_write(ptr)"));
        assert!(ir.contains("call i32 @g1_host_diagnostic_write(ptr"));
        assert!(ir.contains("call void @g1_host_fault(i32 4)"));

        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("diagnostic.ll");
        let executable = directory.path().join("diagnostic");
        fs::write(&source, ir).unwrap();
        let runtime = concat!(env!("CARGO_MANIFEST_DIR"), "/src/native_host_runtime.c");
        let status = Command::new("clang")
            .args(["-O3", "-x", "ir"])
            .arg(&source)
            .args(["-x", "c", runtime, "-o"])
            .arg(&executable)
            .status()
            .unwrap();
        assert!(status.success());
        let output = Command::new(&executable).output().unwrap();
        assert!(output.status.success());
        assert_eq!(output.stderr, b"artifact host ABI\\n");
    }

    #[test]
    fn verified_process_and_filesystem_host_imports_emit_the_frozen_native_abi() {
        let array_text = 19;
        let mut artifact = Artifact {
            entry_function: Some(0), required_features: 1 | (1 << 5),
            constants: vec![Constant::Text("/dev/null".into())],
            imports: vec![
                Import { capability: "fs.read".into(), symbol: "read".into(), signature: Signature { params: vec![TEXT], result: BYTES, outward_protocols: vec![] }, may_trap: true },
                Import { capability: "fs.write".into(), symbol: "write".into(), signature: Signature { params: vec![TEXT, BYTES], result: UNIT, outward_protocols: vec![] }, may_trap: true },
                Import { capability: "process.args".into(), symbol: "get".into(), signature: Signature { params: vec![], result: array_text, outward_protocols: vec![] }, may_trap: true },
            ],
            functions: vec![Function { name: "main".into(), flags: 0, params: vec![], return_type: UNIT, outward_protocols: vec![], receiver_mode: None, register_types: vec![UNIT, TEXT, BYTES, UNIT, TEXT], code_start: 0, code_len: 6, label_slot_count: 0 }],
            code: vec![
                Instruction::Const { dst: 1, constant: 0 },
                Instruction::Copy { dst: 4, src: 1 },
                Instruction::HostCall { dst: Some(2), import: 0, args: vec![1] },
                Instruction::HostCall { dst: Some(3), import: 1, args: vec![4, 2] },
                Instruction::Drop { register: 2 }, Instruction::Return { src: None },
            ],
            ..Artifact::default()
        };
        assert_eq!(artifact.types.len(), array_text as usize);
        artifact.types.push(Type::Array { element: TEXT });
        let artifact = with_generated_cleanup_plans(artifact).unwrap();
        let ir = emit_artifact_llvm_ir(&artifact.encode()).unwrap();
        assert!(ir.contains("define i32 @main(i32 %argc, ptr %argv)"));
        assert!(ir.contains("call void @g1_host_process_init(i32 %argc, ptr %argv)"));
        assert!(ir.contains("declare ptr @g1_host_process_args_get()"));
        assert!(ir.contains("call ptr @g1_host_fs_read(ptr"));
        assert!(ir.contains("call i32 @g1_host_fs_write(ptr"));
        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("host-imports.ll");
        let object = directory.path().join("host-imports.o");
        fs::write(&source, ir).unwrap();
        assert!(Command::new("clang").args(["-x", "ir", "-c"]).arg(&source).arg("-o").arg(&object).status().unwrap().success());
    }

    #[test]
    fn host_call_lookalikes_remain_fail_closed() {
        let mut artifact = with_generated_cleanup_plans(Artifact {
            entry_function: Some(0),
            required_features: 1 | (1 << 5),
            constants: vec![Constant::Text("nope".into())],
            imports: vec![Import {
                capability: "diagnostic".into(),
                symbol: "write".into(),
                signature: Signature {
                    params: vec![TEXT],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                may_trap: true,
            }],
            functions: vec![Function {
                name: "main".into(),
                flags: 0,
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, TEXT, UNIT],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const { dst: 1, constant: 0 },
                Instruction::HostCall { dst: Some(2), import: 0, args: vec![1] },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        })
        .unwrap();
        artifact.imports[0].symbol = "not-write".into();
        let artifact = with_generated_cleanup_plans(artifact).unwrap();
        assert!(matches!(
            emit_artifact_llvm_ir(&artifact.encode()),
            Err(ArtifactLlvmError::UnsupportedInstruction { opcode: "unsupported host import", .. })
        ));
    }

    #[test]
    fn runtime_payload_enums_remain_fail_closed_until_a_tagged_union_abi_exists() {
        let mut artifact = Artifact::default();
        artifact.types.push(Type::Enum {
            name: "Payload".into(),
            variants: vec![EnumVariant {
                name: "Some".into(),
                fields: vec![Field { name: "value".into(), ty: I64 }],
            }],
            copy: true,
        });
        let enum_type = (artifact.types.len() - 1) as u32;
        assert!(matches!(
            llvm_type(&artifact, 0, enum_type),
            Err(ArtifactLlvmError::UnsupportedType { ty, .. }) if ty == enum_type
        ));
    }
}
