//! Fail-closed LLVM lowering for the first scalar-and-value-aggregate `.grbc` AOT slice.
//!
//! This is intentionally an artifact boundary, not a second source compiler:
//! callers hand it encoded bytecode, which is decoded and verified before a
//! single LLVM instruction is emitted.  It does not construct a [`Vm`] or use
//! any interpreter entry point.  The supported surface is deliberately small
//! (direct scalar/value-aggregate functions with ordinary control flow); every other valid G1 instruction
//! remains an explicit lowering error until it has a native ABI.

use std::{collections::{BTreeMap, BTreeSet}, error::Error, fmt};

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
    // A closed `Handle` whose body has no effect operations can be represented
    // as a direct call.  Keep the proof local to this artifact: the handler is
    // not a process-global host capability, and the body is selected only from
    // the exact lexical producer chain recognized below.
    let mut closed_handle_bodies = closed_handle_body_functions(artifact);
    closed_handle_bodies.extend(closed_shared_handle_body_functions(artifact));
    let reachable = reachable_functions(artifact, entry, &closed_handle_bodies)?;
    for (function_id, function) in artifact.functions.iter().enumerate() {
        if reachable.contains(&(function_id as u32)) {
            emit_function(
                &mut output,
                artifact,
                function_id as u32,
                function,
                closed_handle_bodies.contains(&(function_id as u32)),
            )?;
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
    closed_handle_bodies: &BTreeSet<u32>,
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
                | Instruction::TailCallKnownReceiver { function, .. } => pending.push(*function),
                // A callable target normally has a receiver and therefore is
                // not directly executable in this ABI.  The one exception is
                // the body of a statically proven, effect-free closed Handle.
                Instruction::MakeCallable { function, .. }
                    if closed_handle_bodies.contains(function) => pending.push(*function),
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
    allow_empty_owned_receiver: bool,
) -> Result<(), ArtifactLlvmError> {
    if (!allow_empty_owned_receiver && function.receiver_mode.is_some())
        || (allow_empty_owned_receiver && !is_empty_owned_receiver(function))
        || !function.outward_protocols.is_empty()
    {
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
    let closed_handler_plans = closed_host_handler_plans(artifact, function_id, function)?;
    let shared_perform_dispatches = closed_shared_perform_dispatches(artifact, function_id);
    let shared_host_preparations = prepared_shared_host_calls(artifact, function_id);
    let shared_perform_consumes = closed_shared_perform_consume_sites(artifact, function_id);
    let shared_perform_opaque_registers = shared_perform_dispatches
        .iter()
        .map(|dispatch| dispatch.body_register)
        .collect::<BTreeSet<_>>();
    let closed_handles = closed_handle_sites(artifact, function_id);
    let shared_handles = closed_shared_handle_sites(artifact, function_id, function, &closed_handler_plans);
    let closed_handle_opaque_registers = closed_handle_opaque_registers(artifact, function_id, &closed_handles);
    let register_types = function
        .register_types
        .iter()
        .enumerate()
        .map(|(register, ty)| {
            llvm_type(artifact, function_id, *ty).or_else(|error| {
                closed_handler_plans
                    .contains_key(&(register as u32))
                    .then_some("ptr".to_owned())
                    .or_else(|| {
                        closed_handle_opaque_registers
                            .contains(&(register as u32))
                            .then_some("ptr".to_owned())
                    })
                    .or_else(|| {
                        shared_perform_opaque_registers
                            .contains(&(register as u32))
                            .then_some("ptr".to_owned())
                    })
                    .or_else(|| shared_handles.values().any(|site| site.body_register == register as u32).then_some("ptr".to_owned()))
                    .ok_or(error)
            })
        })
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
            Instruction::MakeHandlerShared { dst, .. } => {
                let plan = closed_handler_plans.get(dst).ok_or_else(|| {
                    unsupported(function_id, instruction_id, "closed host handler plan")
                })?;
                // The frame is deliberately materialized at the lexical
                // producer, rather than reconstructed from an import at a
                // later Perform. Field zero is the dynamic Handle-scope bit;
                // one field per frozen route records its one-shot resumption
                // consumption. `Handle`/`Perform` still fail closed below,
                // but their future lowering has an exact native state object
                // to thread, validate, and invalidate.
                let frame_name = format!("%closed_handler_frame_{instruction_id}");
                let field_count = plan.frame.native_field_count();
                output.push_str(&format!("  {frame_name} = alloca [{field_count} x i1]\n"));
                for field in 0..field_count {
                    let pointer = format!("%closed_handler_frame_{instruction_id}_field_{field}");
                    output.push_str(&format!(
                        "  {pointer} = getelementptr inbounds [{field_count} x i1], ptr {frame_name}, i64 0, i64 {field}\n"
                    ));
                    // The frame begins inactive; lexical `Handle` is the
                    // only future instruction permitted to activate it.
                    output.push_str(&format!("  store i1 false, ptr {pointer}\n"));
                }
                // The handler register carries the address of this exact
                // frame. This is intentionally a local pointer only; it is
                // not a host-runtime handle and does not authorize imports.
                emit_store(
                    output,
                    &register_types,
                    function_id,
                    instruction_id,
                    *dst,
                    &frame_name,
                )?;
                output.push_str(&format!(
                    "  ; closed-host-handler-frame r{dst}: def={} routes={} clauses={} active-field=0 one-shot-fields=1..{}\n",
                    plan.frame.handler_def,
                    plan.frame.continuations.len(),
                    plan.clause_functions.len(),
                    field_count - 1,
                ));
                for dispatch in shared_perform_dispatches
                    .iter()
                    .filter(|dispatch| dispatch.handler_instruction == instruction_id)
                {
                    // This records the only future native dispatch route that
                    // this frame can authorize. It is intentionally not a
                    // call: the matching active Handle boundary and actual
                    // continuation transfer still need lowering together.
                    output.push_str(&format!(
                        "  ; closed-host-perform-dispatch handle={} body={} perform={} route=({}, {}) frame-field={} import={}\n",
                        dispatch.handle_instruction,
                        dispatch.body_function,
                        dispatch.perform_instruction,
                        dispatch.continuation.protocol,
                        dispatch.continuation.operation,
                        dispatch.resumption_field,
                        dispatch.continuation.import,
                    ));
                }
                for preparation in shared_host_preparations
                    .iter()
                    .filter(|preparation| preparation.handler_instruction == instruction_id)
                {
                    // This is signature-only preparation. In particular it
                    // emits no `call`: an unresumable Perform must continue
                    // through the fail-closed transition below.
                    output.push_str(&format!(
                        "  ; prepared-frozen-host-call body={} perform={} import={} symbol={} abi={}\n",
                        preparation.body_function,
                        preparation.perform_instruction,
                        preparation.import,
                        preparation.symbol,
                        preparation.abi,
                    ));
                }
                emit_fallthrough(output, function, function_id, instruction_id)?;
            }
            Instruction::MakeCallable { .. } | Instruction::MakeHandler { .. }
                if closed_handle_opaque_registers.iter().any(|register| {
                    instruction_writes_register(instruction) == Some(*register)
                }) || shared_perform_opaque_registers.iter().any(|register| {
                    instruction_writes_register(instruction) == Some(*register)
                }) || shared_handles.values().any(|site| {
                    instruction_writes_register(instruction) == Some(site.body_register)
                }) => {
                // The callable and handler are lexical proof tokens for this
                // restricted path. They have no native representation: exact
                // static plans carry their body/route identity separately.
                emit_fallthrough(output, function, function_id, instruction_id)?;
            }
            Instruction::Handle { dst, args, .. } => {
                if let Some(site) = shared_perform_consumes.get(&instruction_id) {
                    emit_closed_shared_perform_consumption(
                        output,
                        &register_types,
                        function_id,
                        instruction_id,
                        site,
                        &mut temporary,
                    )?;
                    continue;
                }
                if let Some(site) = shared_handles.get(&instruction_id) {
                    emit_closed_shared_handle_scope(
                        output, artifact, &register_types, function, function_id, instruction_id,
                        *dst, args, site, &mut temporary,
                    )?;
                    continue;
                }
                let body = closed_handles.get(&instruction_id).ok_or_else(|| {
                    unsupported(function_id, instruction_id, "closed effect-free handle")
                })?;
                let body_function = artifact.functions.get(*body as usize).ok_or_else(|| {
                    unsupported(function_id, instruction_id, "closed handle body")
                })?;
                if args.len() != body_function.params.len() {
                    return Err(unsupported(function_id, instruction_id, "handle arity"));
                }
                let mut arguments = Vec::with_capacity(args.len());
                for (index, register) in args.iter().enumerate() {
                    let ty = llvm_type(artifact, function_id, body_function.params[index])?;
                    let value = emit_load(
                        output, &register_types, function_id, instruction_id, *register, &mut temporary,
                    )?;
                    arguments.push(format!("{ty} {value}"));
                }
                let arguments = arguments.join(", ");
                let body_result = llvm_type(artifact, function_id, body_function.return_type)?;
                if body_result == "void" {
                    output.push_str(&format!("  call void @grbc_fn_{body}({arguments})\n"));
                } else {
                    let name = format!("%v{temporary}");
                    temporary += 1;
                    output.push_str(&format!(
                        "  {name} = call {body_result} @grbc_fn_{body}({arguments})\n"
                    ));
                    emit_store(
                        output, &register_types, function_id, instruction_id, *dst, &name,
                    )?;
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

/// A lexical, one-shot host-effect route prepared for artifact AOT lowering.
///
/// This is deliberately more precise than an import declaration: `Perform`
/// may only use one of these routes while its matching [`ClosedHostHandlerFrame`]
/// is active.  Keeping the protocol operation result distinct from the import
/// result matters for `ProcessArgs`, whose generated handler wraps the host
/// array before resuming the source continuation.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ClosedHostContinuation {
    protocol: u32,
    operation: u32,
    import: u32,
    operation_result: TypeId,
    import_result: TypeId,
    resumption_type: TypeId,
}

/// The static part of a lexical `Handle` frame for the frozen self-host host
/// protocols.  Future instruction lowering must pair this with the dynamic
/// `MakeHandler`/`Handle` registers and consume its continuations exactly once;
/// it must never turn an arbitrary `Perform` into a process-global host call.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ClosedHostHandlerFrame {
    handler_def: u32,
    continuations: Vec<ClosedHostContinuation>,
}

/// A statically installed, but not yet executable, closed host-handler plan.
///
/// The first AOT slice records this only at the `MakeHandlerShared` site.  It
/// intentionally does not lower `Handle` or `Perform`: executing either
/// without the complete lexical continuation ABI would turn a locally handled
/// effect into an unsound process-global host call.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ClosedHostHandlerPlan {
    frame: ClosedHostHandlerFrame,
    clause_functions: Vec<u32>,
}

#[derive(Clone, Debug)]
struct ClosedSharedHandleSite {
    handler_register: u32,
    body_register: u32,
    body_function: u32,
    frame: ClosedHostHandlerFrame,
}

/// Static identity of the only route a future `Perform` lowering may use while
/// a particular closed frame is lexically active.  This is metadata, not an
/// import capability: callers still need a proven active Handle scope and a
/// continuation ABI before they may emit any behavior.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ClosedFramePerformRoute {
    handler_def: u32,
    protocol: u32,
    operation: u32,
    import: u32,
    one_shot_field: u32,
    resumption_type: TypeId,
    operation_result: TypeId,
    import_result: TypeId,
}

/// A value-transfer ABI proven safe for a future closed-frame dispatch.
///
/// There is deliberately no structural cast or pointer reinterpretation here.
/// The current artifact AOT ABI has not modeled any result wrapper conversion,
/// so type identity is the only admissible transfer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ClosedFrameResultTransfer {
    Identity { ty: TypeId },
}

/// Static contract for consuming one exact frozen-frame resumption field.
/// It is intentionally not an executable continuation: the caller still must
/// establish active scope, consume the field once, and lower control transfer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ClosedFrameResumeTransfer {
    handler_def: u32,
    one_shot_field: u32,
    resumption_type: TypeId,
    value_type: TypeId,
    destination_type: TypeId,
}

/// A direct callable producer that is safe to name in the closed-handler ABI.
/// This is intentionally a lexical identity, rather than an attempt to infer
/// a callable through copies, joins, or a global target set.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ClosedHostCallable {
    function: u32,
    callable_type: TypeId,
}

/// The complete static continuation boundary of one closed `Handle` site.
///
/// This is analysis only.  In particular, recognizing this shape does not
/// permit `Handle`, `Perform`, or `Resume` to reach the LLVM emitter yet.  It
/// gives that later work a compact ABI whose function identities cannot be
/// confused with another handler that happens to use the same callable type.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ClosedHostHandlerContinuationAbi {
    owner_function: u32,
    handle_instruction: u32,
    handler_register: u32,
    body_register: u32,
    clause_registers: Vec<u32>,
    frame: ClosedHostHandlerFrame,
    body: ClosedHostCallable,
    clauses: Vec<ClosedHostCallable>,
}

/// Discover only the simplest generated closed-handler chain:
/// `MakeCallable` (body and clauses), `MakeHandler`, then `Handle`.
///
/// Every value is bound by its exact source register producer in the enclosing
/// function.  Capturing callables, `MakeHandlerShared`, copied/merged handler
/// values, and any effect outside the frozen four-protocol set remain
/// deliberately unrecognized.
fn closed_host_handler_continuation_abis(
    artifact: &Artifact,
) -> Vec<ClosedHostHandlerContinuationAbi> {
    let mut found = Vec::new();
    for (owner_function, owner) in artifact.functions.iter().enumerate() {
        let start = owner.code_start as usize;
        let Some(end) = start.checked_add(owner.code_len as usize) else { continue };
        let Some(code) = artifact.code.get(start..end) else { continue };
        let mut callables = BTreeMap::<u32, ClosedHostCallable>::new();
        let mut handlers =
            BTreeMap::<u32, (ClosedHostHandlerFrame, Vec<ClosedHostCallable>, Vec<u32>)>::new();
        for (offset, instruction) in code.iter().enumerate() {
            match instruction {
                Instruction::MakeCallable { dst, callable_type, function, captures }
                    if captures.is_empty() => {
                        if let Some(callable) = closed_host_callable(artifact, *function, *callable_type) {
                            callables.insert(*dst, callable);
                        } else {
                            callables.remove(dst);
                        }
                    }
                Instruction::MakeCallable { dst, .. } => {
                    callables.remove(dst);
                }
                Instruction::MakeHandler { dst, handler_def, clauses } => {
                    let Some(frame) = ClosedHostHandlerFrame::build(artifact, *handler_def) else {
                        handlers.remove(dst);
                        continue;
                    };
                    let clause_registers = clauses.clone();
                    let clauses = clauses
                        .iter()
                        .map(|register| callables.get(register).cloned())
                        .collect::<Option<Vec<_>>>();
                    let Some(clauses) = clauses else {
                        handlers.remove(dst);
                        continue;
                    };
                    if closed_host_handler_clauses_match(artifact, &frame, &clauses)
                        && handler_register_matches(artifact, owner, *dst, *handler_def, &clauses)
                    {
                        handlers.insert(*dst, (frame, clauses, clause_registers));
                    } else {
                        handlers.remove(dst);
                    }
                }
                // This ABI deliberately starts with independent, empty
                // callable environments.  A shared environment needs a
                // separate lifetime/receiver contract before it is native.
                Instruction::MakeHandlerShared { dst, .. } => {
                    handlers.remove(dst);
                }
                Instruction::Handle { dst, handler, body, args } => {
                    let Some((frame, clauses, clause_registers)) = handlers.get(handler).cloned() else { continue };
                    let body_register = *body;
                    let Some(body) = callables.get(body).cloned() else { continue };
                    if closed_host_handle_matches(artifact, owner, *dst, args, &frame, &body) {
                        found.push(ClosedHostHandlerContinuationAbi {
                            owner_function: owner_function as u32,
                            handle_instruction: offset as u32,
                            handler_register: *handler,
                            body_register,
                            clause_registers,
                            frame,
                            body,
                            clauses,
                        });
                    }
                }
                _ => {}
            }
        }
    }
    found
}

/// The first executable closed-handler slice deliberately stops before
/// `Perform`: it proves that the body cannot observe the installed handler,
/// then lowers the lexical Handle boundary to its direct body call.  This is
/// useful on its own (generated handler scaffolding no longer blocks native
/// code) without pretending that a continuation has an ABI before one exists.
fn closed_handle_body_functions(artifact: &Artifact) -> BTreeSet<u32> {
    closed_host_handler_continuation_abis(artifact)
        .into_iter()
        .filter(|abi| closed_handle_body_is_effect_free(artifact, abi))
        .map(|abi| abi.body.function)
        .collect()
}

fn closed_shared_handle_body_functions(artifact: &Artifact) -> BTreeSet<u32> {
    artifact.functions.iter().enumerate().flat_map(|(function_id, function)| {
        let Ok(plans) = closed_host_handler_plans(artifact, function_id as u32, function) else {
            return BTreeSet::new();
        };
        closed_shared_handle_sites(artifact, function_id as u32, function, &plans)
            .into_values()
            .map(|site| site.body_function)
            .collect()
    }).collect()
}

/// Recognize a direct lexical use of a materialized shared frame.  The body
/// must be the same closed, empty-receiver, effect-free callable used by the
/// existing Handle slice.  No copied handler/body values are admitted.
fn closed_shared_handle_sites(
    artifact: &Artifact,
    _function_id: u32,
    function: &Function,
    plans: &BTreeMap<u32, ClosedHostHandlerPlan>,
) -> BTreeMap<u32, ClosedSharedHandleSite> {
    let start = function.code_start as usize;
    let Some(code) = artifact.code.get(start..start.saturating_add(function.code_len as usize)) else {
        return BTreeMap::new();
    };
    let mut callables = BTreeMap::new();
    let mut active_plans = BTreeMap::new();
    let mut sites = BTreeMap::new();
    for (offset, instruction) in code.iter().enumerate() {
        match instruction {
            Instruction::MakeCallable { dst, callable_type, function, captures }
                if captures.is_empty() => {
                    if let Some(callable) = closed_host_callable(artifact, *function, *callable_type) {
                        callables.insert(*dst, callable);
                    } else {
                        callables.remove(dst);
                    }
                }
            Instruction::MakeCallable { dst, .. } => { callables.remove(dst); }
            Instruction::MakeHandlerShared { dst, .. } => {
                if let Some(plan) = plans.get(dst) {
                    active_plans.insert(*dst, plan.clone());
                }
            }
            Instruction::Move { dst, .. } | Instruction::Copy { dst, .. } => {
                callables.remove(dst);
                active_plans.remove(dst);
            }
            Instruction::Handle { dst, handler, body, args } => {
                let Some(plan) = active_plans.get(handler) else { continue };
                let Some(body_callable) = callables.get(body) else { continue };
                let Some(body_function) = artifact.functions.get(body_callable.function as usize) else { continue };
                let Some(result_type) = frame_result_type(artifact, plan.frame.handler_def) else { continue };
                if !is_effect_free_closed_body(artifact, body_function)
                    || body_function.return_type != result_type
                    || function.register_types.get(*dst as usize) != Some(&result_type)
                    || args.iter().map(|register| function.register_types.get(*register as usize).copied()).collect::<Option<Vec<_>>>() != Some(body_function.params.clone())
                {
                    continue;
                }
                sites.insert(offset as u32, ClosedSharedHandleSite {
                    handler_register: *handler,
                    body_register: *body,
                    body_function: body_callable.function,
                    frame: plan.frame.clone(),
                });
            }
            _ => {}
        }
    }
    sites
}

fn emit_closed_shared_handle_scope(
    output: &mut String,
    artifact: &Artifact,
    register_types: &[String],
    function: &Function,
    function_id: u32,
    instruction_id: u32,
    dst: u32,
    args: &[u32],
    site: &ClosedSharedHandleSite,
    temporary: &mut u32,
) -> Result<(), ArtifactLlvmError> {
    let frame = emit_load(output, register_types, function_id, instruction_id, site.handler_register, temporary)?;
    let fields = site.frame.native_field_count();
    let active = format!("%closed_handler_active_{instruction_id}");
    output.push_str(&format!("  {active} = getelementptr inbounds [{fields} x i1], ptr {frame}, i64 0, i64 0\n"));
    let prior = format!("%closed_handler_prior_active_{instruction_id}");
    output.push_str(&format!("  {prior} = load i1, ptr {active}\n  store i1 true, ptr {active}\n"));
    let body = artifact.functions.get(site.body_function as usize).ok_or_else(|| unsupported(function_id, instruction_id, "closed shared handle body"))?;
    let arguments = args.iter().enumerate().map(|(index, register)| {
        let ty = llvm_type(artifact, function_id, body.params[index])?;
        let value = emit_load(output, register_types, function_id, instruction_id, *register, temporary)?;
        Ok(format!("{ty} {value}"))
    }).collect::<Result<Vec<_>, ArtifactLlvmError>>()?.join(", ");
    let result = llvm_type(artifact, function_id, body.return_type)?;
    if result == "void" {
        output.push_str(&format!("  call void @grbc_fn_{}({arguments})\n", site.body_function));
    } else {
        let value = format!("%v{temporary}");
        *temporary += 1;
        output.push_str(&format!("  {value} = call {result} @grbc_fn_{}({arguments})\n", site.body_function));
        emit_store(output, register_types, function_id, instruction_id, dst, &value)?;
    }
    // Restore, rather than clear, the prior bit so a nested Handle using the
    // same frame cannot deactivate its enclosing lexical scope.
    output.push_str(&format!("  store i1 {prior}, ptr {active}\n"));
    emit_fallthrough(output, function, function_id, instruction_id)
}

fn closed_frame_perform_route(
    frame: &ClosedHostHandlerFrame,
    protocol: u32,
    operation: u32,
) -> Option<ClosedFramePerformRoute> {
    let continuation = frame
        .continuations
        .iter()
        .find(|continuation| {
            continuation.protocol == protocol && continuation.operation == operation
        })?;
    let one_shot_field = frame.native_resumption_field(protocol, operation)?;
    // Field zero is reserved for lexical Handle activity; a route can never
    // silently alias it as a consumed-resumption bit.
    (one_shot_field > 0).then_some(ClosedFramePerformRoute {
        handler_def: frame.handler_def,
        protocol,
        operation,
        import: continuation.import,
        one_shot_field,
        resumption_type: continuation.resumption_type,
        operation_result: continuation.operation_result,
        import_result: continuation.import_result,
    })
}

fn closed_frame_result_transfer(
    route: &ClosedFramePerformRoute,
) -> Option<ClosedFrameResultTransfer> {
    (route.operation_result == route.import_result).then_some(
        ClosedFrameResultTransfer::Identity {
            ty: route.operation_result,
        },
    )
}

fn closed_frame_resume_transfer(
    artifact: &Artifact,
    route: &ClosedFramePerformRoute,
    resumption_type: TypeId,
    value_type: TypeId,
    destination_type: TypeId,
) -> Option<ClosedFrameResumeTransfer> {
    // The import result can only feed the operation result through a proven
    // transfer ABI.  Today that means strict identity; a future wrapper must
    // be modeled explicitly before Resume can see it.
    closed_frame_result_transfer(route)?;
    if route.one_shot_field == 0 || resumption_type != route.resumption_type {
        return None;
    }
    let Type::Resumption { input_type, output_type, lower_uses, upper_uses, .. } =
        artifact.types.get(resumption_type as usize)?.representation() else { return None };
    (*input_type == route.operation_result
        && *input_type == value_type
        && *output_type == destination_type
        && *lower_uses == 1
        && *upper_uses == Some(1))
        .then_some(ClosedFrameResumeTransfer {
            handler_def: route.handler_def,
            one_shot_field: route.one_shot_field,
            resumption_type,
            value_type,
            destination_type,
        })
}

/// Emit the one-shot state transition for an already validated closed-frame
/// resume transfer.  This does not resume anything: it only establishes the
/// deterministic consume-or-fail CFG that a later continuation ABI must use.
fn emit_closed_frame_consume_one_shot(
    output: &mut String,
    frame: &str,
    field_count: u32,
    transfer: ClosedFrameResumeTransfer,
    function_id: u32,
    instruction_id: u32,
) -> Result<(), ArtifactLlvmError> {
    if transfer.one_shot_field == 0 || transfer.one_shot_field >= field_count {
        return Err(unsupported(
            function_id,
            instruction_id,
            "closed frame resumption field",
        ));
    }
    let suffix = format!("{instruction_id}_{}", transfer.one_shot_field);
    let field = format!("%closed_frame_resume_field_{suffix}");
    let used = format!("%closed_frame_resume_used_{suffix}");
    let reused = format!("closed_frame_resume_reused_{suffix}");
    let consume = format!("closed_frame_resume_consume_{suffix}");
    output.push_str(&format!(
        "  {field} = getelementptr inbounds [{field_count} x i1], ptr {frame}, i64 0, i64 {}\n",
        transfer.one_shot_field,
    ));
    output.push_str(&format!(
        "  {used} = load i1, ptr {field}\n  br i1 {used}, label %{reused}, label %{consume}\n{reused}:\n  unreachable\n{consume}:\n  store i1 false, ptr {field}\n"
    ));
    Ok(())
}

/// The exact entry point a future static Resume lowering must use.
///
/// The frame layout currently stores only scope/one-shot bits; it does not
/// contain a captured native return address, register snapshot, or ownership
/// restoration plan.  Therefore even a perfectly typed frozen Resume must
/// fail *before* consuming its one-shot field.  Clearing the bit before this
/// diagnostic would mutate observable handler state without transferring
/// control, which is less safe than rejecting it.
fn emit_closed_frame_resume_or_reject(
    output: &mut String,
    artifact: &Artifact,
    route: &ClosedFramePerformRoute,
    resumption_type: TypeId,
    value_type: TypeId,
    destination_type: TypeId,
    function_id: u32,
    instruction_id: u32,
) -> Result<(), ArtifactLlvmError> {
    let emitted_before = output.len();
    let Some(_transfer) = closed_frame_resume_transfer(
        artifact,
        route,
        resumption_type,
        value_type,
        destination_type,
    ) else {
        return Err(unsupported(function_id, instruction_id, "closed frame resume ABI"));
    };
    debug_assert_eq!(output.len(), emitted_before, "no one-shot state may be consumed before continuation state exists");
    Err(unsupported(
        function_id,
        instruction_id,
        "closed frame continuation state",
    ))
}

fn closed_handle_sites(artifact: &Artifact, owner_function: u32) -> BTreeMap<u32, u32> {
    closed_host_handler_continuation_abis(artifact)
        .into_iter()
        .filter(|abi| {
            abi.owner_function == owner_function && closed_handle_body_is_effect_free(artifact, abi)
        })
        .map(|abi| (abi.handle_instruction, abi.body.function))
        .collect()
}

fn closed_handle_opaque_registers(
    artifact: &Artifact,
    owner_function: u32,
    sites: &BTreeMap<u32, u32>,
) -> BTreeSet<u32> {
    if sites.is_empty() {
        return BTreeSet::new();
    }
    closed_host_handler_continuation_abis(artifact)
        .into_iter()
        .filter(|abi| {
        abi.owner_function == owner_function
            && sites.get(&abi.handle_instruction) == Some(&abi.body.function)
        })
        .flat_map(|abi| {
            std::iter::once(abi.handler_register)
                .chain(std::iter::once(abi.body_register))
                .chain(abi.clause_registers)
        })
        .collect()
}

fn instruction_writes_register(instruction: &Instruction) -> Option<u32> {
    match instruction {
        Instruction::MakeCallable { dst, .. } | Instruction::MakeHandler { dst, .. } => Some(*dst),
        _ => None,
    }
}

fn is_empty_owned_receiver(function: &Function) -> bool {
    function.receiver_mode == Some(2)
        && function.register_types.first() == Some(&UNIT)
}

fn closed_handle_body_is_effect_free(
    artifact: &Artifact,
    abi: &ClosedHostHandlerContinuationAbi,
) -> bool {
    let Some(function) = artifact.functions.get(abi.body.function as usize) else { return false };
    is_effect_free_closed_body(artifact, function)
}

fn is_effect_free_closed_body(artifact: &Artifact, function: &Function) -> bool {
    if !is_empty_owned_receiver(function) || !function.outward_protocols.is_empty() { return false; }
    let start = function.code_start as usize;
    let Some(code) = artifact.code.get(start..start.saturating_add(function.code_len as usize)) else {
        return false;
    };
    code.iter().all(|instruction| matches!(instruction,
        Instruction::Nop
        | Instruction::Drop { .. }
        | Instruction::Deconstruct { .. }
        | Instruction::Const { .. }
        | Instruction::Move { .. }
        | Instruction::Copy { .. }
        | Instruction::Primitive { .. }
        | Instruction::Return { .. }
        | Instruction::Construct { .. }
        | Instruction::ProjectMove { .. }
        | Instruction::ProjectCopy { .. }
        | Instruction::EnumTag { .. }
        | Instruction::Jump { .. }
        | Instruction::Switch { .. }
        | Instruction::Call { .. }
        | Instruction::TailCall { .. }
    ))
}

fn closed_host_callable(
    artifact: &Artifact,
    function: u32,
    callable_type: TypeId,
) -> Option<ClosedHostCallable> {
    let Type::Callable { signature, capture_type, receiver_mode, .. } =
        artifact.types.get(callable_type as usize)?.representation() else { return None };
    if !empty_capture_type(artifact, *capture_type) {
        return None;
    }
    let target = artifact.functions.get(function as usize)?;
    (target.params == signature.params
        && target.return_type == signature.result
        && target.outward_protocols == signature.outward_protocols
        && target.receiver_mode == Some(*receiver_mode)
        && target.outward_protocols.iter().all(|protocol| frozen_protocol(artifact, *protocol)))
        .then_some(ClosedHostCallable { function, callable_type })
}

fn empty_capture_type(artifact: &Artifact, ty: TypeId) -> bool {
    matches!(artifact.types.get(ty as usize).map(Type::representation), Some(Type::Tuple { fields, .. }) if fields.is_empty())
        || ty == UNIT
}

fn frozen_protocol(artifact: &Artifact, protocol: u32) -> bool {
    artifact.protocols.get(protocol as usize).is_some_and(|protocol| {
        protocol.operations.iter().any(|operation| {
            frozen_host_protocol_role(protocol.display_name.as_str(), operation.name.as_str()).is_some()
        })
    })
}

fn closed_host_handler_clauses_match(
    artifact: &Artifact,
    frame: &ClosedHostHandlerFrame,
    clauses: &[ClosedHostCallable],
) -> bool {
    let Some(definition) = artifact.handler_defs.get(frame.handler_def as usize) else { return false };
    if definition.clauses.len() != clauses.len() {
        return false;
    }
    definition.clauses.iter().zip(clauses).all(|(clause, callable)| {
        let Some(function) = artifact.functions.get(callable.function as usize) else { return false };
        let Some(Type::Callable { signature, .. }) = artifact.types.get(callable.callable_type as usize).map(Type::representation) else { return false };
        signature == &clause.callable_signature
            && function.outward_protocols.iter().all(|protocol| *protocol == clause.protocol)
            && frame.continuations.iter().any(|continuation| {
                continuation.protocol == clause.protocol && continuation.operation == clause.operation
            })
    })
}

fn handler_register_matches(
    artifact: &Artifact,
    owner: &Function,
    register: u32,
    handler_def: u32,
    clauses: &[ClosedHostCallable],
) -> bool {
    let Some(handler_type) = owner.register_types.get(register as usize) else { return false };
    let Some(Type::Handler { handler_def: actual, capture_type, .. }) = artifact.types.get(*handler_type as usize).map(Type::representation) else { return false };
    if *actual != handler_def {
        return false;
    }
    matches!(artifact.types.get(*capture_type as usize).map(Type::representation),
        Some(Type::Tuple { fields, .. }) if fields == &clauses.iter().map(|callable| callable.callable_type).collect::<Vec<_>>())
}

fn closed_host_handle_matches(
    artifact: &Artifact,
    owner: &Function,
    destination: u32,
    args: &[u32],
    frame: &ClosedHostHandlerFrame,
    body: &ClosedHostCallable,
) -> bool {
    let Some(body_function) = artifact.functions.get(body.function as usize) else { return false };
    let Some(result_type) = frame_result_type(artifact, frame.handler_def) else { return false };
    owner.register_types.get(destination as usize) == Some(&result_type)
        && body_function.return_type == result_type
        && args.iter().map(|register| owner.register_types.get(*register as usize).copied()).collect::<Option<Vec<_>>>() == Some(body_function.params.clone())
}

fn frame_result_type(artifact: &Artifact, handler_def: u32) -> Option<TypeId> {
    artifact.handler_defs.get(handler_def as usize).map(|definition| definition.result_type)
}

impl ClosedHostHandlerFrame {
    /// Native lexical-frame layout: field zero is Handle-scope activity, and
    /// each remaining field is the consumed bit for one exact frozen route.
    /// Routes are sorted by protocol/operation in `build`, so this layout is
    /// deterministic across independent compiler invocations.
    fn native_field_count(&self) -> u32 {
        1 + self.continuations.len() as u32
    }

    fn native_resumption_field(&self, protocol: u32, operation: u32) -> Option<u32> {
        self.continuations
            .iter()
            .position(|continuation| {
                continuation.protocol == protocol && continuation.operation == operation
            })
            .map(|index| index as u32 + 1)
    }

    /// Recognize the exact four-protocol, one-shot handler shape emitted by
    /// the production self-host manifest.  Any partial handler, extra clause,
    /// lookalike protocol, or non-one-shot continuation remains outside this
    /// AOT foundation.
    fn build(artifact: &Artifact, handler_def: u32) -> Option<Self> {
        let definition = artifact.handler_defs.get(handler_def as usize)?;
        if definition.partial || definition.clauses.len() != 4 {
            return None;
        }
        let mut continuations = Vec::with_capacity(4);
        for clause in &definition.clauses {
            let protocol = artifact.protocols.get(clause.protocol as usize)?;
            let operation = protocol.operations.get(clause.operation as usize)?;
            let role = frozen_host_protocol_role(protocol.display_name.as_str(), operation.name.as_str())?;
            if operation.terminal
                || operation.resumption_lower != 1
                || operation.resumption_upper != Some(1)
            {
                return None;
            }
            let resumption_type = clause.resumption_type?;
            let Type::Resumption {
                input_type,
                output_type,
                lower_uses,
                upper_uses,
                ..
            } = artifact.types.get(resumption_type as usize)?.representation()
            else {
                return None;
            };
            // A resumed operation returns to the `Handle` expression, whose
            // result type is the handler definition's result.  The input is
            // exactly the operation's result value.
            if *input_type != operation.result_type
                || *output_type != definition.result_type
                || *lower_uses != 1
                || *upper_uses != Some(1)
            {
                return None;
            }
            let import = unique_frozen_import(artifact, role)?;
            if operation.payload_signature.params != artifact.imports[import as usize].signature.params {
                return None;
            }
            continuations.push(ClosedHostContinuation {
                protocol: clause.protocol,
                operation: clause.operation,
                import,
                operation_result: operation.result_type,
                import_result: artifact.imports[import as usize].signature.result,
                resumption_type,
            });
        }
        continuations.sort_by_key(|continuation| (continuation.protocol, continuation.operation));
        if continuations
            .windows(2)
            .any(|routes| routes[0].protocol == routes[1].protocol && routes[0].operation == routes[1].operation)
        {
            return None;
        }
        // The set, rather than only the cardinality, is part of the frozen
        // ABI. A handler for four arbitrary protocols must not be admitted.
        if continuations
            .iter()
            .filter_map(|continuation| frozen_host_import(artifact, &artifact.imports[continuation.import as usize]))
            .collect::<BTreeSet<_>>()
            != BTreeSet::from([
                FrozenHostImport::ProcessArgsGet,
                FrozenHostImport::FsRead,
                FrozenHostImport::FsWrite,
                FrozenHostImport::DiagnosticWrite,
            ])
        {
            return None;
        }
        Some(Self { handler_def, continuations })
    }
}

impl ClosedHostHandlerPlan {
    /// Accept only the capture-free shared-handler ABI that the next lowering
    /// slice can reason about.  Clause functions retain their lexical shared
    /// receiver, have no outward effects, and exactly match the handler
    /// definition's callable signatures.  This deliberately excludes every
    /// ordinary dynamic handler shape.
    fn build(
        artifact: &Artifact,
        handler_def: u32,
        functions: &[u32],
        captures: &[u32],
    ) -> Option<Self> {
        let frame = ClosedHostHandlerFrame::build(artifact, handler_def)?;
        let definition = artifact.handler_defs.get(handler_def as usize)?;
        if !captures.is_empty() || functions.len() != definition.clauses.len() {
            return None;
        }
        for (function_id, clause) in functions.iter().zip(&definition.clauses) {
            let function = artifact.functions.get(*function_id as usize)?;
            if function.receiver_mode != Some(0)
                || !function.outward_protocols.is_empty()
                || function.params != clause.callable_signature.params
                || function.return_type != clause.callable_signature.result
                || function.outward_protocols != clause.callable_signature.outward_protocols
            {
                return None;
            }
            let receiver = *function.register_types.first()?;
            if !matches!(
                artifact.types.get(receiver as usize).map(Type::representation),
                Some(Type::RefShared { referent }) if *referent == UNIT
            ) {
                return None;
            }
        }
        Some(Self {
            frame,
            clause_functions: functions.to_vec(),
        })
    }

    fn perform_route(&self, protocol: u32, operation: u32) -> Option<ClosedFramePerformRoute> {
        closed_frame_perform_route(&self.frame, protocol, operation)
    }
}

fn closed_host_handler_plans(
    artifact: &Artifact,
    function_id: u32,
    function: &Function,
) -> Result<BTreeMap<u32, ClosedHostHandlerPlan>, ArtifactLlvmError> {
    let start = function.code_start as usize;
    let end = start
        .checked_add(function.code_len as usize)
        .ok_or_else(|| unsupported(function_id, 0, "invalid function code range"))?;
    let code = artifact
        .code
        .get(start..end)
        .ok_or_else(|| unsupported(function_id, 0, "invalid function code range"))?;
    let mut plans = BTreeMap::new();
    for (offset, instruction) in code.iter().enumerate() {
        let Instruction::MakeHandlerShared {
            dst,
            handler_def,
            functions,
            captures,
        } = instruction
        else {
            continue;
        };
        let plan = ClosedHostHandlerPlan::build(artifact, *handler_def, functions, captures)
            .ok_or_else(|| unsupported(function_id, offset as u32, "closed host handler plan"))?;
        let handler_ty = *function
            .register_types
            .get(*dst as usize)
            .ok_or_else(|| unsupported(function_id, offset as u32, "invalid register"))?;
        if !matches!(
            artifact.types.get(handler_ty as usize).map(Type::representation),
            Some(Type::Handler { handler_def: actual, .. }) if *actual == *handler_def
        ) || plans.insert(*dst, plan).is_some()
        {
            return Err(unsupported(function_id, offset as u32, "closed host handler plan"));
        }
    }
    Ok(plans)
}

/// A statically established future native `Perform` route.  This is not an
/// import permission: it ties one operation in one directly named body to the
/// exact lexical shared-handler producer and one one-shot frame field.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ClosedSharedPerformDispatch {
    handler_instruction: u32,
    handler_register: u32,
    handle_instruction: u32,
    body_register: u32,
    body_function: u32,
    perform_instruction: u32,
    continuation: ClosedHostContinuation,
    resumption_field: u32,
}

/// Recognize only the smallest lexical shared-handler shape:
/// `MakeHandlerShared`, an empty-capture shared body `MakeCallable`, then
/// `Handle`, all in adjacent owner instructions. The direct adjacency and
/// exact registers deliberately reject copies, joins, nested frame selection,
/// and any attempt to discover a handler from an arbitrary `Perform`.
fn closed_shared_perform_dispatches(
    artifact: &Artifact,
    owner_function: u32,
) -> Vec<ClosedSharedPerformDispatch> {
    let Some(owner) = artifact.functions.get(owner_function as usize) else { return Vec::new() };
    let start = owner.code_start as usize;
    let Some(code) = artifact.code.get(start..start.saturating_add(owner.code_len as usize)) else {
        return Vec::new();
    };
    let mut found = Vec::new();
    for (index, window) in code.windows(3).enumerate() {
        let [
            Instruction::MakeHandlerShared { dst: handler, handler_def, functions, captures },
            Instruction::MakeCallable { dst: body_register, callable_type, function: body_function, captures: body_captures },
            Instruction::Handle { dst, handler: actual_handler, body: actual_body, args },
        ] = window else { continue };
        if handler != actual_handler || body_register != actual_body || !body_captures.is_empty() {
            continue;
        }
        let Some(frame_plan) = ClosedHostHandlerPlan::build(
            artifact,
            *handler_def,
            functions,
            captures,
        ) else { continue };
        let Some(body) = closed_shared_body_callable(artifact, *body_function, *callable_type) else {
            continue;
        };
        if !closed_host_handle_matches(artifact, owner, *dst, args, &frame_plan.frame, &body) {
            continue;
        }
        let Some(body_function) = artifact.functions.get(body.function as usize) else { continue };
        let body_start = body_function.code_start as usize;
        let Some(body_code) = artifact.code.get(body_start..body_start.saturating_add(body_function.code_len as usize)) else {
            continue;
        };
        for (perform_instruction, instruction) in body_code.iter().enumerate() {
            let Instruction::Perform { protocol, operation, .. } = instruction else { continue };
            let Some(continuation) = frame_plan.frame.continuations.iter().find(|route| {
                route.protocol == *protocol && route.operation == *operation
            }).cloned() else { continue };
            let Some(resumption_field) = frame_plan.frame.native_resumption_field(*protocol, *operation) else {
                continue;
            };
            found.push(ClosedSharedPerformDispatch {
                handler_instruction: index as u32,
                handler_register: *handler,
                handle_instruction: index as u32 + 2,
                body_register: *body_register,
                body_function: body.function,
                perform_instruction: perform_instruction as u32,
                continuation,
                resumption_field,
            });
        }
    }
    found
}

/// A validated native declaration/signature plan for a future resumed host
/// call. This deliberately contains no SSA values and no permission to emit
/// the call; it is just the immutable ABI proof retained beside the lexical
/// route that established it.
#[derive(Clone, Debug, PartialEq, Eq)]
struct PreparedSharedHostCall {
    handler_instruction: u32,
    body_function: u32,
    perform_instruction: u32,
    import: u32,
    symbol: &'static str,
    abi: &'static str,
}

fn prepared_shared_host_calls(
    artifact: &Artifact,
    owner_function: u32,
) -> Vec<PreparedSharedHostCall> {
    closed_shared_perform_dispatches(artifact, owner_function)
        .into_iter()
        .filter_map(|dispatch| prepare_shared_host_call(artifact, &dispatch))
        .collect()
}

fn prepare_shared_host_call(
    artifact: &Artifact,
    dispatch: &ClosedSharedPerformDispatch,
) -> Option<PreparedSharedHostCall> {
    let import = artifact.imports.get(dispatch.continuation.import as usize)?;
    let role = frozen_host_import(artifact, import)?;
    let body = artifact.functions.get(dispatch.body_function as usize)?;
    let start = body.code_start as usize;
    let instruction = artifact.code.get(start.checked_add(dispatch.perform_instruction as usize)?)?;
    let Instruction::Perform { protocol, operation, payloads, .. } = instruction else { return None };
    if *protocol != dispatch.continuation.protocol
        || *operation != dispatch.continuation.operation
        || payloads.len() != import.signature.params.len()
    {
        return None;
    }
    if payloads.iter().zip(&import.signature.params).any(|(register, expected)| {
        body.register_types.get(*register as usize) != Some(expected)
    }) {
        return None;
    }
    let (symbol, abi) = match role {
        FrozenHostImport::ProcessArgsGet => ("g1_host_process_args_get", "() -> ptr"),
        FrozenHostImport::FsRead => ("g1_host_fs_read", "(ptr) -> ptr"),
        FrozenHostImport::FsWrite => ("g1_host_fs_write", "(ptr, ptr) -> i32"),
        FrozenHostImport::DiagnosticWrite => ("g1_host_diagnostic_write", "(ptr) -> i32"),
    };
    Some(PreparedSharedHostCall {
        handler_instruction: dispatch.handler_instruction,
        body_function: dispatch.body_function,
        perform_instruction: dispatch.perform_instruction,
        import: dispatch.continuation.import,
        symbol,
        abi,
    })
}

/// The one native transition currently sound for a shared closed Perform.
/// It consumes the exact frame bit, then traps: no host value and no
/// resumption value exists until the complete continuation transfer ABI does.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ClosedSharedPerformConsumeSite {
    handler_register: u32,
    resumption_field: u32,
}

fn closed_shared_perform_consume_sites(
    artifact: &Artifact,
    owner_function: u32,
) -> BTreeMap<u32, ClosedSharedPerformConsumeSite> {
    closed_shared_perform_dispatches(artifact, owner_function)
        .into_iter()
        .filter(|dispatch| exact_unit_perform_then_return(artifact, dispatch))
        .map(|dispatch| (
            dispatch.handle_instruction,
            ClosedSharedPerformConsumeSite {
                handler_register: dispatch.handler_register,
                resumption_field: dispatch.resumption_field,
            },
        ))
        .collect()
}

fn exact_unit_perform_then_return(
    artifact: &Artifact,
    dispatch: &ClosedSharedPerformDispatch,
) -> bool {
    let Some(body) = artifact.functions.get(dispatch.body_function as usize) else { return false };
    if body.return_type != UNIT || body.params.len() != 0 {
        return false;
    }
    let start = body.code_start as usize;
    let Some(code) = artifact.code.get(start..start.saturating_add(body.code_len as usize)) else {
        return false;
    };
    matches!(
        code,
        [
            Instruction::Perform { dst: None, protocol, operation, payloads },
            Instruction::Return { src: None },
        ] if *protocol == dispatch.continuation.protocol
            && *operation == dispatch.continuation.operation
            && payloads.is_empty()
    )
}

fn emit_closed_shared_perform_consumption(
    output: &mut String,
    register_types: &[String],
    function_id: u32,
    instruction_id: u32,
    site: &ClosedSharedPerformConsumeSite,
    temporary: &mut u32,
) -> Result<(), ArtifactLlvmError> {
    let frame = emit_load(output, register_types, function_id, instruction_id, site.handler_register, temporary)?;
    let active = format!("%closed_perform_active_{instruction_id}");
    let used = format!("%closed_perform_used_{instruction_id}");
    output.push_str(&format!(
        "  {active} = getelementptr inbounds [5 x i1], ptr {frame}, i64 0, i64 0\n"
    ));
    output.push_str(&format!(
        "  {used} = getelementptr inbounds [5 x i1], ptr {frame}, i64 0, i64 {}\n",
        site.resumption_field,
    ));
    // This Handle is the sole activation point for the exact lexical frame.
    // Both continuations below terminate, so there is no scope bit to restore.
    output.push_str(&format!("  store i1 true, ptr {active}\n"));
    let active_value = format!("%closed_perform_active_value_{instruction_id}");
    output.push_str(&format!("  {active_value} = load i1, ptr {active}\n"));
    output.push_str(&format!(
        "  br i1 {active_value}, label %closed_perform_check_{instruction_id}, label %closed_perform_reject_{instruction_id}\n\
closed_perform_check_{instruction_id}:\n"
    ));
    let used_value = format!("%closed_perform_used_value_{instruction_id}");
    output.push_str(&format!("  {used_value} = load i1, ptr {used}\n"));
    output.push_str(&format!(
        "  br i1 {used_value}, label %closed_perform_reject_{instruction_id}, label %closed_perform_consume_{instruction_id}\n\
closed_perform_consume_{instruction_id}:\n  store i1 true, ptr {used}\n"
    ));
    emit_closed_perform_fault(output, function_id, instruction_id, "closed_perform_consume")?;
    output.push_str(&format!("closed_perform_reject_{instruction_id}:\n"));
    emit_closed_perform_fault(output, function_id, instruction_id, "closed_perform_reject")?;
    Ok(())
}

fn emit_closed_perform_fault(
    output: &mut String,
    function_id: u32,
    instruction_id: u32,
    reason: &str,
) -> Result<(), ArtifactLlvmError> {
    let width = pointer_width_for_target(&default_target_triple());
    output.push_str(&format!(
        "  ; {reason}: host invocation and Resume are intentionally unavailable\n  call void @g1_runtime_fault(i32 1, i32 {function_id}, i32 {instruction_id}, ptr null, i{width} 0)\n  unreachable\n"
    ));
    Ok(())
}

fn closed_shared_body_callable(
    artifact: &Artifact,
    function: u32,
    callable_type: TypeId,
) -> Option<ClosedHostCallable> {
    let callable = closed_host_callable(artifact, function, callable_type)?;
    let target = artifact.functions.get(function as usize)?;
    let Type::Callable { receiver_mode, .. } = artifact.types.get(callable_type as usize)?.representation() else {
        return None;
    };
    if *receiver_mode != 0 || target.receiver_mode != Some(0) {
        return None;
    }
    matches!(
        target.register_types.first().and_then(|receiver| artifact.types.get(*receiver as usize)).map(Type::representation),
        Some(Type::RefShared { referent }) if *referent == UNIT,
    )
    .then_some(callable)
}


fn frozen_host_protocol_role(protocol: &str, operation: &str) -> Option<FrozenHostImport> {
    match (protocol, operation) {
        ("ProcessArgs", "get") => Some(FrozenHostImport::ProcessArgsGet),
        ("FileRead", "read") => Some(FrozenHostImport::FsRead),
        ("FileWrite", "write") => Some(FrozenHostImport::FsWrite),
        ("Diagnostic", "write") => Some(FrozenHostImport::DiagnosticWrite),
        _ => None,
    }
}

fn unique_frozen_import(artifact: &Artifact, role: FrozenHostImport) -> Option<u32> {
    let mut imports = artifact
        .imports
        .iter()
        .enumerate()
        .filter_map(|(index, import)| (frozen_host_import(artifact, import) == Some(role)).then_some(index as u32));
    let import = imports.next()?;
    imports.next().is_none().then_some(import)
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

    use grandiose_vm::bytecode::{
        EnumVariant, Field, HandlerClause, HandlerDef, Import, Operation, Protocol, Signature,
    };
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
    fn closed_host_handler_frame_records_exact_one_shot_frozen_routes() {
        let array_text = 19;
        let mut artifact = Artifact {
            required_features: 1 | (1 << 5),
            imports: vec![
                Import { capability: "diagnostic".into(), symbol: "write".into(), signature: Signature { params: vec![TEXT], result: UNIT, outward_protocols: vec![] }, may_trap: true },
                Import { capability: "fs.read".into(), symbol: "read".into(), signature: Signature { params: vec![TEXT], result: BYTES, outward_protocols: vec![] }, may_trap: true },
                Import { capability: "fs.write".into(), symbol: "write".into(), signature: Signature { params: vec![TEXT, BYTES], result: UNIT, outward_protocols: vec![] }, may_trap: true },
                Import { capability: "process.args".into(), symbol: "get".into(), signature: Signature { params: vec![], result: array_text, outward_protocols: vec![] }, may_trap: true },
            ],
            protocols: vec![
                Protocol { display_name: "Diagnostic".into(), type_arguments: vec![], operations: vec![Operation { name: "write".into(), payload_signature: Signature { params: vec![TEXT], result: UNIT, outward_protocols: vec![] }, result_type: UNIT, resumption_lower: 1, resumption_upper: Some(1), terminal: false }] },
                Protocol { display_name: "FileRead".into(), type_arguments: vec![], operations: vec![Operation { name: "read".into(), payload_signature: Signature { params: vec![TEXT], result: UNIT, outward_protocols: vec![] }, result_type: BYTES, resumption_lower: 1, resumption_upper: Some(1), terminal: false }] },
                Protocol { display_name: "FileWrite".into(), type_arguments: vec![], operations: vec![Operation { name: "write".into(), payload_signature: Signature { params: vec![TEXT, BYTES], result: UNIT, outward_protocols: vec![] }, result_type: UNIT, resumption_lower: 1, resumption_upper: Some(1), terminal: false }] },
                Protocol { display_name: "ProcessArgs".into(), type_arguments: vec![], operations: vec![Operation { name: "get".into(), payload_signature: Signature { params: vec![], result: UNIT, outward_protocols: vec![] }, result_type: array_text, resumption_lower: 1, resumption_upper: Some(1), terminal: false }] },
            ],
            ..Artifact::default()
        };
        assert_eq!(artifact.types.len(), array_text as usize);
        artifact.types.push(Type::Array { element: TEXT });
        for (protocol, input_type) in [(0, UNIT), (1, BYTES), (2, UNIT), (3, array_text)] {
            artifact.types.push(Type::Resumption {
                input_type,
                output_type: UNIT,
                effect_signature: Signature { params: vec![], result: UNIT, outward_protocols: vec![] },
                lower_uses: 1,
                upper_uses: Some(1),
                identity_name: format!("frozen-{protocol}"),
                copy: false,
            });
        }
        artifact.handler_defs.push(HandlerDef {
            result_type: UNIT,
            partial: false,
            clauses: (0..4)
                .map(|protocol| HandlerClause {
                    protocol,
                    operation: 0,
                    callable_signature: Signature { params: vec![], result: UNIT, outward_protocols: vec![] },
                    resumption_type: Some(array_text + 1 + protocol),
                })
                .collect(),
        });
        let frame = ClosedHostHandlerFrame::build(&artifact, 0).expect("frozen handler frame");
        assert_eq!(frame.handler_def, 0);
        assert_eq!(frame.continuations.len(), 4);
        assert_eq!(
            frame.continuations.iter().map(|continuation| continuation.import).collect::<Vec<_>>(),
            vec![0, 1, 2, 3]
        );
        assert!(frame.continuations.iter().all(|continuation| continuation.resumption_type >= 20));

        artifact.protocols[0].operations[0].resumption_upper = Some(2);
        assert!(ClosedHostHandlerFrame::build(&artifact, 0).is_none());
    }

    #[test]
    fn closed_host_continuation_abi_requires_direct_empty_callables_and_frozen_effects() {
        let mut artifact = frozen_handler_artifact_for_continuation_abi();
        let abi = closed_host_handler_continuation_abis(&artifact);
        assert_eq!(abi.len(), 1);
        assert_eq!(abi[0].owner_function, 0);
        assert_eq!(abi[0].handle_instruction, 6);
        assert_eq!(abi[0].body.function, 1);
        assert_eq!(abi[0].clauses.iter().map(|callable| callable.function).collect::<Vec<_>>(), vec![2, 3, 4, 5]);

        let Instruction::MakeCallable { captures, .. } = &mut artifact.code[0] else { unreachable!() };
        captures.push(0);
        assert!(closed_host_handler_continuation_abis(&artifact).is_empty(), "a captured body is not a static continuation ABI");

        let mut artifact = frozen_handler_artifact_for_continuation_abi();
        artifact.functions[2].outward_protocols.push(99);
        assert!(closed_host_handler_continuation_abis(&artifact).is_empty(), "an effect outside the frozen handler protocol set must remain unsupported");
    }

    #[test]
    fn effect_free_closed_handle_lowers_only_its_lexical_body() {
        let artifact = frozen_handler_artifact_for_continuation_abi();
        assert_eq!(closed_handle_body_functions(&artifact), BTreeSet::from([1]));
        let owner = &artifact.functions[0];
        let body = &artifact.functions[1];
        let mut ir = String::new();
        emit_function(&mut ir, &artifact, 0, owner, false).unwrap();
        emit_function(&mut ir, &artifact, 1, body, true).unwrap();
        assert!(ir.contains("call void @grbc_fn_1()"), "{ir}");
        assert!(!ir.contains("g1_host_"), "{ir}");
        assert!(!ir.contains("MakeHandler"), "{ir}");

        let mut effectful = artifact;
        effectful.code[8] = Instruction::Perform {
            dst: None,
            protocol: 0,
            operation: 0,
            payloads: vec![],
        };
        assert!(closed_handle_body_functions(&effectful).is_empty());
    }

    #[test]
    fn closed_handle_opaque_type_admission_is_exact_and_never_admits_resumptions() {
        let artifact = frozen_handler_artifact_for_continuation_abi();
        let owner = &artifact.functions[0];
        let body_callable = owner.register_types[1];
        let resumption = artifact.handler_defs[0].clauses[0].resumption_type.unwrap();
        let opaque = closed_handle_opaque_registers(
            &artifact,
            0,
            &closed_handle_sites(&artifact, 0),
        );
        assert_eq!(opaque, BTreeSet::from([1, 2, 3, 4, 5, 6]));

        // Reusing the same callable definition in a distinct register is not
        // a lexical proof token.  It must still fail the ordinary type gate.
        let mut unrelated_callable = artifact.clone();
        unrelated_callable.functions[0].register_types.push(body_callable);
        let owner = unrelated_callable.functions[0].clone();
        assert_eq!(
            emit_function(&mut String::new(), &unrelated_callable, 0, &owner, false),
            Err(ArtifactLlvmError::UnsupportedType {
                function: 0,
                ty: body_callable,
            })
        );

        // A resumption is a live continuation capability, not an inert
        // handler/callable proof token.  Even a frozen one-shot definition is
        // not admitted until Resume itself has a precise native ABI.
        let mut resumption_register = artifact;
        resumption_register.functions[0].register_types.push(resumption);
        let owner = resumption_register.functions[0].clone();
        assert_eq!(
            emit_function(&mut String::new(), &resumption_register, 0, &owner, false),
            Err(ArtifactLlvmError::UnsupportedType {
                function: 0,
                ty: resumption,
            })
        );
    }

    #[test]
    fn closed_host_handler_plan_installs_only_the_capture_free_shared_shape() {
        let mut artifact = frozen_handler_artifact_for_continuation_abi();
        for clause in &mut artifact.handler_defs[0].clauses {
            clause.callable_signature.outward_protocols.clear();
        }
        let shared_unit = artifact.types.len() as u32;
        artifact.types.push(Type::RefShared { referent: UNIT });
        let handler = artifact.types.len() as u32;
        artifact.types.push(Type::Handler {
            handler_def: 0,
            capture_type: UNIT,
            identity_name: "closed-host".into(),
        });
        artifact.functions = (0..4)
            .map(|index| Function {
                name: format!("clause-{index}"),
                flags: 0,
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: Some(0),
                register_types: vec![shared_unit],
                code_start: 0,
                code_len: 1,
                label_slot_count: 0,
            })
            .chain(std::iter::once(Function {
                name: "plan-entry".into(),
                flags: 0,
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, handler],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }))
            .collect();
        artifact.code = vec![
            Instruction::MakeHandlerShared {
                dst: 1,
                handler_def: 0,
                functions: vec![0, 1, 2, 3],
                captures: vec![],
            },
            Instruction::Return { src: None },
        ];

        let entry = artifact.functions[4].clone();
        let plans = closed_host_handler_plans(&artifact, 4, &entry).unwrap();
        assert_eq!(plans[&1].frame.continuations.len(), 4);
        let mut ir = String::new();
        emit_function(&mut ir, &artifact, 4, &entry, false).unwrap();
        assert!(ir.contains("%closed_handler_frame_0 = alloca [5 x i1]"), "{ir}");
        assert!(ir.contains("store i1 false, ptr %closed_handler_frame_0_field_0"), "{ir}");
        assert!(ir.contains("store ptr %closed_handler_frame_0, ptr %slot1"), "{ir}");
        assert!(ir.contains("closed-host-handler-frame r1: def=0 routes=4 clauses=4 active-field=0 one-shot-fields=1..4"), "{ir}");
        assert_eq!(plans[&1].frame.native_resumption_field(0, 0), Some(1));
        assert_eq!(plans[&1].frame.native_resumption_field(3, 0), Some(4));
        let route = plans[&1].perform_route(3, 0).expect("exact frozen process-args route");
        assert_eq!(route.handler_def, 0);
        assert_eq!(route.import, 3);
        assert_eq!(route.one_shot_field, 4);
        assert_eq!(route.operation_result, 19);
        assert_eq!(route.import_result, 19);
        assert_eq!(
            closed_frame_result_transfer(&route),
            Some(ClosedFrameResultTransfer::Identity { ty: 19 })
        );
        let mut mismatched_import_result = route.clone();
        mismatched_import_result.import_result = UNIT;
        assert!(closed_frame_result_transfer(&mismatched_import_result).is_none());
        let mut mismatched_operation_result = route.clone();
        mismatched_operation_result.operation_result = BYTES;
        assert!(closed_frame_result_transfer(&mismatched_operation_result).is_none());
        let resume = closed_frame_resume_transfer(&artifact, &route, route.resumption_type, 19, UNIT)
            .expect("mapped one-shot resume transfer");
        assert_eq!(resume.handler_def, 0);
        assert_eq!(resume.one_shot_field, 4);
        assert_eq!(resume.value_type, 19);
        assert_eq!(resume.destination_type, UNIT);
        assert!(closed_frame_resume_transfer(&artifact, &route, 20, 19, UNIT).is_none());
        assert!(closed_frame_resume_transfer(&artifact, &route, route.resumption_type, UNIT, UNIT).is_none());
        assert!(closed_frame_resume_transfer(&artifact, &route, route.resumption_type, 19, BYTES).is_none());
        let mut consume_ir = String::new();
        emit_closed_frame_consume_one_shot(
            &mut consume_ir,
            "%frame",
            plans[&1].frame.native_field_count(),
            resume,
            4,
            17,
        )
        .unwrap();
        assert!(consume_ir.contains("getelementptr inbounds [5 x i1], ptr %frame, i64 0, i64 4"), "{consume_ir}");
        assert!(consume_ir.contains("br i1 %closed_frame_resume_used_17_4, label %closed_frame_resume_reused_17_4, label %closed_frame_resume_consume_17_4"), "{consume_ir}");
        assert!(consume_ir.contains("closed_frame_resume_reused_17_4:\n  unreachable"), "{consume_ir}");
        assert!(consume_ir.contains("closed_frame_resume_consume_17_4:\n  store i1 false, ptr %closed_frame_resume_field_17_4"), "{consume_ir}");
        let mut invalid_consume = resume;
        invalid_consume.one_shot_field = 0;
        assert!(matches!(
            emit_closed_frame_consume_one_shot(&mut String::new(), "%frame", 5, invalid_consume, 4, 17),
            Err(ArtifactLlvmError::UnsupportedInstruction { opcode: "closed frame resumption field", .. })
        ));
        let mut resume_ir = String::from("  ; preceding lexical scope state\n");
        assert!(matches!(
            emit_closed_frame_resume_or_reject(
                &mut resume_ir,
                &artifact,
                &route,
                route.resumption_type,
                19,
                UNIT,
                4,
                17,
            ),
            Err(ArtifactLlvmError::UnsupportedInstruction {
                function: 4,
                instruction: 17,
                opcode: "closed frame continuation state",
            })
        ));
        assert_eq!(resume_ir, "  ; preceding lexical scope state\n", "a rejected resume must not consume its one-shot field");
        assert!(matches!(
            emit_closed_frame_resume_or_reject(&mut String::new(), &artifact, &route, 20, 19, UNIT, 4, 17),
            Err(ArtifactLlvmError::UnsupportedInstruction { opcode: "closed frame resume ABI", .. })
        ));
        assert!(plans[&1].perform_route(3, 1).is_none());
        assert!(plans[&1].perform_route(9, 0).is_none());

        artifact.functions[0].receiver_mode = None;
        assert!(closed_host_handler_plans(&artifact, 4, &entry).is_err());
    }

    #[test]
    fn shared_handler_handle_restores_its_exact_lexical_scope_bit() {
        let mut artifact = frozen_handler_artifact_for_continuation_abi();
        let body_callable = artifact.functions[0].register_types[1];
        for clause in &mut artifact.handler_defs[0].clauses {
            clause.callable_signature.outward_protocols.clear();
        }
        let shared_unit = artifact.types.len() as u32;
        artifact.types.push(Type::RefShared { referent: UNIT });
        let handler = artifact.types.len() as u32;
        artifact.types.push(Type::Handler { handler_def: 0, capture_type: UNIT, identity_name: "shared-closed".into() });
        let clauses = (0..4).map(|index| Function {
            name: format!("clause-{index}"), flags: 0, params: vec![], return_type: UNIT,
            outward_protocols: vec![], receiver_mode: Some(0), register_types: vec![shared_unit],
            code_start: 0, code_len: 0, label_slot_count: 0,
        });
        let body = Function {
            name: "effect-free-body".into(), flags: 0, params: vec![], return_type: UNIT,
            outward_protocols: vec![], receiver_mode: Some(2), register_types: vec![UNIT],
            code_start: 0, code_len: 0, label_slot_count: 0,
        };
        let entry = Function {
            name: "shared-owner".into(), flags: 0, params: vec![], return_type: UNIT,
            outward_protocols: vec![], receiver_mode: None,
            register_types: vec![UNIT, handler, body_callable], code_start: 0, code_len: 4,
            label_slot_count: 0,
        };
        artifact.functions = clauses.chain(std::iter::once(body)).chain(std::iter::once(entry.clone())).collect();
        artifact.code = vec![
            Instruction::MakeCallable { dst: 2, callable_type: body_callable, function: 4, captures: vec![] },
            Instruction::MakeHandlerShared { dst: 1, handler_def: 0, functions: vec![0, 1, 2, 3], captures: vec![] },
            Instruction::Handle { dst: 0, handler: 1, body: 2, args: vec![] },
            Instruction::Return { src: None },
        ];
        let plans = closed_host_handler_plans(&artifact, 5, &entry).unwrap();
        let sites = closed_shared_handle_sites(&artifact, 5, &entry, &plans);
        assert_eq!(sites.len(), 1);
        let mut ir = String::new();
        emit_function(&mut ir, &artifact, 5, &entry, false).unwrap();
        assert!(ir.contains("store i1 true, ptr %closed_handler_active_2"), "{ir}");
        assert!(ir.contains("store i1 %closed_handler_prior_active_2, ptr %closed_handler_active_2"), "{ir}");
        assert!(ir.contains("call void @grbc_fn_4()"), "{ir}");
        assert!(!ir.contains("g1_host_"), "{ir}");

        // A copied handler is not the exact materialized frame register.
        artifact.code[2] = Instruction::Handle { dst: 0, handler: 0, body: 2, args: vec![] };
        assert!(closed_shared_handle_sites(&artifact, 5, &entry, &plans).is_empty());
    }

    #[test]
    fn prevalidated_shared_host_handler_stops_at_handle_before_perform_or_resume() {
        // This is deliberately an `emit_function` regression rather than an
        // encoded-artifact test.  `Handle`'s body is a runtime callable, for
        // which the scalar AOT type gate intentionally has no representation
        // yet.  Calling the single-function emitter lets the test prove the
        // next diagnostic *after* the existing shared-handler plan and its
        // admitted handler slot have both succeeded; it does not weaken the
        // verifier or native type admission merely to reach `Handle`.
        let mut artifact = frozen_handler_artifact_for_continuation_abi();
        for clause in &mut artifact.handler_defs[0].clauses {
            clause.callable_signature.outward_protocols.clear();
        }
        let shared_unit = artifact.types.len() as u32;
        artifact.types.push(Type::RefShared { referent: UNIT });
        let handler = artifact.types.len() as u32;
        artifact.types.push(Type::Handler {
            handler_def: 0,
            capture_type: UNIT,
            identity_name: "closed-host".into(),
        });
        // The clause functions are the future continuation targets.  Their
        // `Resume` must remain unreachable from native lowering until Handle
        // dispatch exists.
        let clauses = (0..4)
            .map(|index| Function {
                name: format!("clause-{index}"),
                flags: 0,
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: Some(0),
                register_types: vec![shared_unit, UNIT],
                code_start: 3,
                code_len: 1,
                label_slot_count: 0,
            })
            .collect::<Vec<_>>();
        // The body is likewise deliberately left for the Handle ABI.  Its
        // frozen host Perform is not permission for a process-global call.
        let body = Function {
            name: "body".into(),
            flags: 0,
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![0],
            receiver_mode: Some(0),
            register_types: vec![shared_unit, UNIT],
            code_start: 2,
            code_len: 1,
            label_slot_count: 0,
        };
        let entry = Function {
            name: "plan-entry".into(),
            flags: 0,
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            // r1 is the only non-scalar register and is accepted solely by
            // the already-validated closed-handler-plan exception.
            register_types: vec![UNIT, handler],
            code_start: 0,
            code_len: 2,
            label_slot_count: 0,
        };
        artifact.functions = clauses
            .into_iter()
            .chain(std::iter::once(body))
            .chain(std::iter::once(entry.clone()))
            .collect();
        artifact.code = vec![
            Instruction::MakeHandlerShared {
                dst: 1,
                handler_def: 0,
                functions: vec![0, 1, 2, 3],
                captures: vec![],
            },
            // r0 is intentionally inert here: Handle rejects before reading
            // its callable operand, and a scalar stand-in avoids granting a
            // callable native representation in this regression fixture.
            Instruction::Handle { dst: 0, handler: 1, body: 0, args: vec![] },
            Instruction::Perform { dst: Some(1), protocol: 0, operation: 0, payloads: vec![] },
            Instruction::Resume { dst: 1, resumption: 0, receiver_mode: 0, value: 1 },
        ];

        let mut ir = String::new();
        assert_eq!(
            emit_function(&mut ir, &artifact, 5, &entry, false),
            Err(ArtifactLlvmError::UnsupportedInstruction {
                function: 5,
                instruction: 1,
                opcode: "closed effect-free handle",
            })
        );
        assert!(ir.contains("closed-host-handler-frame r1"), "{ir}");
    }

    #[test]
    fn shared_perform_consumes_exact_one_shot_frame_bit_then_faults_without_host_or_resume() {
        let mut artifact = frozen_handler_artifact_for_continuation_abi();
        for clause in &mut artifact.handler_defs[0].clauses {
            clause.callable_signature.outward_protocols.clear();
        }
        let shared_unit = artifact.types.len() as u32;
        artifact.types.push(Type::RefShared { referent: UNIT });
        let handler = artifact.types.len() as u32;
        artifact.types.push(Type::Handler {
            handler_def: 0,
            capture_type: UNIT,
            identity_name: "closed-host".into(),
        });
        let body_callable = artifact.types.len() as u32;
        artifact.types.push(Type::Callable {
            signature: Signature { params: vec![], result: UNIT, outward_protocols: vec![0] },
            capture_type: UNIT,
            receiver_mode: 0,
            identity_name: "perform-body".into(),
            copy: false,
            zero_use_allowed: true,
        });
        let clauses = (0..4).map(|index| Function {
            name: format!("clause-{index}"), flags: 0, params: vec![], return_type: UNIT,
            outward_protocols: vec![], receiver_mode: Some(0), register_types: vec![shared_unit],
            code_start: 6, code_len: 0, label_slot_count: 0,
        }).collect::<Vec<_>>();
        let body = Function {
            name: "perform-body".into(), flags: 0, params: vec![], return_type: UNIT,
            outward_protocols: vec![0], receiver_mode: Some(0), register_types: vec![shared_unit, UNIT],
            code_start: 4, code_len: 2, label_slot_count: 0,
        };
        let owner = Function {
            name: "owner".into(), flags: 0, params: vec![], return_type: UNIT,
            outward_protocols: vec![], receiver_mode: None,
            register_types: vec![UNIT, handler, body_callable, UNIT],
            code_start: 0, code_len: 4, label_slot_count: 0,
        };
        artifact.functions = clauses.into_iter().chain(std::iter::once(body)).chain(std::iter::once(owner.clone())).collect();
        artifact.code = vec![
            Instruction::MakeHandlerShared { dst: 1, handler_def: 0, functions: vec![0, 1, 2, 3], captures: vec![] },
            Instruction::MakeCallable { dst: 2, callable_type: body_callable, function: 4, captures: vec![] },
            Instruction::Handle { dst: 3, handler: 1, body: 2, args: vec![] },
            Instruction::Return { src: None },
            Instruction::Perform { dst: None, protocol: 0, operation: 0, payloads: vec![] },
            Instruction::Return { src: None },
        ];

        let dispatches = closed_shared_perform_dispatches(&artifact, 5);
        assert_eq!(dispatches.len(), 1);
        assert_eq!(dispatches[0].handler_instruction, 0);
        assert_eq!(dispatches[0].handle_instruction, 2);
        assert_eq!(dispatches[0].body_register, 2);
        assert_eq!(dispatches[0].body_function, 4);
        assert_eq!(dispatches[0].perform_instruction, 0);
        assert_eq!(dispatches[0].resumption_field, 1);
        assert_eq!(dispatches[0].continuation.import, 0);
        assert_eq!(closed_shared_perform_consume_sites(&artifact, 5).len(), 1);
        let mut ir = String::new();
        let emission = emit_function(&mut ir, &artifact, 5, &owner, false);
        assert!(emission.is_ok(), "{emission:?} {ir}");
        assert!(ir.contains("closed-host-perform-dispatch handle=2 body=4 perform=0 route=(0, 0) frame-field=1 import=0"), "{ir}");
        assert!(ir.contains("store i1 true, ptr %closed_perform_active_2"), "{ir}");
        assert!(ir.contains("%closed_perform_used_2 = getelementptr inbounds [5 x i1], ptr"), "{ir}");
        assert!(ir.contains("store i1 true, ptr %closed_perform_used_2"), "{ir}");
        assert!(ir.contains("closed_perform_reject_2"), "{ir}");
        assert!(ir.contains("call void @g1_runtime_fault(i32 1, i32 5, i32 2, ptr null"), "{ir}");
        assert!(!ir.contains("g1_host_"), "{ir}");
        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("closed-perform.ll");
        let object = directory.path().join("closed-perform.o");
        let width = pointer_width_for_target(&default_target_triple());
        fs::write(&source, format!("{}\n{ir}", runtime_fault_declaration(width))).unwrap();
        assert!(Command::new("clang")
            .args(["-x", "ir", "-c"])
            .arg(&source)
            .arg("-o")
            .arg(&object)
            .status()
            .unwrap()
            .success());

        // Adding the statically typed Text payload makes this route eligible
        // for frozen-host call preparation, but it does not make it
        // executable: no native Perform value or Resume transfer exists yet.
        artifact.functions[4].register_types[1] = TEXT;
        let Instruction::Perform { payloads, .. } = &mut artifact.code[4] else { unreachable!() };
        payloads.push(1);
        let preparations = prepared_shared_host_calls(&artifact, 5);
        assert_eq!(preparations.len(), 1);
        assert_eq!(preparations[0].import, 0);
        assert_eq!(preparations[0].symbol, "g1_host_diagnostic_write");
        assert_eq!(preparations[0].abi, "(ptr) -> i32");
        let mut declarations = String::new();
        emit_host_import_declarations(&mut declarations, &artifact);
        assert!(declarations.contains("declare i32 @g1_host_diagnostic_write(ptr)"), "{declarations}");
        let mut prepared_ir = String::new();
        assert!(matches!(emit_function(&mut prepared_ir, &artifact, 5, &owner, false),
            Err(ArtifactLlvmError::UnsupportedInstruction { instruction: 2, opcode: "closed effect-free handle", .. })
        ));
        assert!(prepared_ir.contains("prepared-frozen-host-call body=4 perform=0 import=0 symbol=g1_host_diagnostic_write abi=(ptr) -> i32"), "{prepared_ir}");
        assert!(!prepared_ir.contains("call i32 @g1_host_diagnostic_write"), "{prepared_ir}");

        artifact.code.swap(0, 1);
        assert!(closed_shared_perform_dispatches(&artifact, 5).is_empty(), "a frame must be installed before its exact lexical body/Handle chain");
        artifact.code.swap(0, 1);
        let Instruction::Perform { protocol, .. } = &mut artifact.code[4] else { unreachable!() };
        *protocol = 99;
        assert!(closed_shared_perform_dispatches(&artifact, 5).is_empty(), "non-frozen routes must not acquire a native dispatch");
    }

    fn frozen_handler_artifact_for_continuation_abi() -> Artifact {
        let array_text = 19;
        let mut artifact = Artifact {
            required_features: 1 | (1 << 5),
            imports: vec![
                Import { capability: "diagnostic".into(), symbol: "write".into(), signature: Signature { params: vec![TEXT], result: UNIT, outward_protocols: vec![] }, may_trap: true },
                Import { capability: "fs.read".into(), symbol: "read".into(), signature: Signature { params: vec![TEXT], result: BYTES, outward_protocols: vec![] }, may_trap: true },
                Import { capability: "fs.write".into(), symbol: "write".into(), signature: Signature { params: vec![TEXT, BYTES], result: UNIT, outward_protocols: vec![] }, may_trap: true },
                Import { capability: "process.args".into(), symbol: "get".into(), signature: Signature { params: vec![], result: array_text, outward_protocols: vec![] }, may_trap: true },
            ],
            protocols: vec![
                Protocol { display_name: "Diagnostic".into(), type_arguments: vec![], operations: vec![Operation { name: "write".into(), payload_signature: Signature { params: vec![TEXT], result: UNIT, outward_protocols: vec![] }, result_type: UNIT, resumption_lower: 1, resumption_upper: Some(1), terminal: false }] },
                Protocol { display_name: "FileRead".into(), type_arguments: vec![], operations: vec![Operation { name: "read".into(), payload_signature: Signature { params: vec![TEXT], result: UNIT, outward_protocols: vec![] }, result_type: BYTES, resumption_lower: 1, resumption_upper: Some(1), terminal: false }] },
                Protocol { display_name: "FileWrite".into(), type_arguments: vec![], operations: vec![Operation { name: "write".into(), payload_signature: Signature { params: vec![TEXT, BYTES], result: UNIT, outward_protocols: vec![] }, result_type: UNIT, resumption_lower: 1, resumption_upper: Some(1), terminal: false }] },
                Protocol { display_name: "ProcessArgs".into(), type_arguments: vec![], operations: vec![Operation { name: "get".into(), payload_signature: Signature { params: vec![], result: UNIT, outward_protocols: vec![] }, result_type: array_text, resumption_lower: 1, resumption_upper: Some(1), terminal: false }] },
            ],
            ..Artifact::default()
        };
        artifact.types.push(Type::Array { element: TEXT });
        for (protocol, input_type) in [(0, UNIT), (1, BYTES), (2, UNIT), (3, array_text)] {
            artifact.types.push(Type::Resumption { input_type, output_type: UNIT, effect_signature: Signature { params: vec![], result: UNIT, outward_protocols: vec![] }, lower_uses: 1, upper_uses: Some(1), identity_name: format!("frozen-{protocol}"), copy: false });
        }
        artifact.handler_defs.push(HandlerDef {
            result_type: UNIT,
            partial: false,
            clauses: (0..4).map(|protocol| HandlerClause {
                protocol,
                operation: 0,
                callable_signature: Signature { params: vec![], result: UNIT, outward_protocols: vec![protocol] },
                resumption_type: Some(array_text + 1 + protocol),
            }).collect(),
        });
        let empty_capture = artifact.types.len() as u32;
        artifact.types.push(Type::Tuple { fields: vec![], copy: true });
        let clause_types = (0..4).map(|protocol| {
            let ty = artifact.types.len() as u32;
            artifact.types.push(Type::Callable { signature: Signature { params: vec![], result: UNIT, outward_protocols: vec![protocol] }, capture_type: empty_capture, receiver_mode: 2, identity_name: format!("clause-{protocol}"), copy: false, zero_use_allowed: true });
            ty
        }).collect::<Vec<_>>();
        let body_type = artifact.types.len() as u32;
        artifact.types.push(Type::Callable { signature: Signature { params: vec![], result: UNIT, outward_protocols: vec![] }, capture_type: empty_capture, receiver_mode: 2, identity_name: "body".into(), copy: false, zero_use_allowed: true });
        let handler_capture = artifact.types.len() as u32;
        artifact.types.push(Type::Tuple { fields: clause_types.clone(), copy: false });
        let handler_type = artifact.types.len() as u32;
        artifact.types.push(Type::Handler { handler_def: 0, capture_type: handler_capture, identity_name: "frozen".into() });
        artifact.functions = vec![
            Function { name: "owner".into(), flags: 0, params: vec![], return_type: UNIT, outward_protocols: vec![], receiver_mode: None, register_types: vec![UNIT, body_type, clause_types[0], clause_types[1], clause_types[2], clause_types[3], handler_type, UNIT], code_start: 0, code_len: 8, label_slot_count: 0 },
            Function { name: "body".into(), flags: 0, params: vec![], return_type: UNIT, outward_protocols: vec![], receiver_mode: Some(2), register_types: vec![UNIT], code_start: 8, code_len: 1, label_slot_count: 0 },
            Function { name: "diagnostic".into(), flags: 0, params: vec![], return_type: UNIT, outward_protocols: vec![0], receiver_mode: Some(2), register_types: vec![UNIT], code_start: 9, code_len: 0, label_slot_count: 0 },
            Function { name: "read".into(), flags: 0, params: vec![], return_type: UNIT, outward_protocols: vec![1], receiver_mode: Some(2), register_types: vec![UNIT], code_start: 9, code_len: 0, label_slot_count: 0 },
            Function { name: "write".into(), flags: 0, params: vec![], return_type: UNIT, outward_protocols: vec![2], register_types: vec![UNIT], receiver_mode: Some(2), code_start: 9, code_len: 0, label_slot_count: 0 },
            Function { name: "args".into(), flags: 0, params: vec![], return_type: UNIT, outward_protocols: vec![3], receiver_mode: Some(2), register_types: vec![UNIT], code_start: 9, code_len: 0, label_slot_count: 0 },
        ];
        artifact.code = vec![
            Instruction::MakeCallable { dst: 1, callable_type: body_type, function: 1, captures: vec![] },
            Instruction::MakeCallable { dst: 2, callable_type: clause_types[0], function: 2, captures: vec![] },
            Instruction::MakeCallable { dst: 3, callable_type: clause_types[1], function: 3, captures: vec![] },
            Instruction::MakeCallable { dst: 4, callable_type: clause_types[2], function: 4, captures: vec![] },
            Instruction::MakeCallable { dst: 5, callable_type: clause_types[3], function: 5, captures: vec![] },
            Instruction::MakeHandler { dst: 6, handler_def: 0, clauses: vec![2, 3, 4, 5] },
            Instruction::Handle { dst: 7, handler: 6, body: 1, args: vec![] },
            Instruction::Return { src: None },
            Instruction::Return { src: None },
        ];
        artifact
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
