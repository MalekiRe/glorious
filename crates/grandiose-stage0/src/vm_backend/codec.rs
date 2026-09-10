//! Canonical Stage 0 artifact encoding and bounded, untrusted-input decoding.
//! Decoding produces candidates; semantic verification remains a separate gate.

use std::collections::BTreeMap;
mod decode;
mod instruction;
use super::{
    CandidateVmArtifact, CandidateVmProgram, VmArtifactError, VmCaptureEnvironment, VmCaptureMode,
    VmEffectInstance, VmEffectRow, VmEffectRowProjection, VmFunction, VmGenericArgument,
    VmNominalCopyDescriptor, VmType,
};
use crate::{
    identity::{DefKey, Digest},
    types::{
        ConstKind, EffectTail, Lifetime, PointerMutability, Safety, ScalarType, IntegerConstExpr,
    },
};
use decode::Decoder;
use instruction::encode_instruction;

/// Stable, bounded Stage 0 candidate-artifact envelope. The payload is an
/// implementation-local stepping stone rather than the repository's released
/// G1 `.grbc` container; it exists so cache/process boundaries are decoded and
/// independently verified before the VM can see an execution image.
pub const STAGE0_ARTIFACT_MAGIC: [u8; 8] = *b"G0VM\r\n\x1a\n";
pub const STAGE0_PROGRAM_MAGIC: [u8; 8] = *b"G0VP\r\n\x1a\n";
/// Exact schema of this implementation-local envelope. Earlier schemas are
/// rejected, never interpreted using the current instruction or type layout.
// Schema 116 retains independently verified shared/unique callable receiver
// authority alongside the schema-115 fixed-array representation.
// Schema 117 distinguishes optional one-shot cancellation and carries the
// protected ownership partition for all owned handler policies.
pub const STAGE0_VM_SCHEMA: u32 = 117;
/// Static process-boundary decoding caps, enforced before vector allocation.
pub const STAGE0_MAX_DECODE_FUNCTIONS: u64 = 1 << 16;
pub const STAGE0_MAX_DECODE_REGISTERS: u64 = 1 << 20;
pub const STAGE0_MAX_DECODE_INSTRUCTIONS: u64 = 1 << 22;
pub const STAGE0_MAX_DECODE_TEXT_BYTES: u64 = 1 << 26;
const MAX_DECODE_FUNCTIONS: u64 = STAGE0_MAX_DECODE_FUNCTIONS;
const MAX_DECODE_REGISTERS: u64 = STAGE0_MAX_DECODE_REGISTERS;
const MAX_DECODE_INSTRUCTIONS: u64 = STAGE0_MAX_DECODE_INSTRUCTIONS;
const MAX_DECODE_TEXT_BYTES: u64 = STAGE0_MAX_DECODE_TEXT_BYTES;
// Callable ABI rows make each decoded type frame materially larger. Keep the
// hostile-artifact bound below the process stack budget while still allowing
// far deeper type nesting than any Stage 0 source construct needs.
const MAX_DECODE_TYPE_DEPTH: u64 = 96;

pub fn encode_artifact(artifact: &CandidateVmArtifact) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&STAGE0_ARTIFACT_MAGIC);
    bytes.extend_from_slice(&artifact.schema.to_le_bytes());
    bytes.extend_from_slice(&artifact.fingerprint.as_bytes());
    encode_optional_digest(artifact.runtime_manifest, &mut bytes);
    let payload_start = bytes.len() + 8;
    bytes.resize(payload_start, 0);
    encode_function(&artifact.function, &mut bytes);
    let payload_len = (bytes.len() - payload_start) as u64;
    let payload_length_offset = payload_start - 8;
    bytes[payload_length_offset..payload_start].copy_from_slice(&payload_len.to_le_bytes());
    bytes
}

pub fn decode_artifact(bytes: &[u8]) -> Result<CandidateVmArtifact, VmArtifactError> {
    let mut decoder = Decoder::new(bytes);
    if decoder.bytes(8)? != STAGE0_ARTIFACT_MAGIC {
        return Err(VmArtifactError::MalformedEncoding {
            message: "invalid Stage 0 artifact magic",
        });
    }
    let schema = decoder.u32()?;
    if schema != STAGE0_VM_SCHEMA {
        return Err(VmArtifactError::UnsupportedSchema { found: schema });
    }
    let fingerprint = Digest::from_bytes(decoder.array()?);
    let runtime_manifest = decoder.optional_digest()?;
    let payload_len = decoder.u64()?;
    if payload_len != decoder.remaining() as u64 {
        return Err(VmArtifactError::MalformedEncoding {
            message: "artifact payload length does not match input length",
        });
    }
    let function = decoder.function()?;
    if decoder.remaining() != 0 {
        return Err(VmArtifactError::MalformedEncoding {
            message: "trailing bytes after artifact payload",
        });
    }
    let artifact = CandidateVmArtifact {
        schema,
        runtime_manifest,
        function,
        fingerprint,
    };
    if encode_artifact(&artifact) != bytes {
        return Err(VmArtifactError::NonCanonicalEncoding);
    }
    Ok(artifact)
}

pub fn encode_program(program: &CandidateVmProgram) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&STAGE0_PROGRAM_MAGIC);
    bytes.extend_from_slice(&program.schema.to_le_bytes());
    bytes.extend_from_slice(&program.entry.0.as_bytes());
    bytes.extend_from_slice(&program.fingerprint.as_bytes());
    encode_optional_digest(program.runtime_manifest, &mut bytes);
    bytes.extend_from_slice(&(program.host_capabilities.len() as u64).to_le_bytes());
    for capability in &program.host_capabilities {
        bytes.extend_from_slice(&(capability.len() as u64).to_le_bytes());
        bytes.extend_from_slice(capability.as_bytes());
    }
    bytes.extend_from_slice(&(program.functions.len() as u64).to_le_bytes());
    for function in program.functions.values() {
        encode_function(function, &mut bytes);
    }
    bytes.extend_from_slice(&(program.callable_environments.len() as u64).to_le_bytes());
    for (callee, environment) in &program.callable_environments {
        bytes.extend_from_slice(&callee.0.as_bytes());
        encode_capture_environment(Some(environment), &mut bytes);
    }
    bytes
}

pub fn decode_program(bytes: &[u8]) -> Result<CandidateVmProgram, VmArtifactError> {
    let mut decoder = Decoder::new(bytes);
    if decoder.bytes(8)? != STAGE0_PROGRAM_MAGIC {
        return Err(VmArtifactError::MalformedEncoding {
            message: "invalid Stage 0 program magic",
        });
    }
    let schema = decoder.u32()?;
    if schema != STAGE0_VM_SCHEMA {
        return Err(VmArtifactError::UnsupportedSchema { found: schema });
    }
    let entry = decoder.def_key()?;
    let fingerprint = Digest::from_bytes(decoder.array()?);
    let runtime_manifest = decoder.optional_digest()?;
    let capability_count = decoder.count("host capabilities", MAX_DECODE_REGISTERS)?;
    let mut host_capabilities = Vec::with_capacity(capability_count);
    for _ in 0..capability_count {
        host_capabilities.push(decoder.text()?);
    }
    let count = decoder.count("functions", MAX_DECODE_FUNCTIONS)?;
    let mut functions = BTreeMap::new();
    for _ in 0..count {
        let function = decoder.function()?;
        if functions.insert(function.definition, function).is_some() {
            return Err(VmArtifactError::MalformedEncoding {
                message: "duplicate function definition in program",
            });
        }
    }
    let environment_count = decoder.count("callable environment registry", MAX_DECODE_FUNCTIONS)?;
    let mut callable_environments = BTreeMap::new();
    for _ in 0..environment_count {
        let callee = decoder.def_key()?;
        let Some(environment) = decoder.capture_environment()? else {
            return Err(VmArtifactError::MalformedEncoding {
                message: "callable environment registry contains an absent layout",
            });
        };
        if callable_environments.insert(callee, environment).is_some() {
            return Err(VmArtifactError::MalformedEncoding {
                message: "duplicate callable environment target in program",
            });
        }
    }
    if decoder.remaining() != 0 {
        return Err(VmArtifactError::MalformedEncoding {
            message: "trailing bytes after program payload",
        });
    }
    let program = CandidateVmProgram {
        schema,
        runtime_manifest,
        host_capabilities,
        entry,
        functions,
        callable_environments,
        fingerprint,
    };
    if encode_program(&program) != bytes {
        return Err(VmArtifactError::NonCanonicalEncoding);
    }
    Ok(program)
}

pub(super) fn encode_integer_scalar(value: ScalarType) -> Option<u8> {
    Some(match value {
        ScalarType::U8 => 0,
        ScalarType::U16 => 1,
        ScalarType::U32 => 2,
        ScalarType::U64 => 3,
        ScalarType::U128 => 4,
        ScalarType::Usize => 5,
        ScalarType::I8 => 6,
        ScalarType::I16 => 7,
        ScalarType::I32 => 8,
        ScalarType::I64 => 9,
        ScalarType::I128 => 10,
        ScalarType::Isize => 11,
        _ => return None,
    })
}

fn decode_integer_scalar(value: u8) -> Result<ScalarType, VmArtifactError> {
    Ok(match value {
        0 => ScalarType::U8,
        1 => ScalarType::U16,
        2 => ScalarType::U32,
        3 => ScalarType::U64,
        4 => ScalarType::U128,
        5 => ScalarType::Usize,
        6 => ScalarType::I8,
        7 => ScalarType::I16,
        8 => ScalarType::I32,
        9 => ScalarType::I64,
        10 => ScalarType::I128,
        11 => ScalarType::Isize,
        _ => {
            return Err(VmArtifactError::MalformedEncoding {
                message: "invalid integer runtime scalar",
            });
        }
    })
}

pub(super) fn encode_type(value: &VmType, output: &mut Vec<u8>) {
    output.push(match value {
        VmType::Unit => 0,
        VmType::I64 => 1,
        VmType::Usize => 16,
        VmType::U32 => 17,
        VmType::U8 => 19,
        VmType::U16 => 20,
        VmType::I16 => 21,
        VmType::I32 => 22,
        VmType::I8 => 23,
        VmType::U64 => 24,
        VmType::Isize => 25,
        VmType::U128 => 26,
        VmType::I128 => 27,
        VmType::F32 => 28,
        VmType::F64 => 2,
        VmType::Bool => 3,
        VmType::Char => 4,
        VmType::Text => 5,
        VmType::Bytes => 18,
        VmType::Generic(_) => 9,
        VmType::Array(_) => 10,
        VmType::FixedArray { .. } => 32,
        VmType::Callable {
            safety: Safety::Safe,
            ..
        } => 6,
        VmType::Callable {
            safety: Safety::Unsafe,
            ..
        } => 30,
        VmType::RawPointer { .. } => 31,
        VmType::Tuple(_) => 7,
        VmType::Nominal { .. } => 8,
        VmType::Reference { .. } => 11,
        VmType::ConstInteger(_) => 12,
        VmType::ConstIntegerExpr(_) => 13,
        VmType::ConstQuantity { .. } => 14,
        VmType::ConstGeneric { .. } => 15,
        VmType::StaticData { .. } => 29,
    });
    match value {
        VmType::Callable {
            shared_receiver,
            unique_receiver,
            parameters,
            result,
            effects,
            ..
        } => {
            output.push(u8::from(*shared_receiver));
            output.push(u8::from(*unique_receiver));
            output.extend_from_slice(&(parameters.len() as u64).to_le_bytes());
            for parameter in parameters {
                encode_type(parameter, output);
            }
            encode_type(result, output);
            encode_vm_effect_row(effects, output);
        }
        VmType::Tuple(fields) => {
            output.extend_from_slice(&(fields.len() as u64).to_le_bytes());
            for field in fields {
                encode_type(field, output);
            }
        }
        VmType::Nominal {
            definition,
            arguments,
        } => {
            output.extend_from_slice(&definition.0.as_bytes());
            output.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                encode_vm_generic_argument(argument, output);
            }
        }
        VmType::RawPointer {
            mutability,
            pointee,
        } => {
            output.push(u8::from(*mutability == PointerMutability::Mut));
            encode_type(pointee, output);
        }
        VmType::Generic(index) => output.extend_from_slice(&index.to_le_bytes()),
        VmType::ConstInteger(value) => output.extend_from_slice(&value.canonical_bytes()),
        VmType::ConstIntegerExpr(value) => encode_vm_structural_integer_expr(value, output),
        VmType::ConstQuantity { lower, upper } => {
            output.extend_from_slice(&lower.to_le_bytes());
            match upper {
                Some(upper) => {
                    output.push(0);
                    output.extend_from_slice(&upper.to_le_bytes());
                }
                None => output.push(1),
            }
        }
        VmType::ConstGeneric { index, kind } => {
            output.extend_from_slice(&index.to_le_bytes());
            output.push(encode_const_kind(*kind));
        }
        VmType::Reference { unique, referent } => {
            output.push(*unique as u8);
            encode_type(referent, output);
        }
        VmType::StaticData {
            element,
            tag,
            alignment,
        } => {
            encode_type(element, output);
            output.extend_from_slice(&tag.to_le_bytes());
            output.extend_from_slice(&alignment.to_le_bytes());
        }
        VmType::Array(element) => encode_type(element, output),
        VmType::FixedArray { element, length } => {
            encode_type(element, output);
            output.extend_from_slice(&length.to_le_bytes());
        }
        _ => {}
    }
}

fn encode_const_kind(kind: ConstKind) -> u8 {
    kind.tag()
}

fn decode_const_kind(tag: u8) -> Result<ConstKind, VmArtifactError> {
    ConstKind::from_tag(tag).ok_or(VmArtifactError::MalformedEncoding {
            message: "invalid const generic kind",
        })
}

fn encode_vm_structural_integer_expr(value: &IntegerConstExpr, output: &mut Vec<u8>) {
    value.encode(output);
}

fn encode_capture_environment(value: Option<&VmCaptureEnvironment>, output: &mut Vec<u8>) {
    match value {
        None => output.push(0),
        Some(value) => {
            output.push(1);
            output.extend_from_slice(&value.owner.0.as_bytes());
            output.extend_from_slice(&value.callable.to_le_bytes());
            encode_optional_digest(value.instance, output);
            encode_optional_digest(value.destructor.map(|key| key.0), output);
            output.extend_from_slice(&(value.captures.len() as u64).to_le_bytes());
            for capture in &value.captures {
                output.push(match capture.mode {
                    VmCaptureMode::SharedBorrow => 0,
                    VmCaptureMode::UniqueBorrow => 1,
                    VmCaptureMode::Copy => 2,
                    VmCaptureMode::Move => 3,
                });
                encode_type(&capture.ty, output);
            }
        }
    }
}

fn encode_vm_generic_argument(value: &VmGenericArgument, output: &mut Vec<u8>) {
    match value {
        VmGenericArgument::Type(value) => {
            output.push(0);
            encode_type(value, output);
        }
        VmGenericArgument::EffectRow(value) => {
            output.push(1);
            encode_vm_effect_row(value, output);
        }
        VmGenericArgument::Lifetime(value) => {
            output.push(2);
            match value {
                Lifetime::Infer(variable) => {
                    // Reserved, rejected by the decoder and validator. A
                    // candidate containing inference is never executable.
                    output.push(4);
                    output.extend_from_slice(&variable.0.to_le_bytes());
                }
                Lifetime::Static => output.push(0),
                Lifetime::Generic(index) => {
                    output.push(1);
                    output.extend_from_slice(&index.to_le_bytes());
                }
                Lifetime::Bound { depth, index } => {
                    output.push(2);
                    output.extend_from_slice(&depth.to_le_bytes());
                    output.extend_from_slice(&index.to_le_bytes());
                }
                Lifetime::Elided => output.push(3),
                Lifetime::Inferred(region) => {
                    // Source-body identities must be erased before emission.
                    // Reserve a rejecting wire tag, as for inference cells.
                    output.push(6);
                    output.extend_from_slice(&region.owner.0.as_bytes());
                    output.extend_from_slice(&region.index.to_le_bytes());
                }
                Lifetime::Placeholder(region) => {
                    // Reserved, like Infer above: neither the decoder nor
                    // the validator admits proof-local regions to bytecode.
                    output.push(5);
                    output.extend_from_slice(&region.universe.to_le_bytes());
                    output.extend_from_slice(&region.index.to_le_bytes());
                }
            }
        }
        VmGenericArgument::ConstInteger(value) => {
            output.push(3);
            output.extend_from_slice(&value.canonical_bytes());
        }
        VmGenericArgument::ConstIntegerExpr(value) => {
            output.push(6);
            encode_vm_structural_integer_expr(value, output);
        }
        VmGenericArgument::ConstQuantity { lower, upper } => {
            output.push(4);
            output.extend_from_slice(&lower.to_le_bytes());
            match upper {
                Some(upper) => {
                    output.push(0);
                    output.extend_from_slice(&upper.to_le_bytes());
                }
                None => output.push(1),
            }
        }
        VmGenericArgument::ConstGeneric { index, kind } => {
            output.push(5);
            output.extend_from_slice(&index.to_le_bytes());
            output.push(encode_const_kind(*kind));
        }
    }
}

#[inline(never)]
fn encode_vm_effect_row(value: &VmEffectRow, output: &mut Vec<u8>) {
    output.extend_from_slice(&(value.effects.len() as u64).to_le_bytes());
    for effect in &value.effects {
        output.extend_from_slice(&effect.definition.0.as_bytes());
        encode_vm_generic_arguments(&effect.arguments, output);
    }
    output.extend_from_slice(&(value.projections.len() as u64).to_le_bytes());
    for projection in &value.projections {
        encode_type(&projection.subject, output);
        output.extend_from_slice(&projection.trait_definition.0.as_bytes());
        encode_vm_generic_arguments(&projection.trait_arguments, output);
        output.extend_from_slice(&(projection.name.len() as u64).to_le_bytes());
        output.extend_from_slice(projection.name.as_bytes());
        encode_vm_generic_arguments(&projection.item_arguments, output);
    }
    output.extend_from_slice(&(value.tails.len() as u64).to_le_bytes());
    for tail in &value.tails { match tail {
        EffectTail::Infer(variable) => {
            output.push(0);
            output.extend_from_slice(&variable.0.to_le_bytes());
        }
        EffectTail::Generic(index) => {
            output.push(1);
            output.extend_from_slice(&index.to_le_bytes());
        }
    } }
}

fn encode_vm_generic_arguments(values: &[VmGenericArgument], output: &mut Vec<u8>) {
    output.extend_from_slice(&(values.len() as u64).to_le_bytes());
    for value in values {
        encode_vm_generic_argument(value, output);
    }
}

pub(super) fn vm_effect_instance_key(value: &VmEffectInstance) -> Vec<u8> {
    let mut output = value.definition.0.as_bytes().to_vec();
    encode_vm_generic_arguments(&value.arguments, &mut output);
    output
}

pub(super) fn vm_effect_row_projection_key(value: &VmEffectRowProjection) -> Vec<u8> {
    let mut output = Vec::new();
    encode_type(&value.subject, &mut output);
    output.extend_from_slice(&value.trait_definition.0.as_bytes());
    encode_vm_generic_arguments(&value.trait_arguments, &mut output);
    output.extend_from_slice(&(value.name.len() as u64).to_le_bytes());
    output.extend_from_slice(value.name.as_bytes());
    encode_vm_generic_arguments(&value.item_arguments, &mut output);
    output
}

fn encode_optional_digest(value: Option<Digest>, output: &mut Vec<u8>) {
    match value {
        None => output.push(0),
        Some(value) => {
            output.push(1);
            output.extend_from_slice(&value.as_bytes());
        }
    }
}
pub(super) fn artifact_fingerprint(
    runtime_manifest: Option<Digest>,
    function: &VmFunction,
) -> Digest {
    let mut bytes = b"grandiose-stage0-vm-v27".to_vec();
    encode_optional_digest(runtime_manifest, &mut bytes);
    encode_function(function, &mut bytes);
    Digest::of_bytes(&bytes)
}
pub(super) fn program_fingerprint(
    entry: DefKey,
    runtime_manifest: Option<Digest>,
    host_capabilities: &[String],
    functions: &BTreeMap<DefKey, VmFunction>,
    callable_environments: &BTreeMap<DefKey, VmCaptureEnvironment>,
) -> Digest {
    let mut bytes = b"grandiose-stage0-vm-program-v28".to_vec();
    bytes.extend_from_slice(&entry.0.as_bytes());
    encode_optional_digest(runtime_manifest, &mut bytes);
    bytes.extend_from_slice(&(host_capabilities.len() as u64).to_le_bytes());
    for capability in host_capabilities {
        bytes.extend_from_slice(&(capability.len() as u64).to_le_bytes());
        bytes.extend_from_slice(capability.as_bytes());
    }
    for function in functions.values() {
        encode_function(function, &mut bytes);
    }
    for (callee, environment) in callable_environments {
        bytes.extend_from_slice(&callee.0.as_bytes());
        encode_capture_environment(Some(environment), &mut bytes);
    }
    Digest::of_bytes(&bytes)
}
pub(super) fn encode_function(function: &VmFunction, output: &mut Vec<u8>) {
    output.extend_from_slice(&function.definition.0.as_bytes());
    output.push(u8::from(function.safety == Safety::Unsafe));
    output.push(u8::from(function.unsafe_execution));
    output.extend_from_slice(&function.captures.to_le_bytes());
    output.extend_from_slice(&function.parameters.to_le_bytes());
    output.extend_from_slice(&(function.registers.len() as u64).to_le_bytes());
    for register in &function.registers {
        encode_type(register, output);
    }
    output.extend_from_slice(&(function.nominal_copy_descriptors.len() as u64).to_le_bytes());
    for descriptor in &function.nominal_copy_descriptors {
        output.extend_from_slice(&descriptor.definition.0.as_bytes());
        output.extend_from_slice(&descriptor.source_contract.as_bytes());
        output.push(u8::from(descriptor.is_enum));
        output.extend_from_slice(&(descriptor.arguments.len() as u64).to_le_bytes());
        for argument in &descriptor.arguments {
            encode_vm_generic_argument(argument, output);
        }
        output.extend_from_slice(&(descriptor.variants.len() as u64).to_le_bytes());
        for variant in &descriptor.variants {
            output.extend_from_slice(&(variant.len() as u64).to_le_bytes());
            for field in variant {
                encode_type(field, output);
            }
        }
    }
    output.extend_from_slice(&(function.instructions.len() as u64).to_le_bytes());
    for instruction in &function.instructions {
        encode_instruction(instruction, output);
    }
}

pub(crate) fn vm_nominal_copy_descriptor_key(descriptor: &VmNominalCopyDescriptor) -> Vec<u8> {
    let mut output = descriptor.definition.0.as_bytes().to_vec();
    output.extend_from_slice(&(descriptor.arguments.len() as u64).to_le_bytes());
    for argument in &descriptor.arguments {
        encode_vm_generic_argument(argument, &mut output);
    }
    output
}
