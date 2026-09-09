//! Production LIR cannot inherit the generic fixture language accepted by the
//! legacy artifact checker. Check closure directly in VM-owned metadata, with
//! no compiler types, substitutions or interface queries.
use super::*;
use crate::vm_backend::{VmEffectRow, VmGenericArgument, VmPattern};

fn closed_type(ty: &VmType) -> Result<(), VmArtifactError> {
    match ty {
        VmType::Generic(_) | VmType::ConstGeneric { .. } | VmType::ConstIntegerExpr(_) => {
            Err(invalid("VM LIR retains a non-concrete type or const"))
        }
        VmType::Array(element)
        | VmType::FixedArray { element, .. }
        | VmType::StaticData { element, .. }
        | VmType::Reference {
            referent: element, ..
        }
        | VmType::RawPointer {
            pointee: element, ..
        } => closed_type(element),
        VmType::Tuple(types) => closed_types(types),
        VmType::Nominal { arguments, .. } => closed_arguments(arguments),
        VmType::Callable {
            parameters,
            result,
            effects,
            ..
        } => {
            closed_types(parameters)?;
            closed_type(result)?;
            closed_row(effects)
        }
        VmType::Unit
        | VmType::I64
        | VmType::Usize
        | VmType::U32
        | VmType::U8
        | VmType::U16
        | VmType::I16
        | VmType::I32
        | VmType::I8
        | VmType::U64
        | VmType::Isize
        | VmType::U128
        | VmType::I128
        | VmType::F32
        | VmType::F64
        | VmType::Bool
        | VmType::Char
        | VmType::Text
        | VmType::Bytes
        | VmType::ConstInteger(_)
        | VmType::ConstQuantity { .. } => Ok(()),
    }
}

fn closed_types(types: &[VmType]) -> Result<(), VmArtifactError> {
    types.iter().try_for_each(closed_type)
}

fn closed_arguments(arguments: &[VmGenericArgument]) -> Result<(), VmArtifactError> {
    for argument in arguments {
        match argument {
            VmGenericArgument::Type(ty) => closed_type(ty)?,
            VmGenericArgument::EffectRow(row) => closed_row(row)?,
            VmGenericArgument::Lifetime(crate::Lifetime::Static | crate::Lifetime::Elided)
            | VmGenericArgument::ConstInteger(_)
            | VmGenericArgument::ConstQuantity { .. } => {}
            VmGenericArgument::Lifetime(_)
            | VmGenericArgument::ConstIntegerExpr(_)
            | VmGenericArgument::ConstGeneric { .. } => {
                return Err(invalid("VM LIR retains a non-concrete generic argument"));
            }
        }
    }
    Ok(())
}

fn closed_row(row: &VmEffectRow) -> Result<(), VmArtifactError> {
    if !row.tails.is_empty() || !row.projections.is_empty() {
        return Err(invalid("VM LIR retains an open or projected effect row"));
    }
    for effect in &row.effects {
        closed_arguments(&effect.arguments)?;
    }
    Ok(())
}

fn closed_environment(environment: &VmCaptureEnvironment) -> Result<(), VmArtifactError> {
    environment
        .captures
        .iter()
        .try_for_each(|capture| closed_type(&capture.ty))
}

fn closed_pattern(pattern: &VmPattern) -> Result<(), VmArtifactError> {
    match pattern {
        VmPattern::Any | VmPattern::Literal(_) => Ok(()),
        VmPattern::Tuple(patterns) => patterns.iter().try_for_each(closed_pattern),
        VmPattern::Array { element, elements, .. } => {
            closed_type(element)?;
            elements.iter().try_for_each(closed_pattern)
        }
        VmPattern::Record {
            field_types,
            fields,
            ..
        }
        | VmPattern::Enum {
            field_types,
            fields,
            ..
        } => {
            closed_types(field_types)?;
            for field in fields {
                closed_type(&field.ty)?;
                closed_pattern(&field.pattern)?;
            }
            Ok(())
        }
    }
}

fn closed_instruction(instruction: &VmInstruction) -> Result<(), VmArtifactError> {
    match instruction {
        VmInstruction::DeclareResult { result, .. } => closed_type(result),
        VmInstruction::MemoryIntrinsic { types, .. }
        | VmInstruction::MakeRecord {
            field_types: types, ..
        }
        | VmInstruction::MakeRecordOwned { field_types: types, .. }
        | VmInstruction::MakeEnumOwned { field_types: types, .. }
        | VmInstruction::MakeEnum {
            field_types: types, ..
        } => closed_types(types),
        VmInstruction::MakeArray { element_type, .. } | VmInstruction::MakeArrayOwned { element_type, .. }
        | VmInstruction::ProjectArray { element_type, .. }
        | VmInstruction::ArrayGetBorrowShared { element_type, .. }
        | VmInstruction::ArrayEmpty { element_type, .. }
        | VmInstruction::ArrayPushMove { element_type, .. } => closed_type(element_type),
        VmInstruction::ProjectRecord { field_type, .. }
        | VmInstruction::ProjectTuple { field_type, .. }
        | VmInstruction::UpdateRecord { field_type, .. } => closed_type(field_type),
        VmInstruction::PatternTest { pattern, .. } => closed_pattern(pattern),
        VmInstruction::PerformOwned { effect_arguments, .. } | VmInstruction::Perform {
            effect_arguments, ..
        } => closed_arguments(effect_arguments),
        VmInstruction::InstallHandlerOwned { effect_arguments, resume_type, .. } | VmInstruction::InstallHandler {
            effect_arguments,
            resume_type,
            ..
        } => {
            closed_arguments(effect_arguments)?;
            closed_type(resume_type)
        }
        VmInstruction::HostCall {
            parameters,
            result,
            resident_operations,
            ..
        }
        | VmInstruction::HostCallOwned {
            parameters,
            result,
            resident_operations,
            ..
        } => {
            closed_types(parameters)?;
            closed_type(result)?;
            resident_operations
                .iter()
                .try_for_each(|resident| closed_type(&resident.ty))
        }
        VmInstruction::MakeCallable {
            environment: Some(environment),
            ..
        } => closed_environment(environment),
        // All other machine leaves carry only concrete scalar operands,
        // register numbers, symbols or cleanup provenance, never type terms.
        _ => Ok(()),
    }
}

impl VmLirProgram {
    pub(super) fn validate_closed_metadata(&self) -> Result<(), VmArtifactError> {
        for function in self.functions.values() {
            closed_types(&function.registers)?;
            closed_type(&function.result)?;
            for descriptor in &function.nominal_copy_descriptors {
                closed_arguments(&descriptor.arguments)?;
                for variant in &descriptor.variants {
                    closed_types(variant)?;
                }
            }
            for block in &function.blocks {
                for instruction in &block.instructions {
                    closed_instruction(instruction)?;
                }
            }
        }
        for environment in self.callable_environments.values() {
            closed_environment(environment)?;
        }
        Ok(())
    }
}
