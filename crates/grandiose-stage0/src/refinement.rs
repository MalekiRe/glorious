//! Sealed binding-pack identities and their concrete resident layout.
//! Environment brands are identity-only; only field values occupy storage.
use crate::{
    DefKey, Digest, GenericArgument, Lifetime, RefinementBrand, RefinementEnvironment, Type,
};

pub fn bindings_definition() -> DefKey {
    DefKey(Digest::of_bytes(b"grandiose-intrinsic-bindings-type-v1"))
}

fn environment_definition(brand: RefinementBrand, positive: bool) -> DefKey {
    DefKey(Digest::of_parts([
        b"grandiose-refinement-pack-environment-v1".as_slice(),
        brand.owner.0.as_bytes().as_slice(),
        brand.refinement.to_le_bytes().as_slice(),
        &[u8::from(positive)],
    ]))
}

impl RefinementEnvironment {
    /// Construct the type of compiler-owned evidence, not a source value.
    /// Positive fields retain their already checked observational/copy types;
    /// a negative context grants no positive binders.
    pub fn binding_pack_type(&self, positive: bool, lifetime: Lifetime) -> Result<Type, String> {
        if let Some(error) = crate::core::refinement_environment_error(self) {
            return Err(error);
        }
        let fields = if positive {
            self.binding_types
                .iter()
                .map(|(_, ty)| ty.clone())
                .collect()
        } else {
            vec![]
        };
        let environment = Type::Nominal {
            definition: environment_definition(self.brand, positive),
            arguments: vec![
                GenericArgument::Type(Type::Nominal {
                    definition: self.brand.owner,
                    arguments: vec![],
                }),
                GenericArgument::ConstInteger(self.brand.refinement.into()),
                GenericArgument::ConstInteger(u32::from(positive).into()),
                GenericArgument::Type(Type::Tuple(fields)),
            ],
        };
        Ok(Type::Nominal {
            definition: bindings_definition(),
            arguments: vec![
                GenericArgument::Lifetime(lifetime),
                GenericArgument::Type(environment),
            ],
        })
    }
}

/// Decode only canonical compiler-minted environment identities. An opaque
/// generic P is a valid source type argument, but cannot supply a layout.
pub(crate) fn binding_pack_fields(ty: &Type) -> Option<&[Type]> {
    let Type::Nominal {
        definition,
        arguments,
    } = ty
    else {
        return None;
    };
    if *definition != bindings_definition() {
        return None;
    }
    let [
        GenericArgument::Lifetime(_),
        GenericArgument::Type(Type::Nominal {
            definition: environment,
            arguments,
        }),
    ] = arguments.as_slice()
    else {
        return None;
    };
    let [
        GenericArgument::Type(Type::Nominal {
            definition: owner,
            arguments: owner_arguments,
        }),
        GenericArgument::ConstInteger(refinement),
        GenericArgument::ConstInteger(positive),
        GenericArgument::Type(Type::Tuple(fields)),
    ] = arguments.as_slice()
    else {
        return None;
    };
    let refinement = refinement.as_u32()?;
    let positive = positive.as_u32()?;
    if !owner_arguments.is_empty()
        || positive > 1
        || (positive == 0 && !fields.is_empty())
        || *environment
            != environment_definition(
                RefinementBrand {
                    owner: *owner,
                    refinement,
                },
                positive == 1,
            )
    {
        return None;
    }
    Some(fields)
}

pub(crate) fn binding_pack_contract(ty: &Type) -> Option<Digest> {
    binding_pack_fields(ty)?;
    Some(bindings_layout_contract())
}

pub(crate) fn binding_pack_brand(ty: &Type) -> Option<(RefinementBrand, bool)> {
    binding_pack_fields(ty)?;
    let Type::Nominal { arguments, .. } = ty else { return None; };
    let GenericArgument::Type(Type::Nominal { arguments, .. }) = &arguments[1] else { return None; };
    let [GenericArgument::Type(Type::Nominal { definition: owner, .. }),
        GenericArgument::ConstInteger(refinement), GenericArgument::ConstInteger(positive), _] = arguments.as_slice()
        else { return None; };
    Some((RefinementBrand { owner: *owner, refinement: refinement.as_u32()? }, positive.as_u32()? == 1))
}

pub(crate) fn bindings_layout_contract() -> Digest {
    Digest::of_bytes(b"grandiose-binding-pack-layout-v1")
}

pub(crate) fn vm_binding_pack_fields(ty: &crate::VmType) -> Option<&[crate::VmType]> {
    use crate::VmType as V;
    use crate::vm_backend::VmGenericArgument as A;
    let V::Nominal {
        definition,
        arguments,
    } = ty
    else {
        return None;
    };
    if *definition != bindings_definition() {
        return None;
    }
    let [
        A::Type(V::Nominal {
            definition: environment,
            arguments,
        }),
    ] = arguments.as_slice()
    else {
        return None;
    };
    let [
        A::Type(V::Nominal {
            definition: owner,
            arguments: owner_arguments,
        }),
        A::ConstInteger(refinement),
        A::ConstInteger(positive),
        A::Type(V::Tuple(fields)),
    ] = arguments.as_slice()
    else {
        return None;
    };
    let refinement = refinement.as_u32()?;
    let positive = positive.as_u32()?;
    if !owner_arguments.is_empty()
        || positive > 1
        || (positive == 0 && !fields.is_empty())
        || *environment
            != environment_definition(
                RefinementBrand {
                    owner: *owner,
                    refinement,
                },
                positive == 1,
            )
    {
        return None;
    }
    Some(fields)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::{RefinementBindingKey, ScalarType, VmInstruction, VmType};
    use std::collections::BTreeMap;

    pub(crate) fn environment(ty: Type) -> RefinementEnvironment {
        let brand = RefinementBrand {
            owner: DefKey(Digest::of_bytes(b"binding-pack-producer")),
            refinement: 7,
        };
        RefinementEnvironment {
            brand,
            subject: Some("subject".into()),
            bindings: vec!["found".into()],
            binding_keys: vec![RefinementBindingKey {
                environment: brand,
                binder: 0,
            }],
            binding_types: vec![("found".into(), ty)],
            sealed: true,
        }
    }

    #[test]
    fn binding_pack_identity_distinguishes_outcomes_and_has_no_brand_storage() {
        let environment = environment(Type::Scalar(ScalarType::I64));
        let yes = environment
            .binding_pack_type(true, Lifetime::Static)
            .unwrap();
        let no = environment
            .binding_pack_type(false, Lifetime::Static)
            .unwrap();
        assert_ne!(yes, no);
        assert_eq!(
            binding_pack_fields(&yes),
            Some([Type::Scalar(ScalarType::I64)].as_slice())
        );
        assert_eq!(binding_pack_fields(&no), Some([].as_slice()));
        let mut other = environment.clone();
        other.brand.refinement += 1;
        other.binding_keys[0].environment = other.brand;
        assert_ne!(
            yes,
            other.binding_pack_type(true, Lifetime::Static).unwrap()
        );
        other.binding_keys[0].environment = environment.brand;
        assert!(other.binding_pack_type(true, Lifetime::Static).is_err());
    }

    #[test]
    fn binding_pack_layout_and_use_follow_fields_not_an_opaque_brand() {
        let unique = Type::Reference {
            mutability: crate::Mutability::Unique,
            lifetime: Lifetime::Static,
            referent: Box::new(Type::Scalar(ScalarType::I64)),
        };
        let environment = environment(unique.clone());
        let yes = environment
            .binding_pack_type(true, Lifetime::Static)
            .unwrap();
        let no = environment
            .binding_pack_type(false, Lifetime::Static)
            .unwrap();
        let signatures = crate::ElaboratedInterface::default();
        assert_eq!(
            signatures.principal_use_interval(&yes),
            Some(crate::Quantity::AFFINE)
        );
        assert_eq!(
            signatures.principal_use_interval_with_bounds(&yes, &[]),
            Some(crate::Quantity::AFFINE)
        );
        assert_eq!(
            signatures.principal_use_interval(&no),
            Some(crate::Quantity::UNRESTRICTED)
        );
        let Type::Nominal {
            definition,
            arguments,
        } = &yes
        else {
            unreachable!()
        };
        let fields = signatures
            .instantiate_struct_fields_generic(*definition, arguments)
            .unwrap();
        assert_eq!(fields.len(), 1);
        assert_eq!(fields[0].ty, unique);
        assert!(fields[0].private_authority.is_some());
        let mut forged = yes.clone();
        let Type::Nominal { arguments, .. } = &mut forged else {
            unreachable!()
        };
        let GenericArgument::Type(Type::Nominal { definition, .. }) = &mut arguments[1] else {
            unreachable!()
        };
        *definition = DefKey(Digest::of_bytes(b"forged-pack-environment"));
        assert!(binding_pack_fields(&forged).is_none());
    }

    #[test]
    fn binding_pack_values_cross_ordinary_encoded_vm_calls() {
        let pack = environment(Type::Scalar(ScalarType::I64))
            .binding_pack_type(true, Lifetime::Static)
            .unwrap();
        let Type::Nominal {
            definition,
            arguments,
        } = &pack
        else {
            unreachable!()
        };
        let descriptor =
            crate::vm_backend::vm_nominal_copy_descriptor(&crate::MirNominalCopyDescriptor {
                definition: *definition,
                arguments: arguments.clone(),
                source_contract: binding_pack_contract(&pack).unwrap(),
                is_enum: false,
                variants: vec![vec![Type::Scalar(ScalarType::I64)]],
            })
            .unwrap();
        let pack = crate::vm_backend::vm_type(&pack).unwrap();
        let entry = DefKey(Digest::of_bytes(b"binding-pack-entry"));
        let child = DefKey(Digest::of_bytes(b"binding-pack-child"));
        let function = |definition, parameters, registers, instructions| crate::VmFunction {
            definition,
            parameters,
            registers,
            instructions,
            safety: crate::Safety::Safe,
            unsafe_execution: false,
            captures: 0,
            nominal_copy_descriptors: vec![descriptor.clone()],
        };
        let local = function(
            entry,
            0,
            vec![VmType::I64, pack.clone(), VmType::I64],
            vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::MakeRecord {
                    dst: 1,
                    definition: *definition,
                    fields: vec![0],
                    field_types: vec![VmType::I64],
                },
                VmInstruction::ProjectRecord {
                    dst: 2,
                    base: 1,
                    index: 0,
                    field_count: 1,
                    field_type: VmType::I64,
                },
                VmInstruction::Return { value: 2 },
            ],
        );
        let mut artifact = crate::CandidateVmArtifact {
            schema: crate::STAGE0_VM_SCHEMA,
            runtime_manifest: None,
            fingerprint: Digest::of_bytes(b"unsealed-pack"),
            function: local.clone(),
        };
        artifact.fingerprint = artifact.computed_fingerprint();
        assert_eq!(
            crate::decode_and_verify_artifact(&crate::encode_artifact(&artifact))
                .unwrap()
                .run_i64()
                .unwrap(),
            42
        );
        let mut forged = artifact.clone();
        forged.function.nominal_copy_descriptors[0].variants[0][0] = VmType::Bool;
        forged.fingerprint = forged.computed_fingerprint();
        assert!(crate::decode_and_verify_artifact(&crate::encode_artifact(&forged)).is_err());
        let mut main = local;
        main.instructions[2] = VmInstruction::CallOwned {
            dst: 2,
            callee: child,
            arguments: vec![1],
        };
        let child_body = function(
            child,
            1,
            vec![pack, VmType::I64],
            vec![
                VmInstruction::ProjectRecord {
                    dst: 1,
                    base: 0,
                    index: 0,
                    field_count: 1,
                    field_type: VmType::I64,
                },
                VmInstruction::Return { value: 1 },
            ],
        );
        let mut program = crate::CandidateVmProgram {
            schema: artifact.schema,
            runtime_manifest: None,
            entry,
            functions: BTreeMap::from([(entry, main), (child, child_body)]),
            host_capabilities: vec![],
            callable_environments: BTreeMap::new(),
            fingerprint: artifact.fingerprint,
        };
        program.fingerprint = program.computed_fingerprint();
        assert_eq!(
            crate::decode_and_verify_program(&crate::encode_program(&program))
                .unwrap()
                .run_i64()
                .unwrap(),
            42
        );
    }
}
