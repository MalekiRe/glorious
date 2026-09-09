use grandiose_stage0::{CandidateVmProgram, DefKey, Digest, Safety, VmArtifactError,
    VmFunction, VmGenericArgument, VmInstruction, VmNominalCopyDescriptor, VmType,
    decode_and_verify_program, encode_program, verify_vm_program};
use std::collections::BTreeMap;

#[test]
fn callable_receiver_weakening_cannot_rebind_activation_generics_in_aggregates() {
    for kind in ["tuple", "array", "fixed-array", "record", "enum"] {
        for actual in [VmType::Generic(0), VmType::I64, VmType::Generic(1)] {
            let expected = VmType::Generic(0);
            let definition = DefKey(Digest::of_bytes(b"generic-aggregate-nominal"));
            let nominal_arguments = vec![VmGenericArgument::Type(expected.clone())];
            let mut nominal_copy_descriptors = vec![];
            let aggregate = match kind {
                "tuple" => VmType::Tuple(vec![expected.clone()]),
                "array" => VmType::Array(Box::new(expected.clone())),
                "fixed-array" => VmType::FixedArray { element: Box::new(expected.clone()), length: 1 },
                _ => {
                    nominal_copy_descriptors.push(VmNominalCopyDescriptor {
                        source_contract: Digest::of_bytes(b"generic-aggregate-source-contract"),
                        definition, is_enum: kind == "enum", arguments: nominal_arguments.clone(),
                        variants: vec![vec![expected.clone()]],
                    });
                    VmType::Nominal { definition, arguments: nominal_arguments }
                }
            };
            let mut instructions = vec![VmInstruction::ConstI64 { dst: 3, value: 42 }];
            let parameters = if actual == VmType::I64 {
                instructions.push(VmInstruction::ConstI64 { dst: 1, value: 7 });
                1
            } else { 2 };
            instructions.push(match kind {
                "tuple" => VmInstruction::MakeTuple { dst: 2, fields: vec![1] },
                "array" | "fixed-array" => VmInstruction::MakeArray { dst: 2, fields: vec![1], element_type: expected.clone() },
                "record" => VmInstruction::MakeRecord { dst: 2, definition, fields: vec![1], field_types: vec![actual.clone()] },
                _ => VmInstruction::MakeEnum { dst: 2, definition, variant: 0, fields: vec![1], field_types: vec![actual.clone()] },
            });
            instructions.push(VmInstruction::Return { value: 3 });
            let callee = DefKey(Digest::of_bytes(b"generic-aggregate-boundary"));
            let entry = DefKey(Digest::of_bytes(b"generic-aggregate-entry"));
            let function = VmFunction {
                definition: callee,
                safety: Safety::Safe, unsafe_execution: false, captures: 0,
                nominal_copy_descriptors, parameters,
                registers: vec![expected, actual.clone(), aggregate, VmType::I64], instructions,
            };
            let entry_function = VmFunction {
                definition: entry, safety: Safety::Safe, unsafe_execution: false,
                captures: 0, parameters: 0, nominal_copy_descriptors: vec![],
                registers: vec![VmType::Bool, VmType::I64],
                instructions: vec![
                    VmInstruction::ConstBool { dst: 0, value: false },
                    VmInstruction::Call { dst: 1, callee, arguments: vec![0; parameters as usize] },
                    VmInstruction::Return { value: 1 },
                ],
            };
            let mut candidate = CandidateVmProgram {
                schema: grandiose_stage0::STAGE0_VM_SCHEMA,
                runtime_manifest: None,
                fingerprint: Digest::of_bytes(b"unsealed-generic-aggregate"),
                entry, host_capabilities: vec![], callable_environments: BTreeMap::new(),
                functions: BTreeMap::from([(entry, entry_function), (callee, function)]),
            };
            candidate.fingerprint = candidate.computed_fingerprint();
            for result in [verify_vm_program(candidate.clone()), decode_and_verify_program(&encode_program(&candidate))] {
                if actual == VmType::Generic(0) {
                    assert!(result.is_ok(), "{kind}, lawful generic transfer: {result:?}");
                } else {
                    assert!(matches!(result, Err(VmArtifactError::TypeMismatch { .. })
                        | Err(VmArtifactError::MalformedEncoding {
                            message: "record field layout does not match nominal descriptor"
                                | "enum field layout does not match nominal descriptor"
                        })), "{kind}, actual={actual:?}: {result:?}");
                }
            }
        }
    }
}
