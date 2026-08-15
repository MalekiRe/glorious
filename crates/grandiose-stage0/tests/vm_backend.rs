use grandiose_stage0::{
    BodySyntax, CallableId, CandidateVmArtifact, CandidateVmProgram, CoreId, DeclarationScan,
    DefKey, DefinitionIndex, Digest, ElaboratedInterface, EnvironmentBrand, FileKey,
    GenericArgument, InterfaceSet, LabelBrand, LexedFile, LogicalPath, MirBlock, MirBlockId,
    MirCleanupPlan, MirControlTables, MirFunction, MirInstruction, MirLabelId, MirLocal,
    MirLocalDecl, MirLowering, MirPerformSiteId, MirProgram, MirScopeId, MirSourceStorageScopeId, MirTerminator, PackageKey,
    PlaceFlow, ScalarType, Type, TypedBody, VmArtifactError, VmCapture, VmCaptureEnvironment,
    VmCaptureMode, VmCleanupLoan, VmCleanupPlace, VmCleanupProof, VmContinuationPolicy,
    VmEffectRow, VmExecutionLimits, VmFunction, VmGenericArgument, VmInstruction,
    VmHost, VmNominalCopyDescriptor, VmPattern, VmPatternField, VmStorageErasureWitness, VmType,
    VmStorageErasureAction, VmStorageErasureStorage,
    decode_and_verify_artifact,
    decode_and_verify_program, decode_artifact, decode_program, emit_vm, emit_vm_program,
    encode_artifact, encode_program, verify_vm, verify_vm_program,
};
use std::collections::BTreeMap;

#[derive(Default)]
struct RecordingVmHost {
    diagnostics: Vec<String>,
}

impl VmHost for RecordingVmHost {
    fn process_args(&mut self) -> Result<Vec<String>, String> {
        Ok(vec![])
    }

    fn read_file(&mut self, _path: &str) -> Result<Vec<u8>, String> {
        Err("read_file was not expected".into())
    }

    fn write_file(&mut self, _path: &str, _bytes: &[u8]) -> Result<(), String> {
        Err("write_file was not expected".into())
    }

    fn write_diagnostic(&mut self, text: &str) -> Result<(), String> {
        self.diagnostics.push(text.into());
        Ok(())
    }
}

#[test]
fn text_byte_len_is_a_capability_free_verified_vm_primitive() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"text-byte-len-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::Text, VmType::Usize],
        instructions: vec![
            VmInstruction::ConstText {
                dst: 0,
                value: "a🦀".into(),
            },
            VmInstruction::TextByteLen { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"text-byte-len-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_usize()
            .unwrap(),
        5,
    );
}

#[test]
fn verifier_rejects_text_byte_len_with_forged_operand_or_result_abi() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"forged-text-byte-len-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 1 },
            VmInstruction::TextByteLen { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"forged-text-byte-len-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::TypeMismatch {
            expected: VmType::Usize,
            ..
        })
    ));
}

#[test]
fn verifier_rejects_forged_text_family_opcode_abis() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"forged-text-family-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::Text, VmType::Text, VmType::U32],
        instructions: vec![
            VmInstruction::ConstText {
                dst: 0,
                value: "a".into(),
            },
            VmInstruction::ConstText {
                dst: 1,
                value: "b".into(),
            },
            VmInstruction::TextConcat {
                dst: 2,
                left: 0,
                right: 1,
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"forged-text-family-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::TypeMismatch {
            expected: VmType::Text,
            ..
        })
    ));
}

#[test]
fn verifier_rejects_forged_checked_char_opcode_abi() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"forged-char-family-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::Text, VmType::Text, VmType::U32, VmType::U32],
        instructions: vec![
            VmInstruction::ConstText {
                dst: 0,
                value: "same".into(),
            },
            VmInstruction::ConstText {
                dst: 1,
                value: "same".into(),
            },
            VmInstruction::TextEq {
                dst: 2,
                left: 0,
                right: 1,
            },
            VmInstruction::CharFromU32Checked { dst: 3, value: 2 },
            VmInstruction::Return { value: 3 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"forged-char-family-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let error = verify_vm(candidate).unwrap_err();
    assert!(
        matches!(
            error,
            VmArtifactError::TypeMismatch {
                expected: VmType::Char,
                ..
            }
        ),
        "unexpected verifier result: {error:?}"
    );
}

#[test]
fn verifier_rejects_forged_bytes_family_opcode_abis() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"forged-bytes-family-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::Text, VmType::Usize, VmType::U8],
        instructions: vec![
            VmInstruction::ConstText {
                dst: 0,
                value: "not bytes".into(),
            },
            VmInstruction::BytesGet {
                dst: 2,
                bytes: 0,
                index: 1,
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"forged-bytes-family-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::TypeMismatch {
            expected: VmType::Bytes,
            ..
        })
    ));
}

#[test]
fn manifest_bound_u32_runtime_family_executes_wrapping_checked_and_conversion_abis() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"u32-runtime-family-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![
            VmType::Char,
            VmType::U32,
            VmType::Char,
            VmType::U32,
            VmType::U32,
        ],
        instructions: vec![
            VmInstruction::ConstChar {
                dst: 0,
                value: '🦀' as u32,
            },
            VmInstruction::CharToU32 { dst: 1, value: 0 },
            VmInstruction::ConstChar {
                dst: 2,
                value: '🦀' as u32,
            },
            VmInstruction::CharToU32 { dst: 3, value: 2 },
            VmInstruction::U32WrappingMul {
                dst: 4,
                left: 1,
                right: 3,
            },
            VmInstruction::Return { value: 4 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"u32-runtime-family-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_u32()
            .unwrap(),
        ('🦀' as u32).wrapping_mul('🦀' as u32),
    );
}

#[test]
fn verifier_rejects_forged_u32_runtime_opcode_abi() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"forged-u32-runtime-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::Char, VmType::U32, VmType::Usize],
        instructions: vec![
            VmInstruction::ConstChar {
                dst: 0,
                value: 'a' as u32,
            },
            VmInstruction::CharToU32 { dst: 1, value: 0 },
            VmInstruction::U32CheckedAdd {
                dst: 2,
                left: 1,
                right: 1,
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"forged-u32-runtime-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::TypeMismatch {
            expected: VmType::U32,
            ..
        })
    ));
}

#[test]
fn i64_wrapping_add_round_trips_and_verifier_rejects_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-wrapping-add-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 {
                dst: 0,
                value: i64::MAX,
            },
            VmInstruction::ConstI64 { dst: 1, value: 1 },
            VmInstruction::WrappingAddI64 {
                dst: 2,
                left: 0,
                right: 1,
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-wrapping-add-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_i64()
            .unwrap(),
        i64::MIN,
    );

    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool,
        })
    ));
}

#[test]
fn i64_wrapping_sub_round_trips_and_verifier_rejects_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-wrapping-sub-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 {
                dst: 0,
                value: i64::MIN,
            },
            VmInstruction::ConstI64 { dst: 1, value: 1 },
            VmInstruction::WrappingSubI64 {
                dst: 2,
                left: 0,
                right: 1,
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-wrapping-sub-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_i64()
            .unwrap(),
        i64::MAX,
    );

    let mut forged = candidate;
    forged.function.registers[1] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 1,
            expected: VmType::I64,
            found: VmType::Bool,
        })
    ));
}

#[test]
fn i64_wrapping_mul_round_trips_and_verifier_rejects_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-wrapping-mul-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 {
                dst: 0,
                value: i64::MAX,
            },
            VmInstruction::ConstI64 { dst: 1, value: 2 },
            VmInstruction::WrappingMulI64 {
                dst: 2,
                left: 0,
                right: 1,
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-wrapping-mul-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_i64()
            .unwrap(),
        -2,
    );

    let mut forged = candidate;
    forged.function.registers[1] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 1,
            expected: VmType::I64,
            found: VmType::Bool,
        })
    ));
}

#[test]
fn i64_equality_to_u32_round_trips_and_verifier_rejects_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-equality-u32-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64, VmType::U32],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 7 },
            VmInstruction::ConstI64 { dst: 1, value: 7 },
            VmInstruction::IntEqualI64 {
                dst: 2,
                left: 0,
                right: 1,
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-equality-u32-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_u32()
            .unwrap(),
        1
    );
    let mut forged = candidate;
    forged.function.registers[2] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 2,
            expected: VmType::U32,
            found: VmType::Bool
        })
    ));
}

#[test]
fn i64_less_to_u32_round_trips_and_verifier_rejects_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-less-u32-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64, VmType::U32],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: -1 },
            VmInstruction::ConstI64 { dst: 1, value: 0 },
            VmInstruction::IntLessI64 {
                dst: 2,
                left: 0,
                right: 1,
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-less-u32-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_u32()
            .unwrap(),
        1
    );
    let mut forged = candidate;
    forged.function.registers[2] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 2,
            expected: VmType::U32,
            found: VmType::Bool
        })
    ));
}

#[test]
fn checked_i64_to_usize_rejects_negative_and_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-usize-checked")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::Usize],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: -1 },
            VmInstruction::I64ToUsizeChecked { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        decode_and_verify_artifact(&encode_artifact(&candidate))
            .unwrap()
            .run_usize(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));
    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool
        })
    ));
}

#[test]
fn checked_i64_to_u8_rejects_negative_out_of_range_and_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-u8-checked")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::U8],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: -1 },
            VmInstruction::I64ToU8Checked { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        decode_and_verify_artifact(&encode_artifact(&candidate))
            .unwrap()
            .run_u8(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));
    candidate.function.instructions[0] = VmInstruction::ConstI64 { dst: 0, value: 256 };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        decode_and_verify_artifact(&encode_artifact(&candidate))
            .unwrap()
            .run_u8(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));
    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool
        })
    ));
}

#[test]
fn checked_i64_to_u16_rejects_negative_out_of_range_and_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-u16-checked")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::U16],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: -1 },
            VmInstruction::I64ToU16Checked { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        decode_and_verify_artifact(&encode_artifact(&candidate))
            .unwrap()
            .run_u16(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));
    candidate.function.instructions[0] = VmInstruction::ConstI64 {
        dst: 0,
        value: 65_536,
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        decode_and_verify_artifact(&encode_artifact(&candidate))
            .unwrap()
            .run_u16(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));
    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool
        })
    ));
}

#[test]
fn checked_i64_to_i16_rejects_out_of_range_and_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-i16-checked")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I16],
        instructions: vec![
            VmInstruction::ConstI64 {
                dst: 0,
                value: 32_768,
            },
            VmInstruction::I64ToI16Checked { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        decode_and_verify_artifact(&encode_artifact(&candidate))
            .unwrap()
            .run_i16(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));
    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool
        })
    ));
}

#[test]
fn checked_i64_to_i32_rejects_out_of_range_and_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-i32-checked")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I32],
        instructions: vec![
            VmInstruction::ConstI64 {
                dst: 0,
                value: 2_147_483_648,
            },
            VmInstruction::I64ToI32Checked { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        decode_and_verify_artifact(&encode_artifact(&candidate))
            .unwrap()
            .run_i32(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));
    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool
        })
    ));
}

#[test]
fn checked_i64_to_u32_rejects_negative_out_of_range_and_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-u32-checked")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::U32],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: -1 },
            VmInstruction::I64ToU32Checked { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        decode_and_verify_artifact(&encode_artifact(&candidate))
            .unwrap()
            .run_u32(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));
    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool
        })
    ));
}

#[test]
fn i64_shr_u32_round_trips_and_verifier_rejects_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-shr-u32-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::Char, VmType::U32, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 8 },
            VmInstruction::ConstChar {
                dst: 1,
                value: 1,
            },
            VmInstruction::CharToU32 { dst: 2, value: 1 },
            VmInstruction::IntShrI64 {
                dst: 3,
                left: 0,
                right: 2,
            },
            VmInstruction::Return { value: 3 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-shr-u32-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_i64()
            .unwrap(),
        4
    );
    let mut forged = candidate;
    forged.function.registers[2] = VmType::I64;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 2,
            expected: VmType::U32,
            found: VmType::I64,
        })
    ));
}

#[test]
fn i64_bit_xor_round_trips_and_verifier_rejects_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-bit-xor-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 },
            VmInstruction::ConstI64 { dst: 1, value: 15 },
            VmInstruction::BitXorI64 {
                dst: 2,
                left: 0,
                right: 1,
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-bit-xor-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_i64()
            .unwrap(),
        37
    );
    let mut forged = candidate;
    forged.function.registers[1] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 1,
            expected: VmType::I64,
            found: VmType::Bool,
        })
    ));
}

#[test]
fn i64_bit_and_round_trips_and_verifier_rejects_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-bit-and-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 },
            VmInstruction::ConstI64 { dst: 1, value: 15 },
            VmInstruction::BitAndI64 {
                dst: 2,
                left: 0,
                right: 1,
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-bit-and-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_i64()
            .unwrap(),
        10
    );
    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool
        })
    ));
}

#[test]
fn i64_bit_or_round_trips_and_verifier_rejects_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-bit-or-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 40 },
            VmInstruction::ConstI64 { dst: 1, value: 3 },
            VmInstruction::BitOrI64 {
                dst: 2,
                left: 0,
                right: 1,
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-bit-or-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_i64()
            .unwrap(),
        43,
    );

    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool,
        })
    ));
}

#[test]
fn i64_bit_not_round_trips_and_verifier_rejects_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-bit-not-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 10 },
            VmInstruction::BitNotI64 { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-bit-not-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_i64()
            .unwrap(),
        !10,
    );

    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool,
        })
    ));
}

#[test]
fn i64_shift_left_rejects_a_width_count_and_rejects_count_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-shl-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::Char, VmType::U32, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 1 },
            VmInstruction::ConstChar { dst: 1, value: 64 },
            VmInstruction::CharToU32 { dst: 2, value: 1 },
            VmInstruction::ShlI64 {
                dst: 3,
                value: 0,
                count: 2,
            },
            VmInstruction::Return { value: 3 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-shl-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert!(matches!(
        decode_and_verify_artifact(&encoded).unwrap().run_i64(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));

    let mut forged = candidate;
    forged.function.registers[2] = VmType::I64;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 2,
            expected: VmType::U32,
            found: VmType::I64,
        })
    ));
}

#[test]
fn i64_to_u32_wrapping_round_trips_and_verifier_rejects_input_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-to-u32-wrapping-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::U32],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: -1 },
            VmInstruction::I64ToU32Wrapping { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-to-u32-wrapping-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_u32()
            .unwrap(),
        u32::MAX,
    );

    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool,
        })
    ));
}

#[test]
fn i64_to_usize_wrapping_round_trips_and_verifier_rejects_input_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-to-usize-wrapping-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::Usize],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: -1 },
            VmInstruction::I64ToUsizeWrapping { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-to-usize-wrapping-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_usize()
            .unwrap(),
        u64::MAX,
    );

    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool,
        })
    ));
}

#[test]
fn i64_to_u8_wrapping_round_trips_and_verifier_rejects_input_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-to-u8-wrapping-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::U8],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: -1 },
            VmInstruction::I64ToU8Wrapping { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-to-u8-wrapping-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_u8()
            .unwrap(),
        u8::MAX,
    );

    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool,
        })
    ));
}

#[test]
fn i64_to_u16_wrapping_round_trips_and_verifier_rejects_input_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-to-u16-wrapping-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::U16],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: -1 },
            VmInstruction::I64ToU16Wrapping { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-to-u16-wrapping-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_u16()
            .unwrap(),
        u16::MAX,
    );

    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool,
        })
    ));
}

#[test]
fn i64_to_i16_wrapping_round_trips_and_verifier_rejects_input_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-to-i16-wrapping-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I16],
        instructions: vec![
            VmInstruction::ConstI64 {
                dst: 0,
                value: 65535,
            },
            VmInstruction::I64ToI16Wrapping { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-to-i16-wrapping-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_i16()
            .unwrap(),
        -1
    );
    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool
        })
    ));
}

#[test]
fn i64_to_i32_wrapping_round_trips_and_verifier_rejects_input_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-to-i32-wrapping-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I32],
        instructions: vec![
            VmInstruction::ConstI64 {
                dst: 0,
                value: 4_294_967_295,
            },
            VmInstruction::I64ToI32Wrapping { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-to-i32-wrapping-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_i32()
            .unwrap(),
        -1
    );
    let mut forged = candidate;
    forged.function.registers[0] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::Bool
        })
    ));
}

#[test]
fn i64_greater_to_u32_round_trips_and_verifier_rejects_type_confusion() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"i64-greater-u32-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64, VmType::U32],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 0 },
            VmInstruction::ConstI64 { dst: 1, value: -1 },
            VmInstruction::IntGreaterI64 {
                dst: 2,
                left: 0,
                right: 1,
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"i64-greater-u32-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_u32()
            .unwrap(),
        1,
    );

    let mut forged = candidate;
    forged.function.registers[2] = VmType::Bool;
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::TypeMismatch {
            register: 2,
            expected: VmType::U32,
            found: VmType::Bool,
        })
    ));
}

#[test]
fn checked_u32_shifts_and_division_fail_deterministically() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"checked-u32-runtime-failure-vm")),
        captures: 0,
        parameters: 0,
        registers: vec![
            VmType::Char,
            VmType::U32,
            VmType::Char,
            VmType::U32,
            VmType::U32,
        ],
        instructions: vec![
            VmInstruction::ConstChar {
                dst: 0,
                value: 'a' as u32,
            },
            VmInstruction::CharToU32 { dst: 1, value: 0 },
            VmInstruction::ConstChar {
                dst: 2,
                value: 'A' as u32,
            },
            VmInstruction::CharToU32 { dst: 3, value: 2 },
            VmInstruction::U32CheckedShl {
                dst: 4,
                left: 1,
                right: 3,
            },
            VmInstruction::Return { value: 4 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"checked-u32-runtime-failure-vm-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate).unwrap().run_u32(),
        Err(VmArtifactError::ArithmeticOverflow)
    ));
}

#[test]
fn vm_seals_symbolic_structural_consts_in_nominal_layouts_and_effect_protocols() {
    use grandiose_stage0::{ConstKind, Quantity, StructuralU32Expr};

    let nominal = DefKey(Digest::of_bytes(b"vm-symbolic-const-nominal"));
    let effect = DefKey(Digest::of_bytes(b"vm-symbolic-const-effect"));
    let expression = StructuralU32Expr::Add(
        Box::new(StructuralU32Expr::Literal(1)),
        Box::new(StructuralU32Expr::Param(0)),
    );
    let function = MirFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"vm-symbolic-const-caller")),
        captures: 0,
        parameters: vec![],
        locals: vec![
            MirLocalDecl {
                ty: Type::Scalar(ScalarType::I64),
                source: CoreId(u32::MAX),
            },
            MirLocalDecl {
                ty: Type::Nominal {
                    definition: nominal,
                    arguments: vec![
                        GenericArgument::ConstU32Expr(expression.clone()),
                        GenericArgument::ConstQuantity(Quantity::new(2, Some(4)).unwrap()),
                        GenericArgument::ConstGeneric {
                            index: 3,
                            kind: ConstKind::Quantity,
                        },
                    ],
                },
                source: CoreId(u32::MAX),
            },
        ],
        result: Type::Scalar(ScalarType::I64),
        control: MirControlTables::default(),
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            scope: MirScopeId::ROOT,
            parameters: vec![],
            instructions: vec![MirInstruction::Perform {
                site: MirPerformSiteId::UNASSIGNED,
                dst: MirLocal(0),
                effect,
                effect_arguments: vec![GenericArgument::ConstU32Expr(expression.clone())],
                operation: 0,
                arguments: vec![],
            }],
            terminator: MirTerminator::Return { value: MirLocal(0) },
        }],
    }
    .with_frozen_control_tables();
    let artifact = emit_vm(&function).expect("symbolic structural consts have a VM form");
    assert!(matches!(
        artifact.function.registers[1],
        VmType::Nominal { ref arguments, .. }
            if matches!(arguments.as_slice(), [
                VmType::ConstU32Expr(found),
                VmType::ConstQuantity { lower: 2, upper: Some(4) },
                VmType::ConstGeneric { index: 3, kind: ConstKind::Quantity },
            ] if *found == expression)
    ));
    assert!(matches!(
        artifact.function.instructions.as_slice(),
        [VmInstruction::DeclareResult { .. }, VmInstruction::Perform { effect_arguments, .. }, ..]
            if effect_arguments == &[VmGenericArgument::ConstU32Expr(expression.clone())]
    ));
    let encoded = encode_artifact(&artifact);
    assert_eq!(decode_artifact(&encoded).unwrap(), artifact);
    assert_eq!(
        decode_and_verify_artifact(&encoded).unwrap().fingerprint(),
        artifact.fingerprint
    );

    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: artifact.function.definition,
        functions: BTreeMap::from([(artifact.function.definition, artifact.function.clone())]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"vm-symbolic-const-program-stale"),
    };
    program.fingerprint = program.computed_fingerprint();
    let encoded = encode_program(&program);
    assert_eq!(decode_program(&encoded).unwrap(), program);
    assert_eq!(
        decode_and_verify_program(&encoded).unwrap().fingerprint(),
        program.fingerprint
    );
}

#[test]
fn vm_rejects_forged_noncanonical_structural_const_identity() {
    use grandiose_stage0::StructuralU32Expr;

    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"vm-forged-symbolic-const")),
        captures: 0,
        parameters: 0,
        registers: vec![
            VmType::I64,
            VmType::Nominal {
                definition: DefKey(Digest::of_bytes(b"vm-forged-symbolic-const-nominal")),
                // Addition is commutative and must be serialized in canonical
                // order. A hostile candidate cannot make this alternate
                // spelling observable through a separate layout fingerprint.
                arguments: vec![VmType::ConstU32Expr(StructuralU32Expr::Add(
                    Box::new(StructuralU32Expr::Param(0)),
                    Box::new(StructuralU32Expr::Literal(1)),
                ))],
            },
        ],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 },
            VmInstruction::Return { value: 0 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"vm-forged-symbolic-const-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::NonCanonicalEncoding)
    ));

    let invalid_expression = StructuralU32Expr::Div(
        Box::new(StructuralU32Expr::Literal(1)),
        Box::new(StructuralU32Expr::Literal(0)),
    );
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"vm-forged-invalid-symbolic-const")),
        captures: 0,
        parameters: 0,
        registers: vec![
            VmType::I64,
            VmType::Nominal {
                definition: DefKey(Digest::of_bytes(
                    b"vm-forged-invalid-symbolic-const-nominal",
                )),
                arguments: vec![VmType::ConstU32Expr(invalid_expression)],
            },
        ],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 },
            VmInstruction::Return { value: 0 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"vm-forged-invalid-symbolic-const-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::MalformedEncoding { message })
            if message.contains("invalid structural u32 expression")
    ));

    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"vm-top-level-const-register")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::ConstU32(7)],
        instructions: vec![VmInstruction::Trap],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"vm-top-level-const-register-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::MalformedEncoding { message })
            if message.contains("metadata-only structural const")
    ));
}

#[derive(Clone, Copy)]
struct LeaveFixtureOffsets {
    brand_owner: usize,
    target: usize,
    destination_count: usize,
    moved_path: usize,
    moved_binding: usize,
    moved_root: usize,
    moved_field_count: usize,
    loan_owner_tag: usize,
    loan_field_count: usize,
}

#[test]
fn vm_lowers_non_type_effect_arguments_with_their_original_kinds() {
    let effect = DefKey(Digest::of_bytes(b"vm-non-type-effect"));
    let function = MirFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"vm-non-type-effect-caller")),
        captures: 0,
        parameters: vec![],
        locals: vec![MirLocalDecl {
            ty: Type::Scalar(ScalarType::I64),
            source: CoreId(u32::MAX),
        }],
        result: Type::Scalar(ScalarType::I64),
        control: MirControlTables::default(),
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            scope: MirScopeId::ROOT,
            parameters: vec![],
            instructions: vec![MirInstruction::Perform {
                site: MirPerformSiteId::UNASSIGNED,
                dst: MirLocal(0),
                effect,
                effect_arguments: vec![GenericArgument::ConstU32(1)],
                operation: 0,
                arguments: vec![],
            }],
            terminator: MirTerminator::Return { value: MirLocal(0) },
        }],
    }
    .with_frozen_control_tables();
    let artifact = emit_vm(&function).expect("const protocol argument has a VM identity");
    assert!(matches!(
        artifact.function.instructions.as_slice(),
        [VmInstruction::DeclareResult { .. }, VmInstruction::Perform { effect: found, effect_arguments, .. }, ..]
            if *found == effect && effect_arguments == &[VmGenericArgument::ConstU32(1)]
    ));
    let encoded = encode_artifact(&artifact);
    assert_eq!(decode_artifact(&encoded).unwrap(), artifact);
    let decoded = decode_and_verify_artifact(&encoded).unwrap();
    assert_eq!(decoded.fingerprint(), artifact.fingerprint);
    assert_eq!(
        encode_artifact(&decode_artifact(&encoded).unwrap()),
        encoded
    );

    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: artifact.function.definition,
        functions: BTreeMap::from([(artifact.function.definition, artifact.function.clone())]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"vm-effect-argument-program-stale"),
    };
    program.fingerprint = program.computed_fingerprint();
    let program_bytes = encode_program(&program);
    assert_eq!(decode_program(&program_bytes).unwrap(), program);
    assert_eq!(
        decode_and_verify_program(&program_bytes)
            .unwrap()
            .fingerprint(),
        program.fingerprint
    );
}

#[test]
fn vm_rejects_higher_ranked_lifetime_leaks_in_nested_effect_identity_metadata() {
    use grandiose_stage0::{Lifetime, VmEffectRow, VmEffectRowProjection};

    let entry = DefKey(Digest::of_bytes(b"vm-hrtb-effect-metadata-entry"));
    let effect = DefKey(Digest::of_bytes(b"vm-hrtb-effect-metadata-effect"));
    let trait_definition = DefKey(Digest::of_bytes(b"vm-hrtb-effect-metadata-trait"));
    let arguments = vec![VmGenericArgument::EffectRow(VmEffectRow {
        effects: vec![],
        projections: vec![VmEffectRowProjection {
            subject: VmType::I64,
            trait_definition,
            // Bytecode has no HRTB binder namespace.  This placeholder is
            // deliberately buried in projection metadata to prove recursive
            // validation cannot be bypassed through an associated row.
            trait_arguments: vec![VmGenericArgument::Lifetime(Lifetime::Bound {
                depth: 0,
                index: 0,
            })],
            name: "Escaped".into(),
            item_arguments: vec![],
        }],
        tail: None,
    })];
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64],
        instructions: vec![
            VmInstruction::Perform {
                dst: 0,
                effect,
                effect_arguments: arguments,
                operation: 0,
                arguments: vec![],
            },
            VmInstruction::Return { value: 0 },
        ],
    };
    let mut artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: function.clone(),
        fingerprint: Digest::of_bytes(b"stale-vm-hrtb-effect-metadata-artifact"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    let encoded = encode_artifact(&artifact);
    assert_eq!(decode_artifact(&encoded).unwrap(), artifact);
    assert!(matches!(
        verify_vm(artifact),
        Err(VmArtifactError::MalformedEncoding { message })
            if message.contains("escaped higher-ranked lifetime")
    ));

    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(entry, function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"stale-vm-hrtb-effect-metadata-program"),
    };
    program.fingerprint = program.computed_fingerprint();
    let encoded = encode_program(&program);
    assert_eq!(decode_program(&encoded).unwrap(), program);
    assert!(matches!(
        verify_vm_program(program),
        Err(VmArtifactError::MalformedEncoding { message })
            if message.contains("escaped higher-ranked lifetime")
    ));
}

#[test]
fn program_host_capability_declarations_are_canonical_exact_and_fingerprinted() {
    let entry = DefKey(Digest::of_bytes(b"host-capability-entry"));
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64],
        instructions: vec![
            VmInstruction::HostCall {
                dst: 0,
                capability: "clock".into(),
                symbol: "now".into(),
                parameters: vec![],
                result: VmType::I64,
                arguments: vec![],
            },
            VmInstruction::Return { value: 0 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec!["clock".into()],
        entry,
        functions: BTreeMap::from([(entry, function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"stale-host-capability-fingerprint"),
    };
    program.fingerprint = program.computed_fingerprint();
    let bytes = encode_program(&program);
    assert_eq!(decode_program(&bytes).unwrap(), program);
    let verified = verify_vm_program(program.clone()).unwrap();
    assert!(matches!(
        verified.run_i64(),
        Err(VmArtifactError::HostCallRequiresAuthority { capability, symbol })
            if capability == "clock" && symbol == "now"
    ));

    let mut missing = program.clone();
    missing.host_capabilities.clear();
    missing.fingerprint = missing.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(missing),
        Err(VmArtifactError::MalformedEncoding { .. })
    ));

    let mut extra = program.clone();
    extra.host_capabilities = vec!["clock".into(), "network".into()];
    extra.fingerprint = extra.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(extra),
        Err(VmArtifactError::MalformedEncoding { .. })
    ));

    let mut duplicate = program.clone();
    duplicate.host_capabilities = vec!["clock".into(), "clock".into()];
    duplicate.fingerprint = duplicate.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(duplicate),
        Err(VmArtifactError::MalformedEncoding { .. })
    ));

    let mut forged_abi = program.clone();
    let instruction = &mut forged_abi.functions.get_mut(&entry).unwrap().instructions[0];
    let VmInstruction::HostCall { result, .. } = instruction else {
        panic!("fixture must retain a host instruction");
    };
    *result = VmType::Bool;
    forged_abi.fingerprint = forged_abi.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(forged_abi),
        Err(VmArtifactError::TypeMismatch { .. })
    ));

    let mut fingerprint_tamper = program;
    fingerprint_tamper.host_capabilities = vec!["network".into()];
    assert!(matches!(
        verify_vm_program(fingerprint_tamper),
        Err(VmArtifactError::FingerprintMismatch)
    ));
}

#[test]
fn program_host_execution_requires_and_uses_an_explicit_adapter() {
    let entry = DefKey(Digest::of_bytes(b"host-execution-entry"));
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::Text, VmType::Unit],
        instructions: vec![
            VmInstruction::ConstText {
                dst: 0,
                value: "stage one says hello".into(),
            },
            VmInstruction::HostCall {
                dst: 1,
                capability: "diagnostic".into(),
                symbol: "__g1_diagnostic_write".into(),
                parameters: vec![VmType::Text],
                result: VmType::Unit,
                arguments: vec![0],
            },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec!["diagnostic".into()],
        entry,
        functions: BTreeMap::from([(entry, function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"stale-host-execution-fingerprint"),
    };
    program.fingerprint = program.computed_fingerprint();
    let verified = verify_vm_program(program).unwrap();
    assert!(matches!(
        verified.run_unit(),
        Err(VmArtifactError::HostCallRequiresAuthority { .. })
    ));
    let mut host = RecordingVmHost::default();
    verified.run_unit_with_host(&mut host).unwrap();
    assert_eq!(host.diagnostics, ["stage one says hello"]);
}

#[test]
fn program_host_capabilities_exclude_unreachable_emitted_helpers() {
    let entry = DefKey(Digest::of_bytes(b"reachable-host-capability-entry"));
    let unused = DefKey(Digest::of_bytes(b"unreachable-host-capability-helper"));
    let entry_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 },
            VmInstruction::Return { value: 0 },
        ],
    };
    let unused_host_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: unused,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64],
        instructions: vec![
            VmInstruction::HostCall {
                dst: 0,
                capability: "clock".into(),
                symbol: "now".into(),
                parameters: vec![],
                result: VmType::I64,
                arguments: vec![],
            },
            VmInstruction::Return { value: 0 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(entry, entry_function), (unused, unused_host_function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"unreachable-host-capability-stale"),
    };
    program.fingerprint = program.computed_fingerprint();

    let verified = verify_vm_program(program)
        .expect("an unreachable helper must not inflate executable capability declarations");
    assert_eq!(verified.run_i64().unwrap(), 42);
}

#[test]
fn verifier_rejects_cross_function_nominal_layout_and_manifest_order_conflicts() {
    let entry = DefKey(Digest::of_bytes(b"cross-function-layout-entry"));
    let callee = DefKey(Digest::of_bytes(b"cross-function-layout-callee"));
    let nominal = DefKey(Digest::of_bytes(b"cross-function-layout-record"));
    let nominal_type = VmType::Nominal {
        definition: nominal,
        arguments: vec![],
    };
    // The caller constructs `Record { I64 }`, while the callee claims that
    // the same frozen nominal identity is `Record { Bool }`. Both bodies are
    // locally well-typed because VM nominal registers erase fields; only the
    // program graph can reject the contradictory declaration authority.
    let mut conflicting_layouts = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: Some(Digest::of_bytes(b"cross-function-layout-manifest")),
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([
            (
                entry,
                VmFunction {
                    nominal_copy_descriptors: vec![VmNominalCopyDescriptor {
                        definition: nominal,
                        arguments: vec![],
                        variants: vec![vec![VmType::I64]],
                    }],
                    definition: entry,
                    captures: 0,
                    parameters: 0,
                    registers: vec![VmType::I64, nominal_type.clone(), VmType::Bool],
                    instructions: vec![
                        VmInstruction::ConstI64 { dst: 0, value: 42 },
                        VmInstruction::MakeRecord {
                            dst: 1,
                            definition: nominal,
                            fields: vec![0],
                            field_types: vec![VmType::I64],
                        },
                        VmInstruction::Call {
                            dst: 2,
                            callee,
                            arguments: vec![1],
                        },
                        VmInstruction::Return { value: 2 },
                    ],
                },
            ),
            (
                callee,
                VmFunction {
                    nominal_copy_descriptors: vec![VmNominalCopyDescriptor {
                        definition: nominal,
                        arguments: vec![],
                        variants: vec![vec![VmType::Bool]],
                    }],
                    definition: callee,
                    captures: 0,
                    parameters: 1,
                    registers: vec![nominal_type, VmType::Bool],
                    instructions: vec![
                        VmInstruction::ProjectRecord {
                            dst: 1,
                            base: 0,
                            index: 0,
                            field_count: 1,
                            field_type: VmType::Bool,
                        },
                        VmInstruction::Return { value: 1 },
                    ],
                },
            ),
        ]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"cross-function-layout-stale"),
    };
    conflicting_layouts.fingerprint = conflicting_layouts.computed_fingerprint();
    let layout_bytes = encode_program(&conflicting_layouts);
    assert!(matches!(
        verify_vm_program(conflicting_layouts),
        Err(VmArtifactError::MalformedEncoding {
            message: "program nominal layout declarations disagree"
        })
    ));
    assert!(matches!(
        decode_and_verify_program(&layout_bytes),
        Err(VmArtifactError::MalformedEncoding {
            message: "program nominal layout declarations disagree"
        })
    ));

    let helper = DefKey(Digest::of_bytes(b"unordered-capability-helper"));
    let mut unordered_manifest = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: Some(Digest::of_bytes(b"unordered-capability-manifest")),
        // This represents the same authority set as the reachable imports,
        // but serializes it in a different order. Program fingerprints must
        // have one canonical spelling for that manifest.
        host_capabilities: vec!["zeta".into(), "alpha".into()],
        entry,
        functions: BTreeMap::from([
            (
                entry,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: entry,
                    captures: 0,
                    parameters: 0,
                    registers: vec![VmType::I64, VmType::I64],
                    instructions: vec![
                        VmInstruction::Call {
                            dst: 0,
                            callee: helper,
                            arguments: vec![],
                        },
                        VmInstruction::HostCall {
                            dst: 1,
                            capability: "zeta".into(),
                            symbol: "after_call".into(),
                            parameters: vec![],
                            result: VmType::I64,
                            arguments: vec![],
                        },
                        VmInstruction::Return { value: 1 },
                    ],
                },
            ),
            (
                helper,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: helper,
                    captures: 0,
                    parameters: 0,
                    registers: vec![VmType::I64],
                    instructions: vec![
                        VmInstruction::HostCall {
                            dst: 0,
                            capability: "alpha".into(),
                            symbol: "before_call".into(),
                            parameters: vec![],
                            result: VmType::I64,
                            arguments: vec![],
                        },
                        VmInstruction::Return { value: 0 },
                    ],
                },
            ),
        ]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"unordered-capability-stale"),
    };
    unordered_manifest.fingerprint = unordered_manifest.computed_fingerprint();
    let manifest_bytes = encode_program(&unordered_manifest);
    assert!(matches!(
        verify_vm_program(unordered_manifest),
        Err(VmArtifactError::MalformedEncoding {
            message: "host capability declarations are not canonical"
        })
    ));
    assert!(matches!(
        decode_and_verify_program(&manifest_bytes),
        Err(VmArtifactError::MalformedEncoding {
            message: "host capability declarations are not canonical"
        })
    ));
}

#[test]
fn verifier_rejects_reordered_nominal_descriptor_sets_before_cache_or_execution() {
    let entry = DefKey(Digest::of_bytes(b"reordered-nominal-descriptor-entry"));
    let first = DefKey(Digest::of_bytes(b"reordered-nominal-descriptor-first"));
    let second = DefKey(Digest::of_bytes(b"reordered-nominal-descriptor-second"));
    let descriptor = |definition| VmNominalCopyDescriptor {
        definition,
        arguments: vec![],
        variants: vec![vec![]],
    };
    let mut descriptors = vec![descriptor(first), descriptor(second)];
    // Descriptor lookup is by `(definition, arguments)`, never by position.
    // Reverse this otherwise valid set to forge a second byte spelling of the
    // exact same executable layout authority.
    descriptors.sort_by_key(|descriptor| descriptor.definition);
    descriptors.reverse();
    let function = VmFunction {
        nominal_copy_descriptors: descriptors,
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 },
            VmInstruction::Return { value: 0 },
        ],
    };
    let mut reordered = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: Some(Digest::of_bytes(b"reordered-nominal-descriptor-manifest")),
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(entry, function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"reordered-nominal-descriptor-stale"),
    };
    reordered.fingerprint = reordered.computed_fingerprint();
    let bytes = encode_program(&reordered);
    for result in [
        verify_vm_program(reordered),
        decode_and_verify_program(&bytes),
    ] {
        assert!(matches!(
            result,
            Err(VmArtifactError::InvalidCallableEnvironment {
                message: "nominal copy descriptors are not canonical"
            })
        ));
    }
}

#[test]
fn verifier_rejects_cross_function_effect_abi_confusion_before_resumption() {
    let effect = DefKey(Digest::of_bytes(b"cross-function-effect-abi"));
    let caller = DefKey(Digest::of_bytes(b"cross-function-effect-caller"));
    let callee = DefKey(Digest::of_bytes(b"cross-function-effect-callee"));
    // A caller handler supplies I64 for `Ask`, but the callee records its
    // suspended result in a Bool register. The callee has no local handler,
    // so only program-wide dispatch ABI validation can see this mismatch.
    let mut result_confusion = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: Some(Digest::of_bytes(b"cross-function-effect-manifest")),
        host_capabilities: vec![],
        entry: caller,
        functions: BTreeMap::from([
            (
                caller,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: caller,
                    captures: 0,
                    parameters: 0,
                    registers: vec![VmType::I64, VmType::I64],
                    instructions: vec![
                        VmInstruction::InstallHandler {
                            effect,
                            effect_arguments: vec![],
                            operation: 0,
                            payload_destinations: vec![],
                            resume_type: VmType::I64,
                            continuation: VmContinuationPolicy::Consume,
                            target: 5,
                        },
                        VmInstruction::Call {
                            dst: 0,
                            callee,
                            arguments: vec![],
                        },
                        VmInstruction::UninstallHandler,
                        VmInstruction::Return { value: 0 },
                        VmInstruction::Trap,
                        VmInstruction::ConstI64 { dst: 1, value: 7 },
                        VmInstruction::Resume { value: 1 },
                    ],
                },
            ),
            (
                callee,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: callee,
                    captures: 0,
                    parameters: 0,
                    registers: vec![VmType::Bool, VmType::I64],
                    instructions: vec![
                        VmInstruction::Perform {
                            dst: 0,
                            effect,
                            effect_arguments: vec![],
                            operation: 0,
                            arguments: vec![],
                        },
                        VmInstruction::BranchBool {
                            condition: 0,
                            then_target: 2,
                            else_target: 4,
                        },
                        VmInstruction::ConstI64 { dst: 1, value: 42 },
                        VmInstruction::Return { value: 1 },
                        VmInstruction::ConstI64 { dst: 1, value: 0 },
                        VmInstruction::Return { value: 1 },
                    ],
                },
            ),
        ]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"cross-function-effect-result-stale"),
    };
    result_confusion.fingerprint = result_confusion.computed_fingerprint();
    let result_bytes = encode_program(&result_confusion);
    assert!(matches!(
        verify_vm_program(result_confusion),
        Err(VmArtifactError::MalformedEncoding {
            message: "program effect operation ABI declarations disagree"
        })
    ));
    assert!(matches!(
        decode_and_verify_program(&result_bytes),
        Err(VmArtifactError::MalformedEncoding {
            message: "program effect operation ABI declarations disagree"
        })
    ));

    let payload_callee = DefKey(Digest::of_bytes(b"cross-function-effect-payload-callee"));
    let mut payload_confusion = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: Some(Digest::of_bytes(b"cross-function-effect-payload-manifest")),
        host_capabilities: vec![],
        entry: caller,
        functions: BTreeMap::from([
            (
                caller,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: caller,
                    captures: 0,
                    parameters: 0,
                    registers: vec![
                        VmType::I64,
                        VmType::I64,
                        VmType::Callable {
                            parameters: vec![],
                            result: Box::new(VmType::I64),
                            effects: Box::<VmEffectRow>::default(),
                        },
                    ],
                    instructions: vec![
                        VmInstruction::MakeCallable {
                            dst: 2,
                            callee: payload_callee,
                            captures: vec![],
                            environment: None,
                        },
                        VmInstruction::InstallHandler {
                            effect,
                            effect_arguments: vec![],
                            operation: 0,
                            payload_destinations: vec![0],
                            resume_type: VmType::I64,
                            continuation: VmContinuationPolicy::Consume,
                            target: 6,
                        },
                        VmInstruction::CallIndirect {
                            dst: 1,
                            callee: 2,
                            arguments: vec![],
                        },
                        VmInstruction::UninstallHandler,
                        VmInstruction::Return { value: 1 },
                        VmInstruction::Trap,
                        VmInstruction::Cancel,
                        VmInstruction::ConstI64 { dst: 1, value: 42 },
                        VmInstruction::Return { value: 1 },
                    ],
                },
            ),
            (
                payload_callee,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: payload_callee,
                    captures: 0,
                    parameters: 0,
                    registers: vec![VmType::Bool, VmType::I64],
                    instructions: vec![
                        VmInstruction::ConstBool {
                            dst: 0,
                            value: true,
                        },
                        VmInstruction::Perform {
                            dst: 1,
                            effect,
                            effect_arguments: vec![],
                            operation: 0,
                            arguments: vec![0],
                        },
                        VmInstruction::Return { value: 1 },
                    ],
                },
            ),
        ]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"cross-function-effect-payload-stale"),
    };
    payload_confusion.fingerprint = payload_confusion.computed_fingerprint();
    let payload_bytes = encode_program(&payload_confusion);
    assert!(matches!(
        verify_vm_program(payload_confusion),
        Err(VmArtifactError::MalformedEncoding {
            message: "program effect operation ABI declarations disagree"
        })
    ));
    assert!(matches!(
        decode_and_verify_program(&payload_bytes),
        Err(VmArtifactError::MalformedEncoding {
            message: "program effect operation ABI declarations disagree"
        })
    ));

    let mut non_unit_terminal = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: Some(Digest::of_bytes(b"terminal-policy-manifest")),
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"non-unit-terminal-handler")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64],
            instructions: vec![
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 1,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Terminal,
                    target: 2,
                },
                VmInstruction::Trap,
                VmInstruction::Cancel,
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"non-unit-terminal-handler-stale"),
    };
    non_unit_terminal.fingerprint = non_unit_terminal.computed_fingerprint();
    let terminal_bytes = encode_artifact(&non_unit_terminal);
    assert!(matches!(
        verify_vm(non_unit_terminal),
        Err(VmArtifactError::MalformedEncoding {
            message: "terminal handler has a non-unit resume type"
        })
    ));
    assert!(matches!(
        decode_and_verify_artifact(&terminal_bytes),
        Err(VmArtifactError::MalformedEncoding {
            message: "terminal handler has a non-unit resume type"
        })
    ));
}

#[test]
fn verifier_rejects_unspecialized_generic_effect_abis_at_direct_and_callable_boundaries() {
    let effect = DefKey(Digest::of_bytes(b"generic-effect-specialization-effect"));
    let caller = DefKey(Digest::of_bytes(b"generic-effect-specialization-caller"));
    let callee = DefKey(Digest::of_bytes(b"generic-effect-specialization-callee"));

    // The call ABI proves `T = i64`, but the target operation still names
    // `Ask<T>`. Before the specialization check, this passed verification:
    // the global ABI table treated Ask<T> and Ask<i64> as separate keys, then
    // runtime handler lookup failed to find the caller's Ask<i64> frame.
    let generic_callee = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: callee,
        captures: 0,
        parameters: 1,
        registers: vec![VmType::Generic(0), VmType::Generic(0)],
        instructions: vec![
            VmInstruction::Perform {
                dst: 1,
                effect,
                effect_arguments: vec![VmGenericArgument::Type(VmType::Generic(0))],
                operation: 0,
                arguments: vec![0],
            },
            VmInstruction::Return { value: 1 },
        ],
    };
    let direct_caller = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: caller,
        captures: 0,
        parameters: 1,
        registers: vec![VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::InstallHandler {
                effect,
                effect_arguments: vec![VmGenericArgument::Type(VmType::I64)],
                operation: 0,
                payload_destinations: vec![0],
                resume_type: VmType::I64,
                continuation: VmContinuationPolicy::Consume,
                target: 5,
            },
            VmInstruction::Call {
                dst: 1,
                callee,
                arguments: vec![0],
            },
            VmInstruction::UninstallHandler,
            VmInstruction::Return { value: 1 },
            VmInstruction::Trap,
            VmInstruction::Resume { value: 0 },
        ],
    };
    let mut direct = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: Some(Digest::of_bytes(b"generic-effect-specialization-manifest")),
        host_capabilities: vec![],
        entry: caller,
        functions: BTreeMap::from([(caller, direct_caller), (callee, generic_callee.clone())]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"generic-effect-specialization-direct-stale"),
    };
    direct.fingerprint = direct.computed_fingerprint();
    let direct_bytes = encode_program(&direct);
    for result in [
        verify_vm_program(direct),
        decode_and_verify_program(&direct_bytes),
    ] {
        assert!(matches!(
            result,
            Err(VmArtifactError::MalformedEncoding {
                message: "generic effect operation ABI was not specialized for call"
            })
        ));
    }

    let indirect_caller = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: caller,
        captures: 0,
        parameters: 0,
        registers: vec![
            VmType::I64,
            VmType::Callable {
                parameters: vec![VmType::I64],
                result: Box::new(VmType::I64),
                effects: Box::<VmEffectRow>::default(),
            },
            VmType::I64,
        ],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 41 },
            VmInstruction::MakeCallable {
                dst: 1,
                callee,
                captures: vec![],
                environment: None,
            },
            VmInstruction::InstallHandler {
                effect,
                effect_arguments: vec![VmGenericArgument::Type(VmType::I64)],
                operation: 0,
                payload_destinations: vec![0],
                resume_type: VmType::I64,
                continuation: VmContinuationPolicy::Consume,
                target: 7,
            },
            VmInstruction::CallIndirect {
                dst: 2,
                callee: 1,
                arguments: vec![0],
            },
            VmInstruction::UninstallHandler,
            VmInstruction::Return { value: 2 },
            VmInstruction::Trap,
            VmInstruction::Resume { value: 0 },
        ],
    };
    let mut indirect = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: Some(Digest::of_bytes(b"generic-effect-specialization-manifest")),
        host_capabilities: vec![],
        entry: caller,
        functions: BTreeMap::from([(caller, indirect_caller), (callee, generic_callee)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"generic-effect-specialization-indirect-stale"),
    };
    indirect.fingerprint = indirect.computed_fingerprint();
    let indirect_bytes = encode_program(&indirect);
    for result in [
        verify_vm_program(indirect),
        decode_and_verify_program(&indirect_bytes),
    ] {
        assert!(matches!(
            result,
            Err(VmArtifactError::MalformedEncoding {
                message: "generic effect operation ABI was not specialized for call"
            })
        ));
    }
}

#[test]
fn program_handler_resumes_a_performance_from_an_ordinary_callee_frame() {
    let effect = DefKey(Digest::of_bytes(b"cross-frame-ask"));
    let caller = DefKey(Digest::of_bytes(b"cross-frame-caller"));
    let callee = DefKey(Digest::of_bytes(b"cross-frame-callee"));
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: caller,
        functions: BTreeMap::from([
            (
                caller,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: caller,
                    captures: 0,
                    parameters: 0,
                    registers: vec![VmType::I64; 5],
                    instructions: vec![
                        VmInstruction::ConstI64 { dst: 0, value: 41 },
                        VmInstruction::InstallHandler {
                            effect,
                            effect_arguments: vec![],
                            operation: 0,
                            payload_destinations: vec![1],
                            resume_type: VmType::I64,
                            continuation: VmContinuationPolicy::Consume,
                            target: 5,
                        },
                        VmInstruction::Call {
                            dst: 2,
                            callee,
                            arguments: vec![0],
                        },
                        VmInstruction::UninstallHandler,
                        VmInstruction::Return { value: 2 },
                        VmInstruction::ConstI64 { dst: 3, value: 1 },
                        VmInstruction::AddI64 {
                            dst: 4,
                            left: 1,
                            right: 3,
                        },
                        VmInstruction::Resume { value: 4 },
                    ],
                },
            ),
            (
                callee,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: callee,
                    captures: 0,
                    parameters: 1,
                    registers: vec![VmType::I64, VmType::I64],
                    instructions: vec![
                        VmInstruction::Perform {
                            dst: 1,
                            effect,
                            effect_arguments: vec![],
                            operation: 0,
                            arguments: vec![0],
                        },
                        VmInstruction::Return { value: 1 },
                    ],
                },
            ),
        ]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"cross-frame-handler-stale"),
    };
    program.fingerprint = program.computed_fingerprint();
    let bytes = encode_program(&program);
    assert_eq!(decode_program(&bytes).unwrap(), program);
    let program = verify_vm_program(program).unwrap();
    assert!(matches!(
        program.run_i64_with_limits(VmExecutionLimits {
            max_call_depth: 1,
            ..VmExecutionLimits::default()
        }),
        Err(VmArtifactError::CallDepthLimit { limit: 1 })
    ));
    assert!(matches!(
        program.run_i64_with_limits(VmExecutionLimits {
            max_retained_continuations: 0,
            ..VmExecutionLimits::default()
        }),
        Err(VmArtifactError::ContinuationLimit { limit: 0 })
    ));
    assert_eq!(program.run_i64().unwrap(), 42);
}

#[test]
fn program_forwards_a_nested_callee_performance_to_an_ancestor_handler() {
    let effect = DefKey(Digest::of_bytes(b"cross-frame-forward"));
    let outer = DefKey(Digest::of_bytes(b"cross-frame-forward-outer"));
    let middle = DefKey(Digest::of_bytes(b"cross-frame-forward-middle"));
    let leaf = DefKey(Digest::of_bytes(b"cross-frame-forward-leaf"));
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: outer,
        functions: BTreeMap::from([
            (
                outer,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: outer,
                    captures: 0,
                    parameters: 0,
                    registers: vec![VmType::I64; 5],
                    instructions: vec![
                        VmInstruction::ConstI64 { dst: 0, value: 40 },
                        VmInstruction::InstallHandler {
                            effect,
                            effect_arguments: vec![],
                            operation: 0,
                            payload_destinations: vec![1],
                            resume_type: VmType::I64,
                            continuation: VmContinuationPolicy::Consume,
                            target: 6,
                        },
                        VmInstruction::Call {
                            dst: 2,
                            callee: middle,
                            arguments: vec![0],
                        },
                        VmInstruction::UninstallHandler,
                        VmInstruction::Return { value: 2 },
                        VmInstruction::Trap,
                        VmInstruction::ConstI64 { dst: 3, value: 2 },
                        VmInstruction::AddI64 {
                            dst: 4,
                            left: 1,
                            right: 3,
                        },
                        VmInstruction::Resume { value: 4 },
                    ],
                },
            ),
            (
                middle,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: middle,
                    captures: 0,
                    parameters: 1,
                    registers: vec![VmType::I64; 3],
                    instructions: vec![
                        VmInstruction::InstallHandler {
                            effect,
                            effect_arguments: vec![],
                            operation: 0,
                            payload_destinations: vec![2],
                            resume_type: VmType::I64,
                            continuation: VmContinuationPolicy::Consume,
                            target: 5,
                        },
                        VmInstruction::Call {
                            dst: 1,
                            callee: leaf,
                            arguments: vec![0],
                        },
                        VmInstruction::UninstallHandler,
                        VmInstruction::Return { value: 1 },
                        VmInstruction::Trap,
                        VmInstruction::Forward,
                    ],
                },
            ),
            (
                leaf,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: leaf,
                    captures: 0,
                    parameters: 1,
                    registers: vec![VmType::I64; 2],
                    instructions: vec![
                        VmInstruction::Perform {
                            dst: 1,
                            effect,
                            effect_arguments: vec![],
                            operation: 0,
                            arguments: vec![0],
                        },
                        VmInstruction::Return { value: 1 },
                    ],
                },
            ),
        ]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"cross-frame-forward-stale"),
    };
    program.fingerprint = program.computed_fingerprint();
    assert_eq!(verify_vm_program(program).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn program_replay_resumption_returns_after_the_original_caller_path_completes() {
    let effect = DefKey(Digest::of_bytes(b"cross-frame-replay"));
    let caller = DefKey(Digest::of_bytes(b"cross-frame-replay-caller"));
    let callee = DefKey(Digest::of_bytes(b"cross-frame-replay-callee"));
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: caller,
        functions: BTreeMap::from([
            (
                caller,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: caller,
                    captures: 0,
                    parameters: 0,
                    registers: vec![VmType::I64; 8],
                    instructions: vec![
                        VmInstruction::ConstI64 { dst: 0, value: 40 },
                        VmInstruction::InstallHandler {
                            effect,
                            effect_arguments: vec![],
                            operation: 0,
                            payload_destinations: vec![1],
                            resume_type: VmType::I64,
                            continuation: VmContinuationPolicy::Replay { uses: 2 },
                            target: 7,
                        },
                        VmInstruction::Call {
                            dst: 2,
                            callee,
                            arguments: vec![0],
                        },
                        // These instructions are part of the suspended
                        // caller path, not the handler clause. The returned
                        // result distinguishes a real restored call frame
                        // from a direct jump back into the clause.
                        VmInstruction::ConstI64 { dst: 6, value: 10 },
                        VmInstruction::AddI64 {
                            dst: 7,
                            left: 2,
                            right: 6,
                        },
                        VmInstruction::UninstallHandler,
                        VmInstruction::Return { value: 7 },
                        VmInstruction::ConstI64 { dst: 3, value: 2 },
                        VmInstruction::AddI64 {
                            dst: 4,
                            left: 1,
                            right: 3,
                        },
                        VmInstruction::ResumeReturn { dst: 5, value: 4 },
                        // ResumeReturn restores the replay snapshot; the
                        // clause owns its cleanup and must not leave it live.
                        VmInstruction::Cancel,
                        VmInstruction::Return { value: 5 },
                    ],
                },
            ),
            (
                callee,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: callee,
                    captures: 0,
                    parameters: 1,
                    registers: vec![VmType::I64; 2],
                    instructions: vec![
                        VmInstruction::Perform {
                            dst: 1,
                            effect,
                            effect_arguments: vec![],
                            operation: 0,
                            arguments: vec![0],
                        },
                        VmInstruction::Return { value: 1 },
                    ],
                },
            ),
        ]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"cross-frame-replay-stale"),
    };
    program.fingerprint = program.computed_fingerprint();
    assert_eq!(verify_vm_program(program).unwrap().run_i64().unwrap(), 52);
}

#[test]
fn verifier_rejects_an_unrestored_handler_across_a_replay_return() {
    let replayed = DefKey(Digest::of_bytes(b"replay-return-outer"));
    let unrelated = DefKey(Digest::of_bytes(b"replay-return-unrelated"));
    // ResumeReturn may retain frames restored from the suspended continuation,
    // but it must not turn that return edge into a general escape hatch for a
    // fresh handler installed by forged protected bytecode.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"replay-return-frame-proof")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64; 4],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 1 },
                VmInstruction::InstallHandler {
                    effect: replayed,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Replay { uses: 2 },
                    target: 6,
                },
                VmInstruction::Perform {
                    dst: 1,
                    effect: replayed,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![],
                },
                // This is the resumed protected path. The handler at pc 3
                // was never part of the snapshot, so its active return must
                // fail instead of returning to the replay clause.
                VmInstruction::InstallHandler {
                    effect: unrelated,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 10,
                },
                VmInstruction::Return { value: 1 },
                VmInstruction::Trap,
                VmInstruction::ConstI64 { dst: 2, value: 42 },
                VmInstruction::ResumeReturn { dst: 3, value: 2 },
                VmInstruction::Cancel,
                VmInstruction::Return { value: 3 },
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"replay-return-frame-proof-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert!(matches!(
        verify_vm(candidate.clone()),
        Err(VmArtifactError::HandlerStillActive)
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::HandlerStillActive)
    ));
}

#[test]
fn vm_artifacts_round_trip_every_effect_generic_argument_tag() {
    use grandiose_stage0::{
        ConstKind, EffectTail, Lifetime, VmEffectInstance, VmEffectRow, VmEffectRowProjection,
    };

    let nested_effect = DefKey(Digest::of_bytes(b"vm-effect-argument-nested"));
    let trait_definition = DefKey(Digest::of_bytes(b"vm-effect-argument-trait"));
    let effect = DefKey(Digest::of_bytes(b"vm-effect-argument-outer"));
    let arguments = vec![
        VmGenericArgument::Type(VmType::I64),
        VmGenericArgument::EffectRow(VmEffectRow {
            effects: vec![VmEffectInstance {
                definition: nested_effect,
                arguments: vec![VmGenericArgument::ConstU32(7)],
            }],
            projections: vec![VmEffectRowProjection {
                subject: VmType::Generic(1),
                trait_definition,
                // The enclosing trait head is independently mixed-kind.  It
                // must use the same tagged representation as the associated
                // item's own arguments; otherwise schema 30 could still
                // round-trip rows while silently erasing a head lifetime or
                // structural constant.
                trait_arguments: vec![
                    VmGenericArgument::Type(VmType::Text),
                    VmGenericArgument::EffectRow(VmEffectRow {
                        effects: vec![],
                        projections: vec![],
                        tail: Some(EffectTail::Generic(4)),
                    }),
                    VmGenericArgument::Lifetime(Lifetime::Generic(1)),
                    VmGenericArgument::ConstU32(13),
                    VmGenericArgument::ConstQuantity {
                        lower: 1,
                        upper: Some(3),
                    },
                    VmGenericArgument::ConstGeneric {
                        index: 8,
                        kind: ConstKind::U32,
                    },
                ],
                name: "Associated".into(),
                item_arguments: vec![
                    VmGenericArgument::Lifetime(Lifetime::Elided),
                    VmGenericArgument::EffectRow(VmEffectRow {
                        effects: vec![],
                        projections: vec![],
                        tail: Some(EffectTail::Generic(6)),
                    }),
                ],
            }],
            tail: Some(EffectTail::Generic(2)),
        }),
        VmGenericArgument::Lifetime(Lifetime::Generic(3)),
        VmGenericArgument::ConstU32(11),
        VmGenericArgument::ConstQuantity {
            lower: 4,
            upper: Some(9),
        },
        VmGenericArgument::ConstGeneric {
            index: 5,
            kind: ConstKind::Quantity,
        },
    ];
    let mut artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"vm-effect-argument-round-trip")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64],
            instructions: vec![
                VmInstruction::Perform {
                    dst: 0,
                    effect,
                    effect_arguments: arguments.clone(),
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"vm-effect-argument-round-trip-stale"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    let encoded = encode_artifact(&artifact);
    assert_eq!(decode_artifact(&encoded).unwrap(), artifact);

    // This fixture has one I64 register and a leading `Perform`; its first
    // argument tag is therefore fixed. An unknown tag must fail decoding
    // before the candidate reaches artifact verification.
    // Schema 38 inserts the canonical nominal-copy descriptor count between
    // registers and the instruction stream (zero descriptors here).
    let generic_argument_tag = 53 + 32 + 8 + 8 + 8 + 1 + 8 + 1 + 4 + 32 + 8;
    assert_eq!(encoded[generic_argument_tag], 0);
    let mut hostile = encoded.clone();
    hostile[generic_argument_tag] = u8::MAX;
    assert!(matches!(
        decode_artifact(&hostile),
        Err(VmArtifactError::MalformedEncoding {
            message: "unknown VM effect argument tag"
        })
    ));

    let nested_effect_tag = generic_argument_tag + 2;
    assert_eq!(encoded[nested_effect_tag], 1);
    let mut invalid_nested_tag = encoded.clone();
    invalid_nested_tag[nested_effect_tag] = u8::MAX;
    assert!(decode_and_verify_artifact(&invalid_nested_tag).is_err());

    let mut excessive_instances = encoded.clone();
    excessive_instances[nested_effect_tag + 1..nested_effect_tag + 9]
        .copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(matches!(
        decode_artifact(&excessive_instances),
        Err(VmArtifactError::DecodeLimit { .. })
    ));

    let projection_count = nested_effect_tag + 1 + 8 + 32 + 8 + 1 + 4;
    let mut excessive_projections = encoded;
    excessive_projections[projection_count..projection_count + 8]
        .copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(matches!(
        decode_and_verify_artifact(&excessive_projections),
        Err(VmArtifactError::DecodeLimit { .. })
    ));
}

#[test]
fn vm_decoder_rejects_noncanonical_effect_row_instances() {
    use grandiose_stage0::{VmEffectInstance, VmEffectRow};

    let mut definitions = [
        DefKey(Digest::of_bytes(b"effect-row-order-a")),
        DefKey(Digest::of_bytes(b"effect-row-order-b")),
    ];
    definitions.sort();
    let mut artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"effect-row-order-caller")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64],
            instructions: vec![
                VmInstruction::Perform {
                    dst: 0,
                    effect: DefKey(Digest::of_bytes(b"effect-row-order-outer")),
                    effect_arguments: vec![VmGenericArgument::EffectRow(VmEffectRow {
                        effects: vec![
                            VmEffectInstance {
                                definition: definitions[1],
                                arguments: vec![],
                            },
                            VmEffectInstance {
                                definition: definitions[0],
                                arguments: vec![],
                            },
                        ],
                        projections: vec![],
                        tail: None,
                    })],
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"effect-row-order-stale"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    assert!(matches!(
        verify_vm(artifact.clone()),
        Err(VmArtifactError::NonCanonicalEncoding)
    ));
    assert!(matches!(
        decode_artifact(&encode_artifact(&artifact)),
        Err(VmArtifactError::NonCanonicalEncoding)
    ));
}

/// Byte positions for the intentionally fixed-shape `Leave` fixture below.
/// Keeping these offsets alongside the fixture makes every hostile mutation
/// explicit and protects against silently testing a different instruction.
fn leave_fixture_offsets(bytes: &[u8]) -> LeaveFixtureOffsets {
    // Envelope: magic (8), schema (4), fingerprint (32), no manifest (1),
    // payload size (8). Function: definition (32), captures/parameters (8),
    // two I64 register types (10), descriptor count (8), instruction count
    // (8), ConstI64 (13).
    let leave_opcode = 53 + 32 + 8 + 10 + 8 + 8 + 13;
    assert_eq!(bytes[leave_opcode], 55, "fixture no longer encodes Leave");
    let brand_owner = leave_opcode + 1;
    let target = brand_owner + 32 + 4 + 4;
    let argument_count = target + 4;
    let destination_count = argument_count + 8 + 4;
    let cleanup = destination_count + 8 + 4;
    let moved_path = cleanup + 8;
    let moved_root_length = moved_path + 8;
    let moved_fields = moved_root_length + 8 + b"value".len();
    let loan_count = moved_fields + 8 + 4;
    let loan_owner_tag = loan_count + 8;
    let loan_root_length = loan_owner_tag + 1 + 4;
    let loan_fields = loan_root_length + 8 + b"loan".len();
    LeaveFixtureOffsets {
        brand_owner,
        target,
        destination_count,
        moved_path,
        moved_binding: moved_path + 4,
        moved_root: moved_root_length + 8,
        moved_field_count: moved_fields,
        loan_owner_tag,
        loan_field_count: loan_fields,
    }
}

/// Candidate decoding deliberately does not authenticate the fingerprint;
/// replacing it lets a test isolate verifier rejection of a canonical payload
/// mutation rather than merely testing the integrity check.
fn rebind_artifact_fingerprint(bytes: &mut Vec<u8>) {
    let mut artifact = decode_artifact(bytes).expect("canonical hostile mutation decodes");
    artifact.fingerprint = artifact.computed_fingerprint();
    *bytes = encode_artifact(&artifact);
}

/// One small schema-27 artifact whose payload contains every fixed `Leave`
/// header field plus both parallel register vectors and a cleanup proof. Tests
/// mutate this canonical byte image rather than relying on Debug formatting.
fn encoded_leave_fixture() -> Vec<u8> {
    let mut artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"hostile-leave-fixture")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 7 },
                VmInstruction::Leave {
                    brand_owner: DefKey(Digest::of_bytes(b"hostile-leave-owner")),
                    brand_label: 9,
                    handler_depth: 0,
                    target: 2,
                    arguments: vec![0],
                    destinations: vec![1],
                    cleanup: VmCleanupProof {
                        moved_places: vec![VmCleanupPlace {
                            path: 0,
                            binding: 0,
                            root: "value".into(),
                            fields: vec![0],
                        }],
                        active_loans: vec![VmCleanupLoan {
                            owner: None,
                            binding: 1,
                            root: "loan".into(),
                            fields: vec![1],
                            unique: false,
                        }],
                        storage_erasure: VmStorageErasureWitness::without_source_storage(),
                    },
                },
                VmInstruction::Return { value: 1 },
            ],
        },
        fingerprint: Digest::of_bytes(b"hostile-leave-fixture-fingerprint"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    encode_artifact(&artifact)
}

/// The entry shape shared by the standalone and program envelopes below. The
/// first instruction materializes the value transferred through the `Leave`:
/// a literal in the standalone VM and a cross-function call in the program.
fn cleanup_carrying_leave_entry(definition: DefKey, first: VmInstruction) -> VmFunction {
    VmFunction {
        definition,
        nominal_copy_descriptors: vec![],
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64],
        instructions: vec![
            first,
            VmInstruction::InstallHandler {
                effect: DefKey(Digest::of_bytes(b"leave-parity-handler")),
                effect_arguments: vec![],
                operation: 0,
                payload_destinations: vec![],
                resume_type: VmType::I64,
                continuation: VmContinuationPolicy::Consume,
                target: 4,
            },
            VmInstruction::Leave {
                brand_owner: definition,
                brand_label: 3,
                handler_depth: 0,
                target: 3,
                arguments: vec![0],
                destinations: vec![1],
                cleanup: VmCleanupProof {
                    moved_places: vec![VmCleanupPlace {
                        path: 0,
                        binding: 0,
                        root: "result".into(),
                        fields: vec![0],
                    }],
                        active_loans: vec![VmCleanupLoan {
                        owner: Some("frame".into()),
                        binding: 0,
                        root: "result".into(),
                        fields: vec![1],
                            unique: true,
                        }],
                        storage_erasure: VmStorageErasureWitness::without_source_storage(),
                    },
            },
            VmInstruction::Return { value: 1 },
            // This is a private handler-clause entry. The Leave skips it and
            // thereby proves that it unwinds the installed handler frame.
            VmInstruction::Trap,
        ],
    }
}

fn make_leave_cleanup_noncanonical(function: &mut VmFunction) {
    let VmInstruction::Leave { cleanup, .. } = &mut function.instructions[2] else {
        panic!("cleanup parity fixture must contain a Leave at instruction 2");
    };
    cleanup.moved_places.push(cleanup.moved_places[0].clone());
}

/// A verified CFG with a statically reachable return, but whose true runtime
/// branch repeatedly crosses a cleanup-carrying `Leave`. This is the smallest
/// shape that proves nonlocal edges cannot skip instruction accounting.
fn cleanup_leave_budget_loop(definition: DefKey) -> VmFunction {
    VmFunction {
        definition,
        nominal_copy_descriptors: vec![],
        captures: 0,
        parameters: 0,
        registers: vec![VmType::Bool, VmType::I64],
        instructions: vec![
            VmInstruction::ConstBool {
                dst: 0,
                value: true,
            },
            VmInstruction::ConstI64 { dst: 1, value: 42 },
            VmInstruction::BranchBool {
                condition: 0,
                then_target: 3,
                else_target: 4,
            },
            VmInstruction::Leave {
                brand_owner: definition,
                brand_label: 4,
                handler_depth: 0,
                target: 2,
                arguments: vec![],
                destinations: vec![],
                cleanup: VmCleanupProof {
                    moved_places: vec![VmCleanupPlace {
                        path: 0,
                        binding: 0,
                        root: "loop".into(),
                        fields: vec![0],
                    }],
                    active_loans: vec![],
                    storage_erasure: VmStorageErasureWitness::without_source_storage(),
                },
            },
            VmInstruction::Return { value: 1 },
        ],
    }
}

fn aggregate_allocation_fixture(definition: DefKey) -> VmFunction {
    VmFunction {
        definition,
        nominal_copy_descriptors: vec![],
        captures: 0,
        parameters: 0,
        registers: vec![
            VmType::I64,
            VmType::I64,
            VmType::Array(Box::new(VmType::I64)),
        ],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 7 },
            VmInstruction::ConstI64 { dst: 1, value: 8 },
            VmInstruction::MakeArray {
                dst: 2,
                fields: vec![0, 1],
                element_type: VmType::I64,
            },
            VmInstruction::Return { value: 0 },
        ],
    }
}

fn handler_payload_allocation_fixture(definition: DefKey) -> VmFunction {
    VmFunction {
        definition,
        nominal_copy_descriptors: vec![],
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 7 },
            VmInstruction::ConstI64 { dst: 1, value: 8 },
            VmInstruction::Perform {
                dst: 2,
                effect: DefKey(Digest::of_bytes(b"allocation-payload-effect")),
                effect_arguments: vec![],
                operation: 0,
                arguments: vec![0, 1],
            },
            VmInstruction::Return { value: 2 },
        ],
    }
}

fn assert_continuation_budget_parity(function: VmFunction, max_instructions: u64) {
    let definition = function.definition;
    let mut artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: function.clone(),
        fingerprint: Digest::of_bytes(b"continuation-budget-artifact"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    let limits = VmExecutionLimits {
        max_instructions,
        ..VmExecutionLimits::default()
    };
    assert!(matches!(
        verify_vm(artifact).unwrap().run_i64_with_limits(limits),
        Err(VmArtifactError::InstructionLimit { limit }) if limit == max_instructions
    ));
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: definition,
        functions: BTreeMap::from([(definition, function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"continuation-budget-program"),
    };
    program.fingerprint = program.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(program)
            .unwrap()
            .run_i64_with_limits(limits),
        Err(VmArtifactError::InstructionLimit { limit }) if limit == max_instructions
    ));
}

fn assert_continuation_retention_parity(function: VmFunction) {
    let definition = function.definition;
    let mut artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: function.clone(),
        fingerprint: Digest::of_bytes(b"continuation-retention-artifact"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    let limits = VmExecutionLimits {
        max_retained_continuations: 0,
        ..VmExecutionLimits::default()
    };
    assert!(matches!(
        verify_vm(artifact).unwrap().run_i64_with_limits(limits),
        Err(VmArtifactError::ContinuationLimit { limit: 0 })
    ));
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: definition,
        functions: BTreeMap::from([(definition, function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"continuation-retention-program"),
    };
    program.fingerprint = program.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(program)
            .unwrap()
            .run_i64_with_limits(limits),
        Err(VmArtifactError::ContinuationLimit { limit: 0 })
    ));
}

#[test]
fn schema_26_leave_bytes_reject_every_truncation_and_fingerprint_tampering() {
    let bytes = encoded_leave_fixture();
    assert!(decode_and_verify_artifact(&bytes).is_ok());
    for length in 0..bytes.len() {
        assert!(
            decode_artifact(&bytes[..length]).is_err(),
            "truncated Leave artifact at byte {length} decoded"
        );
    }
    // Magic (8) + schema (4) precede the semantic artifact fingerprint.
    let mut tampered = bytes;
    tampered[12] ^= 1;
    assert!(matches!(
        decode_and_verify_artifact(&tampered),
        Err(VmArtifactError::FingerprintMismatch)
    ));
}

#[test]
fn schema_26_leave_payload_mutations_reject_before_vm_execution() {
    let bytes = encoded_leave_fixture();
    let offsets = leave_fixture_offsets(&bytes);

    let mut invalid_owner_tag = bytes.clone();
    invalid_owner_tag[offsets.loan_owner_tag] = 2;
    assert!(matches!(
        decode_and_verify_artifact(&invalid_owner_tag),
        Err(VmArtifactError::MalformedEncoding {
            message: "invalid cleanup loan owner tag"
        })
    ));

    for (field_count, label) in [
        (offsets.moved_field_count, "moved-place"),
        (offsets.loan_field_count, "active-loan"),
    ] {
        let mut impossible_fields = bytes.clone();
        impossible_fields[field_count..field_count + 8].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(
            matches!(
                decode_and_verify_artifact(&impossible_fields),
                Err(VmArtifactError::DecodeLimit { .. })
            ),
            "impossible {label} fields reached the VM boundary"
        );
    }

    let mut malformed_parallel_payload = bytes.clone();
    malformed_parallel_payload[offsets.destination_count..offsets.destination_count + 8]
        .copy_from_slice(&0_u64.to_le_bytes());
    assert!(matches!(
        decode_and_verify_artifact(&malformed_parallel_payload),
        Err(VmArtifactError::MalformedEncoding {
            message: "leave arguments and destinations differ in length"
        })
    ));

    let mut invalid_target = bytes.clone();
    invalid_target[offsets.target..offsets.target + 4].copy_from_slice(&u32::MAX.to_le_bytes());
    rebind_artifact_fingerprint(&mut invalid_target);
    assert!(matches!(
        decode_and_verify_artifact(&invalid_target),
        Err(VmArtifactError::InvalidInstructionTarget { target: u32::MAX })
    ));

    let mut stale_path = bytes.clone();
    stale_path[offsets.moved_path..offsets.moved_path + 4].copy_from_slice(&u32::MAX.to_le_bytes());
    rebind_artifact_fingerprint(&mut stale_path);
    assert!(matches!(
        decode_and_verify_artifact(&stale_path),
        Err(VmArtifactError::MalformedEncoding {
            message: "leave cleanup proof is not canonical"
        })
    ));

    let mut stale_binding = bytes.clone();
    stale_binding[offsets.moved_binding..offsets.moved_binding + 4]
        .copy_from_slice(&u32::MAX.to_le_bytes());
    rebind_artifact_fingerprint(&mut stale_binding);
    assert!(matches!(
        decode_and_verify_artifact(&stale_binding),
        Err(VmArtifactError::MalformedEncoding {
            message: "leave cleanup proof is not canonical"
        })
    ));

    // Diagnostic roots do not participate in cleanup ownership identity.
    let mut renamed_presentation = bytes.clone();
    renamed_presentation[offsets.moved_root..offsets.moved_root + b"value".len()]
        .copy_from_slice(b"other");
    rebind_artifact_fingerprint(&mut renamed_presentation);
    assert!(decode_and_verify_artifact(&renamed_presentation).is_ok());

    // Label brands are immutable artifact payload. A raw owner substitution is
    // rejected by the verifier's fingerprint gate before any control transfer.
    let mut unknown_brand_owner = bytes;
    unknown_brand_owner[offsets.brand_owner] ^= 1;
    assert!(matches!(
        decode_and_verify_artifact(&unknown_brand_owner),
        Err(VmArtifactError::FingerprintMismatch)
    ));
}

#[test]
fn fixed_seed_hostile_decoder_corpus_never_panics_or_bypasses_bounds() {
    // This is a deterministic, CI-friendly complement to the structured
    // truncation and field-mutation fixtures above.  It exercises both wire
    // envelopes with arbitrary lengths and bytes, ensuring every hostile
    // count, tag, and nested decoder path remains an ordinary error instead
    // of a panic or unbounded allocation attempt.
    let mut state = 0x4d59_5df4_d0f3_3173_u64;
    for case in 0..256_usize {
        let length = (case * 37 + 11) % 513;
        let mut bytes = Vec::with_capacity(length);
        for _ in 0..length {
            state ^= state << 7;
            state ^= state >> 9;
            state ^= state << 8;
            bytes.push(state as u8);
        }
        let result = std::panic::catch_unwind(|| {
            let _ = decode_and_verify_artifact(&bytes);
            let _ = decode_and_verify_program(&bytes);
        });
        assert!(
            result.is_ok(),
            "hostile decoder corpus case {case} panicked at length {length}"
        );
    }
}

#[test]
fn verifier_rejects_leave_storage_witnesses_with_divergent_storage_and_binding_ids() {
    let definition = DefKey(Digest::of_bytes(b"detached-leave-storage-witness"));
    // The cleanup sequence is otherwise canonical, but its storage handle
    // diverges from the frozen binding identity. Those names are one dense
    // source-owner identity at the VM boundary, not two forgeable aliases.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition,
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::Leave {
                    brand_owner: definition,
                    brand_label: 0,
                    handler_depth: 0,
                    target: 2,
                    arguments: vec![0],
                    destinations: vec![1],
                    cleanup: VmCleanupProof {
                        moved_places: vec![],
                        active_loans: vec![],
                        storage_erasure: VmStorageErasureWitness::Verified {
                            storages: vec![VmStorageErasureStorage {
                                storage: 1,
                                binding: 0,
                                value_register: 0,
                                initialized: true,
                                drop_flag: Some(1),
                            }],
                            actions: vec![
                                VmStorageErasureAction::Destroy { storage: 1 },
                                VmStorageErasureAction::SetDropFlag {
                                    drop_flag: 1,
                                    initialized: false,
                                },
                                VmStorageErasureAction::StorageDead { storage: 1 },
                            ],
                            protected_registers: vec![],
                        },
                    },
                },
                VmInstruction::Return { value: 1 },
            ],
        },
        fingerprint: Digest::of_bytes(b"detached-leave-storage-witness-fingerprint"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::MalformedEncoding {
            message: "leave source-storage erasure witness is not canonical"
        })
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::MalformedEncoding {
            message: "leave source-storage erasure witness is not canonical"
        })
    ));
}

#[test]
fn verifier_rejects_writes_that_resurrect_dead_source_storage() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"resurrected-source-storage")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64],
            instructions: vec![
                VmInstruction::StorageLive {
                    binding: 0,
                    local: 0,
                },
                VmInstruction::StorageDead {
                    binding: 0,
                    local: 0,
                },
                // This used to be accepted because a dead source slot had
                // the same `None` register state as an ordinary SSA value.
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"resurrected-source-storage-fingerprint"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::ReadBeforeWrite { register: 0 })
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::ReadBeforeWrite { register: 0 })
    ));
}

#[test]
fn verifier_rejects_labels_laundered_through_mutable_storage() {
    let owner = DefKey(Digest::of_bytes(b"label-mutable-storage-owner"));
    let label = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::Unit),
        effects: Box::<VmEffectRow>::default(),
    };
    let closure = VmType::Callable {
        parameters: vec![],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    // Labels remain legal ordinary call arguments, but they must not become
    // capturable merely by passing through a mutable addressable slot.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: owner,
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                label.clone(),
                VmType::Reference {
                    unique: true,
                    referent: Box::new(label.clone()),
                },
                label.clone(),
                label,
                closure,
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::MakeCallable {
                    dst: 1,
                    callee: DefKey(Digest::of_bytes(b"label-mutable-storage-initial")),
                    captures: vec![],
                    environment: None,
                },
                VmInstruction::Borrow {
                    dst: 2,
                    src: 1,
                    fields: vec![],
                    unique: true,
                    reborrow: false,
                },
                VmInstruction::MakeLabel {
                    dst: 3,
                    brand_owner: owner,
                    brand_label: 1,
                    target: 7,
                    destination: 0,
                },
                VmInstruction::DerefStore {
                    reference: 2,
                    src: 3,
                },
                VmInstruction::DerefCopy {
                    dst: 4,
                    reference: 2,
                },
                VmInstruction::MakeCallable {
                    dst: 5,
                    callee: DefKey(Digest::of_bytes(b"label-mutable-storage-closure")),
                    captures: vec![4],
                    environment: None,
                },
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"label-mutable-storage-fingerprint"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::InvalidLabelContract { .. })
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::InvalidLabelContract { .. })
    ));
}

#[test]
fn verifier_rejects_storage_death_while_a_borrow_remains_live() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"live-borrow-after-storage-dead")),
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                VmType::Reference {
                    unique: false,
                    referent: Box::new(VmType::I64),
                },
                VmType::I64,
                VmType::I64,
            ],
            instructions: vec![
                VmInstruction::StorageLive {
                    binding: 0,
                    local: 0,
                },
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::Borrow {
                    dst: 1,
                    src: 0,
                    fields: vec![],
                    unique: false,
                    reborrow: false,
                },
                VmInstruction::Move { dst: 2, src: 0 },
                // Moving the resident value must not make its live borrow
                // harmless: this ends the addressable source slot too early.
                VmInstruction::StorageDead {
                    binding: 0,
                    local: 0,
                },
                VmInstruction::DerefCopy {
                    dst: 3,
                    reference: 1,
                },
                VmInstruction::Return { value: 3 },
            ],
        },
        fingerprint: Digest::of_bytes(b"live-borrow-after-storage-dead-fingerprint"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::ReadBeforeWrite { register: 0 })
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::ReadBeforeWrite { register: 0 })
    ));
}

#[test]
fn verifier_rejects_program_map_keys_that_disagree_with_function_identity() {
    let entry = DefKey(Digest::of_bytes(b"forged-program-map-entry"));
    let embedded = DefKey(Digest::of_bytes(b"forged-program-embedded-definition"));
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: embedded,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 },
            VmInstruction::Return { value: 0 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(entry, function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"forged-program-map-key-fingerprint"),
    };
    program.fingerprint = program.computed_fingerprint();
    let bytes = encode_program(&program);
    assert!(matches!(
        verify_vm_program(program),
        Err(VmArtifactError::MalformedEncoding {
            message: "program function map key does not match definition"
        })
    ));
    // The wire format carries only the embedded identity, so decoding repairs
    // the map key and leaves the forged entry missing; it is rejected before
    // program execution either way.
    assert!(matches!(
        decode_and_verify_program(&bytes),
        Err(VmArtifactError::MissingFunction { definition }) if definition == entry
    ));
}

#[test]
fn program_envelope_rejects_truncation_and_function_count_amplification_before_allocation() {
    let entry = DefKey(Digest::of_bytes(b"program-decode-limit-entry"));
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 },
            VmInstruction::Return { value: 0 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(entry, function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"program-decode-limit-fingerprint"),
    };
    program.fingerprint = program.computed_fingerprint();
    let bytes = encode_program(&program);
    for length in 0..bytes.len() {
        assert!(
            decode_program(&bytes[..length]).is_err(),
            "truncated program at {length}"
        );
    }
    // Program envelope: magic (8), schema (4), entry (32), fingerprint (32),
    // no manifest tag (1), empty capability vector (8), then the bounded
    // function-count vector.
    let mut amplified = bytes;
    amplified[85..93]
        .copy_from_slice(&(grandiose_stage0::STAGE0_MAX_DECODE_FUNCTIONS + 1).to_le_bytes());
    assert!(matches!(
        decode_and_verify_program(&amplified),
        Err(VmArtifactError::DecodeLimit {
            kind: "functions",
            limit: grandiose_stage0::STAGE0_MAX_DECODE_FUNCTIONS,
        })
    ));
}

#[test]
fn cleanup_carrying_leave_has_standalone_and_multifunction_program_parity() {
    let standalone_definition = DefKey(Digest::of_bytes(b"leave-parity-standalone"));
    let standalone_function = cleanup_carrying_leave_entry(
        standalone_definition,
        VmInstruction::ConstI64 { dst: 0, value: 42 },
    );
    let mut standalone = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: standalone_function.clone(),
        fingerprint: Digest::of_bytes(b"leave-parity-standalone-fingerprint"),
    };
    standalone.fingerprint = standalone.computed_fingerprint();
    let standalone_bytes = encode_artifact(&standalone);
    assert_eq!(decode_artifact(&standalone_bytes).unwrap(), standalone);
    assert_eq!(
        decode_and_verify_artifact(&standalone_bytes)
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );

    let entry = DefKey(Digest::of_bytes(b"leave-parity-program-entry"));
    let helper = DefKey(Digest::of_bytes(b"leave-parity-program-helper"));
    let entry_function = cleanup_carrying_leave_entry(
        entry,
        VmInstruction::Call {
            dst: 0,
            callee: helper,
            arguments: vec![],
        },
    );
    let helper_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: helper,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 },
            VmInstruction::Return { value: 0 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([
            (entry, entry_function.clone()),
            (helper, helper_function.clone()),
        ]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"leave-parity-program-fingerprint"),
    };
    program.fingerprint = program.computed_fingerprint();
    let program_bytes = encode_program(&program);
    assert_eq!(decode_program(&program_bytes).unwrap(), program);
    assert_eq!(
        decode_and_verify_program(&program_bytes)
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );

    // Both envelopes must reject a canonical but semantically malformed
    // cleanup proof before execution. The program keeps its helper valid so
    // this specifically exercises the multi-function program envelope.
    let mut malformed_standalone_function = standalone_function;
    make_leave_cleanup_noncanonical(&mut malformed_standalone_function);
    let mut malformed_standalone = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: malformed_standalone_function,
        fingerprint: Digest::of_bytes(b"leave-parity-malformed-standalone"),
    };
    malformed_standalone.fingerprint = malformed_standalone.computed_fingerprint();
    let malformed_standalone_bytes = encode_artifact(&malformed_standalone);
    assert!(decode_artifact(&malformed_standalone_bytes).is_ok());
    assert!(matches!(
        decode_and_verify_artifact(&malformed_standalone_bytes),
        Err(VmArtifactError::MalformedEncoding {
            message: "leave cleanup proof is not canonical"
        })
    ));

    let mut malformed_entry_function = entry_function;
    make_leave_cleanup_noncanonical(&mut malformed_entry_function);
    let mut malformed_program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(entry, malformed_entry_function), (helper, helper_function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"leave-parity-malformed-program"),
    };
    malformed_program.fingerprint = malformed_program.computed_fingerprint();
    let malformed_program_bytes = encode_program(&malformed_program);
    assert!(decode_program(&malformed_program_bytes).is_ok());
    assert!(matches!(
        decode_and_verify_program(&malformed_program_bytes),
        Err(VmArtifactError::MalformedEncoding {
            message: "leave cleanup proof is not canonical"
        })
    ));
}

#[test]
fn cleanup_carrying_leave_cannot_evict_artifact_or_program_execution_limits() {
    let definition = DefKey(Digest::of_bytes(b"leave-budget-loop"));
    let loop_function = cleanup_leave_budget_loop(definition);
    let mut artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: loop_function.clone(),
        fingerprint: Digest::of_bytes(b"leave-budget-loop-artifact"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    let artifact = verify_vm(artifact).unwrap();
    let step_limit = VmExecutionLimits {
        max_call_depth: 1,
        max_handler_depth: 1,
        max_instructions: 4,
        ..VmExecutionLimits::default()
    };
    assert!(matches!(
        artifact.run_i64_with_limits(step_limit),
        Err(VmArtifactError::InstructionLimit { limit: 4 })
    ));
    assert!(matches!(
        artifact.run_i64_with_limits(VmExecutionLimits {
            max_call_depth: 0,
            ..step_limit
        }),
        Err(VmArtifactError::CallDepthLimit { limit: 0 })
    ));

    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: definition,
        functions: BTreeMap::from([(definition, loop_function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"leave-budget-loop-program"),
    };
    program.fingerprint = program.computed_fingerprint();
    let program = verify_vm_program(program).unwrap();
    assert!(matches!(
        program.run_i64_with_limits(step_limit),
        Err(VmArtifactError::InstructionLimit { limit: 4 })
    ));
    assert!(matches!(
        program.run_i64_with_limits(VmExecutionLimits {
            max_call_depth: 0,
            ..step_limit
        }),
        Err(VmArtifactError::CallDepthLimit { limit: 0 })
    ));
}

#[test]
fn program_call_depth_limit_classifies_recursive_execution() {
    let definition = DefKey(Digest::of_bytes(b"recursive-call-depth"));
    let recursive = VmFunction {
        definition,
        nominal_copy_descriptors: vec![],
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64],
        instructions: vec![
            VmInstruction::Call {
                dst: 0,
                callee: definition,
                arguments: vec![],
            },
            VmInstruction::Return { value: 0 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: definition,
        functions: BTreeMap::from([(definition, recursive)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"recursive-call-depth-fingerprint"),
    };
    program.fingerprint = program.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(program)
            .unwrap()
            .run_i64_with_limits(VmExecutionLimits {
                max_call_depth: 2,
                max_handler_depth: 1,
                max_instructions: 100,
                ..VmExecutionLimits::default()
            }),
        Err(VmArtifactError::CallDepthLimit { limit: 2 })
    ));
}

#[test]
fn aggregate_and_handler_payload_allocation_limits_cover_both_vm_engines() {
    let aggregate_definition = DefKey(Digest::of_bytes(b"aggregate-allocation-limits"));
    let aggregate_function = aggregate_allocation_fixture(aggregate_definition);
    let mut aggregate_artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: aggregate_function.clone(),
        fingerprint: Digest::of_bytes(b"aggregate-allocation-artifact"),
    };
    aggregate_artifact.fingerprint = aggregate_artifact.computed_fingerprint();
    let aggregate_artifact = verify_vm(aggregate_artifact).unwrap();
    let size_limit = VmExecutionLimits {
        max_value_elements: 1,
        ..VmExecutionLimits::default()
    };
    assert!(matches!(
        aggregate_artifact.run_i64_with_limits(size_limit),
        Err(VmArtifactError::ValueSizeLimit {
            kind: "array elements",
            limit: 1,
            found: 2,
        })
    ));
    let allocation_limit = VmExecutionLimits {
        max_value_elements: 2,
        // Three register slots plus the two-element array exceed this cap.
        max_allocation_elements: 4,
        ..VmExecutionLimits::default()
    };
    assert!(matches!(
        aggregate_artifact.run_i64_with_limits(allocation_limit),
        Err(VmArtifactError::AllocationLimit { limit: 4 })
    ));

    let mut aggregate_program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: aggregate_definition,
        functions: BTreeMap::from([(aggregate_definition, aggregate_function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"aggregate-allocation-program"),
    };
    aggregate_program.fingerprint = aggregate_program.computed_fingerprint();
    let aggregate_program = verify_vm_program(aggregate_program).unwrap();
    assert!(matches!(
        aggregate_program.run_i64_with_limits(size_limit),
        Err(VmArtifactError::ValueSizeLimit {
            kind: "array elements",
            limit: 1,
            found: 2,
        })
    ));
    assert!(matches!(
        aggregate_program.run_i64_with_limits(allocation_limit),
        Err(VmArtifactError::AllocationLimit { limit: 4 })
    ));

    let payload_definition = DefKey(Digest::of_bytes(b"handler-payload-allocation-limits"));
    let payload_function = handler_payload_allocation_fixture(payload_definition);
    let mut payload_artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: payload_function.clone(),
        fingerprint: Digest::of_bytes(b"handler-payload-allocation-artifact"),
    };
    payload_artifact.fingerprint = payload_artifact.computed_fingerprint();
    let payload_artifact = verify_vm(payload_artifact).unwrap();
    assert!(matches!(
        payload_artifact.run_i64_with_limits(size_limit),
        Err(VmArtifactError::ValueSizeLimit {
            kind: "handler payload",
            limit: 1,
            found: 2,
        })
    ));

    let mut payload_program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: payload_definition,
        functions: BTreeMap::from([(payload_definition, payload_function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"handler-payload-allocation-program"),
    };
    payload_program.fingerprint = payload_program.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(payload_program)
            .unwrap()
            .run_i64_with_limits(size_limit),
        Err(VmArtifactError::ValueSizeLimit {
            kind: "handler payload",
            limit: 1,
            found: 2,
        })
    ));
}

#[test]
fn verified_stage_zero_vm_artifact_executes_lowered_mir() {
    let package = PackageKey("vm@0.1.0".into());
    let source = "pub fn main() -> i64 { let value = 8; value * 5 + 2 }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    let flow = PlaceFlow::analyze(&core);
    let mir = MirLowering::lower(definition.key, &core, &flow)
        .function
        .unwrap();
    let candidate = emit_vm(&mir).unwrap();
    let verified = verify_vm(candidate).unwrap();
    assert_eq!(verified.run_i64().unwrap(), 42);

    let program = MirProgram {
        entry: definition.key,
        functions: BTreeMap::from([(definition.key, mir)]),
        instances: BTreeMap::new(),
    };
    let candidate = emit_vm_program(&program).unwrap();
    let encoded = encode_program(&candidate);
    assert_eq!(decode_program(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_program(&encoded)
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn vm_artifact_preserves_generic_effect_instance_identity() {
    let package = PackageKey("vm-effect-instance@0.1.0".into());
    let source =
        "effect State<T> { get() -> T; } pub fn main() -> i64 / State<i64> { State<i64>::get() }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    let mir = MirLowering::lower(definition.key, &core, &flow)
        .function
        .expect("effectful body lowers to MIR");
    let candidate = emit_vm(&mir).expect("MIR performs have VM representations");
    let expected_effect = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("State"))
        .unwrap()
        .key;
    assert!(candidate.function.instructions.iter().any(|instruction| {
        matches!(
            instruction,
            VmInstruction::Perform {
                effect,
                effect_arguments,
                operation: 0,
                arguments,
                ..
            } if *effect == expected_effect
                && effect_arguments == &[VmGenericArgument::Type(VmType::I64)]
                && arguments.is_empty()
        )
    }));
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
}

#[test]
fn verified_vm_round_trips_and_executes_typed_tuple_values() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"tuple-value")),
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                VmType::I64,
                VmType::Tuple(vec![VmType::I64, VmType::I64]),
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 40 },
                VmInstruction::ConstI64 { dst: 1, value: 2 },
                VmInstruction::MakeTuple {
                    dst: 2,
                    fields: vec![0, 1],
                },
                VmInstruction::Return { value: 2 },
            ],
        },
        fingerprint: Digest::of_bytes(b"tuple-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_tuple_i64()
            .unwrap(),
        vec![40, 2]
    );
}

#[test]
fn structural_pattern_tests_round_trip_through_the_independent_vm_decoder() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"pattern-test")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64, VmType::Bool],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::PatternTest {
                    dst: 1,
                    subject: 0,
                    pattern: VmPattern::Literal("42".into()),
                },
                VmInstruction::Return { value: 1 },
            ],
        },
        fingerprint: Digest::of_bytes(b"pattern-test-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert!(
        decode_and_verify_artifact(&bytes)
            .unwrap()
            .run_bool()
            .unwrap()
    );
}

#[test]
fn vm_scalar_pattern_literals_share_the_lexer_escape_contract() {
    let mut valid = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"vm-escaped-text-pattern")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::Text, VmType::Bool],
            instructions: vec![
                VmInstruction::ConstText {
                    dst: 0,
                    value: "A🦀\0".into(),
                },
                VmInstruction::PatternTest {
                    dst: 1,
                    subject: 0,
                    pattern: VmPattern::Literal(r#""\x41\u{1f980}\0""#.into()),
                },
                VmInstruction::Return { value: 1 },
            ],
        },
        fingerprint: Digest::of_bytes(b"vm-escaped-text-pattern-stale"),
    };
    valid.fingerprint = valid.computed_fingerprint();
    assert!(verify_vm(valid).unwrap().run_bool().unwrap());

    let mut malformed = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"vm-malformed-text-pattern")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::Text, VmType::Bool],
            instructions: vec![
                VmInstruction::ConstText {
                    dst: 0,
                    value: "A".into(),
                },
                VmInstruction::PatternTest {
                    dst: 1,
                    subject: 0,
                    pattern: VmPattern::Literal(r#""\u{41"#.into()),
                },
                VmInstruction::Return { value: 1 },
            ],
        },
        fingerprint: Digest::of_bytes(b"vm-malformed-text-pattern-stale"),
    };
    malformed.fingerprint = malformed.computed_fingerprint();
    assert!(matches!(
        verify_vm(malformed),
        Err(VmArtifactError::MalformedEncoding {
            message: "invalid scalar literal pattern"
        })
    ));
}

#[test]
fn vm_verifier_rejects_nominal_pattern_fields_outside_frozen_arity() {
    let definition = DefKey(Digest::of_bytes(b"vm-pattern-arity"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![VmNominalCopyDescriptor {
                definition,
                arguments: vec![],
                variants: vec![vec![VmType::I64]],
            }],
            definition: DefKey(Digest::of_bytes(b"vm-pattern-arity-function")),
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                VmType::Nominal {
                    definition,
                    arguments: vec![],
                },
                VmType::Bool,
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::MakeRecord {
                    dst: 1,
                    definition,
                    fields: vec![0],
                    field_types: vec![VmType::I64],
                },
                VmInstruction::PatternTest {
                    dst: 2,
                    subject: 1,
                    pattern: VmPattern::Record {
                        definition,
                        field_types: vec![VmType::I64],
                        field_count: 1,
                        fields: vec![VmPatternField {
                            index: 1,
                            ty: VmType::I64,
                            pattern: VmPattern::Any,
                        }],
                    },
                },
                VmInstruction::Return { value: 2 },
            ],
        },
        fingerprint: Digest::of_bytes(b"vm-pattern-arity-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();

    assert!(
        verify_vm(candidate).is_err_and(|error| matches!(
            error,
            VmArtifactError::MalformedEncoding {
                message: "pattern field is outside its structural arity"
            }
        )),
        "serialized bytecode must fail closed before an invalid pattern can execute"
    );
}

#[test]
fn vm_decoder_verifier_rejects_nominal_pattern_field_type_forgery() {
    let definition = DefKey(Digest::of_bytes(b"vm-pattern-layout"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![VmNominalCopyDescriptor {
                definition,
                arguments: vec![],
                variants: vec![vec![VmType::I64]],
            }],
            definition: DefKey(Digest::of_bytes(b"vm-pattern-layout-function")),
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                VmType::Nominal {
                    definition,
                    arguments: vec![],
                },
                VmType::Bool,
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::MakeRecord {
                    dst: 1,
                    definition,
                    fields: vec![0],
                    field_types: vec![VmType::I64],
                },
                VmInstruction::PatternTest {
                    dst: 2,
                    subject: 1,
                    pattern: VmPattern::Record {
                        definition,
                        field_types: vec![VmType::Bool],
                        field_count: 1,
                        fields: vec![VmPatternField {
                            index: 0,
                            ty: VmType::I64,
                            pattern: VmPattern::Any,
                        }],
                    },
                },
                VmInstruction::Return { value: 2 },
            ],
        },
        fingerprint: Digest::of_bytes(b"vm-pattern-layout-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);

    assert!(
        decode_and_verify_artifact(&bytes).is_err_and(|error| matches!(
            error,
            VmArtifactError::MalformedEncoding {
                message: "pattern field type disagrees with its frozen layout"
            }
        )),
        "a decoded artifact cannot forge an in-range nominal pattern field type"
    );
}

#[test]
fn vm_decoder_verifier_rejects_forged_array_pattern_element_metadata() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"vm-array-pattern-forgery")),
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                VmType::Array(Box::new(VmType::I64)),
                VmType::Bool,
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::MakeArray {
                    dst: 1,
                    fields: vec![0],
                    element_type: VmType::I64,
                },
                VmInstruction::PatternTest {
                    dst: 2,
                    subject: 1,
                    pattern: VmPattern::Array {
                        element: VmType::Bool,
                        elements: vec![VmPattern::Any],
                    },
                },
                VmInstruction::Return { value: 2 },
            ],
        },
        fingerprint: Digest::of_bytes(b"vm-array-pattern-forgery-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(
        decode_and_verify_artifact(&encode_artifact(&candidate)).is_err_and(|error| matches!(
            error,
            VmArtifactError::TypeMismatch {
                expected: VmType::Array(_),
                ..
            }
        )),
        "decoded bytecode cannot relabel an array pattern element type"
    );
}

#[test]
fn verified_vm_reports_unhandled_effects_without_synthesizing_a_handler() {
    let effect = DefKey(Digest::of_bytes(b"Console"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"effect-test")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64],
            instructions: vec![
                VmInstruction::Perform {
                    dst: 0,
                    effect,
                    effect_arguments: vec![VmGenericArgument::Type(VmType::I64)],
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"effect-test-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert!(matches!(
        decode_and_verify_artifact(&bytes).unwrap().run_i64(),
        Err(VmArtifactError::UnhandledEffect {
            effect: actual,
            effect_arguments,
            operation: 0,
        }) if actual == effect && effect_arguments == vec![VmGenericArgument::Type(VmType::I64)]
    ));
}

#[test]
fn suspended_handler_frames_cannot_intercept_fresh_clause_effects() {
    let effect = DefKey(Digest::of_bytes(b"suspended-clause-effect"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"suspended-clause-effect-entry")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64; 3],
            instructions: vec![
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 4,
                },
                VmInstruction::ConstI64 { dst: 0, value: 1 },
                VmInstruction::Perform {
                    dst: 1,
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::Return { value: 1 },
                // This instruction is hostile artifact input: the selected
                // handler is suspended while its clause runs, so the fresh
                // operation cannot re-enter that same frame.
                VmInstruction::Perform {
                    dst: 2,
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::Cancel,
                VmInstruction::Return { value: 2 },
            ],
        },
        fingerprint: Digest::of_bytes(b"suspended-clause-effect-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate).unwrap().run_i64(),
        Err(VmArtifactError::UnhandledEffect {
            effect: found,
            effect_arguments,
            operation: 0,
        }) if found == effect && effect_arguments.is_empty()
    ));
}

#[test]
fn verified_vm_executes_a_deep_one_shot_handler_frame() {
    let effect = DefKey(Digest::of_bytes(b"Ask"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"handler-frame")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64; 5],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 41 },
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![1],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 5,
                },
                VmInstruction::Perform {
                    dst: 2,
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![0],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 2 },
                VmInstruction::ConstI64 { dst: 3, value: 1 },
                VmInstruction::AddI64 {
                    dst: 4,
                    left: 1,
                    right: 3,
                },
                VmInstruction::Resume { value: 4 },
            ],
        },
        fingerprint: Digest::of_bytes(b"handler-frame-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    // The eighth step is the continuation's return, after direct `Resume`.
    assert_continuation_budget_parity(candidate.function.clone(), 7);
    assert_eq!(verify_vm(candidate).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn handlers_match_the_exact_non_type_effect_instance() {
    use grandiose_stage0::{EffectTail, Lifetime, VmEffectInstance, VmEffectRow};

    let effect = DefKey(Digest::of_bytes(b"exact-non-type-handler"));
    let nested = DefKey(Digest::of_bytes(b"exact-non-type-handler-nested"));
    let protocol = vec![
        VmGenericArgument::ConstU32(1),
        VmGenericArgument::Lifetime(Lifetime::Generic(4)),
        VmGenericArgument::EffectRow(VmEffectRow {
            effects: vec![VmEffectInstance {
                definition: nested,
                arguments: vec![VmGenericArgument::ConstQuantity {
                    lower: 2,
                    upper: None,
                }],
            }],
            projections: vec![],
            tail: Some(EffectTail::Generic(3)),
        }),
    ];
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"exact-non-type-handler-caller")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64; 3],
            instructions: vec![
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: protocol.clone(),
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 4,
                },
                VmInstruction::Perform {
                    dst: 0,
                    effect,
                    effect_arguments: protocol,
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 0 },
                VmInstruction::ConstI64 { dst: 1, value: 42 },
                VmInstruction::Resume { value: 1 },
            ],
        },
        fingerprint: Digest::of_bytes(b"exact-non-type-handler-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert_eq!(verify_vm(candidate.clone()).unwrap().run_i64().unwrap(), 42);

    let VmInstruction::Perform {
        effect_arguments, ..
    } = &mut candidate.function.instructions[1]
    else {
        panic!("fixture changed")
    };
    effect_arguments[0] = VmGenericArgument::ConstU32(2);
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate).unwrap().run_i64(),
        Err(VmArtifactError::UnhandledEffect { effect: found, effect_arguments, .. })
            if found == effect && effect_arguments[0] == VmGenericArgument::ConstU32(2)
    ));
}

#[test]
fn replay_handler_policy_round_trips_and_runs_in_both_vm_engines() {
    let effect = DefKey(Digest::of_bytes(b"replay-ask"));
    let definition = DefKey(Digest::of_bytes(b"replay-handler-frame"));
    let function = VmFunction {
        definition,
        nominal_copy_descriptors: vec![],
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64; 10],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 41 },
            VmInstruction::InstallHandler {
                effect,
                effect_arguments: vec![],
                operation: 0,
                payload_destinations: vec![1],
                resume_type: VmType::I64,
                continuation: VmContinuationPolicy::Replay { uses: 2 },
                target: 5,
            },
            VmInstruction::Perform {
                dst: 2,
                effect,
                effect_arguments: vec![],
                operation: 0,
                arguments: vec![0],
            },
            VmInstruction::UninstallHandler,
            VmInstruction::Return { value: 2 },
            VmInstruction::ConstI64 { dst: 3, value: 1 },
            VmInstruction::AddI64 {
                dst: 4,
                left: 1,
                right: 3,
            },
            VmInstruction::ResumeReturn { dst: 5, value: 4 },
            VmInstruction::ConstI64 { dst: 6, value: 2 },
            VmInstruction::AddI64 {
                dst: 7,
                left: 1,
                right: 6,
            },
            VmInstruction::ResumeReturn { dst: 8, value: 7 },
            VmInstruction::Cancel,
            VmInstruction::Return { value: 8 },
        ],
    };
    let mut artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: function.clone(),
        fingerprint: Digest::of_bytes(b"replay-handler-artifact"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    let bytes = encode_artifact(&artifact);
    assert_eq!(decode_artifact(&bytes).unwrap(), artifact);
    assert_eq!(verify_vm(artifact).unwrap().run_i64().unwrap(), 43);

    let mut malformed_policy = function.clone();
    let VmInstruction::InstallHandler { continuation, .. } = &mut malformed_policy.instructions[1]
    else {
        panic!("fixture changed")
    };
    *continuation = VmContinuationPolicy::Replay { uses: 1 };
    let mut malformed = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: malformed_policy,
        fingerprint: Digest::of_bytes(b"replay-handler-malformed-policy"),
    };
    malformed.fingerprint = malformed.computed_fingerprint();
    assert!(matches!(
        verify_vm(malformed),
        Err(VmArtifactError::HandlerStateMismatch)
    ));

    // The verifier admits the CFG shape, but executable replay accounting is
    // still the final hostile-bytecode boundary: a third invocation of a
    // frozen `[2,2]` continuation must fail rather than become unbounded.
    let mut over_replay = function.clone();
    over_replay.instructions.insert(
        over_replay.instructions.len() - 2,
        VmInstruction::ResumeReturn { dst: 9, value: 4 },
    );
    let mut hostile = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: over_replay,
        fingerprint: Digest::of_bytes(b"replay-handler-over-use"),
    };
    hostile.fingerprint = hostile.computed_fingerprint();
    assert!(matches!(
        verify_vm(hostile).unwrap().run_i64(),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));

    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: definition,
        functions: BTreeMap::from([(definition, function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"replay-handler-program"),
    };
    program.fingerprint = program.computed_fingerprint();
    assert_eq!(verify_vm_program(program).unwrap().run_i64().unwrap(), 43);
}

#[test]
fn explicit_resumption_snapshot_round_trips_and_resumes_its_branded_frame() {
    let effect = DefKey(Digest::of_bytes(b"snapshot-ask"));
    let residual_effect = DefKey(Digest::of_bytes(b"snapshot-residual-log"));
    let continuation = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::I64),
        // Captured resumptions are first-class callable values. Their
        // residual outward effects must survive artifact encoding and
        // verification; only their frame provenance grants resume authority.
        effects: Box::new(VmEffectRow {
            effects: vec![grandiose_stage0::VmEffectInstance {
                definition: residual_effect,
                arguments: vec![],
            }],
            projections: vec![],
            tail: None,
        }),
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"explicit-snapshot")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64, continuation, VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 4,
                },
                VmInstruction::Perform {
                    dst: 2,
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 2 },
                VmInstruction::CaptureResumption { dst: 1 },
                VmInstruction::ConstI64 { dst: 3, value: 42 },
                VmInstruction::ResumeSnapshot {
                    snapshot: 1,
                    value: 3,
                },
            ],
        },
        fingerprint: Digest::of_bytes(b"explicit-snapshot-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    // The seventh step is the restored continuation's return.
    assert_continuation_budget_parity(candidate.function.clone(), 6);
    // No CaptureResumption/Snapshot path can create a retained frame once the
    // explicit continuation cap is exhausted.
    assert_continuation_retention_parity(candidate.function.clone());
    assert_eq!(verify_vm(candidate).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn dynamic_label_call_abandons_replay_return_frames() {
    let owner = DefKey(Digest::of_bytes(b"dynamic-label-replay-owner"));
    let effect = DefKey(Digest::of_bytes(b"dynamic-label-replay-effect"));
    let label = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::Unit),
        effects: Box::<VmEffectRow>::default(),
    };
    // The label is captured before the handler.  `ResumeReturn` restores the
    // performed computation, whose first action invokes that label.  This is
    // an abandonment boundary: execution must reach its payload return, not
    // resurrect the handler clause at the pending return address (the trap).
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: owner,
        captures: 0,
        parameters: 0,
        registers: vec![label, VmType::I64, VmType::I64, VmType::I64, VmType::Unit, VmType::I64],
        instructions: vec![
            VmInstruction::MakeLabel {
                dst: 0,
                brand_owner: owner,
                brand_label: 0,
                target: 9,
                destination: 5,
            },
            VmInstruction::InstallHandler {
                effect,
                effect_arguments: vec![],
                operation: 0,
                payload_destinations: vec![],
                resume_type: VmType::I64,
                continuation: VmContinuationPolicy::Replay { uses: 2 },
                target: 6,
            },
            VmInstruction::Perform {
                dst: 1,
                effect,
                effect_arguments: vec![],
                operation: 0,
                arguments: vec![],
            },
            VmInstruction::CallIndirect {
                dst: 4,
                callee: 0,
                arguments: vec![1],
            },
            VmInstruction::UninstallHandler,
            VmInstruction::Return { value: 1 },
            VmInstruction::ConstI64 { dst: 2, value: 41 },
            VmInstruction::ResumeReturn { dst: 3, value: 2 },
            // Reaching this instruction proves the dynamic label left the
            // stale resumption-return frame alive.
            VmInstruction::Trap,
            VmInstruction::Return { value: 5 },
        ],
    };
    let mut artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: function.clone(),
        fingerprint: Digest::of_bytes(b"dynamic-label-replay-artifact"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    let encoded = encode_artifact(&artifact);
    assert_eq!(decode_artifact(&encoded).unwrap(), artifact);
    assert_eq!(verify_vm(artifact).unwrap().run_i64().unwrap(), 41);

    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: owner,
        functions: BTreeMap::from([(owner, function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"dynamic-label-replay-program"),
    };
    program.fingerprint = program.computed_fingerprint();
    assert_eq!(verify_vm_program(program).unwrap().run_i64().unwrap(), 41);
}

#[test]
fn verifier_rejects_dynamic_label_rejoin_that_leaks_a_retained_facade() {
    let owner = DefKey(Digest::of_bytes(b"dynamic-label-facade-owner"));
    let facade = DefKey(Digest::of_bytes(b"dynamic-label-facade-effect"));
    let label = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::Unit),
        effects: Box::<VmEffectRow>::default(),
    };
    // The label is minted inside the facade, so the rejoin deliberately
    // retains that frame. Returning directly from the target is malformed:
    // valid lowering must run the facade's UninstallHandler after completion.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: owner,
            captures: 0,
            parameters: 0,
            registers: vec![label, VmType::I64, VmType::Unit],
            instructions: vec![
                VmInstruction::InstallHandler {
                    effect: facade,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 5,
                },
                VmInstruction::MakeLabel {
                    dst: 0,
                    brand_owner: owner,
                    brand_label: 0,
                    target: 4,
                    destination: 1,
                },
                VmInstruction::ConstI64 { dst: 1, value: 42 },
                VmInstruction::CallIndirect {
                    dst: 2,
                    callee: 0,
                    arguments: vec![1],
                },
                VmInstruction::Return { value: 1 },
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"dynamic-label-facade-leak-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert!(matches!(
        verify_vm(candidate.clone()),
        Err(VmArtifactError::HandlerStillActive)
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::HandlerStillActive)
    ));
}

#[test]
fn verifier_rejects_unique_callable_capture_at_a_dynamic_label_rejoin() {
    let owner = DefKey(Digest::of_bytes(b"dynamic-label-unique-capture-owner"));
    let facade = DefKey(Digest::of_bytes(b"dynamic-label-unique-capture-facade"));
    let label = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::Unit),
        effects: Box::<VmEffectRow>::default(),
    };
    let closure = VmType::Callable {
        parameters: vec![],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    // The normal CFG route removes the facade before jumping to the rejoin.
    // A real label invocation instead reaches that rejoin with the facade
    // retained. In either case, freezing the unique reference into the
    // returned closure must fail before it can become observable.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: owner,
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                VmType::Reference {
                    unique: true,
                    referent: Box::new(VmType::I64),
                },
                VmType::Tuple(vec![VmType::Reference {
                    unique: true,
                    referent: Box::new(VmType::I64),
                }]),
                label.clone(),
                closure,
                VmType::Unit,
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::Borrow {
                    dst: 1,
                    src: 0,
                    fields: vec![],
                    unique: true,
                    reborrow: false,
                },
                VmInstruction::MakeTuple {
                    dst: 2,
                    fields: vec![1],
                },
                VmInstruction::InstallHandler {
                    effect: facade,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 10,
                },
                VmInstruction::MakeLabel {
                    dst: 3,
                    brand_owner: owner,
                    brand_label: 0,
                    target: 8,
                    destination: 0,
                },
                VmInstruction::CallIndirect {
                    dst: 5,
                    callee: 3,
                    arguments: vec![0],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Jump { target: 8 },
                VmInstruction::MakeCallable {
                    dst: 4,
                    callee: DefKey(Digest::of_bytes(b"forged-unique-closure")),
                    captures: vec![2],
                    environment: None,
                },
                VmInstruction::Return { value: 4 },
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"dynamic-label-unique-capture-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::UnsupportedEscapingUniqueReference)
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::UnsupportedEscapingUniqueReference)
    ));
}

#[test]
fn verifier_rejects_nested_label_callable_capture_before_dynamic_rejoin_can_escape() {
    let owner = DefKey(Digest::of_bytes(b"dynamic-label-capture-owner"));
    let facade = DefKey(Digest::of_bytes(b"dynamic-label-capture-facade"));
    let label = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::Unit),
        effects: Box::<VmEffectRow>::default(),
    };
    let closure = VmType::Callable {
        parameters: vec![],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: owner,
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                label.clone(),
                VmType::Tuple(vec![label.clone(), VmType::I64]),
                VmType::Array(Box::new(VmType::Tuple(vec![
                    VmType::Callable {
                        parameters: vec![VmType::I64],
                        result: Box::new(VmType::Unit),
                        effects: Box::<VmEffectRow>::default(),
                    },
                    VmType::I64,
                ]))),
                closure,
                VmType::Unit,
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                // The label is minted before the facade, so invoking it
                // would abandon that frame and return the forged closure.
                VmInstruction::MakeLabel {
                    dst: 1,
                    brand_owner: owner,
                    brand_label: 0,
                    target: 9,
                    destination: 0,
                },
                VmInstruction::MakeTuple {
                    dst: 2,
                    fields: vec![1, 0],
                },
                VmInstruction::MakeArray {
                    dst: 3,
                    fields: vec![2],
                    element_type: VmType::Tuple(vec![label.clone(), VmType::I64]),
                },
                VmInstruction::InstallHandler {
                    effect: facade,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 11,
                },
                VmInstruction::MakeCallable {
                    dst: 4,
                    callee: DefKey(Digest::of_bytes(b"forged-label-closure")),
                    captures: vec![3],
                    environment: None,
                },
                VmInstruction::CallIndirect {
                    dst: 5,
                    callee: 1,
                    arguments: vec![0],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Jump { target: 9 },
                VmInstruction::Return { value: 4 },
                VmInstruction::Trap,
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"dynamic-label-capture-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::InvalidLabelContract { .. })
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::InvalidLabelContract { .. })
    ));
}

#[test]
fn verifier_rejects_label_projected_through_record_array_and_tuple_before_callable_capture() {
    let owner = DefKey(Digest::of_bytes(b"projected-label-capture-owner"));
    let record = DefKey(Digest::of_bytes(b"projected-label-capture-record"));
    let label = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::Unit),
        effects: Box::<VmEffectRow>::default(),
    };
    let tuple = VmType::Tuple(vec![label.clone()]);
    let array = VmType::Array(Box::new(tuple.clone()));
    let closure = VmType::Callable {
        parameters: vec![],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![VmNominalCopyDescriptor {
                definition: record,
                arguments: vec![],
                variants: vec![vec![array.clone()]],
            }],
            definition: owner,
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                label.clone(),
                tuple.clone(),
                array.clone(),
                VmType::Nominal {
                    definition: record,
                    arguments: vec![],
                },
                array.clone(),
                tuple.clone(),
                label.clone(),
                closure,
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::MakeLabel {
                    dst: 1,
                    brand_owner: owner,
                    brand_label: 0,
                    target: 10,
                    destination: 0,
                },
                VmInstruction::MakeTuple {
                    dst: 2,
                    fields: vec![1],
                },
                VmInstruction::MakeArray {
                    dst: 3,
                    fields: vec![2],
                    element_type: tuple.clone(),
                },
                VmInstruction::MakeRecord {
                    dst: 4,
                    definition: record,
                    fields: vec![3],
                    field_types: vec![array],
                },
                VmInstruction::ProjectRecord {
                    dst: 5,
                    base: 4,
                    index: 0,
                    field_count: 1,
                    field_type: VmType::Array(Box::new(tuple.clone())),
                },
                VmInstruction::ProjectArray {
                    dst: 6,
                    base: 5,
                    index: 0,
                    field_count: 1,
                    element_type: tuple.clone(),
                },
                VmInstruction::ProjectTuple {
                    dst: 7,
                    base: 6,
                    index: 0,
                    field_count: 1,
                    field_type: label.clone(),
                },
                VmInstruction::MakeCallable {
                    dst: 8,
                    callee: DefKey(Digest::of_bytes(b"projected-label-capture-closure")),
                    captures: vec![7],
                    environment: None,
                },
                VmInstruction::Return { value: 8 },
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"projected-label-capture-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::InvalidLabelContract { .. })
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::InvalidLabelContract { .. })
    ));
}

#[test]
fn verifier_rejects_nested_resumption_callable_capture_before_dynamic_rejoin_can_escape() {
    let owner = DefKey(Digest::of_bytes(b"dynamic-resumption-capture-owner"));
    let facade = DefKey(Digest::of_bytes(b"dynamic-resumption-capture-facade"));
    let effect = DefKey(Digest::of_bytes(b"dynamic-resumption-capture-effect"));
    let label = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::Unit),
        effects: Box::<VmEffectRow>::default(),
    };
    let snapshot = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    let closure = VmType::Callable {
        parameters: vec![],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: owner,
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                label,
                VmType::I64,
                snapshot.clone(),
                VmType::Tuple(vec![snapshot.clone()]),
                VmType::Array(Box::new(VmType::Tuple(vec![snapshot.clone()]))),
                VmType::Tuple(vec![snapshot.clone()]),
                snapshot.clone(),
                closure,
                VmType::Unit,
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::MakeLabel {
                    dst: 1,
                    brand_owner: owner,
                    brand_label: 0,
                    target: 15,
                    destination: 0,
                },
                VmInstruction::InstallHandler {
                    effect: facade,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 17,
                },
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 8,
                },
                VmInstruction::Perform {
                    dst: 2,
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::UninstallHandler,
                VmInstruction::Jump { target: 15 },
                VmInstruction::CaptureResumption { dst: 3 },
                VmInstruction::MakeTuple {
                    dst: 4,
                    fields: vec![3],
                },
                VmInstruction::MakeArray {
                    dst: 5,
                    fields: vec![4],
                    element_type: VmType::Tuple(vec![snapshot.clone()]),
                },
                VmInstruction::ProjectArray {
                    dst: 6,
                    base: 5,
                    index: 0,
                    field_count: 1,
                    element_type: VmType::Tuple(vec![snapshot.clone()]),
                },
                VmInstruction::ProjectTuple {
                    dst: 7,
                    base: 6,
                    index: 0,
                    field_count: 1,
                    field_type: snapshot,
                },
                VmInstruction::MakeCallable {
                    dst: 8,
                    callee: DefKey(Digest::of_bytes(b"forged-resumption-closure")),
                    captures: vec![7],
                    environment: None,
                },
                VmInstruction::CallIndirect {
                    dst: 9,
                    callee: 1,
                    arguments: vec![0],
                },
                VmInstruction::Return { value: 8 },
                VmInstruction::Trap,
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"dynamic-resumption-capture-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
}

#[test]
fn nested_shared_capture_executes_after_dynamic_label_rejoin() {
    let owner = DefKey(Digest::of_bytes(b"nested-shared-capture-owner"));
    let entry = DefKey(Digest::of_bytes(b"nested-shared-capture-entry"));
    let closure = DefKey(Digest::of_parts([
        b"grandiose-stage0-lifted-callable".as_slice(),
        owner.0.as_bytes().as_slice(),
        0_u32.to_le_bytes().as_slice(),
    ]));
    let facade = DefKey(Digest::of_bytes(b"nested-shared-capture-facade"));
    let shared = VmType::Reference {
        unique: false,
        referent: Box::new(VmType::I64),
    };
    let tuple = VmType::Tuple(vec![shared.clone(), VmType::I64]);
    let array = VmType::Array(Box::new(tuple.clone()));
    let label = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::Unit),
        effects: Box::<VmEffectRow>::default(),
    };
    let callable = VmType::Callable {
        parameters: vec![],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    let environment = VmCaptureEnvironment {
        owner,
        callable: 0,
        instance: None,
        captures: vec![VmCapture {
            mode: VmCaptureMode::Move,
            ty: array.clone(),
        }],
    };
    let closure_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: closure,
        captures: 1,
        parameters: 1,
        registers: vec![
            array.clone(),
            VmType::Reference {
                unique: false,
                referent: Box::new(array.clone()),
            },
            VmType::Usize,
            tuple.clone(),
            VmType::Reference {
                unique: false,
                referent: Box::new(shared.clone()),
            },
            shared.clone(),
            VmType::I64,
        ],
        instructions: vec![
            VmInstruction::Borrow {
                dst: 1,
                src: 0,
                fields: vec![],
                unique: false,
                reborrow: false,
            },
            VmInstruction::ConstUsize { dst: 2, value: 0 },
            VmInstruction::ArrayGetCopy {
                dst: 3,
                value: 1,
                index: 2,
                element_type: tuple.clone(),
            },
            VmInstruction::Borrow {
                dst: 4,
                src: 3,
                fields: vec![0],
                unique: false,
                reborrow: false,
            },
            VmInstruction::DerefCopy {
                dst: 5,
                reference: 4,
            },
            VmInstruction::DerefCopy {
                dst: 6,
                reference: 5,
            },
            VmInstruction::Return { value: 6 },
        ],
    };
    let entry_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![
            VmType::I64,
            shared,
            VmType::I64,
            tuple.clone(),
            array.clone(),
            label,
            callable,
            VmType::Unit,
            VmType::I64,
        ],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 40 },
            VmInstruction::Borrow {
                dst: 1,
                src: 0,
                fields: vec![],
                unique: false,
                reborrow: false,
            },
            VmInstruction::ConstI64 { dst: 2, value: 2 },
            VmInstruction::MakeTuple {
                dst: 3,
                fields: vec![1, 2],
            },
            VmInstruction::MakeArray {
                dst: 4,
                fields: vec![3],
                element_type: tuple.clone(),
            },
            VmInstruction::MakeLabel {
                dst: 5,
                brand_owner: entry,
                brand_label: 0,
                target: 9,
                destination: 0,
            },
            VmInstruction::InstallHandler {
                effect: facade,
                effect_arguments: vec![],
                operation: 0,
                payload_destinations: vec![],
                resume_type: VmType::I64,
                continuation: VmContinuationPolicy::Consume,
                target: 12,
            },
            VmInstruction::CallIndirect {
                dst: 7,
                callee: 5,
                arguments: vec![0],
            },
            VmInstruction::UninstallHandler,
            VmInstruction::MakeCallable {
                dst: 6,
                callee: closure,
                captures: vec![4],
                environment: Some(environment.clone()),
            },
            VmInstruction::CallIndirect {
                dst: 8,
                callee: 6,
                arguments: vec![],
            },
            VmInstruction::Return { value: 8 },
            VmInstruction::Trap,
        ],
    };
    let mut candidate = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(entry, entry_function), (closure, closure_function)]),
        callable_environments: BTreeMap::from([(closure, environment)]),
        fingerprint: Digest::of_bytes(b"nested-shared-capture-program"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_program(&candidate);
    assert_eq!(decode_program(&bytes).unwrap(), candidate);
    assert_eq!(verify_vm_program(candidate.clone()).unwrap().run_i64().unwrap(), 40);
    assert_eq!(decode_and_verify_program(&bytes).unwrap().run_i64().unwrap(), 40);
}

#[test]
fn verifier_rejects_unique_reference_nested_behind_shared_array_capture_at_dynamic_rejoin() {
    let owner = DefKey(Digest::of_bytes(b"nested-shared-unique-owner"));
    let facade = DefKey(Digest::of_bytes(b"nested-shared-unique-facade"));
    let unique = VmType::Reference {
        unique: true,
        referent: Box::new(VmType::I64),
    };
    let tuple = VmType::Tuple(vec![unique.clone()]);
    let shared_tuple = VmType::Reference {
        unique: false,
        referent: Box::new(tuple.clone()),
    };
    let label = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::Unit),
        effects: Box::<VmEffectRow>::default(),
    };
    let closure = VmType::Callable {
        parameters: vec![],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: owner,
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                unique,
                tuple.clone(),
                shared_tuple.clone(),
                VmType::Array(Box::new(shared_tuple.clone())),
                label,
                closure,
                VmType::Unit,
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::Borrow {
                    dst: 1,
                    src: 0,
                    fields: vec![],
                    unique: true,
                    reborrow: false,
                },
                VmInstruction::MakeTuple {
                    dst: 2,
                    fields: vec![1],
                },
                VmInstruction::Borrow {
                    dst: 3,
                    src: 2,
                    fields: vec![],
                    unique: false,
                    reborrow: false,
                },
                VmInstruction::MakeArray {
                    dst: 4,
                    fields: vec![3],
                    element_type: shared_tuple.clone(),
                },
                VmInstruction::MakeLabel {
                    dst: 5,
                    brand_owner: owner,
                    brand_label: 0,
                    target: 9,
                    destination: 0,
                },
                VmInstruction::InstallHandler {
                    effect: facade,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 12,
                },
                VmInstruction::CallIndirect {
                    dst: 7,
                    callee: 5,
                    arguments: vec![0],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::MakeCallable {
                    dst: 6,
                    callee: DefKey(Digest::of_bytes(b"nested-shared-unique-closure")),
                    captures: vec![4],
                    environment: None,
                },
                VmInstruction::Return { value: 6 },
                VmInstruction::Trap,
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"nested-shared-unique-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::UnsupportedEscapingUniqueReference)
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::UnsupportedEscapingUniqueReference)
    ));
}

#[test]
fn verifier_rejects_snapshot_capture_without_a_suspended_handler_frame() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"orphan-snapshot")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::Callable {
                parameters: vec![VmType::I64],
                result: Box::new(VmType::I64),
                effects: Box::<VmEffectRow>::default(),
            }],
            instructions: vec![VmInstruction::CaptureResumption { dst: 0 }],
        },
        fingerprint: Digest::of_bytes(b"orphan-snapshot-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let error = verify_vm(candidate).unwrap_err();
    assert!(
        matches!(error, VmArtifactError::HandlerResumeUnavailable),
        "{error:?}"
    );
}

#[test]
fn verifier_rejects_snapshot_capture_from_a_terminal_handler_frame() {
    let effect = DefKey(Digest::of_bytes(b"terminal-capture"));
    let continuation = VmType::Callable {
        parameters: vec![VmType::Unit],
        result: Box::new(VmType::Unit),
        effects: Box::<VmEffectRow>::default(),
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"terminal-capture-candidate")),
            captures: 0,
            parameters: 0,
            registers: vec![continuation, VmType::I64],
            instructions: vec![
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::Unit,
                    continuation: VmContinuationPolicy::Terminal,
                    target: 2,
                },
                VmInstruction::Trap,
                VmInstruction::CaptureResumption { dst: 0 },
                VmInstruction::Cancel,
                VmInstruction::ConstI64 { dst: 1, value: 42 },
                VmInstruction::Return { value: 1 },
            ],
        },
        fingerprint: Digest::of_bytes(b"terminal-capture-fingerprint"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let error = verify_vm(candidate).unwrap_err();
    assert!(
        matches!(error, VmArtifactError::HandlerResumeUnavailable),
        "terminal frames must never mint a resumable snapshot: {error:?}"
    );
}

#[test]
fn verifier_rejects_resumption_tokens_crossing_direct_call_frames() {
    let entry = DefKey(Digest::of_bytes(b"snapshot-direct-call-entry"));
    let sink = DefKey(Digest::of_bytes(b"snapshot-direct-call-sink"));
    let effect = DefKey(Digest::of_bytes(b"snapshot-direct-call-effect"));
    let snapshot = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    // `CaptureResumption` creates frame-scoped control authority.  Its
    // callable-shaped type must not let an artifact smuggle that authority
    // through an ordinary call frame; the executor already rejects it while
    // rebasing call arguments, so verification must fail before execution.
    let entry_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, snapshot.clone(), VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::InstallHandler {
                effect,
                effect_arguments: vec![],
                operation: 0,
                payload_destinations: vec![],
                resume_type: VmType::I64,
                continuation: VmContinuationPolicy::Consume,
                target: 4,
            },
            VmInstruction::Perform {
                dst: 0,
                effect,
                effect_arguments: vec![],
                operation: 0,
                arguments: vec![],
            },
            VmInstruction::UninstallHandler,
            VmInstruction::Return { value: 0 },
            VmInstruction::CaptureResumption { dst: 1 },
            VmInstruction::ConstI64 { dst: 2, value: 42 },
            VmInstruction::Call {
                dst: 3,
                callee: sink,
                arguments: vec![1],
            },
            VmInstruction::Cancel,
            VmInstruction::Return { value: 3 },
        ],
    };
    let sink_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: sink,
        captures: 0,
        parameters: 1,
        registers: vec![snapshot, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(entry, entry_function), (sink, sink_function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"snapshot-direct-call-program-fingerprint"),
    };
    program.fingerprint = program.computed_fingerprint();
    let bytes = encode_program(&program);
    assert!(matches!(
        verify_vm_program(program),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
    assert!(matches!(
        decode_and_verify_program(&bytes),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
}

#[test]
fn verifier_rejects_resumption_tokens_masquerading_as_indirect_callees() {
    let entry = DefKey(Digest::of_bytes(b"snapshot-indirect-callee-entry"));
    let effect = DefKey(Digest::of_bytes(b"snapshot-indirect-callee-effect"));
    let snapshot = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    // A resumption's ABI is deliberately callable-shaped. `CallIndirect`
    // must nevertheless reject it: only `ResumeSnapshot` carries the frame
    // provenance needed to restore the captured continuation safely.
    let entry_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, snapshot, VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::InstallHandler {
                effect,
                effect_arguments: vec![],
                operation: 0,
                payload_destinations: vec![],
                resume_type: VmType::I64,
                continuation: VmContinuationPolicy::Consume,
                target: 4,
            },
            VmInstruction::Perform {
                dst: 0,
                effect,
                effect_arguments: vec![],
                operation: 0,
                arguments: vec![],
            },
            VmInstruction::UninstallHandler,
            VmInstruction::Return { value: 0 },
            VmInstruction::CaptureResumption { dst: 1 },
            VmInstruction::ConstI64 { dst: 2, value: 42 },
            VmInstruction::CallIndirect {
                dst: 3,
                callee: 1,
                arguments: vec![2],
            },
            VmInstruction::Cancel,
            VmInstruction::Return { value: 3 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(entry, entry_function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"snapshot-indirect-callee-program-fingerprint"),
    };
    program.fingerprint = program.computed_fingerprint();
    let bytes = encode_program(&program);
    assert!(matches!(
        verify_vm_program(program),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
    assert!(matches!(
        decode_and_verify_program(&bytes),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
}

#[test]
fn verifier_rejects_resumption_tokens_hidden_through_mutable_storage() {
    let entry = DefKey(Digest::of_bytes(b"snapshot-mutable-storage-entry"));
    let sink = DefKey(Digest::of_bytes(b"snapshot-mutable-storage-sink"));
    let effect = DefKey(Digest::of_bytes(b"snapshot-mutable-storage-effect"));
    let snapshot = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    // `DerefStore` used to erase the verifier-side resumption marker. A
    // hostile artifact could then re-read the same VM resumption through the
    // reference and present it to `CallIndirect` as an ordinary callable.
    let entry_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![
            snapshot.clone(),
            VmType::Reference {
                unique: true,
                referent: Box::new(snapshot.clone()),
            },
            VmType::I64,
            snapshot.clone(),
            snapshot.clone(),
            VmType::I64,
            VmType::I64,
        ],
        instructions: vec![
            VmInstruction::MakeCallable {
                dst: 0,
                callee: sink,
                captures: vec![],
                environment: None,
            },
            VmInstruction::Borrow {
                dst: 1,
                src: 0,
                fields: vec![],
                unique: true,
                reborrow: false,
            },
            VmInstruction::InstallHandler {
                effect,
                effect_arguments: vec![],
                operation: 0,
                payload_destinations: vec![],
                resume_type: VmType::I64,
                continuation: VmContinuationPolicy::Consume,
                target: 7,
            },
            VmInstruction::Perform {
                dst: 2,
                effect,
                effect_arguments: vec![],
                operation: 0,
                arguments: vec![],
            },
            VmInstruction::UninstallHandler,
            VmInstruction::Trap,
            VmInstruction::Trap,
            VmInstruction::CaptureResumption { dst: 3 },
            VmInstruction::DerefStore {
                reference: 1,
                src: 3,
            },
            VmInstruction::DerefCopy {
                dst: 4,
                reference: 1,
            },
            VmInstruction::ConstI64 { dst: 6, value: 42 },
            VmInstruction::CallIndirect {
                dst: 5,
                callee: 4,
                arguments: vec![6],
            },
            VmInstruction::Cancel,
            VmInstruction::Return { value: 5 },
        ],
    };
    let sink_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: sink,
        captures: 0,
        parameters: 1,
        registers: vec![VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 1, value: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(entry, entry_function), (sink, sink_function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"snapshot-mutable-storage-program-fingerprint"),
    };
    program.fingerprint = program.computed_fingerprint();
    let bytes = encode_program(&program);
    assert!(matches!(
        verify_vm_program(program),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
    assert!(matches!(
        decode_and_verify_program(&bytes),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
}

#[test]
fn verifier_rejects_resumption_tokens_returned_after_handler_exit() {
    let effect = DefKey(Digest::of_bytes(b"snapshot-return-after-cancel-effect"));
    let snapshot = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    // Cancellation invalidates the owning handler frame. Returning its
    // callable-shaped snapshot would export stale control authority to an
    // embedding host, where it could only fail after verification.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"snapshot-return-after-cancel")),
            captures: 0,
            parameters: 0,
            registers: vec![snapshot, VmType::I64],
            instructions: vec![
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 4,
                },
                VmInstruction::Perform {
                    dst: 1,
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Trap,
                VmInstruction::CaptureResumption { dst: 0 },
                VmInstruction::Cancel,
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"snapshot-return-after-cancel-fingerprint"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
}

#[test]
fn verifier_rejects_an_ordinary_callable_used_as_a_resumption_snapshot() {
    let effect = DefKey(Digest::of_bytes(b"forged-snapshot-effect"));
    let continuation = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::I64),
        // A residual effect row is legitimate for a captured continuation,
        // but it is not a substitute for the verifier's frame provenance.
        effects: Box::new(VmEffectRow {
            effects: vec![grandiose_stage0::VmEffectInstance {
                definition: effect,
                arguments: vec![],
            }],
            projections: vec![],
            tail: None,
        }),
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"forged-snapshot")),
            captures: 0,
            // Register zero is a well-typed ordinary callable. It must not
            // gain the authority of `CaptureResumption`.
            parameters: 0,
            registers: vec![continuation, VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::MakeCallable {
                    dst: 0,
                    callee: DefKey(Digest::of_bytes(b"ordinary-callable")),
                    captures: vec![],
                    environment: None,
                },
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 5,
                },
                VmInstruction::Perform {
                    dst: 1,
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 1 },
                VmInstruction::ConstI64 { dst: 2, value: 42 },
                VmInstruction::ResumeSnapshot {
                    snapshot: 0,
                    value: 2,
                },
            ],
        },
        fingerprint: Digest::of_bytes(b"forged-snapshot-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let error = verify_vm(candidate).unwrap_err();
    assert!(
        matches!(error, VmArtifactError::HandlerResumeUnavailable),
        "{error:?}"
    );
}

#[test]
fn resumed_handler_frame_reinstalls_for_the_next_matching_operation() {
    let effect = DefKey(Digest::of_bytes(b"Ask-deep"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"deep-handler-frame")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64; 8],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 10 },
                VmInstruction::ConstI64 { dst: 1, value: 20 },
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![2],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 8,
                },
                VmInstruction::Perform {
                    dst: 3,
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![0],
                },
                VmInstruction::Perform {
                    dst: 4,
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![1],
                },
                VmInstruction::AddI64 {
                    dst: 5,
                    left: 3,
                    right: 4,
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 5 },
                VmInstruction::ConstI64 { dst: 6, value: 1 },
                VmInstruction::AddI64 {
                    dst: 7,
                    left: 2,
                    right: 6,
                },
                VmInstruction::Resume { value: 7 },
            ],
        },
        fingerprint: Digest::of_bytes(b"deep-handler-frame-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert_eq!(verify_vm(candidate).unwrap().run_i64().unwrap(), 32);
}

#[test]
fn nested_partial_handler_forwards_to_an_outer_frame_and_restores_it_on_resume() {
    let effect = DefKey(Digest::of_bytes(b"Console-forward"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"nested-forwarding")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64; 5],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 40 },
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 1,
                    payload_destinations: vec![1],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 9,
                },
                // This inner frame handles operation zero only. Operation one
                // must cross it, invoke the outer frame, then be restored
                // before the continuation uninstalls it.
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 12,
                },
                VmInstruction::Perform {
                    dst: 2,
                    effect,
                    effect_arguments: vec![],
                    operation: 1,
                    arguments: vec![0],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 2 },
                VmInstruction::Trap,
                VmInstruction::Trap,
                VmInstruction::ConstI64 { dst: 3, value: 2 },
                VmInstruction::AddI64 {
                    dst: 4,
                    left: 1,
                    right: 3,
                },
                VmInstruction::Resume { value: 4 },
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"nested-forwarding-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert_eq!(verify_vm(candidate).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn verifier_rejects_a_forged_nested_arm_that_skips_the_inner_continuation() {
    let outer = DefKey(Digest::of_bytes(b"nested-arm-outer"));
    let inner = DefKey(Digest::of_bytes(b"nested-arm-inner"));
    // A nested arm must resume the topmost (inner) suspended frame first.
    // Forged bytecode cannot use `Resume` to skip it and reach the older
    // outer frame: the verifier observes that the active inner frame has no
    // captured continuation and rejects the edge.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"forged-nested-arm-resume")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64; 2],
            instructions: vec![
                VmInstruction::InstallHandler {
                    effect: outer,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 5,
                },
                VmInstruction::Perform {
                    dst: 0,
                    effect: outer,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 0 },
                VmInstruction::Trap,
                VmInstruction::InstallHandler {
                    effect: inner,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 8,
                },
                VmInstruction::ConstI64 { dst: 1, value: 41 },
                VmInstruction::Resume { value: 1 },
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"forged-nested-arm-resume-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert!(matches!(
        verify_vm(candidate.clone()),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
}

#[test]
fn verifier_rejects_a_forged_three_frame_resume_that_skips_the_live_suffix() {
    let outer = DefKey(Digest::of_bytes(b"forged-three-frame-outer"));
    let middle = DefKey(Digest::of_bytes(b"forged-three-frame-middle"));
    let inner = DefKey(Digest::of_bytes(b"forged-three-frame-inner"));
    // A residual continuation can legitimately restore an arbitrary suffix
    // of inner frames, but forged code cannot manufacture that suffix and
    // resume an older frame through it. The topmost live frame must itself
    // own a suspended continuation before any `Resume` edge is admissible.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"forged-three-frame-resume")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64; 2],
            instructions: vec![
                VmInstruction::InstallHandler {
                    effect: outer,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 5,
                },
                VmInstruction::Perform {
                    dst: 0,
                    effect: outer,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 0 },
                VmInstruction::Trap,
                VmInstruction::InstallHandler {
                    effect: middle,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 9,
                },
                VmInstruction::InstallHandler {
                    effect: inner,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 10,
                },
                VmInstruction::ConstI64 { dst: 1, value: 41 },
                VmInstruction::Resume { value: 1 },
                VmInstruction::Trap,
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"forged-three-frame-resume-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
}

#[test]
fn verifier_rejects_a_forged_partial_handler_forward_without_an_outer_frame() {
    let effect = DefKey(Digest::of_bytes(b"forged-partial-forward"));
    // A matrix miss is allowed to `Forward` only when an enclosing handler
    // owns the suspended operation. A hostile clause cannot turn that edge
    // into a resume-capability escape at the root of the handler stack.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"forged-partial-forward-root")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64],
            instructions: vec![
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 3,
                },
                // This is not a clause reached from `Perform`, so the frame
                // has no suspended continuation to decline.
                VmInstruction::Forward,
                VmInstruction::Return { value: 0 },
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"forged-partial-forward-root-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
}

#[test]
fn verifier_rejects_a_replay_snapshot_after_its_frame_is_cancelled() {
    let effect = DefKey(Digest::of_bytes(b"cancelled-replay-snapshot"));
    let snapshot = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    // Replay may clone a live continuation suffix, but `Cancel` revokes every
    // snapshot alias of that frame. A forged post-cancel resume cannot spend
    // an otherwise well-typed replay capability.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"cancelled-replay-snapshot-candidate")),
            captures: 0,
            parameters: 0,
            registers: vec![snapshot, VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 1, value: 41 },
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Replay { uses: 2 },
                    target: 6,
                },
                VmInstruction::Perform {
                    dst: 2,
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 2 },
                VmInstruction::Trap,
                VmInstruction::CaptureResumption { dst: 0 },
                VmInstruction::Cancel,
                VmInstruction::ResumeSnapshot {
                    snapshot: 0,
                    value: 1,
                },
            ],
        },
        fingerprint: Digest::of_bytes(b"cancelled-replay-snapshot-fingerprint"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
}

#[test]
fn declined_handler_pattern_forwards_the_suspended_operation_to_an_outer_frame() {
    let effect = DefKey(Digest::of_bytes(b"Console-decline"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"declined-handler-pattern")),
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                VmType::I64,
                VmType::I64,
                VmType::I64,
                VmType::Bool,
                VmType::I64,
                VmType::I64,
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 40 },
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![1],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 12,
                },
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![2],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 8,
                },
                VmInstruction::Perform {
                    dst: 3,
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![0],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 3 },
                VmInstruction::Trap,
                VmInstruction::PatternTest {
                    dst: 4,
                    subject: 2,
                    pattern: VmPattern::Literal("0".into()),
                },
                VmInstruction::BranchBool {
                    condition: 4,
                    then_target: 10,
                    else_target: 11,
                },
                VmInstruction::Trap,
                VmInstruction::Forward,
                VmInstruction::ConstI64 { dst: 5, value: 2 },
                VmInstruction::AddI64 {
                    dst: 6,
                    left: 1,
                    right: 5,
                },
                VmInstruction::Resume { value: 6 },
            ],
        },
        fingerprint: Digest::of_bytes(b"declined-handler-pattern-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    // Forward crosses an inner frame, then outer Resume restores the original
    // continuation; the thirteenth step is its final return.
    assert_continuation_budget_parity(candidate.function.clone(), 12);
    assert_eq!(verify_vm(candidate).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn cancelled_handler_continuation_abandons_its_snapshot_and_returns_clause_value() {
    let effect = DefKey(Digest::of_bytes(b"Ask-cancel"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"cancelled-handler")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64; 3],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 1 },
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![1],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 6,
                },
                VmInstruction::Perform {
                    dst: 2,
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![0],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 2 },
                VmInstruction::Trap,
                VmInstruction::ConstI64 { dst: 2, value: 42 },
                VmInstruction::Cancel,
                VmInstruction::Return { value: 2 },
            ],
        },
        fingerprint: Digest::of_bytes(b"cancelled-handler-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert_eq!(verify_vm(candidate).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn verifier_rejects_a_snapshot_alias_after_its_handler_is_cancelled() {
    let cancelled = DefKey(Digest::of_bytes(b"cancelled-snapshot-effect"));
    let later = DefKey(Digest::of_bytes(b"later-snapshot-effect"));
    let snapshot = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    // This is deliberately forged bytecode rather than lowered source.  The
    // first handler captures a replay capability, copies it, and cancels its
    // suspended continuation.  It then installs a distinct, live handler and
    // attempts to resume the stale alias there.  A callable type alone must
    // not regain authority after its branded activation has exited.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"cancelled-snapshot-alias")),
            captures: 0,
            parameters: 0,
            registers: vec![snapshot.clone(), snapshot, VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 2, value: 1 },
                VmInstruction::InstallHandler {
                    effect: cancelled,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Replay { uses: 2 },
                    target: 6,
                },
                VmInstruction::Perform {
                    dst: 3,
                    effect: cancelled,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 3 },
                VmInstruction::Trap,
                VmInstruction::CaptureResumption { dst: 0 },
                VmInstruction::Copy { dst: 1, src: 0 },
                VmInstruction::Cancel,
                VmInstruction::InstallHandler {
                    effect: later,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 13,
                },
                VmInstruction::Perform {
                    dst: 3,
                    effect: later,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![],
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 3 },
                VmInstruction::ResumeSnapshot {
                    snapshot: 1,
                    value: 2,
                },
            ],
        },
        fingerprint: Digest::of_bytes(b"cancelled-snapshot-alias-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    let error = verify_vm(candidate.clone()).unwrap_err();
    assert!(
        matches!(error, VmArtifactError::HandlerResumeUnavailable),
        "cancellation must invalidate all snapshot aliases before a later handler activates: {error:?}"
    );
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
}

#[test]
fn verifier_allows_checked_store_reinitialization_but_rejects_type_confusion() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"store-value")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 1 },
                VmInstruction::ConstI64 { dst: 1, value: 42 },
                VmInstruction::Store { dst: 0, src: 1 },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"store-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&bytes)
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );

    candidate.function.registers[1] = VmType::Bool;
    candidate.function.instructions[1] = VmInstruction::ConstBool {
        dst: 1,
        value: true,
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::TypeMismatch { .. })
    ));
}

#[test]
fn verified_vm_round_trips_arrays_and_rejects_type_confused_elements() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"array-value")),
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                VmType::I64,
                VmType::Array(Box::new(VmType::I64)),
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 40 },
                VmInstruction::ConstI64 { dst: 1, value: 2 },
                VmInstruction::MakeArray {
                    dst: 2,
                    fields: vec![0, 1],
                    element_type: VmType::I64,
                },
                VmInstruction::Return { value: 2 },
            ],
        },
        fingerprint: Digest::of_bytes(b"array-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&bytes)
            .unwrap()
            .run_array_i64()
            .unwrap(),
        vec![40, 2]
    );

    candidate.function.instructions[2] = VmInstruction::MakeArray {
        dst: 2,
        fields: vec![0, 1],
        element_type: VmType::Bool,
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::TypeMismatch { register: 2, .. })
    ));
}

#[test]
fn verified_vm_round_trips_and_executes_typed_nominal_records() {
    let definition = DefKey(Digest::of_bytes(b"record-value"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            definition,
            nominal_copy_descriptors: vec![VmNominalCopyDescriptor {
                definition,
                arguments: vec![],
                variants: vec![vec![VmType::I64, VmType::I64]],
            }],
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                VmType::I64,
                VmType::Nominal {
                    definition,
                    arguments: vec![],
                },
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 40 },
                VmInstruction::ConstI64 { dst: 1, value: 2 },
                VmInstruction::MakeRecord {
                    dst: 2,
                    definition,
                    fields: vec![0, 1],
                    field_types: vec![VmType::I64, VmType::I64],
                },
                VmInstruction::Return { value: 2 },
            ],
        },
        fingerprint: Digest::of_bytes(b"record-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_record_i64()
            .unwrap(),
        vec![40, 2]
    );
}

#[test]
fn verifier_round_trips_record_projection_and_rejects_out_of_bounds_indices() {
    let definition = DefKey(Digest::of_bytes(b"record-projection"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            definition,
            nominal_copy_descriptors: vec![VmNominalCopyDescriptor {
                definition,
                arguments: vec![],
                variants: vec![vec![VmType::I64, VmType::I64]],
            }],
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                VmType::I64,
                VmType::Nominal {
                    definition,
                    arguments: vec![],
                },
                VmType::I64,
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 40 },
                VmInstruction::ConstI64 { dst: 1, value: 2 },
                VmInstruction::MakeRecord {
                    dst: 2,
                    definition,
                    fields: vec![0, 1],
                    field_types: vec![VmType::I64, VmType::I64],
                },
                VmInstruction::ProjectRecord {
                    dst: 3,
                    base: 2,
                    index: 1,
                    field_count: 2,
                    field_type: VmType::I64,
                },
                VmInstruction::Return { value: 3 },
            ],
        },
        fingerprint: Digest::of_bytes(b"record-projection-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_i64()
            .unwrap(),
        2
    );

    candidate.function.instructions[3] = VmInstruction::ProjectRecord {
        dst: 3,
        base: 2,
        index: 2,
        field_count: 2,
        field_type: VmType::I64,
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::InvalidRegister { register: 2 })
    ));
}

#[test]
fn verifier_rejects_callable_signature_forged_through_a_nominal_record_projection() {
    let entry = DefKey(Digest::of_bytes(b"forged-callable-record-entry"));
    let closure = DefKey(Digest::of_bytes(b"forged-callable-record-closure"));
    let record = DefKey(Digest::of_bytes(b"forged-callable-record-layout"));
    let actual = VmType::Callable {
        parameters: vec![],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    let forged = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([
            (
                closure,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: closure,
                    captures: 0,
                    parameters: 0,
                    registers: vec![VmType::I64],
                    instructions: vec![
                        VmInstruction::ConstI64 { dst: 0, value: 42 },
                        VmInstruction::Return { value: 0 },
                    ],
                },
            ),
            (
                entry,
                VmFunction {
                    nominal_copy_descriptors: vec![VmNominalCopyDescriptor {
                        definition: record,
                        arguments: vec![],
                        variants: vec![vec![actual.clone()]],
                    }],
                    definition: entry,
                    captures: 0,
                    parameters: 0,
                    registers: vec![
                        actual.clone(),
                        VmType::Nominal {
                            definition: record,
                            arguments: vec![],
                        },
                        forged.clone(),
                        VmType::I64,
                        VmType::I64,
                    ],
                    instructions: vec![
                        VmInstruction::MakeCallable {
                            dst: 0,
                            callee: closure,
                            captures: vec![],
                            environment: None,
                        },
                        VmInstruction::MakeRecord {
                            dst: 1,
                            definition: record,
                            fields: vec![0],
                            field_types: vec![actual],
                        },
                        // This used to relabel the stored `() -> i64` as an
                        // `(i64) -> i64` callable and let the following
                        // indirect invocation cross a false ABI boundary.
                        VmInstruction::ProjectRecord {
                            dst: 2,
                            base: 1,
                            index: 0,
                            field_count: 1,
                            field_type: forged,
                        },
                        VmInstruction::ConstI64 { dst: 3, value: 7 },
                        VmInstruction::CallIndirect {
                            dst: 4,
                            callee: 2,
                            arguments: vec![3],
                        },
                        VmInstruction::Return { value: 4 },
                    ],
                },
            ),
        ]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"forged-callable-record-stale"),
    };
    program.fingerprint = program.computed_fingerprint();
    let bytes = encode_program(&program);
    assert!(matches!(
        verify_vm_program(program),
        Err(VmArtifactError::MalformedEncoding {
            message: "nominal projection layout does not match frozen descriptor"
        })
    ));
    assert!(matches!(
        decode_and_verify_program(&bytes),
        Err(VmArtifactError::MalformedEncoding {
            message: "nominal projection layout does not match frozen descriptor"
        })
    ));
}

#[test]
fn runtime_rechecks_callable_signature_when_an_enum_projection_is_variant_dependent() {
    let entry = DefKey(Digest::of_bytes(b"variant-callable-entry"));
    let closure = DefKey(Digest::of_bytes(b"variant-callable-closure"));
    let choice = DefKey(Digest::of_bytes(b"variant-callable-choice"));
    let actual = VmType::Callable {
        parameters: vec![],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    let other_variant = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([
            (
                closure,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: closure,
                    captures: 0,
                    parameters: 0,
                    registers: vec![VmType::I64],
                    instructions: vec![
                        VmInstruction::ConstI64 { dst: 0, value: 42 },
                        VmInstruction::Return { value: 0 },
                    ],
                },
            ),
            (
                entry,
                VmFunction {
                    nominal_copy_descriptors: vec![VmNominalCopyDescriptor {
                        definition: choice,
                        arguments: vec![],
                        variants: vec![vec![actual.clone()], vec![other_variant.clone()]],
                    }],
                    definition: entry,
                    captures: 0,
                    parameters: 0,
                    registers: vec![
                        actual.clone(),
                        VmType::Nominal {
                            definition: choice,
                            arguments: vec![],
                        },
                        other_variant.clone(),
                        VmType::I64,
                        VmType::I64,
                    ],
                    instructions: vec![
                        VmInstruction::MakeCallable {
                            dst: 0,
                            callee: closure,
                            captures: vec![],
                            environment: None,
                        },
                        VmInstruction::MakeEnum {
                            dst: 1,
                            definition: choice,
                            variant: 0,
                            fields: vec![0],
                            field_types: vec![actual.clone()],
                        },
                        // The static projection shape exists in variant 1,
                        // but the concrete value is variant 0. The runtime
                        // field guard must retain the actual callable ABI.
                        VmInstruction::ProjectRecord {
                            dst: 2,
                            base: 1,
                            index: 0,
                            field_count: 1,
                            field_type: other_variant.clone(),
                        },
                        VmInstruction::ConstI64 { dst: 3, value: 7 },
                        VmInstruction::CallIndirect {
                            dst: 4,
                            callee: 2,
                            arguments: vec![3],
                        },
                        VmInstruction::Return { value: 4 },
                    ],
                },
            ),
        ]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"variant-callable-stale"),
    };
    program.fingerprint = program.computed_fingerprint();
    let bytes = encode_program(&program);
    assert!(matches!(
        verify_vm_program(program).and_then(|program| program.run_i64()),
        Err(VmArtifactError::ResultType {
            expected,
            found,
        }) if expected == other_variant && found == actual
    ));
    assert!(matches!(
        decode_and_verify_program(&bytes).and_then(|program| program.run_i64()),
        Err(VmArtifactError::ResultType {
            expected,
            found,
        }) if expected == other_variant && found == actual
    ));
}

#[test]
fn verifier_rejects_malformed_candidate_artifacts_before_execution() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: Some(Digest::of_bytes(b"trusted-runtime-manifest")),
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"bad")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64],
            instructions: vec![VmInstruction::Return { value: 0 }],
        },
        fingerprint: Digest::of_bytes(b"candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::ReadBeforeWrite { register: 0 })
    ));
}

#[test]
fn standalone_artifact_verifier_rejects_unbound_entry_parameters() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"parameterized-artifact")),
            captures: 0,
            parameters: 1,
            registers: vec![VmType::I64],
            instructions: vec![VmInstruction::Return { value: 0 }],
        },
        fingerprint: Digest::of_bytes(b"parameterized-artifact-fingerprint"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();

    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::CallArity {
            expected: 1,
            found: 0,
        })
    ));
}

#[test]
fn verifier_rejects_type_confused_constants_before_execution() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"bad-type")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::F64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"type-confusion"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::TypeMismatch {
            register: 0,
            expected: VmType::I64,
            found: VmType::F64,
        })
    ));
}

#[test]
fn vm_rejects_payload_distinct_nan_constants_at_candidate_and_decode_boundaries() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"forged-vm-nan-payload")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::F64],
            instructions: vec![
                VmInstruction::ConstF64 {
                    dst: 0,
                    bits: 0x7ff8_0000_0000_0001,
                },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"forged-vm-nan-payload-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate.clone()),
        Err(VmArtifactError::NonCanonicalFloat {
            bits: 0x7ff8_0000_0000_0001
        })
    ));
    assert!(matches!(
        decode_artifact(&encode_artifact(&candidate)),
        Err(VmArtifactError::NonCanonicalFloat {
            bits: 0x7ff8_0000_0000_0001
        })
    ));
}

#[test]
fn verifier_rejects_candidates_with_stale_schema_or_fingerprint() {
    let candidate = CandidateVmArtifact {
        schema: 1,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"schema")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 1 },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"stale"),
    };
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::UnsupportedSchema { found: 1 })
    ));
    let tampered = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"fingerprint")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 1 },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"not-the-canonical-encoding"),
    };
    assert!(matches!(
        verify_vm(tampered),
        Err(VmArtifactError::FingerprintMismatch)
    ));
}

#[test]
fn stage_zero_artifact_envelope_round_trips_and_rejects_hostile_bytes() {
    let package = PackageKey("vm-envelope@0.1.0".into());
    let source = "pub fn main() -> Text { \"hello, \" + \"world\" }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    let flow = PlaceFlow::analyze(&core);
    let mir = MirLowering::lower(definition.key, &core, &flow)
        .function
        .unwrap();
    let candidate = emit_vm(&mir).unwrap();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&bytes)
            .unwrap()
            .run_text()
            .unwrap(),
        "hello, world"
    );

    assert!(matches!(
        decode_artifact(&bytes[..bytes.len() - 1]),
        Err(VmArtifactError::MalformedEncoding { .. })
    ));
    let mut fingerprint_tampered = bytes;
    fingerprint_tampered[12] ^= 0x80;
    assert!(matches!(
        decode_and_verify_artifact(&fingerprint_tampered),
        Err(VmArtifactError::FingerprintMismatch)
    ));
}

#[test]
fn verified_vm_executes_typed_indirect_calls_to_lifted_callables() {
    let closure = DefKey(Digest::of_bytes(b"lifted-closure"));
    let entry = DefKey(Digest::of_bytes(b"callable-entry"));
    let closure_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: closure,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 },
            VmInstruction::Return { value: 0 },
        ],
    };
    let entry_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![
            VmType::Callable {
                parameters: vec![],
                result: Box::new(VmType::I64),
                effects: Box::<VmEffectRow>::default(),
            },
            VmType::I64,
        ],
        instructions: vec![
            VmInstruction::MakeCallable {
                dst: 0,
                callee: closure,
                captures: vec![],
                environment: None,
            },
            VmInstruction::CallIndirect {
                dst: 1,
                callee: 0,
                arguments: vec![],
            },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: Some(Digest::of_bytes(b"trusted-runtime-manifest")),
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(closure, closure_function), (entry, entry_function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"callable-program"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_program(&candidate);
    assert_eq!(decode_program(&encoded).unwrap(), candidate);
    let verified = grandiose_stage0::verify_vm_program(candidate).unwrap();
    assert_eq!(
        verified.runtime_manifest(),
        Some(Digest::of_bytes(b"trusted-runtime-manifest"))
    );
    assert_eq!(verified.run_i64().unwrap(), 42);
}

#[test]
fn verifier_retains_resumption_provenance_across_handler_clause_joins() {
    let effect = DefKey(Digest::of_bytes(b"joined-resumption-effect"));
    let owner = DefKey(Digest::of_bytes(b"joined-resumption-owner"));
    let snapshot = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    let closure = VmType::Callable {
        parameters: vec![],
        result: Box::new(VmType::I64),
        effects: Box::<VmEffectRow>::default(),
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: owner,
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::Bool,
                VmType::I64,
                VmType::I64,
                snapshot,
                closure,
                VmType::I64,
            ],
            instructions: vec![
                VmInstruction::ConstBool { dst: 0, value: true },
                VmInstruction::ConstI64 { dst: 1, value: 7 },
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![5],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 5,
                },
                VmInstruction::Perform {
                    dst: 2,
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    arguments: vec![1],
                },
                VmInstruction::Trap,
                // Process the ordinary callable branch first. The other
                // branch carries a frame-branded snapshot into the same
                // register and joins at instruction 10.
                VmInstruction::BranchBool {
                    condition: 0,
                    then_target: 8,
                    else_target: 6,
                },
                VmInstruction::MakeCallable {
                    dst: 3,
                    callee: DefKey(Digest::of_bytes(b"joined-ordinary-callable")),
                    captures: vec![],
                    environment: None,
                },
                VmInstruction::Jump { target: 10 },
                VmInstruction::CaptureResumption { dst: 3 },
                VmInstruction::Jump { target: 10 },
                VmInstruction::MakeCallable {
                    dst: 4,
                    callee: DefKey(Digest::of_bytes(b"joined-capture-sink")),
                    captures: vec![3],
                    environment: None,
                },
                VmInstruction::Cancel,
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"joined-resumption-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    let direct = verify_vm(candidate);
    assert!(
        matches!(direct, Err(VmArtifactError::HandlerResumeUnavailable)),
        "unexpected direct verification result: {direct:?}"
    );
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
}

#[test]
fn verifier_retains_label_provenance_across_callable_joins() {
    let owner = DefKey(Digest::of_bytes(b"joined-label-owner"));
    let label = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::Unit),
        effects: Box::<VmEffectRow>::default(),
    };
    let closure = VmType::Callable {
        parameters: vec![],
        result: Box::new(VmType::Unit),
        effects: Box::<VmEffectRow>::default(),
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: owner,
            captures: 0,
            parameters: 0,
            registers: vec![VmType::Bool, label, VmType::I64, closure],
            instructions: vec![
                VmInstruction::ConstBool { dst: 0, value: true },
                // The ordinary callable path is explored first; the label
                // branch then merges into its register slot at instruction 6.
                VmInstruction::BranchBool {
                    condition: 0,
                    then_target: 4,
                    else_target: 2,
                },
                VmInstruction::MakeCallable {
                    dst: 1,
                    callee: DefKey(Digest::of_bytes(b"joined-label-ordinary-callable")),
                    captures: vec![],
                    environment: None,
                },
                VmInstruction::Jump { target: 6 },
                VmInstruction::MakeLabel {
                    dst: 1,
                    brand_owner: owner,
                    brand_label: 0,
                    target: 8,
                    destination: 2,
                },
                VmInstruction::Jump { target: 6 },
                VmInstruction::MakeCallable {
                    dst: 3,
                    callee: DefKey(Digest::of_bytes(b"joined-label-capture-sink")),
                    captures: vec![1],
                    environment: None,
                },
                VmInstruction::Trap,
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"joined-label-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::InvalidLabelContract {
            message: "callable capture cannot retain a lexical label"
        })
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::InvalidLabelContract {
            message: "callable capture cannot retain a lexical label"
        })
    ));
}

#[test]
fn callable_environment_contracts_round_trip_and_reject_forged_layouts() {
    let owner = DefKey(Digest::of_bytes(b"callable-environment-owner"));
    let brand = EnvironmentBrand {
        owner,
        callable: CallableId(7),
    };
    let callable_index = brand.callable.0.to_le_bytes();
    let callable = DefKey(Digest::of_parts([
        b"grandiose-stage0-lifted-callable".as_slice(),
        owner.0.as_bytes().as_slice(),
        callable_index.as_slice(),
    ]));
    let entry = DefKey(Digest::of_bytes(b"callable-environment-entry"));
    let environment = VmCaptureEnvironment {
        owner: brand.owner,
        callable: brand.callable.0,
        instance: None,
        captures: vec![VmCapture {
            mode: VmCaptureMode::Move,
            ty: VmType::I64,
        }],
    };
    let closure = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: callable,
        captures: 1,
        parameters: 1,
        registers: vec![VmType::I64],
        instructions: vec![VmInstruction::Return { value: 0 }],
    };
    let entry_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![
            VmType::I64,
            VmType::Callable {
                parameters: vec![],
                result: Box::new(VmType::I64),
                effects: Box::<VmEffectRow>::default(),
            },
            VmType::I64,
        ],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 },
            VmInstruction::MakeCallable {
                dst: 1,
                callee: callable,
                captures: vec![0],
                environment: Some(environment.clone()),
            },
            VmInstruction::CallIndirect {
                dst: 2,
                callee: 1,
                arguments: vec![],
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut valid = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: Some(Digest::of_bytes(b"trusted-runtime-manifest")),
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(callable, closure), (entry, entry_function)]),
        callable_environments: BTreeMap::from([(callable, environment.clone())]),
        fingerprint: Digest::of_bytes(b"callable-environment-program"),
    };
    valid.fingerprint = valid.computed_fingerprint();
    let encoded = encode_program(&valid);
    assert_eq!(decode_program(&encoded).unwrap(), valid);
    assert_eq!(
        verify_vm_program(valid.clone()).unwrap().run_i64().unwrap(),
        42
    );

    // The lexical environment brand is an executable provenance witness, not
    // merely capture-layout metadata.  Even a sibling whose body and ABI are
    // byte-for-byte compatible cannot be substituted for this source lift.
    let sibling = DefKey(Digest::of_bytes(b"callable-environment-sibling"));
    let mut forged_target = valid.clone();
    let mut sibling_function = forged_target.functions.remove(&callable).unwrap();
    sibling_function.definition = sibling;
    forged_target.functions.insert(sibling, sibling_function);
    let instruction = &mut forged_target
        .functions
        .get_mut(&entry)
        .unwrap()
        .instructions[1];
    let VmInstruction::MakeCallable { callee, .. } = instruction else {
        panic!("expected callable construction")
    };
    *callee = sibling;
    let environment = forged_target
        .callable_environments
        .remove(&callable)
        .unwrap();
    forged_target
        .callable_environments
        .insert(sibling, environment);
    forged_target.fingerprint = forged_target.computed_fingerprint();
    let forged_target_bytes = encode_program(&forged_target);
    assert!(matches!(
        verify_vm_program(forged_target),
        Err(VmArtifactError::InvalidCallableEnvironment {
            message: "callable environment brand does not authenticate target"
        })
    ));
    assert!(matches!(
        decode_and_verify_program(&forged_target_bytes),
        Err(VmArtifactError::InvalidCallableEnvironment {
            message: "callable environment brand does not authenticate target"
        })
    ));

    // Generic lifted bodies use a distinct key derived from the enclosing
    // instance.  The witness accepts that canonical materialization but
    // rejects a descriptor whose instance is changed in both the producer
    // and registry, closing the serialized cross-function spoofing path.
    let instance = Digest::of_bytes(b"callable-environment-generic-instance");
    let materialized = DefKey(Digest::of_parts([
        b"grandiose-stage0-lifted-callable-instance-v1".as_slice(),
        instance.as_bytes().as_slice(),
        callable.0.as_bytes().as_slice(),
    ]));
    let mut materialized_program = valid.clone();
    let mut materialized_function = materialized_program.functions.remove(&callable).unwrap();
    materialized_function.definition = materialized;
    materialized_program
        .functions
        .insert(materialized, materialized_function);
    let instruction = &mut materialized_program
        .functions
        .get_mut(&entry)
        .unwrap()
        .instructions[1];
    let VmInstruction::MakeCallable {
        callee,
        environment: Some(environment),
        ..
    } = instruction
    else {
        panic!("expected sealed callable construction")
    };
    *callee = materialized;
    environment.instance = Some(instance);
    let mut environment = materialized_program
        .callable_environments
        .remove(&callable)
        .unwrap();
    environment.instance = Some(instance);
    materialized_program
        .callable_environments
        .insert(materialized, environment);
    materialized_program.fingerprint = materialized_program.computed_fingerprint();
    let materialized_bytes = encode_program(&materialized_program);
    assert_eq!(
        verify_vm_program(materialized_program.clone())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
    assert_eq!(
        decode_and_verify_program(&materialized_bytes)
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );

    let mut forged_instance = materialized_program;
    let forged_instance_digest = Digest::of_bytes(b"forged-callable-environment-instance");
    let instruction = &mut forged_instance
        .functions
        .get_mut(&entry)
        .unwrap()
        .instructions[1];
    let VmInstruction::MakeCallable {
        environment: Some(environment),
        ..
    } = instruction
    else {
        panic!("expected sealed callable construction")
    };
    environment.instance = Some(forged_instance_digest);
    forged_instance
        .callable_environments
        .get_mut(&materialized)
        .unwrap()
        .instance = Some(forged_instance_digest);
    forged_instance.fingerprint = forged_instance.computed_fingerprint();
    let forged_instance_bytes = encode_program(&forged_instance);
    assert!(matches!(
        verify_vm_program(forged_instance),
        Err(VmArtifactError::InvalidCallableEnvironment {
            message: "callable environment brand does not authenticate target"
        })
    ));
    assert!(matches!(
        decode_and_verify_program(&forged_instance_bytes),
        Err(VmArtifactError::InvalidCallableEnvironment {
            message: "callable environment brand does not authenticate target"
        })
    ));

    let mut orphan_registry = valid.clone();
    let orphan_owner = DefKey(Digest::of_bytes(b"orphan-callable-environment-owner"));
    let orphan = DefKey(Digest::of_parts([
        b"grandiose-stage0-lifted-callable".as_slice(),
        orphan_owner.0.as_bytes().as_slice(),
        0_u32.to_le_bytes().as_slice(),
    ]));
    orphan_registry.callable_environments.insert(
        orphan,
        VmCaptureEnvironment {
            owner: orphan_owner,
            callable: 0,
            instance: None,
            captures: vec![],
        },
    );
    orphan_registry.fingerprint = orphan_registry.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(orphan_registry),
        Err(VmArtifactError::InvalidCallableEnvironment {
            message: "callable environment registry does not exactly match producers"
        })
    ));

    let mut forged_brand = valid.clone();
    let instruction = &mut forged_brand.functions.get_mut(&entry).unwrap().instructions[1];
    let VmInstruction::MakeCallable { environment, .. } = instruction else {
        panic!("expected callable construction")
    };
    environment.as_mut().unwrap().callable += 1;
    forged_brand.fingerprint = forged_brand.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(forged_brand),
        Err(VmArtifactError::InvalidCallableEnvironment { .. })
    ));

    let mut forged_count = valid.clone();
    let instruction = &mut forged_count.functions.get_mut(&entry).unwrap().instructions[1];
    let VmInstruction::MakeCallable { environment, .. } = instruction else {
        panic!("expected callable construction")
    };
    environment.as_mut().unwrap().captures.clear();
    forged_count.fingerprint = forged_count.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(forged_count),
        Err(VmArtifactError::InvalidCallableEnvironment { .. })
    ));

    let mut forged_type = valid.clone();
    let instruction = &mut forged_type.functions.get_mut(&entry).unwrap().instructions[1];
    let VmInstruction::MakeCallable { environment, .. } = instruction else {
        panic!("expected callable construction")
    };
    environment.as_mut().unwrap().captures[0].ty = VmType::Bool;
    forged_type.fingerprint = forged_type.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(forged_type),
        Err(VmArtifactError::InvalidCallableEnvironment { .. })
    ));

    let mut forged_mode = valid;
    let instruction = &mut forged_mode.functions.get_mut(&entry).unwrap().instructions[1];
    let VmInstruction::MakeCallable { environment, .. } = instruction else {
        panic!("expected callable construction")
    };
    environment.as_mut().unwrap().captures[0].mode = VmCaptureMode::SharedBorrow;
    forged_mode.fingerprint = forged_mode.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(forged_mode),
        Err(VmArtifactError::InvalidCallableEnvironment { .. })
    ));
}

#[test]
fn callable_type_decoder_limits_recursive_hostile_encodings() {
    let mut ty = VmType::I64;
    for _ in 0..98 {
        ty = VmType::Callable {
            parameters: vec![],
            result: Box::new(ty),
            effects: Box::<VmEffectRow>::default(),
        };
    }
    let candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"deep-callable-type")),
            captures: 0,
            parameters: 0,
            registers: vec![ty],
            instructions: vec![VmInstruction::Return { value: 0 }],
        },
        fingerprint: Digest::of_bytes(b"fingerprint-is-not-checked-by-decoder"),
    };
    assert!(matches!(
        decode_artifact(&encode_artifact(&candidate)),
        Err(VmArtifactError::DecodeLimit {
            kind: "callable type nesting",
            limit: 96,
        })
    ));
}

#[test]
fn callable_effect_rows_are_part_of_artifact_and_program_type_contracts() {
    let effect_a = DefKey(Digest::of_bytes(b"callable-effect-row-a"));
    let effect_b = DefKey(Digest::of_bytes(b"callable-effect-row-b"));
    let callable = |effect| VmType::Callable {
        parameters: vec![],
        result: Box::new(VmType::I64),
        effects: Box::new(VmEffectRow {
            effects: vec![grandiose_stage0::VmEffectInstance {
                definition: effect,
                arguments: vec![],
            }],
            projections: vec![],
            tail: None,
        }),
    };
    let expected = callable(effect_a);
    let found = callable(effect_b);

    // A standalone artifact cannot pass an effectful callable where a host
    // ABI requests the same parameter/result shape with another effect row.
    let mut artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"callable-effect-artifact")),
            captures: 0,
            parameters: 0,
            registers: vec![found.clone(), VmType::I64],
            instructions: vec![
                VmInstruction::MakeCallable {
                    dst: 0,
                    callee: DefKey(Digest::of_bytes(b"unresolved-standalone-callable")),
                    captures: vec![],
                    environment: None,
                },
                VmInstruction::HostCall {
                    dst: 1,
                    capability: "test".into(),
                    symbol: "accept".into(),
                    parameters: vec![expected.clone()],
                    result: VmType::I64,
                    arguments: vec![0],
                },
                VmInstruction::Return { value: 1 },
            ],
        },
        fingerprint: Digest::of_bytes(b"callable-effect-artifact-stale"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    assert!(matches!(
        verify_vm(artifact),
        Err(VmArtifactError::TypeMismatch { .. })
    ));

    // The independent program verifier performs the same exact comparison at
    // a direct boundary, including rows nested in callable parameter types.
    let entry = DefKey(Digest::of_bytes(b"callable-effect-entry"));
    let target = DefKey(Digest::of_bytes(b"callable-effect-target"));
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([
            (
                entry,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: entry,
                    captures: 0,
                    parameters: 1,
                    registers: vec![found, VmType::Unit],
                    instructions: vec![
                        VmInstruction::Call {
                            dst: 1,
                            callee: target,
                            arguments: vec![0],
                        },
                        VmInstruction::Return { value: 1 },
                    ],
                },
            ),
            (
                target,
                VmFunction {
                    nominal_copy_descriptors: vec![],
                    definition: target,
                    captures: 0,
                    parameters: 1,
                    registers: vec![expected, VmType::Unit],
                    instructions: vec![
                        VmInstruction::ConstUnit { dst: 1 },
                        VmInstruction::Return { value: 1 },
                    ],
                },
            ),
        ]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"callable-effect-program-stale"),
    };
    program.fingerprint = program.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(program),
        Err(VmArtifactError::TypeMismatch { .. })
    ));
}

#[test]
fn verifier_rejects_noncanonical_callable_effect_rows() {
    let first = DefKey(Digest::of_bytes(b"callable-row-first"));
    let second = DefKey(Digest::of_bytes(b"callable-row-second"));
    let (greater, lesser) = if first.0.as_bytes() > second.0.as_bytes() {
        (first, second)
    } else {
        (second, first)
    };
    let malformed = VmType::Callable {
        parameters: vec![],
        result: Box::new(VmType::I64),
        effects: Box::new(VmEffectRow {
            effects: vec![
                grandiose_stage0::VmEffectInstance {
                    definition: greater,
                    arguments: vec![],
                },
                grandiose_stage0::VmEffectInstance {
                    definition: lesser,
                    arguments: vec![],
                },
            ],
            projections: vec![],
            tail: None,
        }),
    };
    let mut artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"noncanonical-callable-effect-row")),
            captures: 0,
            parameters: 0,
            registers: vec![malformed, VmType::I64],
            instructions: vec![
                VmInstruction::MakeCallable {
                    dst: 0,
                    callee: DefKey(Digest::of_bytes(b"malformed-callable-row-target")),
                    captures: vec![],
                    environment: None,
                },
                VmInstruction::ConstI64 { dst: 1, value: 42 },
                VmInstruction::Return { value: 1 },
            ],
        },
        fingerprint: Digest::of_bytes(b"noncanonical-callable-effect-row-stale"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    assert!(matches!(
        verify_vm(artifact),
        Err(VmArtifactError::NonCanonicalEncoding)
    ));
}

#[test]
fn vm_executes_verified_multiblock_mir_boolean_control_flow() {
    let i64_ty = Type::Scalar(ScalarType::I64);
    let mir = MirFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"mir-branch")),
        captures: 0,
        parameters: vec![],
        locals: vec![
            MirLocalDecl {
                ty: Type::Scalar(ScalarType::Bool),
                source: CoreId(u32::MAX),
            },
            MirLocalDecl {
                ty: i64_ty.clone(),
                source: CoreId(u32::MAX),
            },
            MirLocalDecl {
                ty: i64_ty.clone(),
                source: CoreId(u32::MAX),
            },
        ],
        result: i64_ty,
        control: MirControlTables::default(),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![MirInstruction::ConstBool {
                    dst: MirLocal(0),
                    value: true,
                }],
                terminator: MirTerminator::SwitchBool {
                    condition: MirLocal(0),
                    then_target: MirBlockId(1),
                    then_arguments: vec![],
                    else_target: MirBlockId(2),
                    else_arguments: vec![],
                },
            },
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![MirInstruction::ConstI64 {
                    dst: MirLocal(1),
                    value: 42,
                }],
                terminator: MirTerminator::Return { value: MirLocal(1) },
            },
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![MirInstruction::ConstI64 {
                    dst: MirLocal(2),
                    value: 7,
                }],
                terminator: MirTerminator::Return { value: MirLocal(2) },
            },
        ],
    }
    .with_frozen_control_tables();
    let candidate = emit_vm(&mir).unwrap();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&bytes)
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn vm_lowers_typed_cfg_edge_arguments_through_parallel_copies() {
    let i64_ty = Type::Scalar(ScalarType::I64);
    let local = |ty| MirLocalDecl {
        ty,
        source: CoreId(u32::MAX),
    };
    let mir = MirFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"mir-edge-arguments")),
        captures: 0,
        parameters: vec![],
        locals: vec![
            local(Type::Scalar(ScalarType::Bool)),
            local(i64_ty.clone()),
            local(i64_ty.clone()),
            local(i64_ty.clone()),
            local(i64_ty.clone()),
        ],
        result: i64_ty,
        control: MirControlTables::default(),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![
                    MirInstruction::ConstBool {
                        dst: MirLocal(0),
                        value: true,
                    },
                    MirInstruction::ConstI64 {
                        dst: MirLocal(1),
                        value: 42,
                    },
                    MirInstruction::ConstI64 {
                        dst: MirLocal(2),
                        value: 7,
                    },
                ],
                terminator: MirTerminator::SwitchBool {
                    condition: MirLocal(0),
                    then_target: MirBlockId(1),
                    then_arguments: vec![MirLocal(1)],
                    else_target: MirBlockId(2),
                    else_arguments: vec![MirLocal(2)],
                },
            },
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![MirLocal(3)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(3) },
            },
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![MirLocal(4)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(4) },
            },
        ],
    };
    assert_eq!(
        verify_vm(emit_vm(&mir).unwrap())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn vm_omits_identity_cfg_edge_transfers() {
    let i64_ty = Type::Scalar(ScalarType::I64);
    let mir = MirFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"mir-identity-edge")),
        captures: 0,
        parameters: vec![],
        locals: vec![MirLocalDecl {
            ty: i64_ty.clone(),
            source: CoreId(u32::MAX),
        }],
        result: i64_ty,
        control: MirControlTables::default(),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![MirInstruction::ConstI64 {
                    dst: MirLocal(0),
                    value: 42,
                }],
                terminator: MirTerminator::Goto {
                    target: MirBlockId(1),
                    arguments: vec![MirLocal(0)],
                },
            },
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![MirLocal(0)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(0) },
            },
        ],
    }
    .with_frozen_control_tables();
    let candidate = emit_vm(&mir).unwrap();
    assert_eq!(candidate.function.instructions.len(), 4);
    assert!(matches!(
        candidate.function.instructions.as_slice(),
        [
            VmInstruction::DeclareResult { .. },
            VmInstruction::ConstI64 { value: 42, .. },
            VmInstruction::Jump { .. },
            VmInstruction::Return { .. },
        ]
    ));
    assert_eq!(verify_vm(candidate).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn vm_preserves_mir_leave_cleanup_and_label_identity() {
    let i64_ty = Type::Scalar(ScalarType::I64);
    let owner = DefKey(Digest::of_bytes(b"mir-leave-owner"));
    let mir = MirFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"mir-cleanup-leave")),
        captures: 0,
        parameters: vec![],
        locals: vec![
            MirLocalDecl {
                ty: i64_ty.clone(),
                source: CoreId(u32::MAX),
            },
            MirLocalDecl {
                ty: i64_ty.clone(),
                source: CoreId(u32::MAX),
            },
        ],
        result: i64_ty,
        control: MirControlTables::default(),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![MirInstruction::ConstI64 {
                    dst: MirLocal(0),
                    value: 42,
                }],
                terminator: MirTerminator::Leave {
                    label: MirLabelId::UNASSIGNED,
                    brand: LabelBrand { owner, label: 9 },
                    target: MirBlockId(1),
                    arguments: vec![MirLocal(0)],
                    cleanup: MirCleanupPlan {
                        source_storage_scope: MirSourceStorageScopeId::ROOT,
                        target_storage_scope: MirSourceStorageScopeId::ROOT,
                        moved_paths: vec![],
                        moved_places: vec![],
                        active_loans: vec![],
                        drop_flags: vec![],
                        actions: vec![],
                        protected_values: vec![],
                    },
                },
            },
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![MirLocal(1)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(1) },
            },
        ],
    }
    .with_frozen_control_tables();
    let candidate = emit_vm(&mir).unwrap();
    assert!(matches!(
        candidate.function.instructions.as_slice(),
        [
            VmInstruction::DeclareResult { .. },
            VmInstruction::ConstI64 { .. },
            VmInstruction::Leave {
                brand_owner,
                brand_label: 9,
                arguments,
                destinations,
                cleanup,
                ..
            },
            VmInstruction::Return { .. },
        ] if *brand_owner == owner
            && arguments == &vec![0]
            && destinations == &vec![1]
            && cleanup.validate()
    ));
    assert_eq!(verify_vm(candidate).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn text_materialization_obeys_value_limits_before_standalone_and_decoded_program_allocation() {
    let definition = DefKey(Digest::of_bytes(b"text-materialization-limits"));
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::Text, VmType::Text, VmType::Text],
        instructions: vec![
            VmInstruction::ConstText {
                dst: 0,
                value: "a".into(),
            },
            VmInstruction::ConstText {
                dst: 1,
                value: "b".into(),
            },
            VmInstruction::TextConcat {
                dst: 2,
                left: 0,
                right: 1,
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let tight = VmExecutionLimits {
        max_value_elements: 1,
        ..VmExecutionLimits::default()
    };
    let mut artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: function.clone(),
        fingerprint: Digest::of_bytes(b"text-materialization-artifact-stale"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    let artifact = verify_vm(artifact).unwrap();
    assert!(matches!(
        artifact.run_text_with_limits(tight),
        Err(VmArtifactError::ValueSizeLimit {
            kind: "text bytes",
            limit: 1,
            found: 2,
        })
    ));
    assert_eq!(artifact.run_text().unwrap(), "ab");

    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: definition,
        functions: BTreeMap::from([(definition, function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"text-materialization-program-stale"),
    };
    program.fingerprint = program.computed_fingerprint();
    let bytes = encode_program(&program);
    let program = decode_and_verify_program(&bytes).unwrap();
    assert!(matches!(
        program.run_text_with_limits(tight),
        Err(VmArtifactError::ValueSizeLimit {
            kind: "text bytes",
            limit: 1,
            found: 2,
        })
    ));
    assert_eq!(program.run_text().unwrap(), "ab");
}

#[test]
fn vm_leave_in_cfg_successor_retains_outer_handler_depth() {
    let i64_ty = Type::Scalar(ScalarType::I64);
    let owner = DefKey(Digest::of_bytes(b"successor-leave-owner"));
    let effect = DefKey(Digest::of_bytes(b"successor-leave-effect"));
    let mut mir = MirFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"successor-leave")),
        captures: 0,
        parameters: vec![],
        locals: vec![
            MirLocalDecl { ty: i64_ty.clone(), source: CoreId(u32::MAX) },
            MirLocalDecl { ty: i64_ty.clone(), source: CoreId(u32::MAX) },
        ],
        result: i64_ty,
        control: MirControlTables::default(),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![
                    MirInstruction::ConstI64 { dst: MirLocal(0), value: 42 },
                    MirInstruction::InstallHandler {
                        site: grandiose_stage0::MirHandlerSiteId::UNASSIGNED,
                        effect,
                        effect_arguments: vec![],
                        operation: 0,
                        payload_destinations: vec![],
                        resume_type: Type::Scalar(ScalarType::I64),
                        continuation: grandiose_stage0::MirContinuationPolicy::Consume,
                        target: MirBlockId(3),
                    },
                ],
                terminator: MirTerminator::Goto { target: MirBlockId(1), arguments: vec![] },
            },
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Leave {
                    label: MirLabelId::UNASSIGNED,
                    brand: LabelBrand { owner, label: 0 },
                    target: MirBlockId(2),
                    arguments: vec![MirLocal(0)],
                    cleanup: MirCleanupPlan {
                        source_storage_scope: MirSourceStorageScopeId::ROOT,
                        target_storage_scope: MirSourceStorageScopeId::ROOT,
                        moved_paths: vec![], moved_places: vec![], active_loans: vec![],
                        drop_flags: vec![], actions: vec![], protected_values: vec![],
                    },
                },
            },
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![MirLocal(1)],
                instructions: vec![MirInstruction::UninstallHandler],
                terminator: MirTerminator::Return { value: MirLocal(1) },
            },
            MirBlock { scope: MirScopeId::ROOT, parameters: vec![], instructions: vec![], terminator: MirTerminator::Unreachable },
        ],
    }.with_frozen_control_tables();
    mir.control.leave_handler_depths.insert(MirBlockId(1), 1);
    let candidate = emit_vm(&mir).expect("successor leave must lower");
    assert!(candidate.function.instructions.iter().any(|instruction| matches!(
        instruction,
        VmInstruction::Leave { handler_depth: 1, .. }
    )));
    assert_eq!(verify_vm(candidate).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn verifier_rejects_a_label_brand_retargeted_to_another_typed_destination() {
    let definition = DefKey(Digest::of_bytes(b"forged-vm-label-contract"));
    let owner = DefKey(Digest::of_bytes(b"forged-vm-label-contract-owner"));
    let function = VmFunction {
        definition,
        nominal_copy_descriptors: vec![],
        captures: 0,
        parameters: 0,
        registers: vec![VmType::Bool, VmType::I64, VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::ConstBool {
                dst: 0,
                value: true,
            },
            VmInstruction::BranchBool {
                condition: 0,
                then_target: 2,
                else_target: 4,
            },
            VmInstruction::ConstI64 { dst: 1, value: 1 },
            VmInstruction::Leave {
                brand_owner: owner,
                brand_label: 0,
                handler_depth: 0,
                target: 6,
                arguments: vec![1],
                destinations: vec![3],
                cleanup: VmCleanupProof {
                    moved_places: vec![],
                    active_loans: vec![],
                    storage_erasure: VmStorageErasureWitness::without_source_storage(),
                },
            },
            VmInstruction::ConstI64 { dst: 2, value: 2 },
            VmInstruction::Leave {
                brand_owner: owner,
                brand_label: 0,
                handler_depth: 0,
                target: 7,
                arguments: vec![2],
                destinations: vec![2],
                cleanup: VmCleanupProof {
                    moved_places: vec![],
                    active_loans: vec![],
                    storage_erasure: VmStorageErasureWitness::without_source_storage(),
                },
            },
            VmInstruction::Return { value: 3 },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: function.clone(),
        fingerprint: Digest::of_bytes(b"stale-forged-vm-label-contract"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    assert!(matches!(
        verify_vm(artifact),
        Err(VmArtifactError::InvalidLabelContract { .. })
    ));

    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: definition,
        functions: BTreeMap::from([(definition, function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"stale-forged-vm-label-contract-program"),
    };
    program.fingerprint = program.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(program),
        Err(VmArtifactError::InvalidLabelContract { .. })
    ));
}

#[test]
fn verifier_rejects_branch_targets_outside_the_instruction_stream() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"invalid-branch-target")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::Bool],
            instructions: vec![
                VmInstruction::ConstBool {
                    dst: 0,
                    value: true,
                },
                VmInstruction::BranchBool {
                    condition: 0,
                    then_target: 99,
                    else_target: 99,
                },
            ],
        },
        fingerprint: Digest::of_bytes(b"invalid-branch-fingerprint"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::InvalidInstructionTarget { target: 99 })
    ));
}

#[test]
fn verifier_rejects_ordinary_control_flow_into_handler_clauses() {
    let effect = DefKey(Digest::of_bytes(b"forged-handler-entry"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"branch-into-handler-clause")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::Bool],
            instructions: vec![
                VmInstruction::ConstBool {
                    dst: 0,
                    value: true,
                },
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::Unit,
                    continuation: VmContinuationPolicy::Consume,
                    target: 4,
                },
                VmInstruction::BranchBool {
                    condition: 0,
                    then_target: 4,
                    else_target: 3,
                },
                VmInstruction::Trap,
                VmInstruction::Cancel,
            ],
        },
        fingerprint: Digest::of_bytes(b"branch-into-handler-clause-fingerprint"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::HandlerTargetReachedByControlFlow { target: 4 })
    ));

    let mut fallthrough = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"fallthrough-into-handler-clause")),
            captures: 0,
            parameters: 0,
            registers: vec![],
            instructions: vec![
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::Unit,
                    continuation: VmContinuationPolicy::Consume,
                    target: 1,
                },
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"fallthrough-into-handler-clause-fingerprint"),
    };
    fallthrough.fingerprint = fallthrough.computed_fingerprint();
    assert!(matches!(
        verify_vm(fallthrough),
        Err(VmArtifactError::HandlerTargetReachedByControlFlow { target: 1 })
    ));
}

#[test]
fn verifier_rejects_dynamic_label_targets_at_private_handler_clauses() {
    let owner = DefKey(Digest::of_bytes(b"label-into-handler-clause"));
    let effect = DefKey(Digest::of_bytes(b"label-into-handler-clause-effect"));
    let label = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::Unit),
        effects: Box::<VmEffectRow>::default(),
    };
    // The label is created before the handler and is otherwise never invoked.
    // Its target alone must be rejected: a later indirect invocation would
    // enter the private clause without `Perform` materializing its payload and
    // continuation evidence.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: owner,
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64, label],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::MakeLabel {
                    dst: 1,
                    brand_owner: owner,
                    brand_label: 0,
                    target: 5,
                    destination: 0,
                },
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::Unit,
                    continuation: VmContinuationPolicy::Consume,
                    target: 5,
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 0 },
                VmInstruction::Cancel,
            ],
        },
        fingerprint: Digest::of_bytes(b"label-into-handler-clause-fingerprint"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::HandlerTargetReachedByControlFlow { target: 5 })
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::HandlerTargetReachedByControlFlow { target: 5 })
    ));
}

#[test]
fn verifier_rejects_dynamic_labels_with_one_brand_and_contradictory_targets() {
    let owner = DefKey(Digest::of_bytes(b"contradictory-dynamic-label-owner"));
    let label = VmType::Callable {
        parameters: vec![VmType::I64],
        result: Box::new(VmType::Unit),
        effects: Box::<VmEffectRow>::default(),
    };
    // Both values are well-typed labels and neither target is a handler
    // entry. Their shared proof-only brand is nonetheless one static label,
    // so it cannot name two runtime destinations.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: owner,
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64, label.clone(), label],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::MakeLabel {
                    dst: 1,
                    brand_owner: owner,
                    brand_label: 0,
                    target: 4,
                    destination: 0,
                },
                VmInstruction::MakeLabel {
                    dst: 2,
                    brand_owner: owner,
                    brand_label: 0,
                    target: 5,
                    destination: 0,
                },
                VmInstruction::Return { value: 0 },
                VmInstruction::Return { value: 0 },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"contradictory-dynamic-label-fingerprint"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::InvalidLabelContract { .. })
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::InvalidLabelContract { .. })
    ));
}

#[test]
fn vm_emits_and_executes_the_checked_mir_unreachable_terminal_as_a_trap() {
    let i64_ty = Type::Scalar(ScalarType::I64);
    let local = |ty| MirLocalDecl {
        ty,
        source: CoreId(u32::MAX),
    };
    let mir = MirFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"mir-trap-terminal")),
        captures: 0,
        parameters: vec![],
        locals: vec![local(Type::Scalar(ScalarType::Bool)), local(i64_ty.clone())],
        result: i64_ty,
        control: MirControlTables::default(),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![
                    MirInstruction::ConstBool {
                        dst: MirLocal(0),
                        value: false,
                    },
                    MirInstruction::ConstI64 {
                        dst: MirLocal(1),
                        value: 42,
                    },
                ],
                terminator: MirTerminator::SwitchBool {
                    condition: MirLocal(0),
                    then_target: MirBlockId(1),
                    then_arguments: vec![],
                    else_target: MirBlockId(2),
                    else_arguments: vec![],
                },
            },
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(1) },
            },
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Unreachable,
            },
        ],
    };
    let candidate = emit_vm(&mir).unwrap();
    assert_eq!(candidate.schema, grandiose_stage0::STAGE0_VM_SCHEMA);
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert!(matches!(
        verify_vm(candidate).unwrap().run_i64(),
        Err(VmArtifactError::Trap)
    ));
}

#[test]
fn program_verifier_rejects_inconsistent_generic_call_bindings() {
    let generic = DefKey(Digest::of_bytes(b"generic-pair"));
    let entry = DefKey(Digest::of_bytes(b"generic-call-entry"));
    let generic_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: generic,
        captures: 0,
        parameters: 2,
        registers: vec![VmType::Generic(0), VmType::Generic(0), VmType::Generic(0)],
        instructions: vec![
            VmInstruction::Copy { dst: 2, src: 0 },
            VmInstruction::Return { value: 2 },
        ],
    };
    let entry_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::Bool, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 },
            VmInstruction::ConstBool {
                dst: 1,
                value: true,
            },
            VmInstruction::Call {
                dst: 2,
                callee: generic,
                arguments: vec![0, 1],
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(generic, generic_function), (entry, entry_function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"generic-call-mismatch"),
    };
    program.fingerprint = program.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(program),
        Err(VmArtifactError::TypeMismatch { register: 1, .. })
    ));
}

#[test]
fn generic_vm_programs_round_trip_and_execute_after_call_instantiation() {
    let generic = DefKey(Digest::of_bytes(b"generic-identity"));
    let entry = DefKey(Digest::of_bytes(b"generic-identity-entry"));
    let generic_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: generic,
        captures: 0,
        parameters: 1,
        registers: vec![VmType::Generic(0), VmType::Generic(0)],
        instructions: vec![
            VmInstruction::Copy { dst: 1, src: 0 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let entry_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 },
            VmInstruction::Call {
                dst: 1,
                callee: generic,
                arguments: vec![0],
            },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(generic, generic_function), (entry, entry_function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"generic-identity-program"),
    };
    program.fingerprint = program.computed_fingerprint();
    let bytes = encode_program(&program);
    assert_eq!(decode_program(&bytes).unwrap(), program);
    assert_eq!(verify_vm_program(program).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn unique_reference_mutates_its_live_register_and_round_trips() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"unique-reference-store")),
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                VmType::Reference {
                    unique: true,
                    referent: Box::new(VmType::I64),
                },
                VmType::I64,
                VmType::I64,
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 40 },
                VmInstruction::Borrow {
                    dst: 1,
                    src: 0,
                    fields: vec![],
                    unique: true,
                    reborrow: false,
                },
                VmInstruction::ConstI64 { dst: 2, value: 42 },
                VmInstruction::DerefStore {
                    reference: 1,
                    src: 2,
                },
                VmInstruction::DerefCopy {
                    dst: 3,
                    reference: 1,
                },
                VmInstruction::Return { value: 3 },
            ],
        },
        fingerprint: Digest::of_bytes(b"reference-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&bytes)
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn unique_reference_writeback_survives_direct_call_and_return() {
    let callee = DefKey(Digest::of_bytes(b"unique-reference-mutator"));
    let entry = DefKey(Digest::of_bytes(b"unique-reference-mutator-entry"));
    let unique_i64 = VmType::Reference {
        unique: true,
        referent: Box::new(VmType::I64),
    };
    let callee_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: callee,
        captures: 0,
        parameters: 1,
        registers: vec![unique_i64.clone(), VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 1, value: 42 },
            VmInstruction::DerefStore {
                reference: 0,
                src: 1,
            },
            VmInstruction::Return { value: 0 },
        ],
    };
    let entry_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![
            VmType::I64,
            unique_i64.clone(),
            unique_i64,
            VmType::I64,
            VmType::I64,
        ],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 1 },
            VmInstruction::Borrow {
                dst: 1,
                src: 0,
                fields: vec![],
                unique: true,
                reborrow: false,
            },
            VmInstruction::Call {
                dst: 2,
                callee,
                arguments: vec![1],
            },
            VmInstruction::ConstI64 { dst: 3, value: 43 },
            VmInstruction::DerefStore {
                reference: 2,
                src: 3,
            },
            VmInstruction::DerefCopy {
                dst: 4,
                reference: 1,
            },
            VmInstruction::Return { value: 4 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(callee, callee_function), (entry, entry_function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"unique-reference-mutator-program"),
    };
    program.fingerprint = program.computed_fingerprint();
    assert_eq!(verify_vm_program(program).unwrap().run_i64().unwrap(), 43);
}

#[test]
fn unique_reference_writeback_survives_indirect_call_and_return() {
    let callee = DefKey(Digest::of_bytes(b"indirect-unique-reference-mutator"));
    let entry = DefKey(Digest::of_bytes(b"indirect-unique-reference-mutator-entry"));
    let unique_i64 = VmType::Reference {
        unique: true,
        referent: Box::new(VmType::I64),
    };
    let callable = VmType::Callable {
        parameters: vec![unique_i64.clone()],
        result: Box::new(unique_i64.clone()),
        effects: Box::<VmEffectRow>::default(),
    };
    let callee_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: callee,
        captures: 0,
        parameters: 1,
        registers: vec![unique_i64.clone(), VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 1, value: 42 },
            VmInstruction::DerefStore {
                reference: 0,
                src: 1,
            },
            VmInstruction::Return { value: 0 },
        ],
    };
    let entry_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![
            VmType::I64,
            unique_i64.clone(),
            callable,
            unique_i64,
            VmType::I64,
            VmType::I64,
        ],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 1 },
            VmInstruction::Borrow {
                dst: 1,
                src: 0,
                fields: vec![],
                unique: true,
                reborrow: false,
            },
            VmInstruction::MakeCallable {
                dst: 2,
                callee,
                captures: vec![],
                environment: None,
            },
            VmInstruction::CallIndirect {
                dst: 3,
                callee: 2,
                arguments: vec![1],
            },
            VmInstruction::ConstI64 { dst: 4, value: 43 },
            VmInstruction::DerefStore {
                reference: 3,
                src: 4,
            },
            VmInstruction::DerefCopy {
                dst: 5,
                reference: 1,
            },
            VmInstruction::Return { value: 5 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(callee, callee_function), (entry, entry_function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"indirect-unique-reference-mutator-program"),
    };
    program.fingerprint = program.computed_fingerprint();
    assert_eq!(verify_vm_program(program).unwrap().run_i64().unwrap(), 43);
}

#[test]
fn verifier_rejects_copying_a_nominal_carrier_of_a_unique_reference() {
    let definition = DefKey(Digest::of_bytes(b"affine-nominal-copy"));
    let unique_i64 = VmType::Reference {
        unique: true,
        referent: Box::new(VmType::I64),
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            definition,
            nominal_copy_descriptors: vec![VmNominalCopyDescriptor {
                definition,
                arguments: vec![],
                variants: vec![vec![unique_i64.clone()]],
            }],
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                unique_i64.clone(),
                VmType::Nominal {
                    definition,
                    arguments: vec![],
                },
                VmType::Nominal {
                    definition,
                    arguments: vec![],
                },
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 1 },
                VmInstruction::Borrow {
                    dst: 1,
                    src: 0,
                    fields: vec![],
                    unique: true,
                    reborrow: false,
                },
                VmInstruction::MakeRecord {
                    dst: 2,
                    definition,
                    fields: vec![1],
                    field_types: vec![unique_i64],
                },
                VmInstruction::Copy { dst: 3, src: 2 },
                VmInstruction::Return { value: 2 },
            ],
        },
        fingerprint: Digest::of_bytes(b"affine-nominal-copy-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::AffineValueCopy { register: 2 })
    ));
}

#[test]
fn verifier_rejects_a_forged_tuple_borrow_referent_before_dereference() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"forged-tuple-borrow-referent")),
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                VmType::Tuple(vec![VmType::I64]),
                VmType::Reference {
                    unique: false,
                    referent: Box::new(VmType::Bool),
                },
                VmType::Bool,
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::MakeTuple {
                    dst: 1,
                    fields: vec![0],
                },
                VmInstruction::Borrow {
                    dst: 2,
                    src: 1,
                    fields: vec![0],
                    unique: false,
                    reborrow: false,
                },
                VmInstruction::DerefCopy {
                    dst: 3,
                    reference: 2,
                },
                VmInstruction::Return { value: 3 },
            ],
        },
        fingerprint: Digest::of_bytes(b"forged-tuple-borrow-referent-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::TypeMismatch {
            register: 2,
            expected: VmType::I64,
            found: VmType::Bool,
        })
    ));
}

#[test]
fn verifier_rejects_forged_reborrow_capability_and_whole_place_referent() {
    let mut shared_to_unique = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"forged-shared-to-unique-reborrow")),
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                VmType::Reference {
                    unique: false,
                    referent: Box::new(VmType::I64),
                },
                VmType::Reference {
                    unique: true,
                    referent: Box::new(VmType::I64),
                },
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 1 },
                VmInstruction::Borrow {
                    dst: 1,
                    src: 0,
                    fields: vec![],
                    unique: false,
                    reborrow: false,
                },
                VmInstruction::Borrow {
                    dst: 2,
                    src: 1,
                    fields: vec![],
                    unique: true,
                    reborrow: true,
                },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"forged-shared-to-unique-reborrow"),
    };
    shared_to_unique.fingerprint = shared_to_unique.computed_fingerprint();
    assert!(matches!(
        verify_vm(shared_to_unique),
        Err(VmArtifactError::TypeMismatch { register: 1, .. })
    ));

    let mut wrong_referent = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"forged-whole-borrow-referent")),
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::I64,
                VmType::Reference {
                    unique: false,
                    referent: Box::new(VmType::Text),
                },
            ],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 1 },
                VmInstruction::Borrow {
                    dst: 1,
                    src: 0,
                    fields: vec![],
                    unique: false,
                    reborrow: false,
                },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"forged-whole-borrow-referent"),
    };
    wrong_referent.fingerprint = wrong_referent.computed_fingerprint();
    assert!(matches!(
        verify_vm(wrong_referent),
        Err(VmArtifactError::TypeMismatch { register: 1, .. })
    ));
}

#[test]
fn cleanup_carrying_leave_round_trips_and_unwinds_active_handler_frames() {
    let handler_effect = DefKey(Digest::of_bytes(b"leave-handler"));
    let label_owner = DefKey(Digest::of_bytes(b"leave-label-owner"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"cleanup-carrying-leave")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::InstallHandler {
                    effect: handler_effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 4,
                },
                VmInstruction::Leave {
                    brand_owner: label_owner,
                    brand_label: 7,
                    handler_depth: 0,
                    target: 3,
                    arguments: vec![0],
                    destinations: vec![1],
                    cleanup: VmCleanupProof {
                        moved_places: vec![VmCleanupPlace {
                            path: 0,
                            binding: 0,
                            root: "value".into(),
                            fields: vec![0],
                        }],
                        active_loans: vec![],
                        storage_erasure: VmStorageErasureWitness::without_source_storage(),
                    },
                },
                VmInstruction::Return { value: 1 },
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"cleanup-carrying-leave-candidate"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&bytes)
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: candidate.function.definition,
        functions: BTreeMap::from([(candidate.function.definition, candidate.function.clone())]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"cleanup-carrying-leave-program"),
    };
    program.fingerprint = program.computed_fingerprint();
    assert_eq!(verify_vm_program(program).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn cleanup_leave_preserves_the_lexical_outer_handler_prefix() {
    let outer_effect = DefKey(Digest::of_bytes(b"leave-retained-outer-handler"));
    let inner_effect = DefKey(Digest::of_bytes(b"leave-exited-inner-handler"));
    let owner = DefKey(Digest::of_bytes(b"leave-retained-prefix-owner"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"leave-retained-prefix")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::InstallHandler { effect: outer_effect, effect_arguments: vec![], operation: 0, payload_destinations: vec![], resume_type: VmType::I64, continuation: VmContinuationPolicy::Consume, target: 6 },
                VmInstruction::InstallHandler { effect: inner_effect, effect_arguments: vec![], operation: 0, payload_destinations: vec![], resume_type: VmType::I64, continuation: VmContinuationPolicy::Consume, target: 6 },
                VmInstruction::Leave {
                    brand_owner: owner,
                    brand_label: 3,
                    handler_depth: 1,
                    target: 4,
                    arguments: vec![0],
                    destinations: vec![1],
                    cleanup: VmCleanupProof { moved_places: vec![], active_loans: vec![], storage_erasure: VmStorageErasureWitness::without_source_storage() },
                },
                VmInstruction::UninstallHandler,
                VmInstruction::Return { value: 1 },
                VmInstruction::Trap,
            ],
        },
        fingerprint: Digest::of_bytes(b"leave-retained-prefix-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&bytes).unwrap(), candidate);
    assert_eq!(decode_and_verify_artifact(&bytes).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn lowered_partial_move_leave_keeps_only_the_residual_aggregate_cleanup() {
    let package = PackageKey("vm-partial-move-cleanup@0.1.0".into());
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; label done { move pair.left; transfer done pair.right; 0 } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    assert_eq!(
        flow.moved_places,
        vec![grandiose_stage0::MoveFact {
            root: "pair".into(),
            fields: vec![0],
        }]
    );
    let mir = MirLowering::lower(definition.key, &core, &flow)
        .function
        .expect("partial move with leave lowers");
    let mut artifact = emit_vm(&mir).expect("partial move cleanup emits");
    let pair = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Pair"))
        .expect("Pair definition")
        .key;
    // This direct lowering test intentionally bypasses the package linker,
    // which normally freezes declaration layouts onto every emitted body.
    // Supply the same declaration-owned record layout before independently
    // verifying the raw artifact.
    artifact.function.nominal_copy_descriptors = vec![VmNominalCopyDescriptor {
        definition: pair,
        arguments: vec![],
        variants: vec![vec![VmType::I64, VmType::I64]],
    }];
    artifact.fingerprint = artifact.computed_fingerprint();
    let cleanup = artifact
        .function
        .instructions
        .iter()
        .find_map(|instruction| match instruction {
            VmInstruction::Leave { cleanup, .. } => Some(cleanup),
            _ => None,
        })
        .expect("label transfer retains cleanup proof");
    assert!(cleanup.validate(), "{cleanup:#?}");
    assert_eq!(
        cleanup.moved_places,
        vec![VmCleanupPlace {
            path: 1,
            binding: 0,
            root: "pair".into(),
            fields: vec![0],
        }]
    );
    let bytes = encode_artifact(&artifact);
    assert_eq!(
        decode_and_verify_artifact(&bytes)
            .unwrap()
            .run_i64()
            .unwrap(),
        2
    );
}

#[test]
fn verifier_rejects_noncanonical_or_handler_entering_leave_edges() {
    let effect = DefKey(Digest::of_bytes(b"leave-reject-effect"));
    let owner = DefKey(Digest::of_bytes(b"leave-reject-owner"));
    let mut malformed = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"leave-reject-canonical")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 1 },
                VmInstruction::Leave {
                    brand_owner: owner,
                    brand_label: 0,
                    handler_depth: 0,
                    target: 2,
                    arguments: vec![0],
                    destinations: vec![1],
                    cleanup: VmCleanupProof {
                        moved_places: vec![
                            VmCleanupPlace {
                                path: 0,
                                binding: 0,
                                root: "x".into(),
                                fields: vec![],
                            },
                            VmCleanupPlace {
                                path: 1,
                                binding: 0,
                                root: "x".into(),
                                fields: vec![],
                            },
                        ],
                        active_loans: vec![],
                        storage_erasure: VmStorageErasureWitness::without_source_storage(),
                    },
                },
                VmInstruction::Return { value: 1 },
            ],
        },
        fingerprint: Digest::of_bytes(b"leave-reject-canonical-fingerprint"),
    };
    malformed.fingerprint = malformed.computed_fingerprint();
    assert!(matches!(
        verify_vm(malformed),
        Err(VmArtifactError::MalformedEncoding { .. })
    ));

    let mut enters_clause = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"leave-reject-clause")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 1 },
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: VmType::I64,
                    continuation: VmContinuationPolicy::Consume,
                    target: 3,
                },
                VmInstruction::Leave {
                    brand_owner: owner,
                    brand_label: 1,
                    handler_depth: 0,
                    target: 3,
                    arguments: vec![0],
                    destinations: vec![1],
                    cleanup: VmCleanupProof {
                        moved_places: vec![],
                        active_loans: vec![],
                        storage_erasure: VmStorageErasureWitness::without_source_storage(),
                    },
                },
                VmInstruction::Return { value: 1 },
            ],
        },
        fingerprint: Digest::of_bytes(b"leave-reject-clause-fingerprint"),
    };
    enters_clause.fingerprint = enters_clause.computed_fingerprint();
    assert!(matches!(
        verify_vm(enters_clause),
        Err(VmArtifactError::HandlerTargetReachedByControlFlow { target: 3 })
    ));
}

#[test]
fn verifier_rejects_overlapping_or_loaned_cleanup_slots() {
    let owner = DefKey(Digest::of_bytes(b"leave-cleanup-overlap-owner"));
    let candidate = |cleanup| {
        let mut artifact = CandidateVmArtifact {
            schema: grandiose_stage0::STAGE0_VM_SCHEMA,
            runtime_manifest: None,
            function: VmFunction {
                nominal_copy_descriptors: vec![],
                definition: DefKey(Digest::of_bytes(b"leave-cleanup-overlap")),
                captures: 0,
                parameters: 0,
                registers: vec![VmType::I64, VmType::I64],
                instructions: vec![
                    VmInstruction::ConstI64 { dst: 0, value: 1 },
                    VmInstruction::Leave {
                        brand_owner: owner,
                        brand_label: 0,
                        handler_depth: 0,
                        target: 2,
                        arguments: vec![0],
                        destinations: vec![1],
                        cleanup,
                    },
                    VmInstruction::Return { value: 1 },
                ],
            },
            fingerprint: Digest::of_bytes(b"stale-leave-cleanup-overlap"),
        };
        artifact.fingerprint = artifact.computed_fingerprint();
        artifact
    };
    let overlapping = candidate(VmCleanupProof {
            moved_places: vec![
                VmCleanupPlace {
                    path: 0,
                    binding: 0,
                    root: "pair".into(),
                    fields: vec![]
                },
                VmCleanupPlace {
                    path: 1,
                    binding: 0,
                    root: "pair".into(),
                    fields: vec![0]
                },
            ],
            active_loans: vec![],
            storage_erasure: VmStorageErasureWitness::without_source_storage(),
        });
    let encoded_overlapping = encode_artifact(&overlapping);
    assert_eq!(decode_artifact(&encoded_overlapping).unwrap(), overlapping);
    assert!(matches!(
        verify_vm(overlapping),
        Err(VmArtifactError::MalformedEncoding { .. })
    ));
    assert!(matches!(
        decode_and_verify_artifact(&encoded_overlapping),
        Err(VmArtifactError::MalformedEncoding { .. })
    ));
    assert!(matches!(
        verify_vm(candidate(VmCleanupProof {
            moved_places: vec![VmCleanupPlace {
                path: 0,
                binding: 0,
                root: "pair".into(),
                fields: vec![0]
            }],
            active_loans: vec![VmCleanupLoan {
                owner: Some("loan".into()),
                binding: 0,
                root: "pair".into(),
                fields: vec![],
                unique: false,
            }],
            storage_erasure: VmStorageErasureWitness::without_source_storage(),
        })),
        Err(VmArtifactError::MalformedEncoding { .. })
    ));
    assert!(matches!(
        verify_vm(candidate(VmCleanupProof {
            moved_places: vec![VmCleanupPlace {
                path: 0,
                binding: 7,
                root: "moved-display".into(),
                fields: vec![0],
            }],
            active_loans: vec![VmCleanupLoan {
                owner: Some("loan".into()),
                binding: 7,
                root: "unrelated-display".into(),
                fields: vec![],
                unique: false,
            }],
            storage_erasure: VmStorageErasureWitness::without_source_storage(),
        })),
        Err(VmArtifactError::MalformedEncoding { .. })
    ));
    assert!(
        verify_vm(candidate(VmCleanupProof {
            moved_places: vec![VmCleanupPlace {
                path: 0,
                binding: 7,
                root: "same-display".into(),
                fields: vec![0],
            }],
            active_loans: vec![VmCleanupLoan {
                owner: Some("loan".into()),
                binding: 8,
                root: "same-display".into(),
                fields: vec![],
                unique: false,
            }],
            storage_erasure: VmStorageErasureWitness::without_source_storage(),
        }))
        .is_ok(),
        "presentation text must not create a numeric cleanup overlap"
    );
}

#[test]
fn leave_from_a_handler_clause_abandons_its_suspended_continuation() {
    let effect = DefKey(Digest::of_bytes(b"leave-clause-effect"));
    let owner = DefKey(Digest::of_bytes(b"leave-clause-owner"));
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"leave-clause")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64, VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 42 },
            VmInstruction::InstallHandler {
                effect,
                effect_arguments: vec![],
                operation: 0,
                payload_destinations: vec![],
                resume_type: VmType::I64,
                continuation: VmContinuationPolicy::Consume,
                target: 5,
            },
            VmInstruction::Perform {
                dst: 1,
                effect,
                effect_arguments: vec![],
                operation: 0,
                arguments: vec![],
            },
            VmInstruction::UninstallHandler,
            VmInstruction::Return { value: 1 },
            VmInstruction::Leave {
                brand_owner: owner,
                brand_label: 2,
                handler_depth: 0,
                target: 7,
                arguments: vec![0],
                destinations: vec![3],
                cleanup: VmCleanupProof {
                    moved_places: vec![],
                    active_loans: vec![],
                    storage_erasure: VmStorageErasureWitness::without_source_storage(),
                },
            },
            VmInstruction::Trap,
            VmInstruction::Return { value: 3 },
        ],
    };
    let mut artifact = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: function.clone(),
        fingerprint: Digest::of_bytes(b"leave-clause-artifact"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    assert_eq!(verify_vm(artifact).unwrap().run_i64().unwrap(), 42);

    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: function.definition,
        functions: BTreeMap::from([(function.definition, function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"leave-clause-program"),
    };
    program.fingerprint = program.computed_fingerprint();
    assert_eq!(verify_vm_program(program).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn cleanup_leave_program_artifacts_are_insertion_order_deterministic() {
    let entry = DefKey(Digest::of_bytes(b"deterministic-leave-entry"));
    let helper = DefKey(Digest::of_bytes(b"deterministic-leave-helper"));
    let leave = cleanup_carrying_leave_entry(entry, VmInstruction::ConstI64 { dst: 0, value: 42 });
    let helper = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: helper,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64],
        instructions: vec![
            VmInstruction::ConstI64 { dst: 0, value: 1 },
            VmInstruction::Return { value: 0 },
        ],
    };
    let mut first_functions = BTreeMap::new();
    first_functions.insert(entry, leave.clone());
    first_functions.insert(helper.definition, helper.clone());
    let mut second_functions = BTreeMap::new();
    second_functions.insert(helper.definition, helper);
    second_functions.insert(entry, leave);
    let build = |functions| {
        let mut program = CandidateVmProgram {
            schema: grandiose_stage0::STAGE0_VM_SCHEMA,
            runtime_manifest: None,
            host_capabilities: vec![],
            entry,
            functions,
            callable_environments: BTreeMap::new(),
            fingerprint: Digest::of_bytes(b"deterministic-leave-seed"),
        };
        program.fingerprint = program.computed_fingerprint();
        program
    };
    let first = build(first_functions);
    let second = build(second_functions);
    assert_eq!(first.fingerprint, second.fingerprint);
    assert_eq!(encode_program(&first), encode_program(&second));
    assert_eq!(
        decode_and_verify_program(&encode_program(&first))
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

/// Source storage has an independent lifetime: `StorageLive` makes a slot
/// addressable but does not define a resident value.  The first ordinary
/// definition into that slot must therefore be accepted, while a second
/// ordinary definition remains a forged replacement.
#[test]
fn verifier_and_runtime_distinguish_live_uninitialized_storage_from_double_writes() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"live-uninitialized-storage")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::I64, VmType::I64, VmType::I64],
        instructions: vec![
            VmInstruction::StorageLive {
                binding: 0,
                local: 0,
            },
            VmInstruction::ConstI64 { dst: 1, value: 42 },
            VmInstruction::Copy { dst: 0, src: 1 },
            VmInstruction::Move { dst: 2, src: 0 },
            VmInstruction::StorageDead {
                binding: 0,
                local: 0,
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"live-uninitialized-storage-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let encoded = encode_artifact(&candidate);
    assert_eq!(decode_artifact(&encoded).unwrap(), candidate);
    assert_eq!(
        decode_and_verify_artifact(&encoded)
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );

    let mut forged = candidate;
    forged.function.instructions.insert(
        3,
        VmInstruction::ConstI64 {
            dst: 0,
            value: 7,
        },
    );
    forged.fingerprint = forged.computed_fingerprint();
    assert!(matches!(
        verify_vm(forged),
        Err(VmArtifactError::DoubleWrite { register: 0 })
    ));
}

/// Compiler-created drop flags are explicit state cells, so changing their
/// value is not a generic SSA double write.  This keeps their lifecycle
/// separate from ordinary source-storage initialization.
#[test]
fn verifier_allows_explicit_drop_flag_transitions_without_relaxing_value_writes() {
    let function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(b"drop-flag-transitions")),
        captures: 0,
        parameters: 0,
        registers: vec![VmType::Bool, VmType::I64],
        instructions: vec![
            VmInstruction::SetDropFlag {
                flag: 0,
                value: true,
            },
            VmInstruction::SetDropFlag {
                flag: 0,
                value: false,
            },
            VmInstruction::ConstI64 { dst: 1, value: 42 },
            VmInstruction::Return { value: 1 },
        ],
    };
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function,
        fingerprint: Digest::of_bytes(b"drop-flag-transitions-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    assert_eq!(verify_vm(candidate).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn verifier_rejects_cfg_join_that_revives_dead_source_storage() {
    // The ordinary arm keeps `r1` live, while the other arm ends it.  Before
    // the verifier treated storage liveness as a must fact, the arm processed
    // first made the join look live and a later write revived the dead slot.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"cfg-storage-revival")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::Bool, VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::ConstBool {
                    dst: 0,
                    value: true,
                },
                VmInstruction::StorageLive {
                    binding: 1,
                    local: 1,
                },
                VmInstruction::ConstI64 { dst: 2, value: 42 },
                VmInstruction::BranchBool {
                    condition: 0,
                    then_target: 6,
                    else_target: 4,
                },
                VmInstruction::Jump { target: 9 },
                VmInstruction::Trap,
                VmInstruction::StorageDead {
                    binding: 1,
                    local: 1,
                },
                VmInstruction::Jump { target: 9 },
                VmInstruction::Trap,
                VmInstruction::Copy { dst: 1, src: 2 },
                VmInstruction::Return { value: 1 },
            ],
        },
        fingerprint: Digest::of_bytes(b"cfg-storage-revival-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    let direct = verify_vm(candidate);
    assert!(
        matches!(direct, Err(VmArtifactError::ReadBeforeWrite { register: 1 })),
        "unexpected direct verification result: {direct:?}"
    );
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::ReadBeforeWrite { register: 1 })
    ));
}

#[test]
fn verifier_retains_all_possible_reference_roots_across_cfg_joins() {
    // `r3` is a reference to source storage on one arm and an ordinary SSA
    // value on the other.  The join must retain both possible roots: choosing
    // the first predecessor's root lets the source-storage arm die while its
    // live borrow remains reachable.
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"cfg-reference-origin-join")),
            captures: 0,
            parameters: 0,
            registers: vec![
                VmType::Bool,
                VmType::I64,
                VmType::I64,
                VmType::Reference {
                    unique: false,
                    referent: Box::new(VmType::I64),
                },
                VmType::I64,
            ],
            instructions: vec![
                VmInstruction::StorageLive {
                    binding: 1,
                    local: 1,
                },
                VmInstruction::ConstI64 { dst: 2, value: 42 },
                VmInstruction::Copy { dst: 1, src: 2 },
                VmInstruction::ConstBool {
                    dst: 0,
                    value: true,
                },
                VmInstruction::BranchBool {
                    condition: 0,
                    then_target: 7,
                    else_target: 5,
                },
                VmInstruction::Borrow {
                    dst: 3,
                    src: 2,
                    fields: vec![],
                    unique: false,
                    reborrow: false,
                },
                VmInstruction::Jump { target: 8 },
                VmInstruction::Borrow {
                    dst: 3,
                    src: 1,
                    fields: vec![],
                    unique: false,
                    reborrow: false,
                },
                VmInstruction::Move { dst: 4, src: 1 },
                VmInstruction::StorageDead {
                    binding: 1,
                    local: 1,
                },
                VmInstruction::Return { value: 4 },
            ],
        },
        fingerprint: Digest::of_bytes(b"cfg-reference-origin-join-stale"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let bytes = encode_artifact(&candidate);
    assert!(matches!(
        verify_vm(candidate),
        Err(VmArtifactError::ReadBeforeWrite { register: 1 })
    ));
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::ReadBeforeWrite { register: 1 })
    ));
}

#[test]
fn declared_nonreturn_abi_preserves_bottom_coerced_direct_and_indirect_calls() {
    let terminal = DefKey(Digest::of_bytes(b"declared-nonreturn-terminal"));
    let entry = DefKey(Digest::of_bytes(b"declared-nonreturn-entry"));
    let terminal_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: terminal,
        captures: 0,
        parameters: 0,
        registers: vec![VmType::Unit],
        // The trailing Return is intentionally unreachable. The leading ABI
        // declaration must summarize normal control, not merely scan every
        // serialized instruction for a return-shaped opcode.
        instructions: vec![
            VmInstruction::DeclareResult {
                result: VmType::Unit,
                returns: false,
            },
            VmInstruction::Trap,
            VmInstruction::Return { value: 0 },
        ],
    };
    let entry_function = VmFunction {
        nominal_copy_descriptors: vec![],
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![
            VmType::I64,
            VmType::Callable {
                parameters: vec![],
                result: Box::new(VmType::I64),
                effects: Box::new(VmEffectRow::default()),
            },
            VmType::I64,
        ],
        instructions: vec![
            VmInstruction::DeclareResult {
                result: VmType::I64,
                returns: true,
            },
            // The source `!` callee can be coerced to i64 at both call
            // surfaces. Its sealed `returns: false` ABI proves neither
            // destination is observable on a normal return edge.
            VmInstruction::Call {
                dst: 0,
                callee: terminal,
                arguments: vec![],
            },
            VmInstruction::MakeCallable {
                dst: 1,
                callee: terminal,
                captures: vec![],
                environment: None,
            },
            VmInstruction::CallIndirect {
                dst: 2,
                callee: 1,
                arguments: vec![],
            },
            VmInstruction::Return { value: 2 },
        ],
    };
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: BTreeMap::from([(entry, entry_function), (terminal, terminal_function)]),
        callable_environments: BTreeMap::new(),
        fingerprint: Digest::of_bytes(b"declared-nonreturn-program-stale"),
    };
    program.fingerprint = program.computed_fingerprint();
    let bytes = encode_program(&program);
    assert_eq!(decode_program(&bytes).unwrap(), program);
    assert!(verify_vm_program(program).is_ok());
    assert!(decode_and_verify_program(&bytes).is_ok());
}
