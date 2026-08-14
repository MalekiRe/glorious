use grandiose_stage0::{
    BodySyntax, CallableId, CandidateVmArtifact, CandidateVmProgram, CoreId, DeclarationScan,
    DefKey, DefinitionIndex, Digest, ElaboratedInterface, EnvironmentBrand, FileKey,
    GenericArgument, InterfaceSet, LabelBrand, LexedFile, LogicalPath, MirBlock, MirBlockId,
    MirCleanupPlan, MirFunction, MirInstruction, MirLocal, MirLocalDecl, MirLowering, MirProgram,
    MirTerminator, PackageKey, PlaceFlow, ScalarType, Type, TypedBody, VmArtifactError, VmCapture,
    VmCaptureEnvironment, VmCaptureMode, VmCleanupLoan, VmCleanupPlace, VmCleanupProof,
    VmContinuationPolicy, VmEffectRow, VmExecutionLimits, VmFunction, VmGenericArgument,
    VmInstruction, VmNominalCopyDescriptor, VmPattern, VmPatternField, VmType,
    decode_and_verify_artifact, decode_and_verify_program, decode_artifact, decode_program,
    emit_vm, emit_vm_program, encode_artifact, encode_program, verify_vm, verify_vm_program,
};
use std::collections::BTreeMap;

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
        10,
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
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![MirInstruction::Perform {
                dst: MirLocal(0),
                effect,
                effect_arguments: vec![GenericArgument::ConstU32Expr(expression.clone())],
                operation: 0,
                arguments: vec![],
            }],
            terminator: MirTerminator::Return { value: MirLocal(0) },
        }],
    };
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
        [VmInstruction::Perform { effect_arguments, .. }, ..]
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
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![MirInstruction::Perform {
                dst: MirLocal(0),
                effect,
                effect_arguments: vec![GenericArgument::ConstU32(1)],
                operation: 0,
                arguments: vec![],
            }],
            terminator: MirTerminator::Return { value: MirLocal(0) },
        }],
    };
    let artifact = emit_vm(&function).expect("const protocol argument has a VM identity");
    assert!(matches!(
        artifact.function.instructions.as_slice(),
        [VmInstruction::Perform { effect: found, effect_arguments, .. }, ..]
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
    assert!(matches!(
        verify_vm(candidate),
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
    let target = brand_owner + 32 + 4;
    let argument_count = target + 4;
    let destination_count = argument_count + 8 + 4;
    let cleanup = destination_count + 8 + 4;
    let moved_root_length = cleanup + 8;
    let moved_fields = moved_root_length + 8 + b"value".len();
    let loan_count = moved_fields + 8 + 4;
    let loan_owner_tag = loan_count + 8;
    let loan_root_length = loan_owner_tag + 1;
    let loan_fields = loan_root_length + 8 + b"loan".len();
    LeaveFixtureOffsets {
        brand_owner,
        target,
        destination_count,
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
                    target: 2,
                    arguments: vec![0],
                    destinations: vec![1],
                    cleanup: VmCleanupProof {
                        moved_places: vec![VmCleanupPlace {
                            root: "value".into(),
                            fields: vec![0],
                        }],
                        active_loans: vec![VmCleanupLoan {
                            owner: None,
                            root: "loan".into(),
                            fields: vec![1],
                            unique: false,
                        }],
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
                target: 3,
                arguments: vec![0],
                destinations: vec![1],
                cleanup: VmCleanupProof {
                    moved_places: vec![VmCleanupPlace {
                        root: "result".into(),
                        fields: vec![0],
                    }],
                    active_loans: vec![VmCleanupLoan {
                        owner: Some("frame".into()),
                        root: "result".into(),
                        fields: vec![1],
                        unique: true,
                    }],
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
                target: 2,
                arguments: vec![],
                destinations: vec![],
                cleanup: VmCleanupProof {
                    moved_places: vec![VmCleanupPlace {
                        root: "loop".into(),
                        fields: vec![0],
                    }],
                    active_loans: vec![],
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
            nominal_copy_descriptors: vec![],
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
            nominal_copy_descriptors: vec![],
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
    assert!(matches!(
        verify_vm(candidate),
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
    let error = verify_vm(candidate).unwrap_err();
    assert!(
        matches!(error, VmArtifactError::HandlerResumeUnavailable),
        "cancellation must invalidate all snapshot aliases before a later handler activates: {error:?}"
    );
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
            nominal_copy_descriptors: vec![],
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
            nominal_copy_descriptors: vec![],
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
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
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
                parameters: vec![],
                instructions: vec![MirInstruction::ConstI64 {
                    dst: MirLocal(1),
                    value: 42,
                }],
                terminator: MirTerminator::Return { value: MirLocal(1) },
            },
            MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::ConstI64 {
                    dst: MirLocal(2),
                    value: 7,
                }],
                terminator: MirTerminator::Return { value: MirLocal(2) },
            },
        ],
    };
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
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
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
                parameters: vec![MirLocal(3)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(3) },
            },
            MirBlock {
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
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
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
                parameters: vec![MirLocal(0)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(0) },
            },
        ],
    };
    let candidate = emit_vm(&mir).unwrap();
    assert_eq!(candidate.function.instructions.len(), 3);
    assert!(matches!(
        candidate.function.instructions.as_slice(),
        [
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
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::ConstI64 {
                    dst: MirLocal(0),
                    value: 42,
                }],
                terminator: MirTerminator::Leave {
                    brand: LabelBrand { owner, label: 9 },
                    target: MirBlockId(1),
                    arguments: vec![MirLocal(0)],
                    cleanup: MirCleanupPlan {
                        moved_places: vec![],
                        active_loans: vec![],
                    },
                },
            },
            MirBlock {
                parameters: vec![MirLocal(1)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(1) },
            },
        ],
    };
    let candidate = emit_vm(&mir).unwrap();
    assert!(matches!(
        candidate.function.instructions.as_slice(),
        [
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
                target: 6,
                arguments: vec![1],
                destinations: vec![3],
                cleanup: VmCleanupProof {
                    moved_places: vec![],
                    active_loans: vec![],
                },
            },
            VmInstruction::ConstI64 { dst: 2, value: 2 },
            VmInstruction::Leave {
                brand_owner: owner,
                brand_label: 0,
                target: 7,
                arguments: vec![2],
                destinations: vec![2],
                cleanup: VmCleanupProof {
                    moved_places: vec![],
                    active_loans: vec![],
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
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
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
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(1) },
            },
            MirBlock {
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
                    target: 3,
                    arguments: vec![0],
                    destinations: vec![1],
                    cleanup: VmCleanupProof {
                        moved_places: vec![VmCleanupPlace {
                            root: "value".into(),
                            fields: vec![0],
                        }],
                        active_loans: vec![],
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
    let artifact = emit_vm(&mir).expect("partial move cleanup emits");
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
                    target: 2,
                    arguments: vec![0],
                    destinations: vec![1],
                    cleanup: VmCleanupProof {
                        moved_places: vec![
                            VmCleanupPlace {
                                root: "x".into(),
                                fields: vec![],
                            },
                            VmCleanupPlace {
                                root: "x".into(),
                                fields: vec![],
                            },
                        ],
                        active_loans: vec![],
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
                    target: 3,
                    arguments: vec![0],
                    destinations: vec![1],
                    cleanup: VmCleanupProof {
                        moved_places: vec![],
                        active_loans: vec![],
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
    assert!(matches!(
        verify_vm(candidate(VmCleanupProof {
            moved_places: vec![
                VmCleanupPlace {
                    root: "pair".into(),
                    fields: vec![]
                },
                VmCleanupPlace {
                    root: "pair".into(),
                    fields: vec![0]
                },
            ],
            active_loans: vec![],
        })),
        Err(VmArtifactError::MalformedEncoding { .. })
    ));
    assert!(matches!(
        verify_vm(candidate(VmCleanupProof {
            moved_places: vec![VmCleanupPlace {
                root: "pair".into(),
                fields: vec![0]
            }],
            active_loans: vec![VmCleanupLoan {
                owner: Some("loan".into()),
                root: "pair".into(),
                fields: vec![],
                unique: false,
            }],
        })),
        Err(VmArtifactError::MalformedEncoding { .. })
    ));
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
                target: 7,
                arguments: vec![0],
                destinations: vec![3],
                cleanup: VmCleanupProof {
                    moved_places: vec![],
                    active_loans: vec![],
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
