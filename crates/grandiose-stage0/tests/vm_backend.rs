use grandiose_stage0::{
    BodySyntax, CandidateVmArtifact, CandidateVmProgram, CoreId, DeclarationScan, DefKey,
    DefinitionIndex, Digest, ElaboratedInterface, FileKey, InterfaceSet, LexedFile, LogicalPath,
    MirBlock, MirBlockId, MirFunction, MirInstruction, MirLocal, MirLocalDecl, MirLowering,
    MirProgram, MirTerminator, PackageKey, PlaceFlow, ScalarType, Type, TypedBody, VmArtifactError,
    VmFunction, VmInstruction, VmPattern, VmType, decode_and_verify_artifact,
    decode_and_verify_program, decode_artifact, decode_program, emit_vm, emit_vm_program,
    encode_artifact, encode_program, verify_vm, verify_vm_program,
};
use std::collections::BTreeMap;

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
            } if *effect == expected_effect && effect_arguments == &[VmType::I64] && arguments.is_empty()
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
fn verified_vm_reports_unhandled_effects_without_synthesizing_a_handler() {
    let effect = DefKey(Digest::of_bytes(b"Console"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            definition: DefKey(Digest::of_bytes(b"effect-test")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64],
            instructions: vec![
                VmInstruction::Perform {
                    dst: 0,
                    effect,
                    effect_arguments: vec![VmType::I64],
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
        }) if actual == effect && effect_arguments == vec![VmType::I64]
    ));
}

#[test]
fn verified_vm_executes_a_deep_one_shot_handler_frame() {
    let effect = DefKey(Digest::of_bytes(b"Ask"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
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
    assert_eq!(verify_vm(candidate).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn resumed_handler_frame_reinstalls_for_the_next_matching_operation() {
    let effect = DefKey(Digest::of_bytes(b"Ask-deep"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
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
fn declined_handler_pattern_forwards_the_suspended_operation_to_an_outer_frame() {
    let effect = DefKey(Digest::of_bytes(b"Console-decline"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
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
                    target: 12,
                },
                VmInstruction::InstallHandler {
                    effect,
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![2],
                    resume_type: VmType::I64,
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
    assert_eq!(verify_vm(candidate).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn cancelled_handler_continuation_abandons_its_snapshot_and_returns_clause_value() {
    let effect = DefKey(Digest::of_bytes(b"Ask-cancel"));
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
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
fn verifier_allows_checked_store_reinitialization_but_rejects_type_confusion() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
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
fn verifier_rejects_type_confused_constants_before_execution() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
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
fn verifier_rejects_candidates_with_stale_schema_or_fingerprint() {
    let candidate = CandidateVmArtifact {
        schema: 1,
        runtime_manifest: None,
        function: VmFunction {
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
        definition: entry,
        captures: 0,
        parameters: 0,
        registers: vec![
            VmType::Callable {
                parameters: vec![],
                result: Box::new(VmType::I64),
            },
            VmType::I64,
        ],
        instructions: vec![
            VmInstruction::MakeCallable {
                dst: 0,
                callee: closure,
                captures: vec![],
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
        entry,
        functions: BTreeMap::from([(closure, closure_function), (entry, entry_function)]),
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
fn callable_type_decoder_limits_recursive_hostile_encodings() {
    let mut ty = VmType::I64;
    for _ in 0..130 {
        ty = VmType::Callable {
            parameters: vec![],
            result: Box::new(ty),
        };
    }
    let candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
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
            limit: 128,
        })
    ));
}

#[test]
fn vm_executes_verified_multiblock_mir_boolean_control_flow() {
    let i64_ty = Type::Scalar(ScalarType::I64);
    let mir = MirFunction {
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
fn verifier_rejects_branch_targets_outside_the_instruction_stream() {
    let mut candidate = CandidateVmArtifact {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
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
fn vm_emits_and_executes_the_checked_mir_unreachable_terminal_as_a_trap() {
    let i64_ty = Type::Scalar(ScalarType::I64);
    let local = |ty| MirLocalDecl {
        ty,
        source: CoreId(u32::MAX),
    };
    let mir = MirFunction {
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
        entry,
        functions: BTreeMap::from([(generic, generic_function), (entry, entry_function)]),
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
        entry,
        functions: BTreeMap::from([(generic, generic_function), (entry, entry_function)]),
        fingerprint: Digest::of_bytes(b"generic-identity-program"),
    };
    program.fingerprint = program.computed_fingerprint();
    let bytes = encode_program(&program);
    assert_eq!(decode_program(&bytes).unwrap(), program);
    assert_eq!(verify_vm_program(program).unwrap().run_i64().unwrap(), 42);
}
