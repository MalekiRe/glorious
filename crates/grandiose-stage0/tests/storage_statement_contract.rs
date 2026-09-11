//! Regression contracts for the executable storage-statement slice.
//!
//! `source_storage_cleanup.rs` already proves the frozen lexical arena and
//! cleanup witness cannot be forged. These fixtures cover the executable
//! *program-point* half of MIR design sections 2.2, 3.3, 4.3, and 5.3: an
//! addressable local may not become live by an incidental register write, a
//! replacement needs a prior zero-use destroy, and an all-false drop-flag arm
//! must erase exactly to the skip-cleanup VM path.

use grandiose_stage0::{
    decode_and_verify_artifact, decode_artifact, emit_vm, encode_artifact, CandidateVmArtifact,
    CoreId, DefKey, Digest, MirBlock, MirBlockId, MirControlTables, MirFunction, MirInstruction,
    MirLocal, MirLocalDecl, MirScopeId, MirTerminator, ScalarType, Type, VmCleanupProof,
    VmFunction, VmInstruction, VmStorageErasureAction, VmStorageErasureStorage,
    VmStorageErasureWitness, VmType, STAGE0_VM_SCHEMA,
};

fn local(ty: Type) -> MirLocalDecl {
    MirLocalDecl {
        ty,
        source: CoreId(u32::MAX),
    }
}

fn forged_function(
    name: &'static [u8],
    instructions: Vec<MirInstruction>,
    result: MirLocal,
) -> MirFunction {
    MirFunction {
        safety: grandiose_stage0::Safety::Safe,
        unsafe_execution: false,
        nominal_copy_descriptors: vec![],
        definition: DefKey(Digest::of_bytes(name)),
        captures: 0,
        parameters: vec![],
        locals: vec![
            local(Type::Scalar(ScalarType::I64)),
            local(Type::Scalar(ScalarType::I64)),
            local(Type::Scalar(ScalarType::I64)),
        ],
        result: Type::Scalar(ScalarType::I64),
        control: MirControlTables::default(),
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            scope: MirScopeId::ROOT,
            parameters: vec![],
            instructions,
            terminator: MirTerminator::Return { value: result },
        }],
    }
}

/// Sections 2.2 and 3.3 require the transition
/// `Dead -> StorageLive -> Uninitialized -> Store -> Initialized`; neither a
/// bare `Store` nor a general register write is `StorageLive`.  A replacement
/// is independently legal only after compiler-mediated `Destroy` with
/// `Use<[0,0]>` proof.  A transfer makes the source uninitialized, so a later
/// read is use-after-dead even if the VM happens to retain a register number.
///
/// Raw and frozen MIR validate these executable storage statements and their
/// ownership state at each program point.
#[test]
fn mir_storage_statement_matrix_rejects_implicit_liveness_replacement_and_reuse() {
    let cases = [
        (
            "store before StorageLive",
            forged_function(
                b"storage-statement-store-before-live",
                vec![
                    MirInstruction::ConstI64 {
                        dst: MirLocal(1),
                        value: 1,
                    },
                    MirInstruction::Store {
                        dst: MirLocal(0),
                        src: MirLocal(1),
                    },
                ],
                MirLocal(0),
            ),
        ),
        (
            "replacement without prior zero-use Destroy",
            forged_function(
                b"storage-statement-replacement-without-destroy",
                vec![
                    MirInstruction::ConstI64 {
                        dst: MirLocal(0),
                        value: 1,
                    },
                    MirInstruction::ConstI64 {
                        dst: MirLocal(1),
                        value: 2,
                    },
                    MirInstruction::Store {
                        dst: MirLocal(0),
                        src: MirLocal(1),
                    },
                ],
                MirLocal(0),
            ),
        ),
        (
            "read after Move made the source uninitialized",
            forged_function(
                b"storage-statement-read-after-move",
                vec![
                    MirInstruction::ConstI64 {
                        dst: MirLocal(0),
                        value: 1,
                    },
                    MirInstruction::Move {
                        dst: MirLocal(1),
                        src: MirLocal(0),
                    },
                    MirInstruction::Copy {
                        dst: MirLocal(2),
                        src: MirLocal(0),
                    },
                ],
                MirLocal(2),
            ),
        ),
    ];

    let accepted = cases
        .iter()
        .filter_map(|(name, function)| {
            (function.validate().is_ok() || emit_vm(function).is_ok()).then_some(*name)
        })
        .collect::<Vec<_>>();
    assert!(
        accepted.is_empty(),
        "MIR must reject every illegal storage transition before VM lowering; accepted: {accepted:?}"
    );
}

fn all_false_drop_flag_exit() -> CandidateVmArtifact {
    let mut artifact = CandidateVmArtifact {
        schema: STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            safety: grandiose_stage0::Safety::Safe,
            unsafe_execution: false,
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"storage-statement-all-false-erasure")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 7 },
                VmInstruction::Leave {
                    brand_owner: DefKey(Digest::of_bytes(b"storage-statement-all-false-label")),
                    brand_label: 0,
                    retained_handlers: vec![], exited_handlers: vec![],
                    target: 2,
                    arguments: vec![],
                    destinations: vec![],
                    cleanup: VmCleanupProof {
                        moved_places: vec![],
                        active_loans: vec![],
                        storage_erasure: VmStorageErasureWitness::Verified {
                            storages: vec![VmStorageErasureStorage {
                                storage: 0,
                                binding: 0,
                                value_register: 0,
                                initialized: false,
                                drop_flag: Some(0),
                            }],
                            // This is the `DestroyIf` false arm: it must not
                            // synthesize a destroy or a flag clear for an
                            // owner which was never initialized.
                            actions: vec![VmStorageErasureAction::StorageDead { storage: 0 }],
                            protected_registers: vec![],
                        },
                    },
                },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"stale-storage-statement-all-false-erasure"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    artifact
}

/// Sections 4.3 and 5.3 permit a conditionally initialized owner to take the
/// false cleanup arm: no `Destroy` runs, the slot dies, and no protected value
/// is touched.  Section 10.4 permits bytecode erasure only when this exact
/// branch is carried by a checked witness.  The true arm and malformed-witness
/// cases are covered in `source_storage_cleanup.rs` and
/// `vm_storage_erasure.rs`; this is the missing semantic counterpart.
#[test]
fn vm_erasure_preserves_the_all_false_drop_flag_cleanup_arm() {
    let artifact = all_false_drop_flag_exit();
    let bytes = encode_artifact(&artifact);
    assert_eq!(decode_artifact(&bytes).unwrap(), artifact);
    assert!(
        decode_and_verify_artifact(&bytes).is_ok(),
        "a verified all-false drop-flag cleanup must erase to StorageDead without Destroy"
    );
}
