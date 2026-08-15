//! Deliberately-red artifact-boundary contract for source-storage cleanup.
//!
//! MIR section 2.2 makes source storage a lifecycle rather than an always-live
//! register, and section 4.3 requires a concrete `EndBorrow`, destruction,
//! drop-flag, and `StorageDead` sequence on a lexical exit.  The compact VM
//! artifact is allowed to erase that sequence only after it carries a witness
//! which the artifact verifier can check.  This test deliberately constructs
//! the hostile, already-compact artifact boundary: no frontend or MIR helper
//! can accidentally make the proof appear by convention.

use grandiose_stage0::{
    decode_and_verify_artifact, decode_artifact, encode_artifact, CandidateVmArtifact, DefKey,
    Digest, VmCleanupProof, VmFunction, VmInstruction, VmStorageErasureAction,
    VmStorageErasureStorage, VmStorageErasureWitness, VmType, STAGE0_VM_SCHEMA,
};

fn compact_exit_without_storage_witness() -> CandidateVmArtifact {
    let mut artifact = CandidateVmArtifact {
        schema: STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"storage-erasure-no-witness")),
            captures: 0,
            parameters: 0,
            // Register zero represents a newly initialized inner lexical
            // source owner. Register one is the protected label payload. The
            // compact encoding has no way to state either distinction.
            registers: vec![VmType::I64, VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 10 },
                VmInstruction::ConstI64 { dst: 1, value: 42 },
                VmInstruction::Leave {
                    brand_owner: DefKey(Digest::of_bytes(b"storage-erasure-label")),
                    brand_label: 0,
                    handler_depth: 0,
                    target: 3,
                    arguments: vec![1],
                    destinations: vec![2],
                    // Canonical moved-path/loan facts are insufficient: they
                    // neither identify the source owner nor prove the
                    // required lifecycle/action sequence before the exit.
                    cleanup: VmCleanupProof {
                        moved_places: vec![],
                        active_loans: vec![],
                        storage_erasure: VmStorageErasureWitness::Missing,
                    },
                },
                VmInstruction::Return { value: 2 },
            ],
        },
        fingerprint: Digest::of_bytes(b"stale-storage-erasure-no-witness"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    artifact
}

/// The eventual artifact witness must make this hostile compact exit fail
/// closed.  Passing requires all three properties at the trust boundary:
/// canonical encoding, lossless decoding, and verifier rejection when no
/// proof relates the compact registers to the validated source-storage
/// lifecycle/drop-flag/cleanup sequence.
#[test]
fn verifier_rejects_compact_exit_without_source_storage_erasure_witness() {
    let artifact = compact_exit_without_storage_witness();
    let encoded = encode_artifact(&artifact);

    // The present wire format does round-trip the only facts it knows about.
    // Keep that assertion so a future implementation cannot satisfy this test
    // by making the artifact undecodable rather than by adding a checked
    // erasure witness.
    assert_eq!(decode_artifact(&encoded).unwrap(), artifact);

    assert!(
        decode_and_verify_artifact(&encoded).is_err(),
        "the verifier accepted an exit which has no source-storage lifecycle, \
         drop-flag, or ordered cleanup-erasure witness"
    );
}

fn witnessed_storage_exit() -> CandidateVmArtifact {
    let mut artifact = CandidateVmArtifact {
        schema: STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"storage-erasure-witnessed")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::ConstI64 { dst: 0, value: 42 },
                VmInstruction::Leave {
                    brand_owner: DefKey(Digest::of_bytes(b"storage-erasure-witnessed-label")),
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
                                storage: 0,
                                binding: 0,
                                value_register: 0,
                                initialized: true,
                                drop_flag: Some(0),
                            }],
                            actions: vec![
                                VmStorageErasureAction::EndBorrow { storage: 0 },
                                VmStorageErasureAction::Protect {
                                    storage: 0,
                                    register: 0,
                                },
                                VmStorageErasureAction::SetDropFlag {
                                    drop_flag: 0,
                                    initialized: false,
                                },
                                VmStorageErasureAction::StorageDead { storage: 0 },
                            ],
                            protected_registers: vec![0],
                        },
                    },
                },
                VmInstruction::Return { value: 1 },
            ],
        },
        fingerprint: Digest::of_bytes(b"stale-storage-erasure-witnessed"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    artifact
}

#[test]
fn source_storage_erasure_witness_round_trips_and_malformed_actions_fail_decode() {
    let artifact = witnessed_storage_exit();
    let bytes = encode_artifact(&artifact);
    assert_eq!(decode_artifact(&bytes).unwrap(), artifact);
    assert!(decode_and_verify_artifact(&bytes).is_ok());

    // This fixture's final payload is its protected-register list (12 bytes)
    // followed by `Return` (5 bytes).  The preceding action stream is fixed:
    // EndBorrow (5), Protect (9), SetDropFlag (6), StorageDead (5). Mutating
    // the first action tag therefore exercises decoder rejection before the
    // artifact fingerprint is consulted.
    let mut malformed = bytes;
    let first_action_tag = malformed.len() - 5 - 12 - (5 + 9 + 6 + 5);
    malformed[first_action_tag] = 9;
    assert!(decode_artifact(&malformed).is_err());
}

#[test]
fn verifier_rejects_storage_dead_before_witness_disarm() {
    let mut artifact = witnessed_storage_exit();
    let VmInstruction::Leave { cleanup, .. } = &mut artifact.function.instructions[1] else {
        panic!("fixture must begin with witnessed cleanup");
    };
    let VmStorageErasureWitness::Verified { actions, .. } = &mut cleanup.storage_erasure else {
        panic!("fixture must carry a verified storage witness");
    };
    *actions = vec![VmStorageErasureAction::StorageDead { storage: 0 }];
    artifact.fingerprint = artifact.computed_fingerprint();
    let bytes = encode_artifact(&artifact);
    assert!(decode_artifact(&bytes).is_ok());
    assert!(decode_and_verify_artifact(&bytes).is_err());
}

#[test]
fn verifier_rejects_malformed_storage_witness_state_machine_actions() {
    let cases = vec![
        vec![
            VmStorageErasureAction::EndBorrow { storage: 0 },
            VmStorageErasureAction::EndBorrow { storage: 0 },
            VmStorageErasureAction::Protect {
                storage: 0,
                register: 0,
            },
            VmStorageErasureAction::SetDropFlag {
                drop_flag: 0,
                initialized: false,
            },
            VmStorageErasureAction::StorageDead { storage: 0 },
        ],
        vec![
            VmStorageErasureAction::EndBorrow { storage: 0 },
            VmStorageErasureAction::Protect {
                storage: 0,
                register: 1,
            },
            VmStorageErasureAction::SetDropFlag {
                drop_flag: 0,
                initialized: false,
            },
            VmStorageErasureAction::StorageDead { storage: 0 },
        ],
        vec![
            VmStorageErasureAction::EndBorrow { storage: 0 },
            VmStorageErasureAction::Protect {
                storage: 0,
                register: 0,
            },
            VmStorageErasureAction::SetDropFlag {
                drop_flag: 0,
                initialized: true,
            },
            VmStorageErasureAction::StorageDead { storage: 0 },
        ],
        vec![
            VmStorageErasureAction::EndBorrow { storage: 0 },
            VmStorageErasureAction::Protect {
                storage: 0,
                register: 0,
            },
            VmStorageErasureAction::SetDropFlag {
                drop_flag: 0,
                initialized: false,
            },
            VmStorageErasureAction::StorageDead { storage: 0 },
            VmStorageErasureAction::StorageDead { storage: 0 },
        ],
    ];
    for actions in cases {
        let mut artifact = witnessed_storage_exit();
        let VmInstruction::Leave { cleanup, .. } = &mut artifact.function.instructions[1] else {
            panic!("fixture must retain its leave instruction");
        };
        let VmStorageErasureWitness::Verified {
            actions: witness_actions,
            ..
        } = &mut cleanup.storage_erasure
        else {
            panic!("fixture must carry a verified storage witness");
        };
        *witness_actions = actions;
        artifact.fingerprint = artifact.computed_fingerprint();
        assert!(decode_and_verify_artifact(&encode_artifact(&artifact)).is_err());
    }
}

#[test]
fn verifier_rejects_duplicate_storage_binding_witness_identity() {
    let mut artifact = witnessed_storage_exit();
    let VmInstruction::Leave { cleanup, .. } = &mut artifact.function.instructions[1] else {
        panic!("fixture must retain its leave instruction");
    };
    let VmStorageErasureWitness::Verified { storages, .. } = &mut cleanup.storage_erasure
    else {
        panic!("fixture must carry a verified storage witness");
    };
    let mut duplicate = storages[0].clone();
    duplicate.storage = 1;
    storages.push(duplicate);
    artifact.fingerprint = artifact.computed_fingerprint();
    assert!(decode_and_verify_artifact(&encode_artifact(&artifact)).is_err());
}
