//! Hostile artifact tests for the executable source-storage identity channel.

use grandiose_stage0::{
    CandidateVmArtifact, DefKey, Digest, STAGE0_VM_SCHEMA, VmArtifactError, VmFunction,
    VmInstruction, VmType, decode_and_verify_artifact, decode_artifact, encode_artifact,
};

fn swapped_storage_dead_bindings() -> CandidateVmArtifact {
    let mut artifact = CandidateVmArtifact {
        schema: STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            safety: grandiose_stage0::Safety::Safe,
            unsafe_execution: false,
            nominal_copy_descriptors: vec![],
            definition: DefKey(Digest::of_bytes(b"vm-storage-binding-swap")),
            captures: 0,
            parameters: 0,
            registers: vec![VmType::I64, VmType::I64, VmType::I64],
            instructions: vec![
                VmInstruction::StorageLive {
                    binding: 17,
                    local: 0,
                },
                VmInstruction::StorageLive {
                    binding: 23,
                    local: 1,
                },
                // Both locals are independently live and uninitialized, so
                // register-state checking alone accepts these transitions.
                // The binding identities are deliberately crossed.
                VmInstruction::StorageDead {
                    binding: 17,
                    local: 1,
                },
                VmInstruction::StorageDead {
                    binding: 23,
                    local: 0,
                },
                VmInstruction::ConstI64 { dst: 2, value: 42 },
                VmInstruction::Return { value: 2 },
            ],
        },
        fingerprint: Digest::of_bytes(b"vm-storage-binding-swap-stale"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    artifact
}

#[test]
fn verifier_rejects_storage_dead_with_a_forged_binding_local_pair() {
    let artifact = swapped_storage_dead_bindings();
    let bytes = encode_artifact(&artifact);
    assert_eq!(decode_artifact(&bytes).unwrap(), artifact);
    assert!(matches!(
        decode_and_verify_artifact(&bytes),
        Err(VmArtifactError::InvalidSourceStorageIdentity {
            binding: 17,
            local: 1,
            ..
        })
    ));
}
