//! Portable bytecode container, verifier, and register VM for Grandiose.
//!
//! Bytecode is deliberately a smaller semantic boundary than the source
//! language. In particular it has no source-level boolean, pattern matching,
//! or structured-control instruction.

pub mod arena;
pub mod bytecode;
mod system_host;
pub mod value;
pub mod verify;
pub mod vm;

/// Version of the seed/toolchain identity negotiation protocol. The identity
/// is intentionally derived from the frozen compiler/VM contract and exact G1
/// artifact feature set rather than mutable executable paths or timestamps.
pub const SEED_IDENTITY_VERSION: u32 = 1;
pub const RELEASED_SEED_IDENTITY: &str =
    "grandiose-seed-v1;grc-contract=1;grvm-contract=1;artifact=1.0;features=00000000000000ff";

pub use bytecode::{
    Artifact, BYTES, CHAR, Constant, DROP_HOOK, DecodeError, DropGlue, EXPORTED, F32, F64,
    Function, I8, I16, I32, I64, I128, ISIZE, Instruction, NO_RETURN, NONE32, Primitive, TEXT,
    Type, TypeId, U8, U16, U32, U64, U128, UNIT, USIZE,
};
pub use system_host::{HostLimits, SystemHost};
pub use value::Value;
pub use verify::{LoadError, VerifiedArtifact, VerifyError, load_verified, verify};
pub use vm::{Host, HostFault, HostLinkError, RuntimeError, RuntimeFaultCategory, Vm};

#[cfg(test)]
mod released_seed_tests {
    use super::*;

    #[test]
    fn released_identity_tracks_the_frozen_artifact_feature_contract() {
        assert_eq!(Artifact::SUPPORTED_FEATURES, 0xff);
        assert!(RELEASED_SEED_IDENTITY.ends_with("features=00000000000000ff"));
    }
}
