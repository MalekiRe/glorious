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

pub use bytecode::{
    Artifact, BYTES, CHAR, Constant, DROP_HOOK, DecodeError, DropGlue, EXPORTED, F32, F64,
    Function, I8, I16, I32, I64, I128, ISIZE, Instruction, NO_RETURN, NONE32, Primitive, TEXT,
    Type, TypeId, U8, U16, U32, U64, U128, UNIT, USIZE,
};
pub use system_host::{HostLimits, SystemHost};
pub use value::Value;
pub use verify::{VerifiedArtifact, VerifyError, verify};
pub use vm::{Host, HostFault, HostLinkError, RuntimeError, RuntimeFaultCategory, Vm};
