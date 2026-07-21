//! grand — build tool for the Grandiose language.
//!
//! Exposed as a library so sibling tooling (the LSP in `tooling/lsp`) can
//! reuse project discovery, dependency resolution, bundling, and the
//! compiler-owned interface scanner without shelling out to the binary.

pub mod bundle;
pub mod compiler;
pub mod contract;
pub mod lock;
pub mod manifest;
pub mod ops;
pub mod resolve;
pub mod scan;
pub mod target;
pub mod util;
