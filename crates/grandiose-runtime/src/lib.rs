//! Shared machine mechanisms, not standard-library collection implementations.
//!
//! This crate's first slice is host-target raw storage. It does not expose
//! Glorious unsafe syntax, bytecode pointer operations, or native import trust.
//! Those require the independent compiler/verifier and shared-ABI gates in
//! `docs/unsafe-memory-and-native-abi.md`.

#![deny(unsafe_op_in_unsafe_fn)]

pub mod memory;
