# Grandiose Stage0 compiler

**Status:** current implementation contract  
**Owner:** `crates/grandiose-stage0/` code and tests

`grandiose-stage0` is the independent Rust stage-zero compiler. It does not
call, wrap, or share frontend, semantic, MIR, or code-generation code with the
retired pre-Stage0 compiler. The only intended cross-component boundary is the
frozen verified VM artifact contract.

The crate provides the `grc-stage0` binary.

## Commands

```text
grc-stage0 [OPTIONS] check FILE
grc-stage0 [OPTIONS] run FILE
grc-stage0 [OPTIONS] emit-vm SOURCE OUTPUT
grc-stage0 [OPTIONS] emit-bootstrap-vm SOURCE OUTPUT MANIFEST
grc-stage0 [OPTIONS] verify-vm PROGRAM
grc-stage0 [OPTIONS] run-vm PROGRAM [-- GUEST_ARGS...]
grc-stage0 [OPTIONS] verify-bootstrap \
  EARLIER_PROGRAM EARLIER_MANIFEST LATER_PROGRAM LATER_MANIFEST
```

Common options include:

```text
--diagnostics text|json
--root-package PACKAGE
--source PACKAGE LOGICAL_PATH FILE          # repeatable
--capability CAPABILITY                     # repeatable
--runtime-standard-library PACKAGE
--runtime-leaf ROLE MODULE NAME             # repeatable
--runtime-host CAPABILITY SYMBOL MODULE NAME
```

Runtime selectors require `--runtime-standard-library`. Host capabilities are
explicit; compilation and VM execution do not acquire ambient authority from
language source.

During development, invoke the binary with:

```sh
cargo run -p grandiose-stage0 -- check path/to/main.glorious
```

## Correctness boundary

A feature is not complete merely because it parses. It must satisfy the
semantic, diagnostic, determinism, artifact, verifier, and operational
contracts exercised by this crate's tests.

Current implementation behavior is defined by code and tests. Design documents
under `docs/self-hosted-compiler/` are proposals unless the documentation index
explicitly marks them otherwise.
