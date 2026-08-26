# Current repository architecture

**Status:** current implementation overview  
**Baseline reviewed:** `3fd2e0ddf3c10e2d558ad21190b975500374ed71`

This document describes the active repository, not the retired pre-Stage0
compiler architecture.

## Active Rust workspace

The root Cargo workspace contains two crates:

- `grandiose-stage0` — compiler library plus the `grc-stage0` host adapter.
- `grandiose-vm` — portable verified bytecode VM plus the `grvm` binary.

The Stage0 command constructs an immutable compilation request from explicit
package/logical-path/source inputs. A successful build yields a verified VM
artifact. Source execution and artifact execution both cross the decode and
verification boundary before running with an explicit host.

```text
host files and CLI options
          |
          v
CompilationRequest
          |
          v
StageZeroCompiler
          |
          v
verified GVM1 artifact
          |
          v
Grandiose VM + explicit host capabilities
```

The bytecode format and verifier boundary are documented in
[`bytecode.md`](bytecode.md) and exercised by VM tests and checked fixtures.

## Self-hosting tree

`self-host-stage0/` is an in-progress Glorious mirror of the Rust Stage0
compiler. It is governed by a pinned baseline, a 36-module ledger, an explicit
primitive boundary, and no-fallback checks. It is not yet a converged
self-hosting compiler. See [`self-hosting.md`](self-hosting.md).

## Language design versus implementation

The branded-environment core and standard-library documents are normative
language-design inputs. Frontend, MIR, and snowflake compiler documents are
proposals. Neither category proves current implementation coverage; code,
tests, fixtures, and ledgers provide that evidence.

## Retired components

The following components remain in the repository only for historical or
migration context and are outside the active compiler workspace:

- the old `grand` package/CLI;
- `grandfmt`;
- `grand-lsp`;
- the old `grc` command and its server/tooling protocol;
- the removed `crates/grandiose` compiler;
- the old `self-host/` compiler;
- the LLVM/Wild native self-hosting workflow.

Historical architecture, backend, tooling, and parity documents are preserved
under [`archive/pre-stage0/`](archive/pre-stage0/).
