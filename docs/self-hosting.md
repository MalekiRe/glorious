# Stage0 self-hosting status

**Status:** current self-hosting overview  
**Baseline reviewed:** `3fd2e0ddf3c10e2d558ad21190b975500374ed71`  
**Last reconciled:** 2026-08-25

This is the single hand-written status page for the active self-hosting
program. Detailed facts live in machine-readable ledgers and generated maps;
old parity reports do not define current status.

## Current state

The active target is a Glorious implementation of the independent Rust Stage0
compiler under `self-host-stage0/`.

At the reviewed baseline:

- the source mirror contains the 36 modules named by
  `self-host-stage0/module-ledger.toml`;
- every ledger entry is still classified as `scaffolded`;
- the baseline records 68 public Stage0 API symbols and 1,726 Rust test
  functions;
- the semantic test map is an inventory of source tests, not proof that the
  Glorious mirror passes them;
- the port has not demonstrated semantic parity, artifact identity, or
  bootstrap convergence.

Accordingly, the repository must not describe Stage0 as self-hosted yet.

## Canonical evidence

- [`glorious-stage0-self-hosting-plan.md`](glorious-stage0-self-hosting-plan.md)
  — migration order, no-fallback rule, and completion gates.
- [`../self-host-stage0/baseline.toml`](../self-host-stage0/baseline.toml) —
  pinned Rust baseline and inventory counts.
- [`../self-host-stage0/module-ledger.toml`](../self-host-stage0/module-ledger.toml)
  — one status per mirrored module.
- [`self-host-stage0/primitive-boundary.md`](self-host-stage0/primitive-boundary.md)
  — frozen language/runtime/host boundary.
- [`self-hosted-compiler/stage0-semantic-test-map.md`](self-hosted-compiler/stage0-semantic-test-map.md)
  — generated semantic test inventory.
- [`../self-host-stage0/README.md`](../self-host-stage0/README.md) and
  [`../self-host-stage0/src/README.md`](../self-host-stage0/src/README.md) —
  local no-fallback contracts.
- `tooling/check-self-host-stage0-status.py` — validates the ledger and source
  mirror.
- `tooling/check-self-host-stage0-no-fallback.py` — rejects fallback to the Rust
  compiler.

[`self-host-stage0/performance-baseline.md`](self-host-stage0/performance-baseline.md)
is a measured snapshot. It must not be used as a substitute for current
functional status.

## Completion gates

A module should advance beyond `scaffolded` only when its ledger state is
supported by reviewable source and the relevant checks. The overall program is
not complete until it demonstrates, at minimum:

1. complete module and public API coverage;
2. semantic and diagnostic parity against the pinned Rust baseline;
3. deterministic canonical artifact emission;
4. execution through the verified VM boundary without Rust compiler fallback;
5. repeated bootstrap convergence under the declared manifest and limits.

## Historical material

The old `self-host/` compiler, LLVM/Wild native flow, and pre-Stage0 parity
reports describe a different implementation. They are preserved under
[`archive/pre-stage0/`](archive/pre-stage0/) and have no current authority.
