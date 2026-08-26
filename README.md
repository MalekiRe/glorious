# Glorious

Glorious is an experimental language implementation. The active repository is
centered on a Rust stage-zero compiler, a portable verified bytecode VM, and an
in-progress Glorious implementation of that compiler.

## Active components

- [`crates/grandiose-stage0/`](crates/grandiose-stage0/) — the independent Rust
  stage-zero compiler library and the `grc-stage0` command.
- [`crates/grandiose-vm/`](crates/grandiose-vm/) — the portable verified
  bytecode VM library and the `grvm` command.
- [`self-host-stage0/`](self-host-stage0/) — a 36-module Glorious mirror of the
  Stage0 compiler. It is an active port, not a converged self-hosting compiler.
- [`docs/`](docs/) — current specifications, active plans, proposals, measured
  snapshots, and an explicit archive.

The older `grand`, `grandfmt`, `grand-lsp`, `grc`, LLVM/native-backend, and
pre-Stage0 self-hosting material is retained for historical context only. It is
not part of the active Cargo workspace and must not be used to infer current
support.

## Build and test

```sh
cargo build --workspace
cargo test --workspace
```

The workspace currently contains `grandiose-stage0` and `grandiose-vm`.

## Stage0 command line

Run the Stage0 compiler through Cargo while developing:

```sh
cargo run -p grandiose-stage0 -- check path/to/main.glorious
cargo run -p grandiose-stage0 -- run path/to/main.glorious
cargo run -p grandiose-stage0 -- emit-vm path/to/main.glorious program.gvm
cargo run -p grandiose-stage0 -- verify-vm program.gvm
cargo run -p grandiose-stage0 -- run-vm program.gvm -- arg1 arg2
```

Bootstrap-specific commands are also available:

```sh
cargo run -p grandiose-stage0 -- emit-bootstrap-vm SOURCE PROGRAM MANIFEST
cargo run -p grandiose-stage0 -- verify-bootstrap \
  EARLIER_PROGRAM EARLIER_MANIFEST LATER_PROGRAM LATER_MANIFEST
```

See [`crates/grandiose-stage0/README.md`](crates/grandiose-stage0/README.md)
for the complete option model, including explicit source worlds, runtime
primitive selectors, and capability declarations.

## Documentation

Start with [`docs/README.md`](docs/README.md). It defines which documents are
normative, current implementation contracts, active plans, proposals, measured
snapshots, or historical records. [`docs/documentation-policy.md`](docs/documentation-policy.md)
defines the precedence rules used when documents disagree.

The current self-hosting status is summarized in
[`docs/self-hosting.md`](docs/self-hosting.md). Progress is not inferred from
old reports or design prose; it is tracked by the pinned baseline and ledgers
linked there.

## Project status

Glorious is not yet a stable distribution. The Stage0 compiler and VM are the
current executable baseline, while the self-hosting port and several language
and compiler designs remain incomplete or proposed.
