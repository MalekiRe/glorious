# Glorious

Glorious is an experimental systems language built around quantitative
ownership, algebraic effects, source-defined control flow, and portable verified
bytecode. It aims to make resource usage and non-local control explicit without
giving up higher-order functions, Rust-style borrowing, traits, or generics.

Grandiose is the compiler and toolchain implementation in this repository.

The project is pre-alpha. There is no backward-compatibility requirement for
source, standard-library APIs, compiler interfaces, ABI, or G1 artifacts. These
unfinished components evolve together; old artifacts may need to be rebuilt.
The independently implemented Stage0 compiler and verified VM are the active
Rust toolchain. The former package tool, formatter, and language server are
retained only as explicitly disabled legacy code while they are redesigned.

The Grandiose compiler is being implemented in [compiler/](compiler/)
under the [GSC-2 specification](GSC-2-glorious-incremental-self-hosted-compiler-spec.md).
Its storage, revision, and query machinery precedes the semantic port. The old
`self-host-stage0` implementation and its build scripts have been retired;
their historical coverage does not count toward GSC-2.

The chosen [execution model](docs/unsafe-memory-and-native-abi.md) specializes the
compiler and source libraries, including `Vec<T>` and unsafe memory operations,
into bytecode over host-compatible storage. **Self-hosting comes before the
Grandiose LLVM backend**; native-precompiled std and native generic specialization
are not prerequisites. Shared native/VM objects target zero marshalling. The
unsafe-enabled profile is not a memory sandbox. Current distribution ships source
for local compilation; independent admission of untrusted distributed bytecode
and trusted-native safe exports are deferred. Source raw-pointer types, explicit
unsafe scopes, and unsafe callable/trait contracts now propagate through the
compiler; pointer execution and general zero-marshalling interop are not
available yet. The current bytecode format rejects unsafe requirements. See the
[delivery gates](compiler/spec/unsafe-memory-progress.md).

## Normative specifications

- [Glorious language specification](glorious-language-specification.md)
- [Glorious standard-library specification](glorious-standard-library-specification.md)
- [Grandiose self-hosted compiler specification](GSC-2-glorious-incremental-self-hosted-compiler-spec.md)
- [Grandiose bytecode specification](docs/bytecode.md)

## What makes the language different?

### Values describe how many times they may be used

Glorious exposes unrestricted, affine, and exact-linear ownership through `Use`.
The selected principal class is part of the type's evidence:

```rust
struct Ticket { serial: i64 }

impl Use<[1,1]> for Ticket {}

fn redeem(ticket: Ticket) -> i64 {
    let Ticket { serial } = move ticket;
    serial
}
```

`Use<[1,1]>` means that a `Ticket` must be transferred or deconstructed exactly
once. `Use<[0,1]>` describes an affine value and `Use<[0,*]>` an unrestricted,
duplicable value. Grandiose tracks path-sensitive use intervals internally through
branches, loops, calls, closures, partial moves, cancellation, and continuation replay.

Cleanup is not a loophole: destroying a value contributes zero uses and cannot
satisfy a positive lower bound.

### Private representation controls who may finish consuming a value

There is no universal `destroy` intrinsic for escaping an ownership obligation.
A must-move value must be transferred, or its representation must eventually be
deconstructed by code with authority to see it. Private fields make that
authority explicit:

```rust
struct Secret {
    private payload: Bytes,
}
```

Code outside the defining module can move a `Secret`, but cannot destructure its
private field. It must pass the value to an authorized function that can finish
consuming it. This makes opaque resource APIs and must-move types work together
naturally.

### Effects and resumptions are part of ordinary typed control flow

Effects are nominal and effect rows are checked. Operations state how many times
their continuation may be resumed:

```rust
effect Ask {
    ask() -> i64
}

fn answer() -> i64 {
    handle Ask::ask() {
        Ask::ask(continuation) => continuation(42)
    }
}
```

Glorious supports terminal effects, one-shot and finite multi-shot resumptions,
deep handlers, explicit cancellation, nested suspension, effectful closures,
and reference-bearing payloads. Resumption quantities participate in the same
ownership arithmetic as ordinary values, so replaying a continuation also
accounts for every captured owner.

### Familiar control is library code

The compiler understands structural calls, labels, effects, handlers, and
patterns. It does not give special semantic status to names such as `if`,
`match`, `loop`, `return`, `yield`, `await`, or operators such as `+` and `==`.
Those are ordinary declarations, fixities, traits, and effects supplied by the
standard library.

This keeps the trusted language core small and lets control abstractions compose
with effects, ownership, and user-defined operators instead of living in a
separate compiler-only world.

### Rust-shaped static reasoning, explicit lowered invariants

The static system includes shared and unique references, non-lexical lifetime
reasoning, reborrowing, variance, traits, associated types and effect rows,
GATs, higher-ranked bounds, const generics, closures, and partial moves.
Compilation lowers accepted programs into ownership-aware CFG MIR with explicit
cleanup, cancellation, handler, and resumption edges.

The final `.grbc` artifact is decoded and verified before the VM executes it.
Bytecode verification checks register types, ownership modes, references,
cleanup, and control-flow invariants independently of the source compiler.

## Toolchain overview

- `grc-stage0` compiles `.glorious` source into verified G1 bytecode.
- `grvm` verifies and executes `.grbc` artifacts.
- `grand`, `grandfmt`, and `grand-lsp` are disabled legacy implementations;
  they will be restructured against the Stage0 architecture.
- `editors/vscode` contains the VS Code extension and TextMate grammar.

The source suffix is `.glorious`.

## Install from this checkout

Install a stable Rust toolchain with Cargo first. Then run:

```sh
cargo install --path crates/grandiose-stage0 --bin grc-stage0
cargo install --path crates/grandiose-vm --bin grvm
```

Cargo normally installs these commands into `~/.cargo/bin`; ensure that
directory is on `PATH`.

To build without installing:

```sh
cargo build --release --workspace --bins

export GRAND_COMPILER="$PWD/target/release/grc-stage0"
export GRAND_VM="$PWD/target/release/grvm"
export PATH="$PWD/target/release:$PATH"
```

`GRAND_COMPILER` and `GRAND_VM` select explicit Stage0 compiler and VM builds.

System `git` is required for Git dependencies.

## Create and run a project

```sh
grand new hello
cd hello

grand check
grand run
grand build -O2
grand fmt
grand test
```

`grand new hello` creates `./hello`. To choose a different destination:

```sh
grand new hello --path ./projects/my-hello
```

Use `grand init` to scaffold the current directory. A new executable contains:

```text
hello/
├── grandiose.toml
└── src/
    └── main.glorious
```

Build artifacts go under `target/grand/`; the VM artifact for the example is
`target/grand/hello.grbc`.

## Packages, workspaces, and modules

An executable manifest names its entry point:

```toml
[project]
name = "hello"
version = "0.1.0"
entry = "src/main.glorious"

[runtime]
# Exact host capabilities granted to `grand run` and executable tests.
# Omit this table for a sandbox with no host access.
capabilities = ["process.args", "diagnostic"]
```

A library package omits `entry` and may set `sources = ["src"]`. A workspace
lists member directories:

```toml
[workspace]
members = ["app", "libs/parser"]
```

Select a member by package name or directory:

```sh
grand -p app check
grand -p libs/parser test
```

The source module layout is a hybrid of Rust's inline and directory module
styles. From `src/main.glorious`:

```rust
mod parser;
use crate::parser::parse;
```

the external module lives at:

```text
src/parser/parser.glorious
```

Inline modules advance the same logical directory. For example,
`mod syntax { pub mod tokens; }` resolves the external module at
`src/syntax/tokens/tokens.glorious`. Named module items are private by default;
use `pub` to export them.

## Everyday `grand` commands

```text
grand new <name> [--path <dir>]  create a package
grand init                       create a package in the current directory
grand check                      type-check and verify without an artifact
grand build [-O 0..3]            compile the package (default: O2)
grand run [-O 0..3] -- <args>    compile at O2 by default and execute in grvm
grand test [filter]              run source and compile-fail tests
grand fmt [--check] [paths...]   format sources, or check formatting
grand fmt --stdin                format standard input to standard output
grand fix                        apply machine-applicable diagnostics
grand doc [--open]               write API docs to target/grand/doc
grand clean [--cache]            remove outputs and optionally shared cache
grand lsp                        run grand-lsp over stdio
```

`grand test` executes `tests/**/*.glorious` and treats exit status zero as a
pass. Files under `tests/compile-fail/` are compared with matching `.stderr`
goldens; update them deliberately with `grand test --bless`.

`grand build` always emits verified G1 bytecode, and `grand run` always executes
it through `grvm`. O0 is retained for raw lowering and bytecode-verification
work; normal builds start at O2:

```sh
grand build -O3
grand run -- first-argument second-argument
```

Runtime authority is declared explicitly in `[runtime].capabilities`. It is
empty by default, and every entry becomes one exact `grvm --allow` grant; there
is no prefix or wildcard matching. The standard host capabilities are
`process.args`, `fs.read`, `fs.write`, and `diagnostic`.

Lint levels can be stored in the manifest's `[lints]` table or overridden with
`-A/--allow`, `-W/--warn`, and `-D/--deny` using a diagnostic code or
`warnings`.

## Dependencies and reproducible builds

```sh
grand add util --path ../util
grand add parser --github user/repository --tag v1.0.0
grand add codec --git https://example.com/codec.git --rev <commit>

grand lock
grand update parser
grand vendor
```

Git dependencies require exactly one of `--tag`, `--rev`, or `--branch`.
Commit `grandiose.lock` for reproducible resolution. Set `GRAND_LOCKED=1` to
reject lockfile changes and `GRAND_OFFLINE=1` to forbid network access.
`grand vendor` copies resolved Git dependencies into `./vendor` for offline
builds.

## Use the compiler and VM directly

`grand` is the recommended interface, but the lower-level tools are useful for
compiler development and automation:

```sh
grc -O2 --emit bytecode src/main.glorious -o app.grbc
grc --check src/main.glorious
grc --phase resolve src/main.glorious
grc --emit mir src/main.glorious -o app.mir
grc --diagnostics json src/main.glorious
grc --dependency util=../util src/main.glorious

grvm verify app.grbc
grvm run app.grbc -- argument
```

`grc --phase` supports `lex`, `scan`, `resolve`, and `check`. Its structured
emit surface includes bytecode, MIR, Core, provisional typing, and interface
JSON. Run `grc --help` or `grc --capabilities` for the machine contract.

The VM runner also supports supervision and capability options such as
`--time-limit`, `--memory-limit`, and repeated `--allow` flags. Invoke `grvm`
without arguments to print its complete command syntax.

## Formatting, LSP, and editors

Format a package with `grand fmt`; use `grand fmt --check` in CI. The same
formatter backs `textDocument/formatting` in `grand-lsp`.

Run the language server directly:

```sh
grand-lsp
```

or through the build tool:

```sh
grand lsp
```

Both speak ordinary LSP over stdin/stdout. Configuration examples for Neovim,
Helix, Zed, and other clients are in [editors/README.md](editors/README.md).

The repository root is also a native `tree-sitter-grandiose` package. Run
`npm ci` followed by `npm test` to regenerate-check and test its parser. Zed
uses this grammar directly; it does not alias Grandiose to another language.

For VS Code development or local installation:

```sh
cd editors/vscode
npm ci --ignore-scripts

# Press F5 in VS Code for an Extension Development Host, or package it:
npm run package
code --install-extension grandiose-0.1.0.vsix
```

The extension needs Node.js 22 or newer for packaging; CI currently uses Node
24. Set `grandiose.serverPath` to an absolute `grand-lsp` path, or to `grand`
to launch `grand lsp`. Syntax highlighting works without the language server.
See [editors/vscode/README.md](editors/vscode/README.md) for details.

For Zed, build `grand-lsp`, then choose **Zed: Install Dev Extension** and
select `editors/zed`. The extension recognizes `.glorious`, loads the native
Tree-sitter grammar pinned in its manifest, and starts `grand-lsp`. See
[editors/zed/README.md](editors/zed/README.md) for the server-path override.
Standard-library definitions use ordinary cached `file://` locations and open
in Zed without a custom URI provider.

To produce a locked VSIX, host-native language-server archive, and checksums:

```sh
editors/package-local.sh /path/to/new-empty-output-directory
```

## Developing the toolchain

The compiler and VM form the root Cargo workspace. The formatter, package tool,
and language server are deliberately separate workspaces, so their commands use
explicit manifests:

When an investigation repeatedly requires an expensive full-pipeline build,
prefer adding narrow, reusable diagnostic tooling over continuing with manual
traces. Artifact snapshots and replay commands, phase/PC filters, state-delta
views, and source-to-IR maps are appropriate development tools when they make a
failure faster to reproduce and explain. Keep them opt-in, deterministic, and
covered by focused tests so the next compiler bug benefits from the same
visibility.

Self-host diagnostics report token identities in the complete distributed
source stream. Map one of those identities back to its owning file and local
coordinates without rebuilding the compiler by passing the production inputs
in bundle order:

```sh
grc --inspect-bundle-token path/to/main.glorious path/to/module.glorious -- 24956
```

The inspector prepends the embedded standard library exactly as an ordinary
distributed compilation does. `--inspect-token` remains available for a single
raw source stream.

For cleanup-oracle failures, capture the compiler's exact verifier input once
and replay it without recompiling the source bundle:

```sh
G1_PRE_ORACLE_ARTIFACT=target/pre-oracle.grbc grc -O2 src/main.glorious
G1_VERIFY_TRACE=1 grvm verify-seeded target/pre-oracle.grbc
grvm inspect-seeded target/pre-oracle.grbc FUNCTION PC
```

`verify-seeded` is a development command for artifacts whose compiler-provided
`LEAVE` cleanup anchors have not yet been completed by the VM oracle; ordinary
finished artifacts should continue to use `grvm verify`.
`inspect-seeded` prints the selected function's signature, aggregate-reference
return contract, and a bounded instruction window around the failing PC.

For failures introduced while lowering optimized MIR into physical edge
transfers, `G1_PRE_EDGE_MIR=target/pre-edge.mir` captures the canonical MIR
immediately before emission-only edge canonicalization and writes the result
afterward to `target/pre-edge.mir.post`. Set
`G1_EDGE_COPY_TRACE=<function-name-fragment>` to report copy-to-move decisions
for matching functions; `G1_EDGE_COPY_REGISTER=<logical-register>` narrows that
trace to one register.

Set `G1_RAW_MIR=target/raw.mir` to capture the canonical ownership-aware MIR
immediately after Core lowering and before validation or optimization. Comparing
this with `G1_PRE_EDGE_MIR` distinguishes frontend ownership-state mistakes from
optimizer-introduced CFG or cleanup changes without rerunning a VM replay.

To locate VM memory growth during a long compiler replay, enable the sparse
instruction sampler with `G1_VM_MEMORY_PROFILE_MIB=<growth-per-report>`. It
prints process RSS/virtual memory, the current function and PC, active and
deferred frame counts, live register counts, place-arena occupancy, and tracked
versus live cycle-reclamation nodes whenever RSS grows by that many MiB.
`G1_VM_MEMORY_PROFILE_STEPS` controls the sampling interval and defaults to one
million VM instructions.

For long VM-hosted compiler runs whose memory use is stable, set
`G1_VM_PROGRESS_STEPS=<instructions>` to print sparse execution progress. Each
sample reports total interpreted instructions, elapsed time, instruction rate,
current function and PC, and active call depth. This distinguishes a slow but
advancing phase from a stalled loop and identifies the function to inspect
without enabling the much larger per-instruction function trace.
For low-overhead cumulative attribution, set
`G1_VM_HOT_FUNCTION_SAMPLE_STEPS=<instructions>` (1,024 is a useful starting
point). `G1_VM_HOT_FUNCTION_REPORT_STEPS` controls the reporting interval and
defaults to 100 million instructions. Reports rank sampled function IDs by
their share of execution; map IDs with `grvm functions <artifact.grbc>` or the
compiler-emitted function map below.
Set `G1_VM_FUNCTION_MAP=<path>` while compiling the artifact to write a compact
TSV mapping from those runtime function IDs to MIR declaration IDs, semantic
function names, and bytecode ranges. The map is diagnostic-only and does not
change the encoded artifact.

For repeated self-host boundary work, set
`G1_SELF_HOST_REPLAY_DIR=target/self-host-replay` on the ignored fixed-point
test. The test retains the verified Rust-bootstrap `stage1.grbc` and its exact
canonical `input.glorious`, allowing the expensive bootstrap half to be reused:

```sh
grvm run --memory-limit 8192MiB \
  --allow process.args --allow fs.read --allow fs.write --allow diagnostic \
  target/self-host-replay/stage1.grbc -- \
  target/self-host-replay/stage2.grbc target/self-host-replay/input.glorious
```

Set `G1_TAIL_CALL_TRACE=<function-name-fragment>` while compiling to report
whether each direct-call candidate in matching MIR functions has an exact
return continuation and consumes its complete caller frame.

Set `G1_VM_ERROR_TRACE=1` while running bytecode to attach the executing
function, program counter, and instruction to a returned VM runtime error.

### Local command RAM gate

Use `tooling/ram-gate.sh` for every local command that executes more than
`cargo check`. It applies a 16 GiB virtual-memory cap to `cargo test` and an
8 GiB cap to direct non-Cargo commands, using four shared
`/tmp/grandiose-ram-gate/slot-*.lock` `flock` slots across all worktrees. The wrapper sets
`G1_TEST_MEMORY_CAPPED=1`, allowing memory-capped LLVM tests to avoid ASAN's
large virtual-address reservation, and defaults Rust test executables to one
in-process test thread; set `RUST_TEST_THREADS` explicitly only after measuring
the suite's memory use. The full Rust workspace has been validated with eight
threads and test optimization level 1; see [measured performance](docs/stage0-performance.md).
`cargo build` and `cargo check` deliberately pass through without taking a slot.
Test commands also use `test-with-budget.sh` for the ten-minute command bound.

```sh
cargo check --workspace
./tooling/ram-gate.sh cargo fmt --all -- --check
./tooling/ram-gate.sh cargo clippy --workspace --all-targets -- -D warnings
CARGO_PROFILE_TEST_OPT_LEVEL=1 RUST_TEST_THREADS=8 \
  ./tooling/test-with-budget.sh ./tooling/ram-gate.sh cargo test --workspace --all-targets

./tooling/test-with-budget.sh ./tooling/ram-gate.sh cargo test --manifest-path tooling/fmt/Cargo.toml --all-targets
./tooling/test-with-budget.sh ./tooling/ram-gate.sh cargo test --manifest-path tooling/grand/Cargo.toml --all-targets
./tooling/test-with-budget.sh ./tooling/ram-gate.sh cargo test --manifest-path tooling/lsp/Cargo.toml --all-targets
```

Useful design references:

- [Glorious language specification](glorious-language-specification.md)
- [compiler and VM architecture](docs/architecture.md)
- [frontend design](docs/frontend-design.md)
- [MIR design](docs/mir-design.md)
- [bytecode format and verifier contract](docs/bytecode.md)
- [Glorious standard-library specification](glorious-standard-library-specification.md)
- [live remaining-work list](docs/remaining-work.md)
