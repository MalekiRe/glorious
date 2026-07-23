# Grandiose

Grandiose is an experimental systems language built around quantitative
ownership, algebraic effects, source-defined control flow, and portable verified
bytecode. It aims to make resource usage and non-local control explicit without
giving up higher-order functions, Rust-style borrowing, traits, or generics.

The project is pre-alpha. Source and artifact compatibility are not stable yet,
but the Rust compiler, verifier, VM, package tool, formatter, language server,
and editor extension are usable today.

## What makes the language different?

### Values describe how many times they may be used

Grandiose generalizes affine and linear ownership with `Use<[lower, upper]>`.
The interval is part of the type's evidence:

```rust
struct Ticket { serial: i64 }

impl Use<[1,1]> for Ticket {}

redeem(ticket: Ticket) -> i64 {
    let Ticket { serial } = move ticket;
    serial
}
```

`Use<[1,1]>` means that a `Ticket` must be transferred or deconstructed exactly
once. `Use<[0,1]>` describes an affine value, `[0,infinity]` a conventionally
reusable value, and `[0,0]` a value that may be destroyed without being used.
The compiler tracks these quantities through branches, loops, calls, closures,
partial moves, cancellation, and continuation replay.

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

answer() -> i64 {
    handle Ask::ask() {
        Ask::ask(continuation) => continuation(42)
    }
}
```

Grandiose supports terminal effects, one-shot and finite multi-shot resumptions,
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

- `grc` compiles `.glorious` source into verified G1 bytecode.
- `grvm` verifies and executes `.grbc` artifacts.
- `grand` manages packages, dependencies, builds, tests, formatting, docs, and
  the language server.
- `grandfmt` is the formatter library used by `grand fmt` and the LSP. It does
  not install a separate command.
- `grand-lsp` provides diagnostics, formatting, symbols, completion, hover,
  definitions, references, and rename over standard input/output.
- `editors/vscode` contains the VS Code extension and TextMate grammar.

The source suffix is `.glorious`.

## Install from this checkout

Install a stable Rust toolchain with Cargo first. Then run:

```sh
cargo install --path crates/grandiose --bin grc
cargo install --path crates/grandiose-vm --bin grvm
cargo install --path tooling/grand --bin grand
cargo install --path tooling/lsp --bin grand-lsp
```

Cargo normally installs these commands into `~/.cargo/bin`; ensure that
directory is on `PATH`.

To build without installing:

```sh
cargo build --release --workspace --bins
cargo build --release --manifest-path tooling/grand/Cargo.toml --bin grand
cargo build --release --locked --manifest-path tooling/lsp/Cargo.toml --bin grand-lsp

export GRAND_COMPILER="$PWD/target/release/grc"
export GRAND_VM="$PWD/target/release/grvm"
export PATH="$PWD/tooling/grand/target/release:$PWD/tooling/lsp/target/release:$PATH"
```

`grand` prefers this checkout's release-mode `grc` and `grvm`, then discovers
installed tools on `PATH`. It intentionally does not select binaries from
`target/debug`; compiler debug builds are dramatically slower on real source.
`GRAND_COMPILER` and `GRAND_VM` remain useful when explicitly testing a
particular toolchain build.

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

```sh
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace --all-targets

cargo test --manifest-path tooling/fmt/Cargo.toml --all-targets
cargo test --manifest-path tooling/grand/Cargo.toml --all-targets
cargo test --manifest-path tooling/lsp/Cargo.toml --all-targets
```

Useful design references:

- [language core specification](glorious-branded-environment-core-spec.md)
- [compiler and VM architecture](docs/architecture.md)
- [frontend design](docs/frontend-design.md)
- [MIR design](docs/mir-design.md)
- [bytecode format and verifier contract](docs/bytecode.md)
- [standard-library contract](docs/std-lib.md)
- [live remaining-work list](docs/remaining-work.md)
