# Grandiose Developer Tooling Plan

Covers four deliverables: a build tool (`grand`), dependency management (GitHub + local
path), an auto-formatter (`grand fmt`), and a language server (`grand lsp`). Written
against `docs/frontend-design.md`, `docs/architecture.md`, `docs/std-lib.md`, and
the core spec, with implementation status called out below.

Current implementation note: the Rust `grand` crate provides the
scaffold/build/check/run/test foundation, deterministic path and pinned-git
resolution, lockfiles, caching, vendoring, and compile-fail tests. The formatter
uses the authoritative semantic parser and lossless lexer, ordered bundle
fixity context, a fixed-width document algebra with structured delimiter and
body wrapping, verbatim anchored comments, and fail-closed normalization and
token-equivalence checks. `grand fmt` renders every package file before writing
any of them, so malformed input refuses the operation transactionally; corpus,
idempotence, width, and malformed-input tests cover the implementation. The LSP
now runs the shared compiler bundle/interface/diagnostic pipeline in a persistent
multi-root document session. The compiler exports typed, scoped local-definition,
local-occurrence, and expression-type side tables derived from successfully
elaborated Core. The LSP atomically retains last-good body snapshots and uses
compiler identities for symbols, cross-file and dependency definition,
completion, references, rename, inferred-type hover and inlay hints, and
signature/doc hover; it has no lexical local-resolution fallback. `grand` probes
the real versioned `grc` contract,
passes ordered canonical `.glorious` inputs, consumes JSON diagnostics and
authoritative user/std interfaces, emits `.grbc`, and executes it through
`grvm`; legacy `.gr` and fake/LLVM flows remain compatibility paths. The
`grand` also probes the selected VM's contract/artifact range before compiling
and fingerprints compiler + VM content identities atomically. The `lex`, declaration-`scan`, and
interface/name/type `resolve`, and `check` stop boundaries are real. Released-seed
identity negotiation and the bounded versioned `grc --serve` JSON-line transport
are also implemented. `IncrementalCompilerSession` performs genuine per-body
inference reuse when declaration context is unchanged, transactionally rolling
back a failed request. The milestone table records implementation dependency
order rather than outstanding work.

Ground rules (project decisions):
- **All tooling is written in Rust**, as crates alongside the existing bootstrap
  interpreter crate. Migration to Grandiose happens after the compiler is done; the
  plan calls out the migration seams so nothing is designed into a corner.
- **Native code is the eventual compilation target.** The build tool's default
  pipeline assumes it, but the current execution path (LLVM IR → `lli` with the
  dlopen'd C runtime / bytecode-style interpretation) stays as a supported target
  until the native fixed point lands.

---

## 0. Design facts the tooling leans on

These properties of the language design shape everything below:

- **Package/module compilation model.** A program is `std-lib` + an application
  root and module closure + explicitly named dependency roots and their closures,
  all in deterministic order; a segment table maps byte ranges back to files. The
  compiler owns package-root, module, import, privacy, and fixity resolution.
- **Structured namespaces and authority.** Definitions carry module identities;
  item and private-field access is checked against the declaring module's privacy
  domain. Cross-package collisions are handled at package-root/module boundaries.
- **Source-declared operator fixities.** `infixl/infixr/none 0..255` and `prefix`
  declarations live in source and affect how expressions *group*. Any tool that parses
  expressions (formatter, LSP) must collect fixities from the whole bundle — including
  dependencies — before parsing bodies. Fixities are interface-level facts, so they are
  discoverable in the declaration-scan pass without elaborating bodies.
- **Structural syntax, insignificant whitespace, canonical forms in the spec.** The
  spec already legislates canonical signature forms (`-> ()` omitted as bare `->`,
  empty effect row `/ {}` omitted, `!` never omitted). The formatter enforces spec
  canon; there is no style configuration.
- **Comments: line comments + nested block comments** (per frontend-design). The
  semantic lexer and shared gap-free lossless stream implement both forms; the
  formatter retains them as anchored trivia rather than dropping their bytes.
- **Structured diagnostics.** Phases return `(origin, proof_trace, reason)` failure
  objects; a renderer owns wording; spans are `(start_byte, end_byte)` u32 pairs into
  the bundle. The compiler's JSON diagnostic mode and the LSP both consume this
  machine-readable shape (§1.2).
- **Batch compilation remains whole-bundle and non-incremental by design.** The
  persistent editor path reparses and resolves the bundle, then reuses checked
  per-body inference products when the declaration context and that body's
  fingerprint are unchanged. Failed requests roll back the session cache. This
  remains a compact two-level design, not a general query engine.
- **Frozen CLI contract** (`architecture.md §7`): `grc [-O..] [--emit ...] SOURCE... -o OUT`.
  The build tool drives this; it does not reimplement the frontend.

## 1. Shared infrastructure (prerequisites inside the compiler)

Small compiler-side investments that all three tools consume. Do these first; they are
cheap now and expensive to retrofit.

### 1.1 Lexer trivia
- The compiler's authoritative lexer recognizes line and nested block comments and
  also exposes a gap-free lossless token stream. The semantic pipeline ignores
  trivia while the formatter and LSP consume the lossless view; there is no second
  tooling lexer.
- Keep the invariant: concatenating `(token text + trivia)` reproduces the source
  byte-for-byte. This is the formatter's round-trip foundation and costs nothing to
  maintain from day one.

### 1.2 Diagnostics as data: `--emit diagnostics-json`
- A flag that prints one JSON object per diagnostic: code, severity, title, primary +
  secondary labels as `{file, start_byte, end_byte, line, col, message}` (segment
  table already recovers file/line), note, help.
- LSP phase 1 (§4.2) is *only* this flag plus a thin server. Golden diagnostic tests
  gain a stable machine-checkable format as a side benefit.

### 1.3 Interface dump: `--emit interfaces-json`
- Emit the declaration-scan products as JSON: every top-level declaration (callables
  with signatures, structs/enums with fields/variants, effects with operations, type
  aliases, globals, fixity declarations, trait impl heads), each with its defining
  span and doc-comment text if present.
- This is the syntax-level backbone for LSP document symbols, go-to-definition,
  completion of top-level names, and for the build tool's collision detection (§2.6).
  It requires no body elaboration, so it stays fast and robust to body-level errors.

### 1.4 Stop-after-phase flags
- `--phase lex|scan|resolve|check` so tools can pay only for what they need
  (formatter: lex+parse; symbol queries: scan; full diagnostics: check).

## 2. Build tool: `grand`

A single CLI binary that subsumes the `grc` wrapper script. Implemented in Rust as a
crate next to the existing bootstrap crate (per the ground rules): it needs git,
networking, filesystems, process supervision, and JSON/TOML — all free in Rust. The
build tool is host-side plumbing (cargo isn't written in rustc's object language
either); it is also the piece with the *least* pressure to ever migrate to Grandiose.

### 2.1 Commands
```
grand new <name> [--path <path>]   # scaffold a package (default: ./<name>)
grand init                         # scaffold the current, existing directory
grand build [-O..] [--emit ...]    # resolve deps -> ordered file list -> compiler
grand run [-- args]                # build + execute under the supervisor limits
grand check                        # frontend only, no emission (fast feedback)
grand test                         # run *_test.glorious files / test callables (see 2.7)
grand fmt [--check]                # formatter (§3)
grand lsp                          # start the language server (§4)
grand add <dep>                    # edit [dependencies] + update lockfile
grand vendor                       # copy resolved deps into ./vendor for offline builds
grand clean
```

### 2.2 Manifest — extend the existing `grandiose.toml`
```toml
[project]
name = "my-app"          # must match package-name rules: [a-z][a-z0-9-]*
version = "0.1.0"        # semver
entry = "src/main.glorious"

[dependencies]
# local path dependency
mylib = { path = "../mylib" }
# github dependency — always pinned to an immutable revision in the lockfile
json  = { git = "https://github.com/user/grandiose-json", tag = "v0.2.0" }
utils = { git = "https://github.com/user/gr-utils", rev = "a1b2c3d" }
# shorthand for github
text  = { github = "user/gr-text", branch = "main" }

[backend]
kind = "vm"              # canonical G1 `.grbc` + `grvm` pipeline
```
- A dependency is itself a directory with a `grandiose.toml`. **Library packages have
  no `entry`;** instead `sources = ["src/**/*.glorious"]` (default: canonical
  `.glorious` plus legacy `.gr` sources sorted
  lexicographically for determinism). An executable package has `entry`; its entry
  file is placed last in the bundle.
- `git` requires exactly one of `tag | rev | branch`. `branch` is resolved to a
  commit at lock time and never re-resolved until `grand update`.

### 2.3 Resolution and the bundle order
1. Read the manifest graph transitively (path deps read in place; git deps fetched to
   the cache, §2.6).
2. Build the package DAG; reject cycles with a diagnostic naming the cycle.
3. **Version policy: one version per package name, minimal-version selection.** If two
   packages require `json` at incompatible pins, that's a hard error listing both
   requirers. Explicit dependency roots are assigned normalized package aliases;
   this policy avoids two different roots competing for the same alias.
4. Topologically sort packages (dependencies first), then within each package apply
   its deterministic source ordering.
5. Final bundle: `std-lib` + dep packages in topo order + root package, entry file
   last. Hand the ordered file list to the compiler; the segment table keeps
   per-file diagnostics accurate. Same lockfile + same sources ⇒ byte-identical
   bundle ⇒ byte-identical artifact (this composes with the stage-2/3
   reproducibility story).

### 2.4 Build targets: native by default, interpreted path preserved
`grand build` owns the *whole* pipeline, not just the frontend invocation:
- **`--target native` (the eventual default):** compiler emits `.ll` → `llc`/`clang`
  compile + link against the C runtime (`compiler/runtime/`) → real executable in
  `target/`. The build tool owns toolchain discovery (clang/llc ≥ the manifest's
  `minimum-version`), object caching keyed by bundle hash, and linking.
- **`--target interp` (the working path today):** compiler emits `.ll` → run via
  `lli --dlopen`'d C runtime, under the supervisor limits (wall clock, 4 GiB
  address-space ceiling). `grand run` uses whichever target the manifest/flag
  selects, so switching a project to native later is a one-line change.
- The target abstraction is a small trait in the build tool (`emit → materialize →
  execute`), so a VM/bytecode backend slots in as a third implementation if it
  returns; nothing outside that trait knows how programs run.

### 2.5 Lockfile — `grandiose.lock`
```toml
version = 1

[[package]]
name = "json"
source = "git+https://github.com/user/grandiose-json?tag=v0.2.0"
commit = "f00dfeed..."          # full 40-char sha, the only thing that matters
content-hash = "blake3:..."     # hash of the package's file set, verified on use
deps = ["text"]
```
- Committed to VCS. `grand build` fails if the lockfile is stale relative to the
  manifest (`--locked` behavior by default in CI via env var).
- `grand update [package]` re-resolves branches/tags and rewrites the lock.
- Path deps appear in the lock without a commit (they are the local workspace's
  responsibility), but their manifests still participate in resolution.

### 2.6 Fetching and caching
- Cache root: `~/.cache/grandiose/` (XDG-respecting):
  `git-db/<repo-hash>/` bare clones, `checkouts/<repo-hash>/<commit>/` immutable
  worktrees.
- Fetch by shelling out to system `git` (not libgit2): simpler, respects the user's
  auth setup (ssh keys, credential helpers) for private repos.
- Checkouts are read-only; `content-hash` is verified before every build so a
  tampered cache is detected.
- **No build scripts, no code execution at resolution time — ever.** A package is
  data (`.glorious`/legacy `.gr` files + manifest). This is a security stance worth keeping permanently;
  the concatenation model means there's nothing a build script would legitimately do.
- `grand vendor` copies checkouts into `./vendor/` and a config key redirects
  resolution there for offline/hermetic builds.

### 2.7 Namespace collisions
Run the compiler interface scan per package and compare fully qualified exported
identities. Duplicate leaf names in distinct modules are valid. Only conflicting
package/module identities are build-tool diagnostics; the compiler remains the
authority for imports, visibility, and ambiguity.

### 2.8 Tests
- Convention: files matching `tests/**/*.glorious` (plus legacy `.gr`) each compile as their own executable
  (package sources + that file, its `main` as entry); exit code 0 = pass. This
  matches the existing e2e harness style and needs zero language features.
- Later, when attributes/annotations exist, migrate to in-source `test` callables.

## 3. Formatter: `grand fmt`

### 3.1 Architecture
- **Rust, using the compiler frontend directly.** `tooling/fmt` depends on the
  `grandiose` compiler crate and consumes its authoritative gap-free lossless lexer,
  interface/fixity collection, and parser validation. There is no independently
  vendored tooling parser or lexer to keep synchronized.
- Migration seam: formatting remains a pure transformation over compiler-produced
  syntax and trivia. A future compiler port can preserve the same interface and
  golden corpus without creating a second grammar authority.
- Pipeline: lex with trivia (§1.1) → parse to AST-with-trivia → pretty-print via a
  Wadler/Prettier-style document algebra (`group`, `indent`, `softline`, `hardline`)
  with a max width (100) — the standard algorithm; it fits the "one canonical
  algorithm, no config" stance.

### 3.2 The fixity problem
Expression grouping depends on fixity declarations that may live in *other files*
(std-lib, dependencies). Two rules keep this sane:
- `grand fmt` always formats in the context of the resolved bundle's fixity set
  (it runs the declaration scan over the ordered file list first — cheap).
- The formatter **never re-associates**: it prints the grouping the parser produced
  and only removes parentheses that are provably redundant *under the known fixity
  table*, and only when the operand chain's fixities were all resolved. Unknown
  operator ⇒ keep the user's parens. This makes formatting stable even when a
  fixity later changes.

### 3.3 Canonical style (initial rule set)
- Spec-mandated normalizations: `-> ()` → `->`; `/ {}` → omitted; `!` preserved.
- 4-space indent; braces K&R style (`name(params) -> Type {` on one line while it
  fits, params broken one-per-line with trailing comma when it doesn't).
- One blank line max between declarations; struct/enum fields one per line once the
  inline form exceeds width; `handle` arms and match-style arms one per line.
- Comments: preserved verbatim, anchored to the token they preceded/followed
  (leading trivia stays leading). Never reflow comment text.
- Idempotence and safety invariants, enforced in CI on the whole corpus
  (`examples/`, `tests/cases/`, `src/main.glorious` itself):
  1. `fmt(fmt(x)) == fmt(x)`
  2. `parse(fmt(x))` is α-identical to `parse(x)` (token stream modulo trivia is
     unchanged apart from the spec normalizations)
  3. files with parse errors are left untouched (formatter refuses, exits nonzero).

### 3.4 Deliverables
- `grand fmt` (write in place), `grand fmt --check` (CI), `grand fmt --stdin` (editor
  integration / LSP `textDocument/formatting`), range formatting later.

## 4. Language server: `grand lsp`

### 4.1 Architecture
- **Rust host, Grandiose brain.** The server binary (Rust, `tower-lsp` or hand-rolled
  JSON-RPC over stdio) owns: transport, document store with open-buffer overlays,
  UTF-16↔byte-offset position mapping (LSP speaks UTF-16 line/col; compiler speaks
  byte offsets — one conversion layer, tested hard), debouncing, request
  cancellation, and process supervision.
- The semantic engine is the compiler: the LSP uses the shared `grandiose` frontend
  and `IncrementalCompilerSession` in process, while the versioned `grc` JSON
  contract exposes the corresponding batch surfaces to external tools. The shared
  frontend is the grammar and name/type authority; the LSP does not maintain a
  private parser or resolver.
- The build tool provides project shape: `grand lsp` reads `grandiose.toml` +
  lockfile to discover the application root and explicit dependency package roots.
  Those roots are marked in the compiler bundle, so package aliases, module paths,
  privacy, diagnostics, and go-to-definition into dependency source all use the
  compiler's structured identities.

### 4.2 Phase 1 — diagnostics (ship first, tiny)
- On open/change, compile the overlaid project bundle through the in-process
  compiler session and map compiler spans through the segment table to per-file
  LSP diagnostics. External clients can obtain the same structured diagnostics
  through `grc --diagnostics json`.
- Whole-bundle check must stay fast enough for keystroke-ish latency; the <120 s
  budget is for *self-hosting the 36 k-line compiler at -O2* — a `--phase check`
  run of a normal project should be well under a second. If the compiler-on-itself
  case is too slow for interactive use, fall back to check-on-save for that repo.
- Also in phase 1: document formatting (delegates to §3), and that's it. This alone
  is 80 % of daily editor value.

### 4.3 Phase 2 — syntax + interface features (implemented)
Interface features consume compiler interface and occurrence tables plus the shared
lossless token stream:
- Document symbols / workspace symbols (declaration list with spans).
- Go-to-definition and find-references for top-level and imported names use the
  compiler's resolved occurrences. This includes structured module paths and
  manifest dependency package roots.
- Completion: top-level callables/types/variants/effect operations with signatures
  from interface data; keyword + snippet completion (`handle`, `effect`, `struct`).
- Hover: declared signature text + doc comment for top-level names.
- Semantic tokens (coarse: from lexer + declaration kinds), folding ranges, selection
  ranges.

### 4.4 Phase 3 — body-level semantics (implemented)
- **Persistent frontend session.** The Rust frontend provides `grc --serve`
  over versioned JSON lines, with bounded requests/source snapshots,
  whole-bundle content invalidation, atomic last-good commits, and one-shot
  diagnostic/artifact parity. The in-process `IncrementalCompilerSession` caches
  per-body inferred products behind context and body fingerprints; unchanged bodies
  are reused, changed bodies are elaborated, and failure restores the prior cache.
- **Compiler-owned semantic side tables.** Successful typed Core produces stable
  file-local local identities, exact definition/reference spans, lexical scope
  ranges, inferred local types, and expression types. These tables power:
  hover with inferred types, go-to-definition for locals/params, find-references,
  rename (top-level + local), inferred-local-type inlay hints, and signature help.
- Completion inside bodies: compiler-resolved scope at cursor position (params, lets in
  scope, then top-levels), typed member access after `.` / `::` from the side
  tables of the enclosing body's last successful elaboration.
- **Error resilience matters more than freshness:** the LSP retains last-good body
  tables only through the unchanged source prefix; shifted or ambiguous spans fail
  closed rather than being rebound lexically.

### 4.5 Editor distribution
- VS Code extension (TextMate grammar for instant syntax highlighting — worth
  writing in phase 1 regardless of the LSP — plus LSP client config), plus a
  documented `grand lsp` stdio contract for Neovim/Helix/Zed users.

## 5. Sequencing

Ordered so every step ships user-visible value and nothing blocks on the compiler's
long tail:

| # | Milestone | Depends on |
|---|-----------|------------|
| 1 | Comment syntax + trivia-preserving lexer (§1.1) | — |
| 2 | `--emit diagnostics-json` (§1.2) | — |
| 3 | `grand` skeleton: `new/init/build/run/check` over path-only deps + bundle ordering (§2.1–2.3) | — |
| 4 | LSP phase 1: diagnostics + TextMate grammar + VS Code extension (§4.2) | 2, 3 |
| 5 | Git deps + lockfile + cache + vendor (§2.5–2.6) | 3 |
| 6 | Interface scan emission + collision checking (§1.3, §2.7) | 3 |
| 7 | Formatter core + `grand fmt` + LSP formatting (§3) | 1 |
| 8 | LSP phase 2: symbols/nav/completion from interfaces (§4.3) | 4, 6 |
| 9 | `grand test` (§2.8) | 3 |
| 10 | Compiler session mode + per-body re-elaboration + side tables (§4.4) | 6 |
| 11 | LSP phase 3: hover types, rename, references, inlay hints | 10 |

All listed milestones are implemented. Their numbering remains useful as the order
in which the interfaces depend on one another.

## 6. Risks / open questions

- **Whole-bundle parse/resolve latency** remains the LSP's structural scaling risk.
  Per-body inference reuse removes unchanged elaboration work, while debounce and
  check-on-save remain available if project-scale bundle rebuilding becomes visible.
- **Package ecosystem breadth** beyond the implemented explicit manifest-name to
  dependency-root mapping (version selection, registries, and artifact caching)
  remains build-tool policy rather than compiler module semantics.
- **Fixity-dependent parsing** means a lone file can't be parsed in isolation with
  certainty. Every tool here therefore operates on the *resolved bundle*, never on a
  single file out of context. Worth stating as a project-wide invariant.
- **Tooling migration to Grandiose** (post-compiler) is cheapest if the Rust crates
  keep hard seams now: the shared compiler frontend API, the formatter's pure
  syntax/trivia-to-text function, and the LSP's semantic snapshot boundary are each
  independently replaceable; the git/network/process layer likely stays Rust the
  longest.
