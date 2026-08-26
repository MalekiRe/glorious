# Documentation consistency audit — 2026-08-25

**Status:** historical audit record  
**Repository baseline:** `3fd2e0ddf3c10e2d558ad21190b975500374ed71`  
**Scope:** every Markdown file in the baseline tree, plus the Stage0 CLI and
selected implementation metadata used to verify documentation claims

## Executive finding

The repository did not primarily suffer from missing prose. It suffered from
unbounded authority: normative specifications, greenfield proposals, completed
migration notes, worktree reports, benchmarks, tutorials, and current
implementation guides were stored beside one another without a status system.

At the audited baseline there were 54 Markdown files:

- 6 at repository root;
- 2 local crate contracts;
- 30 under `docs/`;
- 3 editor guides;
- 3 self-host/tooling local guides;
- 10 tutorial files.

Several documents accurately describe their local subtree. The severe drift was
concentrated in broad project-status and architecture documents inherited from
the removed pre-Stage0 compiler.

## Confirmed contradictions and inconsistencies

### 1. The root README describes two incompatible repositories

The README first identifies the active workspace as `grandiose-stage0` plus
`grandiose-vm`, then presents the retired `grand`, `grandfmt`, `grand-lsp`, and
old `grc` interfaces as supported. Its documented `grc` phases, server mode,
LLVM/native emissions, formatter, package commands, and workspace examples do
not match the root Cargo workspace or the Stage0 command parser.

**Resolution:** rewrite the README around the active workspace and exact
`grc-stage0` commands. Keep old commands only in the archive/legacy boundary.

### 2. Editor documentation contradicts both tooling policy and package metadata

`tooling/LEGACY.md` says `grand-lsp` is intentionally disabled and must not be
repaired as part of Stage0. `tooling/lsp/Cargo.toml` also identifies it as a
disabled legacy language server and the root workspace excludes it. The editor
READMEs nevertheless promise diagnostics, navigation, formatting, packaged
binaries, and release automation backed by `grand-lsp`.

The non-Markdown VS Code and Zed manifests still advertise the legacy server.
That is an implementation/release follow-up; this PR makes the Markdown status
truthful without pretending the manifests are fixed.

**Resolution:** classify editor assets as syntax support and explicitly mark all
LSP behavior unsupported pending a Stage0-native server.

### 3. Architecture and backend documents make mutually exclusive claims

`docs/architecture.md` describes the removed `crates/grandiose` compiler and
says Generation 1 has no native backend. `docs/llvm-backend.md` says the LLVM
backend is active and extensively implemented in that same removed compiler.
Neither describes the active root workspace.

**Resolution:** archive both historical texts and replace `docs/architecture.md`
with the Stage0/VM/self-host component map.

### 4. Several documents claim implementation in paths and commands that do not exist

Examples include:

- `crates/grandiose`;
- `self-host/` and `self-host/src/compiler`;
- old `self_host_*` test modules;
- `grc --serve`;
- `grc --emit control-plan`;
- old MIR/Core/LLVM/native emission phases;
- `tooling/self-host-native.sh`;
- `tooling/seed-native-selfhost-cache.sh`;
- old compiler protocol/client/LSP integration test paths.

`docs/control-kernel.md`, `docs/compiler-changes-for-tooling.md`,
`docs/tooling-plan.md`, `docs/native-selfhost-development.md`, and several
self-host reports use these references to assert current completion.

**Resolution:** archive the documents as pre-Stage0 records.

### 5. “Implemented” design records still contain unresolved design questions

`docs/optional-label-unification.md` labels compiler, self-host, formatter, LSP,
and documentation migration complete, but later leaves a key grammar choice
open. Other records describe rollout against directories that no longer exist.

**Resolution:** archive these as design records rather than current contracts.

### 6. The standard library has two overlapping authorities

`docs/std-lib.md` and `docs/new-stdlib.md` both present broad standard-library
definitions. They disagree on discarded-value ownership bounds (including
`Use<[0,0]>` versus `Use<[0,1]>`), constructor spelling, and organization.
Readers can select incompatible rules without any precedence signal.

**Resolution:** retain `std-lib.md` as the sole canonical Generation-1 design,
archive the duplicate proposal, and leave a supersession notice at its old path.
No compiler semantics are changed by this documentation PR; tests and a
separate conformance decision should resolve implementation differences.

### 7. Self-hosting status spans incompatible compiler generations

Old files claim various degrees of parity or completed testing for
`crates/grandiose` and `self-host/`. The current program instead mirrors
`grandiose-stage0` under `self-host-stage0/`, pins a baseline, tracks 36 modules,
and marks all 36 ledger entries `scaffolded`.

**Resolution:** create one current `docs/self-hosting.md`, retain the active
plan/baseline/ledger/primitive boundary/generated semantic map, and archive the
pre-Stage0 parity/readiness reports.

### 8. The snowflake document series is simultaneously incomplete and duplicated

The roadmap specifies a 32-chapter corpus, but only chapters 01, 02, and 05 are
maintained as separate files. A roughly 1.4 MB generated compendium duplicates
a full dossier-like corpus in one file, making review and authority unclear.
Existing chapters also link to removed paths or present implementation-shaped
APIs without current-code evidence.

**Resolution:** classify the series as an incomplete proposal, add a directory
index, retain the generated compendium in Git history at the audited baseline,
and replace its former path with a concise index.

### 9. The tutorial presents a retired workflow as currently checked

The tutorial uses `grand`, `grand test`, `grand fmt`, the old compiler, and the
old VM/package flow. Its entry and limitations chapters describe that workflow
as current or checked by the repository, although those tools are explicitly
legacy and outside the active workspace.

**Resolution:** preserve all original chapters in the archive and replace the
active mdBook with a historical-status page.

### 10. Root reports and benchmarks lack lifecycle boundaries

`REPORT.md` explicitly describes modified/uncommitted and unpushed work.
Performance and architecture reviews are not consistently tied to a durable
date, commit, environment, and maintained code layout. `TODO.md` duplicates live
project tracking without ownership or freshness.

**Resolution:** move all four root snapshots into `docs/archive/reports/` and
remove them from the repository entry surface.

### 11. A broken relative specification link exists

`docs/effect-syntax-redesign.md` links to
`glorious-branded-environment-core-spec.md` as though the target were under
`docs/`, while the file lives at repository root.

**Resolution:** archive the superseded design record; archived links are
preserved as provenance and are not treated as current navigation.

### 12. Status is copied into prose instead of generated from evidence

Counts, parity claims, implementation checklists, and readiness statements are
repeated across hand-written reports. They drift independently from
`baseline.toml`, `module-ledger.toml`, source inventories, and tests.

**Resolution:** make the ledgers/generated map canonical for their facts and
require prose to link instead of copying live status.

## General Stage0 compiler/driver issues

This is intentionally a general list rather than a full compiler review.

1. **The usage interface is incomplete.** The first usage line advertises only
   `<check|run>`, and the usage block omits the accepted `--runtime-host`
   option. There is no conventional `--help`, `help`, `--version`, or
   command-specific help.
2. **Global options are not validated per command.** Runtime, source, and
   capability options are parsed before dispatch and can be silently accepted
   by verification commands that do not use them. `--diagnostics json` is also
   accepted for verification/execution commands whose errors remain debug-form
   text.
3. **Source execution leaks host compiler argv into the guest.** `run` creates
   the VM host with `env::args().collect()`, so guest arguments include the
   Stage0 invocation rather than a deliberate guest argv contract.
4. **Artifact execution invents argv[0].** `run-vm` hard-codes `"grc"` rather
   than the artifact path or an explicitly documented value.
5. **The primary source identity is detached from the input path.** Every main
   file is mapped to the logical path `src/main.glorious`; two different host
   paths can therefore share the same logical identity unless the caller
   changes package/source options.
6. **Important identities and limits are embedded in the adapter.** The build
   identity string, default package, target, 64 MiB driver stack, bootstrap
   ordinal/optimization, and bootstrap limits are hard-coded rather than
   surfaced as versioned policy or configuration.
7. **Error rendering is inconsistent.** Some errors use stable display text;
   artifact/manifest/VM failures use Rust debug formatting. The machine-readable
   diagnostic contract does not cover all failure paths.
8. **The CLI contract is not separately tested/documented as a stable API.**
   Exit codes, stdout payloads (for example verification fingerprints), stderr
   format, overwrite behavior, and guest-argument semantics should have
   end-to-end tests.
9. **The 64 MiB worker stack is a broad operational workaround.** It may be
   justified by current compiler-world layout, but it raises per-invocation
   memory requirements and hides which phases need large stacks.
10. **No explicit TODO markers were found by repository code search.** That is
    good hygiene, but it also means incomplete behavior must be tracked through
    tests, ledgers, and issues rather than discoverable stubs.

## Structural changes made by the cleanup PR

- Add one documentation map and one precedence/lifecycle policy.
- Rewrite the root README and Stage0 README against the actual workspace and
  parser.
- Add one current architecture overview and one current self-hosting overview.
- Retain canonical specifications and current local contracts.
- Reclassify frontend, MIR, and snowflake material as proposals.
- Move retired compiler, tooling, backend, parity, report, tutorial, and design
  documents under `docs/archive/` without editing their historical contents.
- Replace the duplicate standard-library document with a supersession notice.
- Replace the large generated compendium with a concise index; the original
  remains recoverable from the audited baseline instead of inflating this PR.
- Rewrite editor Markdown so syntax support is not confused with a supported
  LSP.
- Replace the runnable-looking historical tutorial with a status page.

## Complete file-by-file disposition

| File | Classification at baseline | PR disposition |
|---|---|---|
| `ARCHITECTURAL_REVIEW.md` | Historical report | Archive as `docs/archive/reports/ARCHITECTURAL_REVIEW.md`; it describes the removed compiler. |
| `PERFORMANCE_COMPARISON.md` | Measured snapshot without durable provenance | Archive as `docs/archive/reports/PERFORMANCE_COMPARISON.md`. |
| `README.md` | Current entry point | Rewrite against the active Cargo workspace and actual `grc-stage0` parser. |
| `REPORT.md` | Worktree-specific historical report | Archive as `docs/archive/reports/REPORT.md`; it explicitly discusses uncommitted/unpushed work. |
| `TODO.md` | Stale task snapshot | Archive as `docs/archive/reports/TODO.md`; use issues/ledgers for live work. |
| `glorious-branded-environment-core-spec.md` | Normative language design | Retain; scope it through the documentation map so it is not confused with Stage0 implementation status. |
| `crates/grandiose-stage0/README.md` | Current implementation contract | Rewrite with the seven actual commands and option model. |
| `crates/grandiose-vm/tests/fixtures/README.md` | Current local contract | Retain. |
| `docs/architecture.md` | Pre-Stage0 architecture presented as current | Archive original and replace with the active Stage0/VM/self-host architecture. |
| `docs/bytecode.md` | Artifact-format reference | Retain; implementation and verifier tests resolve drift. |
| `docs/compiler-changes-for-tooling.md` | Historical tooling design presented as implemented | Archive under `pre-stage0/`. |
| `docs/control-kernel.md` | Historical design with false implementation references | Archive under `pre-stage0/`. |
| `docs/default-moves-and-closure-captures.md` | Superseded design record | Archive under `design-records/`. |
| `docs/effect-syntax-redesign.md` | Superseded design record with stale paths/link | Archive under `design-records/`. |
| `docs/frontend-design.md` | Future frontend proposal | Retain and classify as proposal. |
| `docs/glorious-stage0-self-hosting-plan.md` | Active self-host plan | Retain and link from one current status page. |
| `docs/llvm-backend.md` | Removed backend presented as active | Archive under `pre-stage0/`. |
| `docs/mir-design.md` | Future MIR proposal | Retain and classify as proposal. |
| `docs/native-selfhost-development.md` | Removed LLVM/Wild workflow | Archive under `pre-stage0/`. |
| `docs/new-stdlib.md` | Duplicate/superseded stdlib proposal | Archive original; replace old path with a supersession notice. |
| `docs/optional-label-unification.md` | Historical design claiming completion while retaining open grammar questions | Archive under `design-records/`. |
| `docs/remaining-work.md` | Old compiler roadmap/status | Archive under `pre-stage0/`. |
| `docs/self-host-parity.md` | Old self-host parity status | Archive under `pre-stage0/`. |
| `docs/self-host-stage0/performance-baseline.md` | Measured snapshot | Retain, but classify as dated evidence rather than current status. |
| `docs/self-host-stage0/primitive-boundary.md` | Current self-host boundary | Retain. |
| `docs/self-host-test-parity.md` | Old completed-parity claim | Archive under `pre-stage0/`. |
| `docs/self-hosted-compiler-snowflake-stage-one.md` | Future self-host architecture proposal | Retain and classify as proposal. |
| `docs/self-hosted-compiler/00-snowflake-document-roadmap.md` | Incomplete 32-chapter proposal roadmap | Retain with an index that states the series is incomplete. |
| `docs/self-hosted-compiler/00-snowflake-synopsis-compendium.md` | 1.4 MB generated duplicate corpus | Replace with a concise index; retain the original in Git history at the audited baseline. |
| `docs/self-hosted-compiler/01-architecture-and-trust-boundaries.md` | Proposal chapter with stale current-code links | Retain as proposal; do not use for current status. |
| `docs/self-hosted-compiler/02-compilation-inputs-revisions-and-session-ownership.md` | Proposal chapter with stale current-code links | Retain as proposal; do not use for current status. |
| `docs/self-hosted-compiler/05-dependency-tracking-and-invalidation.md` | Proposal chapter with inconsistent series/status framing | Retain as proposal and index it. |
| `docs/self-hosted-compiler/stage0-semantic-test-map.md` | Generated current inventory | Retain; explicitly not a completion score. |
| `docs/self-hosted-compiler/stage1-readiness.md` | Historical readiness snapshot | Archive under `pre-stage0/`. |
| `docs/selfhost-parity-audit.md` | Old self-host audit | Archive under `pre-stage0/`. |
| `docs/size-speed-review.md` | Old compiler measurement/review | Archive under `pre-stage0/`. |
| `docs/std-lib.md` | Canonical Generation-1 stdlib design | Retain as the sole canonical stdlib document. |
| `docs/tooling-plan.md` | Removed tooling stack presented as implemented | Archive under `pre-stage0/`. |
| `editors/README.md` | Current guide contradicting disabled LSP | Rewrite: syntax assets current, LSP legacy. |
| `editors/vscode/README.md` | Current guide overstating LSP support | Rewrite: package/validate syntax assets; no supported Stage0 LSP. |
| `editors/zed/README.md` | Current guide overstating LSP support | Rewrite: syntax assets only; launcher is legacy. |
| `self-host-stage0/README.md` | Current local no-fallback contract | Retain. |
| `self-host-stage0/src/README.md` | Current local source contract | Retain. |
| `tooling/LEGACY.md` | Current legacy boundary | Retain. |
| `tutorial/src/01-package.md` | Historical tutorial chapter | Archive under `docs/archive/tutorial/`. |
| `tutorial/src/02-parser.md` | Historical tutorial chapter | Archive under `docs/archive/tutorial/`. |
| `tutorial/src/03-tape.md` | Historical tutorial chapter | Archive under `docs/archive/tutorial/`. |
| `tutorial/src/04-effects.md` | Historical tutorial chapter | Archive under `docs/archive/tutorial/`. |
| `tutorial/src/05-execution.md` | Historical tutorial chapter | Archive under `docs/archive/tutorial/`. |
| `tutorial/src/06-cli.md` | Historical tutorial chapter | Archive under `docs/archive/tutorial/`. |
| `tutorial/src/07-testing.md` | Historical tutorial chapter | Archive under `docs/archive/tutorial/`. |
| `tutorial/src/08-limitations.md` | Historical tutorial chapter | Archive under `docs/archive/tutorial/`. |
| `tutorial/src/README.md` | Historical tutorial entry presented as current | Archive original and replace with a status page. |
| `tutorial/src/SUMMARY.md` | Historical mdBook navigation | Archive original and reduce active summary to the status page. |

## Follow-up work not hidden by this PR

1. Decide whether to remove or redesign the legacy LSP behavior in the VS Code
   and Zed manifests, extension clients, and release workflow.
2. Add a Markdown link/status checker that rejects current documents linking
   into `docs/archive/` as implementation authority.
3. Add end-to-end `grc-stage0` CLI tests for help, command-specific option
   validation, exit codes, diagnostics, output contracts, and guest argv.
4. Resolve standard-library conformance questions with executable tests rather
   than another prose specification.
5. Update self-host status only through the module ledger, generated semantic
   map, and checked convergence evidence.
