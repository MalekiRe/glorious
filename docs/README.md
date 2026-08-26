# Glorious documentation map

**Status:** current navigation and authority map  
**Review trigger:** any new Markdown file, renamed subsystem, or changed public
command

This page is the entry point for repository documentation. Its purpose is to
prevent design proposals, worktree reports, benchmarks, and retired
implementations from competing with current contracts.

## Precedence when documents disagree

Authority is scoped to the question being answered:

1. **Current implementation contracts** answer what the repository executes
   now. Code, tests, checked fixtures, machine-readable ledgers, and
   command-line parsing win over prose that claims an implementation exists.
2. **Normative specifications** answer what the language or artifact is
   intended to mean within their stated scope. They do not imply that Stage0
   implements every rule; a mismatch is a conformance gap.
3. **Active plans** describe intended work and completion gates. They are not
   implementation status unless backed by a ledger or test.
4. **Proposals** explore future designs. They must not be cited as current
   behavior.
5. **Measured snapshots** record one commit, environment, and procedure. They
   are evidence, not timeless project status.
6. **Historical records** are preserved under [`archive/`](archive/) and have
   no current authority.

The detailed maintenance rules are in
[`documentation-policy.md`](documentation-policy.md).

## Current implementation and format contracts

- [`architecture.md`](architecture.md) — current repository architecture and
  active component boundaries.
- [`../crates/grandiose-stage0/README.md`](../crates/grandiose-stage0/README.md)
  — Stage0 compiler command and correctness contract.
- [`../crates/grandiose-vm/tests/fixtures/README.md`](../crates/grandiose-vm/tests/fixtures/README.md)
  — checked VM fixture-generation contract.
- [`bytecode.md`](bytecode.md) — GVM1 bytecode format reference. VM code,
  verifier tests, and checked fixtures resolve implementation drift.
- [`../self-host-stage0/README.md`](../self-host-stage0/README.md) — local
  no-fallback contract for the self-host source tree.
- [`../self-host-stage0/src/README.md`](../self-host-stage0/src/README.md) —
  source-directory rules for the self-host mirror.

## Normative language design

- [`../glorious-branded-environment-core-spec.md`](../glorious-branded-environment-core-spec.md)
  — Generation-1 branded-environment core semantics.
- [`std-lib.md`](std-lib.md) — canonical Generation-1 standard-library design.

Normative design and implementation completeness are separate claims. When the
Stage0 implementation differs, record the gap rather than silently rewriting a
specification to match an accident.

[`new-stdlib.md`](new-stdlib.md) is now a supersession notice; its original,
overlapping proposal is archived.

## Current self-hosting program

- [`self-hosting.md`](self-hosting.md) — single current status and navigation
  page.
- [`glorious-stage0-self-hosting-plan.md`](glorious-stage0-self-hosting-plan.md)
  — active migration plan and completion gates.
- [`self-host-stage0/primitive-boundary.md`](self-host-stage0/primitive-boundary.md)
  — frozen primitive/host boundary for the port.
- [`self-hosted-compiler/stage0-semantic-test-map.md`](self-hosted-compiler/stage0-semantic-test-map.md)
  — generated semantic inventory; not a completion score.
- [`self-host-stage0/performance-baseline.md`](self-host-stage0/performance-baseline.md)
  — dated measured snapshot, not current status.
- [`../self-host-stage0/baseline.toml`](../self-host-stage0/baseline.toml) and
  [`../self-host-stage0/module-ledger.toml`](../self-host-stage0/module-ledger.toml)
  — machine-readable baseline and module state.

Old `self-host/`, native LLVM/Wild, and pre-Stage0 parity reports are archived.

## Active proposals

These documents describe future architecture. They are useful inputs, not proof
of implementation:

- [`frontend-design.md`](frontend-design.md)
- [`mir-design.md`](mir-design.md)
- [`self-hosted-compiler-snowflake-stage-one.md`](self-hosted-compiler-snowflake-stage-one.md)
- [`self-hosted-compiler/README.md`](self-hosted-compiler/README.md) and the
  incomplete snowflake chapter series it indexes

The original 1.4 MB generated snowflake compendium is preserved in the archive.
The file at its former path is a small index so generated prose is not mistaken
for maintained current documentation.

## Local and historical guides

- [`../editors/README.md`](../editors/README.md) — editor integration status.
  Syntax assets remain; `grand-lsp` is legacy and unsupported.
- [`../tutorial/src/README.md`](../tutorial/src/README.md) — historical tutorial
  status. Its `grand`/`grandfmt`/old compiler workflow is not runnable against
  the active workspace.
- [`../tooling/LEGACY.md`](../tooling/LEGACY.md) — boundary around retained
  legacy tools.
- [`archive/`](archive/) — reports, retired implementation documents, design
  records, tutorial chapters, and generated material.

## Maintenance rule

Every new document must have one owner, one status, and one reason to exist.
Do not create a second roadmap, parity report, standard-library specification,
or current-status page when an existing canonical document can be updated.
