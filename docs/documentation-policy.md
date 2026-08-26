# Documentation policy

**Status:** current repository policy  
**Owner:** maintainers of the subsystem named by each document

This policy keeps the documentation set navigable and prevents historical
claims from becoming accidental specifications.

## Required status classes

Every new or materially rewritten Markdown document must identify one class:

- **Normative specification** — defines language or artifact semantics in a
  bounded scope.
- **Current implementation contract** — describes behavior exercised by current
  code, tests, fixtures, or machine-readable state.
- **Active plan** — defines intended work, dependencies, and completion gates.
- **Proposal** — explores a design that is not current behavior.
- **Measured snapshot** — records a dated measurement tied to a commit,
  environment, commands, and inputs.
- **Historical record** — preserves context but has no current authority.

A document may not be both a proposal and an implementation contract. A plan
must not call a feature complete unless an identified test or ledger supports
that claim.

## Authority and scope

- Code and tests resolve claims about what the current compiler, VM, CLI, or
  editor integration actually does.
- A normative language specification may intentionally describe behavior not
  implemented by Stage0. Such gaps should be tracked explicitly.
- A local README owns only its subtree. It must not redefine repository-wide
  status.
- Generated inventories and ledgers own the facts they generate. Hand-written
  prose should link to them instead of copying counts.
- Historical files may contain stale paths, commands, and conclusions. They
  must live under `docs/archive/` and must not be linked as current guidance.

## One source for each recurring question

Maintain exactly one current answer for each of these questions:

- What code is active? — `README.md` and `docs/architecture.md`.
- Which document wins? — `docs/README.md` and this policy.
- What is the current self-hosting status? — `docs/self-hosting.md` plus the
  machine-readable ledgers.
- What is the canonical standard-library design? — `docs/std-lib.md`.
- What commands does Stage0 accept? — the Stage0 CLI parser and
  `crates/grandiose-stage0/README.md`.
- What editor tooling is supported? — `editors/README.md`.

## Snapshot requirements

A benchmark, audit, readiness report, or performance comparison must include:

1. an absolute date;
2. the commit or tree being measured;
3. exact commands and inputs;
4. relevant toolchain and platform information;
5. a statement that the result is a snapshot, not current status.

If those facts are unavailable, archive the document as provenance rather than
presenting it as evidence.

## Link and lifecycle rules

- Prefer relative links to canonical documents.
- When replacing a large or widely referenced document, leave a short
  supersession notice at the old path or provide an obvious archive index.
- Archive reports once their underlying code layout, command surface, or
  completion model no longer exists.
- Delete generated prose from the current navigation surface when a concise
  index plus source ledgers can express the same state.
- Review this map whenever a crate, binary, directory, public command, or
  self-host phase changes.

A documentation change is incomplete when it creates two plausible sources of
truth.
