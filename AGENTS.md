# Compiler development rules

These rules apply to Stage0, the self-hosted compiler, and their tests and tools.
Read [the compiler architecture contract](docs/compiler-architecture.md) before
changing semantic analysis, intermediate representations, or lowering.

## Highest-priority development constraint

The user considers this the most important instruction to preserve across
sessions for both Stage0 and the self-hosted compiler: **every fix must target
an actual bug or make the compiler pipeline correct**. Do not substitute tiny
one-off patches, side tracks, or parallel information-carrying mechanisms for
repairing the authoritative semantic path. If a boundary is wrong, correct its
contract and migrate its real consumers; remove the superseded path. An unused
fact table, duplicated analysis, or isolated passing test is not that repair.
Incremental work is appropriate only when it advances that same coherent
pipeline correction, with the remaining integration stated explicitly.

## Shared semantics, explicit transformations

- Prefer typed, inspectable data products and composable transformation or
  inference rules over independent procedural reconstructions of semantics.
- Give each semantic fact one authoritative producer. Ownership, lifetime,
  quantity, control-flow, and lowering consumers must share the relevant facts;
  do not add another source/Core walker that independently guesses them.
- Keep transformations, analysis, validation, and runtime mechanisms separate.
  Each phase must declare its required facts, produced facts, and invariants.
- Model captures and ordinary arguments through a common invocation relation.
  Preserve storage identity, execution order, control-flow guards, and distinct
  return, transfer, cancellation, and unknown outcomes.
- Unknown or missing evidence is not proof of absence or permission. Reject an
  unsupported proof obligation rather than weakening a language guarantee.
- Prefer declarative rules where they make the semantics explicit. A rule DSL
  is optional; procedural solvers and runtime machinery are appropriate behind
  well-defined contracts. Do not introduce a new framework merely for syntax.
- Consolidate incrementally: migrate real consumers, remove superseded logic,
  and test composition as well as individual features. A new unused data model
  is not a completed architectural improvement.
- Never change a test or the source language's meaning just to make a new
  representation appear correct. Preserve discovered failing regressions and
  document incomplete conformance honestly.

## Verification and checkpoints

- Keep testing infrequent and focused. Prioritize implementation over repeatedly
  running broad suites; normally check only the changed semantic boundary.
  Reserve broad regression sweeps for occasional major integration checkpoints
  or concrete evidence of a cross-cutting regression. Safety-critical changes
  still need targeted positive and negative checks.
- Test the changed semantic boundary, including positive and negative cases,
  with verification proportional to the risk. Preserve unrelated work.
- Commit and push after every meaningful verified change, or a small batch of
  related changes. Do not accumulate many local checkpoints without pushing.
- A checkpoint may document an existing failing regression; it must not claim
  that a failing acceptance gate passed or that partial work is full conformance.
