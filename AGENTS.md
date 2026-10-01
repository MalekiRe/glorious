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

## Serial work only: no subagents

Do all work yourself, serially. Do not launch subagents, delegate proof or
implementation work, or run parallel worker lanes. The user explicitly requires
this because subagent output has introduced sloppiness and integration risk.
This rule applies across sessions and may change only with explicit user approval;
requests to continue or finish all work do not authorize delegation.

## Lean specification: purpose and working method

The goal is to provide a semantic Lean definition of the compiler's intended
language semantics and correctness contract **before implementing the compiler**.
Prioritize faithful semantic definitions and general proofs, not implementation
work or a growing collection of examples.

- Unit tests and test-style concrete examples are not useful as routine evidence
  for this phase. Do not add or run them routinely. Use them only in extreme
  cases, such as isolating a specific suspected modeling error that cannot
  readily be addressed by the general proof. Preserve existing work.
- Running Lean to verify definitions and proofs is necessary proof checking,
  not unit testing. Establish the general theorem; neither example counts nor
  successful builds alone establish semantic soundness.
- Take on large, dependency-coherent chunks, hardest obligations first. Aim to
  close an entire difficult semantic boundary, carrying prerequisite lemmas
  through to the general preservation, progress, or correctness result that
  consumes them. Treat helper lemmas as intermediate steps, not the default
  checkpoint or deliverable.
- Be aggressive about scope and sustained proof progress without weakening
  guarantees, assuming the desired conclusion, or claiming unfinished work is
  complete. When a boundary remains open, identify the exact remaining proof
  obligation and continue along that same dependency chain.

For Lean specification work, this section overrides the routine positive and
negative testing guidance below; that guidance still applies to compiler
implementation work.

## Lean specification reset: mandatory durable requirements

The active specification development is `formal/semantics/`. Its single
authoritative proof plan is [PROOF-PLAN.md](formal/semantics/PROOF-PLAN.md).
The existing `formal/spec/`, `formal/grounded-spec/`, and `formal/lean/` trees
are preserved reference work, not concurrent development tracks or evidence
that the new development has proved their guarantees. Do not delete them or
resume work there without explicit user direction. Reuse code only after
auditing its semantics, premises, producers, and actual consumers. Do not copy
an old admission architecture into the new folder to obtain a quick build.

### No temporary work

- Every implemented definition, proof, and interface must be intended as a
  permanent part of the correct solution. Iteration extends correct coverage;
  it must not accumulate shortcuts to replace later. Necessary corrections to
  newly discovered mistakes are not permission to knowingly introduce them.
- No temporary assumptions, `sorry`, `admit`, unapproved axioms, placeholder
  implementations, fake fallbacks, special cases, duplicate semantic paths,
  or weakened guarantees to get a proof through. Do not hide an unproved
  obligation behind a structure field, callback, typeclass, or admission
  predicate and describe the consumer as having discharged it.
- Incomplete coverage must remain explicitly unproved. A target theorem may
  be recorded as a design obligation in the proof plan, never installed as an
  axiom or admitted declaration. Conditional lemmas are legitimate only when
  their premises are explicit and their intended producers are identified;
  they do not close a boundary until those producers are connected.
- Repair an incorrect contract and migrate its real consumers coherently.
  Remove mechanisms superseded by that cutover; do not retain compatibility
  wrappers around known-wrong interfaces. Preserve unrelated work.

### Modular, extensible proofs

- Separate facts that have different preservation conditions: resource
  correspondence, ownership/provenance, initialization/readiness, and current
  operation permission. Do not require readiness at every intermediate state
  merely because that makes an induction easier. Derive its exact use, call,
  transfer, and cleanup requirements from the normative language semantics.
- Each operation contract must state its current-state requirements, actual
  transition, preserved invariants, resource changes, and effects on unrelated
  resources and previously produced values. Use authoritative storage and loan
  relations, not a second proof-only analysis of the same facts.
- Factor genuine composition boundaries such as sequencing, argument/capture
  evaluation, selected-branch execution, and ordered cleanup. Do not create a
  generic framework merely to make proofs look modular. Organize files around
  semantic responsibilities once their contracts are understood.
- Work in vertical slices: checking rule -> operation construction -> invariant
  preservation -> general theorem case -> public consumer. Supporting lemmas
  are intermediate work, not substitutes for closing that chain.

### Mandatory acceptance gates

1. At session start, read this file, the architecture contract, the relevant
   normative specification, and the single active proof plan. Inspect the
   public theorem and its premises when it exists, the current semantic
   boundary, and the latest verified checkpoint before editing. Never infer
   completion from an archived summary or a successful build.
2. Before implementation, state the intended public theorem, legitimate entry
   evidence, covered language fragment, and outcome distinctions. Do not
   reduce the full-language goal silently or confuse big-step termination
   results with progress for recursion and divergence.
3. For each contract change, explain the defect, its normative justification,
   and the affected producers and consumers. Resolve interacting invariant
   defects together before launching another broad proof rewrite.
4. For every added premise, identify its authoritative producer and where it
   is discharged. Future execution, successful cleanup, progress, and
   successor-state correspondence must not be assumed in place of proving
   them. Legitimate external and current-state assumptions must be explicit.
5. A semantic completion checkpoint must show a connected producer-to-consumer
   result, with strict Lean checking and axiom inspection of the affected
   public result. A checked theorem can still state the wrong contract: review
   premise and signature changes as well as proof acceptance.
6. Record assumptions removed, guarantees established, exercised verification,
   and exact remaining obligations in the proof plan. Distinguish proved
   results, conditional results, suspected defects, and unsupported features.
   Lemma counts, build counts, worker activity, and passing examples are not
   measures of semantic completion. Do not create competing status/handoff
   documents as alternative sources of truth.
7. Keep one owner of the semantic core. Follow the serial-work-only rule above;
   independent tasks or stable interfaces do not authorize subagent use.
8. Before claiming whole-language completion, audit normative coverage, public
   theorem premises, real consumers, and remaining external contracts. No
   compiler implementation or unrelated feature expansion substitutes for
   completing the semantic specification.

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
