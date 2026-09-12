# Formal language specification

This independent Lean project specifies the language described by
`glorious-language-specification.md`. It does not implement a compiler,
import the earlier `formal/lean` compiler draft, or specify/verify library
algorithms. Source-owned libraries are arbitrary programs using the same
language rules as application code. Machine and foreign boundaries are
explicit contracts.

Status: whole-specification draft, in its semantic repair and proof pass.
General proofs now cover storage preservation for every executable transition
and finite execution, invocation loan exclusion and physical lease cleanup,
constructibility of the logical/coinductive capability interpretation, typed public-value observations,
complete code-typing transport for snapshot region renaming, and current/saved
control-address and loan-authority provenance through every machine step and finite run, with
saved-home ownership, actual final/copied replay ownership and opaque host-registry
authority origins, and callback runtime liveness through nested execution and cleanup.
Closed logical equality is proved equivalent to definitional
conversion, and source predicate scope reaches actual match entry and its first
binding/cleanup action. These are
not full-language soundness or conformance: conversion-safe capability inversion,
source lexical/type normalization,
task/frame typing and retained-frame liveness, initialized return lifetimes, resource progress and
complete target contracts remain open. `PROOF-PLAN.md` records the current
hardest-first dependency chain; `DRAFT.md` retains the earlier draft audit.
The earlier compiler work remains reference material, not the foundation
or a dependency of this project.

## Organization

- `Foundation`, `Terms`: quantities, identities, typed terms, substitution,
  unbounded executions and two-way observational refinement.
- `Syntax`, `SourceRules`, `Elaboration`, `Origins`: UTF-8, AST-indexed concrete
  grammar, contextual elaboration, declarations and source authentication.
- `Declarations`, `Static`, `Instantiation`, `Typing`: one declaration
  inventory, resolution, kinds, traits, capabilities, concrete instances and
  structural typing.
- `Storage`, `Kernel`, `Machine`, `Atoms`: one storage world, explicit
  sequencing, invocation, transfers, borrowing and executable cleanup.
- `Effects`, `Relocation`, `Control`, `Contracts`: handlers, continuation
  quantities, snapshots, labels, guarded environments and body-checked
  invocation contracts.
- `ControlOrigin`, `ControlOriginPreservation`: actual current and captured
  control-address and historical authority support, canonical invocation admission
  and whole-run preservation.
- `ControlAuthority` and its producer modules: actual recorded loan authorities,
  reservation provenance, callback leases and mapped replay authority.
- `ActivationOrigin`, its producer modules and `ActivationPreservation`: historical
  home and executable-context bounds, fresh ordinary/clause/snapshot owners and
  the activation component of canonical whole-machine control preservation.
- `ForeignRegistration`, `ForeignAuthorityOrigin`: exact registry transition
  grants, host-indexed initial admission and whole-run historical authority recording.
- `ForeignRuntimeSupport`, `ForeignRuntimePreservation`: actual callback entries,
  retained cleanup barriers, runtime handoff coverage and whole-run runtime liveness.
- `PredicateInterpretation`, `PredicateScope`, `MatchEntryContextTyping`: hygienic
  predicate semantics and source-derived scope through actual selected-arm entry.
- `ClosedDefinitionalEquality`, `HeadOriginDecomposition`: assumption-free equality
  conservativity and positive source origins of actual selected generic bindings.
- `SuspensionOrigins`, `SuspensionOwnership`: authenticated capture homes,
  historical inventories and ownership by the actual replayed cleanup frames.
- `Target`, `Memory`, `Primitives`, `Foreign`, `ABI`: scalar mathematics,
  layouts, provenance, machine leaves, explicit host models and target
  admission requirements.
- `Specification`, `Checks`: aggregate language/implementation obligations
  and foundational positive/negative regression propositions.

`Execution.Step` is the shared executable meaning. It is consumed by control
contracts, semantic admission and source observations. The grammar produces
the AST consumed by elaboration; source origins authenticate the declaration
inventory rather than accepting a separately supplied unrelated AST.

## Checking

Use the pinned toolchain to build the changed proof targets, for example
`lake build GloriousLanguage.ExecutionPreservation GloriousLanguage.PublicValues`.
Warnings are errors and implicit identifier creation is disabled. The default
aggregate also includes the preserved `Checks`; examples are not routine
evidence for this semantic proof phase. No `sorry`, new axiom, evaluator fuel
bound, or always-rejecting implementation counts as a completed specification.

Checking that definitions and sample propositions elaborate is different
from proving determinism, type soundness, adequacy of every source rule,
or compiler correctness. See `COVERAGE.md` for the audit boundaries.
