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
- `InvocationInputs`, `InvocationBoundary`, `DropInvocation`: the actual entry
  recipe's common input coordinates and caller-delimited execution intervals;
  destructor dispatch establishes admission without erasing ambient frames or
  host exposure. Existing preservation and observation consumers use this boundary.
- `InvocationLifecycle`, `InvocationLifecyclePreservation`: escaped continuation
  creation and cancellation initiation tied to the same actual outward request;
  separate caller traces and preserved capture identity, not internal-event exits.
- `OperationBoundary`: nonvacuous ordered payload protection and the selected
  terminal/resumptive permission shared with actual effect execution; exact
  composition of callee-owned and caller-owned post-payload obligations.
- `OperationExecution`: actual terminal, tail-arm and bound-resumption steps
  constructed from those shares and the selected source arm's common mode
  contract, with post-world typing, the actual clause's typed binder cursor and
  the same request's capture lifecycle. Pattern access and successful physical
  allocation remain explicit.
- `OperationSignatures`, `ContinuationCreation`, `StorageConstruction`: actual
  source/request signature conversion, exact continuation brand/result/quantity
  and constructed handle initialization. Continuations and scalar results share
  the common vacant-storage write and empty-input value producer.
- `RootSelection`, `LabelBoundary`: constructive reverse-creation cleanup lists
  for the common storage selection and actual label leave execution from
  callee/caller post-payload permissions, without assuming a completed step.
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
- `ExternalHomePreservation`: whole-run external/allocation-home preservation,
  actual registration-owner origin and source cleanup/cancellation separation.
- `PrivateStorage`, the private-preservation producer modules, `DropPrivate`:
  actual hook allocation/input entry and complete-machine caller-slot preservation
  up to the first normal caller handoff. The actual selected Drop contract supplies
  interval restrictions, internally handled terminal operations are covered, and
  the original caller suffix is unrestricted.
- `PredicateInterpretation`, `PredicateScope`, `MatchEntryContextTyping`: hygienic
  predicate semantics and source-derived scope through actual selected-arm entry.
- `ClosedDefinitionalEquality`, `HeadOriginDecomposition`: assumption-free equality
  conservativity and positive source origins of actual selected generic bindings.
- `DeclarationDependencyKinding`, `CapabilitySubstitution`, `LogicalSubstitution`:
  kinded declaration dependencies, recursive structural capability substitution
  and hygienic substitution-domain transport through actual logical equality.
- `BinderDefaults`, `DeclarationKinding`: ordered default admission and full
  declaration term-kinding through actual instantiation.
- `StaticAtomTransport`, `LogicalCut`, `LogicalUniverse`: shared static/runtime
  atom transport, assumption cut and larger-universe universal evidence.
- `LogicalPredicateInterpretation`, `PredicateComposition`: admitted predicate
  interpretation equivalent to entailment and exact generic-table composition.
- `AtomInstantiation`, `CapabilityAtomTransport`, `FreshAtomTransport`:
  shared noninjective atom substitution through actual structural capabilities
  and all sixteen mutual static judgments.
- `FreshInstantiation`, `FreshParametricity`: concrete fresh-universe inspection
  specializes to the caller's actual generic substitution, including nested
  universal requirements.
- `GeneralAtomTransport`, `LogicalParameterCut`, `LogicalInstantiation`: general
  hygienic parameter cut, actual generic-table composition and closed equality,
  with derived preimages for caller-only parameters, regions and brands.
- `PositiveSubstitution`, `DefinitionalSubstitution`, `HeadOriginSubstitution`:
  positive reduction and genuine conversion under lawful caller substitution,
  consumed to construct actual implementation selection from admitted source
  origins, including determining alias/projection expansions.
- `HeadOriginInstantiation`, `RootReductionJoining`: instantiated positive
  source origins and root-pair reduction to joining actual selected generic
  tables; global parallel moves and confluence remain unproved.
- `HeadInspection`, `HeadInspectionInstantiation`, `InspectionResiduals`:
  source-admitted finite inspection dependencies, preserved through actual caller
  instantiation and root/child and row/root residuals. Query-premise joining and
  global confluence remain open.
- `InspectionPaths`, `InspectionPathResiduals`: fixed paths extracted from those
  source inspections identify actual raw generic values and update actual
  selection through query residuals. Ordinary-to-path-ready simulation remains open.
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
