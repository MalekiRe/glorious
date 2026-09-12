# Formal language specification

This independent Lean project specifies the language described by
`glorious-language-specification.md`. It does not implement a compiler,
import the earlier `formal/lean` compiler draft, or specify/verify library
algorithms. Source-owned libraries are arbitrary programs using the same
language rules as application code. Machine and foreign boundaries are
explicit contracts.

Status: whole-specification draft, in its semantic repair and proof pass.
Earlier verified checkpoints cover storage preservation for every executable transition
and finite execution, invocation loan exclusion and physical lease cleanup,
constructibility of the logical/coinductive capability interpretation, typed public-value observations,
complete code-typing transport for snapshot region renaming, and current/saved
control-address and loan-authority provenance through every machine step and finite run, with
saved-home ownership, actual final/copied replay ownership and opaque host-registry
authority origins, and callback runtime liveness through nested execution and cleanup.
Closed logical equality is proved equivalent to definitional
conversion, and source predicate scope reaches actual match entry and its first
binding/cleanup action. These are
not full-language soundness or conformance: source lexical/type normalization,
task/frame typing and retained-frame liveness, initialized return lifetimes, resource progress and
complete target contracts remain open. `PROOF-PLAN.md` records the current
hardest-first dependency chain; `DRAFT.md` retains the earlier draft audit.
The current raw-resource and allocation-outcome correction changes those
executable contracts. Its checked boundary covers common resident/raw input
binding, actual local execution, source-local context entry, payload-pattern
transport, ordered preparation success/exhaustion and actual source-selected
operation success/resource failure. Common loan-kind/custody preservation and
buffer-allocation progress compose with that boundary. Whole actual execution
and public storage preservation now consume those changed contracts, as do
copied-snapshot resource closure/restoration and replay/cancellation admission.
Other private, control-lifetime and foreign-runtime proofs are being migrated;
their older checkpoints do not establish conformance of this changed graph.
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
- `BindingDomain`, `InputTyping`, `InputLending`, `ContextTyping`: source
  locals are a projection of the same resident/raw binding environment.
  Invocation custody, raw ports and real reference permissions are retained;
  erased resources do not acquire fictitious source locals.
- `OrderedHandoff`, `HandoffPreservation`, `PayloadHandoff`,
  `PatternPlanTransport`: one whole-batch clear footprint through actual
  ordered handoffs, source-selected payload plans and retained reference support.
- `AllocationOutcomes`, `PreparationOutcomes`, `HandoffProgress`,
  `AllocationExecution`, `OperationPayloadPreparation`: positive allocation
  requests produce actual success or physical exhaustion. Failed preparation
  retains its successful prefix and partial world. Entry and payload protection
  share outcome-indexed folds; actual fatal states admit no executable suffix.
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
- `OperationBoundary`: selected
  terminal/resumptive permission shared with actual effect execution; exact
  composition of callee-owned and caller-owned post-payload obligations.
  Positive payload preflight constructs success or exhaustion; routing barriers
  are independent of successful allocation.
- `OperationExecution`: actual terminal, tail-arm and bound-resumption steps
  constructed from those shares and the selected source arm's common mode
  contract, with post-world typing, the actual clause's typed binder cursor and
  the same request's capture lifecycle. Pattern plans and handle initialization
  are derived. Positive allocation requests produce actual success or resource
  failure, retaining payload prefixes and suspended roots; only successful
  suspension establishes the capture lifecycle.
- `OperationSignatures`, `ContinuationCreation`, `StorageConstruction`: actual
  source/request signature conversion, exact continuation brand/result/quantity
  and constructed handle initialization. Continuations and scalar results share
  the common vacant-storage write and empty-input value producer.
- `RootSelection`, `LabelBoundary`: constructive reverse-creation cleanup lists
  for the common storage selection and actual label leave execution from
  callee/caller post-payload permissions, without assuming a completed step.
- `LabelExecution`: the boundary retains the actual first matching route, the
  common singleton resident handoff preflight and a positive allocation
  request. `LabelReady.prepare` consumes `Protect.success_or_exhausted` and
  `LabelReady.execute` constructs the actual `ControlStep.leave` or
  `leaveExhausted` with exactly the unchanged before-world. `LabelRoute.functional`
  fixes the selected delimiter, and `MayTransfer.source_execution` composes
  source `PlaceType`/`Subtype` with the actual moved resident, its physical
  type, resources and the real caller event trace. The explicit before
  `AddressType` and source-assumption interpretation remain theorem hypotheses,
  not runtime equality claims.
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
- `CapabilityInversion`, `CapabilityFields`, `DropCapabilities`: guarded recursive
  capability evidence has a genuine structural origin modulo conversion.
  Transparent expansion is finite; recursive fields share the original evidence.
  Actual resident fields and captures inherit the resulting canonical permission,
  consumed by drop dispatch and hook return. Unique references cannot acquire Copy.
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
  tables, consumed by the complete conversion proof below.
- `HeadInspection`, `HeadInspectionInstantiation`, `InspectionResiduals`:
  source-admitted finite inspection dependencies, preserved through actual caller
  instantiation and root/child and row/root residuals.
- `InspectionPaths`, `InspectionPathResiduals`: fixed paths extracted from those
  source inspections identify actual raw generic values and update actual
  selection through query residuals and a shared raw-table producer.
- `FullHeadInspection`, `FullInspectionSubstitution`, `InspectionCompletion`:
  one full source-inspection minimum retains actual query conversions and derives
  ordinary-to-path-ready completion under real caller instantiation.
- `InspectionParallel`, `InspectionConfluence`, `DefinitionalChurchRosser`:
  ordinary definitional equality has actual positive common reducts, with no
  normalization or simulation assumption. `DefinitionalSeparation` consumes this
  in constructor, scalar, normal-form and actual definitional-quotient proofs.
  Capability inversion and target layout coherence consume this separation.
  Arbitrary lexical equality is not assumed consistent.
- `SuspensionOrigins`, `SuspensionOwnership`: authenticated capture homes,
  historical inventories and ownership by the actual replayed cleanup frames.
- `Target`, `Memory`, `Primitives`, `Foreign`, `ABI`: scalar mathematics,
  layouts, provenance, machine leaves, explicit host models and target
  admission requirements.
- `BufferAllocationPreservation`, `BufferAllocationProgress`,
  `BufferReallocationProgress`, `PointerStorageConstruction`: the actual raw
  allocator establishes its fresh owning loan and typed vacant shell. Positive
  requests construct allocation or the complete old-slot move and old-region
  release, followed by a typed pointer, or an unchanged-world resource fault.
  Reallocation consumes the same positive source admission on both outcomes;
  no successful move, release or typed post-world is assumed. Source admission
  synthesis and progress for the other raw primitives remain open.
- `UnitStorageConstruction`, `BufferReleaseProgress`, `RawMutationProgress`:
  the unit-result installer shares the common vacant write and empty-input
  value producer and derives its typed result, actual write and framing.
  Admitted empty-buffer release constructs the real `PrimitiveStep` release and
  unit result from `BufferAt`, `shellLive = false`, `resources = []`, all-hole
  fields, claim readiness, unreserved availability and region readiness.
  `RawRead.move_exists` and `RawWrite.exists_with_result` construct the actual
  move-read/write and the actual unit installation from the pointer/range
  relation, stored initialized value, `MoveReady` footprint, owned source
  permission, destination vacancy/type and pairwise disjointness; the moved
  payload's resources stay accessible in the result world. Raw copy and raw
  borrow construction, pointer arithmetic and source-admission synthesis remain
  open.
- `LoanPreservation`, `CopyResourcePreservation`: all owning loans are unique,
  owning/storage-borrow rows retain custody, and actual loan mutations preserve
  that common invariant. Ordinary copies retain their shared resource closure.
  The source-admitted copy construction is now `CopyProgress` below.
- `LoanCompatibility`, `InputBindingProgress`: `Authority.LoanCompatible` is the
  pre-state compatibility relation for one newly formed live loan (owning,
  loan, shared and guarded carriers observe the actual pre-world rows and
  guards), and `LoanCompatibility` characterizes exactly when an existing
  `Permitted` survives a fresh loan, a storage claim or an allocation claim as
  `Permitted after ↔ Permitted before ∧ pre-state compatibility`.
  `InputBindingProgress` constructs the actual binder for all six real input
  cases (`BindsInputAt.success_or_exhausted`) from positive
  `InvocationInput.StorageRequest` and `input.Ready` pre-state facts, with
  exhaustion available only for resident allocation. This is not general batch
  or pre-entry progress: compatibility with previously bound outputs, pending
  custody and owning-claim invalidation, the ordered whole-input theorem and
  the source pre-entry derivation all remain open.
- `CopyProgress`: source duplication capability and actual closed initialized
  storage construct the single `CopyTree`/`CopyValue` traversal and its fresh
  owner-origin table (`CopyTree.origins_unique` derives key uniqueness from the
  stored tree's real owner uniqueness), and `Acquires` selects the actual
  copy/explicit-move/default-move branch from the canonical principal.
  `Acquires.allocate_success_or_exhausted` and
  `Copies.allocate_success_or_exhausted` consume one positive `AllocationRequest`
  and return actual allocation plus the actual acquisition, or positive physical
  `AllocationExhausted` for that same request; the actual `AtomStep`/`Step`
  `copy_progress` and `acquire_progress` lift them. Source admission now
  requires `UnsafeInvariantContract.copyResources`: a valid pre-world, the
  contract's holds predicate and actual duplicability imply that the erased
  retained bindings are read-only. This is the formal counterpart of §7.2's rule
  that a structural copy creates an additional owner only for duplicable types,
  applied to the §7.3 unsafe invariant contracts that determine owner behaviour
  for residents not stored syntactically by value; the normative text does not
  enumerate this clause itself, so it is recorded here as a formal obligation
  and an interpretation, not added source syntax. Ordered capture/call-entry
  totality and missing capture-exhaustion outcomes remain open.
- `SnapshotResourcePreservation`, `SnapshotReplayPreservation`: one mixed
  copied/external graph proof derives nominal closure and transitive reference
  restoration, retaining old external allocation ownership. Actual copied
  roots inherit suspension/replay admission and source-admitted cancellation.
  Construction of a physical replay and cancellation execution remain open.
- `BulkMovePreservation`, `MemoryPreservation`, `ForeignPreservation`,
  `SemanticPreservation`: real resident snapshots, raw custody and indexed host
  transactions compose into storage preservation for every actual step/run and
  public reachable, observed, lifecycle and divergent execution. Proof metadata
  uses the ordinary invariant framing law. Raw buffer release must discharge
  retained shell resources and its actual region lifetime obligations.
- `TargetLayoutValidity`, `LayoutValidity`, `LayoutCoherence`: actual ordered
  ordinary/C layouts are valid and unique modulo closed conversion. C enums
  and scalars consume the same exact target mapping. Callable field conversion
  is shared with capability inversion through `LogicalEvidence`.
- `RepresentationCoherence`, `LayoutExecution`: actual encoded values retain
  that layout and exact byte length; the real layout query is deterministic,
  with storage-safe progress conditional on a representable layout and a
  real vacant result destination.
- `LayoutContext`, `AllocationLayout`: actual allocation admits only a closed
  runtime layout; logical cut transports caller metadata. Physical admission
  supplies usize bounds, and allocation, encoding and layout queries agree.
  Explicit exhaustion is now connected to ordinary local allocation, entry
  input binding and ordered operation payloads; complete runtime-site coverage
  and actual source-derived progress remain open.
- `ABIAdmission`: actual loader admission matches the target's layout identity
  and concrete representation bounds. Admitted descriptors derive layout,
  capability and Drop agreement from concrete type agreement; accepted layouts
  supply the real layout query's storage-safe unique progress. Code, relocation
  and complete concrete-site coverage remain separate open obligations.
- `Specification`, `Checks`: aggregate language/implementation obligations
  and foundational positive/negative regression propositions.

`Execution.Step` is the shared executable meaning. It is consumed by control
contracts, semantic admission and source observations. The grammar produces
the AST consumed by elaboration; source origins authenticate the declaration
inventory rather than accepting a separately supplied unrelated AST.

## Checking

Use the pinned toolchain to build the changed proof targets by name, for example
the current recovered checkpoint

`lake build GloriousLanguage.SnapshotPlacement GloriousLanguage.SnapshotPlacementConstruction GloriousLanguage.SnapshotReplayConstruction GloriousLanguage.SnapshotReplayProgress GloriousLanguage.SnapshotCopyConstruction GloriousLanguage.CleanupPreservation GloriousLanguage.ForeignEvolution GloriousLanguage.InvocationLending GloriousLanguage.ResumptionPreservation GloriousLanguage.SourceAddress GloriousLanguage.LabelExecution GloriousLanguage.InputBindingProgress GloriousLanguage.LoanCompatibility GloriousLanguage.LoanResourceRows GloriousLanguage.CopyProgress GloriousLanguage.RawMutationProgress GloriousLanguage.SemanticPreservation GloriousLanguage.SnapshotReplayPreservation GloriousLanguage.OperationExecution GloriousLanguage.BufferReallocationProgress GloriousLanguage.PublicValues GloriousLanguage.RuntimeWorldEquivariance GloriousLanguage.ReferenceTransferPreservation GloriousLanguage.SnapshotResourcePreservation GloriousLanguage.AllocationFraming GloriousLanguage.CopyResourcePreservation`

which passes 224 jobs (the same list without the two compatibility modules
passes 223); the four frame consumers alone check as 80 jobs. Warnings are errors and implicit identifier creation is
disabled. The default aggregate also includes the preserved `Checks`; examples
are not routine evidence for this semantic proof phase. No `sorry`, new axiom,
evaluator fuel bound, or always-rejecting implementation counts as a completed
specification.

The whole library is not green and is not claimed to be. Named targets that
currently fail at this revision are `BasicChecks`, `BindingChecks`,
`ExecutionChecks`, `ControlChecks`, `PreservationChecks`, `SourceChecks`,
`AllocationLayout`, `FunctionEntryContextTyping` and `ScalarMachine`; they are
stale consumers outside the checked dependency graph and are not evidence for
or against the recovered boundary. `PublicValues`, `RuntimeWorldEquivariance`,
`CleanupPreservation`, `ForeignEvolution`, `InvocationLending` and
`ResumptionPreservation` left that list: each was migrated to the current
storage, task, entry-attempt and public-observation shapes and now check inside
the graph.

Checking that definitions and sample propositions elaborate is different
from proving determinism, type soundness, adequacy of every source rule,
or compiler correctness. See `COVERAGE.md` for the audit boundaries.
