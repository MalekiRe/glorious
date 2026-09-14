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
  type, resources and the real caller event trace. Neither the payload before
  `AddressType` nor an independent layout realization is assumed: both physical
  facts follow from world typing and actual source resolution. Logical
  interpretation follows from entry-produced context admission, not a
  separate reading certificate or fabricated runtime equality.
- `ControlOrigin`, `ControlOriginPreservation`: actual current and captured
  control-address and historical authority support, canonical invocation admission
  and whole-run preservation. NOT checked at this revision: the module is
  unimportable because its closure still contains the stale `ForeignAuthority`
  (renamed `Reachable.pointer` constructor, rewritten `AccessSeed`, removed
  `FreshExposed`, `liveLoan_origin`'s fourth fresh-root disjunct), so
  `Execution.Step.controlWellFormed`, `Run.controlWellFormed`, `Observes.control`,
  `Diverges.control` and `Specification.reachable_control` are stated but not
  exercised; the earlier note calling them re-verified was wrong.
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
  payload's resources stay accessible in the result world. `RawRead.copy_exists`
  now constructs the real copy from explicit duplicability and shared readiness,
  retaining the source and producing an initialized owned-view-ready result.
  `RawBorrow.exists` uses the common checked loan producer, original support
  and new-view compatibility to construct the actual accessible reference.
  Both reach `PrimitiveStep` and `Step`. Pointer offset/address replacement
  likewise construct the bounded result and real destination write, retaining
  provenance and generation; replacement derives its unsigned bound from the
  actual scalar operand. Address inspection derives its bound from the typed
  pointer resident without granting dereference permission. Existing layout
  progress is reused unchanged. The raw/layout gate passes 179 jobs; sixteen
  general axiom audits report standard axioms only. Overlapping bulk-move
  construction, missing primitive dispatch and source/task admission remain open.
- `LoanPreservation`, `CopyResourcePreservation`: all owning loans are unique,
  owning/storage-borrow rows retain custody, and actual loan mutations preserve
  that common invariant. Ordinary copies retain their shared resource closure.
  The source-admitted copy construction is now `CopyProgress` below.
- `LoanCompatibility`, `InputBindingProgress`: exact pre-state compatibility
  characterizes permission survival under fresh loans and claims. The real
  six-case input binder constructs success or physical exhaustion from positive
  readiness and storage requests; erased ports require no invented allocation.
- `InputBatchProgress`: `Kernel.BatchPrepared.attemptFor` constructs the
  ordered complete-or-exhausted binder while retaining pending inputs and
  earlier outputs through actual loan, claim, custody and storage changes.
  `Kernel.EntryBatch.enterWorldAttempt` constructs the real entry attempt and,
  on completion, derives receiver retirement from the actual capture transfers.
  Receiver addresses may be projected; ordinary and raw inputs share the fold.
  Callable typing supplies capture arity and the empty shell-resource list.
  No future-world finishing callback, pre-emptied captures or assumed successor
  remains. This prepared-phase theorem is now consumed by
  `EntrySource.Admitted.enterWorldAttempt`: original-world recipe readiness,
  positive requests, input interference, incoming resources and owned-receiver
  compatibility construct every real entry outcome. Fresh-lifetime creation,
  authority-changing captures, ordered binding and receiver retirement are
  composed; no intermediate-world admission is supplied.
  `EntrySource.Admitted.enterStep` consumes the same finite admission in the
  actual non-tail machine step, including exact-prefix physical exhaustion.
  Proper-tail caller cleanup and the general `InvocationStart` consumer are
  now constructed below from original-world admission.
- `BodyInventory` also validates unsafe caller-contract declaration ownership
  (§15.1): an attached contract must name an unsafe function declaration.
  `Instance.unsafe_contract_none` derives absence for safe selected bodies;
  no attached predicate is ignored. The canonical declaration-selection proof
  is shared at `Kernel`, and destructor-handle privacy now consumes the real
  `.destructor` loan purpose. The integrated gate including `DropHandle` passes
  221 jobs. `Authority.carriers` now distinguishes explicit access authorities
  from inherited loan dependencies. Reference/resource views no longer expand
  inherited guards into independent permission checks. The general
  `Permitted.referenceView_iff` and `resourceView_iff` contracts prove exactly
  which permissions remain required. Ordered-input, control, pattern and
  suspension consumers use the common corrected views; obsolete guard-frame
  products and their duplicate observations are removed.
- Created-reference readiness now follows the actual loan graph. The common
  carrier-preserving rebase derives full reference/resource access for a new
  handle; `FormsLoan.handed_off_ready` frames the original source across the
  actual write and fresh loan. `Temporary.borrowed_handle_ready` discharges
  fresh-slot separation from the real allocation.
  `LocalStep.hook_inputs_admitted` consumes these producers and actual private
  storage to construct the complete destructor input product: initialized
  singleton handoff readiness, real formal coordinates, the actual positive
  allocation request and the safe selected declaration's caller contract.
  Source readiness and prospective-row view compatibility remain finite
  original-world requirements, not assumed after-world readiness.
- `InvocationStart` carries the actual recipe's `EntrySource.Admitted`, its
  selected declaration and original caller cleanup admission for proper-tail
  tasks. `InvocationStart.step` derives an actual ordinary or proper-tail
  successor, including physical exhaustion. The isolated producer consumes
  the same product and canonical input root bounds; the headed-authority side
  condition and its module are removed. Current/saved authority preservation
  now covers guarded relocation,
  carried caller contracts, raw return bindings, cleanup queues, and actual
  host transaction outputs rather than endpoint-derived fresh exposure.
  `EffectStep.recorded` and `Step.recorded` retain historical rows even at the
  real fatal prefixes; they do not claim completed suspension ownership there.
  The combined `DropHandle`/`ControlAuthorityForeign`/`ResumptionPreservation`
  gate passes 163 jobs; ordinary entry, actual Drop input, saved/historical
  recording and published-output axiom audits report standard axioms only.
- Whole-control provenance now follows the actual raw inputs, returned caller
  contexts, cleanup queues and ordered host outputs. Buffer root bounds and
  activation homes share the real allocation/claim-release producers; the
  superseded availability proof is removed. The `ControlOriginPreservation`
  gate passes 173 jobs. Terminal inversion, nonfatal-path derivation, complete
  control preservation, divergence, published-root and activation audits use
  only standard axioms. `Step.controlWellFormed` and its run consumer require
  non-resource-fatal execution. General observations/reachability retain
  complete control or the actual resource-fatal terminal; infinite execution
  derives safety from its real successors. The blanket “every run is nonfatal”
  assumptions are removed from suspension consumers. Immutable saved control
  still excludes future roots at fatal endpoints.
  Ambient host registry/callback preservation now covers actual indexed
  mutation publications and all terminal prefixes without assuming complete
  after-control. The actual Drop dispatch constructs finite invocation
  admission in the ambient machine. The combined `DropInvocation` and
  `DropSuspension` gate passes 181 jobs; registry, callback, dispatch and
  saved-suspension audits use only standard axioms. External root grants are
  carrier-free; a missing parent alone does not exclude explicit guard loans.
  Private-body integration now passes the combined `DropPrivate` and
  `DropSuspension` gate (190 jobs). All six transition families preserve the
  actual private slot and guard, including physical resource-fatal prefixes.
  Internal routing keeps partial suspension above the guard; snapshot copies
  use actual root/loan origins. The invocation and arbitrary-run Drop prefix
  theorems retain this guarantee without assuming complete fatal after-control;
  their audits use only standard axioms. Original source handoff evidence and
  selected Drop admission remain hypotheses, not consequences of arbitrary
  world typing. Source-fact production and whole-task progress remain open.
  External cleanup separation is now integrated as well: `ExternalHomePreservation`,
  `DropPrivate`, `DropSuspension` and `SuspensionContent` pass 199 jobs together.
  External/allocation homes and active saved-root exclusion survive actual
  fatal payload, freeze and replay prefixes without full after-control. The
  general run, retained cancellation and admitted-invocation audits use only
  standard axioms. This proves cleanup separation, not resident liveness or
  whole-program progress.
- Ordinary replay now has `resume_progress` from original-world stored,
  initialized, permitted handoff evidence and one positive layout request. The
  active budget selects final restoration or copying; only copying requires
  the original physical snapshot admission. Both branches construct the real
  replay or exact physical-exhaustion prefix, without future-world readiness
  callbacks. Live shared-row selection itself preserves every original
  permission through copying. Rehome graph and permission producers are shared
  with input, pattern and Drop dispatch consumers; the combined gate passes
  244 jobs, and twelve general audits use only standard axioms. This replay
  result does not establish whole-task progress.
- Returned Drop cleanup now consumes original `CustodyDischarge` and
  `CustodyReleaseReady`, performs the real relinquished shell write and drains
  its pending loans before retiring the unit and saved handle. The retry
  closure admits ordinary/destructor restoration as well as raw storage loans;
  no global raw-only kind restriction or future-world callback is used. The
  result preserves the actual frame stack and ended destructor row. Permissions
  backed by retained resident carriers survive; arbitrary ended-loan permissions
  and an unchanged whole loan table are not claimed. The combined cleanup,
  replay, input, pattern and private/Drop gate passes 256 jobs; twelve general
  audits use only standard axioms. Source/task production of the returned-state
  inventories and private-root evidence remains open.
- `TailEntryProgress` closes proper-tail entry from original caller admission.
  `EntrySource.CleanupAdmitted` checks exact surviving residual invariants,
  finite raw-claim/custody/support exclusions, original custody coverage,
  caller-relevant restoration targets and lent-root separation. Moved-out
  fields impose no surviving custody checks; frozen reference observations
  require closure, not permission. Actual preparation and binding produce the
  custody discharge, exact caller root list and residual resource closure.
  `Suspensible` survives the real custody-return scheduling operation.
  `EntrySource.Admitted.tailStep` constructs the actual tail transition or
  physical-exhaustion prefix; `InvocationStart.step` covers both ordinary and
  proper-tail entry. Isolated and Drop-hook admission use the same contract.
  The integrated invocation/cleanup/replay gate passes 257 jobs; sixteen
  general theorem audits use only standard Lean axioms. Producing original
  admission from source/task invariants and whole-task progress remain open.

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
  and an interpretation, not added source syntax. Whole call-entry totality
  remains open; receiver/witness and ordered-input exhaustion are represented
  and constructed under their concrete pre-state obligations.
- `SnapshotResourcePreservation`, `SnapshotReplayPreservation`: one mixed
  copied/external graph proof derives nominal closure and transitive reference
  restoration, retaining old external allocation ownership. Actual copied
  roots inherit suspension/replay admission and source-admitted cancellation.
  Construction of a physical replay remains open; the post-cancel cleanup
  execution is now constructed (below).
- `CustodyDischarge`, `CleanupDestruction`: the two admission products the
  cleanup rules consume are produced rather than assumed — the discharge
  inventory enumerates a custody's live owning claims with the successor row
  each received through the entry binder's own `ClaimsAllocation` step and
  yields the whole-table `World.CustodyHandedOff` that
  `RelinquishesCustody`/`shellDone` needs, and `World.ReferenceFree` is the
  closed stored-value inventory that discharges the reference premises of
  `ReturnsStorageLoan`/`EndsLoan`, retained by the actual retirements and
  region closures. `CleanupDestruction` runs the destructor and loan-ending
  rules themselves (structural, reference and declared-hook dispatch, the
  field loop, `shellDone`, the endings) and reports each actual outcome, and
  `CleanupRun.cleanup_root_shell` composes them for a captured root holding a
  live shell. Readiness is derived: `World.RootClear` reads the real
  `loans`/`availability`/`roots` tables instead of `CanEndStorage` and yields
  both the retirement's endability and the destructor's owning permission, its
  loan clause follows from the endings that discharged a root, and
  `RegionCanEnd.of_discharged` derives a region's readiness from the
  retirements and endings performed. Full recursive destructor assembly
  remains open; arbitrary source Drop hooks are not claimed terminating.
- `CleanupDrain`: the general destructor continuation. `CleanupRun.release_queue`
  executes the pending-return list `shellDone` schedules to its task with the
  machine's own `releaseLoan` rules, including the parent/guard retry: a silent
  rule consumes its head, an ending rule ends the loan and re-inserts the
  recorded dependencies, and the well-founded measure is the pair (live loans,
  queue length) — silent steps shorten the queue, ending steps strictly reduce
  the live-loan count. `World.ReleaseReady` is scoped to the actual seeds and
  recorded parent/guard retry closure, retaining original ordinary/Drop
  initialization and resource restoration through each ending.
  `World.CustodyReleaseReady.requested` and `World.ReleaseReady.write_empty_shell` derive that
  admission through the actual relinquishment and clear. `release_custody_returns`
  reports the exact resulting world with all other state fields unchanged and
  the stronger `LoanReleaseFrame`: rows and metadata remain, liveness can only
  turn off, and dead bookkeeping is retained.
  `CleanupRun.cleanup_root_shell_retired` composes the captured shell's
  destruction, the relinquishment, the drain and the root's actual retirement
  into one run, transporting the retirement's endability through the drain's
  release frame. `ForeignRootFraming` and `InvocationLeaseCleanup` were migrated
  to the current storage/task shapes (the stale `EndsLoan` argument, the
  allocation-claim release, `ResolvedPlace` roots) so the `Step`-level control
  lane can be built again; the unused, unprovable `InitializedAncestors`
  recursion and the unused `referenceRoot_cleanup`/`lendsResident_cleanup` chain
  were removed rather than re-established, since `EndsLoan.restored` now carries
  `ResourcesClosed`, which that obligation did not supply.
- `CleanupDrain` (continued): the destructor recursion's inventory and first
  transport are checked — `World.Destroys` is the inductive tree predicate (a
  stored disposable shell whose fields are holes or further destructible
  residents, with the owning permission and the pending-return readiness of its
  custody) and `World.Destroys.write_disjoint` shows a write apart from the whole
  subtree preserves it (shell, permission, loan-table readiness and every child,
  with the prefix law chaining the apartness). The recursion theorem
  (`CleanupRun.destroy_tree`) that consumes them is NOT yet stated. The
  relinquishment frame is done: `World.restamp`/`World.RequestReturns.get_eq` read
  the relinquished table as the old table restamped, and
  `World.RequestReturns.frame_set`/`frame_set_none` show an ending row commutes
  with that map (every other row untouched; at the ended identity the restamping
  decision reads only the custody and the kind, neither of which an ending
  changes). `World.Destroys.end_loan` is the kill transport on top of that frame:
  an ending only kills a row, so the owning permission's raw-table exclusion and
  the pending-return clauses still hold (the latter read earlier living rows
  through `frame_set`/`frame_set_none`). Still to write: the reversed-index field
  loop and the recursion theorem. The loop's remaining design point is exact: a
  node's destruction must report a *footprint* — its writes are confined to the
  subtree's own slots (so the landed `World.Destroys.write_disjoint` transports a
  sibling's readiness across them) and its endings are confined to its own
  custody's rows (so `World.Destroys.end_loan` transports it) — because the
  transports need that relation between the child's produced world and the world
  the next sibling is read in; `CleanupRun.destroy_tree` then follows by induction
  on the tree with that footprint conjunct carried through the field loop. The
  address half of that push-down is checked: `Address.child_not_prefix` (different
  children are prefix-incomparable), `Address.Prefix.not_outer` (transitivity),
  `Address.child_prefix_grandchild` (a descendant of one child is only reached from
  that child) and `Address.Prefix.comparable`; the inventory's readiness clauses
  now read the raw loan table so the transport is conversion-free; and the frame
  itself is checked: `World.DestroyFrame` (outside the subtree neither the read nor
  the resolved root changes, the loan table keeps every row, and every live row of
  the result is a live row of the original with the same kind, mode and referent)
  with `World.Destroys.of_destroy_frame` transporting a whole subtree's inventory
  across it, which subsumes `write_disjoint` and `end_loan` as single-step
  instances. What remains: the frame's composition along a run (`DestroyFrame`
  transitivity) and its per-rule instances for the destructor chain
  (destroyStructural/fieldNext/fieldsDone change nothing; the shell write and the
  relinquishment satisfy the outside clauses and keep every row, with the restamp
  parent/guard lemmas; each `releaseLoan` ending is a kill), then the reversed-index
  loop and `CleanupRun.destroy_tree`, then the composition with
  `cleanup_root_shell_retired`.
- `RealizationLayout`, `SourceAddress`, `AllocationPreservation`: the physical
  bridge is integrated with world typing. `WorldTypedWithOrigins` requires an
  admitted layout for every live root, including vacant allocations. Initial
  input admission carries that invariant; the allocator establishes each new
  root fact, and actual mutation, retirement, rehome, replay and runtime
  renaming preserve it through whole-machine `Step`/`Run` and public reachable
  world typing. `World.representation` derives `TargetRepresentation`; the
  source projection/place proofs and label consumers no longer require an
  independent `World.LayoutRealized` certificate. Actual resident counts and
  nominal/alias layout derivations supply the physical field offsets.
- `ScopedInterpretation`, `ContextTyping`, `SourceInterpretation`: logical
  source admission is integrated. The general `Entails.decode_scope` proof
  transports all sixteen mutual static judgments, including quantified
  predicates, hygienic substitution, associated projections and greatest
  capability evidence for non-injective scope images. Arbitrary predicate
  templates and substitution values are both mapped; only actual declared
  requirements are fixed by declaration closure. `Kernel.Instance.predicates`
  discharges the entered signature from the actual `ConstraintsHold` evidence.
  `ContextBindingsTyped` records that admission, completed generic
  instantiation and the source kinding level; actual entry and context
  transitions produce and preserve these facts. `conversionClosed` derives
  runtime definitional equality from them. Both source address bridges and
  both label consumers now require no independent logical-reading premise.
  The old callback-based interpretation certificates are removed.
- `InitialInvocation.of_empty_resumptions` consumes the same finite entry
  admission as ordinary entry. Authority records come from its actual input
  product; storage bounds use `InvocationInput.ReadyFor.root_bound`. The old
  headed-share restriction, duplicate root-bound analysis and superseded
  `InputAuthorityProvenance` module are removed.
- `SuspensionCapture`: the suspend-time capture admission produced from the real
  suspend instructions and the actual continuation-handle allocation, with the
  fresh frame's side condition taken from the machine's live-loan law and the
  value's restoration closure made hereditary; captured-content freezing across
  intervening steps, control-region liveness and external scoping remain open.
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

The integrated physical, logical and entry-preparation checkpoint passes this proof gate:

```sh
lake build GloriousLanguage.InputBatchProgress \
  GloriousLanguage.SemanticPreservation GloriousLanguage.SourceAddress \
  GloriousLanguage.LabelExecution GloriousLanguage.AllocationLayout \
  GloriousLanguage.RuntimeWorldEquivariance GloriousLanguage.SnapshotReplayPreservation \
  GloriousLanguage.FunctionEntryContextTyping GloriousLanguage.AllocationExecution \
  GloriousLanguage.PrivateStorage GloriousLanguage.ActivationStorageOrigin \
  GloriousLanguage.ControlAuthorityStorage
```

The strict gate passes 220 jobs. Axiom audits of general scoped logical
transport, actual instance/entry admission, lexical context preservation,
source conversion, both source address bridges, both label consumers, whole
`Step`/`Run` preservation and public reachable-world typing report only
`propext`, `Classical.choice` and `Quot.sound`. The audited signatures derive
physical realization from `WorldTyped` and logical interpretation from the
entry-produced `ContextBindingsTyped`, without a separate reading callback.

`FunctionEntryContextTyping` is now repaired and included. Its actual entry
result preserves the source body context on success, the caller custody-release
prefix and inherited contracts on proper-tail success, or the exact exhausted
world and consumed fresh identities on resource failure. Resident, contextual
and foreign callback consumers share this result, including nonempty erased
resource inputs. Their axiom audits also report only the standard three axioms.
`PreparesEntryAttempt` now represents receiver-lease exhaustion and contextual
witness-lease exhaustion, retaining the first successful lease when the second
fails. `EnterWorldAttempt` consumes either that actual failure or successful
preparation followed by the ordered input fold. Both phases preserve world
typing, suspension state, activation bounds and private storage. Exhaustion
derives a positive physical allocation failure in the retained world. Entry
exclusivity distinguishes fatal preparation failure from acquiring a real loan.

Privacy uses the original recipe footprint: an erased port may name vacant
storage, so vacancy alone cannot establish input exclusion. Authority provenance
likewise comes from the original recipe, including guard carriers, and survives
the actual preparation, binding and receiver-finishing phases. It is not inferred
from an erased loan port's parent identity alone. The general entry-invariant
axiom audits report only the standard three axioms.

`EntrySource.prepare` constructs every supplied, resident and contextual
preparation outcome. `FormsLoan.borrower_permitted` derives the new borrower
authority; capture permissions follow through its real projections. Contextual
preparation transports witness requests, reachable resources and the frozen
reservation product through the receiver lease, then constructs both actual
consumption writes. The two physical failure sites retain their exact prefixes.
Receiver and witness frames use the same actual loan producer as ordinary
inputs, without invented receiver locals or future-world readiness. These
general construction and input-observation audits use only the standard axioms.

`PreparesEntry.contextual_inputsCompatible` preserves the whole original
readiness, physical-request, authority-record and pairwise-interference product
through both loans, receiver marking, and witness clearing/deactivation. Its
compatibility and mutation exclusions are all original-world facts. The common
observer reads resident contents only for resident formals: erased ports at the
cleared witness slot survive without fictitious unchanged values. Receiver
marking preserves physical offsets and live slots at arbitrary projection depth
using actual ancestor heads and field arities. `InputFramed` is now derived
from the authoritative input product rather than separately admitted by entry.
The contextual, physical-transport and entry axiom audits use only the standard
three axioms; the integrated 220-job gate passes.

`PreparesEntry.inputsCompatible` now closes original-to-prepared input transport
for all three recipes. Resident captures use the actual borrower authority,
source region and inherited guards; their readiness, physical requests and all
five pairwise interference channels are derived before composing the receiver
write. `EntrySource.prepareInputs` constructs the actual outcome and publishes
that product on completion under the same original-world `PreparationConditions`.
The permission observer follows actual formal reads: resident/storage access,
guarded allocation opening, and no fictitious pointee access for ordinary
allocation or raw-loan handoff. The obsolete separate owned-permission channel
and its helper are removed. The general all-source, resident-product and
ordered-binder axiom audits report only the standard three axioms.

Input-resource preconditions now belong to the original invocation boundary.
Both `EnterWorldAttempt` constructors require `IncomingResources` in
`before.world` over `source.originalInputs`; preparation exhaustion cannot
bypass that check. An arbitrary unsafe input predicate is not transported
through receiver/witness mutation. The entry producer derives prepared key
uniqueness from the actual coordinate theorem and original admission, removing
its separate prepared-input `Nodup` premise. The phase-preservation consumers,
strict 220-job gate and general entry/exhaustion/preparation axiom audits pass.

The preserved `Checks` were not run. This is general proof checking, not example
evidence, a whole-library success or source-wide progress. Higher task/frame
consumers are still being migrated and are not included in this gate. Deriving
the concrete preparation conditions and original resource preconditions from
source admission, transporting fresh-lifetime requests, and deriving receiver
fresh-row compatibility for actual entry remain on the same dependency chain.

Earlier recovery checkpoints used this target set:

This historical command includes the now-retired `InputAuthorityProvenance`
target; it is not a current verification command.

`lake build GloriousLanguage.CleanupExecution GloriousLanguage.SnapshotPlacement GloriousLanguage.SnapshotPlacementConstruction GloriousLanguage.SnapshotReplayConstruction GloriousLanguage.SnapshotReplayProgress GloriousLanguage.SnapshotCopyConstruction GloriousLanguage.CleanupPreservation GloriousLanguage.ForeignEvolution GloriousLanguage.InvocationLending GloriousLanguage.ResumptionPreservation GloriousLanguage.SourceAddress GloriousLanguage.LabelExecution GloriousLanguage.InputBindingProgress GloriousLanguage.LoanCompatibility GloriousLanguage.LoanResourceRows GloriousLanguage.CopyProgress GloriousLanguage.RawMutationProgress GloriousLanguage.SemanticPreservation GloriousLanguage.SnapshotReplayPreservation GloriousLanguage.OperationExecution GloriousLanguage.BufferReallocationProgress GloriousLanguage.PublicValues GloriousLanguage.CustodyDischarge GloriousLanguage.CleanupDestruction GloriousLanguage.InputAuthorityProvenance GloriousLanguage.SuspensionCapture GloriousLanguage.RuntimeWorldEquivariance GloriousLanguage.ReferenceTransferPreservation GloriousLanguage.SnapshotResourcePreservation GloriousLanguage.AllocationFraming GloriousLanguage.CopyResourcePreservation`

which passed 232 jobs from a fresh source-only tree at the previous revision;
that count and target list were not re-exercised at 7bc81b08. The targets
actually built and green at 7bc81b08 are the changed closure:
`GloriousLanguage.CleanupDrain`, `GloriousLanguage.CleanupDestruction`,
`GloriousLanguage.CustodyDischarge`, `GloriousLanguage.ForeignRootFraming`,
`GloriousLanguage.InvocationLeaseCleanup`, `GloriousLanguage.RealizationLayout`,
`GloriousLanguage.AllocationLayout`, `GloriousLanguage.SourceInterpretation`,
`GloriousLanguage.SourceAddress`, `GloriousLanguage.LabelExecution` (184 jobs,
strict flags). The four frame consumers alone check as 80 jobs. Warnings are errors and implicit identifier creation is
disabled. The default aggregate also includes the preserved `Checks`; examples
are not routine evidence for this semantic proof phase. No `sorry`, new axiom,
evaluator fuel bound, or always-rejecting implementation counts as a completed
specification.

The whole library is not green and is not claimed to be. `ForeignRootFraming`
and `InvocationLeaseCleanup` now check inside the graph; the stale frontier is
larger than the thirteen modules previously recorded here, because any module
that transitively consumes `BasicChecks` or still uses the pre-migration
`EndsLoan`/`ForeignAuthority` shapes also fails (for example `ForeignAuthority`,
`ActivationStorageOrigin`, `SuspensionStorage`, `PrivateStorage` and the `Checks`
aggregate). The exact list has not been enumerated at this revision. The modules
below are stale consumers of earlier storage/task shapes and are not evidence
for or against the recovered boundary.

`PublicValues`, `RuntimeWorldEquivariance`,
`CleanupPreservation`, `ForeignEvolution`, `InvocationLending` and
`ResumptionPreservation` left that list: each was migrated to the current
storage, task, entry-attempt and public-observation shapes and now check inside
the graph.

Checking that definitions and sample propositions elaborate is different
from proving determinism, type soundness, adequacy of every source rule,
or compiler correctness. See `COVERAGE.md` for the audit boundaries.
