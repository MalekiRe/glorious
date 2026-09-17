# Specification audit

## Literal execution and the nominal-view boundary

`LiteralExecution.PrimitiveStep.literal_typed_progress` materializes a
manifest-admitted literal view as the octet tuple the elaborator emits:
typed destination write, world typing, octet leaves, unchanged root/region/
loan frontiers. `PrimitiveStep.literal_nominal_impossible` proves the
constant-value vocabulary cannot produce a nominal library value from an
octet tuple; `Execution.Step.literal_nominal_impossible` extends the
exclusion across every `Execution.Step` family, including foreign entry,
and `Contracts.StateProgress.literal_nominal_impossible` and
`Contracts.ResourceAdmissionAt.no_nominal_literal` carry it to the real
progress/admission obligations. Axiom audit: propext, Quot.sound only.

Honest scope: these are obstruction results. The normative §3.3 contract —
immutable static UTF-8/octet data through an ordinary manifest-selected
library view (normally nominal `Str<'static>`/`Slice<'static,u8>`) with no
forgeable static-segment descriptor — is not yet implemented in this model:
`Home.staticData` is never installed by any rule, and no construction
recipe ties a root's byte image to a nominal value. Extending the machine
to a constructive static-data rule is the declared next obligation; the
obstruction theorems above are then replaced by positive constructibility
statements, since they quantify over all derivations.

The retirement prerequisite is now enforced by the existing `CanEndStorage`
guard: neither suspended nor static homes admit ordinary retirement.
`Retires.static_root` proves that every actual retirement preserves the whole
record of every static root, even a vacant one. Cleanup's `RootClear`, fresh
private-slot admission, and suspension consumers use that same strengthened
guard. The focused private/cleanup/drop/buffer preservation closure passes
(249 jobs). The retention theorem uses only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. This does not establish static write
protection, static-image installation, or nominal literal construction.

## Produced invocation-entry lifetime

`EnterWorldAttempt.region_live` derives the callee's live region from actual
fresh-region creation, receiver/witness preparation, the ordered input attempt
and receiver finishing. The proof covers successful and exhausted entry;
neither post-state liveness nor successful allocation is an assumption.
`FunctionEntryResult` now includes the successful callee's live-region fact.
Ordinary, contextual, proper-tail and foreign-callback entry consumers derive
that strengthened result; tail custody relinquishment preserves the fact.

The producer and entry consumers pass strict Lean checking, together with
`DropDispatch`, `InvocationLifecyclePreservation` and `MatchEntryContextTyping`.
This is liveness at entry, not preservation through arbitrary body execution,
the subsequently scheduled tail cleanup, saved frames or replay. Those
obligations and the derivation of `ResourceAdmissionAt` remain open.

## Constructive destructor hook outcomes

`Execution.destroyHook_progress` constructs the temporary reference allocation
and destructor loan from the original receiver's location type, unique
permission, resource/loan compatibility and positive `AllocationRequest`.
Its successful outcome retains typed ordinary invocation inputs and the actual
hook-entry step. Its exhausted outcome retains the same admitted request and
constructs `LocalStep.destroyHookExhausted`, a fatal resource transition with
unchanged storage. `Contracts.StateProgress.destroyHook` consumes both outcomes
as actual invocation progress inside the caller boundary.

`AllocationRequest.reference` constructs the fixed reference-layout request
from target validity, runtime-region support, region liveness and the target's
explicit pointer-size capacity bound. `StateProgress.destroyHook` now uses this
producer rather than assuming an opaque request: it derives referent support
from world/address typing and the loan-region bound from world well-formedness.
The target contract is unchanged; pointer-size capacity is not silently assumed.

Cleanup classification and invocation lending cover the new transition.
Callback runtime preservation tracks inclusion of retained dependencies:
fatal termination can abandon a task continuation, but every retained callback
runtime remains live. General storage, control, private and callback consumers
pass focused strict Lean checking.

This closes hook dispatch, not execution or termination of arbitrary destructor
bodies. Source production and preservation of the pre-state permissions,
resource compatibility, region liveness and pointer-size capacity remain
obligations of general source admission; `ResourceAdmissionAt` is not thereby
discharged. The derived-request chain and downstream `DropPrivate`,
`CleanupRunProgress` and `PublicValues` pass focused strict Lean checking.

## Current ABI inventory and transfer checkpoint

`ABISiteAdmission.Code.mem_tailSites` proves declaring-function identity and
tail-node shape for every member of the mutual syntax traversal, including
handler completions and operation arms. Its induction generalizes the selected
site through all four syntax families; no membership premise is fabricated.
`Code.tailSites_self` and `TailSites_ne_nil` establish the direct-tail inventory
boundary. `TailEvidence.transfer` now spans the actual pending-tail request,
callable-selection step and retiring step, rather than requiring one state to
be both pending syntax and a retirement source. The canonical source engine
constructs all three transitions and derives the endpoint activation-frame bound.

The focused ABI and `Specification` gate passes with strict Lean settings. This
is not full ABI soundness: source progress, the complete cleanup/control-space
bound, target-state coverage beyond tail entries, and label brand instantiation
and direct-transfer correspondence still require proof. Conditional `realizes`
alone does not exclude an empty engine/source relation. The full specification
goal remains open.

Initial draft only. The entries below locate the proposed formal meaning;
they are not a table of passed conformance gates.

| Language boundary | Formal modules |
| --- | --- |
| Supplied files/packages; no ambient imports | Declarations, Origins |
| UTF-8, literals, grammar and source forms | Syntax, SourceRules, Elaboration |
| Names, privacy, aliases and nominal identity | Declarations, Static, Elaboration |
| Calls, tuple arity, contextual blocks, evaluation order | Kernel, Elaboration, Machine |
| Pattern coverage, binding environments and ownership | Kernel, Typing, Control |
| Principal quantities, generic restrictions and recursion | Foundation, Static |
| Ownership, partial initialization, loans and cleanup | Storage, Machine, Contracts |
| Fn/RunsIn and guarded control interfaces | Declarations, Static, Contracts |
| Lifetimes, variance, higher-ranked constraints | Terms, Static, Typing |
| Effects, exact instances, deep handlers and quantities | Effects, Relocation |
| Direct labels and mandatory tail transfer | Machine, Control, ABI |
| Generics, traits, coherent impls and structural consts | Static, Instantiation, Elaboration |
| Fixity and ordinary operator calls | SourceRules, Elaboration |
| Unsafe memory, provenance and representation | Memory, Primitives, Typing |
| C declarations, callbacks and foreign barriers | Foreign |
| VM/native ABI, shared storage and artifact admission | ABI |
| Finite observations, divergence, rejection and limits | Foundation, Specification |

## Required repair/verification pass

The full initial draft must be written before the first build. Afterward:

1. Repair Lean elaboration failures without weakening semantic premises or
   replacing unfinished proofs with axioms/admissions.
2. Establish general preservation, progress and correctness theorems with
   strict Lean proof checking. Preserve `Checks` as regression material, not
   routine evidence of semantic soundness.
3. Audit every source form against the normative text, including generics,
   associated bindings, ownership markers, implicit operation instances,
   bodyless declarations, contextual alternatives and source-origin paths.
4. Check progress and composition at storage/control boundaries: partial
   holes, real drop-hook execution, cleanup order, nested handlers, cancellation,
   replay aliasing, lifetime restoration, binding packs and tail transfers.
5. Audit each primitive and target obligation for total defined behavior,
   closed authority, nonvacuous site coverage, and shared physical storage.
6. Distinguish checked definitions/examples from larger open metatheorems.

The target contract is for future implementations. There is no asserted
Stage0/self-hosted migration, VM/native execution test, or end-to-end compiler
proof in this standalone specification project. Library algorithms and their
verification are outside its scope, not a deferred phase of this work.

## Current resource/outcome integration boundary

The checked source-context and preparation graph has general proofs for the
six resident/raw binding cases, custody-aware local world preservation, actual
source-local environment selection and entry, and source-selected payload
pattern transport through ordered handoff. Positive allocation requests share
the real physical-extent predicate with exhaustion. Constructed payload
preparation preserves every successful prefix; actual entry and payload
failures retain the partial world and terminate without cleanup or rollback.
The general attempt relations preserve world typing for both outcomes.

The fresh strict 83-job gate checks `ContextTyping`, `PayloadHandoff`,
`PatternPlanTransport`, `InputLending`, `AllocationExecution`,
`OperationPayloadPreparation` and `StorageConstruction`. It does not run
examples or the aggregate. Current ABI/layout and guarded capability
definitions are retained, not replaced by older collaborator backgrounds.

The next coherent checkpoint passes the fresh strict 173-job gate for
`OperationExecution`, `LifecyclePreservation`, `BufferAllocationProgress` and
`CopyResourcePreservation`, also replayed in the integrated main tree. The
actual operation source theorem constructs success or resource failure from
source arm typing, common payload preflight, caller disposition permission and
positive continuation requests. It derives payload plans and handle
initialization; it no longer assumes successful allocation. Partial payload
worlds and completed root suspension survive actual failures, with no invented
capture event or successful clause cursor. Only a real suspension event
establishes the request's capture lifecycle.

The same check composes the common loan-kind/custody invariant, actual loan
mutations and raw buffer-allocation success/fault progress. Owning rows are
unique; owning and storage-borrow rows have custody, including historical rows.
Snapshot selection retains actual reference, resource, control and dependency
loans through the same storage plan and authority support. Current/saved
resource-input bindings and stopped contexts remain in actual control support.
Ordinary copy preserves shared resource closure. Copied stored-value typing
does not by itself establish mixed copied/external snapshot resource closure.

The following fresh strict 135-job gate, also replayed in main, checks
`SemanticPreservation`, `ControlContextTyping`, `SnapshotReplayPreservation`
and `OperationExecution`. General actual `Step.worldTyped`, `Run.worldTyped`
and the public storage-safety consumers compose without changing their
statements or adding a typed-output premise. This includes indexed foreign
mutation/custody, actual host-produced callback worlds, all actual primitive
and control resource faults, and nonempty proof-binding construction via the
ordinary declared invariant framing law. Superseded higher bulk-move proofs
were removed in favor of the common lower producer. `MemoryPreservation` and
`ControlContextTyping` are now checked for the changed graph.

The same gate closes the mixed copied/external snapshot resource graph.
`CopiesSnapshot` derives closed nominal resources and restored reference
targets, then actual copied-root suspension/replay admission and conditional
cancellation admission. The nominal invariant relocation law has its real
consumer; old external allocation ownership is retained because actual fresh
shared loans cannot be owning rows. This is not an assumed post-world
resource invariant. Cancellation still needs its source admission.

Raw buffer release now requires `value.resources = []`; hole fields and
structural array typing cannot justify silently discarding raw bindings.
Reallocation's common success/fault source admission also records the positive
old-region root/loan/availability/binding-pack facts needed by actual teardown.

The strict 195-job `BufferReallocationProgress`, `SemanticPreservation`,
`SnapshotReplayPreservation` and `OperationExecution` gate passed on the
integrated source. The constructive raw-growth chain consumes admission through actual
fresh allocation, disjoint snapshot/clear/install, owning-claim discharge,
storage retirement and region end. `BufferReallocationRequest.progress` and
the actual `PrimitiveStep`/`Step.reallocate_typed_progress` conclude a typed
pointer result or unchanged-world physical exhaustion of the same positive
request. They assume no completed move/release or typed after-world. The
common resident-graph frame now observes actual reference rows instead of
requiring the entire loan table to be unchanged; the actual fresh allocator
derives its preservation premises. Source admission synthesis is still open.

The recovered strict 205-job gate checks `CopyProgress`, `LabelExecution`,
`RawMutationProgress`, `SemanticPreservation`, `SnapshotReplayPreservation`,
`OperationExecution` and `BufferReallocationProgress` on a source-only tree
(warnings as errors, implicit identifiers disabled, no copied `.olean` data).
It closes three previously open boundaries. Ordinary Copy: source duplication
capability and actual closed initialized storage construct the single
`CopyTree`/`CopyValue` traversal and its fresh owner-origin table, and the
selected acquisition is the actual copy/explicit-move/default-move branch of
the canonical principal; `Acquires`/`Copies.allocate_success_or_exhausted`
consume one positive `AllocationRequest` and return actual allocation plus the
actual acquisition, or positive physical `AllocationExhausted` for that same
request, and the actual `AtomStep`/`Step` consumers lift them. Label: the
boundary retains the actual first matching route, the common singleton resident
handoff preflight and a positive allocation request, so
`LabelReady.prepare` yields the actual `Protect` or its physical exhaustion and
`LabelReady.execute` constructs the actual `ControlStep.leave` or
`leaveExhausted`, the latter retaining exactly the unchanged before-world.
Raw: admitted empty-buffer release, raw move-read and raw move-write construct
the actual primitive and its unit/moved result from before-state admission only
(authenticated buffer, pointer/range relation, stored initialized value,
`MoveReady` footprint, owned source permission, destination vacancy/type and
disjointness), with the moved payload's recursive resources still accessible in
the result world.

Raw observation and pointer arithmetic now have constructed machine outcomes.
`RawRead.copy_exists` consumes explicit source duplicability, shared readiness
and the real pointer/range relation, preserves the source resident and produces
an initialized owned-view-ready copy. `RawBorrow.exists` consumes source
addressability, live lifetime, actual access, retained support and finite new-loan
view compatibility; the common `FormsLoan` producer constructs the checked
reference and its recursively accessible result without a post-world certificate.
Both feed actual `PrimitiveStep` and `Step` consumers.

Pointer offset and provenance-preserving address replacement construct their
actual numeric result and destination write from a selected live allocation,
matching generation and permitted bounds, including one-past positions. Address
replacement derives its target-width bound from the actual unsigned scalar;
address inspection derives it from the actual typed pointer resident. Inspection
does not require a live allocation and grants no ownership or dereference
permission. The existing constructive unique layout query is reused unchanged.
The combined raw/layout gate passes 179 jobs, and sixteen general axiom audits
report only standard Lean axioms. Overlapping bulk-move construction is now
proved by `BulkMove.exists`: destinations may equal source slots, with no
source clearing a destination's proper ancestor. Reallocation uses this same
constructor instead of a disjoint-only path. `BulkMove.typed_progress` derives
world typing, exact indexed destination contents (including holes), and
recursive resource accessibility from the original-world move admission.
The focused bulk/reallocation/raw gate passes 177 jobs. `PrimitiveStep.rawMove`
now connects the manifest tag to actual `BulkMove` and unit installation.
`RawMoveRange` authenticates source/destination pointer and count operands
against consecutive logical slots, actual element stride, physical provenance
and checked ranges. Zero-sized slots retain logical identity; empty ranges
require live aligned backing. Authority comes separately from actual resource
resolution and permission, never pointer bits.
`Step.rawMove_typed_progress` constructs both writes from original-world
admission and proves exact destination snapshot and resource accessibility
through unit installation. The 249-job integration gate and eight general
axiom audits pass. Source-derived admission and the other missing non-raw
primitive dispatch cases remain open.
The private preservation closure also passes (184 jobs): resolved raw-move
resources exclude the saved slot throughout clears, installation, and the
result write. Scalar construction determinism now uses the actual runtime
handoff contract, restoring `ScalarExecution` (104 jobs). The repaired
bulk/privacy/scalar-progress theorems use only standard Lean axioms.
Remaining stale Checks modules still prevent a verified root-module build.
`BasicChecks` now uses general closed parameter exclusion and canonical
unique-reference affinity from `CapabilityInversion`, with explicit declaration
well-formedness where conversion separation needs it. Its strict direct check
and 82-job gate pass; the capability/Copy/Drop/preservation gate passes 181 jobs.
Three capability axiom audits report only standard Lean axioms.
`ExecutionChecks` and `SourceChecks` also pass (120-job combined gate).
`BorrowChecks` and `BindingChecks` subsequently pass direct strict Lean checking.
The binding migration derives move/copy handoff readiness from actual reachable
residents and composite capabilities through canonical equation composition;
it does not assume readiness or a capability model. `ControlChecks` also passes
direct strict checking with derived witness handoff readiness and explicit
availability-consumption authority. `AuthorityChecks` now passes direct strict
checking: construction readiness follows the reachable graph, and both successful
and exhausted handoff paths retain their owned-permission requirement. The old
universal no-resume-step claim was false because blocked snapshot placement can
fault before argument transfer; the corrected claim excludes successful replay.
`PreservationChecks` now passes direct strict Lean checking, including whole-root
and nested move/restore, reference survival across a vacant referent, and rejection
of the forged ancestor graph. Handoff readiness is derived; current loan-kind,
guard and physical-layout obligations are discharged. The eight-byte reference
fixtures require a 64-bit pointer target. No general source soundness is established.

The nested destructor composition boundary is now actual: `CleanupRun.destroy_fields_loop`,
`destroy_fields_tree` and `CleanupDrain.destroy_node` accept a child run with its real event
trace instead of an impossible empty-trace premise, and they no longer demand that
still-unscheduled sibling slots be vacant after one child is destroyed. Final holes follow from
the selected child hole plus unchanged other slots under the duplicate-free schedule. The leaf
instance `destroy_child` and the recursive tree producer remain open: a child's destruction
still needs the recursive `World.Destroys` inventory admitted for arbitrary nesting.

The destruction frame now preserves reads only at non-overlapping addresses:
clearing a child necessarily changes an ancestor's stored value. Root presence
is preserved everywhere. `World.DestroyFrame.of_write` derives this frame from
the actual write and subtree containment, not an assumed footprint theorem;
`World.Destroys.of_destroy_frame` consumes the corrected exclusion relation.
The focused `CleanupDrain` proof check and aggregate `Specification` target
pass. Neither check discharges recursive child execution or the run-quantified
progress/resource-completion assumptions in `ResourceAdmissionAt`.

`UnsafeInvariantContract.copyResources` is added as an admission law of the
existing contract: a valid pre-world, the contract's holds predicate and actual
duplicability imply the erased retained bindings are read-only. It is the
formal counterpart of §7.2's rule that a structural copy creates an additional
owner only for duplicable types, applied to the §7.3 unsafe invariant contracts
that determine owner behaviour for residents not stored syntactically by value;
the normative text does not enumerate the clause, so this is recorded as a
formal obligation and an interpretation, not as added source syntax. No field
of any runtime relation, rule or language meaning was changed by the recovery.

The whole library is not green. At this revision the named targets
`BasicChecks`, `BindingChecks`, `ExecutionChecks`, `ControlChecks`,
`PreservationChecks`, `SourceChecks`, `CleanupPreservation`, `InvocationLending`,
`ForeignEvolution`, `ResumptionPreservation`, `AllocationLayout`,
`FunctionEntryContextTyping` and `ScalarMachine` fail as stale consumers
outside the checked dependency graph; their error sets are identical to the
pristine pre-recovery tree, and the recovery additionally repairs the duplicate
`Value.Initialized.resident` that previously made `DropCapabilities` fail.
Full-source checking therefore still fails; an older checkpoint result is not
evidence for the current graph.

Two consumers left that stale set by repair rather than by re-snapshot.
`RuntimeWorldEquivariance` was migrated to the current `Value.resident`
(region renaming retains the resident's erased `resources` verbatim, since a
`StorageBinding` names root/generation identities and loan authorities and no
runtime region), its loan-permission transport now covers the full conjunct list
including the live-guard and shared-guard obligations and the added `guarded`
authority, and its whole-world well-formedness proof now discharges all nineteen
`WellFormedWithOrigins` obligations including `LoanGuards` and `LoanKinds`.
`PublicValues` was migrated to the canonical `Execution.Task.stopped context
address` and to `∀ context address, state.task = .stopped context address →
state.world.Initialized address` in `resourceAdmission_safe_iff` /
`WellFormed.safe_iff_initialized_returns`.

That repair exposed one genuine definitional defect in the public observation
relation, now fixed: `Specification.Reveals` was drafted before `Value.resident`
gained its `resources` field, so its five-argument constructor patterns silently
pinned `resources := []` through the field's default. That accident restricted
the observer to resource-free residents, which would have made
`resourceAdmission_safe_iff`'s documented equivalence to "preservation of
initialized stopped result addresses" false. `Reveals` now carries each
resident's actual `resources`; erased resource obligations remain internal
ownership state and are not part of the public value, so the observation is
unchanged by them. This restores the pre-`resources` extent of the relation
rather than adding a condition; whether a returned resident's erased
obligations are closed stays a separate unsafe-invariant duty and is not
assumed here.

The recovered checkpoint gate over the targets listed above passes 205 jobs;
adding `InputBindingProgress` and `LoanCompatibility` passes 208.
The then-current gate added the repaired consumers `PublicValues` and `RuntimeWorldEquivariance`,
the promoted `LoanResourceRows`, `ReferenceTransferPreservation`,
`SnapshotResourcePreservation`, `AllocationFraming` and
`CopyResourcePreservation`, and passed 212 jobs, or 210 without the two
compatibility modules. That checkpoint closed the single-input and permission
boundaries. `Authority.LoanCompatible` is the
pre-state compatibility relation for one newly formed live loan: owning, loan,
shared and guarded authorities observe the actual pre-world loan rows and the
pre-world guards, so shared access may overlap a shared loan and a carrier
newly used as a guard becomes shared-only. `LoanCompatibility` then
characterizes exactly when an existing `Permitted` survives a fresh loan, a
storage claim or an allocation claim, in both directions, as
`Permitted after ↔ Permitted before ∧ pre-state compatibility`, consuming the
actual loan insertion and location extension rather than a post-state
permission. `InputBindingProgress` constructs the actual binder for each of the
six real input cases from a positive `InvocationInput.StorageRequest` plus the
input's `Ready` pre-state facts; only resident allocation may exhaust, and lack
of semantic evidence is never reclassified as a resource fault.

The earlier single-input/permission boundary is now consumed by
`InputBatchProgress`. `Kernel.BatchPrepared.attemptFor` folds the real
six-case binder, retaining pending readiness/requests, observed resources,
claims/custody and already emitted bindings through every successful prefix.
It constructs completion or the first physical input-allocation exhaustion.

`Kernel.EntryBatch.enterWorldAttempt` now constructs the actual
`Execution.EnterWorldAttempt` without `consumed : World → World` or a
`finishes` callback. On completion, the actual preparation publishes a marked
receiver and its indexed capture inventory. The actual binder clears every
owned capture; later inputs cannot refill old holes or clear the marked receiver
or an ancestor containing it. This supports projected receivers and mixed
ordinary/raw inputs, rather than a root-only all-captures fold.
`Typing.ValueTyped.callable_shape` derives the shell's empty resource list and
capture count from the existing callable typing rule and selected instance.
There is no resource-erasing accumulator. Contextual call readiness retains
the code-only receiver shape already required by its real control transition.
Fresh-row compatibility at the prepared world derives the final owning
permission, and the stored receiver produces its actual retiring write.

The strict 73-job `InputBatchProgress` dependency gate passed after removing the
superseded `ReceiverFramed`, root-only shell folds and duplicated capture
helpers. The endpoint's axiom audit reports only `propext`, `Classical.choice`
and `Quot.sound`; no `sorryAx` or new semantic axiom is used.
The combined gate with `ControlContextTyping`, `InvocationLifecyclePreservation`
and `RuntimeWorldEquivariance` passed 120 jobs; joint imports and the preparation
producer axiom audit passed too.

This closes ordered **prepared-input batch preentry progress**, not general
source-derived execution progress. Original source readiness, actual
receiver/witness preparation, original-world incoming-resource agreement, prepared-state
batch compatibility and receiver fresh-row compatibility remain explicit
admission premises of that endpoint; separate batch framing is now derived.
Whole preparation, ordinary entry and proper-tail composition from finite
original-world admission are proved below. Source-derived admission and
whole-machine progress remain open.

The scoped framing promotions are now integrated and checked, not resident in a
lane workspace. They are level moves plus one disclosed redesign: the
`Storage` permission-state block gains `Loan.permissionState_eq_iff` and
`Authority.Recorded.parentLoan` (removed from `LoanPreservation` and
`ControlAuthority` respectively, so every dependent reads them at their lower
level), the three `Value.{ResourcesClosed,LoansRestored}.reachable` /
`Value.InvariantClosed.framed` lemmas move from `SnapshotResourcePreservation`
into `ReferenceTransferPreservation` with byte-identical statements, and
`BufferAllocationFraming` supplies the projected row fact its consumer now
expects. The new `LoanResourceRows` module carries producer row laws, and
`LoanCompatibility` grows additively from its checked permission-only
foundation. The redesign changes exactly one predicate: `Value.ReferenceRowsFramed`
compares the canonical `Loan.permissionState` projection of the observed row
rather than the whole row. That is the projection `Storage` already designates
for retention consumers ("custody and a requested return change administration,
not the loan's exclusion geometry"), and the permission, support and observation
predicates never inspect custody or return-request state, so the framing
conclusions are unchanged while custody is carried by the separate scoped
obligations. Verified before integration: no declaration of the previous tree is
dropped, the only changed statements are `Value.ReferenceRowsFramed` and its
`.lookup`, and the moved lemmas are text-identical. The composed strict gate over
the recovered targets plus the two repaired public-safety consumers and
`ReferenceTransferPreservation`, `SnapshotResourcePreservation`,
`AllocationFraming` and `CopyResourcePreservation` passes 212 jobs from a fresh
source-only tree; the same base without this chunk passes the recovered targets
with the identical whole-library failure set (thirteen modules, unchanged error
text).

The source-to-physical-address boundary is now integrated with authoritative
world typing. `WorldTypedWithOrigins` includes `World.LayoutRealized` for every
live allocation, vacant or occupied, so initial input admission requires
physically admitted storage. The allocator establishes the new root fact from
its actual `LayoutOf`; ordinary writes preserve root locations, and retirement,
rehome, snapshot copying and runtime renaming retain the layout law through
their actual root transformations. Whole `Step`/`Run` storage preservation and
`Specification.reachable_worldTyped` check with the strengthened invariant.

`World.representation` now derives `TargetRepresentation` from `WorldTyped`,
without an independent layout certificate. The general source projection
induction and `ContextBindingsTyped.place_addressTyped` consume this result;
`ControlStep.leave_source_result` and `MayTransfer.source_execution` likewise
drop the separate realization premise. The bridge derives the actual physical
payload type, then relates it to the translated source type by
`DefinitionallyEqual`. Array counts, nominal fields and aliases use the
existing resident/layout derivations; no extra count normalization or
requested address type is assumed.

Logical admission is now produced along the actual entry path.
`Kernel.Instance.predicates` consumes the selected instance
`ConstraintsHold` evidence, and `EnterWorld.contextBindingsTyped` records
discharged decoded assumptions, completed generics and the source universe
level in the existing context invariant. Its actual local, fresh-region,
fresh-brand, capture, handler and label transitions preserve these facts.
`Entails.decode_scope` proves transport of all sixteen mutual static
judgments, including quantified predicates, associated projections and
recursive capability evidence with non-injective scope images. Arbitrary
predicate templates are mapped with substitution values; only actual
declared requirements are fixed by program closure. The resulting
`ContextBindingsTyped.conversionClosed` is consumed by source projection,
place and label execution without an independent reading callback. The
superseded certificate lane has been removed. General source-admitted
progress and full specification conformance remain separate obligations.

The integrated strict gate passes 220 jobs for `InputBatchProgress`,
`SemanticPreservation`, `SourceAddress`, `LabelExecution`, `AllocationLayout`,
`RuntimeWorldEquivariance`, `SnapshotReplayPreservation`, the repaired
`FunctionEntryContextTyping`, `AllocationExecution`, `PrivateStorage`,
`ActivationStorageOrigin` and `ControlAuthorityStorage`. General logical
transport, actual instance/entry admission, context preservation, source
conversion, both address bridges, both label consumers, whole `Step`/`Run`
and public reachable-world axiom audits report only `propext`,
`Classical.choice` and `Quot.sound`. The repaired actual entry result includes
body typing and admitted local/logical context on success, real custody release
and inherited contracts before proper-tail cleanup, and the exact partial
world/fresh-counter consumption on exhaustion. Ordinary, contextual and foreign
callback recipes share that result; erased resource inputs do not fabricate
source-local formals. The entry and all three caller axiom audits report only
the same standard axioms.

Receiver/witness preparation failure is now represented by the authoritative
`PreparesEntryAttempt` and consumed by `EnterWorldAttempt`. A first-lease
failure retains the input world; a contextual second-lease failure retains
the actual receiver lease. General world typing, suspension retention,
activation bounds, private-slot preservation and positive allocation-exhaustion
proofs cover both preparation and input-binding failure. Exclusivity no longer
asserts that allocation failure acquired a loan.

`EntrySource.prepare` now constructs every source recipe's preparation outcome
from original `EntrySource.Ready` and concrete `PreparationConditions`: real
physical requests, original receiver/witness access, separation, and the existing
observed input/value graph. `FormsLoan.borrower_permitted` produces the new
borrower permission. Capture initialization, contextual witness resources, the
second request, reservation permissions and both actual consumption writes are
derived rather than assumed afterward. Owned receiver lending allocates nothing;
shared/unique lending uses the same positive request producer as ordinary inputs.
The actual lender's frame is shared by receivers, witnesses and the ordered
binder. The integrated 220-job gate and all general construction audits pass
with only `propext`, `Classical.choice` and `Quot.sound`.

`PreparesEntry.contextual_inputsCompatible` now derives the complete prepared
contextual input product from its original-world product, existing preparation
conditions, and original storage/support exclusions. Both actual loans, receiver
marking, and witness clearing/deactivation are composed; no middle-world
readiness, interference or retained-support premise is supplied. Receiver
marking preserves live slots and physical offsets at arbitrary depths through
ancestor arities and heads. Erased ports observe location and loan/custody state,
not unchanged resident contents; a cleared witness slot can remain an erased
port. The same product derives `InputFramed` for the real entry endpoint. The
integrated strict 220-job gate and general composition/transport/entry axiom
audits pass with only the standard three axioms.

`PreparesEntry.inputsCompatible` closes this original-input boundary for every
recipe, including authority-changing resident captures. Their top permission,
borrow region and guards come from the actual receiver loan. The same value
graph transports readiness and all five pairwise interference channels, then
actual receiver consumption uses the authoritative input-coordinate theorem.
`EntrySource.prepareInputs` constructs success/exhaustion and the complete
success product under one original-world `PreparationConditions` contract.
Top-level permission reads now match resident/storage and guarded-allocation
rules; ordinary allocation and raw-loan handoff impose no fictitious access
to T. The separate owned-permission observer and its unused helper are removed.
The strict 220-job gate and all-source, resident-product and ordered-binder
axiom audits pass with only the standard three axioms.

The incoming-resource boundary is corrected in both actual entry outcomes:
`EnterWorldAttempt` checks the original world and `source.originalInputs`,
including preparation exhaustion. No arbitrary unsafe predicate is asserted
stable through internal preparation. `EnterWorldAttempt.incomingResources`
exposes that common original admission; the success/prepared and exhaustion
consumers use it. Prepared key uniqueness is derived from original contract
keys and the actual preparation coordinate theorem. The separate prepared
`Nodup` premise is removed. The strict 220-job gate and general entry, original-
contract, exhaustion and preparation axiom audits pass with standard axioms only.

Fresh-lifetime preparation is now constructive from the caller world.
`StepObservation.regionState` preserves existing live regions and a monotone
frontier instead of requiring table identity; every old producer is migrated.
`AllocationRequest.retarget` shares positive layout evidence, retaining source
lifetime support while selecting the actually live callee lifetime. Actual
`FreshRegion` transports the whole input product, source recipe and preflight.
`EntrySource.prepareFreshInputs` constructs the fresh world and every real
preparation outcome from original-world incoming resources, readiness, requests
and interference. No fresh-world product or chosen preparation is admitted.
The strict 220-job gate passes; the new construction and frame theorem axiom
audits report standard axioms only.

Whole entry now consumes `EntrySource.Admitted`, a product of original-world
recipe readiness, positive preparation/layout requests, input interference,
incoming-resource agreement and receiver fresh-row compatibility. Actual owned
preparation preserves original input authorities and at most the witness's
fresh row; shared loan/storage frames derive prepared receiver compatibility.
`Admitted.enterWorldAttempt` constructs lifetime creation, preparation, the
ordered resident/raw binder and actual receiver retirement, or the exact
physical exhaustion prefix. `Admitted.enterStep` consumes it in the real
non-tail machine transition. The strict 220-job gate and the general entry,
step, receiver and exhaustion axiom audits pass with standard axioms only.

The private-slot proof transports the original source footprint through
`PreparesEntry.map_inputs`; erased ports are not mistaken for initialized
residents. Entry control-authority provenance transports the original recipe
records, including guarded carriers, through actual preparation, binding and
receiver finishing. These general theorem axiom audits also report only the
standard axioms. `InvocationStart` now consumes the finite original entry and
proper-tail cleanup contracts below. General source admission and task/frame
integration remain open. No full-tree success is claimed; preserved example
modules were not run.

The shared `BodyInventory` now checks `RuntimeProgram.UnsafeContractsValid`:
unsafe caller contracts belong to actual unsafe function declarations (§15.1).
The declaration-selection producer is promoted to `Kernel` and reused by Drop
and instantiation; safe selected instances derive contract absence rather than
ignoring predicates. `Temporary.borrowed_handle_private` consumes every actual
`FormsLoan` purpose, including `.destructor`, and the real hook-entry privacy
consumer checks again. The integrated gate including `DropHandle` passes 221
jobs; metadata and hook-entry axiom audits report standard axioms only.

The inherited-guard modeling bug is repaired in the common producer.
`Authority.carriers` retains only the authority expression's explicit loans;
`throughReference`, `referenceView` and `resourceView` are world-independent.
Inherited `Loan.guards` remain liveness dependencies and freeze their direct
carriers; they are not requested again as independent access permissions.
`Permitted.referenceView_iff` and `resourceView_iff` prove the full explicit
carrier permission contracts. Their axiom audits report `propext` and
`Quot.sound` only. Actual source address, ordered-input, pattern, snapshot,
control and destructor-privacy consumers check with the corrected producer.
The redundant global/recorded guard-frame products and graph admission
premises are removed; real loan-construction dependency framing is retained.
The integrated 221-job gate and original-admission entry-step axiom audit
pass.

Created-reference readiness is now constructed through the actual loan
formation and temporary allocation. `Value.ReachableResident.rebase_carriers`
is the common graph producer; the existing weaker rebase projects it.
`Value.ResourcesAccessible.reference` proves complete nested reference and
retained-resource access, not merely direct dereference permission.
`FormsLoan.handed_off_ready` and `Temporary.borrowed_handle_ready` frame the
original source and discharge actual fresh-slot separation. Private storage
excludes every reachable live-loan/resource support edge from the slot being
cleared, so `LocalStep.hook_inputs_admitted` constructs the actual destructor
argument's initialized singleton `HandoffReady`. The retained-resource loan
witness is promoted from suspension-only scope and shared, not duplicated.
The `DropHandle`/`SuspensionContent` gate passes 166 jobs; graph, reference,
formation, temporary and actual-step theorem audits use standard axioms only.
Original source readiness and prospective-row view compatibility are explicit
finite pre-state requirements. The actual hook product now also constructs
typed/common formal coordinates, its real positive allocation request and
original safe caller contract. `InvocationStart` carries this finite
`EntrySource.Admitted` and original proper-tail cleanup admission; `step`
produces the real successor without an extra declaration or intermediate-world
admission premise. The isolated producer uses original input records and the
canonical root-bound theorem.

Control authority preservation is migrated across ordinary entry, proper-tail
caller-contract retention, raw return bindings, guarded relocation and actual
dependent/custody release queues. `EffectStep.recorded` and `Step.recorded`
retain historical records through every fatal physical prefix without asserting
completed suspension ownership. Primitive buffer claims and host exposure share
the actual allocation producers; `Mutations.published_recorded` follows the
ordered action transaction, replacing obsolete endpoint `FreshExposed` reasoning.
The combined `DropHandle`/`ControlAuthorityForeign`/`ResumptionPreservation`
gate passes 163 jobs. Ordinary invocation, actual hook-input, historical/saved
recording and transaction-output audits report standard axioms only.
Root and activation consumers now follow the same actual invocation recipes,
returned contexts, claim releases and host outputs. The complete
`ControlOriginPreservation` gate passes 173 jobs, with standard-only axiom
audits for terminal inversion, nonfatal-path construction, control preservation,
divergence, published root bounds and activation preservation. A real fatal
event produces a terminal task with no successor; therefore a non-resource-
fatal endpoint or an infinite successor chain supplies the required nonfatal
run. General observation/reachability now state complete control/suspensions
or the actual resource-fatal terminal, instead of assuming all runs nonfatal.
Saved-control root exclusion uses immutable metadata and remains unconditional.
Actual indexed host publications, registry origins and callback runtimes now
preserve their guarantees even at resource-fatal endpoints: the final step
preserves those records and the actual terminal task has no successor. Root
grants require carrier-free authority, not merely an absent parent loan.
The ambient Drop dispatcher constructs the finite `InvocationStart` from
actual hook inputs while retaining the caller, registry and callback state.
`DropInvocation` plus `DropSuspension` pass 181 jobs; the registry, callback,
dispatch and saved-suspension audits use only standard axioms. The latter
theorem retains unconditional historical exclusion while distinguishing
complete after-control from the actual resource-fatal terminal.

Private-body integration now passes `DropPrivate` plus `DropSuspension` (190
jobs). Actual raw-return binding, proper-tail custody cleanup, allocation-claim
origins and deferred contextual/callback recipes feed the same private-control
invariant. An absent suspend event does not rule out a partial freeze: the real
internal route and private frame owners prove that its root selection omits
the caller slot. Real snapshot-copy origins preserve that slot during replay
exhaustion. `InvocationRun.private_guard` remains unconditional on fatal
endpoints because the actual final step preserves privacy and has no successor.
The Drop theorem factors arbitrary ambient runs up to the first normal return
while preserving the private prefix. Handoff, copy, effect, host, invocation
and Drop audits use only standard axioms. Finite original handoff evidence and
selected Drop admission remain required; this is not a proof of body progress
or termination from world typing. Original source-fact production and
whole-task progress remain open.

External cleanup separation now follows the same terminal-aware contract.
Capture cannot create an exterior home; restoration reads the actual saved
frame-owned homes. The existing ownership-shape proof is promoted to `Machine`
and shared by content preservation and fatal restoration reflection. Actual
fatal steps preserve active saved-root exclusion even when restored/frozen
storage no longer satisfies full suspension ownership. The general run,
retained-record origin, cancellation and admitted-invocation consumers retain
their unconditional separation conclusions. Host publications are indexed by
actual actions, and callbacks use deferred entry without fictitious lending.
The combined `ExternalHomePreservation`, `DropPrivate`, `DropSuspension` and
`SuspensionContent` gate passes 199 jobs; the general consumer audits use only
standard axioms. Root liveness, resident contents and general source progress
are not established by this separation result.

Ordinary replay progress now consumes only the original argument facts.
`SnapshotMap.old_permitted` derives compatibility from the actual selector
(only live shared loans are copied), old permission exclusions and the parent
mode invariant; no extra copy-compatibility admission is introduced. The
canonical old-row and support frame transports the original handoff graph.
Final replay uses the active saved-home inventory and the shared rehome
producer. `resumeLast_or_exhausted` and `resumeCopy_or_blocked` retain their
exact successor worlds, and `resume_progress` derives the branch from the
actual accounted budget. `Run.replay_owned` derives its nonfatal prefix from
the actual next replay instead of requiring a separate run certificate.
The shared permission/rehome migration also checks the original-input, pattern
and actual destructor-purpose Drop dispatch consumers. The combined nine-target
gate passes 244 jobs; twelve general audits use only standard axioms.

The returned-unit custody boundary is now integrated rather than excluded.
`World.CustodyReleaseReady` supplies original restoration for the actual
custody inventory's parent/guard retry closure; its producer transports those
facts through real relinquishment and private empty-shell consumption. The
general drain admits ordinary/destructor loans without a global raw-only kind
restriction, retains exact non-task state and reports row-preserving
`LoanReleaseFrame`. `DropReturn` consumes finite original custody discharge,
that retry admission and the actual destructor loan kind. It constructs the
variable drain trace, both root retirements, current Self retention and the
unchanged already-ended destructor row. Only permissions justified by retained
resident carriers are preserved; no arbitrary ended-loan permission or whole
loan-table equality is assumed. The combined ten-target cleanup/replay/input/
pattern/private/Drop gate passes 256 jobs, with twelve general audits using
only standard axioms. Producing returned-state private-root and custody/retry
admission from source/task invariants remains open, as do cancellation and
whole-task progress.

Proper-tail entry now has original-world admission and a constructed machine
successor. `EntrySource.clearedStorage` records the actual receiver, witness and
owned-input erasures; `Value.AfterClearing` observes exact residual shells and
field holes through canonical path lookup. Actual entry proves that every
surviving old resident is such a residual. Its remaining graph is a subgraph of
the original one; a fully moved field contributes no surviving obligation.
`EntrySource.CleanupAdmitted` checks residual unsafe invariants and finite
claim/custody/support compatibility in the original world. It also checks the
original caller root selection, custody-port coverage, relevant restoration
targets and lent-storage separation. No future-world readiness, field-insensitive
invariant law or permission for a frozen reference is assumed.

The real common binder transfers every covered owning obligation, including
guarded child claims. Preparation preserves complete erased inputs and creates
only its actual receiver/capture authorities. The composed entry frame covers
both physical failure kinds; restoration-loan origins, exact protected reads
and ordered root selection come from the actual producers. Surviving residents
and caller-relevant referents are closed after entry; real custody relinquishment
retains that `Suspensible` result. `EntrySource.Admitted.tailStep` constructs
`LocalStep.enterTail` or the exhausted prefix. `InvocationStart.step` replaces
the non-tail-only consumer, with original cleanup admission guarded by the real
tail flag. Isolated and Drop-hook producers are migrated. The integrated
invocation/cleanup/replay/content/private gate passes 257 jobs; sixteen general
axiom audits report only standard Lean axioms. General source production of
these original admission predicates, cancellation and whole-task progress
remain open; this does not claim complete specification conformance.


The paused task/frame consumers are recovered and checked rather than rebuilt.
`CleanupPreservation` gains the actual custody-return step (the relinquished
write precedes the shell write and is performed on the relinquished world) and
the storage-return step, and forms the destructor lease through `FormsLoan` with
purpose `.destructor` instead of assuming a source borrow. `ForeignEvolution`
restates the changed producer graph: a producer may add loan rows or rewrite
rows in place, never dropping a recorded row and never reviving a dead one, with
`World.HomeExtension.congr_roots` and `Authority.Recorded.rewrite_loans` as the
general facts the stability consumers need. `InvocationLending` is migrated to
the real entry product: the attempt is the six-existential/eight-conjunct
`EnterWorldAttempt`, and every exclusivity statement is indexed by the actual
`PreparationOutcome`, so the exhausted prefix of a failed entry is covered by
the same retention argument as a completed one. Retention runs through the real
chain (lending, receiver consume, ordered input binder, finishing step) via the
additive `Kernel.retained_through_entry` and the attempt-level/retained-target
retentions in `InputLending`; `LocalStep.enter_world` yields the outcome-indexed
attempt together with either the entered world or a `RelinquishesCustody` step
to the proper-tail world, and the additive `RelinquishesCustody.permitted_reflected`
transports permission back across that administration-only change.
`ResumptionPreservation` derives the caller's whole structural support including
the bound invocation-resource contracts, derives each input's address support
from the actual `ReadyFor` product, and takes the inputs' authority provenance
as an explicit admission hypothesis because a storage-borrow input handed over
through a shared backing authority names no row for that backing and therefore
is not derivable. No statement is weakened and no previously derivable fact is
assumed. Verified exact: the four modules check as 80 jobs, and the composed
gate including them passes 224 jobs from a fresh source-only tree.

The suspension boundary's captured-product release is integrated:
`SuspensionAdmission` records the suspend rules' own admission (their
`SuspendPermission` supplies the replayable roots and snapshot frames of the
suspension they create, and every step's actual resumption-table change retains
a previously stored suspension's captured product), `SuspensionContent` builds
the captured content as a real product of the actual capture, replay and
cancellation storage operations (`DelimitedRoots.replayable_suspendRoots`,
`Suspension.restore_replayable`, the rehoming and fresh-root frames for
`Replayable`/`Suspensible`/`Cancelable`/`Authority.Replayable` and
`Value.ResourcesClosed`/`LoansRestored`/`InvariantClosed`), and
`SuspensionRetention` delegates the retention of a stored suspension's captured
product to `ResumptionChange.retains_metadata`. No wrapper is presented as a
completed admission: the lane deleted the unused `Suspension.Admitted` wrapper
rather than claim it. The capture release closes the dead-loan frontier bound
rather than recording it: the fresh-root frame's side condition is now the
machine's own live-loan law (`World.loan_referent_bound`, `World.loan_referent_ne`,
`World.exists_root_of_root`), the value's `LoansRestored` closure is threaded
through the frame family (`Value.LoansRestored.reachable` makes it hereditary
along the reachability graph), and `SuspensionCapture` produces the admission at
the real suspend instructions (`EffectStep.capture_replayable` through
`CreatesContinuation.replayable` over the actual handle allocation) plus the
loan-table-only control-replayability transports
(`Authority.Replayable.congr_loans`, `CreatesContinuation.controlReplayable`,
`suspendRoots.controlReplayable`). Residual, recorded: the live-control/captured-root
separation needed to freeze captured content across intervening steps, the
control-replayability clause of the disposition admission (whose only real
producer is the `MayAwait`/`Permits` chain, so it is not added to the rule),
control-region liveness for the captured frames' owned regions, and external
scoping of `SnapshotMap.externalReferentsScoped`.

The authoritative alias contract is landed: `FieldOffset` gains the `alias`
constructor, so an alias application's physical field offsets are its actual
expansion's (`program.alias` supplies the declaration, the checked
substitution edge reaches the expansion, and the selected field keeps the
expansion's — the actually stored — type, which is why initialized residents are
never alias-headed). The declaration data is carried explicitly rather than as
an `Equal` premise exactly so the region invariant is derivable
(`FieldOffset.alias_runtimeRegionsBelow`). Consumers were migrated by their
owner: `FieldOffset.transport`, `Relocation.old_fieldOffset`,
`FieldOffset.runtimeRegionsBelow`, `SnapshotMap.copied_fieldOffset`,
`RegionPermutation.fieldOffset` (all now recursive inductions over the new
constructor) and `ConstructorHead.field_type`. The same release replaced the
unprovable world law `TargetRepresentation.structural` with the derived
`AddressType.structural_of_stored` (an occupied address is read at its resident's
own type) and added `Typing.StructuralExpansion`. That checkpoint also included
physical-to-runtime metadata transport in
`DefinitionallyEqual.runtime_context` and an assumption-free interpretation
fragment. The latter has been superseded by actual entry predicate admission,
not retained as a separate certificate path. The then-open producer for
`TargetRepresentation.offsets` is now `World.representation`, derived from the
authoritative layout-bearing `WorldTyped` invariant described above.

One additive shared-core hunk landed for the suspension boundary:
`UnsafeInvariantContract` gains `rehomed`, the rehoming counterpart of
`relocated` (a declared invariant cannot depend on internal home bookkeeping,
since capture, replay and cancellation relabel the ghost home field while moving
no value, creating no loan and leaving every read of the resident unchanged). The
structure has no instance anywhere in the tree, so the field is additive and
changes no existing definition.

Post-cancellation cleanup is executed rather than only classified, on the
non-vacant resident path as well as the cleared one:
`CleanupExecution` proves that the machine's own `cleanupRoot`, `destroyVacant`,
`retire`, `regionEnd` and `cleanupDone` steps actually retire every captured root
of a cancelled suspension and then close every region it captured, reaching the
task the cancel scheduled, and connects that whole run to the real cancel rule
(`EffectStep.cancel_roots_execution` / `CleanupRun.cleanup_execution`). It
provides the two `RegionCanEnd` transport facts the chain needs (ending a region
leaves the roots, loans and reservations unchanged; retiring storage only removes
one root's liveness and its now-empty value) and composes cleanup segments along
their traces.

`CleanupDestruction` runs the destructor and loan-ending rules themselves and
reports the state each actually produces: `destroyStructural` (a real shell with
real fields and the nested `destroyFields` continuation in reverse index order),
`destroyReference` (the cleared slot plus the `releaseLoan` the rule schedules),
`destroyHook` (the destructor lease and hook entry), `Run.hook_returned` (the
continuation the machine schedules when the hook yields: both retirements, the
loan close and the field continuation), `CleanupRun.shell_done` (the relinquished
write and the pending release list of the shell's owner), and the
`releaseLoan`/`closeLoan` endings. `CleanupRun.cleanup_root_shell` composes them
into the real chain for a captured root holding a live shell, from the `.cleanup`
task to the relinquished write and pending release list, and
`CleanupRun.destroy_fields_holes` executes the field loop of the structural rule.

The admission products those steps consume are no longer unowned.
`CustodyDischarge` carries the live owning claims of one custody together with
the successor row each actually received through the entry binder's own
`ClaimsAllocation` step (`HandedOffClaim.of_claimsAllocation`, retained across
later insertions by `HandedOffClaim.retained`), and produces the whole-table
`World.CustodyHandedOff` that `RelinquishesCustody`/`shellDone` consumes
(`CustodyHandedOff.of_discharge`). The same module's `World.ReferenceFree` is the
closed stored-value inventory that makes `ReturnsStorageLoan` and `EndsLoan`
executable without per-step reference premises
(`ReturnsStorageLoan.of_referenceFree`, `EndsLoan.of_referenceFree`), and it is
retained by the actual retirements and region closures
(`ReferenceFree.of_retires`, `ReferenceFree.of_regionEnds`).

Readiness is derived rather than assumed. `World.RootClear` reads the three real
tables (`loans`, `availability`, `roots`) instead of `CanEndStorage`, yields the
`CanEndStorage` the retirement needs (`RootClear.canEndStorage`) and the
`.owner .owned` permission the structural destructor needs
(`RootClear.owner_permission`); its loan clause is itself derived from the
endings that actually discharged a root (`RootClear.of_ended_loan`), and it is
transported by the shell write (`RootClear.of_write`). `RegionCanEnd.of_discharged`
likewise derives a region's readiness from the retirements and loan endings the
cleanup performed.

Residual, exact: (a) a captured value whose field stores a further resident needs
the destructor recursion over the stored tree — each real field's own `.destroy`
continuation is the same machine rule and is executed here, but the recursion
across the value tree is not yet assembled; (b) the pending-return list
`shellDone` schedules drains row by row
(`release_storage_returned`/`release_already_ended`) and the list-to-retirement
composition is not yet stated; (c) executing a declared drop hook's arbitrary
body remains the whole-machine control obligation recorded by
`CleanupPreservation`, while that path's entry and return outcomes are now
reported here.

The isolated invocation now shares the actual finite original-input product.
It consumes that product's authority records and the canonical ready-input
root bound, instead of imposing a headed-share shape or repeating formal
analysis. The superseded `InputAuthorityProvenance` module and umbrella import
are removed; raw-input recording is preserved through actual resource
resolution and the common binder.

The replay/reconstruction release adds five modules and exactly three new
`EffectStep` constructors, all fatal-resource steps, so a failed replay does not
consume the suspension budget. `SnapshotPlacement` (importing only `Storage`)
defines the ordered placement contract: real extents (positive, aligned, in
bounds, disjoint from live storage) that do not overlap. Its construction module
proves the fold total — either the whole captured inventory is placed by a real
table or the next selected root has no real extent compatible with the
successful prefix — and `SnapshotPhysicalBlocked.no_extension` proves no
complete table agreeing with that prefix exists, so the failure is prefix
relative rather than an assumed impossibility. `SnapshotReplayConstruction`
builds the real `Relocation`, `SnapshotMap` and `CopiesSnapshot` from the actual
suspension inventory plus that placement, or reports the real blocked
exhaustion; `SnapshotReplayProgress` reaches the real replay step through an
actual `Protect` or the real fatal-resource exhaustion steps, and executes the
real cancel step from the source `Cancelable` admission without granting any
extent, copy, Protect or cancellation permission. The three new constructors
needed arms at exactly three sites, all present here. `Suspension.PhysicalAdmission`
names the suspend-time source product that replay-time `Replayable` needs; the
actual post-cancel cleanup execution is now constructed on the non-vacant
resident path as recorded above, while moving that admission across intervening
steps remains open and is owned by the suspension lane.

This is not whole-language soundness. Private, complete control-lifetime and
foreign-runtime consumers still need the changed raw/failure constructors.
General input/pre-entry progress needs a mode-aware pending-loan/custody
interference contract; independent initial input permissions are insufficient.
Label and other allocation sites, remaining raw primitive progress, physical replay,
the destructor recursion over nested stored residents, the pending-return-list
drain to retirement, and task/frame preservation/progress remain open.
Storage preservation and source-conditional replay admission do not prove
those obligations or replace the unfinished source resource-soundness theorem.
