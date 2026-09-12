# Specification audit

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
adding `InputBindingProgress` and `LoanCompatibility` passes 208. The current
gate adds the repaired consumers `PublicValues` and `RuntimeWorldEquivariance`,
the promoted `LoanResourceRows`, `ReferenceTransferPreservation`,
`SnapshotResourcePreservation`, `AllocationFraming` and
`CopyResourcePreservation`, and passes 212 jobs, or 210 without the two
compatibility modules. It closes narrow
boundaries, not a batch or pre-entry theorem. `Authority.LoanCompatible` is the
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

Open at this boundary: compatibility with already bound outputs, pending
custody and owning-claim invalidation, the ordered whole-input/pre-entry
theorem, and the source pre-entry derivation. This is a single-input producer
plus a permission-only compatibility foundation; it is not general batch
progress and must not be reported as such.

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

The source-interpretation release adds three modules
(`ScopedAtomTransport`, `SourceInterpretation`, `SourceAddress`) and migrates
`LabelExecution`'s label-argument consumer. The migration deletes the assumed
payload `AddressType`: the located declared type is derived from the source
place (`PlaceType` plus its actual `ResolvesPlace` resolution), the caller's
`ContextBindingsTyped` and the world `TargetRepresentation`, and the value type
is related to the caller's translated label type by `DefinitionallyEqual`
rather than syntactic identity. The consumer's premise is the source
interpretation of the place (`Typing.SourceInterpreted`), from which the runtime
closing law `Typing.SourceConversionClosed` is now derived
(`SourceInterpreted.sourceConversionClosed`) instead of being assumed: its
definitional fragment (structural steps, rows and alias expansion, including
`ScopeInstantiation.definitionalStep_alias`) is proved, while the general
runtime-image derivation and the projection transport
`Typing.ProjectionStepConversion` remain recorded obligations. The other stated
premise is `Typing.TargetRepresentation`, which requires that every located
declared type is a structural head and that every source field step has its
actual physical field offset; the alias-headed `LayoutOf` case without a
corresponding physical `FieldOffset` derivation is the recorded gap there and is
being closed by the physical-realization lane. Neither premise is weakened by the bridge, no declaration of the
previous tree is dropped, and no other module consumes the two changed
theorems. The composed strict gate including `SourceAddress` and `LabelExecution`
passes 215 jobs from a fresh source-only tree (213 without the two compatibility
modules).

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

Post-cancellation cleanup is now executed rather than only classified:
`CleanupExecution` proves that the machine's own `cleanupRoot`, `destroyVacant`
and `retire` steps actually retire every captured root of a cancelled
suspension, and connects that to the real cancel rule. It provides the two
`RegionCanEnd` transport facts the chain needs (ending a region leaves the roots,
loans and reservations unchanged; retiring storage only removes one root's
liveness and its now-empty value), composes cleanup segments along their traces,
and proves the per-root and whole-list retirement runs. The residual readiness is
exact and named: the captured-root list is duplicate free, and every captured
root is live, empty and endable in the restored world. Vacancy through the
destructor chain for non-vacant captured residents, ending the suspension's own
live loans first, and executing the scheduled region closure (which reuses the
same shape and the two transport facts proved here) remain open.

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
names the suspend-time source product that replay-time `Replayable` needs; moving
that admission across intervening steps and the actual post-cancel cleanup
execution remain open and are owned by the suspension and frame/cleanup lanes
respectively.

This is not whole-language soundness. Private, complete control-lifetime and
foreign-runtime consumers still need the changed raw/failure constructors.
General input/pre-entry progress needs a mode-aware pending-loan/custody
interference contract; independent initial input permissions are insufficient.
Label and other allocation sites, remaining raw primitive progress, physical replay,
cancellation execution and task/frame preservation/progress remain open.
Storage preservation and source-conditional replay admission do not prove
those obligations or replace the unfinished source resource-soundness theorem.
