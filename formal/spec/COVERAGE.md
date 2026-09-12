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
`ForeignEvolution`, `ResumptionPreservation`, `RuntimeWorldEquivariance`,
`AllocationLayout`, `FunctionEntryContextTyping`, `ScalarMachine` and
`PublicValues` fail as stale consumers outside the checked dependency graph;
their error sets are identical to the pristine pre-recovery tree, and the
recovery additionally repairs the duplicate `Value.Initialized.resident` that
previously made `DropCapabilities` fail. Full-source checking therefore still
fails; an older checkpoint result is not evidence for the current graph.

This is not whole-language soundness. Private, complete control-lifetime and
foreign-runtime consumers still need the changed raw/failure constructors.
General input/pre-entry progress needs a mode-aware pending-loan/custody
interference contract; independent initial input permissions are insufficient.
Label and other allocation sites, remaining raw primitive progress, physical replay,
cancellation execution and task/frame preservation/progress remain open.
Storage preservation and source-conditional replay admission do not prove
those obligations or replace the unfinished source resource-soundness theorem.
