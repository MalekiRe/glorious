# Hardest-first completion order

The active priority is the user's instruction to do the hardest remaining
obligation first. A checked draft, a new local feature, or a build count is not
the completion criterion. This order preserves the standalone language-spec
scope; it does not add compiler implementation or library-algorithm verification.

The purpose is a semantic Lean definition of the compiler's intended language
semantics and correctness contract before implementation. Routine unit tests
and test-style concrete examples are not useful for this phase; use them only
in extreme cases to isolate a specific modeling error. Lean proof checking
remains necessary. Work in large, dependency-coherent chunks that close difficult
general semantic obligations; helper lemmas are intermediate steps, not the
default deliverable. Do not substitute example coverage for general proofs.

## 1. Nonvacuous semantic soundness — active

Establish preservation, progress, ownership/lifetime safety and lawful resource
completion for the actual execution relation. `ResourceAdmission` still
quantifies over runs and requires progress and resource completion. Storage
typing has been removed from that admission and proved separately. Projecting
the remaining requirements out of admission is not the missing soundness
proof. Moving the same assumption into a certificate is not a repair either.

Work outward from the required invariant and its proof failures:

1. Prove the storage algebra, typed destination obligations, partial-hole
   invariants and reference preservation for arbitrary storage paths. Keep one
   authoritative address/field product and migrate its real consumers.
2. Establish complete control-state validity: environments, frames, active
   labels, loans, activation freshness and suspended continuations. Prove the
   hardest replay, cancellation, transfer and cleanup cases against that state.
3. Supply compositional resource judgments and derive their execution safety;
   migrate admission to the proven boundary instead of assuming its conclusion.
4. Prove meaningful source-admitted nonvacuity and progress, including calls,
   mutation through unique references and abnormal control. A single empty
   program is not sufficient evidence. Allocation/host failure and legitimate
   outward outcomes must be explicit, not stuck states.

`Preservation.lean` starts the general proof. It establishes root location/loan
preservation and arbitrary-path address/field-offset preservation outside a
write's proper ancestors. The strengthened parent/location invariant now derives
that exclusion for transfers, so retained reference and unchanged value-tree
typing transport no longer need the path condition as a hypothesis. Borrow,
transfer and loan ending preserve the new loan sub-invariants. `StorageTyping`
now proves agreement of all resident field forms with the same `FieldOffset`
product, using declaration well-formedness and the shared body inventory.
Arbitrary-path clear/install proofs compose into typing of every resulting
transfer resident, including changed ancestor trees. `TransferPreservation`
derives resident origins from the actual writes, proves owner uniqueness and
all world metadata/loan invariants, and establishes `Transfers.wellFormed` and
`Transfers.worldTyped` for arbitrary storage paths. Neither theorem assumes a
safe post-state or resource admission. Other storage operations and machine
preservation remain open.
The existing `PreservationChecks` examples apply these results to whole-root
and nested move-and-restore executions; they are not the general soundness proof
or evidence of source-program admission. Following the current working method,
further work prioritizes general obligations, not additional examples.

`RelocationPreservation` now derives the entire world invariant for snapshot
copying. `CopiesSnapshot` no longer assumes its output is well formed. The
proof required repairing the shared-loan graph: copied handles receive fresh
shared loans even for external referents, and parent edges retain unselected
unique ancestors. This establishes world-invariant preservation and correct
reference target/region relocation, not full relocated value typing or the
complete control-state/replay/cancellation theorem. Those remain active.

The copied-pointer case now has a complete producer-to-consumer proof in
`PointerPreservation`. Resident pointer typing requires allocation/base/offset
coherence, without claiming liveness or permission to dereference. Allocation,
reallocation, offset and address derivation establish it; writes, bulk moves
and retirement preserve it. `PrimitiveStep.pointer_result_typed` proves typing
of the actual installed outputs, and `CopiesSnapshot.pointer_typed` proves the
relocated pointer case, including address-width bounds and unchanged generation
and domain. General transfer preservation consumes the strengthened invariant.
No post-state typing assumption is added. Full snapshot typing still requires
declaration-instantiation equivariance and lifetime support for external
referents; the control-state/replay/cancellation obligation remains open.

`ResumptionPreservation` now establishes the quantitative control invariant
for every actual machine-step family, every finite run and every finite prefix
of an infinite execution. The real invocation entry contract requires unique,
fresh, consistently identified suspension budgets; a general constructor proves
the condition for empty initial tables. Existing budgets cannot be overwritten
by new suspensions. Trace replay counts equal the increase of the actual table's
use count, including identities created during the run. Replay through aliases
therefore cannot exceed the declared upper bound; inactive budgets have lawful
quantities and cannot be replayed again, and exact obligations cannot be
canceled later in the run. No resource admission or typed post-state supplies
these conclusions. This is budget/lifecycle safety, not physical cancellation
completion or proof that every normally returning clause discharges its pending
obligations. Frame ownership, reference-lifetime support and cleanup progress
remain part of the same unfinished full control-state invariant.

## 2. Source and normative adequacy

Storage creation and teardown now compose through the real cleanup steps.
`AllocationPreservation` proves fresh empty storage preserves all world facts
and typing. `BorrowPreservation` proves the new handle, changed enclosing
aggregates and the full parent/alias graph stay valid, consuming actual
referent-location typing from the repaired borrow producer. Invocation/pattern
input binding consumes these results.

`LifecyclePreservation` proves general nested clearing, storage retirement,
loan ending, reservation deactivation and region closure preserve world typing.
The proofs exposed and repaired missing lifetime guards for active reservations
and resident binding packs. Buffer release now uses that same region-closure
relation, and shell cleanup retains and rechecks its access authority.
`CleanupPreservation` derives `Step.cleanup_worldTyped` for all actual cleanup
task transitions, including cancellation and destructor-handle creation, and
lifts it over cleanup run segments. This does not prove progress, completion,
resource discharge or arbitrary destructor-body execution: those still require
the full invocation/frame/control-state invariant, including generic drop-hook
admission. Neither an admissible post-state nor resource admission supplies
these storage-preservation conclusions.

`LocalPreservation` now proves `LocalStep.worldTyped` for every ordinary local
transition, not only cleanup tasks. Fresh-region creation, call entry and
input binding, result protection, owned receiver consumption and pattern
deconstruction all preserve the same world invariant. Shell consumption is
proved from the actual same-type structural write and retained resident
identities, without inventing a new physical-path admission condition.
`CopyPreservation` proves the complete world and typing invariants for source
Copy, including fresh owner separation and binding-fact origin renaming, and
composes them through actual acquisition, capture and observation-copy rules.
Atomic construction, non-cleanup effect/control/primitive steps and full task
and frame preservation/progress remain open.

The immutable declaration admission now excludes literal execution identities
through its complete semantic term projection, including captures, defaults
and invocation contracts. `InstantiationEquivariance` consumes that correction
to prove kinded substitution, nominal constructor fields and callable capture
fields commute with runtime-region relocation. Full snapshot value typing is
still open: quantified entailment requires a supported permutation action,
and the sealed environment ledger and external-referent lifetime contracts
need coherent runtime instantiation and control support.

Runtime-region generativity is now part of the authoritative root typing
contract, including vacant and retired roots. Allocation requires that a type
refer only to identities already allocated; existing transfer, borrowing and
lifecycle consumers preserve that contract. This does not require old regions
to remain live. `RuntimeSupport` proves a total fresh-name permutation that
agrees with executable relocation on supported terms, using one shared term
action in both the actual relocation and its proof. `SnapshotTyping` derives
support for nested residents and vacant locations from nominal/callable
instantiation and the actual root contract, proves permutation agreement at
those locations, and preserves all original values under snapshot copying.
Full copied value typing still requires static entailment/layout equivariance
and external-referent lifetime support; no such conclusion is assumed.

Operation-value construction now consumes the same `OperationInstance` as
performance. The former declaration-only lookup did not authenticate generic
arguments or constraints. Complete atomic storage preservation is still open.

The scalar producer boundary now has general integer-operation totality and
result-range proofs in `ScalarPreservation`: every supported integer arity
produces a valid result or an explicit fault. Scalar result validity follows
from operand/destination validity. Fused multiply-add now covers nonfinite
inputs without rounding a finite product before the addition, and character
narrowing has an explicit out-of-range outcome. These corrections are consumed
by the actual primitive-calculation relation. General finite floating-point
rounding/square-root existence and the distinction between trapping machine
conversion and the library's conversion policies remain open; this is not a
claim of complete scalar or source-library conversion semantics.

The conversion primitive now carries an explicit lossy, checked or exact
policy, replacing the earlier mixed behavior. All consumers use shared integer
bounds and the same rounding relation. `ConversionPreservation` proves total
valid integer-destination outcomes for every policy, deterministic integer and
fraction policy decisions, exact-value preservation and the checked half-open
input interval. Thus negative fractions cannot become successful checked
unsigned zero by truncation. Floating-destination policy decisions consume an
actual rounding witness; general rounding existence and the checked library
Result construction remain separate obligations. Fatal machine outcomes are
not treated as catchable source conversion errors.

`ScalarSignatures` now supplies the primitive-identity-specific scalar arity,
argument and result contract to the actual `Typing.AtomType.primitive` rule;
an arbitrary manifest signature cannot admit a mismatched scalar operation.
`ScalarProgress` derives a valid normal result or explicit fault for every
admitted nonfloating-result scalar calculation from actual typed scalar reads,
including floating comparisons and finite/nonfinite inputs to integer
conversion. Its result-type theorem covers all successful scalar families.
`IntegerDeterminism` proves arithmetic's normal/fault outcomes are disjoint and
deterministic. Finite floating rounding/square-root existence, result storage
creation and full primitive-step progress remain open.

After the soundness foundation, prove that elaboration and observations give
the normative language meaning. This includes complete source coverage,
contextual/implicit captures and arguments, sealed binding provenance, generic
and associated inference, effect/label behavior, and observable equivalence.
Required producer repairs discovered while proving item 1 are dependencies of
that proof, not a reason to return to feature-by-feature scheduling.

The sealed environment contract now carries its frozen resident-type product
through `Term.environment`, `Term.available` and the runtime reservation ledger.
The uninstantiable declaration-side environment lookup has been removed.
Reservation formation authenticates the actual locations and exact types;
capability, lifetime, layout and contextual invocation consume that same product.
`ControlPreservation` proves atomic witness publication from the actual storage
constructor, then storage preservation for the complete reserve/call/consume/
close cycle. `TestPreservation` completes the pattern-result construction and
proves `ControlStep.worldTyped` for every control transition. The earlier test
exception and its partial theorem have been removed. Full task/frame typing
and progress are not claimed by this storage theorem.

`ConstructionPreservation` now proves full world preservation for `NewValue`
from actual head/field typing and fresh-owner facts, and consumes it in
`AtomStep.worldTyped` for every atomic constructor. Constants retain their
static type derivation and now also authenticate instantiated constructor
identity and field shape through the same `ConstructorHead` product used by
runtime construction. `EffectPreservation` proves home reassignment, handler
installation, clause entry and continuation creation preserve world typing.
`EffectStep.worldTyped` now covers every effect step, including copying replay
through the complete relocated-value typing theorem below.

`FloatRounding` proves finite rounding existence over an exact finite format
grid, with nearest-even selection and explicit overflow/nonfinite outcomes.
`FloatProgress` consumes it for nonsquare-root floating calculations and all
floating-destination conversion policies. `FloatSqrt` proves the remaining
square-root existence obligation from rational isolation: exact midpoint-grid
roots use point intervals, while other roots have a tie-free interval whose
entire contents round to the same result. Exceptional inputs are covered too.
`ScalarProgress` now derives valid results or explicit faults for every admitted
scalar calculation; its earlier restricted theorems are corollaries. Full
floating determinism, result-storage progress and checked source-library
result construction remain open.

The actual memory producers now require supported element regions, a
representable pointer-width element count, and old/new array element agreement
on reallocation. Bulk relocation requires pairwise disjoint sources and
pairwise disjoint destinations, while retaining legal cross-range overlap;
each insertion consumes its actual post-clear address type. `MemoryPreservation`
derives typed allocation, reallocation, overlapping bulk relocation and raw
read/write/borrow preservation from those actual producers, then proves
`PrimitiveStep.worldTyped` for every primitive transition. This is full storage
preservation, not allocation existence, resource admission or primitive progress.
Snapshot copying
now explicitly checks that captured references to unchanged external storage
cannot rename a local identity in that storage's referent type. This is an
input scope-closure obligation, not a typed-output premise. Its derivation
from the eventual control-state invariant and full replay progress remain open.

`RuntimeEquivariance` proves capability equations and their greatest models,
kinded substitution, quantified entailment, equality, lifetime and row
relations, declaration instances and all layouts invariant under a supported
runtime-region permutation. `SnapshotWorldTyping` consumes these results in
`CopiesSnapshot.worldTyped`: every copied and retained resident, including
nominal/callable fields, references to internal or unchanged external storage,
operation values, pointers and binding packs, preserves the full world typing
contract. The proof uses the actual snapshot map and its input scope closure;
it assumes neither declaration commutation nor a typed copied world. Full
continuation task/frame typing, code relocation and replay/cancellation
progress remain separate unfinished consumers.

Atomic pattern construction uses a proof factor of the same world invariant:
private binding packs may refer to the enclosing result's future owner, while
actual owner allocation, uniqueness and every other invariant remain intact.
`World.WellFormed` and `Typing.WorldTyped` retain exactly their previous
allocated-origin bound. The complete result theorem closes that bound at the
actual final constructor. Existing allocation, clear and construction proofs
consume this factor internally and retain their original public guarantees.
Observed bindings and unit fields derive their exact types from actual
locations/reads. `CarrierFields` now consumes the shared `ConstructorHead`,
removing a separate constructor lookup that did not authenticate agreement
with the manifest-selected nominal result type.

Relocated signatures and scope closing now share `Signature.mapTerms`,
including generic defaults and quantified-constraint defaults. The incomplete
independent relocation constraint walker has been removed. The signature and
context-commutation proofs in `RuntimeSignatureEquivariance` reach actual
`Typing.CallSignature` and relocated tail requests. Full body/coverage and
continuation-frame transport remain open; those require lexical body support
and transport of the semantic coverage obligations, not assumed stability.

The lexical body boundary is now closed through the actual callable consumer.
`BodyInventory` checks the complete function-template term projection, including
nested bodies, patterns and invocation contracts. Generic instantiation and
runtime relocation share one structural syntax transformation, with their
distinct signature actions explicit; the duplicate relocation walker is gone.
`RuntimeCodeEquivariance` proves exact `Instance.permute`, including the complete
body, and `SnapshotWorldTyping` consumes it in place of the former captures-only
instance theorem. Full `CodeType`, pattern coverage and continuation-frame
transport still require proof; exact instance transport is not their conclusion.

`FloatDeterminism` proves uniqueness of nearest-even rounding, all floating
calculations (including rational square-root isolation and fused operations),
and conversion outcomes. `ScalarStorageProgress` constructs the actual vacant
destination write and derives scalar observations from typed, initialized,
permitted resident inputs. `ScalarMachine` and `ScalarExecution` compose this
with all scalar calculations and storage preservation: every lawful scalar
task has exactly one actual executable normal/fatal step and a typed post-world.
No calculated result, write witness or typed output is assumed. Deriving those
lawful task inputs from source/control typing, general non-scalar progress and
checked source-library result construction remain open.

Foreign calls now carry an immutable selected invocation and thread one ambient
host state through nested callbacks. The host's declared session protocol and
actual storage mutations replace the old arbitrary post-world transition.
`ForeignPreservation` derives every foreign step's world typing from existing
allocation, copy, borrow, construction, raw-memory and lifecycle producers.
Registrations refer to the actual callable owner, with evolving runtime and
registration liveness; captures use the common invocation input relation.
Lent callbacks obtain real child loans, excluding conflicting re-entry through
their parent authority, and end the reference handle before restoring that
parent. Normal result transfer preserves active registered owners, and retained
owners are excluded from actual source activation/scope cleanup. Full registry
preservation across arbitrary source callback execution and callback/cleanup
progress still depend on the complete control-state invariant.

`ExecutionPreservation` now proves `Step.worldTyped` for the sole executable
relation with all six transition families, and `Run.worldTyped` for every
finite execution prefix under the host's mutation/protocol laws. This closes
full storage preservation without resource admission or any typed-post-state
premise. It does not close semantic soundness: task/frame preservation,
ownership/lifetime progress, source admission and resource completion remain
active. In particular, ordinary/contextual invocation still needs the common
real-loan producer integrated with callee-owned lifetimes, including proper-tail
entry; merely wrapping owner authority as lent is not an adequate contract.

That invocation producer is now repaired. `FormsLoan` is the single loan
constructor; source `Borrows` retains its addressability restriction, while
hidden invocation leases can lock logical storage without exposing a source
reference to a label or environment witness. `LendsResident` allocates the
ordinary cleanup handle and is consumed by receiver lending and every lent
`BindsInput`. Ordinary and contextual calls retain an explicit entry recipe
until the fresh callee activation exists. All captures and arguments then use
the common binder. `InvocationLending` proves parent exclusion survives the
entire input binding, reaches actual normal/tail entry steps, includes the
receiver lease in callee cleanup and excludes it from a fresh caller's cleanup.
The old wrapper-only examples are retained as rejected modeling regressions.
Full cleanup progress still requires restoration/lifetime obligations from the
eventual control invariant, not merely this exclusion theorem.

Foreign callback return now schedules ordinary reference destruction, recursive
parent-loan release and handle retirement before resuming the host protocol.
The earlier atomic receiver-lease ending relation is removed: it could end a
child without revisiting an unreferenced parent whose release had been deferred.
The general execution and resumption preservation proofs consume the new path.

Dynamic indices now belong to the shared recursive projection resolver, with
one unique environment-binding selection and initialized, readable unsigned
pointer-sized index values. The separate one-index-only place rule is removed.
`ProjectionResolution` and `ProjectionStorage` prove unique address/authority,
arbitrary projection composition and live/vacant storage location transport.
`PrimitiveDispatch` consumes that resolver and manifest uniqueness to derive
actual dispatch identity from static primitive admission. Canonical resident
type agreement through equality, aliases and associated projections remains
open; it is not supplied by assuming the scalar task's desired input types.

External manifest signatures now use the same complete lexical term seal as
declarations, before runtime generic instantiation. `RuntimeTypingEquivariance`
consumes it for full atomic, invocation, pattern, place and subtype transport.
Full code typing still requires transport of coverage over arbitrary typed
worlds, and static implementation-head coherence needs repair before associated
normalization can justify the source-to-runtime representation boundary.

`InvocationLeaseCleanup` constructs the ordinary reference-destruction,
recursive parent-release and root-retirement execution for the actual
`LendsResident` handle. Its decreasing measure is the canonical loan-parent
identity order. A referenced parent or a live child defers release; restoration
is required only for unreferenced ancestors without live children off the
released branch. An unrelated sibling's unique hole is not assumed initialized.
The activation-cleanup consumer uses the actual selected root and retains full
world typing. Proof that a completed call restores and keeps its hidden handles
private remains open; the cleanup theorem does not assume its own termination
or post-world typing.

`CapabilityModels` constructs the greatest model of the existing recursive
capability equations for every declaration program. Equation functionality
and permission monotonicity establish the fixed point over all post-fixed
assignments, without an acyclic-type assumption or an independent type walker.
Unsupported equations remain unknown, not permission. The prior existential
`PrincipalOf` judgment selects exactly this unique greatest answer. Invocation
lease disposal now consumes the constructed shared/unique principals and no
longer assumes a capability model. Generic destructor dispatch still needs its
actual checked specialization carried from the nominal resident to hook entry.

`SemanticPreservation` connects the public transition system to the actual
execution relation in both directions, with exact filtered traces and identical
reachable states. It derives storage typing for all public reachable states,
finite observations and every state in an infinite execution. The redundant
typed-post-world clause has been removed from `ResourceAdmissionAt`; it is now
a theorem of execution, not another source admission condition. Public
`WellFormed.no_invalid_reachable` consumes the result. This proves the storage
part of public safety, not `TransitionSystem.Safe`: task/frame preservation,
progress, initialized representable results and resource completion remain
unfinished and must not be inferred from world typing alone.

The public result observer is now complete for initialized typed residents.
`PublicValues` proves existence, uniqueness and exact initialization of logical
value views, including operation values and contextual/control carriers.
Callable observations recursively retain their captured residents instead of
erasing them. These logical observations do not authorize runtime addresses or
lifetime escape for proof-only values. The actual `Finished` relation consumes
the observer for returns and outward effect payloads; every admitted outward
request now produces a public result. Under existing semantic resource
admission and its input-access condition, `resourceAdmission_safe_iff` proves
that full public safety is equivalent to preservation of initialized stopped
result addresses. This identifies, but does not assume or discharge, the
remaining return/cleanup lifetime invariant. Source resource admission itself
remains a semantic obligation rather than a proved structural typing rule.

`RuntimeWorldEquivariance` transports the whole existing storage world,
including loan ancestry, permissions, partial residents and region freshness.
It constructs the world required by universally quantified pattern coverage;
neither exhaustiveness nor branch usefulness is assumed stable. Full effect
coverage uses that same world/permission/matching transport and exact selected
operation signatures. `RuntimeBodyTyping` then proves transport of all five
mutual code/arm/handler typing judgments and complete function typing.

Finite snapshot relocation now consumes this result through the actual
`SnapshotMap`: the checked lexical template and supported invocation arguments
determine the exact relocated whole function, including its body. The actual
snapshot capture/value consumer projects that common producer. The weaker
existential operation transport and duplicate signature-preserving proof are
removed. Source lexical scope closing and runtime context/frame typing remain
open: unrestricted rigid-name admission and the missing relationship between
body lifetime binders and outward signatures must be repaired at their actual
producer before a sound copied-frame/control invariant can be established.

`DropApplication` now selects the actual generic destructor declaration using
the nominal resident and independent borrowing region. Declaration admission
requires a selection for every supported nominal application, rather than
checking an uninstantiated result and effect row. `DropDispatch` consumes the
body inventory and ordinary function admission to construct the executable
hook instance, fresh owned reference input and typed hook-entry transition.
The old zero-argument specialization is removed. Destructor restrictions now
hold for all finite execution prefixes, including prefixes of divergence;
they are not conditional on a hook reaching a final observation. The nominal
discard restriction follows from the authoritative capability equation.
Capability-domain admission, receiver restoration and complete destructor
execution/cleanup progress remain open. The frozen destructor batch and its
execution/public-safety consumers passed the targeted Lean gate (59 jobs).

Associated defaults specialize under the owning trait's checked binders and
the associated item's own binders. These substitutions are simultaneous:
sequential rewriting incorrectly captures caller parameters that share an
item-binder identity. The selected implementation's substitution does not
interpret a trait-owned default body. The actual equality rule and its
runtime-equivariance consumer use the corrected substitution product.

The foreign protocol now bounds host authority by actual input handoffs,
retained external callbacks, explicit imported external-storage grants and
fresh allocations within each uninterrupted host step. Projection, dereference
and raw-pointer access use the existing storage authority and provenance rules.
The actual host mutation constructors consume that authority; an arbitrary
`writable` predicate no longer permits access to unrelated source-frame roots.
Nested callbacks expose enclosing host handoffs and their protected returned
value, not their hidden invocation leases or arbitrary source allocations.

`ForeignEvolution` proves home preservation and the exact origins of newly
created loans from those mutation producers. `ForeignAuthority` derives privacy
of fresh lending handles and preserves every unexposed internal resident, with
world typing, through arbitrarily many actual consecutive host continuations.
Its post-world privacy is a theorem, not a foreign-contract admission premise.
The targeted foreign/execution/public-result gate passed (62 jobs). This closes
the host-only authority boundary, not arbitrary callback execution: source
control must still preserve private placement across callbacks and prove that
returned values cannot name hidden leases. Persistent external registration
invariants and initialized return/cleanup preservation also remain open.

Callback registration now requires the exact handed-off callable authority,
including its shared view, for every newly active record. Retention adds the
contract's permission; it cannot turn mere address reachability into ownership.
The old address-only registration admission is removed. `ForeignRegistration`
derives authority grants from actual start, return and host-step laws and proves
their origin through arbitrary host continuations, with the exact trace split.
An unchanged record is retained verbatim; changes to its authority or activation
must discharge a new grant. This is registration-authority preservation, not
yet the source lifetime/frame invariant for externally retained callbacks.

Foreign private-storage preservation now covers the exact root, including
vacancy, liveness, generation and all storage metadata. `ForeignRootFraming`
derives the root frame from each actual storage producer, including raw buffer
reallocation and release. `ForeignAuthority.HostRun.internal_root` preserves
that same root through arbitrary host continuations; resident preservation is
a projection of this stronger invariant. The former privacy proof's dependency
on the host's frame-postcondition law is removed. Source callbacks still need
the shared control-origin invariant: hidden roots must not appear in incoming
suspension inventories or be exported by source control transitions.

Executable lexical regions and brands now have constructors distinct from
universal eigenvariables. One explicit lexical scope admits them and one runtime
scope map closes them. Declaration signatures and capture interfaces exclude
body-local names; actual runtime instances inherit closed generic arguments.
Source closure checking uses declaration invocation signatures, not the runtime
instance relation. `ScopeClosing` proves closure of scoped terms under a
covering runtime map; `ContextTyping` derives it for typed body results.
`InputTyping` and `ContextTyping` derive real entry bindings from the
shared ordinary/capture/callback recipes and sequential input transfers.
Fresh scope, brand, label and clause consumers use the same product. Labels
look up their lexical lifetime instead of silently rebinding it to the cleanup
region; attached handler arms preserve their lexical unsafe-site permission.
Whole-body binding persistence, copied external bindings and complete frame
typing remain open, especially for retired locals and loan-backed subobjects.

Drop's actual generic application now discharges its affine prerequisite in
an assumption-free context. `DropCapabilities` propagates the constructed
canonical capability through all initialized nested residents, and dispatch
derives disposal permission instead of taking it as a premise. Normal hook
completion requires the original loan ended and the current Self initialized;
it does not assert that reassignment preserves the original Self owner or that
arbitrary parent loans survive. `DropReturn` consumes actual normal observations
and constructs the ordinary unit-result/handle cleanup suffix to the current
receiver's reverse field cleanup. `DropHandle` derives saved-handle vacancy
and privacy at actual function entry. Preserving that private caller state
through arbitrary hook bodies and completing nested field cleanup remain open.

Implementation matching now consumes actual inferred substitutions and positive
definitional convertibility, including reflexive opaque projections and unordered
row equivalence. The superseded eager-normalization matcher is removed. Actual
alias and associated bodies are kind-checked at their owner/item domains, and
`ProjectionKinding` derives kind preservation for every real expansion.
`DefinitionalCoherence` establishes selection coherence and joins competing
root expansions. This is not global confluence: contextual reduction, domain
transport and legitimate lexical-equality entailment remain explicit obligations.

Suspension admission now retains the actual capture-time root frontier, exact
saved-home domain and active ownership inventory. Incoming continuations cannot
claim future storage IDs. Ordinary storage retirement rejects suspended homes;
cancellation explicitly restores saved homes before running ordinary cleanup.
The former rehome proof has moved to one lower shared preservation module.
`ForeignSuspension` derives unchanged reservation metadata and preservation of
suspended-root locations/liveness from actual host mutations. Budget preservation
continues to use the existing component, but preservation of the full new
suspension-origin invariant across all source control transitions remains open.

This combined scope, destructor, positive-conversion and suspension-boundary
checkpoint passed the targeted Lean dependency gate (85 jobs), including foreign
registration/suspension, drop return/handle, context/scope typing, runtime body
equivariance, definitional coherence/kinding and execution/public safety. The
gate proof-checks this boundary; it does not establish the open general results.

The suspension-origin invariant is now preserved by both actual capture
instructions, final replay, cancellation and every foreign transition.
`SuspensionOrigins` derives the capture frontier and saved-home domain from
actual delimited-root selection; `SuspensionStorage` composes the existing
storage producers. `ForeignSuspensionOwnership` consumes that shared product
through host mutations and both ordinary callback handoffs. Reverse foreign
root provenance is derived too: a host cannot introduce a newly suspended
root. This boundary passed its targeted Lean dependency gate (62 jobs).
Copied replay and preservation through the remaining source-step families
are still required before claiming the invariant for arbitrary execution.

## 3. Remaining boundary completeness and final audit

Finish total primitive behavior, representation/ABI site coverage and target
obligations. Audit every requirement against authoritative evidence, preserving
negative regressions and distinguishing conditional theorems from established
existence. No unproved, circular, vacuous or missing requirement counts as done.
