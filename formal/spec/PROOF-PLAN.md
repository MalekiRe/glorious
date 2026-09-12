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
including its shared view, for every new record, even inactive ones. Retention adds the
contract's permission; it cannot turn mere address reachability into ownership.
The old address-only registration admission is removed. `ForeignRegistration`
derives authority grants from actual start, return and host-step laws and proves
their origin through arbitrary host continuations, with the exact trace split.
An unchanged record is retained verbatim; unregistering changes only its active
flag, while other changes must discharge a new grant. This is registration-authority preservation, not
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

That suspension preservation chain is now closed for the sole executable
step relation. The actual copied snapshot cannot introduce a suspended home:
its relocated roots use the original capture's saved local/temporary homes.
`SuspensionSource` covers local, atomic, control and effect transitions;
`PrimitiveSuspensionOwnership` covers every primitive branch. The general
`SuspensionPreservation` theorem composes all six families into finite runs,
actual observations, finite divergence prefixes and public reachable states.
It needs initial world/suspension well-formedness and actual host laws, not
`ResourceAdmission` or a post-state ownership certificate. Its current-source
dependency gate passed (74 jobs). The remaining drop/control problem is
retained hidden-handle and frame lifetime, not suspension inventory preservation.

Local binding types now persist across movement and retirement of whole
root slots. The actual sequential input and handler producers construct this
canonical relation, and successful reads consume real selection and storage.
Pattern/clause typing previously concatenated bindings despite execution's
sequential shadowing; both now use the common `Context.bindLocals` fold.
`PatternContextTyping` proves the scheduled pattern binding order and actual
binding-step context production. Live loan-backed subobjects still require
their retained invocation lifetime; whole-frame preservation remains open.

Positive definitional conversion now preserves full kinding, including row
equivalence and contextual reduction. Logical predicate transport uses one
template's actual substitutions and pointwise lexical equality. Entailment,
reference lifetime subtyping, type-outlives and RunsIn consume that evidence.
The original logical/runtime-equivariance dependency gate passed (37 jobs).

The combined frozen suspension, pattern/context, logical-evidence and runtime
equivariance checkpoint passed its targeted dependency gate (90 jobs).

The subsequent predicate boundary repairs the actual substitution operation,
not just a capture-admission side condition. Quantified binders are freshened
from finite lexical source/substitution support before caller values are
inserted unchanged. Each default masks and renames only preceding binders;
the previous whole-list default mask could incorrectly hide an outer name
that matched a later local binder. Runtime-region renaming commutes with this
actual operation because generative runtime atoms do not determine lexical
fresh names. The former arbitrary-term-map commutation claim is removed.

Published declaration requirements and invocation predicates now require
`ConstraintKinded` in their real declaration scopes, including owner/item
parameters and recursively ordered quantified defaults. This is kind
admission, not evidence that a predicate is true. One support-sensitive term
transport proof is consumed by the existing `Kinding.substitute` API and by
general finite-support predicate alpha-renaming. `PredicateSubstitutionKinding`
derives both the checked substitution graph and the kinding of the actual
hygienic result for every predicate constructor. No output-kind certificate,
global caller-name freshness, or eager normalization premise is used.
`PredicateAlpha` derives argument-order/kind and unchanged-caller-value
correspondence for the actual fresh quantified output binders.

Universal elimination now derives its substitution graph from source predicate
admission and actual ordered arguments. `PredicateAdmission` consumes published
admission at actual implementation selection, projection domains, nominal and
effect domains, and function/operation generic instances. Projection-domain
conversion no longer requires caller-supplied target capture admissibility:
the actual recursively masked kind checks are derived from conversion of the
existing raw environments. `ReductionResiduals` proves that root expansions
survive arbitrary child reductions and all row-equivalence laws, with actual
positively reduced or row-equivalent results respectively.

Global confluence, termination/scalar discrimination, and complete trait-method
selection remain open. An additional admission audit is required for `ImplLocal`:
it still uses logical equality under implementation requirements to establish
nominal self locality, unlike the positive-conversion head-matching path.
The checked invocation-entailment rules also need their actual generic-domain
and declaration-requirement connection audited; kinded invocation instances
alone do not establish that stronger logical contract.

The frozen predicate/admission, reduction-residual, runtime-equivariance and
primitive-dispatch dependency gate passed (47 jobs). The major whole
umbrella gate did not pass: `DropCapabilities.Entails.use_principal` cannot
invert logical congruence or quantified elimination into the current
syntax-indexed canonical capability equations. In particular, those equations
have no projection case although logical equality can identify a projection
with a type that has a principal. This is an authoritative capability/equality
mismatch, not an omitted proof case; adding a postulated capability to Drop
admission would not repair it. Existing `PreservationChecks`, `BorrowChecks`
and `SourceChecks` also contain stale proof obligations at strengthened
admission boundaries. Their failures are preserved; no full integration or
runtime Drop-preservation success is claimed.

The head-coherence audit also exposed an overstrong admission premise:
`HeadSolutionsCoherent` requires positive joinability of arbitrary matching
substitutions. With a single generic implementation this already implies
joinability for arbitrary kinded definitionally equal arguments, hiding the
global confluence obligation in admission. That premise must be repaired to
state actual semantic uniqueness, and its joining consumers must derive
positive joining independently. The current checkpoint does not establish
global confluence from that premise. The following checkpoint repairs the
actual admission condition to `SubstitutionsConvertible`, preserving binder
keys and pointwise definitional equality. Selection uniqueness consumes this
condition; the unsupported unconditional root-joining consequence is removed.
Independently witnessed joining still yields unique expansion-normal endpoints
and scalar identity in `DefinitionalNormalForms`. No global common-reduct
existence is assumed or concluded.

## 3. Remaining boundary completeness and final audit

The actual control-address provenance boundary is now closed through all six
machine-step families. `ControlOrigin` defines support of current tasks, frames,
callback sessions and captured control, including nested hook-cleanup tasks.
Saved contexts, handlers and frames are bounded by the existing immutable
capture frontier, not merely by the current world's allocation counter.
`ControlOriginPreservation` establishes this combined control/suspension
invariant for arbitrary runs, observed states, divergence prefixes and public
reachable states. The canonical `InitialInvocation` contract consumes it;
the empty-entry constructor derives supplied-input support and requires
caller-environment bounds and recorded authorities. No alternate execution relation, new runtime
inventory, post-state certificate or resource-admission premise supplies it.

This repairs a real hole in the earlier suspension invariant: an incoming old
suspension could otherwise keep a forged future address in its saved context
even though its owned-root inventory was historically bounded. Both actual
capture forms establish the new saved-control component, ordinary execution
retains it, and final/copied replay derives current support from the same
saved product and executable relocation map. `DropSuspension` now consumes the
whole-run result to exclude the freshly allocated private hook handle from
both old inventories and old saved control, as well as their cancellation
root lists. This is historical address provenance, not unconditional storage
liveness. Retained activation/scope ownership, arbitrary-body preservation of
hidden handles and initialized normal-return lifetimes remain on the same
unfinished dependency chain; transfer and cancellation may legitimately
dispose abandoned frames. At that checkpoint, `DropSuspension` remained
blocked by the capability-extraction failure recorded above. The later lower
private-storage integration below checks this consumer without the unused
`DropReturn` dependency; it does not claim to repair Drop capability inversion.

Saved-home provenance now authenticates the actual cleanup roles as well.
`FrameOwnsHome` is the authoritative home-based ownership judgment used by
`FrameOwns`, delimited capture and abandoned-frame cleanup. `CaptureOrigin`
requires each saved home to belong to the computation scope or a captured
cleanup-owning frame; its previous arbitrary local/temporary-home fact is
only a derived projection. Both capture producers and the complete suspension
preservation chain consume this stricter contract. `SuspensionOwnership`
proves that actual final and copied replay, including the protected argument
move, reassign every inventory root to a frame actually reinstalled. Its
whole-run consumer covers replay after arbitrary execution, and cancellation
restores only authenticated homes. The same audit repaired `scopeReturn`:
its cleanup selector now uses the popped frame's activation, not a potentially
unrelated yielding context's activation; the actual transition's selected
roots are proved owned by that frame. The current-source control-preservation
gate passes 85 jobs with these dependencies. Retained caller-frame lifetime
remains open; saved loan-authority provenance is established by the following
extension of the same control/ownership invariant.

`Authority.Recorded` now requires an actual historical loan-table entry for
every non-owner authority, including shared backing authorities. The existing
world well-formedness contract requires it for all reservation entries, even
inactive ones. Previously, a vacant reserved place could carry a guessed future
loan identity and later introduce it into cleanup. Actual reservation creation
derives the requirement from its resolved operand permissions; all world
producers and runtime permutation preserve the stronger contract.

The same `ControlWellFormed` now records authorities of actual current tasks,
retained frames and saved control, including pending loan release, hook loans
and callback leases. The existing suspension-storage product carries historical
recording through ordinary storage, host mutations, capture and settlement.
The single saved-property classifier serves both address and authority support;
copied replay proves authority recording from the actual mapped loan entries.
All six machine-step families, arbitrary runs, observations, divergence prefixes
and public reachable states preserve the canonical combined invariant.
Immutable resumption metadata now includes saved contexts, handlers and frames,
so an old saved authority cannot acquire a newly created loan identity after
arbitrary execution, even when its referent address was already known. The
corresponding Drop-guard integration remains unverified: its consumer's gate
is blocked by capability inversion, not certified by the successful general
control gate.

Recording is historical provenance, not permission or live retained-frame
ownership. General cleanup framing for retained caller homes and reference
guards remains open. The opaque host-origin gap is closed by the following
extension; it does not imply live retained-callback permission.

`ForeignAuthorityOrigin` covers actual current and inactive registration records.
The canonical `InitialInvocation` is now indexed by the real host model and
requires historical recording of its initial registry authorities; all observation,
divergence, semantic admission and reachability consumers use that initializer.
The actual registry transition contract is the declarative `RegistrationOrigin`:
retain an exact old record, unregister it without changing its authority, or
register through the shared access resolver and retention grant. Initial inactive
records cannot guess future loan identities and later launder them by activation.
Explicit imported external-storage grants supply root authority only; actual
loan authority comes from a handoff, registration or resident reference, not a
guessed identity that happens to exist at access time.

Actual start, host continuation, callback entry/return and storage producers derive
registry recording from those origins. Every execution-step family, arbitrary
finite run, canonical observation and divergence prefix preserves it, using the
same control and suspension-storage provenance products. The strict targeted
host-origin dependency gate passes (95 jobs). Recording is not initial callable
permission or retained liveness; source mutation and callback lifetime framing
remain separate obligations.

The existing exact registration-grant history now covers all actual startup,
host-action and callback-return boundaries, with each grant tied to its real
intermediate mutation world before source lending or result transfer. The general
`Execution.Run.registration_origin` consumes every source/host step and produces
the exact trace split around a grant, or the exact original admitted record.
Its canonical invocation consumer shares `Execution.Step.host_state` with the
historical authority invariant; copied replay cannot restore an old opaque host
registry. The strict combined host-origin/history gate passes (95 jobs). This
establishes authority history; callback runtime lifetime is established by the
following actual protocol/control repair.

`CallbackAdmission` now consumes the actual current callable permission,
selected source function, bounded ABI entry and runtime in the host's new state.
Previously, a host action could remove a runtime and still dispatch a callback
using its old registry snapshot. Lent callbacks retain their exact active record;
owned callbacks atomically consume registration ownership before ordinary source
receiver consumption. This does not require a consumed callable to remain
initialized or pretend that a parent's permission remains usable while lent.

The actual `CallbackEntry` replaces the callback frame's old bare registration ID.
The same frame remains present through reference/Drop cleanup and is popped only
by the actual callback-return transition. Previously, popping it before cleanup
also removed the foreign control barrier while the C return was still pending.
Captured-control origin now requires foreign-free saved frames, derived from the
real effect route. Pending foreign returns in a hook's cleanup count as foreign
control too; the shared effect/label barrier preserves ordinary frame behavior
while rejecting those hidden returns and forged initial saved foreign frames.

`HostStateEvolution` replaces the registration-only transition contract. Its
existing registration-origin obligation is paired with no shutdown of runtime
handles actually handed to this host session. Those handles come from actual
callback/hook control, persist through protocol advance and callback return, and
refer to the model's existing runtime inventory. `ForeignRuntimePreservation`
derives handoff coverage and runtime liveness through all six step families,
arbitrary runs, canonical observations, divergence prefixes and reachable states.
Active callback frames and pending return tasks therefore retain a live runtime
through arbitrary intervening source and nested host execution. The strict
runtime dependency gate passes (97 jobs); the migrated source-entry gate passes
(64 jobs). This runtime theorem does not establish that distinct owning source
aliases cannot consume a retained callable's environment.

`ExternalHomePreservation` now carries the retained-storage ownership projection
through arbitrary execution. The existing ordinary `SuspensionExtension`
extends the authoritative `HomeExtension`, removing its duplicate root counter;
all real storage producers and consumers share exact old-home preservation.
The exceptional capture and restore cases use actual `DelimitedRoots` and the
selected suspension's current active ownership, so historical saved metadata
cannot rehome an unrelated exterior root. Copied replay preserves old homes
through the actual fresh relocation.

The general run theorem retains every external/allocation home across source
code, nested host callbacks, unique lending, owning consumption and cancellation.
Actual registry-changing producers establish that every active retained record
has an exterior owner at introduction. Whole-run consumers distinguish exact
initial records from later introduced records; canonical initial historical
authority alone is not silently treated as storage evidence for an old record.
After actual checked host handoff or normal return, every later active retained
owner is excluded from scope cleanup, activation cleanup and active cancellation
inventories, including the actual root list scheduled by cancellation. The strict
combined home/control/callback-runtime dependency gate passes (108 jobs).

This closes implicit source cleanup/cancellation ownership separation, not
retained callable liveness. Exterior metadata survives explicit retirement and
value mutation, so its presence proves neither a live root nor initialized
callable contents. The remaining boundary is authoritative role-aware ownership
against explicit aliases, including the ready/lent/owned-consumed lifecycle;
requiring blanket post-state callable permission would incorrectly reject real
unique loans and one-shot receiver consumption.

The combined frozen control/ownership, retained-context, source-entry,
predicate, runtime-equivariance and repaired-coherence dependency gate passed
(111 jobs). The source-entry results cover ordinary/contextual/host callback
function entry, both suspension-clause forms and their first actual pattern
step. They consume the selected source body and the actual argument, capture
and ordered pattern products. Disposal and proper-tail cleanup remain explicit
scheduled continuations, not assumed lifetime-preserving execution.

The lent-binding contract now retains an actual resident reference guard as
well as the loan record. Real loan formation and input binding produce that
guard; movement, construction and retirement preserve it, and the actual
loan-release admission cannot end the guarded loan. Every effect and control
transition preserves retained original contexts. Arbitrary destructive local
or primitive transitions and relocated external bindings still require their
retained-frame/guard-lifetime proof.

A further general head audit remains open: an implementation generic not
determined by its head can choose arbitrary associated results, and those
results can make its own inferred arguments definitionally equal. Thus
pointwise conversion alone is not the complete coherence contract. The next
repair must establish actual generic determination at the head producer,
without using the ambiguous associated results as inference evidence. The
111-job gate establishes the stated theorems, not global confluence.

The capability/equality mismatch is now repaired at the authoritative
producer. `CapabilityEvidence` and `CapabilityUnfolds` combine greatest
structural recursion with finite logical leaves in the same positive mutual
judgment as entailment, equality and declaration reduction. An interval
establishes a permission lower bound, not an arbitrary principal class.
`Principal.quantity` distinguishes a class's complete interval from an
exact-once request. The semantic `PrincipalOf` selects the greatest actually
supported class in an assumption-free context. `CapabilityModels` proves its
existence, uniqueness, general coinduction, finite equation composition and
extraction from every valid closed Use derivation. Actual alias/associated
expansion transports this evidence; unsupported types retain no answer.

The superseded syntax-only model, its separate greatest-fixed-point selector
and its raw-principal inversion interface have been removed. Runtime
entailment, code/type/world renaming and invocation lease cleanup consume the
new interpretation. Unique references retain unconditional discard evidence;
their precise affine-only classification is not claimed without the missing
constructor-rigidity theorem. The Drop gate still fails at its old
`principalOf_equation` uses: conversion-safe propagation into the actual
resident fields, nominal restrictions and destructor dispatch remains to be
proved. The removed equation interface must not be restored by assuming that
semantic principal evidence already has raw structural form.

Implementation-head inference now records finite origins for every inferred
generic argument. Source templates expose determining positions through
ordered structural children or actual positive source-context reduction;
query conversion retains that origin. Matching also checks the complete
instantiated head, including repeated occurrences. Source declaration
admission requires actual head determination. The mutual judgments now index
their contexts explicitly, so source-head expansion uses the implementation's
own lexical context. Selection, coherent query transport, contextual reduction,
residuals, constructor decomposition and runtime renaming consume this same
inference relation. General missing-origin exclusion now rejects nonparameter
structural leaves and actual unit-erasing aliases, even when erased raw
arguments syntactically contain a generic. The rejection reaches both actual
matching and source declaration admission. The positive structural-origin
theorem constructs source admission, actual matching and selected
implementations from ordinary occurrences, lawful substitutions, whole-head
conversion and real requirements; it does not ask callers for the inferred
answer. General source-reduction instantiation, global confluence and
conversion-safe structural inversion remain open.

The combined frozen capability/head, runtime-equivariance, invocation-cleanup,
predicate-admission, clause-entry and whole-run control/suspension dependency
gate, including canonical recorded-control authority preservation, passed
(122 jobs, warnings as errors, no routine example suite).
The separate Drop capability/dispatch gate failed at the inversion obligation
above; neither full soundness nor the aggregate acceptance gate is claimed.
Higher-ranked introduction also needs an explicit fresh-placeholder and
context-extension audit against normative §13.3: fixed-caller-domain
quantified interpretation alone is not a parametricity or leak-check proof.

The predicate-to-match scope boundary is now closed. The generic interpretation
proves hygienic simultaneous substitution, alpha-freshening and the actual
fixed-context quantifier rules. Its concrete scope interpretation proves the
full mutual entailment/equality judgment preserves admitted lexical scopes.
Function signature admission supplies assumption scope at actual entry; the
existing context product carries it through every binder and world constructor.
The real projection/place consumer uses equality scope preservation, and actual
match selection derives the chosen arm's scoped locals and exact scheduled
binding cursor. Its first execution preserves that cursor or retains pending
destruction explicitly, including bottom-result coercions. No scoped output
certificate or new source-body walker supplies the result.

The same predicate interpretation has a genuine definitional-quotient model.
It proves closed logical equality equivalent to actual definitional conversion
for arbitrary programs, with no confluence premise or constructor-injectivity
assumption. The full interval/capability inversion debt is not thereby solved:
conversion must still be shown to admit the required positive structural join.
Actual generic-origin evidence now has an exact decomposition into positive
source expansion, a whole-query conversion and an ordered structural determining
path. Matching and selection expose that origin for each actual substitution
lookup. Transport of open source reductions through discharged prerequisites,
global confluence and conversion-safe Drop dispatch remain open.

The frozen combined scope-to-match, closed equality/head-origin, host-origin
and exact registration-history integration gate passes (129 jobs, warnings as
errors), together with the existing runtime-equivariance, invocation-cleanup
and whole-control/suspension consumers. The preserved Drop inversion failure
and full aggregate soundness gate are not counted as passing. Activation/home
freshness and active callback-runtime lifetime repairs were still open at that checkpoint.

Historical activation provenance is now part of the canonical control invariant.
Every recorded home, current task context, owning frame role and saved context
is older than the machine's next activation. This includes ended roots and
inactive suspensions: they cannot anticipate future owners. Entry, fresh clauses,
ordinary allocation, raw-memory and foreign mutations, final restoration and
copied replay establish the same bounds through their actual producers. Snapshot
copying derives its selected activation domain from authenticated capture homes
and actual saved control, then advances the real allocation supply.

`ActivationPreservation` proves the complete six-family transition theorem;
`ControlOriginPreservation` consumes it in whole-run, observation, divergence and
reachable-state preservation. `InitialInvocation` no longer carries the weak
one-time guard against a live root at exactly the next activation, or a duplicate
caller-activation bound. Both follow from canonical control admission; arbitrary
empty invocations remain constructible from ordinary historical home bounds.
Actual entry excludes all prior homes from its fresh callee owner, and arbitrary
execution cannot insert a future activation into old saved control or saved
restoration homes. These are historical ownership facts, not an assertion that
every retained caller root remains live or private through arbitrary bodies.
The hidden Drop-handle, initialized return and genuine ambient-stack composition
obligations remain open on the same chain. In particular, removing caller frames
can change a nested foreign call's actual exposed storage and held runtimes;
standalone observations are not automatically observations in an ambient stack.

The frozen combined activation/control, callback-runtime and registry-origin
gate passes (143 jobs, warnings as errors), including source/match entry,
runtime world/coverage/body renaming and invocation cleanup consumers. Existing
example files were mechanically migrated but not executed as routine evidence.
The known Drop inversion failure and full aggregate soundness remain open.

The lower `PrivateStorage` producer now owns exact vacant internal-slot framing
through actual allocation, writes, copies, moves, loans and common input binding.
`DropHandle` consumes it, rather than owning a second copy of those generic
proofs. Its actual two-step entry product also retains the source destruction
task, body stack and fresh callee activation, including the real unsafe-context
reset on the activation frame. `DropSuspension` carries the newly allocated
loan's freshness through historical saved authority and actual cancellation.

`PrivateLocalControl`, `PrivateEffectPreservation`, `PrivateBranchPreservation`
and `PrivateForeignPreservation` derive executable operand and cleanup-owner
exclusion through the real producers. Pattern tests construct their actual
binding carriers; active suspension restoration cannot select a private root;
foreign mutation follows actual exposure, callback inputs and retained lease
cleanup. The guard itself may retain the private handle, but it is not a host
exposure seed. No future-frame or post-world privacy premise is assumed.

`PrivatePreservation` covers every branch of the complete six-family `Step`
relation. Its general finite-run theorem either retains the protected stack
prefix and exact slot or factors the run at the actual first silent guard pop,
with the private slot intact on both sides. It places no slot-preservation
obligation on the caller's later suffix. `DropPrivate` derives the initial
invariant from actual hook dispatch and ordinary owned-input entry and feeds
that complete-machine theorem. This closes the conditional caller-handle
preservation argument, including nested callbacks and cancellation, rather
than just checking isolated transitions or examples.

The ambient run's no-label-transfer/no-operation-dispatch/no-replay restrictions
are still explicit inputs to that result. The current `DropContract` quantifies
isolated initial invocations; erasing real caller frames changes host exposure
and cannot justify those inputs. Correct ambient invocation admission, initialized
normal-return integration and dependent conversion-safe Drop inversion remain
open. This checkpoint does not claim a complete destructor or language proof.
The frozen combined caller-private, suspension, exterior-home and callback-runtime
gate passes 129 jobs with warnings as errors. Existing examples and the known
failing higher Drop aggregate were not run.

The structural capability substitution boundary now consumes kinded declaration
dependencies. Actual declaration admission previously omitted function captures
and data quantity sources; it now checks captures under the full signature
context and quantity sources under the data's real generics and requirements.
Quantity sources retain both permitted forms: a quantity term or a type whose
structural capability supplies the marker. The existing equation is unchanged.
`DeclarationDependencyKinding` derives the exact instantiated dependency kinds;
`InstantiationComposition` composes the real ordered generic table and captured
field substitution. `CapabilitySubstitution` handles every equation constructor
and arbitrary recursive, noninjective type substitution through the shared
coinductive image construction. Finite logical leaves remain the responsibility
of the open mutual cut, not a supplied structural-capability conclusion.

The logical equality boundary now preserves full source `Kinding` under kinded
assumptions, including every actual nested quantified rule. Its interpretation
uses the same generic quotient node/rebuild producer as closed definitional
equality; the earlier closed-equality theorem retains its unchanged contract.
`LogicalSubstitution` consumes this result to derive converted substitution
admissibility, including occurrence kinds, binder masks and ordered default
prefixes. The actual instantiated-requirement converter no longer asks for the
prospective target table's admissibility as an independent premise.

The frozen declaration/kinding/capability batch passes its combined 149-job
dependency gate, including actual source and match entry, whole-machine control,
callback lifetime and runtime-renaming consumers; the logical substitution
consumer passes its 29-job gate. These are strict general proofs, not examples
or a completed logical/source-reduction cut. Confluence, conversion-safe Drop
inversion and full-language soundness remain unproved.

The actual declaration default boundary now uses one ordered lexical producer,
`BinderDefaultsWellFormed`, for signatures, data, aliases, traits, associated
items, implementations, effects and constants. Associated defaults retain their
outer owner scope; a binder default sees only its preceding item prefix.
`Instantiates.default_step` consumes the source admission and current prefix
substitution to establish the actual chosen default's kind. Constructor constant
typing also checks its real generic arguments, closing the other missing source
term-kinding premise. `DeclarationKinding` derives kind and universe bounds for
every term in the authoritative declaration inventory, including defaults,
captures, quantity markers, requirements and invocation contracts.

`StaticAtomTransport` now transports all sixteen mutual static judgments through
one concrete atom bijection that fixes the actual program. Runtime-region
equivariance is its universe-preserving instance; the superseded runtime-only
mutual proof and separate kind/capability/callable transport proofs are removed.
Actual runtime signatures, code, typing, world, coverage and body consumers keep
their original interfaces through that shared producer.

`LogicalPredicateInterpretation` establishes admitted interpretation iff actual
`Entails`, including nested quantifiers. `PredicateComposition` carries the real
mapped generic table into the instantiated-requirement judgment. `LogicalCut`
proves assumption replacement across the complete mutual judgment family at
identical kinding domains, with derived projections for equality, capability,
rows, type lifetimes and instantiated requirements. It does not silently assume
that universal evidence tolerates a larger argument domain.

That larger-universe obligation is discharged separately by `LogicalUniverse`.
A concrete finite-support bijection fixes all declaration, assumption and goal
atoms while absorbing the new universe level into the old level's infinite atom
domain. The shared static transport and actual assumption cut then establish
`Entails.raiseUniverse` for arbitrary larger universes under kinded assumptions
and a kinded goal. Universal introduction still covers every newly admitted
value; no quantifier rule, semantic domain or source meaning is weakened.
At that checkpoint, the general parameter cut, source-reduction confluence and
dependent conversion-safe Drop inversion remained open. These results do not establish full
language soundness or close the ambient caller-storage obligations above.
The frozen combined gate passes 163 targets with warnings as errors, including
the actual head-inference/coherence admission consumers, source and match entry,
whole-machine control, exterior cleanup separation, callback runtime lifetime
and runtime world/coverage/body transport. Existing examples were not run.

`AtomInstantiation` now supplies a single globally kind-preserving atom map,
including proof-only nodes, and `CapabilityAtomTransport` transports the actual
recursive capability equation through noninjective maps. The ordinary parameter
substitution consumer derives a total proof-node extension that agrees exactly
with `Term.substitute` on its admitted terms; its superseded equation walker is
removed. `UniverseEmbedding` also consumes the shared fixed-atom theorem.

`FreshAtomTransport` carries all sixteen actual static judgments into the
existing hygienic predicate interpretation. `FreshInstantiation` derives the
canonical fresh rigid generic table and proves that specializing it recovers
the caller's exact table. `Entails.specialize_fresh_instance` then derives
actual `EntailsSubstitution` from one fresh-universe inspection proof and caller
evidence for the source requirements. Duplicate and compound arguments and
nested universal requirements are covered by the general proof; no syntactic
constraint replacement or postulated semantic transport is used.

This closes specialization of a genuinely fresh inspection proof. The bridge
from arbitrary parameter-context derivations was still open at that checkpoint:
caller-only parameters, scoped regions and scoped brands in universally chosen
arguments require distinct caller/current valuations and actual source preimages.
Source-reduction confluence,
conversion-safe Drop inversion, ambient caller-slot privacy and full-language
soundness are still open.
The frozen fresh-specialization batch passes its strict 166-job combined gate,
including actual head-inference and coherence admission, source match entry,
whole-machine control, exterior storage separation and runtime transport.
Existing example targets and the unresolved Drop aggregate were not run.

`LogicalParameterCut` now closes that general hygienic parameter cut.
`Entails.substitute` and `Entails.substitutes` derive actual target entailment
and its authoritative substitution graph from the original source derivation,
admitted source predicate and assumptions, caller-kinded replacements, forward
universe/scope inclusions and actual caller evidence for the source requirements.
Substitutions may be noninjective and compound; nested universal requirements
do not require backward inclusion of caller binders, regions or brands.

`FreshArgumentPreimage` and `FreshSubstitutionModel` construct the previously
missing caller-only atom preimages. Kinding and term interpretation generalize
their existing atom-map producers; old interfaces are wrappers, not duplicated
structural proofs. `CurrentAtomInterpretation` keeps source-current and fixed
caller valuations distinct. `AtomOpening` derives the actual raw-table treatment
of absent declaration keys. `GeneralAtomTransport` consumes these in all sixteen
mutual judgments, and the former fresh-only case proof is removed in favor of
the shared theorem. The original `LogicalSubstitution` graph-congruence module
is preserved as an upstream dependency, not overwritten by the new cut.

`LogicalInstantiation` consumes the result for actual opened predicates and
equality: nested generic value-table substitution composes through the existing
hygienic relation, and opening an admitted source equality into an assumption-free
caller yields genuine `DefinitionallyEqual` after its real requirements are
discharged. This does not establish positive source-reduction preservation,
global confluence or conversion-safe Drop inversion; those remain the next
dependent obligations, alongside ambient invocation and complete return cleanup.
The source-only combined gate passes 186 jobs with warnings as errors, including
existing fresh specialization, source/head admission, runtime transport and the
actual whole-machine caller-private consumer. No example or failing aggregate
target was used as evidence.

`PositiveSubstitution` now proves preservation of actual positive source
reduction under arbitrary lawful caller substitution. Internal unkinded proof
nodes use the existing guarded atom map; kinding of both endpoints recovers the
language's actual simultaneous substitution. Selected implementation and
projection requirements consume the proved logical parameter cut. This does
not replace positive reduction by logical or assumed equality.
`DefinitionalSubstitution` carries genuine conversion into assumption-bearing
callers using that positive theorem. `HeadOriginSubstitution` consumes it to
instantiate the actual determining origins in source implementation admission.
`MatchesImplHead.of_admitted_instantiation` and `SelectsImpl.of_admitted_head`
construct real matching and selection, including heads determined through
source alias/projection expansions. A second caller-supplied origin certificate
is no longer needed for this construction; actual argument kinding and source
requirements remain necessary.

`HeadOriginInstantiation` retains each source expansion, its positive caller
instance, the whole-query conversion and its structural determining path.
`RootReductionJoining` resolves alias, default and override root pairs through
one relation-parametric proof. Its remaining override case requires positive
joining of the actual selected generic tables, not merely the convertibility
witness in declaration coherence. The combined fresh source-only dependency
gate checks these consumers with warnings as errors and implicit identifiers
disabled. The global strip/parallel-moves theorem is still open: root/child
residuals and generic-origin subderivations must provide a well-founded proof
of common positive reducts. No global confluence, constructor separation,
conversion-safe Drop inversion or full-language soundness is claimed here.

`HeadInspection` derives a finite source-inspection certificate from the actual
admitted determining origins. A whole implementation's canonical minimum
inspection level induces a well-founded strict dependency order; it is not a
normalization measure or a size assigned to arbitrary equality proofs.
`HeadInspectionInstantiation` retains paired genuine source/caller positive
expansions at that same minimum. The actual admitted-head construction consumes
them. Root-step substitution uses the single mutual selection/predicate
transport, and ordinary reduction/conversion delegate to that producer.
The frozen source-only 69-job gate checks this integrated source/caller endpoint.

`InspectionResiduals` now carries independent source-inspection bounds through
actual root/child squares: the residual root retains the original root bound,
while the body residual retains the child bound. Row/root residuals preserve
the original bound as well. `Term.substitutions_related` is the common
constructor-congruence producer for these residuals, positive substitution,
conversion and row equivalence; the three superseded walks were removed.
The frozen 68-job dependency closure verifies the migrated consumers. Full
positive strip/parallel moves and conversion-to-joining remain open, including
control of arbitrary query-equality premises. These inspection levels alone
are not a proof of global confluence or constructor separation.

`InspectionPaths` extracts fixed ordered determining paths from those actual
minimum source exposures. Reading a fixed path identifies the raw generic table
of a path-ready ordinary selection; the proof does not infer raw identity from
definitional conversion. `PathInspectedStep.root_equal` consumes those identities
for real root expansions. `InspectionPathResiduals` updates the raw values when
queries change, transports their requirements and constructs the real replacement
selection and substituted body. Child and row residuals consume that producer.
The common `RowEquivalent.root_relation_residuals` now handles ordinary,
inspection-ranked and path-ready roots, removing the duplicate row induction.

This is a proof-only subrelation of existing execution of static reductions,
not a replacement source semantics. The strict 70-job dependency gate checks
the residual batch. The decisive remaining obligation is ordinary admitted
reduction/conversion simulation through these fixed source paths, including
positive exposure of query constructors and control of whole-query conversion
premises. Raw path-ready root identity alone does not establish ordinary
confluence, constructor separation or conversion-safe capability inversion.

`InvocationBoundary` now gives the actual caller-delimited invocation interval.
Its steps are guarded instances of the one `Execution.Step`, retaining the
complete ambient stack, callback sessions and host exposure. Non-tail entry
records the actual caller continuation; proper-tail entry takes its real outer
continuation from `TailFrames`. Normal return is the saved context and ambient
suffix before the caller consumes its result. Any yield at that suffix stops
the interval; a wrong return context cannot pass progress admission. Internal
operation and label classification use the existing `Routes` and `LabelRoute`
producers, including their barriers, rather than a second delimiter matcher.
Every actual run factors at its first interval exit, even if later execution
re-enters a similar stack. Isolated execution is the same relation's specialization.

`InvocationStart` admits the actual entry recipe, ordered original inputs,
current control/authority invariants, callback runtime liveness, live caller
region and unsafe-call permission. `InvocationInputs` proves that the actual
receiver/capture preparation retains the same formal, origin and access
coordinates. Ordinary arguments are owned inputs. The shared capture projection
produces both original and prepared coordinates, with lending changing authority
rather than reconstructing capture identity. `Observes`, `Diverges`, resource
admission and their real preservation consumers now use the common interval.
Internal suspension and cancellation remain trace events, not invocation exits.
`LifecycleObserves` separately correlates the SAME outward request and actual
caller-side capture with its suspended continuation or later cancellation
initiation. Request events and caller/lifecycle events have separate attribution;
their composition is proved to be the original whole-machine run. The derived
interface and its exact characterization consume both observation forms.
`InvocationLifecyclePreservation` proves the same saved continuation origin
survives intervening caller execution and copied replays; cancellation requires
that original quantity to be optional. World typing and Drop's exclusion of
escaped lifecycles are derived through the real execution/prefix witnesses.
Cancellation initiation is not completion of arbitrary destructor cleanup.
The old table-entry and internal-prefix-event exit classifications are removed.
Outward label progress retains its actual destination and nonvacuous payload
preparation. `LabelBoundary` replaces the prior existential complete-step
admission with the callee's post-payload cleanup permission. The caller supplies
its own share for the SAME actual `LabelRoute` and protected payload. Exact
root-membership composition proves the caller share equivalent to the complete
leave rule's cancellation permission, under callee admission. `MayTransfer.execute`
constructs that ordinary `ControlStep.leave`, rather than assuming it; it also
derives the post-world's typing. A missing or foreign-blocked target is not
admitted, and the isolated outward-label case is proved impossible.

`RootSelection` constructs reverse-creation, duplicate-free selections from
the actual finite root table. Scope, activation, delimited handler and abandoned
label-frame selection are definitionally identical specializations of the
common `RootsWhere` contract. The label execution proof consumes this general
existence theorem for actual callee/caller cleanup composition; no extra root
inventory or preselected complete cleanup list is assumed.
The strict 147-job dependency gate verifies this label/root-selection migration,
including ordinary control preservation, the public-safety consumer's derived
isolated impossibility, private Drop intervals and escaped lifecycle proofs.

`OperationBoundary` replaces the former pre-payload suspension-only check.
`MayAwait` now retains the actual selected operation's terminal or resumptive
disposition and a nonvacuous ordered `Protects` preparation. Its actual fresh
clause home can be retargeted without changing the protected addresses or output
world. Admission requires the callee frame prefix to be foreign-barrier-free,
and checks its actual `AbandonedRoots` after protecting the payload, excluding
the same kept roots as real effect execution. The shared disposition permission
is `Cancelable` for terminal operations and the actual quantity-indexed
`SuspendPermission` for resumptive ones. Real effect rules consume this product.

The actual `Routes` producer locates an outward delimiter in the ambient suffix.
The admitted callee share and caller `DelimitedRoots` share compose to exactly
the full handler permission, including replayable frames; with callee admission,
caller permission is equivalent to full-handler permission. Isolated invocations
use this same frame-owned boundary with an empty ambient suffix. Neither absent
routing nor impossible payload preparation makes the predicate vacuously true.
`PublicValues` retains the complete admission when observing outward payloads.
`OperationExecution` consumes the split to construct all three actual handler
transitions: terminal dispatch, tail-arm capture and bound-resumption capture.
The real fresh clause context, ordered full cleanup/capture roots, saved-home
table and quantitative bound are constructed from the same preparation and
admitted disposition. Both capture branches produce the same outward request's
`LifecycleObserves` witness, and actual preservation supplies their post-world
typing. Real clause-pattern planning and continuation-storage creation remain
explicit dependent producer inputs; they are not complete transition premises.
The strict 138-job handler/private/lifecycle dependency gate checks these
constructed transitions and their actual public-observation consumers.
Source dispatch now consumes `Typing.OperationArmMode`, the exact existing
`OperationArmsType.cons` contract exposed by its common selected-arm projection.
`MayAwait.source_execution` derives the terminal/tail/bound branch, declaration
quantity, implicit one-use condition and explicit generative brand from that
source derivation. It constructs the real effect step, preserves world typing
and proves the actual clause's typed ordered binder cursor, retaining terminal
cleanup as pending rather than claiming the body is already running. The
terminal clause consumer no longer performs a second induction over arm typing;
it projects that same contract. Snapshot code-typing transport checks against
the shared source premise as well.
The strict 155-job dependency gate covers source-driven construction, actual
clause entry, elaboration, snapshot body transport, lifecycle preservation and
private-hook preservation; no concrete example is used as proof evidence.
`Installs.handler_context` now produces one `InstalledHandlerTyped` context
for both completion and operation clauses, retaining the actual declared
handler result and its scope. All actual clause-entry consumers use this
product; the separate installation projections and unrelated existential
result types are removed. Terminal/completion entry now proves precisely the
selected handler's declared result, not merely some result type.

`OperationSignatures` closes the source/runtime signature boundary from actual
`SelectsOperation` and the two real generic instantiations. Argument equality
transports the raw substitution tables to all parameter, result and effect
components. Scope closing commutes with this same substitution. Fresh source
continuation brands preserve those earlier signature components at actual
clause entry. `ContinuationBindingType` therefore retains the source binder's
literal continuation shape and exact runtime brand, handler answer and quantity,
while requiring real conversion for its argument/effect components. The former
syntactic-equality restriction in `CreatesContinuation` is removed; its real
world-typing consumer retains the exact structural shape.

`ContinuationCreation` derives this type contract and constructs initialization
from actual successful allocation. `MayAwait.source_execution` consumes it;
the source-facing callback no longer supplies a completed continuation creation
or an initialized post-world. The existing vacant-write and empty-input value
proofs moved unchanged from scalar progress into `StorageConstruction`; scalar
results and continuation handles use that same construction. Actual allocation
supplies its original declared address type and vacancy through the common
allocation producer. Physical extent/layout success, its failure behavior, and
post-handoff pattern access remain separate open obligations. The construction
does not infer allocation success from a finite world's typing.
The strict 174-job dependency gate verifies this construction through actual
handler execution, scalar storage progress, elaboration, snapshot body typing,
whole-execution preservation, lifecycle/control-origin and private-hook
consumers. The unrelated higher Drop conversion-inversion gate remains open.
This strengthens semantic admission; it does not prove source resource progress.
General ordered layout/allocation and loan readiness must still produce the
payload preparation and residual permissions. Ordered matching/pattern access,
clause binding progress and continuation allocation/failure remain obligations
of complete handler progress.

`DropInvocation` derives this admission from actual `destroyHook` dispatch,
including the freshly allocated and borrowed argument handle and unchanged
caller stack. `DropObservation` applies the selected Drop contract directly to
these ambient prefixes. The former blanket ban on all performance events is
removed: a pending operation must have its real accepting delimiter inside the
invocation. `PrivateEffectPreservation` now carries internally handled terminal
operations through their real routing, payload and abandoned-frame cleanup.
`PrivatePreservation` covers all six transition families and excludes a hook
pop by the invocation's current handoff guard, not an after-state certificate.

`DropPrivate.hook_body_admitted_private` connects actual dispatch and ordinary
entry to preservation throughout every admitted interval. Its trace restrictions
are derived from the selected Drop admission, not supplied as an independent
ambient-run hypothesis. `hook_body_private_until_return` then factors an arbitrary
actual body run before its first normal caller handoff, preserving the private
slot and guard at that boundary while retaining an unrestricted original caller
suffix. The earlier no-performance whole-run restriction and its superseded
private-run induction have been removed.

The fresh source-only combined dependency gate passes 189 jobs with warnings
as errors, including the interval/private-hook theorem, operation-boundary
composition, actual lifecycle origin, preservation/public-observation consumers
and the current source-inspection/residual proofs. This does not check the
known failing higher Drop inversion dependency or the aggregate examples.

This does not establish full invocation progress or full Drop conformance.
Resource progress and initialized normal-return lifetimes still need their
compositional control/ownership proof. Resident/contextual lending readiness and
erased resource-input custody still require positive initial origin obligations;
the raw resource producer repair must supply those, not assume entry success.
The event-only Drop field-move condition remains overbroad and incomplete: actual
silent input/aggregate handoffs and host transactions need their authoritative
storage-effect product before the normative proper-field rule is established.
The higher Drop cleanup consumer remains behind the recorded conversion-safe
capability-inversion failure; its entire gate is not certified by the successful
lower invocation/private proof closure. No example or aggregate soundness claim
is used to bridge these remaining obligations.

The ordinary conversion boundary is now closed by `DefinitionalChurchRosser`.
`FullHeadInspection` extracts one finite certificate from the actual static
derivation, retaining each projection's real head-query conversions alongside
its strictly earlier full source inspection. `HeadInspection` now minimizes
only that full certificate; legacy weak evidence is its same-level erasure,
not a second source matcher or independent minimum. `FullInspectionSubstitution`
replays the exact chosen source path in the actual caller at that same level.
Projection-domain transport and related generic tables share their existing
producers with ordinary reduction and selection.

`InspectionParallel` proves the finite complete-development triangle and diamond,
including all structural row equations. It recurses only over proper source
children, not over freshly expanded recursive declaration bodies. Canonical
confluence then joins the finite family of actual source-path exposures in
`InspectionCompletion`, which reconstructs real selection at their common query.
The full certificate's own induction handles query conversions; a separate
strict induction on the one full source minimum handles caller replay.
Consequently `DefinitionallyEqual.joinable` and `DefinitionalReduction.confluence`
produce common reducts in the original positive language relation from only
program well-formedness and kinded actual context assumptions. Neither global
termination nor a desired simulation or injectivity conclusion is assumed.

`DefinitionalSeparation` consumes this result for structural constructor/child
decomposition, nominal identity, scalar discrimination, row-equivalent normal
forms and positive agreement of selected generic tables. The actual definitional
quotient and assumption-free logical scalar equality use these conclusions.
Arbitrary lexical equality assumptions are not declared scalar-consistent.
Conversion-safe capability inversion, layout/ABI consumers and full resource
progress remain unfinished; the higher Drop gate is not certified by this
conversion theorem or its successful lower consumers.
The fresh source-only integration gate passes 223 jobs with warnings as errors,
covering ordinary conversion and residuals, source handler construction,
scalar storage progress, elaboration, runtime body typing, whole-execution
preservation, invocation lifecycle and private-hook preservation. Neither
examples nor the known failing higher Drop dependency are counted as passing.

Finish total primitive behavior, representation/ABI site coverage and target
obligations. Audit every requirement against authoritative evidence, preserving
negative regressions and distinguishing conditional theorems from established
existence. No unproved, circular, vacuous or missing requirement counts as done.
