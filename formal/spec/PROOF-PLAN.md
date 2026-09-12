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
completion for the actual execution relation. The current `ResourceAdmission`
quantifies over runs and requires typed post-states and progress. Projecting
those requirements out of an admission assumption is not the missing soundness
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

## 3. Remaining boundary completeness and final audit

Finish total primitive behavior, representation/ABI site coverage and target
obligations. Audit every requirement against authoritative evidence, preserving
negative regressions and distinguishing conditional theorems from established
existence. No unproved, circular, vacuous or missing requirement counts as done.
