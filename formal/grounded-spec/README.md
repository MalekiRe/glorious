# Grounded language specification

This directory starts a new Lean specification of the language semantics and
future compiler correctness contract. It is not a compiler implementation.
The goal is a smaller, inspectable development built entirely from ground truth,
with one connected body of definitions and proofs—not a collection of proof
islands awaiting integration.

## Shared and unique reference boundary

This development extends the same source producer, Core evaluator and
general correctness theorem; it does not introduce a separate reference model.

- `Context.names` selects stable binder identities in authoritative
  `Context.storage`. Hidden caller storage survives calls, and resume uses the
  actual callee post-storage rather than stale caller initialization masks.
- `AccessType`, mode-indexed loans and ancestry-aware `Permits` distinguish
  positive authority from conflicting access. Unique referent authority does not
  require a mutable handle binding. Shared/shared overlap and statically disjoint
  unique fields remain legal; parent use is suspended only by conflicting children.
- `moveIndirect` and `assignIndirect` operate on canonical projected targets.
  Assignment evaluates its RHS first, destroys the exact old resident using its
  authoritative initialization mask, and reconstructs global storage correspondence.
  Masked resolution permits restoration without presupposing a restored target.
- Reads, borrows, reborrows and handle transfers require whole-target readiness.
  Every ordinary own-ending, sequence disposal, carrier overwrite and scope or
  parameter cleanup consumes pre-ending restored-target evidence. Pending argument
  and result readiness lives in `StateTyped.heldReady`; vacant moves require
  pre-state separation from their targets, while complete writes preserve it.
- Unique ancestor modes are derived from `Context.Derived.unique`, not an
  admission assumption. `correctness_canonicalTargets` preserves authoritative
  paths and masks. `correctness_noDangling` covers addressable typed targets of
  both modes and additionally proves readable shared targets.
- `Environment.Evolution` frames outside incoming owner/live-unique roots and
  proves fresh scoped-root retirement; it does not confer access permission.
  Reference-free conservation still specializes the sole Core evaluator.

Arbitrary aliasing shared input worlds remain supported. Live external unique
`.input` origins remain excluded; actual source-derived unique call arguments
retain canonical binder origins. Inactive unique-input history is inert. This is
not complete externally supplied unique-input semantics, nor coverage of
nonlocal transfer, effects, generic parameters or compiler realization.

## Governing discipline

**Build from established meaning upward. Do not work backward from a desired
soundness theorem by introducing assumptions that promise its prerequisites.**

The normative [language specification](../../glorious-language-specification.md)
is the source of intended language meaning. Relevant normative library and
machine-interface contracts govern their respective boundaries. Follow the
[compiler architecture contract](../../docs/compiler-architecture.md) without
mistaking implementation organization for language semantics.

Existing Lean code is reference material, not ground truth. A checked proof
establishes its stated proposition under its premises; it does not establish
that its definitions faithfully describe the language, that its premises are
inhabited, or that source programs produce them.

### One connected body, no speculative prerequisites

1. Start with the smallest faithful semantic foundation needed for the current
   construction. Each definition must have a present semantic purpose grounded
   in a normative rule or an explicit execution mechanism.
2. Extend that foundation using only established definitions and checked results.
   Connect each extension to the existing body and prove its applicable
   guarantees before building further on it.
3. Do not introduce temporary prerequisite lemmas, speculative interfaces, unused
   fact tables, or standalone theorems for anticipated future integration.
   Intermediate reasoning belongs inside the proof that needs it. Extract a
   shared lemma only when actual consumers require it, and migrate those
   consumers in the same change.
4. Do not create a second semantic path to avoid repairing the first. Each fact
   has one authoritative producer; consumers use that producer's evidence.
5. A checkpoint must strengthen the connected semantic result. New files, helper
   counts, successful builds, and promises of later composition are not progress
   criteria by themselves.

The foundation is necessary semantic definition, not permission to accumulate a
framework for future proofs. Keep it minimal and extend it through real use.

### Grounded premises, not assumed conclusions

Every premise must have an explicit source: a normative language requirement,
an established invariant produced by the current development, or a genuinely
external machine/foreign assumption whose meaning and scope are documented.

- Derive execution readiness from source admission and established state facts.
  Do not define admission to assume progress, preservation, successful execution,
  valid future states, or eventual resource completion.
- A property may be defined as a proof target. It must not then be supplied as
  admission evidence in place of proving that target.
- Moving an unresolved obligation into a structure, certificate, callback, or
  host contract does not discharge it.
- External assumptions must describe the actual external boundary, not conceal
  obligations belonging to the language semantics.
- Missing evidence is unknown, not absence, permission, or allocation exhaustion.
- No `sorry`, `admit`, or new axioms used to bypass semantic obligations. Identify
  logical axiom dependencies and audit the connected theorem's premises.

### Preserve meaning while simplifying

Optimize for fewer independent concepts, fewer separately supplied premises,
and fewer reconstructions of the same fact—not merely fewer lines.

Preserve distinctions required by the language: source equality versus physical
storage identity; ownership versus borrowed permission; permission versus
custody; captures versus their common invocation coordinates; normal return,
transfer, cancellation, divergence, and failure. Preserve evaluation order,
guards, provenance, and lifetimes through actual transitions.

Allocation must not be assumed successful. Exhaustion must concern the actual
admitted request and preserve any already executed preparation prefix. Logical
type conversion must not be silently treated as physical tag identity.

### Simpler semantics first: complete subsets end to end

Start with the simplest faithful subset and complete its semantic proof end to
end before extending it. This supersedes the older hardest-first construction
order for this directory. The full language remains the goal.

State the supported syntax, admission rules, execution relation, and both ends
of the correctness theorem precisely. Exclude unsupported constructs explicitly;
never give them placeholder behavior. Prove admission is nonvacuous and prove
all applicable typing, progress, result, resource and lifetime guarantees for
every admitted program. Progress alone does not imply termination.

Grow the same definitions and general result. Each extension must preserve the
meaning and guarantees of previously supported programs, with agreement proved
when representations change. Do not build disposable toy languages or parallel
fragments for later unification. Completed subset soundness is a legitimate
milestone, not whole-language completion or compiler correctness.

An AST-to-value theorem does not prove parsing, physical allocation behavior,
or implementation correctness. Those boundaries must later be established,
not silently inferred from a logical evaluation theorem.

## Reusing existing work

[`../spec/`](../spec/) contains prior semantics, proofs, audit findings, and
counterexamples to attempted designs. [`../lean/`](../lean/) is the older
compiler draft, not this development's foundation.

Read and reuse what is justified; do not copy either tree wholesale. Before
bringing code into this directory:

- identify the normative meaning and immediate consumer;
- inspect all premises and transitive dependencies;
- adapt the smallest coherent piece and check it in the new connected chain;
- record provenance in a concise source comment when code is adapted;
- retain discovered semantic constraints even when replacing their old encoding.

Do not import the old proof graph merely to hide dependencies or make a check
pass. Any direct dependency must be deliberate, audited, and necessary for the
current construction. Preserve old trees as reference material; do not delete
unrelated or unfinished work. Within the new development, remove superseded
paths as consumers migrate rather than retaining compatibility layers.

## Acceptance and verification

For each change, answer:

1. Which normative rule or explicit mechanism gives this construction meaning?
2. Which already established facts does it use?
3. Which part of the connected result now becomes stronger?
4. Where are its conclusions consumed now—not in a promised future stage?
5. Which premises, duplicated reasoning, or obsolete paths does it eliminate?
6. What remains outside the proved boundary?

Check the actual Lean definitions and general proofs, including affected
consumers. Audit assumptions and nonvacuity; compilation alone is insufficient.
Do not routinely add or run concrete examples or unit tests. Use an example only
to isolate a suspected modeling error when a general argument is insufficient.
Commit and push meaningful verified changes, preserving unrelated repository
work. Development proceeds serially unless the user changes that direction.

Maintain a concise current account here of the established boundary and its next
grounded extension. Do not turn this README into a checkpoint diary or duplicate
status across competing ledgers. Whole-language completion requires all intended
cases, general preservation/progress and resource/lifetime guarantees, and an
explicit semantic-fidelity and proof-assumption audit.

## Current boundary

**Completed subset: unit, selected fixed/target-width nonnegative integer and
decoded character literals, grouping, place reads, sequencing, immutable and
mutable initialized bindings, whole-local and nested tuple/structure moves, restoration and assignment,
optional type annotations, tuples/projection, fixed-array construction, non-generic transparent aliases, structural constants,
non-generic finite-inline nominal data with coherent principal restrictions, direct
nonrecursive first-order calls, immediate structural pattern-callable
application with conservative affine conditional initialization joins, and the
first-class shared/unique-reference subset described below.** Records,
tuple structs and enum variants retain declaration
identity; projection and deconstruction check field visibility. The boundary
is decoded declarations/expressions to logical values and stable-root storage post-states. Normative basis:
§§2.2–2.3, 3.2–3.4, 4.1–4.4, 5.1–5.3, 6.1–6.3, 7.2–7.7, 9.1–9.2 and 13.1. No
previous proof modules are imported. The objective is the full
specification, not a feature percentage.

`Grounded.correctness` proves finite evaluation, result typing, lexical-state
preservation, active-loan/custody preservation, protected-result usability,
stable-root storage evolution and uniqueness for a fixed admitted Core. Every
constituent consumes its predecessor’s actual post-state.
Initializers execute before their binding receives a fresh root; their result
and post-store construct the body environment. Scope exit retires its own root
prefix and retains changes to surrounding locals. Copying requires duplicability;
zero-use sites require the distinct affine-bound permission `MayDiscard`.
`closed_correctness` derives empty visible bindings and no occupied store cells
from actual evolution starting at `Environment.empty`. It preserves the advanced
identity supply rather than falsely equating the final environment to the initial
empty environment. Admission supplies no successful execution, normalization or
allocation-success witness. Exact scalar admission theorems and `unit_agreement`
remain connected to this general result. This is logical storage preservation,
not physical-machine preservation.



Tuple arity is preserved: unit is the empty tuple; grouping and a singleton
tuple are distinct. Constituent evaluation and positional value typing are
proved inside the connected theorem, not left as separate prerequisites.
Projection derives its actual resident and typing from the evaluated tuple;
an in-range runtime selection is not separately assumed. Out-of-range tuple
projections cannot be admitted. Physical evaluation traces remain outside this
logical big-step boundary.

`Place` selects the nearest lexical root and a source field path.
`Environment.resolvePlace` produces one `Address` consisting of that stable
`Root` and canonical `List Nat` field indices. The existing
`Value.fieldIndex` remains the runtime field producer; no second nominal-layout
lookup algorithm or fact table is introduced. Resolution requires an actual
allocated root cell and a present child at each step, permits a vacant selected
slot, and cannot descend through a vacancy. The nearest vacant binding still
shadows older names. Addresses are logical coordinates, not physical byte addresses.

`ProjectionType` checks tuple bounds and nominal-field visibility; `PathType`
composes its canonical indices. `EnvironmentTyped.resolvePlace` derives runtime
resolution and the selected resident from those source facts and current resident
typing. `resolution_fidelity` proves the runtime indices equal the `PathType`
indices; that equality is consumed by typed writing, never supplied as a premise.

Actual stored reads, moves and assignments carry the resolved address explicitly.
`Environment.at` returns raw selected storage, including vacancy, for assignment
disposal; `readAddress` additionally requires the entire selected subtree to be
initialized for owned access. `writeAddress` and `takeAddress` operate only on
canonical indices. No lexical name or `FieldKey` is re-resolved during access.
Assignment evaluates the RHS first, resolves in that actual post-state once,
and shares the address between old-resident disposal and replacement. Source
admission still requires a mutable root and legal old-resident disposal; a vacant
selected subtree is restored without destroying an old value. Nested writes need
present ancestors, not complete siblings or an initialized destination.
`PathType.write` and `EnvironmentTyped.writeAddress` preserve the computed partial
state and derive readback from the actual canonical update. The old stored-place
`readPlace/writePlace/takePlace` operations, lexical `Environment.replace`,
and source-key `Value.readPath/writePath` walkers are removed. Owned temporary
projection retains only its necessary single-field `readField/takeField`
operations and the existing residual `StorageDisposition`/result-protection contract.

Typing now produces the final initialization context, rather than requiring
every expression to preserve its input context. Runtime slots contain either
a resident or a vacancy; a vacant nearest binding still shadows outer bindings.
Whole-root and nested `move` extract the actual selected resident and clear
that path, even for a duplicable value. The correctness induction constructs
`takeAddress` from canonical resolution, the initialized resident and typed
canonical clearing. `takeAddress_invalidates` proves that address unreadable afterward. Reads and
moves require the selected subtree to be complete; later arguments and bodies
consume the preceding initialization context. Assignment restores a vacant
subtree of a mutable root after evaluating its RHS. Function
parameters and pattern binders start initialized; scope exit removes only its
own prefix and preserves changes to outer slots. Vacancies reside directly
in the resident tree. The authoritative store distinguishes a still-live moved-out
cell (`some .vacant`) from a retired or nonexistent cell (`none`); absence never
projects to a fabricated vacancy. `ValueHasType.initialized` proves that every typed owned
result contains no vacancy at any depth. Reads check the selected subtree, and
extraction uses the same canonical write as restoration, replacing the selected
resident with a vacancy rather than retaining its payload elsewhere.
`Evaluates.move_invalidates` proves that every actual move makes a subsequent
read of that exact address fail, including nested paths in already partial trees,
and proves that the source spelling still resolves to the same address.
Its proof needs neither source admission nor an assumed post-state invariant.
The shared operational readback theorem also supplies typed write preservation;
the superseded typed-only child-readback proof is removed.
`Evaluates.move_restore` proves the exact operational round trip: immediately
writing the extracted resident back to the same canonical address recovers the entire original
environment, including siblings, pre-existing holes and shadowed bindings.
This is not merely equality of the selected field or preservation of its type.
It does not grant source-level write permission to an immutable place.
Whole-root and nested writes now share one path-update implementation.
The static initialization context now stores finite field overrides rather than
a whole-root Boolean. `ResidentTyped` is the authoritative storage typing
relation; owned-value typing is its fully initialized specialization, not a
second value-typing relation. `ResidentTyped.complete` recovers owned typing
and proves physical absence of vacancies from complete initialization evidence.
Reads, moves and writes share `Initialization.Access` along the exact coordinates
produced by `PathType`. The former read-only `Initialization.Ready` relation is
removed. Source moves and assignments compute the next mask with the same
`Initialization.write`; `ProjectionType.access` and `PathType.write` prove that
the actual resident replacement has that state. `correctness` consumes those
proofs and preserves partial initialization through arguments, bodies and scope
exit, without assuming any runtime post-state.
`Initialization.Access.write_frame` preserves the selected state at every
disjoint coordinate path, including siblings below a shared prefix. Complete
retained subtrees therefore remain readable.
`HasType.no_whole_read_after_clear` rejects a whole-root source read after any
accessible nested clear. `Initialization.setChild_complete_iff` characterizes
restoration: the replacement and every other child must be complete.
`Initialization.Access.restore_complete` proves that writing a complete value
back to an extracted path recovers whole-root completeness when the root was
complete before extraction. These laws accompany the existing exact physical
move/restore round trip.
Strict Lean checking connects nested take/write, sibling framing, restoration
and whole-read rejection to general correctness. Custom hooks remain open; this
is not whole-language soundness. Array indexing and enum payload writes are not
silently treated as ordinary field projection. Indirect reference writes use
the canonical access and permission rules described below.

### Authoritative logical storage identity

`Environment` contains lexical `(name, Root)` bindings, one authoritative
`Root → Option Value` store, and a monotone `nextRoot : Nat` supply.
`Environment.Valid` bounds every occupied cell, including hidden caller cells,
and every visible root below the supply, with distinct visible roots.
`Valid.fresh` derives availability from that invariant. Roots are unbounded
logical identities, not physical addresses, allocation requests or a model of
allocation exhaustion. Shadowing creates a fresh root rather than changing the
identity of the older binding. Retirement never rewinds the supply.

Canonical address resolution/access, binding creation and source-order
parameter/pattern preparation all consume this store. `StoredBindings` is a
read-only relational projection requiring an actual `some resident` for every
binding; typing consumes it, and no missing cell receives a default value.
`BindingValues` denotes transferred inputs before fresh-root introduction, not a
second runtime environment. `prepare` introduces these inputs left to right,
producing the reversed newest-first lexical prefix used by cleanup.

Calls hide caller names, not caller cells. Fresh parameter roots and body
execution use the same store; return restores caller visibility while retaining
the actual post-store and advanced supply. `Evaluates.call_frame` proves that
old roots remain outside callee lexical bindings at entry, and storage outside
incoming live unique-target roots is unchanged after cleanup. Shared-only calls
therefore preserve the complete post-argument caller store. `Evaluates.storage`
and `correctness` prove `Environment.Evolution`: incoming lexical identities and
monotone supply are preserved, and mutation is confined to incoming owners or
live unique-target roots. Hidden cells remain globally typed and bounded.

`Cleans.retired` proves that actual cleanup removes every selected root cell;
`Cleans.frame` and `Environment.retire_retained` preserve all other cells and
retained lexical roots exactly. `Cleans.retired_stays_absent` proves that actual
continuation execution cannot make a retired identity resolve again.
`Environment.Agrees` compares checked lexical logical-value observations across
different root names, supplies and hidden cells. `correctness_referenceFree`
recovers the prior same-data-result agreement from reference-free source and
declarations and loan-free starting worlds. Its empty-final-history premise is
derived, not assumed. General reference executions carry explicit root/node
interpretations; literal equality of reference identities across renamed worlds
is not claimed. No duplicate old evaluator or executable projected store remains.

`Environment.AddressUpdate` is the derived contract of the actual
`writeAddress` equation, not an extra execution or admission premise.
`writeAddress_update` proves exact raw readback, unchanged bindings/supply,
and unchanged raw residents at every disjoint address: different roots or
`CoordinatesApart` field paths below a common root. This includes initialized
siblings and existing holes. Typed write preservation consumes its readback;
`writeAddress_storage` consumes its bindings, supply and frame to produce the
storage evolution used at every nested move/assignment in `Evaluates.storage`
and the general `correctness` contract. There is no second source
walker or execution-occurrence table. This is a per-write frame, not a claim
that later scope retirement preserves the retired cells. Lifecycle framing
remains the separate, existing `Environment.Evolution`/`Cleans` guarantee.

Public source authorization still comes from `ProjectionType/PathType`, not
from possessing arbitrary numeric coordinates. The internal raw `at` API can
observe vacancies; `readAddress` rejects them and any incomplete selected tree,
just as the removed owned `readPlace` did. Canonical access never fabricates a
cell: even an empty-path write fails for a missing or retired root. Direct numeric
addresses are not a newly admitted source syntax or a borrow permission. Arrays
and enum payloads remain outside source field resolution; reference access
uses the checked canonical-address extension below.

### First-class shared and unique references

`HasType` elaborates decoded expressions to `Core`: the original `Expr` plus a
recursively matched `CorePlan`. The sole `Evaluates` relation executes that Core.
Shared/unique borrowing and dereference use `AccessType` and masked canonical
address resolution. Projected access does not copy the containing aggregate.
Referents have finite, reference-free inline layouts; handles can be locals and
direct arguments/results, but are not nested in aggregates in this subset.

Expected types enter the same `HasType`/`HasTypes` producer at binding annotations,
direct-call parameters, reference-assignment RHSs and declared function result
bodies. `ArmsType` carries the expectation into every pattern-result clause;
groups, sequences, continuations and checked administrative nodes preserve it.
A reference-expected bare handle read emits `CorePlan.reborrow mode` in the
requested mode. `HasType.reference_read_selection` proves that the actual plan
is that reborrow, allowing only checked own-ending metadata around it; neither
leaf copying nor implicit transfer is an alternative. Explicit `move` remains
an intentional transfer. `HasTypes.expected_types` derives call argument
agreement; no independent expected-type elaborator or source walker is used.

Without reference expectation, ordinary owned reads copy `Duplicable` values
and move values with positive `Nonduplicable` evidence. The same
`HasType.implicitMove` rule handles unique references and nonduplicable owned
data by reusing the existing authoritative move derivation; its distinct Core
plan preserves fixed-Core determinism. Evidence comes from structural resident
witnesses and nominal restrictions, never failed Copy proof search.
`Nonduplicable.not_duplicable` excludes copying; `FiniteLayout.owned_choice`
classifies every finite data layout. Empty arrays remain duplicable even when
their element type is not; nominal structural evidence covers all variants.
`Evaluates.implicitMove_invalidates` proves that actual default transfer
invalidates the selected source resident. General inference remains outside
this decoded boundary.

Each usable handle has its own loan node and immutable mode. Shared copies and
compatible reborrows allocate fresh child nodes; `Evaluates.reborrow_preserves_storage`
proves implicit reborrowing preserves the original carrier and all owner storage.
Explicit moves transfer the same node and clear the source carrier. Ended records
retain their target and ancestry, but provide no own authority. Ending neither
clears carrier bits nor destroys referents or surviving children. Unique ancestry
is derived from the well-formed parent-mode invariant. A unique handle need not
occupy a mutable binding to authorize mutation of its referent.

`Context.storage` is authoritative for canonical types and initialization masks.
`StoreTyped.cells` covers all stored binders, including hidden callers. `StateTyped`
adds custody and protected evaluated reference prefixes/results. Every active
node has exactly one carrier across the store and pending values; inert ended
bits do not confer custody. `heldReady` tracks actual target readiness, not a
duplicate initialization flag in the loan table.

`endOwn` and `endAfter` are checked administrative Core metadata, not a source
liveness walker. They inspect their actual pre-ending contexts and reject
protected nodes or unrestored live targets. Runtime `endSlot` checks the actual
target before clearing own; `endSlot_checked` proves the readiness consumed.
`Disposes.reference` requires the same readiness, and `Context.Cleanable` checks
scope and parameter disposal in youngest-first order. Reference-carrier
overwrite checks the old handle after RHS evaluation; sequence disposal derives
readiness from its protected result. Metadata has no store/binding/supply effect.
`Core.erase` retains the source; determinism is for fixed Core, not arbitrary
alternative elaboration plans.

`Permits` distinguishes conflict exclusion from positive `Authorizes`. Shared
loans can overlap; unique operations exempt only their selected self/ancestors,
not conflicting descendants. Disjoint fields remain independent. Reads, borrows
and handle transfer require the whole referent restored. Indirect assignment
uses masked access so a hole can actually be repaired. It evaluates the RHS
first, derives ordered destruction from the exact canonical mask and actual
old resident, and writes an initialized replacement. `StateTyped.writeTarget`
reconstructs cells, target correspondence, custody and held readiness. Vacant
moves additionally check pre-state separation from pending targets; complete
writes preserve pending readiness constructively.

`Evaluates.moveIndirect_restore` proves canonical vacancy and exact whole-store
restoration by replacing the extracted resident, preserving siblings and hidden
cells. The actual indirect source/evaluation constructors participate in general
correctness, fixed-Core determinism, storage evolution and reference-free
conservation; no second evaluator or supplied future-state invariant is used.

Calls accept mixed data/reference arguments and arbitrarily aliasing shared
inputs without a non-aliasing premise. Reference results currently require one
reference input and checked `Context.Derived` provenance; local owners cannot
escape. Multiple-input result-origin unions remain outside this subset.
`correctness_noDangling` proves addressable typed targets for both modes and
additionally readable shared targets. `correctness_canonicalTargets` retains
exact authoritative root-to-referent paths and masks. Protected returned values
are restored regardless of mode.

Aggregates containing references, borrowed patterns, captures, branch-origin
unions, effects, custom hooks and physical realization remain open. Parsing,
general inference and whole-language lifetime elaboration are not proved.

### Affine conditional initialization joins

Immediate pattern applications retain each arm's own post-context before joining
it to the common continuation context. `ArmsType.clause` consumes
`Context.Joins`; `correctness` applies `StateTyped.join` only after the
actual selected body and clause-local cleanup. The join retypes that exact
environment without changing, dropping or inventing any branch resident.
Pattern selection and failed alternatives retain their existing non-consuming
meaning. Loan histories, origins, reference node identities and slot binder
identities must agree exactly across the join; initialization-only merging
cannot erase a branch's borrow restrictions.

`Initialization.Joins` preserves an identical mask, or widens an affine
binding to `Initialization.maybe` using its existing `MayDiscard` permission.
`ResidentTyped.uncertain` retains the actual typed resident, including an
actual vacancy or partial aggregate. Identical partial masks preserve field
precision. Widening is deliberately whole-binding conservative: differing
partial masks lose all field precision until the whole mutable root is restored.
This is not field-sensitive join completeness.

`Initialization.Present` now governs every ancestor access: both vacancy
and maybe-initialization forbid descent. `Initialization.Access.maybe_iff`
proves that only the whole root is accessible in a maybe state, and
`HasType.no_use_maybe` rejects both whole and nested reads and moves. Root
assignment still evaluates its RHS first, derives disposal of the actual old
resident through `EnvironmentTyped.resolvePlace` and `StorageDisposition.realized`,
and writes an initialized replacement through `EnvironmentTyped.writeAddress`
and the same `PathType`/`Initialization.write` contract. Thus
restoration establishes definite initialization without assuming old vacancy.
Scope and overwrite eligibility likewise use the actual branch resident; a
vacancy never becomes a fabricated owner. The ordered cleanup relation below
consumes these derived permissions; successful cleanup is not a join premise.

Positive-lower owners cannot use the affine widening rule, regardless of
whether a particular partial residual could be discarded.
`Initialization.Joins.positive_lower` proves the entire existing mask must
remain identical; two arms can therefore share a plain post-context only when
their exact-owner masks agree, including identical partial masks. Conditional
exact-linear control islands and exported correlations remain unsupported.
The source-use rejection and old data cases remain connected under the extended
producer. Borrowing does not license widening or forgetting loan origins; the
current strict-check and axiom audit is recorded below.

### Ownership permissions and zero-use boundaries

`UsePermission` replaces the copy-only structural relation. Its index is a
requested interval, not a claim that the principal class equals that interval:
an exact-once request is supported by all three ordinary principal classes.
`Duplicable` and `MayDiscard` are specializations of this same producer.
Manual restrictions are checked against every field of every variant; they
cannot widen structural capability. Empty arrays remain resident-free.
`UsePermission.weaken` proves interval-request weakening, and
`UsePermission.nominal_restriction` proves fidelity to the selected declaration.

Local bindings, function parameters and pattern binders are checked at their
final initialization state. `StorageDisposition` permits vacancy, whole-type
`MayDiscard`, or an incomplete tuple/structure whose remaining fields are
individually eligible. Pattern binding itself requires neither copying nor
discardability. These cases feed the same general correctness theorem.

`Value.Disposable` states zero-use eligibility for an actual resident.
`Value.Disposable.destroys` constructs an actual `Value.Destroys` derivation:
children execute in reverse declaration order, the enclosing resident finishes
afterward, and vacant slots are skipped. `ResidentTyped.children_disposable`
derives child permissions from the existing structural use producer, including
uncertain affine residents. No execution witness is supplied by admission.
`EnvironmentTyped.cleanup` derives ordered scope destruction and retirement
from the actual final typed store. `EnvironmentTyped.place_disposable` derives overwrite
evidence for the actual selected resident after RHS evaluation, including
vacancy restoration. `correctness` constructs these permissions; source
admission does not assume successful runtime cleanup.
`ResidentTyped.hole_uninitialized` proves that a source-valid vacant path is an
actual resident vacancy: an unused initialization-mask entry cannot authorize
discarding a live fieldless owner. `StorageDisposition.realized` derives actual
residual-shell eligibility, including surviving nested fields.
`StorageDisposition.live_requires_discard` proves that a fully restored resident
again requires whole-type zero-use permission.
`Value.Disposable.not_live_exact_nominal` excludes fully initialized manually
exact-linear owners, including fieldless owners.

Evaluation now consumes destruction executions at sequencing and overwrite
boundaries. Scope removal consumes `Cleans` executions, not permission-only
guards. Parameter and pattern owners receive fresh roots in source order and
are exposed in reverse order, matching newest-owner-first scope cleanup;
arguments still evaluate left to right. `Cleans.suffix` identifies the actual
retired post-state; `Cleans.frame` preserves every cell outside the cleanup
prefix. In valid environments, `Cleans.trace_scoped` and distinct roots exclude
retained owners from cleanup, and `Cleans.exactly_once` rules out repeated
resident occurrences. Traces use stable roots paired with relative field paths,
not shifting lexical indices; distinct roots distinguish equal-valued owners.

Owned-expression projection checks `StorageDisposition` for the statically
computed residual mask, not whole-parent discardability. This admits extracting
from an exact temporary when all surviving fields have a legal disposition.
Evaluation extracts the selected child and clears its slot before destroying
the residual parent. `Evaluates.field_protects_result` proves that no cleanup
event targets that slot or any descendant; no extra Copy requirement is
introduced. Selected patterns use `Pattern.Consumes` and
`ConsumesArm`: binders transfer their complete payload without destruction,
wildcard/literal leaves execute destruction, and deconstruction processes field
discards in reverse order. Failed candidate patterns remain non-consuming.
`PatternType.consume` produces typed bindings and the actual selected-pattern
execution together; the old binding-only theorem is removed.

`Value.Destroys.result_order` identifies every execution's result and reverse
field/postorder trace; `exactly_once` and `skips_vacant_field` prove
uniqueness and vacancy exclusion. The connected `correctness` theorem retains
its result, post-context and determinism contract while constructing these
stronger executions, including after affine joins and shared-handle transfer.
The current connected axiom audit is recorded below.

This is finite logical destruction without hooks. Finish events are not physical
releases or addresses. Shared-carrier cleanup changes own usability separately
from target destruction. Custom hooks and their possible divergence, nonlocal
exits, cancellation, physical release and exact-linear control islands remain open.

The explicit target supplies its positive pointer width. Signed and unsigned
fixed widths remain 8/16/32/64/128; `usize/isize` use the target width throughout
admission, execution and result typing. Integer checking never wraps. Characters
exclude surrogates and values above U+10FFFF. Array construction reuses the
existing constituent relations; admission enforces homogeneous residents,
exact arity and target-representable length. Known-empty arrays are resident-free.

Alias bodies resolve finitely to existing types, including nested tuple/array
types; binding annotations consume that resolution. No alias identity is added
to runtime values. Constant references select declared structural initializers,
check their declared types, and evaluate them with caller names hidden while
retaining the same root store and supply.
Their bodies are admitted in the declaring module, not the caller’s module;
the caller must have access to the constant itself.
The existing evaluation relation and correctness induction perform the work;
there is no separate constant evaluator or assumed evaluated-value table.
Declaration lookup is supplied as decoded maps; whole-package validation,
duplicate-name rejection, generic schemes and source name resolution remain open.

Nominal construction consumes the existing ordered constituent relation and
produces tagged nominal values, never structural tuples masquerading as owners.
One declaration supplies constructor schemas, projection indices and field
types. Private access includes descendants; package/parent/public visibility
is explicit. Aliases cannot change a nominal field’s access rule. Numeric
tuple-struct access and named record access remain distinct; enum payloads
cannot be projected without matching. `UsePermission` checks every variant and
validates a manual principal restriction against structural availability before
allowing any requested bound. Inline type expansion checks every
field and rejects direct recursive layouts and duplicate record field names.
Empty arrays remain resident-free but must have valid element types. This also
repairs the previously unchecked malformed element type of an empty array.

Direct calls select a resolved function identity, check visibility, exact
argument arity/types and distinct parameter names, and admit the actual body
in its declaring module. Arguments evaluate in order. Their proved value
typing constructs fresh parameter roots over the caller store with caller
names hidden; caller cells persist but their names cannot leak into the body. Body admission is a recursive static derivation, not a
promise of execution: correctness carries both argument and body induction
hypotheses through actual invocation. Recursive call cycles have no finite
admission derivation in this subset. Structural constants still exclude calls.
Computed callees, first-class function values, captures, effects, recursion and
named-label exits are not included in this direct-call boundary.

Immediate pattern-callable application supports binders, wildcards, nested
scalar/tuple/array/nominal constructor patterns and named structural constants. It retains the callable’s
argument list: one tuple argument is not two arguments. Source-ordered selection
executes just the first matching body; bindings remain clause-local. Each body
receives the caller environment after argument evaluation and the declared
result type. The selected body’s outer-local updates survive clause exit.
`Covers` is an inductive constructor-space specialization, not a future-match
assumption. Its proof constructs actual successful dispatch for every typed
subject. Pattern binding preservation then constructs the body’s typed
environment; both results are consumed by `correctness`. Duplicate binders
are rejected. Every clause needs a static typed datum distinguishing it from
previous clauses, excluding unreachable clauses without assuming a result
for the subject expression. There is no primitive Boolean or library-name
dispatch rule.

Named constants are retained in `PatternSource`. Their initializers are checked
by ordinary source typing; `correctness` constructs unique normalization using
the same `Evaluates` relation, not a second evaluator or a supplied value table.
Coverage and body typing are checked over those constant normal forms; their
existence is proved before either check is consumed, so missing normalization
cannot make admission vacuous. A normalized literal retains its declared type,
including the element type of an empty array. Structural equality is total and
proved lawful; it calls no user `Eq` and does not ownership-deconstruct a
constant’s private representation. Comparison-only nodes created during
coverage specialization cannot be admitted as typed source patterns.

This pattern boundary is decoded immediate application, not stored callables
or a proof of library `match`. Source record/remainder expansion, borrowed
patterns, first-class callable identity and captured-storage semantics remain
open at their respective source/borrowing/callable boundaries. In particular,
this does not prove source capture formation or compatibility between a
materialized callee’s captured loans and argument evaluation.

Nominal scope excludes generic instances, indirections, hooks and
non-exhaustive-enum deconstruction. Constructor arguments are
already ordered decoded expressions; source record-initializer elaboration
and name resolution are not proved. Parsing, inference, prefix negation,
floating conversion, static strings, custom destruction hooks and effects remain
open. There is no physical-storage, allocation-failure, package-admission
or compiler-realization claim. Big-step evaluation is not a small-step theorem.

Verification: strict checking of `Grounded.lean` with warnings as errors and
auto-implicit variables disabled passed after composing indirect mutation,
mandatory ordinary endings, all existing reference-expected sites, and
positive-evidence default owned transfer. General consumer smoke proofs use
public correctness to derive actual default-transfer execution and source
invalidation, and compulsory requested-mode reborrow plans with usable results.
Earlier consumers also exercised fresh reborrow/unchanged storage and indirect
vacancy/unreadability/exact restoration. These assume arbitrary typed worlds and
source premises, not successful future states; temporary proof scripts were removed.

The independent exhaustive audit selected declarations by their defining module
index, not by name: all 3,607 Grounded declarations, including 185 private and all
generated declarations, depend only on Lean's standard `propext`,
`Classical.choice` and `Quot.sound`. Connected correctness and no-dangling use
those three; fixed-Core determinism and canonical update/readback/frame use only
`propext` and `Quot.sound`. No admitted proof or bypass axiom is present.
Reproduce the strict check and representative connected audits:

```sh
lake env lean -DwarningAsError=true -DautoImplicit=false Grounded.lean
lake build
lake env lean -DwarningAsError=true -DautoImplicit=false --stdin <<'LEAN'
import Grounded
#print axioms Grounded.correctness
#print axioms Grounded.closed_correctness
#print axioms Grounded.correctness_referenceFree
#print axioms Grounded.correctness_noDangling
#print axioms Grounded.correctness_canonicalTargets
#print axioms Grounded.HasType.reference_read_selection
#print axioms Grounded.HasType.reference_read_not_implicitMove
#print axioms Grounded.Nonduplicable.not_duplicable
#print axioms Grounded.FiniteLayout.owned_choice
#print axioms Grounded.Evaluates.implicitMove_invalidates
#print axioms Grounded.HasTypes.expected_types
#print axioms Grounded.Evaluates.reborrow_preserves_storage
#print axioms Grounded.Evaluates.moveIndirect_restore
#print axioms Grounded.Environment.endSlot_checked
#print axioms Grounded.StateTyped.writeTarget
#print axioms Grounded.Evaluates.deterministic
#print axioms Grounded.Environment.borrowed_owner_exclusion
#print axioms Grounded.Evaluates.endOwn_transparent
#print axioms Grounded.Evaluates.endAfter_transparent
#print axioms Grounded.StoreTyped.resolveAccess
#print axioms Grounded.StateTyped.prepare
#print axioms Grounded.StateTyped.resume
#print axioms Grounded.Environment.writeAddress_update
#print axioms Grounded.Environment.writeAddress_storage
#print axioms Grounded.Value.writeIndices_frame
#print axioms Grounded.Evaluates.move_invalidates
#print axioms Grounded.Evaluates.move_restore
#print axioms Grounded.Evaluates.storage
#print axioms Grounded.Evaluates.call_frame
#print axioms Grounded.Cleans.retired_stays_absent
#print axioms Grounded.Evaluates.referenceFree_source_agreement
#print axioms Grounded.Covers.selectArm
#print axioms Grounded.PatternType.consume
#print axioms Grounded.integer_admission
#print axioms Grounded.character_admission
#print axioms Grounded.unit_agreement
LEAN
```

## Construction order and size reviews

Proceed serially, closing each extension through the same end-to-end theorem:

1. Ordinary values, non-generic constants and aliases: connected as described above.
2. Nominal data, constructors, visibility and projection: connected for the subset above.
3. Direct calls and immediate structural-pattern application: connected; remaining pattern/callable boundaries above.
4. Mutable places, initialization, assignment and explicit moves: whole-root and
   nested tuple/structure moves, partial restoration, sibling access and
   incomplete-aggregate rejection are connected through the general theorem.
5. Affine/exact-linear ownership, destruction and scope cleanup: shared use
   permissions, final-state zero-use eligibility and residual exact-linear
   shells, conservative affine joins and ordered logical destruction are connected
   above; hooks and correlation-preserving exact-linear control islands remain open.
6. Stable logical roots, authoritative storage, non-reused supply, actual
   retirement, canonical stored-place addresses and exact update framing are
   connected prerequisites, as above.
   First-class shared/unique borrowing, canonical projected referents, mutable
   indirect access, hole restoration, checked own ending, affine handle transfer
   and single-input-origin returned references use the same storage, ancestry,
   custody and invocation mechanisms described above.
7. Callables, captures and invocation quantities.
8. Recursion and finite/infinite execution guarantees.
9. Labels, nonlocal transfer and proper tail invocation.
10. Effects, handlers, replay, cancellation and cleanup.
11. Generics, traits, constraints, inference and static evidence.
12. Physical representation, allocation/exhaustion and unsafe operations.
13. Floating-point contracts and authenticated static literal storage.
14. Source authentication, packages, resolution and elaboration.
15. Foreign/runtime/ABI and compiler-correctness composition; full normative audit.

This is dependency order, not disconnected workstreams. Move a requirement
earlier when its current consumer needs it. Do not add a standalone admission
checker without a present semantic obligation requiring one. No primitive
booleans: truth and branching use ordinary library declarations.

At verified checkpoints, review size, duplicated reasoning and unused concepts.
Simplify where meaning and guarantees are preserved; do not introduce a generic
framework merely to shorten local proof plumbing. Pattern coverage and binding
preservation are connected immediately to the same expression theorem. Runtime
typing supplies one constructor decomposition to both proofs. Place and
expression projections share field selection; tuple and nominal updates share
positional typing. Arrays and constructors share constituent evaluation;
constants reuse ordinary evaluation. Shared storage and custody preservation
are consumed by the same expression, constituent, call and pattern induction.
The module remains one connected development; no standalone admission checker,
reference evaluator or speculative proof module is added.
