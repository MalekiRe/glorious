# Grounded language specification

This is a language-semantics and future compiler-correctness development, not a
compiler implementation. The normative
[language specification](../../glorious-language-specification.md), especially
§§5.2–5.3, 7.2–7.7 and 9.1–9.2, governs this boundary. Follow the
[compiler architecture contract](../../docs/compiler-architecture.md) when
connecting implementation work. Earlier `formal/spec` and `formal/lean` trees
are reference material, not imported foundations.

## Discipline

Build from established meaning toward soundness. Admission must not assume
successful execution, a future typed state, runtime readiness callbacks, or an
allocation-success witness. A strict Lean proof proves its stated proposition,
not fidelity of its definitions or inhabitance of arbitrary premises. Audit
those independently. No `sorry`, `admit`, bypass axioms, parallel source walkers,
or unused precursor interfaces are acceptable.

One authoritative product should connect each source rule to actual evaluation,
storage and consumers. Preserve ownership, permissions, custody, initialization,
provenance and declaration identity as distinct concepts. Grow the same
semantics and general result; remove replaced paths rather than maintain shims.
Use general consumer proofs and exhaustive axiom audits, not routine examples or
unit tests. A completed bounded extension is not full-language completion.

## Connected boundary

`Grounded.lean` contains the complete connected development. The authoritative
expression producer is `Grounded.Elaboration.HasType`, mutually defined with
`HasTypes`, `ArmsType` and pattern-constant producers. These produce types,
compositional payloads, final contexts and Core plans. `Grounded.Evaluates` is
the sole evaluator, including constant normalization. There is no old direct-only
expression producer alongside this one.

The admitted decoded syntax covers unit, selected nonnegative fixed/target-width
integer literals, Unicode scalar characters, grouping, ordinary reads, explicit
and evidence-backed default moves, sequencing, initialized mutable/immutable
bindings, annotations, tuples, arrays, non-generic nominal constructors and
projection, transparent aliases, structural constants, finite nonrecursive
first-order calls, and immediate structural pattern application. Partial moves,
restoration, reference borrowing/reborrowing, indirect access and mutation use
stable logical roots and canonical field coordinates. Literal bounds, nominal
identity, field visibility, principal restrictions, arity and evaluation order
remain checked. Unit, grouping and singleton tuples are distinct.

### Qualified declarations and signature resolution

`Program.declarations` owns qualified nominal fields; `Program.data` derives
canonical layouts by erasure, rather than accepting an independently supplied
declaration table. `QualifiedTy` retains nested lifetime arguments while its
index fixes the canonical storage shape. Qualified projection and path proofs
preserve declared view bounds and derive canonical projection from this same
program product. Nominal view conversion unfolds the qualified declared fields;
unique referents remain invariant, including their nested qualifiers.

`FunctionDecl.signature` owns qualified input and result syntax and distinct
named lifetime binders. `ResolvedSignature` resolves inputs left-to-right from
a supply beyond the named binders. Every omitted input occurrence gets a fresh
parameter; repeated named occurrences share their declared parameter. Omitted
output lifetimes require one unique resolved input lifetime, not one active
runtime node or mutually exclusive constructor. Unknown names and ambiguous
output elision have no resolution derivation. Omitted function results are unit.

The actual `HasType.call` constructor carries this resolved product in both
phases and checks qualified input/result well-formedness against the same
`Program.declarations`, including nominal existence and lifetime-argument arity.
Erasure preserves both resolution and well-formedness evidence.
`ResolvedSignature.unique` proves determinism; `ResolvedSignature.closed` bounds
every input and result region by the produced supply. `HasType.call_signature`
derives well-formedness and closure for every admitted named call, including
administrative and expected-type wrappers. The existing general execution-
correctness theorem consumes the migrated producer.

Source and checked slots, expression results, pattern fields and aggregate
results now carry intrinsic qualified types. Binding and preparation retain
them; storage joins preserve qualification alongside canonical type and owner
identity. Reads and dereferences preserve the selected qualified type. Moves,
borrows, writes and field extraction consume qualified paths/projections from
the same declaration product. Pattern decomposition instantiates the qualified
constructor fields rather than inventing erased field types. Checked-to-source
cell correspondence requires equality of the complete qualified type; canonical
entry import and phase erasure preserve that correspondence. The general
execution and cleanup correctness proofs consume these migrated producers.

Invocation substitutions, qualified annotations/coercions, region-validity
interpretation and source return provenance remain open. A carried qualifier is
not yet a proof of its lifetime bound. The bounded return rule below remains;
no multi-input lifetime safety or complete declared-lifetime conformance is claimed.

### A single produced payload and authoritative storage

`SourcePayload` is `.plain`, a reference node, or a constructor head plus child
payloads. It records the actual selected nominal variant and nested field
occurrences. `.plain` denotes an actually reference-free subtree; it does not
assert that every variant of its nominal type is reference-free. Its node list,
selection and replacement are projections of this product, not independent
reference scans.

`Slot.payload` and `ResultType.payload` replace direct-only reference metadata.
`Context.storage` is authoritative for every canonical backing root, including
external storage. `Context.names` selects only lexical owners; hidden backing
roots need not be named and are not retired by lexical cleanup. Each cell has a
declared root type, current initialization mask and current payload. Immutable
declaration metadata excludes mutable payloads. Hidden caller payloads may change
through authorized indirect mutation; calls reconstruct from actual callee
post-storage rather than restoring old metadata.

Arguments are handles, not root identities. Shared aliases, disjoint unique
fields and parent/child targets can select the same canonical root with their
respective paths. Interpretation is injective only on distinct canonical roots,
never on argument references. Unique access derives its referent authority from
the loan, not mutability of the local handle binding. Reads, moves and writes
query the same root mask/payload; a move can create a hole and assignment restores
the selected subtree without stale per-input state. Source identities do not
allocate runtime owners.

`StateTyped` relates a list of pending source payloads to the **actual pending
values**. `Carries` records a stored root or pending-value index together with
its exact nested field path. Custody uniqueness therefore concerns occurrences,
not just aggregate roots. Packing/unpacking tuples or argument bundles changes
only this representation; no second ownership inventory is maintained.

### Checking, dormant clauses and actual realization

The producer is indexed by `.checking` or `.executable`. `Payload` retains one
selected symbolic product; executable points additionally carry its source
interpretation. Exact erasure keeps expression/plan indices, chosen products,
ordinary resource checks and branch bodies. It drops only actual-world evidence.
Fresh symbolic identities are allocated at their producing step, not constrained
to predict later meanings.

An opaque schema retains declared possible reference paths without claiming
that any runtime field or live handle exists. Source-proved reference-free
knowledge remains distinct from arbitrary hypothetical schemas. Canonical
current-state import derives knowledge from authoritative cells and their typed
residents, and supplies
`SourceImport.pointOfStore`; `imported_correctness` consumes that entry. Imported
opaque schema identities distinguish canonical roots and constructor/field
paths, with fresh schema supply reserved above those identities. Ending one
source-known plain subtree cannot accidentally end another through a reused ghost
identity. No source cell is fabricated from a nominal type.

`SourceImport.CanonicalEntry` exposes the initial backing-root contract: declared
root types/masks and payloads agree with actual store residents, together with
current loan history, permission, custody and exact pending-value evidence. It
derives visible resident typing and slot correspondence through
`Context.reconstruct`, constructs `StateTyped`, then supplies the canonical
imported producer point. It assumes neither successful normalization nor future
evaluation. This strengthens the former open-world value-shape premise to
genuine canonical root typing: a current subvalue alone cannot establish the
type of a vacant unique target or the backing layout. This is missing modeling
evidence made explicit, not a new source-language restriction.

`PatternProduces` consumes the same chosen payload. Its executable projection
uses the existing `PatternType` and `Pattern.matchValue`, transferring bindings
and disposing actual residual resources in order. A dormant clause still checks
its entire body and siblings with the same checking producer on declared input;
its impossibility proof is indexed by the original produced product. The general
no-match consumer uses the existing matcher. It does not assume runtime match
success, reconstruct a second matching relation, or erase ordinary checking.

Pattern constants normalize by the same evaluator. The general
`PatternConstantsTyped.normalizes` and `ArmConstantsTyped.normalizes` proofs
already establish an inhabited normalization domain in checking, so universal
coverage/body obligations cannot be satisfied vacuously.

### Construction, copying, transfer and projections

Aggregate construction evaluates constituents once from left to right,
threading their actual post-states and pending payloads. Argument preparation
consumes those same results. Structural shared Copy recursively creates a fresh
child loan at each actual reference occurrence; both checked and source Copy
products record its lineage. Aggregates containing actual unique reference
occurrences cannot be copied; zero-resident constituents retain the existing
positive permission rules. Ordinary noncopy read selection requires positive
`Nonduplicable` evidence rather than treating failure to prove Copy as permission
to move. Explicit moves transfer existing nodes and clear only the selected
resident; other fields and aliases are not silently cleared.

Reference-expected bare reads retain the requested-mode reborrow plan. Aggregate
expected-data propagation cannot bypass direct-reference reborrow. Owned field
projection selects the child payload, clears that child in the residual payload,
and disposes the residual value with the selected result protected. Copy,
transfer and disposal therefore use the same produced nested resources.

### Permission, inner resources and ordered ending

Own permission, supported ancestry and readiness are separate. A live outer
loan or initialized bits alone do not authorize use of inner handles.
`TargetPayload` selects the authoritative target product, and source
resource-availability checks establish the required inner ownership/support.
Every live outer observation retains the required inner Own protection; ending
and mutation preserve that closure. Parent and descendant permissions remain
distinct, including suspended unique parents, shared aliases and disjoint unique
fields.

Pending arguments and returned nested references retain Own and restored-target
obligations. Ordinary ending resolves the **current** carrier field, including
post-body selection. Sequence disposal, overwrites and cleanup cannot end a
protected pending reference or an inner handle still observed elsewhere.

`Environment.Disposes` recursively ends nested handles in reverse field order;
lexical/parameter cleanup uses reverse binding order. Assignment evaluates the
RHS first and disposes the old resident **in place at the same canonical address**
before replacement. It does not detach the old value into another storage
identity, exempt an observer from closure, or invoke pure data destruction on
reference bits. The old mask controls partial destruction; complete replacement
restores only the selected subtree. Target/caller preservation is derived from
the actual resulting store.

### Calls, returned origins and canonical views

Calls hide names, not authoritative cells. They prepare actual argument values,
execute the body, protect the returned payload through ordered parameter cleanup,
and resume the caller from actual post-storage. `Environment.Evolution` frames
outside incoming owner/live-unique roots and proves fresh-root retirement; it
never grants access authority.

Every returned nested node must satisfy the actual input-origin rule.
`ReturnStep` also checks this locally for declared symbolic occurrences. A
positively handle-free result needs no reference input. Otherwise the current
bounded rule permits at most one simultaneous input reference occurrence, and
every result node must derive from it. Mutually exclusive variants do not count
as simultaneous runtime occurrences. This is **not** full declared-lifetime
return checking: signatures resolve lifetime parameters and bindings retain
qualified types, but calls do not yet instantiate those signatures and
`ReturnStep` still checks bounded provenance. `correctness_return_cleanup` connects general
body execution, actual cleanup, returned usability and runtime ancestry at every
nested returned occurrence; cleanup does not auto-end the returned handles.
Every active target after cleanup is backed by storage already present before
body evaluation and lies outside the retired parameter roots. This is derived
from actual execution, canonical target addressability and retirement, not an
assumed owner-survival or declared-region contract.

Executable referent views are immutable lenses, not owner allocations or mask
caches. `ContextMeaning.noOpaqueCells` forbids opaque referent cells in every
executable producer point; root coverage includes hidden storage, and represented
root identity prevents two checked cells from denoting one actual canonical root.
This does not require distinct reference targets or paths. `ViewStep.canonical`
queries an already-known symbolic target, its existing root and full path, and
the current mask without changing any target, cell, name, loan history or supply.
`ViewStep.executable_lens` proves this for every executable view.

`SourceImport.Cells.canonicalView` derives that lens from the actual selected
stored handle and its field path; `CanonicalEntry.view` constructs the producer
branch with exact erasure. Parent/child aliases and vacant unique targets retain
their current canonical masks. The old separately typed input subvalues and
opaque shared-only fallback are removed. Derived copies retain canonical
provenance, and ended views retain no stale mutable mask.

Hypothetical opaque views remain available for dormant checking. They cannot
inhabit executable points. Erasure preserves the selected canonical or
hypothetical branch exactly; this does not claim that every hypothetical
checking derivation has an executable realization. `checked_correctness`
continues to require the exact realization of the chosen checking product.

## General theorem and public consumers

`Elaboration.HasType.execution_correctness`, `HasTypes.execution_correctness`
and `ArmsType.execution_correctness` are the connected mutual proof. Given a
current typed state, they construct evaluation and actual post-state typing.
They contain no premise asserting future evaluation or successful cleanup.

`Elaboration.correctness` exports evaluation existence, result typing, exact
pending-value state/custody, interpretation and source-history progress, storage
evolution, returned usability and uniqueness for the admitted Core. Public
consumers include:

- `canonical_entry_correctness`: constructs the initial state from canonical
  root and current resource evidence, then consumes the imported producer and
  the same general correctness theorem.
- `imported_correctness` and `closed_correctness`: canonical imported or empty
  entry; closed evaluation retires cells without resetting supplies/history.
- `correctness_referenceFree`: conservation and agreement for the same evaluator
  under reference-free syntax/declarations and empty initial loan histories.
- `correctness_noDangling`: addressable typed active targets with actual masks,
  backed by roots already present at expression entry. Fresh scoped roots and
  resurrected vacancies cannot escape. Universal readability is asserted for
  shared targets, not arbitrary unique targets with temporary holes.
- `correctness_canonicalTargets`: exact root-to-target paths, masks and actual
  resident typing for all active targets, including hidden external roots.
- `correctness_targetClosure`: every nested leaf of an active target retains
  Own and support; every actual pending leaf additionally retains restoration.
- `checked_correctness`: an executable source-rule realization must erase to the
  particular chosen checking derivation, not only agree in type/plan indices.
- `correctness_return_cleanup`: occurrence-wise returned origin and protection
  through actual ordered cleanup, excluding retired parameter roots from every
  surviving active target.
- Expected-read and ordinary-choice consumers: compulsory requested-mode
  reborrow and positive-evidence default Copy/transfer selection.

These specialize the one general theorem or the authoritative producer; they are
not examples, additional admission paths, or an alternate reference evaluator.

## Explicit limits

`FiniteLayout` expands inline fields of every nominal variant but treats a
reference as a finite handle, without recursively expanding its referent. It is
separate from positive `ReferenceFreeLayout` and from referent ownership or
readiness. Even zero-length arrays check element layout and target size bounds.
This distinction does not establish generic layouts, physical sizes/alignment,
allocation success, or a complete recursive-type semantics.

External unique references use the same canonical mutation/restoration rules as
source-derived callers, including initially masked targets. Entry requires
genuine canonical backing-root evidence; arbitrary value-shape-only external
worlds are not claimed to supply it. The return boundary remains the bounded
singleton-origin rule above. Reference-free agreement is not observational
equivalence of all loan-bearing worlds or proof that every surface program
elaborates.

Other open language boundaries include recursive/diverging calls, general
callables/captures, nonlocal transfer and proper tail invocation, effects and
handlers, replay/cancellation, generics/traits/constraints, full lifetime and
drop checking, custom destructor hooks, physical allocation/exhaustion, unsafe
operations, floating conversion/static strings, packages/source authentication,
foreign/ABI/runtime composition and compiler realization. Logical big-step
soundness is neither small-step progress nor full language completion.

## Verification

Strict standalone checking passed with auto-implicit variables disabled and
warnings as errors. The exhaustive defining-module audit covered **7,718
declarations, including 291 private declarations** and all generated
declarations. Its only transitive axioms were the standard `propext`,
`Classical.choice` and `Quot.sound`; no admitted or unapproved axiom was present.
Verification rests on general theorems and exhaustive axiom auditing; no
permanent example/test suite is introduced. Reproduce the strict module check
and exhaustive defining-module audit from this directory:

```sh
mkdir -p .lake/build/lib/lean
lake env lean -DautoImplicit=false -DwarningAsError=true \
  -o .lake/build/lib/lean/Grounded.olean Grounded.lean
lake env lean -DautoImplicit=false -DwarningAsError=true --stdin <<'LEAN'
import Lean
import Grounded
open Lean Elab Command
set_option autoImplicit false
run_cmd do
  let environment ← getEnv
  let some definingModule := environment.getModuleIdx? `Grounded
    | throwError "Grounded defining module is missing"
  let mut names : Array Name := #[]
  for (name, _) in environment.constants.toList do
    if environment.getModuleIdxFor? name == some definingModule then
      names := names.push name
  if names.isEmpty then throwError "Empty defining-module audit"
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut privateCount : Nat := 0
  let mut used : Array Name := #[]
  for name in names.qsort Name.quickLt do
    if name.toString.startsWith "_private." then privateCount := privateCount + 1
    let axioms ← collectAxioms name
    for axiomName in axioms do
      if !allowed.contains axiomName then
        throwError "Unapproved axiom {axiomName} in {name}"
      if !used.contains axiomName then used := used.push axiomName
  logInfo m!"AUDIT_DECLARATIONS={names.size}; PRIVATE={privateCount}; AXIOMS={used.qsort Name.quickLt}"
#print axioms Grounded.Elaboration.correctness
#print axioms Grounded.Elaboration.correctness_noDangling
#print axioms Grounded.Elaboration.checked_correctness
#print axioms Grounded.Elaboration.correctness_targetClosure
#print axioms Grounded.Elaboration.correctness_return_cleanup
#print axioms Grounded.Elaboration.imported_correctness
#print axioms Grounded.Elaboration.canonical_entry_correctness
#print axioms Grounded.Elaboration.HasType.reference_read_selection
#print axioms Grounded.ResolvedSignature.unique
#print axioms Grounded.ResolvedSignature.closed
#print axioms Grounded.Elaboration.HasType.call_signature
LEAN
```
