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

### A single produced payload and authoritative storage

`SourcePayload` is `.plain`, a reference node, or a constructor head plus child
payloads. It records the actual selected nominal variant and nested field
occurrences. `.plain` denotes an actually reference-free subtree; it does not
assert that every variant of its nominal type is reference-free. Its node list,
selection and replacement are projections of this product, not independent
reference scans.

`Slot.payload` and `ResultType.payload` replace direct-only reference metadata.
`Context.names` selects stable binder identities in authoritative
`Context.storage`. Stored cells pair canonical initialization masks with the
current payload. Immutable declaration metadata excludes mutable payloads.
Hidden caller payloads may change through authorized indirect mutation; calls
reconstruct from actual callee post-storage rather than restoring old metadata.

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
opaque schema identities distinguish canonical binder/input roots and constructor/field
paths, with fresh schema supply reserved above those identities. Ending one
source-known plain subtree cannot accidentally end another through a reused ghost
identity. No source cell is fabricated from a nominal type.

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
elision: distinct lifetime parameters, variance and outlives constraints are not
represented by this `Ty` model. `correctness_return_cleanup` connects general
body execution, actual cleanup, returned usability and runtime ancestry at every
nested returned occurrence; cleanup does not auto-end the returned handles.

First-use referent views are checking metadata, not owner allocations. Known
parent/descendant targets use their canonical owner root and current mask.
Canonical source import preserves known active-variant facts. Only an absent
external, source-proved reference-free **shared** target may use the opaque
existing-node referent view; this fallback cannot acquire unique write authority.
Derived copies retain the canonical view. Ended views need no stale mutable mask
cache, and shared input aliases are not assumed injective or disjoint.

## General theorem and public consumers

`Elaboration.HasType.execution_correctness`, `HasTypes.execution_correctness`
and `ArmsType.execution_correctness` are the connected mutual proof. Given a
current typed state, they construct evaluation and actual post-state typing.
They contain no premise asserting future evaluation or successful cleanup.

`Elaboration.correctness` exports evaluation existence, result typing, exact
pending-value state/custody, interpretation and source-history progress, storage
evolution, returned usability and uniqueness for the admitted Core. Public
consumers include:

- `imported_correctness` and `closed_correctness`: canonical imported or empty
  entry; closed evaluation retires cells without resetting supplies/history.
- `correctness_referenceFree`: conservation and agreement for the same evaluator
  under reference-free syntax/declarations and empty initial loan histories.
- `correctness_noDangling`: addressable typed active targets with actual masks;
  universal readability is asserted for shared targets, not arbitrary unique
  targets with temporary holes.
- `correctness_canonicalTargets`: canonical binder-target paths, masks and
  actual resident typing; no fabricated external target cells.
- `correctness_targetClosure`: every nested leaf of an active target retains
  Own and support; every actual pending leaf additionally retains restoration.
- `checked_correctness`: an executable source-rule realization must erase to the
  particular chosen checking derivation, not only agree in type/plan indices.
- `correctness_return_cleanup`: occurrence-wise returned origin and protection
  through actual ordered cleanup.
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

Live external unique `.input` origins remain excluded. Actual source-derived
unique call arguments retain canonical binder origins; arbitrary shared aliases
remain allowed. The return boundary is the bounded singleton-origin rule above.
The reference-free agreement theorem is not observational equivalence of all
loan-bearing worlds, nor a proof that every surface program elaborates.

Other open language boundaries include recursive/diverging calls, general
callables/captures, nonlocal transfer and proper tail invocation, effects and
handlers, replay/cancellation, generics/traits/constraints, full lifetime and
drop checking, custom destructor hooks, physical allocation/exhaustion, unsafe
operations, floating conversion/static strings, packages/source authentication,
foreign/ABI/runtime composition and compiler realization. Logical big-step
soundness is neither small-step progress nor full language completion.

## Verification

Strict standalone checking passed with auto-implicit variables disabled and
warnings as errors. The exhaustive defining-module audit covered **6,655
declarations, including 252 private declarations** and all generated
declarations. Its only transitive axioms were the standard `propext`,
`Classical.choice` and `Quot.sound`; no admitted or unapproved axiom was present.
No routine examples or tests were used. Reproduce the strict module check and
exhaustive defining-module audit from this directory:

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
#print axioms Grounded.Elaboration.checked_correctness
#print axioms Grounded.Elaboration.correctness_targetClosure
#print axioms Grounded.Elaboration.correctness_return_cleanup
#print axioms Grounded.Elaboration.imported_correctness
#print axioms Grounded.Elaboration.HasType.reference_read_selection
LEAN
```
