# Language semantics proof plan

## Authority and current status

This is the single active proof plan for the new development in
`formal/semantics/`. The requirements in [AGENTS.md](../../AGENTS.md) govern it.
The [compiler architecture contract](../../docs/compiler-architecture.md)
governs semantic authority; the
[language specification](../../glorious-language-specification.md) and relevant
normative library contracts determine language meaning.

The user authorized this new folder after reviewing the previous development's
assumed realization bridges and incompatible invariants. Existing work in
`formal/spec/`, `formal/grounded-spec/`, and `formal/lean/` is preserved as
reference, not developed in parallel. No old theorem is automatically a theorem
of this development. No temporary code, assumed bridge, or placeholder Lean
project is introduced by this reset. Subagent use remains paused.

## Current proved contract and ownership

General source safety is defined in `Grounded/Soundness.lean`:

```lean
program.Checked →
HasType program home context expression type →
EnvironmentTyped program environment context →
Run program ⟨environment, .expression expression, []⟩ state →
ConfigurationTyped program context (.one type) state ∧
  (Terminal state ∨ ∃ next, Step program state next) ∧
  EnvironmentFrame context environment state.outerEnvironment
```

Call sites check declaration signatures, not callee bodies. `Program.Checked`
checks each declaration body against its interface. It contains no termination,
future-state readiness or execution-success premise. Recursive calls are therefore
admitted without finite expansion of their bodies. Preservation obtains body
checking from the selected declaration at invocation entry.

`HasType.evaluation_soundness` proves declared result typing, successor-store
realization and immutable framing for every completed execution, including
recursive executions. `correctness` additionally constructs a unique completed
execution when supplied `FiniteCalls program expression`: accessibility of the
static subexpression/call-body dependency relation. This is an optional
termination criterion, not part of ordinary admission or prefix safety.

Structural constants terminate directly from their checking derivation through
`constant_correctness`, independently of `Program.Checked` and `FiniteCalls`.
Certified source-pattern normalization consumes this theorem. Its public safety
consumer exports the complete prefix contract above; its terminating correctness
consumer separately requires finite call expansion.

The admitted logical fragment still requires fully initialized storage and
copyable/disposable expression operations. Mutable lexical storage, checked
projected writes and recursive declared functions are covered. Moves, holes,
loans, resolved storage identities and physical memory remain outside it.



| Module | Authoritative responsibility |
| --- | --- |
| `Model` | Decoded vocabulary and declarations; no checking/execution certificates |
| `Types` | Alias resolution, finite layout and duplicability |
| `Values` | Structural value equality, resident typing and indexed access |
| `Lexical` | Binding lookup, lexical realization, replacement and immutable framing |
| `Places` | Checked projection/path/place contracts and actual reads/writes |
| `Matching` | Runtime matching, subject interpretation and first-arm selection |
| `Patterns` | Pattern typing, coverage/usefulness and constructive binding/selection proofs |
| `Checking` | Expression, argument and arm admission |
| `Execution` | Explicit frames, single-step execution, finite runs and operational determinism |
| `Evaluation` | Terminating execution and composition derived from machine runs |
| `ConfigurationTyping` | Current-state/continuation realization, entry, preservation and progress |
| `Termination` | Structural constant termination and optional well-founded call expansion |
| `Soundness` | Prefix safety and the preserved terminating-fragment theorem |
| `SourcePatterns` | Certified constant normalization and its public source consumer |

The former `Core.lean` is removed, not retained as a compatibility import.
Checking consumes storage and pattern contracts; execution consumes storage
operations and matching. Soundness joins the two. Constant normalization
consumes soundness, so its compile-time evaluation dependency is acyclic.
The original terminating contract is preserved; `Evaluates` now denotes finite machine execution.

## Verified recursive declaration boundary

`FunctionChecked` owns parameter distinctness, the current duplicable-parameter
exit requirement, and body checking against the declared parameter/result types.
`HasType.call` and `FrameTyped.call` no longer embed callee-body derivations.
`ConfigurationTyped.preservation` and `run` consume `Program.Checked`;
`progress` constructs an actual next step from current realization.

`Frame.environment` is the shared scope-exit/caller-return operation used by
`Step` and the entry-visible environment projection. `frame_step` and
`frame_run` prove immutable framing through actual ordered transitions,
including RHS mutation, local scopes, selected clauses and recursive calls.
The projection does not execute pending code or assume future completion.
`HasType.soundness` and `SourceArmsChecked.soundness` export this invariant.

The independent `Termination` module proves structural constant evaluation and
optional finite-call evaluation using the same machine. No second evaluator,
compatibility call rule or future-execution field remains.

Verification: strict `lake build` passed (17 jobs). The defining-module audit
covers private and generated declarations as well as public theorems and permits
only `propext`, `Quot.sound` and `Classical.choice`. No concrete examples or
unit tests were added. This is a recursive safety boundary, not whole-language
soundness: resolved binding/activation/storage identities and flow-sensitive
move/restoration/scope-disposition checking remain open.


## Resolved lexical-key cutover

`BindingId` is now the key of local declarations, rooted places, function
parameters, pattern bindings, checking contexts and runtime environments.
Matching produces bindings with those same IDs; lookup and replacement compare
IDs rather than source spellings. The complete preservation/progress, optional
termination and source-normalization consumers use this representation. There
is no legacy string-keyed local access path or compatibility coercion.

This is a decoded-core input contract, not a proved source resolver. Alias,
constant and named-field lookup retain their existing textual interfaces.
The source-pattern interface now takes already-resolved binder IDs. Proving
source resolution, declaration-ID freshness and dynamic activation/storage
identity remains necessary; a lexical ID is explicitly not a storage address.
The logical environment still directly holds resident values, so this cutover
alone does not close the full identity/availability migration.

Verification: strict `lake build` passed (17 jobs). Transient general Lean proofs
established that any injective encoding of the former local keys preserves
actual lookup and replacement for every environment. These comparison functions
existed only in stdin. The defining-module audit covered 1,939 declarations and
found only `propext`, `Quot.sound` and `Classical.choice`.


## Verified explicit-frame migration

`Execution` now owns `Control`, `Frame`, `Configuration`, `Step`, `Run` and
`Terminal`. Pending argument values, selected declarations, scope boundaries
and caller environments are explicit runtime data. Runtime configurations
contain no typing or future-execution proof. Invalid access has no transition;
it is not treated as exhaustion or an allowed abort.

`Evaluates` and `EvaluatesMany` are definitions of finite machine runs.
Their composition theorems execute subcomputations under actual continuation
frames. The old inductive evaluation rules are removed. `Step.unique`,
`Run.unique` and evaluation uniqueness are proved independently of checking.

The current-state invariant is `ConfigurationTyped`: actual environment typing,
current code/value typing and compositional continuation typing. Frames retain
only checked future code and actual typed held values; they do not assume that
future evaluation succeeds. `ConfigurationTyped.entry` constructs this invariant
from `HasType` and the actual entry environment. `preservation` proves it after
every actual step, `progress` constructs a step or proves normal termination,
and `run` carries it through arbitrary finite execution prefixes.
`normal_form` extracts the typed final value/store of a completed expression.

`HasType.soundness` and `SourceArmsChecked.soundness` consume that chain.
The source theorem uses `SourceArmsChecked.admits`, also consumed by the
terminating source theorem; normalized arms and their checking products are not
reselected. `EnvironmentTyped.parameters` is the shared invocation-entry
producer, while `ArmsType.selected` constructs the actual selected body's
checking and local realization from the original checked alternatives.

Verification: strict `lake build` passed (16 jobs). A transient general Lean
proof compared the former evaluator with machine evaluation for every admitted
expression, actual typed entry store, result and successor store, proving both
directions. The old relation existed only in stdin for this proof; no legacy
evaluator or compatibility module remains. Lean audited all 1,858 declarations
from the thirteen semantic modules, including private/generated declarations;
only `propext`, `Quot.sound` and `Classical.choice` occur. The runtime-only
import still contains neither `HasType` nor `correctness`.

At this earlier checkpoint, the operational migration covered the original
fragment only. Call-site typing still embedded body typing; that restriction is
removed by the recursive declaration boundary above. Resolved identities and
flow-sensitive holes/restoration remain open semantic cutovers.
No allocation, loans, control transfer, cancellation or foreign-runtime outcome
has been added or assumed.



## Migration contracts and premise producers

The restructuring migrates this development; it does not introduce a second
specification tree. The current terminating theorem remains a preservation
obligation during the migration, not the destination theorem for recursion.
The following are design contracts, not assumed Lean declarations.

| Boundary | Required conclusion | Premise producer |
| --- | --- | --- |
| Checking | Resolved code, incoming static facts and guarded outgoing contracts | Source resolution, declaration interfaces and compositional checking rules |
| Entry | A valid initial configuration realizing the checked incoming facts | Actual entry arguments and their legitimate type/resource evidence |
| Preservation | An actual step preserves configuration realization and its applicable outcome contract | The operational step and the preceding configuration invariant |
| Progress | A realized nonterminal configuration takes a step or reaches a specifically permitted external boundary | Checking, declaration-body correctness and current-state operation contracts |
| Terminating behavior | A finite run has the promised result, successor storage and disposition | Preservation along that run; termination proved separately where required |
| Structural constants | Checking constructs a unique terminating constant run and normal form | Structural syntax and well-founded constant dependencies, not general function termination |
| Refinement | A concrete implementation preserves permitted observable behaviors | Explicit representation and step-simulation proofs, not a source-admission field |

Static facts, runtime state and their realization are separate responsibilities.
Realization must describe unavailable storage without making it ready: read,
move, borrowing, transfer and cleanup consume their own current-state readiness.
Incoming argument carriers and already-produced values remain represented while
later arguments execute. No pending post-state readiness may be supplied as an
entry premise. The producer-consumer chain for selected branches keeps the
original checking derivation, actual first-match decision and branch correlation.

Source names resolve to lexical binding identities; dynamic activations map
those identities to actual storage identities. Recursion reuses the lexical
identity but creates a distinct activation and storage. Reference-handle storage,
referents and loans remain distinct. These distinctions enter together with
resolution, lookup, allocation and realization consumers, not as unused tables.

Checking must describe incoming facts and possible outgoing facts. Normal
return, nonlocal transfer, cancellation and absence of normal continuation must
not be collapsed into one unconditional context. The first stateful cutover
must implement actual availability changes and restoration; an extra context
parameter that is always equated to its input would not close that boundary.
Calls use declared interfaces; checked bodies establish those interfaces
separately. A call-site derivation must not recursively contain the callee body.

The operational cutover uses explicit evaluation frames and one step relation.
Frames represent ordered arguments, retained values, scopes and return targets.
The existing terminating evaluation interface must be recovered from finite
machine execution, with equivalence proved before removing its old rules.
Divergence is not a safety fault; neither invalid access nor an unproved case may
be reclassified as exhaustion or an allowed abort.

Operation contracts are shared across reads, writes, moves, loans, invocation,
scope exit and later control disposition. Each operation states its required
facts, actual transition and proved preservation/postconditions. Physical
allocation, foreign interaction and compiler representations remain separate
refinement boundaries. No physical or whole-language theorem is claimed by the
current logical storage model.

The implementation order is dependency-driven: separate existing authoritative
owners; migrate identity and flow-sensitive storage together; replace the
termination-bound call/checking boundary and evaluator with proved machine
contracts; preserve source normalization and all public consumers; then extend
those contracts through ownership, control and representation boundaries.
A module split alone does not complete these semantic migrations.

## Physical, foreign and compiler refinement boundaries

These are obligations for extending the logical specification, not assumed
Lean fields and not implemented operations. The current `Target` supplies only
pointer width; `Value`, `Environment` and `Step` do not model byte layouts,
allocators, foreign calls or compiler output.

- **Representation (§17.1–17.3):** a representation relation must connect a
  concrete target's allocations and bytes to the logical residents, storage
  identities, initialization and ownership state. Its target evidence must fix
  size/alignment, field offsets, array stride, enum layouts, endianness and ABI
  identity. Zero-sized residents retain distinct logical lifetime/ownership
  obligations. Equal byte size is not type equality. Reading or updating a
  shared VM/native object must use the same backing allocation, not a marshalled
  copy. No such relation is proved by `EnvironmentTyped` today.
- **Allocation and exhaustion (§18):** the concrete transition must identify
  the requested size, alignment and allocation domain. Success establishes
  freshness, valid storage and its representation; exhaustion must describe
  failure of that same request. Failure of a typing, permission, cleanup or
  simulation proof is not allocator exhaustion. Release must use the matching
  domain and preserve unrelated residents. Logical recursion currently makes
  no claim about concrete stack/memory exhaustion.
- **Foreign calls (§16):** capability admission, configured symbol resolution,
  C representation and semantic permission are separate requirements. A host
  contract may describe actual external reads/writes, ownership transfer and
  return validity; it must not supply whole-source preservation or future
  execution success. Synchronous callback loans end with the dynamic call;
  retained callbacks require a live registration owner. Re-entry must observe
  current shared storage and preserve unique access. Arbitrary foreign unwind,
  label transfer and capture/replay of foreign stacks are not admitted. A C
  callback entry bridge is not a bytecode program counter.
- **Compiler simulation (§19):** each implemented representation needs entry
  correspondence and step simulation consuming the authoritative checked
  identities and contracts. Internal implementation steps may be unobservable,
  but an unbounded internal loop cannot stand in for required source progress.
  The relation must preserve observable ordering, results, ownership transfers,
  cleanup, faults and permitted external outcomes; any silent-step argument
  must separately justify progress. Physical exhaustion requires the actual
  allocation obligation above rather than an unconstrained exceptional exit.
  Closing this boundary also requires stating which source behaviors are
  observable and proving the concrete compiler transformations—not adding a
  universal simulation assumption to `Program.Checked`.

The current logical proof imports no compiler implementation or older formal
model. No placeholder foreign/allocator transition or vacuous refinement theorem
is introduced. These boundaries do not enlarge the theorem's admitted fragment.


## Recovered, verified baseline

At commit `2958fffc`, `Grounded.lean` was restored byte-for-byte from commit
`d182ea2a` ("Derive ordered pattern dispatch from structural coverage"), the
1,081-line early second-revision milestone. This historical baseline established
the independent Lean 4.33.1 project described below. Subsequent changes are
recorded separately; the active files are no longer a byte-identical restoration.
The package remains `languageSemantics`, with module/namespace `Grounded`.

Covered: target-bounded integer and Unicode scalar literals; immutable lexical
binding and sequencing; tuples, fixed arrays and projections; decoded aliases
and structural constants; finite-layout duplicable nominal data with visibility
checks; direct noncapturing calls with finite body-typing derivations; and
immediate ordered pattern application with structural coverage and usefulness.

The public theorem is `Grounded.correctness`:

```lean
HasType program home context expression type →
EnvironmentTyped program environment context →
∃ value, Evaluates program environment expression value ∧
  ValueHasType program value type ∧
  ∀ other, Evaluates program environment expression other → other = value
```

`Grounded.closed_correctness` discharges the entry environment using the empty
environment constructor. The general induction constructs binding and parameter
environments and invokes the same evaluation relation for constants, calls,
and selected pattern bodies. No executable-realization, future evaluation,
successful cleanup, or run-level progress premise is supplied.

Premise-producer map:

| Premise | Meaning and producer | Actual consumer |
| --- | --- | --- |
| `HasType` | Ordinary rules check decoded syntax, declarations, visibility, bounds and permitted duplicable operations. Calls include a finite derivation for their declared body. | `correctness` inducts on these rules and their list/arm derivations. |
| `EnvironmentTyped` | Legitimate current values agree with lexical types. Empty entry constructs it; binding, parameter zipping and pattern binding preserve it. | Lookup and recursive body correctness. |
| `Covers` | Structural constructor-space coverage, not an evaluation-success certificate. | `Covers.selectArm` constructs selection after argument evaluation. |
| `PatternType` | Static constructor/field typing, access and legal duplicable disposal. | `PatternType.bindings` derives the selected body's typed environment. |
| `Useful` | A typed datum distinguishes a clause from preceding clauses; it does not assert evaluation of the subject. | `ArmsType.clause` admits only useful clauses. |

This is a logical terminating AST-to-value theorem, not whole-language
soundness, a source parser/typechecker implementation, or machine progress.
Inductive body typing does not admit general recursive calls. Immutable values
model no mutable storage, loans, captures, physical allocation, exhaustion,
nonlocal control or custom destructors. No later reference/admission machinery
was restored. The old pending/view defects below are constraints on future
extensions, not defects asserted to exist in this recovered fragment.

Verification performed in `formal/semantics`:

- `cmp Grounded.lean <(git show d182ea2a:formal/grounded-spec/Grounded.lean)`
  passed: exact historical source, not a reconstructed approximation.
- `lake build` passed with `autoImplicit=false` and `warningAsError=true`
  configured in `lakefile.toml`.
- A strict Lean defining-module audit checked all 1,135 declarations, including
  28 private declarations and generated declarations. The only transitive
  axioms were `propext` and `Quot.sound`. The public correctness, closed
  correctness, coverage-selection and pattern-binding results were also
  inspected individually. No concrete examples or unit tests were added.

The recovered proof is the first semantic checkpoint here. It supplies a
connected base to extend, not permission to replay the later development's
assumed bridges or to treat its finite terminating subset as the full language.

## Structural constant-pattern boundary

At checkpoint `9f29766c`, the development separated core semantics from source
pattern normalization while preserving the original public theorem signature.
The subsequent stateful cutover below gives execution and lexical preservation
their own modules and strengthens that signature. There remains one evaluator
and no copied admission framework.

Normative scope: §4.3 structural constant patterns, composed with §§6.1–6.4
ordered pattern application. Normalized constants retain their resolved declared type
and compare complete structural values without invoking user-defined Eq.
Nominal identity, constructor tags, scalar kinds and aggregate shape participate
in equality. The existing coverage-selection and binding theorems now handle
literal patterns, and the general correctness induction consumes them.

The new public theorem is `SourceArmsChecked.correctness`:

- Inputs: source patterns with ordinary closed constant typing; typed arguments;
  a nonempty source arm list; ordinary coverage, usefulness, pattern and body
  checking of the **computed normalized list**; a typed current environment.
- Conclusions: normalization of that source list; uniqueness of the entire
  normalized list, including declared type tags; actual evaluation of its
  application; result typing; uniqueness of the evaluation result.
- No successful evaluation or normalization is supplied. Static checking of the
  normalized patterns remains explicit: normalization alone does not establish
  exhaustiveness, usefulness, visibility, or body typing.

| Fact | Producer | Consumer |
| --- | --- | --- |
| Constant value | Existing `closed_correctness`, from ordinary constant typing | Certified `SourcePattern.Checked.normalize` result |
| Unique constant type and value | `ResolvesType.unique` and existing evaluation uniqueness | `NormalizesPattern.unique`, then `NormalizesArms.unique` |
| Ordered normalized patterns and unchanged bodies | Certified `SourceArmsChecked.normalize` result | Ordinary `Covers` / `ArmsType`, then `SourceArmsChecked.correctness` |
| Actual selected-body execution | `Covers.selectArm`, `PatternType.bindings`, general correctness | The source application theorem |

Normalization uses standard `Classical.choice` to extract a value whose
existence is already proved; its uniqueness is proved independently of choice.
This is a semantic definition, not an implemented normalization algorithm.
Source patterns are elaborated for an application whose arguments and bodies
remain decoded core. No parser or complete recursive source elaborator is
claimed. Stateful and whole-language obligations remain open.

Verification: `lake build` passed with strict configured options. A strict
Lean audit inspected every declaration defined by both modules, including
private/generated declarations (1,428 total, 64 private). Only `propext`,
`Quot.sound` and standard `Classical.choice` occur transitively. Core
correctness, coverage selection, pattern binding and normalization uniqueness
still require only `propext` and `Quot.sound`; the chosen normalization
product and its public consumer additionally use `Classical.choice`.
No `sorry`, custom axiom, unit test or concrete-example evidence was introduced.


## Destination contract

The full-language goal remains a faithful semantic specification and a proved
language/compiler correctness contract before compiler implementation. The
following are design obligations, not asserted Lean propositions or axioms:

- Start from ordinary source checking and explicit, legitimate current-state
  and external-interface evidence. Construct the execution correspondence;
  do not require a separately supplied executable realization.
- Prove preservation through actual transitions and progress at the appropriate
  machine boundary. Do not assume progress over all runs as source admission.
- Preserve the chosen elaboration/checking products and evaluation order. Keep
  the checking of alternatives distinct from runtime execution of the selected
  alternative; use the actual matcher, including preceding failures.
- Preserve resource ownership, provenance, lifetime, initialization, and
  control obligations across the outcomes where they apply. Distinguish normal
  return, nonlocal transfer, cancellation/cleanup, resource exhaustion, fatal
  abort, and divergence. A terminating big-step theorem is not a substitute
  for a correctness contract covering recursion and divergence.
- State the obligations of compiler transformations and foreign/runtime
  interfaces explicitly. Do not label an abstract language theorem as physical
  allocation, ABI, or compiler correctness.

Before extending the recovered fragment, refine the destination into precise
public theorem signatures and a premise-producer map for the next coherent
boundary. Record unsupported constructs explicitly; partial coverage is not
approval to reduce the full-language goal.

## Required design boundary before stateful extensions

Resolve these interacting questions together before extending the baseline with
mutable storage, resource-bearing references, or their execution contracts:

1. **Pending resources and initialization holes.** Separate resource
   correspondence and ownership from current readiness. Determine exactly when
   use, passing, transfer, and cleanup require restoration under language
   sections 5.2, 5.3, and 7.5. The old global `StateTyped.heldReady` requirement
   may reject a legal temporarily suspended pending ancestor; that path is a
   suspected defect, not a proved counterexample. Establish the actual producer
   path and the normative obligation before choosing the invariant. Neither
   blanket overlap rejection nor weakened restoration guarantees is a repair.
2. **Canonical target resolution and dormant declarations.** Use authoritative
   loan/storage resolution. Raw target lookup or a missing cached cell is not
   proof that a reference is dormant. Settle how unexecuted declared reference
   inputs are checked without inventing runtime storage or unjustified
   separation between potentially aliased references. Audit any proposal to
   introduce fresh symbolic roots against that aliasing requirement.
3. **Selected branch products.** Construct concrete source products for the
   actually selected branch while retaining the original checked alternatives,
   coverage, and priority. Do not demand incompatible concrete constructor
   evidence for every alternative, or silently select a different checking
   derivation to make realization possible.
4. **Entry and produced values.** Canonical entry must derive the current-state
   correspondence it promises from actual backing storage and resources.
   Untouched opaque pending carriers must not acquire an unjustified nominal
   typing requirement. Produced results and invocation arguments need their
   actual typed interpretation and freshness evidence from their producers.

For each decision record: normative requirement, exact contract, premise
producer, preservation consumers, and what discharges it at public entry.
Existing `Context.Resolves`, custody proofs, operation producers, and import
proofs are reference candidates, not predetermined interfaces to preserve.

## Implementation and composition discipline

Implement the settled boundary as a connected vertical slice:

1. Define the authoritative semantic relation and its legitimate entry facts.
2. Prove each real operation constructs its outcome, preserving the appropriate
   structural invariants and establishing the readiness required by consumers.
3. Compose sequencing, arguments/captures, selected branches, and ordered
   cleanup through those contracts. Transport freshness and interpretation
   through the complete sequence, not merely each local step.
4. Close the general preservation/progress or correctness result for the stated
   boundary and connect its public entry consumers.

Extend the recovered connected source through modules with actual semantic
responsibilities, rather than growing another monolith or creating a generic
framework in advance. Source organization changes must preserve the existing
public result. Reused proofs need audited hypotheses and real consumers; no
extra evaluator, resource walker, compatibility layer, or callback may stand in
for a missing proof.

The older `checked_correctness.realized` premise, run-level `ResourceAdmissionAt`,
eager executable arm evidence, and raw-target opaque-view discriminator must not
be copied into the new development as convenient admission assumptions.

## Checkpoint and continuation record

At each meaningful checkpoint update this document with:

- The exact covered semantic boundary and public theorem symbols.
- Each remaining premise, its producer, and its actual discharge site.
- Assumptions removed and guarantees established by connected consumers.
- Strict Lean command/results and transitive axiom inspection for the affected
  public results; no implication that successful checking validates the model.
- Suspected defects distinguished from proved obstructions, conditional
  theorems distinguished from discharged guarantees, and unsupported features.
- The exact next obligation on the same dependency chain.

Current next obligation: move/initialization-state transitions under §§5.3 and
7.5. Define one flow-sensitive checking/current-storage contract which permits
holes, rejects unavailable reads, and proves legal restoration and scope exit.
The current all-initialized context cannot simply be retained with an assumed
post-state. Preserve projected write/readback and framing while migrating the
general theorem and source entry consumers together.

Whole-language completion additionally requires an explicit normative coverage
and consumer audit. Features absent from this new folder remain unproved,
including recursion/divergence, general callables/captures, effects and handlers,
nonlocal control, replay/cancellation, generics/traits, full lifetime and custom
Drop checking, physical allocation/exhaustion, unsafe operations, and
foreign/ABI/compiler composition. This list is not an exhaustive coverage audit.

## Verified mutable lexical storage boundary

Covered: §5.2 evaluation order and §5.3 mutable binding/whole-local assignment,
within the existing duplicable, fully initialized, reference-free fragment.
The one evaluator returns an actual final lexical store. Ordinary `HasType` plus
current `EnvironmentTyped` now imply evaluation, typed result and final store,
immutable-cell framing, and uniqueness of both value and final store.
No successor-state, frame-preservation or successful-write premise is supplied.

- `BindingType` records declared type and mutability. Assignment is a statement
  with a continuation, evaluates its RHS first, and replaces only the nearest
  lexical binding. Checking requires that binding to be mutable and its old
  resident duplicable/discardable. Projected assignment and initialization-hole
  restoration remain separate, unimplemented language cases, not implicit rules.
- Sequencing, aggregate constituents and argument lists thread the actual
  intermediate store left-to-right. Scope exit removes precisely the introduced
  prefix; it must not restore an obsolete snapshot of outer values. Named calls
  evaluate arguments in caller storage, then use a separate parameter store.
- Immediate contextual clauses use the actual selected arm after argument
  evaluation. Pattern bindings are immutable and local to that arm. This is not
  a specification of independently materialized/escaping capture environments.
- The four stateful questions above are resolved for this cutover as follows:
  there are no reference/loan carriers or holes in the admitted syntax; no
  dormant references, invented referent roots or separation claims are added;
  only the selected branch executes; entry supplies actual typed resident values,
  and every intermediate/result value comes from the same correctness induction.
  These facts do not solve the later resource-bearing versions of the questions.
- Constant normalization consumes closed execution ending in the empty store.
  Source application correctness exports the actual typed/framed successor
  store and uniqueness; it does not erase the new state contract.

Producer/consumer chain: static destination lookup and current store typing
construct `replaceBinding` success; its preservation proof feeds continuation
correctness; typed scope-prefix removal feeds enclosing correctness; the closed
and source-pattern entry theorems consume the same general result.


Verified public result in `Grounded/Execution.lean`:

`HasType` and current `EnvironmentTyped` construct evaluation, result typing,
final-store typing, `EnvironmentFrame context before after`, and uniqueness of
both result and final store. The frame preserves every immutable resident,
including shadowed slots, and the lexical slot/name structure. It is composed
through the actual RHS, write, continuation and selected-branch transitions;
it is not an entry assumption. `closed_correctness` derives the empty final
store. `SourceArmsChecked.correctness` exports the same typed/framed successor.

Module ownership: `Core` holds decoded syntax, static checking and coverage;
`Lexical` holds the one replacement operation and its typing/framing producer;
`Execution` holds the one evaluator and general correctness induction;
`SourcePatterns` holds normalization and source application. The old stateless
evaluation signature and replacement proof were removed, not retained as shims.
The historical state-threading proof was reused only after removing its obsolete
normalization callbacks; immutable-cell framing is proved in the new pipeline.

Verification: strict `lake build` passed. The all-defining-module axiom audit
covered all four modules (1,490 declarations, 72 private/generated-private).
Only `propext`, `Quot.sound`, and the normalization product's existing standard
`Classical.choice` occur. General/closed stateful correctness use only
`propext` and `Quot.sound`; write preservation uses `propext`; frame composition
uses no axioms. No concrete examples, unit tests or admitted proofs were added.

## Verified projected storage boundary

Covered §§4.2 and 5.3 with one `ProjectionType` relation and one runtime field
selector for tuple and visible nominal-struct fields. Enum payloads are not
numeric places. `PathType` and rooted `PlaceType` compose that relation; these
are shared by place reads and writes. Rvalue projection uses the same
single-field producer rather than separate tuple/nominal rules.

The whole-local-only read/write constructors were replaced, not supplemented.
A place read requires the selected type to be duplicable, not a copied enclosing
aggregate. Assignment requires a mutable root and legal disposal of the selected
old resident. The RHS executes first; field resolution/update then consumes its
actual successor store. Recursive updates preserve siblings, outer constructor
identity and declared field types. The operation producer derives read/write
success and updated typing; general correctness and immutable framing consume
that producer. No references, unchecked enum projection, overloaded indexing,
or initialization holes are introduced by this extension.



Verified consumers: `ProjectionType.access` constructs selection and typed
replacement with exact readback. `PathType.read` and `PathType.write` compose
it through arbitrary finite field paths. `writeFields_siblings` proves that
actual nested writes preserve siblings at each selected prefix. Rooted
`EnvironmentTyped.writePlace` constructs the updated store, typing, immutable
frame and exact place readback. `Grounded.correctness` consumes these producers
for both reads and assignment; `SourceArmsChecked.correctness` retains the full
successor-store contract. No successful access/update is supplied to checking.

The old whole-local read and separate nominal-field expression/rules were
removed. `Expr.read` uses a rooted `Place`; whole-local access is its empty
field path. Rvalue tuple and nominal projection use one `Expr.project`,
`ProjectionType`, and `Value.projectField`. `Grounded/Places.lean` owns the
shared runtime access/update producers; no compatibility constructors remain.

Strict `lake build` passed. The exhaustive defining-module audit now covers
all five modules (1,580 declarations, 86 private/generated-private). Field/path
access, rooted updates and sibling preservation depend only on `propext`.
General and closed correctness still use only `propext` and `Quot.sound`;
standard `Classical.choice` remains confined to extraction of the previously
proved constant normal form and its source consumer. No tests, examples,
custom axioms, assumed execution bridges or unfinished proof declarations were
introduced. This remains a fully initialized logical-storage fragment, not a
proof of move/hole, borrowing, cleanup, machine or whole-language correctness.


## Certified normalization reduction

Pattern, pattern-list and arm-list normalization now return a subtype containing
both the normalized value and its existing normalization proof. Consumers use
`.val` and `.property`; the three separate recursive `normalizes` traversals
were removed without compatibility wrappers. The normalization relations and
their uniqueness proofs are unchanged. Choice still extracts only already-proved
constant values; no new admission premise or axiom was introduced.

`SourceArmsChecked.correctness` consumes the certified arm list directly and
retains actual execution, result/store typing, immutable framing and uniqueness
of both result and successor store. Strict `lake build` passed. A general
stdin proof checked equality with every result satisfying the original
normalization relation and transported the complete public execution guarantee
to that result. The exhaustive module audit checked 1,579 declarations; only
`propext`, `Quot.sound` and `Classical.choice` occur. The removed traversal
names are absent from the loaded environment. No test or proof scaffold remains.

`SourcePatterns.lean` decreased from 199 to 188 lines; the six Lean files total
1,751 lines, down from 1,762 (including comments and blank lines). The optional
preservation-record wrapper was not added: it would introduce constructors and
transport methods without removing the existing case-proof structure. Semantic
coverage and the next move/initialization-state obligation are unchanged.

