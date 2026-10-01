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
project is introduced by this reset. All work must be performed by the lead
assistant, serially, without subagents or delegated proof/implementation lanes.
See the durable serial-work-only rule in `AGENTS.md`.

## Current proved contract and ownership

General source safety is defined in `Grounded/Soundness.lean`:

```lean
program.Checked →
HasType program home before expression type final →
BindingMap.Typed program environment.heap environment.activation environment.bindings before →
environment.supply.Issued environment.activation →
Run program ⟨environment, .expression expression, []⟩ state →
ConfigurationTyped program final (.one type) state ∧
  (Terminal state ∨ ∃ next, Step program state next) ∧
  AddressedEnvironment.ConsumptionFrame program final.slots environment state.outerEnvironment ∧
  (state.environment.bindings.map Prod.fst).Nodup
```

Call sites check declaration signatures, not callee bodies. `Program.Checked`
checks each declaration body against its interface. It contains no termination,
future-state readiness or execution-success premise. Recursive calls are therefore
admitted without finite expansion of their bodies. Preservation obtains body
checking from the selected declaration at invocation entry.

`NamedProgramAdmitted.soundness` derives this core contract from named
direct-function declarations and recursively elaborated named expressions,
including named pattern clauses. `Program.Checked` is a proved intermediate
product, not a supplied execution guarantee. Callable imports use seeded least
candidate closure, visibility, explicit-over-glob priority and unique selection.
`SourceClosure.Admitted.function_soundness` now derives the declaring modules
and owners from supplied roots and explicit module inclusion, constructs fresh
function entry and proves general body-prefix safety. File permutation preserves
actual admission. Callable lookup and imports now require explicit package
dependencies, with checked normalized names and collision rejection. Textual
paths/groups, other namespaces, prelude profiles and the remaining source
frontend are still open.

`HasType.evaluation_soundness` proves declared result typing, exact output-mask
realization, issued activation and consumption-only immutable framing for every
completed execution, including recursive executions. `correctness` constructs a unique completed
execution when supplied `FiniteCalls program expression`: accessibility of the
static subexpression/call-body dependency relation. This is an optional
termination criterion, not part of ordinary admission or prefix safety.

Structural constants terminate directly from their checking derivation through
`constant_correctness`, independently of `Program.Checked` and `FiniteCalls`.
Certified source-pattern normalization consumes this theorem. Its public safety
consumer exports the complete prefix contract above; its terminating correctness
consumer separately requires finite call expansion.

The admitted logical fragment supports initialized and partially consumed storage,
named moves, restoration, mutable lexical storage, projected access and recursive
declared functions over one shared heap with generative activation identities.
Disposal and construction still carry duplicability restrictions; principal
ownership, destruction, loans and physical memory remain open.



| Module | Authoritative responsibility |
| --- | --- |
| `Model` | Decoded vocabulary, declarations and identity-indexed lookup/replacement; no checking/execution certificates |
| `Types` | Alias resolution, finite layout and duplicability |
| `Values` | Structural value equality, resident typing and indexed access |
| `Projections` | Shared field/path authority and value selection/replacement, independent of lexical storage |
| `Places` | Rooted lexical place contracts using the shared checked field path |
| `BindingStorage` | Addressed binding realization, actual allocation/activation entry, scope extension and retirement |
| `BindingAccess` | Resolved address reads, moves and restoration through shared path/heap operations |
| `Matching` | Runtime matching, subject interpretation and first-arm selection |
| `Patterns` | Pattern typing, coverage/usefulness and constructive binding/selection proofs |
| `Checking` | Expression, argument and arm admission |
| `Execution` | Explicit frames, single-step execution, finite runs and operational determinism |
| `Evaluation` | Terminating execution and composition derived from machine runs |
| `ConfigurationTyping` | Current-state/continuation realization, entry, preservation and progress |
| `Termination` | Structural constant termination and optional well-founded call expansion |
| `Soundness` | Prefix safety and the preserved terminating-fragment theorem |
| `SourcePatterns` | Certified constant normalization and its public source consumer |
| `Identifiers` | Total checked identifier decoding and exact ASCII lexeme grammar |
| `SourceLocals` | Named-local resolution, fresh lexical scope entry and source checking/safety consumers |
| `NamedPatterns` | Named pattern-binder allocation and exact matcher/body scope agreement |
| `SourceExpressions` | Recursive named-expression and clause elaboration into core admission |
| `FunctionResolution` | Named function syntax, seeded callable import closure, priority, visibility and unique selection |
| `SourceDeclarations` | Named direct-function interfaces/bodies, import admission and derived program safety |
| `SourceClosure` | Declaration-driven supplied-file inclusion, assigned module ownership and source-owned function safety |

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
The source-pattern interface takes already-resolved binder IDs. Lexical
freshness is now enforced as described below. Proving source resolution and
dynamic activation/storage identity remains necessary; an ID is not an address.
The logical environment still directly holds resident values, so this cutover
alone does not close the full identity/availability migration.

Verification: strict `lake build` passed (17 jobs). Transient general Lean proofs
established that any injective encoding of the former local keys preserves
actual lookup and replacement for every environment. These comparison functions
existed only in stdin. The defining-module audit covered 1,939 declarations and
found only `propext`, `Quot.sound` and `Classical.choice`.


## Verified lexical-identity freshness

`EnvironmentTyped.cons` now requires the new ID to be absent from the remaining
checked environment. `HasType.bind` produces this freshness obligation before
execution; the pending bind frame retains it until installation. Clause checking
requires uniqueness of the combined clause-local and outer context, not merely
uniqueness within the pattern. `ArmsType.selected` carries that exact evidence
with the actual selected body's typing and matching result. Invocation entry
consumes `FunctionChecked.distinct`, rather than reconstructing declarations.

The shared append, replacement, scope-drop and parameter-installation producers
preserve this stronger realization. `ConfigurationTyped.bindings_distinct`
extracts runtime uniqueness, and both public source-safety theorems now export
it for every reachable current environment. Source spelling shadowing requires
distinct resolved IDs; recursive callees may reuse their lexical IDs in their
separate invocation environments. This proves no globally fresh runtime address
or activation identity.

Strict `lake build` passed (17 jobs). The defining-module axiom audit covered
1,943 declarations, including private/generated declarations, with only the
standard `propext`, `Quot.sound` and `Classical.choice` dependencies. No
examples, unit tests, new axioms or assumed post-state distinctness were added.


## Verified named-local resolution boundary

`SourceLocals` owns source-local spelling resolution. `SourceScope` contains
source bindings and a fresh lexical-ID bound; its core checking context is
computed from those bindings rather than maintained as a second fact table.
`resolve_first` characterizes exact nearest-spelling selection, and
`resolve_missing` characterizes rejection of absent names. `enter` constructs
a fresh ID and the body's scope. The initializer is checked in the incoming
scope. `enter_preserves_selected` proves that introducing a shadowing spelling
cannot capture an already-resolved outer reference.

`resolvePlace` produces a core place with that exact ID. `place` proves its
static selection using the same core lookup; field authority remains the existing
`PathType` contract. The read, assignment and binding checking producers consume
these facts, including binding freshness derived from `enter`. Their public
soundness theorems derive realization, progress, immutable entry-store framing
and runtime binding uniqueness for every actual execution prefix. RHS order and
scope exit remain the existing machine transitions, not another source evaluator.

This checkpoint closed compositional named-local resolution for three operations.
The recursive named-expression admission below now supplies their nested core
checking derivations. Parsing, inference and pattern-binder allocation remain
open; `SourcePatterns` still receives resolved binder IDs. The allocation bound
establishes freshness relative to the source scope, not a globally fresh runtime
activation or storage address. Flow-sensitive moves/restoration remain open.

Verification: strict `lake build` passed (18 jobs). The defining-module audit
covered 2,011 declarations including private/generated declarations, permitting
only `propext`, `Quot.sound` and `Classical.choice`. All three named-local
soundness theorems depend only on `propext` and `Quot.sound`. A runtime-only
import check confirmed that `SourceScope`, `HasType` and `correctness` are
absent. No examples, unit tests, new axioms or temporary files were added.


## Verified recursive named-expression admission

`SourceExpressions` extends the existing named-local producers to recursively
nested expressions and ordered argument lists. `NamedExpr.Elaborates` records
source syntax, the selected core expression and its type. Its general
`checked` theorem derives `HasType`; callers no longer supply core typing for
each named expression's initializer, body, RHS or argument. Local resolution,
projection authority, annotation resolution and declaration signatures reuse
the existing producers. Closed constant declarations retain their existing core
checking contract; this is not source declaration elaboration.

The relation covers unit/integer/character literals, grouping, named reads,
sequencing, bindings, tuples, projections, arrays, constant references, nominal
construction, resolved direct calls and named assignment statements. Binding
initializers use the incoming scope; bodies use `SourceScope.enter`. Argument
lists preserve their exact order. The emitted core is executed by the one
existing machine; no source evaluator or alternate field analysis is introduced.

The public `soundness` theorem proves preservation, progress, immutable caller
framing and runtime binding uniqueness for every execution prefix, including
recursive calls. `evaluation_soundness` proves result and successor-store typing
for completed execution. `correctness` constructs unique completed execution
only under the separately supplied finite-call termination criterion.

This is a declarative elaboration relation, not a parser or executable inference
algorithm. It does not establish elaboration existence or uniqueness for arbitrary
source text. The named-pattern and direct-function checkpoint below closes those
source boundaries for this fragment. Dynamic activation/storage identity and
flow-sensitive moves/restoration remain open. Lexical IDs are fresh relative
to the active scope, not globally unique across disjoint scopes.

Verification: strict `lake build` passed (19 jobs). An axiom-closure audit of
2,060 declarations in the `Grounded` namespace permitted only `propext`,
`Quot.sound` and `Classical.choice`. The four new expression checking/safety/
correctness theorems depend only on `propext` and `Quot.sound`. No concrete
examples or unit tests were added or run.


## Verified named patterns and direct-function declarations

`NamedPatterns` allocates lexical IDs for explicit named binders, recursively
through structural patterns. Constant patterns reuse
`SourcePattern.Checked.normalize`; no second evaluator is introduced. Its
`checked` theorem proves both core pattern typing and the exact equality
between the emitted match-binding context plus incoming context and the body's
source scope. `fresh` derives ID distinctness from scope allocation.

`NamedExpr.applyPatterns` and `NamedArmsElaborate` now elaborate named arguments,
patterns and clause bodies together. Duplicate binder spellings are rejected.
Every clause starts from the same incoming scope, so bindings cannot leak to
siblings. Core coverage and usefulness consume the emitted patterns; the real
first-match execution and selected-body preservation remain the existing proof
chain. Tail-first static ID allocation preserves the matcher's head-before-tail
binding order; it does not reorder runtime argument evaluation.

`SourceDeclarations` elaborates named direct-function parameters, result
annotations and bodies. Omitted results mean unit, not an inferred arbitrary
result. Duplicate parameter and qualified function names are rejected. Parameter
IDs are allocated through `SourceScope.enter`, and parameter order is retained
in the runtime invocation signature. Named calls resolve through
`functionNames`, computed from the source declaration list; no parallel runtime
name table is installed. `NamedFunctionsAdmitted.resolves` proves that this name
lookup selects the exact emitted source declaration, including forward and
mutually recursive references.

`NamedFunctionsAdmitted` requires every runtime function to be an elaborated
source declaration. It derives `Program.Checked` rather than storing it as an
assumption. Its public `soundness`, `evaluation_soundness` and `correctness`
theorems consume named expression elaboration and actual entry typing, deriving
prefix safety, completed-result safety and optional finite-call termination.
No successful run, successor readiness or assumed progress is source admission.

This closes explicit named pattern-binder allocation, immediate pattern-callable
expression elaboration and named direct-function admission for the existing
fragment. Parsing/import expansion, bare-identifier constant/constructor/binder
classification, source data/constant declaration elaboration, first-class
callables, dynamic activation/storage IDs, moves, holes and restoration remain
outside this checkpoint. Function names are qualified declaration keys; nominal
constructor/module identities and the alias/data/constant tables remain decoded
inputs. No whole-language soundness or completed storage migration is claimed.

Verification: strict `lake build` passed (21 jobs). The defining-module axiom
closure audit covered 2,376 declarations, including private/generated declarations,
and permitted only `propext`, `Quot.sound` and `Classical.choice`. The named
source proofs use those standard axioms; choice comes from the existing certified
constant normalizer. No examples or unit tests were added or run.


## Verified post-RHS assignment frame

`replaceBinding.lookup_other` preserves every different lexical root, including
mutable roots. `writePlace.lookup_other` and `writePlace.read_other` carry the
same guarantee through arbitrary destination projections and arbitrary observed
paths under another root. The actual machine consumer is
`Step.assignment_frame`, not an assumed write-success field in checking.

`SourceScope.shadow_assignment_preserves_outer` consumes that machine theorem
and the source scope's fresh-ID producer. Writing the newly resolved binding
cannot modify an already-resolved outer binding, even when their source spellings
are identical. The comparison is explicitly against the store after RHS
evaluation and immediately before the destination write; mutations performed by
the RHS are not incorrectly claimed to be absent or undone. Same-root disjoint
nested-path framing and move/restoration semantics remain separate obligations.

Strict `lake build` passed (18 jobs). The defining-module audit covered 2,016
declarations with only standard Lean axioms. Both the machine assignment-frame
and source-shadow assignment theorems depend on `propext` and `Quot.sound`.


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



## Addressed storage and shared-heap machine cutover

The following prerequisite checkpoints record the path to the integrated
machine theorem described at the end of this section. Earlier pending-cutover
statements in those checkpoints are superseded by that result, not by source
move admission, which remains open.

`Grounded/RuntimeHeap.lean` supplies the authoritative logical storage operations.
Storage identities are monotone and are distinct from
lexical binding identities. A retired cell is absent below the allocation
frontier; a live initialization hole must instead be represented inside a cell
payload. Writes cannot recreate a retired cell.

The strict proof gate checks general allocation, write, retirement, ordered
batch allocation and batch retirement. `allocate_scope_retire` constructs
retirement of a freshly allocated batch, proves exact restoration of every
preexisting heap observation, and retains the advanced identity frontier.
`Retired.history` proves that retirement survives every subsequent history
generated by actual heap operations. Batch-retirement existence follows from
current liveness and distinctness, not an assumed successful release.

These are supporting storage proofs, **not an integrated language-soundness
checkpoint**. The existing machine still stores lexical values directly;
`EnvironmentTyped` still describes fully initialized bindings. Activation
allocation, address-bearing frames, partial residents, flow-sensitive checking,
source consumers and their joint preservation/progress migration remain open.
No physical allocation/exhaustion, destructor permission or whole-language
soundness follows from logical heap retirement.

Verification: `lake build Grounded.RuntimeHeap` passed with the project strict
settings. A defining-namespace audit inspected 114 declarations, including
generated declarations, and found no axioms outside the permitted standard Lean
set. The scope-lifecycle theorem uses only `propext` and `Quot.sound`;
retirement-history and batch-retirement existence use only `propext`. No
examples or unit tests were used. The public source theorem is unchanged.


The resident layer in `Grounded/PartialStorage.lean` now distinguishes live
holes from retired storage and separates declared layout from availability.
`ValueHasType.finite` derives layout from resident typing; a storage cell
retains it after its resident moves out. Tuple and nominal partial residents
have a structural initialization description. General read construction and
read preservation connect that description to actual resident reconstruction.

`PartialFields` now composes the existing `ProjectionType` and `PathType`
through arbitrary-depth partial-resident selection and restoration. Declared
layout opens whole holes into absent fields without inventing resident values.
`PathType.restore_partial` constructs both the static initialization update
and the actual storage update, with typed reconstruction and exact readback.
`Initialization.write_select` proves restored availability directly from the
static transformation. Single-field replacement preserves every sibling's
partial resident, including its holes.

`StorageOperations` owns the path-based `takeStorage` and `restoreStorage`
operations. Their former root-only definitions and consumers were removed;
empty paths are the whole-owner case of the same operations. General progress
and preservation consume checked paths, current cell typing and, for moves,
current source-state readiness. They prove same-cell updates, preserved
activation/type, global resident typing and outside-cell framing.
`takeStorage.restore` composes an actual move and restoration at any field
depth: the static state changes to absent then present, a second intermediate
take fails, and no new identity is allocated. Retired storage rejects both
operations.

Core local bindings now carry their resolved `Ty`, rather than an optional
source `TypeExpr`. Named elaboration still checks annotations and emits this
type; `HasType.bind` checks the initializer against it. `Step.bind` carries
the same type into `Frame.bind`, and frame realization ties its incoming
value to that type. Source checking, evaluation composition, termination,
preservation/progress and named-declaration consumers were migrated together.
This supplies declared layout metadata for the pending cell-allocation
cutover; it does not yet allocate a runtime cell. Strict checking of
`Grounded.SourceDeclarations` and `Grounded.StorageOperations` passed
(23 jobs). The source closure audit inspected 2,265 `Grounded` declarations
and found only standard Lean axioms.

Pattern binders likewise retain their resolved type. Named pattern elaboration
produces it, and `PatternType.binder` requires that exact subject type. The
decoded constant-pattern normalization interface preserves both identity and
type; normalization uniqueness, coverage, matching realization and source
soundness continue to check. Runtime matching still returns lexical values;
it has not yet been migrated to cell allocation. Strict source-declaration
checking passed (19 jobs), and the source closure audit found only standard
Lean axioms.

The shared `ProjectionType`/`PathType` producer and value-level projection
proofs now live in `Projections`. Both `Places` and `PartialFields` consume
that producer. Removing the former `PartialFields → Places → Lexical`
dependency allows addressed lexical storage to consume `StorageOperations`
without an import cycle. No projection rules or guarantees changed; the
source-declaration and storage-operation closures check together (24 jobs).

`BindingStorage` now connects lexical IDs to allocated storage IDs. Its
realization records each cell’s activation, declared type and initialization
state; it stores no duplicate resident. Ordered input allocation constructs
that realization and preserves existing live bindings. Scope extension derives
address separation from allocation bounds and pre-state liveness. Invocation
entry advances the activation supply even for zero arguments. Scope retirement
constructs the actual release, proves permanent retirement, and preserves a
disjoint retained caller map. The shared lookup/replacement functions moved
from `Lexical` to `Model`; their old definitions were removed.
`BindingMap.Typed.exit_scope` also constructs prefix retirement and preserves
the surviving outer scope. It derives their address separation from current
realization, rather than requiring successful cleanup or supplying a retained
post-state. Its strict dependency check passed (11 jobs), and its axiom closure
contains only `propext` and `Quot.sound`.


`BindingAccess` consumes this realization and the existing `StorageOperations`
contracts. Checked paths and current availability construct resolved reads and
moves. Moves update both the resident and the static initialization state,
preserve the binding map, and reject an immediate second move. Restoration
updates the same cell and its checking state, with exact readback and framing
of all other addresses. These operations are storage mechanisms, not permission
to bypass language ownership or destruction.

The composed binding-access/source-declaration gate passed (26 jobs); subsequent
scope-extension checking passed its 11-job dependency closure. An axiom audit
of both closures inspected 2,826 declarations and found only standard Lean
axioms. The new allocation, scope-extension and access results use only
`propext` and `Quot.sound`. No examples or unit tests were added or run.

`prepareBindings` pairs arguments with the actual resolved declaration slots
and rejects arity mismatch. Its progress proof derives typed transient inputs
and exact declared-slot correspondence from argument typing and declared
parameter distinctness. `enterFunction` derives initialized storage states at
the allocation boundary and consumes those inputs through the same
activation/storage allocator. `NamedFunctionsAdmitted.enter` now derives
checked body admission and actual addressed entry from source admission,
including preservation of every previously realized caller map and derived
caller/callee address separation. Scope extension reuses this same separation
proof. This is a source-to-storage entry result, not body execution or machine
preservation.
Strict source-declaration checking passed (25 jobs); the full source closure
audit found only standard Lean axioms. No future execution or successful
allocation is a premise. Logical allocation still makes no physical-resource
exhaustion claim.

The actual `Step.callInputs` transition now consumes `prepareBindings` too;
its truncating `List.zip` implementation has been removed. Typed arguments
construct preparation for progress, and preservation uses the resulting
typed inputs. Evaluation composition and the finite-termination proof consume
the same preparation result. `Step.call_arity` proves for every raw call-entry
transition, independently of source admission, that parameter and argument
counts agree. The current value-bearing environment remains a projection of
these inputs until the addressed-machine cutover; it is not an allocated heap.
The 25-job source gate and full imported-declaration axiom audit passed after
this migration, including general preservation, progress and source soundness.

Pattern matching now produces `BindingInput` values too, retaining each
binder’s resolved slot instead of discarding its type during matching.
`PatternType.bindings` proves both `BindingInputsTyped` and exact agreement
with the checked local context. The first-match coverage theorem, actual
`Step.selectedPattern` transition, selected-body admission, scope preservation
and finite-evaluation proof consume the migrated product. Direct and pattern
invocations share `BindingInputsTyped.environment` for the current lexical
realization; the old local proof copy has been removed. The 25-job source
gate and imported-declaration axiom audit passed, including general
preservation/progress and named-source soundness/correctness. This preserves
allocation metadata end to end but does not yet allocate the expression
machine’s locals in the addressed heap.

Activation generativity is now explicit in the source-entry result:
`ActivationSupply.Issued` includes every ID below the persistent supply
frontier, including activations with no allocated cells. Actual entry produces
an ID not previously issued, records it as issued, preserves issuance of all
older IDs, and proves the new ID differs from each of them. This property
cannot be recovered from live heap cells alone. The 26-job source/storage
gate passed; the primitive supply proofs use no axioms and the composed entry
results use only standard Lean axioms. Propagation of that supply through the
expression machine and returns is still part of the required cutover below.

`Initialization.write_ready` proves that replacing a selected subtree with
initialized contents preserves whole-owner readiness when the owner was
already initialized. `BindingMap.restore.progress` consumes that result,
alongside its general partial-restoration contract. This supplies the
initialized-fragment preservation obligation needed by the machine cutover
without assuming a ready successor. The combined binding-access/source gate
passed (26 jobs), and the combined axiom audit found only standard Lean axioms.

Addressed entry now returns an `AddressedEnvironment` with named activation,
supply, binding-map and shared-heap fields instead of a nested tuple.
`enterBindings`, `enterFunction` and the source-admitted entry theorem have
all migrated to this product. `AddressedScope` retains only the activation
and binding map, never a heap snapshot or saved supply.

`AddressedEnvironment.restore` retires the current bindings in the current
heap and installs the retained scope, preserving the current activation
supply and heap frontier. Its general progress proof constructs actual
retirement and caller realization from current cell typing. Separation is
derived from different activation identities and the cells’ unique recorded
owners, not assumed as an unrelated disjointness certificate. The combined
26-job source/access proof gate and full imported-declaration axiom audit
passed. This is the addressed return mechanism; `Execution.Frame.restore`
still uses the older lexical representation and must be migrated below.

The addressed environment also has lexical `extend` and `exitScope` operations
using the existing allocator and retirement operations. Extension preserves
every existing realized map without advancing the activation supply. Exit
constructs retirement, preserves surviving local bindings and every retained
scope owned by a different activation, and leaves both supplies unchanged.
The actual pending `Frame.bind` now retains the complete `BindingType`,
including mutability; frame typing and evaluation composition consume it.
The combined 26-job proof gate and imported-declaration axiom audit passed.
The addressed lexical operations still await the expression-machine cutover;
their proofs do not substitute for its general preservation theorem.

`AddressedEnvironment.read`, `take` and `write` now consume the same binding
map/path operations. Their general progress proofs carry exact static
availability updates, preserve scope metadata and allocation supplies, and
derive retained-caller realization from the modified cell’s actual owner.
Moves reject an immediate second take; writes establish exact readback and
preserve whole-owner readiness when it held before. No independent alias
analysis or post-state readiness premise is used. The combined 26-job gate
and imported-declaration axiom audit passed. These access mechanisms remain
to be connected to expression stepping and its continuation realization.

`AddressedScope.Realizes` specializes authoritative partial-cell typing to
the initialized source fragment: masks are ready and their declared slots
project to the source context. It stores no second resident representation.
`AddressedEnvironment.Realizes` also requires the current activation to have
been issued. Named source admission now constructs this realization at
entry, replacing the raw initialized-mask typing output.

General checked-path reads derive selected readiness from whole-owner
readiness and execute the actual addressed read. Checked writes preserve
the same source context despite changing the internal mask shape, using
exact slot projection and readiness preservation through `replaceBinding`.
They also preserve retained callers, supplies and readback. The 26-job
source gate and imported-declaration axiom audit passed. These results
prepare the initialized-fragment machine migration; they do not establish
flow-sensitive move admission or replace the outstanding machine proof.

Initialized source realization now also survives actual addressed scope
extension, scope exit and caller restoration. Extension uses the existing
typed input product and preserves every pre-existing realized scope. Exit
derives the dropped source context, actual local retirement and retained
caller realization. Restoration requires an already-issued distinct caller
activation and reconstructs its source realization in the current heap,
without restoring a saved supply. The 26-job source gate and full imported
axiom audit passed. These scope results close the initialized realization
operations, not their outstanding expression-machine integration.

Addressed assignment now also has immutable-observation framing. Actual
distinct storage identities establish that differently rooted reads survive
a write; differing lexical names alone are not treated as physical
separation. `AddressedEnvironment.Frames` relates scope identities and every
read rooted in an immutable source binding, without storing snapshots.
The constructive initialized write theorem consumes the source slot’s
mutability permission and returns this framing result alongside readback
and preserved realization. The 26-job source gate and imported-declaration
axiom audit passed. Replacement of the lexical machine’s framing relation
and continuation consumers remains part of the same cutover below.

Selected pattern-body admission now returns authoritative `BindingInputsTyped`
and exact slot correspondence instead of discarding those facts into the
legacy value-environment projection. Existing machine preservation and
termination consumers project only at their current lexical boundary.
`ArmsType.enter` composes coverage, actual first selection, body admission
and addressed local allocation. It constructs initialized body realization
and preserves all retained scopes, without assuming selection or allocation
success and without advancing the activation supply for lexical locals.
The 26-job source gate and full imported-declaration axiom audit passed.
This closes the addressed pattern-entry contract, not body execution in
the still-unmigrated expression machine.

Ordinary input preparation now exposes the same typed-input and exact-slot
contract as pattern selection. Separate name and initialization-mask outputs
were removed from `prepareBindings.progress`; the addressed entry consumer
derives its initialization masks from those slots, while the current lexical
consumer directly projects the typed inputs. The 26-job source gate and
imported-declaration axiom audit passed after migrating both consumers.

Retained-caller contracts now preserve exact heap cells, not merely their
typing. Actual allocation, moves, writes, lexical exit and caller restoration
derive equality of every retained address lookup from allocation bounds,
ownership separation and the actual write/retirement operation. The same
equality establishes retained typing; it is not supplied as a future-state
premise. Scope exit also preserves all surviving local cells. Ordinary and
pattern source-entry consumers carry this stronger result.
`BindingMap.read.frame` transports every projected read through exact cell
framing, including failed reads. Source-facing restoration consumes it to
prove that every restored caller read equals its pre-restoration observation.
The 26-job source gate and imported-declaration axiom audit passed. This
closes retained-value framing for these addressed operations, but not the
expression-machine and continuation consumer cutover below.

Caller restoration additionally frames every retained scope whose activation
differs from the retiring activation, not just the immediate return target.
The proof derives all address separation from live-cell ownership and uses
the same actual retirement result for all callers. The source-realization
consumer carries exact cell equality and retained readiness for those deeper
callers. No assumption that deeper callers survive appears in the premise.
The 26-job source gate and imported-declaration axiom audit passed.

The shared-heap expression-machine cutover is now integrated. Runtime
`Environment` is the authoritative `AddressedEnvironment`: lexical IDs map
to storage IDs; the shared heap and activation supply are never saved inside
restoration frames. Those frames retain only caller activation IDs and maps.
`FrameTyped` and `ContinuationTyped` realize every retained caller in the
current heap, with strictly older activation identities at return boundaries.
Actual allocation, writes, scope retirement and return retirement preserve
these facts. General preservation, progress and arbitrary-run framing consume
the same invariant, including recursive calls and nested retained scopes.

`AddressedEnvironment.Frames` preserves exact immutable heap cells and scope
identity; preservation of all projected reads follows from that relation.
The source shadow-assignment theorem now derives address separation from
current realization instead of treating distinct lexical names as sufficient.
`HasType.executes` constructs finite-call execution through actual allocation
and retirement; caller restoration follows from the preserved continuation,
not an assumed successful cleanup. Its postconditions use general machine
preservation rather than a second preservation argument.

All named-source safety, evaluation and finite-call correctness consumers now
use this addressed realization. Structural constants produce one typed value
for every caller heap and supply, preserve the caller scope and heap, and run
through the same machine. Closed execution and constant normalization expose
the actual final environment because invocation advances the supply. The old
`Lexical` runtime, value-environment typing/framing and list-based place
read/write operations have been removed, not retained as compatibility paths.

The complete source-consumer gate passed (25 jobs). An imported-declaration
axiom audit checked 2,936 `Grounded` declarations and found only `propext`,
`Quot.sound` and `Classical.choice`. The general machine preservation,
progress and framing proofs and finite-call construction use only `propext`
and `Quot.sound`. No unit tests or concrete examples were added or run.

The addressed source-realization boundary now also constructs a complete
same-path move/restoration sequence. `AddressedEnvironment.Realizes.take_restore`
derives the moved value, an actual intermediate hole that rejects another take,
and actual restoration/readback of a typed replacement. It reconstructs final
source realization by composing the authoritative mask and binding-context
updates. It does not assume that the intermediate source context is initialized.
The same result preserves immutable cells, caller cells and caller typing across
both transitions; neither transition allocates or changes the activation supply.

The general same-path mask overwrite law and binding replacement laws are
consumed by this composition, including nested aggregate paths. Strict
`lake build Grounded.SourceDeclarations` passed (25 jobs). The imported-declaration
audit checked 2,942 `Grounded` declarations and found only standard Lean axioms;
the new composition uses only `propext` and `Quot.sound`. No examples or unit tests
were added or run. That checkpoint established storage-to-realization composition;
the source checking and continuation cutover is established below.


The flow-sensitive cutover is now integrated through named-source soundness.
`HasType`, `HasTypes` and `ArmsType` carry exact incoming/outgoing
`BindingState` contexts. Arguments, tuple fields, sequences, initializers and
pattern subjects thread those states in execution order. Assignment selects its
destination after RHS evaluation. Moves require readiness at the selected path
and replace that path's mask with absence; restoration writes presence through
the same path and binding-context operations.

`ConfigurationTyped` realizes the current partial storage, not the future
contexts predicted by pending continuations. Retained callers remain typed in
the current shared heap. General preservation and progress cover actual moves,
restoration, recursive calls, lexical exit and caller retirement. Terminal
results realize the exact output masks, including remaining holes.

Immutable bindings may be consumed, so unconditional cell equality is not a
valid general move-aware invariant. `ConsumptionFrame` preserves scope identity
and relates immutable cells only by reflexivity, actual path writes of holes,
and composition. It does not permit replacement residents or retirement of an
external immutable cell. Actual allocation, retirement and retained-caller
transitions preserve those cells exactly. `ConfigurationTyped.consumption_run`
derives this relation across every run. The older exact `Frames` relation remains
in storage-level results that genuinely preserve entire cells; it is not used
as an invalid general guarantee for moves.

Named expression elaboration now threads the same flow states, including named
moves and restoration. Name scopes agree with flow contexts on declarations;
no future readiness is assumed. Pattern-local masks are removed at scope exit,
and function bodies may finish with holes. `NamedFunctionsAdmitted.soundness`
and its completed-execution and finite-call consumers derive the migrated core
contract from actual named declarations. Structural constants still normalize
through the same machine independently of function-body checking.

Fresh source-only verification passed `lake build Grounded.SourceDeclarations`
(25 jobs). The imported-declaration audit checked 2,999 `Grounded` declarations
and found only standard Lean axioms. General preservation, progress,
consumption framing and finite-call execution use only `propext` and
`Quot.sound`; source constant normalization additionally uses
`Classical.choice`. No unit tests or concrete examples were added or run.

Remaining boundary: principal ownership and destruction must replace the
fragment's duplicability-based disposal restrictions through the same checking,
execution and source-admission chain. Logical allocation remains unbounded.
Loans, destruction hooks, nonlocal cleanup, physical exhaustion, foreign runtime
correctness and whole-language soundness remain open.



Verification: strict `lake build Grounded.StorageOperations` passed. The
all-defining-module audit of `RuntimeHeap`, `PartialStorage`,
`PartialFields` and `StorageOperations` inspected 516 declarations and found
only standard Lean axioms. The path, heap-progress/preservation and composed
move/restoration results use `propext` and `Quot.sound`. An import audit
confirmed absence of `HasType`, `correctness` and `SourceScope` from the
storage runtime closure. No examples or unit tests were added or run.



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
| `HasType` | Ordinary rules check decoded syntax, declarations, visibility, bounds and permitted duplicable operations. Calls check the declared signature; `Program.Checked` separately supplies body checking. | Configuration preservation and source soundness; finite-call evidence separately supports termination. |
| `EnvironmentTyped` | Legitimate current values agree with lexical types. Empty entry constructs it; binding, prepared invocation inputs and pattern binding preserve it. | Lookup and recursive body correctness. |
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


## Verified lexical shadowing at direct calls

The named-call elaboration rule previously selected the global function table
even when the same spelling resolved to a lexical value binding. A general
Lean proof reproduced that admission for arbitrary scopes, argument lists,
and matching global declarations. This violated the lexical precedence rule
in normative §2.3; argument and result types cannot select a hidden function.

For unqualified calls, `NamedExpr.Elaborates.call` requires absence from the
authoritative `SourceScope.resolve` lookup before selecting a global function.
`call_not_shadowed` proves this for every admitted unqualified direct call. The
existing recursive named-expression checking theorem and named-function
soundness/correctness consumers use the repaired rule; no alternate resolver
or runtime name lookup was added. The new premise is an incoming lexical
lookup result, not an execution-success or future-state assumption.

Strict `lake build Grounded.SourceDeclarations` passed (25 jobs). A general
stdin proof established that any matching lexical binding excludes every
direct-global-call elaboration, independently of argument and result types.
The repaired rule theorem and public named-source soundness/correctness
axiom inspections contain only standard Lean axioms. No concrete examples
or unit tests were added or run.

This repairs shadowing in the currently admitted direct-call fragment. Local
callable invocation remains unsupported rather than falling back to a hidden
global declaration. Complete source closure, qualified path/import resolution,
namespace separation, lexical decoding and the full callable semantics remain
open. The whole-language completion task is not discharged by this repair.


## Verified module-qualified direct-function resolution

Direct function names are no longer flattened string keys.
`FunctionName` distinguishes unqualified spellings from a spelling qualified
by a resolved `Module`. Unqualified lookup selects the caller's module and
requires absence from its lexical scope. Qualified lookup selects the explicit
module and is independent of lexical shadowing; both forms still check the
visibility of the actual selected runtime declaration.

`functionNames` now resolves the pair (declaring module, spelling). Source
admission rejects duplicate pairs, not matching spellings in unrelated modules
or packages. Function bodies, recursive calls, named patterns, declaration
elaboration and all public source safety/correctness consumers use this same
module-indexed producer. The superseded flat callable lookup is removed.

`NamedFunctionsAdmitted.call_resolution` connects every admitted source call
to its emitted runtime call, selected declaration, exact requested module and
visibility evidence. It derives module identity from source declaration
elaboration and list-position selection, not from an assumed correspondence.
General named-source preservation, progress and finite-call correctness remain
proved over the unchanged addressed machine.

Fresh source-only `lake build Grounded.SourceDeclarations` passed (25 jobs).
The complete imported `Grounded` axiom audit covered 3,034 declarations and
found only standard Lean axioms. General stdin proofs checked qualified-call
admission in arbitrary lexical scopes and rejection of shadowed unqualified
calls. No concrete examples or unit tests were added or run.

The qualifier currently contains an already-resolved module identity. Package
source closure, textual path decoding, import/prelude fixed points and other
namespaces remain unproved. Constants and type aliases retain their separate
decoded textual interfaces. This checkpoint does not establish source-text
resolution or whole-language soundness.



## Verified decoded callable import closure

`FunctionResolution` is the authoritative producer for decoded callable
imports. Its inductive `FunctionCandidate` relation is seeded by actual source
declarations and closed under accessible explicit/alias and glob import edges.
`FunctionCandidate.least` proves leastness against every relation closed under
those same rules. Cycles cannot invent a declaration identity; unseeded cycles
cannot resolve. Multiple paths to one identity are not an ambiguity.

Explicit source bindings suppress glob candidates, including when an explicit
import is unresolved. Lookup selects only a unique visible declaration identity;
distinct surviving candidates are rejected rather than ordered by traversal,
argument types or expected result. `functionNames` is a noncomputable semantic
selector over the proved candidate relation, not an executable resolver algorithm.
No arbitrary import-result table is supplied to source program admission.

`FunctionImportsValid` checks the supplied module set, declaration/import
membership, resolution of every explicit target, and absence of visible identity
conflicts. These are static name-admission conditions, not runtime-progress or
future-state assumptions. The module set is still driver/decoded source input;
its derivation from package source closure remains open. General import-set
congruence proves that reordering or repeating edges preserves lookup, import
validity and the actual `NamedFunctionsAdmitted` program.

All named expression/declaration consumers now use caller-sensitive import
resolution. `call_resolution` follows aliases to the original emitted declaration
and retains its original module and visibility. The earlier equality between the
lookup module and declaration module is correctly superseded: an alias need not
be declared in the original module. `import_call_soundness` constructs name
selection from a visible candidate and static admission, constructs the source
call, then proves the general preservation/progress and consumption-framing
contract for every actual execution prefix. Qualified calls cannot bypass an
import binding's visibility or the original declaration's invocation visibility.

Fresh source-only `lake build Grounded.SourceDeclarations` passed (26 jobs).
The full imported audit covered 3,113 `Grounded` declarations with only standard
Lean axioms. Leastness, cycle/ambiguity rejection, import-order admission,
source/runtime identity and imported-call soundness received explicit axiom
inspection. No unit tests, concrete examples, new axioms or proof placeholders
were added. Existing general named-source and finite-call consumers also check.

This is decoded callable import semantics, not completed source closure or all
namespace resolution. Textual paths/groups, package acquisition/normalization,
prelude profiles and their priority, non-callable namespaces, lexical decoding,
and the rest of the whole-language obligations remain open. No full-language
completion claim follows from this checkpoint.



## Verified checked identifier boundary

`Identifiers` owns the executable ASCII character classifier and total
`Identifier.decode` producer for the identifier lexemes of normative §3.1.
`identifierLexeme_grammar` proves exact equivalence with the nonempty
`[A-Za-z_][A-Za-z0-9_]*` grammar and exclusion of the standalone wildcard
`_`. Decoder proofs characterize both successful exact-spelling selection
and rejection. Character classification is not delegated to Unicode alphabetic
predicates, locale, or another source consumer.

The checked `Identifier` product replaces arbitrary strings in source-local
bindings and uses, named pattern binders, parameters, direct-function names,
qualified/unqualified callable spellings and explicit import aliases. Scope
entry, shadowing, duplicate-name checks, seeded import resolution and named
source admission all consume the same representation. No unchecked string
coercion or compatibility lookup remains on these migrated paths. Core binding
and declaration identities and the runtime machine are unchanged.

Fresh source-only `lake build Grounded.SourceDeclarations` passed (27 jobs).
The full imported audit covered 3,150 `Grounded` declarations with only
standard Lean axioms. Decoder acceptance/rejection, exact grammar equivalence,
imported-call soundness and named finite-call correctness received explicit
axiom inspection. No unit tests or concrete examples were added or run.

This closes identifier-lexeme admission on the listed source paths, not byte
lexing or parsing. UTF-8 validation, token boundaries/comments, keyword roles,
spans, other literal forms and source package/module closure remain open.
Constants, type aliases and field keys retain decoded textual interfaces;
they have not been represented as fully validated source tokens. The broader
lexical and whole-language completion tasks remain incomplete.



## Verified declaration-driven module inclusion

`SourceClosure` derives included modules from driver-selected package roots
and explicit inline/external module declarations over finite supplied decoded
file collections. External children select exactly
`D/child/child.glorious`; both external and inline children advance the
logical directory to `D/child`. An inline child retains its containing file
identity. Roots use their selected file without the child filename rule.
There is no filesystem I/O, directory enumeration, or implicit sibling rule.

Module paths now contain checked identifier components, rather than arbitrary
numeric path segments. `FunctionSyntax` and `FunctionImportSyntax` do not
contain a declaring home. Inclusion assigns their home from the module tree;
the resulting `NamedFunction` and `FunctionImport` products feed the existing
resolver and declaration elaborator. There is no alternate callable analysis.
The public `Grounded` import now includes this source-closure boundary.

General proofs establish:

- Uniqueness of loading and of the entire `SourceClosure` product for fixed
  supplied packages. Duplicate file keys are rejected; root and child file
  selection cannot choose competing bodies.
- Preservation of package identity and provenance in an actually supplied file.
- Invariance of the exact loaded modules and actual program admission under
  arbitrary within-package file permutations. File position does not establish
  private authority or change declaration identity.
- Every selected runtime function elaborates from a function in an included
  module, with the declaring owner assigned by inclusion.
- `SourceClosure.Admitted.function_soundness` consumes that inclusion-derived
  owner and supplied-file provenance, constructs fresh addressed function entry,
  preserves existing caller cells at entry, and proves preservation, progress,
  consumption framing and binding distinctness for every actual body execution
  prefix. It assumes neither completed execution nor future-state readiness.

Fresh source-only `lake build Grounded` passed (30 jobs). The imported audit
covered 3,353 `Grounded` declarations with only standard Lean axioms. Closure
uniqueness, file-order admission equivalence, file provenance and both public
closure soundness theorems received explicit axiom inspection. No unit tests,
concrete examples, custom axioms or proof placeholders were added.

This closes declaration-driven inclusion of decoded module/function syntax,
not the full source frontend. Package identities and qualified import targets
are still decoded inputs. Explicit dependency authorization, normalized package
names/collisions, textual path/group resolution, prelude profiles, other
namespaces, parsing/UTF-8 and preservation of original byte spans remain open.
Nominal declarations, aliases and constants retain their earlier decoded
interfaces. The overall source-closure task and whole-language soundness are
not complete.



## Verified explicit callable dependency authority

Each supplied package now declares its dependencies by manifest name and target
package identity. `PackageDependency.name` normalizes hyphens to underscores
and invokes the shared checked identifier decoder. Admission rejects failed
decoding, duplicate normalized names and targets absent from the supplied
package collection. General proofs establish normalized-name uniqueness and
construct exact dependency lookup from each valid manifest binding.

`SourceClosure.functionNames` guards the existing seeded callable resolver
with the caller's own explicit package bindings. Every imported edge is checked
against the same authorization relation. All function bodies are elaborated
with that guarded resolver. Supplying a package or depending on one of its
dependents is no longer sufficient authority for direct lookup into it.
`SourceClosure.call_dependency` proves that every elaborated cross-package
call namespace has a normalized binding in the caller's actual manifest.

`dependency_call_soundness` constructs dependency lookup, unique callable
selection and source call elaboration from a valid manifest binding and visible
candidate, then proves preservation, progress and consumption framing through
the actual emitted call. Authorization applies to the lookup namespace, not
the ultimate declaration owner: valid re-exports retain their original runtime
identity and visibility without requiring an extra direct dependency on that
ultimate owner. `call_resolution` proves the resulting identity/owner contract.

The obsolete `NamedFunctionsAdmitted` wrapper is removed. Its shared body and
exact-emission contract is now `NamedProgramAdmitted`; the closure is the
source-admission boundary that produces its resolver. Existing general safety,
completed-evaluation, finite-call correctness and entry guarantees are retained
through that shared contract. Public closure correctness and identity theorems
consume the authorized resolver. File-order-independent admission still holds.
No compatibility alias or parallel body analysis remains.

Fresh source-only `lake build Grounded` passed (30 jobs) after the full cutover.
The imported audit covered 3,390 `Grounded` declarations with only standard
Lean axioms. Direct-dependency necessity, dependency-derived call soundness,
function-body soundness, identity preservation, finite-call correctness and
file-permutation admission equivalence received explicit axiom inspection.
No unit tests, concrete examples, custom axioms or proof placeholders were added.

This establishes explicit dependency authorization for the modeled callable
namespace, including normalized dependency-name validation. Module qualifiers
and import targets are still decoded identities, not textual paths. Other
namespaces still require their source-resolution cutovers. Textual paths/groups,
module-binding visibility along paths, prelude profiles, parsing/UTF-8, byte
spans and the other whole-language obligations remain open. No full-language
completion claim follows.

