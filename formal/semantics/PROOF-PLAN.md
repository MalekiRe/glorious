# Language semantics proof plan

## Authority and current status

This plan records the proved baseline in `formal/semantics/` and the newly
authorized semantic MIR ownership slice in `formal/mir/`, described below.
The requirements in [AGENTS.md](../../AGENTS.md) govern both.
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

## Active scope: ownership proofs only

New language-feature goals remain frozen. The admitted-core ownership safety
milestone below is complete. The user has now authorized a separate semantic
MIR ownership slice in a new directory, while preserving this existing core.
That authorization does not reopen the older whole-language feature roadmap
or imply that the new slice replaces the existing source development.

The current ownership baseline covers structural principals, partial
initialization, moves, replacement, authorized structural cleanup, recursive
direct calls, retained callers, and nonreturning execution. It does not claim
borrowing, custom destruction hooks, closure captures, effects, raw memory,
foreign calls, or backend refinement. Those feature goals remain frozen.

## Verified semantic MIR ownership slice

The user subsequently authorized a new proof in `formal/mir/`. That project
is the active architecture slice; `formal/semantics/` remains the preserved,
verified admitted-core baseline. Neither development inherits the other's
soundness claims. The frozen whole-language feature roadmap remains deferred.
Work remains serial, without delegated implementation lanes.

Atomic ownership commands lower through nonempty finite instruction blocks.
The current move/copy/dispose translations remain two operations each, but
simulation and reverse matching no longer depend on that length. Branches and
loops retain shared control proofs; aggregates are not a second execution or
ownership pipeline. The transfer register is part of the actual runtime state.

- `Tree.lean`: scalar data, opaque affine/exact resource identities, ordered
  products, nominal shells, and typed initialization holes. A live fieldless
  exact shell is not a hole. Shell deconstruction authority is independent of
  disposal permission; recursive capabilities include the shell and residents.
  The former value-carried `canOpen` flag is removed.
- `Nominal.lean`: one resolved declaration environment supplies nominal identity,
  principal restriction, ordered field layouts, and field visibility. Logical
  module ancestry and package identity determine private, exported, package, and
  parent access. `Layout.Declared` validates cached metadata, including holes;
  `Layout.Accessible` checks selected fields, while `Authority.CanOpen` requires
  authority over every field of an ownership-deconstructed shell. Whole-owner
  transfer remains independent of representation visibility. General private
  field exclusion proofs cover deconstruction and projection.
- `Metadata.lean`: the existing checked instruction producer preserves declared
  metadata through selection, hole installation, filling, copying, and dropping.
  `Op.Checked.deconstruction_authorized` derives declaration identity, restriction,
  payload layout, and lexical field authority for the value actually extracted
  by a physical transition. No permission Boolean or post-state validity premise
  supplies this conclusion.
- `Focus.lean`, `Places.lean`: one executable field focus/rebuild, constructive
  classification correspondence, and an additive ownership-frame equation.
  Whole slots use the empty path. Restoration requires vacancy and, for field
  holes, agreement with the recorded layout. No post-state readiness is assumed.
- `Model.lean`, `Instructions.lean`: exact runtime occupancy and constructive
  local progress/preservation proofs for take, put, copy, and drop. Constructive
  checking produces an `Op.Effect` witness of actual selection, extraction,
  replacement, and register contents. `Op.Checked.realize` and `.effect` expose
  full resident-level `Effect.Legal` evidence: take layout and deconstruction
  authority, put layout compatibility, copyability, and drop disposability plus
  exhaustion. The narrower `ConservationAllowed` predicate states only the
  conditions needed by resource conservation; legality derives it. The former
  ambiguous `Permitted` interface is removed, and shell consumers use this
  derived conservation evidence. Raw runtime execution remains unchanged;
  source admission now also requires lexical projection authority.
  Resource conservation, shell accounting, and raw retained-storage framing
  consume those witnesses rather than reconstructing execution independently.
  Raw execution does not consult ownership permissions. Checked drop releases
  only scalars or exhausted containers, not arbitrary remaining fields.
- `Blocks.lean`, `Machine.lean`, `Lowering.lean`, `Adequacy.lean`: finite-block
  execution and checking preservation, positive simulation, exact returned-state
  equivalence, and bidirectional correspondence of actual infinite executions.
  Reverse prefix matching carries a finite residual run to a source boundary,
  not a distinguished second instruction. Physical block steps consume a
  strictly decreasing pending-list rank; infinite internal block execution is
  impossible. Ordinary source moves still require actual initialization.
  Shared control now separates `InstructionProgress` (construct an execution)
  from `InstructionPreservation` (type and conserve an actual execution).
  `Safe.step` and `Safe.run` require preservation only; `Safe.progress` requires
  progress only. Block construction and divergence consumers explicitly take
  both. `Block.executed` transports preservation through an observed block;
  source-command preservation consumes it rather than constructing a second
  execution. Concrete proofs reuse the existing instruction effect producer.
- `ShellSafety.lean`: nonincrease of all noncopyable-shell occurrences and
  exact-shell accounting at every prefix. Any exact-shell decrease is counted
  from actual deconstruction steps. These are interpretations of actual
  residents and traces, not independently updated owner or discharge tables.
- `TreeFrame.lean`, `Cleanup.lean`: reusable proof contexts for the same
  executable focus; structural cleanup in reverse field order, followed by
  enclosing storage. Nested holes emit no operations. An empty root binding
  is retired. The general checker derivation feeds each actual residual
  context into the next step, and finite cleanup execution is derived.
- `Scope.lean`, `Framing.lean`: fixed-slot lexical ownership in acquisition
  order; cleanup reverses that order. `Scope.exit_iff` proves that the generated
  MIR returns exactly the independently defined atomic scope-exit state.
  `Scope.cleanup_frame` preserves actual retained/result slots at every MIR
  prefix, including transient transfer-register states. `Scope.program_safety`
  composes user code and scope exit into preservation, progress, resource
  uniqueness/conservation, and both shell bounds.

- `Execution.lean`: one finite `Run` and one `Diverges` definition over an
  arbitrary transition relation. Shared proofs provide composition, terminal
  inversion/uniqueness, deterministic prefix comparison, divergence transport
  and exclusion, and infinite-trace construction from reachable progress.
  This module imports no machine, typing, or ownership definitions and uses
  explicit hypotheses, not machine records or typeclasses. Local execution
  uses `Run (Step exec)`; activation execution uses `Run (Transition program)`.
  Both consumers migrate directly; the old activation `Execution` relation
  and duplicate divergence/sequence proofs are removed without aliases.
- `Trace.lean`: reusable ownership events, trace composition/comparison, and
  block observations depend only on `Blocks` and its machine prerequisites,
  not source lowering, scope cleanup, or framing. Concrete step determinism
  and inability to step from halt remain in `Machine.lean`; execution-sequence
  facts live in `Execution.lean`.
  `OwnershipTrace.terminal_unique` and `.prefix` derive from `.compare`, rather
  than repeat deterministic-step alignment. Command observations live with
  their translation in `Lowering.lean`; observational guarantees are unchanged.
- `CleanupTrace.lean`: scope-specific ordering and handoff consume those shared
  observations of successful MIR transitions, including separate detach and
  release actions. An independent structural specification visits newest roots first, fields right-to-left,
  and enclosing storage last; it reads the original occupancy, not successive
  generator contexts. Nested holes and absent roots have no events; occupied
  root holes still retire their binding. `Scope.cleanup_trace_iff` proves both
  exact endpoint and exact event order. `Scope.cleanup_observed_safety` combines
  preservation, progress, resource conservation/uniqueness, retained-storage
  framing, and ordered observations for every actual cleanup prefix, including
  pauses between detach and release. This is stronger than endpoint-only
  correctness; cleanup order is no longer justified only by generator syntax.
  `Scope.exit_trace_then` generalizes the boundary to arbitrary continuations;
  standalone cleanup is its halt instance. `Scope.cleanup_then_prefix` compares
  actual finite observations with the complete cleanup trace: either a residual
  cleanup trace reaches handoff, or the full cleanup trace precedes continuation
  observations. The alternatives need not be exclusive.
  `Scope.cleanup_then_return_iff` factors every normal return through handoff
  with an exact event split. `Scope.cleanup_then_diverges_iff` preserves and
  reflects actual infinite execution without requiring continuation admission
  or termination. `Scope.cleanup_then_safety` composes checked continuations
  at the cleared context; the standalone observed-safety theorem now consumes
  that contract. Retained-slot framing is not falsely extended past handoff:
  the continuation may subsequently modify those slots.

- `Store.lean`, `Calls.lean`, `CallSafety.lean`: source and MIR activations use
  one addressable region store and one transfer register. Continuation frames
  contain region identities and control, never saved copies of resident slots.
  Region creation appends a fresh identity; empty retirement leaves a tombstone
  and never reuses the identity. Local operations update their selected region
  in the same store. Entry transfers the prepared argument into fresh slot zero;
  checked result handoff installs directly into the actual caller region before
  callee cleanup. Retirement requires an empty region and empty register.
  `StackTyped` and `ResumeTyped` refer to actual store cells, with strict
  region ordering for retained callers. `activationScope` covers every slot.
  Program admission checks bodies, readiness, declarations, and structural
  residual disposability; it assumes no successful return or future run.
  Call-body preservation now instantiates the same shared `Safe.step` via
  `Instruction.Checked.executed`; the duplicate `Calls.local_step` branch/loop
  proof and the bundled `InstructionSound` interface are removed. Calls still
  advance through activation transitions, never a fictitious local execution.
- `CallOwnership.lean`, `CallShells.lean`: arbitrary additive tree measures
  agree across argument transfer and protected result handoff. Ownership and
  shell measures range over every live region of the physical store and its
  single transfer register, independently of the continuation stack. Joint
  uniqueness is not a collection of separate per-frame claims.
  `Calls.program_safety` derives preservation,
  progress, exact-resource conservation, affine bounds, noncopyable-shell
  bounds, and exact-shell discharge accounting at every actual finite prefix.
- `CallControl.lean`: concrete activation determinism and terminality feed
  shared execution proofs. Checked nontermination iff no terminal execution
  consumes shared infinite-trace construction; infinite-prefix safety consumes
  shared trace reachability.
- `CallCleanup.lean`: the existing ordered scope-cleanup trace discharges all
  activation slots before resumption. Every call-cleanup prefix is an actual
  local cleanup trace embedded into the same store, or has crossed empty
  retirement into the caller continuation. Cleanup preserves and reflects
  continuation divergence. Result installation frames caller roots outside
  its destination; region update laws preserve unrelated regions.
- `CallBoundary.lean`: appending retained control frames preserves actual
  transitions and executions without copying storage. `Safe.within_run`
  proves exterior-region framing for the current region-local instruction set.
  `Function.call_return` composes a real callee run in the actual ambient store
  with entry, constructively checked caller installation, ordered cleanup,
  and retirement; it no longer supplies a standalone copied callee store.
  `Function.call_diverges` propagates actual ambient-store divergence through
  entry. `Function.return_initialized` derives an initialized returned value.

- `SourceCalls.lean`: an independent resolved ownership source language extends
  atomic commands with recursive direct calls and result transfer. Source call
  entry acquires the argument from the actual caller region before allocating
  a fresh callee region, rather than assuming a prepared MIR register. Both
  source and MIR preserve the same store and region identities at boundaries;
  source cleanup executes atomic commands. Source checking
  requires initialized whole-value arguments/results, declaration agreement,
  valid result placement, and complete activation cleanup. It derives
  `Calls.Program.Checked` for the compiled program, without successful execution
  or return premises.
- `SourceCallLowering.lean`: every source transition produces a nonempty finite
  target execution. Argument transfer precedes actual call entry; commands and
  cleanup expand through the existing finite-block lowering. Retained source
  continuations and cleanup code are lowered along with the current control;
  the underlying resident storage is unchanged at corresponding boundaries.
- `Simulation.lean`: positive finite-step simulation and source progress reflect
  a terminal target run to an exact mapped source endpoint. Deterministic finite
  termination gives accessibility, which strictly descends across each positive
  source-step implementation. No assumed reverse simulation or eventual return
  to a source boundary is used. Actual infinite-trace equivalence additionally
  consumes progress at every target-reachable state, including internal steps.
- `SourceCallAdequacy.lean`: source-boundary progress is derived from checked
  finite prefixes. Its invariant is the existing activation invariant pulled
  back through lowering; its preservation follows actual forward simulation.
  Public source admission derives target-prefix ownership/conservation, both
  shell bounds, actual source progress, exact terminal-return correspondence,
  bidirectional divergence correspondence, and initialized returned residents.
  The existing MIR cleanup and call proofs remain the physical consumers.
- `CallMetadata.lean`: declaration validity covers every live region and the
  transfer register, including regions not named by the current control stack.
  It is preserved across transfer, handoff, cleanup, and retirement. Each
  program carries shared declarations;
  each function is checked in its own lexical module. Function admission checks
  input/output layouts and the cleanup context against those declarations. Both
  public source and compiled program-safety theorems now derive declaration-valid
  residents at every execution prefix, alongside the existing ownership and
  progress guarantees. Source-to-MIR lowering preserves the declaration
  environment and lexical modules.
- Generated cleanup is checked directly as MIR from its complete destruction
  plan, not by granting user source commands access to private fields. User
  move/copy/dispose projections and call argument/result places require lexical
  visibility. Internal MIR projection operations do not independently enforce
  source privacy; source checking is its authoritative producer.

Bounds: this is a resolved ownership source-to-MIR slice, not the full named
source language. Function identities, field paths, nominal metadata, and slot
acquisition order are resolved. A source call takes an already constructed
argument-tuple place by explicit whole move; duplicable arguments can be copied
by a preceding source command. Calls producing arguments execute in the source
control sequence, not as assumed-terminating argument evaluators. Name
resolution, arbitrary argument-expression/tuple elaboration, implicit
copy/reborrow selection remain outside these claims. Declaration-derived
authority and visibility are integrated for this resolved ownership slice.
Exact occupancy and branch agreement remain checking
precision policy; loops retain invariant contexts. No maybe-initialized
admission is added.

Each activation has the same arbitrary finite slot capacity, with slot indices
  in resolved acquisition order; the stack and region store are unbounded.
  Freshness and nonreuse are structural region-identity properties, not physical
  allocation or numerical-address theorems. Cleanup visits every callee slot;
  installed results remain outside the retired region.
The outermost activation is an explicit caller boundary: a terminal execution
returns its declared output context, including its residual region, rather than
silently destroying it. Heap allocation/exhaustion, physical addresses,
borrowing/lifetimes, custom destructors, effects, foreign execution, CFG/SSA,
and backend refinement remain outside this slice. Earlier compiler and Lean
code are preserved, not silently replaced or granted these claims.

Nominal declarations here contain finite instantiated structural field layouts.
Parsing, alias/name resolution, recursive type elaboration, enum/non-exhaustive
representation, and custom destruction are not modeled by this slice. The
declaration and module identities are already resolved; this does not claim
full language elaboration or hostile-bytecode admission.

Verification: after the unified-store migration, a fresh
`lake clean && lake build OwnershipMir` passed all 35 jobs with warnings as
errors and auto-implicit parameters disabled. Fourteen general theorem
dependencies were inspected: MIR preservation/progress, global ownership and
shell accounting, declaration validity, cleanup prefix/return, ambient-store
call return/divergence, positive source simulation, source progress, compiled
safety, exact terminal correspondence, and actual divergence equivalence.
Dependencies are limited to `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, new axioms, concrete examples, or unit tests bypass the obligations.
This verified checkpoint completes the store cutover, not borrowing:
reference values, permissions, reborrowing, dereference, and lifetime-aware
return/cleanup admission remain the next part of the requested integration.


### Joint storage ownership

Configuration.OwnershipSafe now includes Configuration.ExclusiveOwnership:
active bindings have distinct storage identities; each retained caller does
too; the active map is disjoint from every retained caller; and distinct
retained frame positions cannot share a storage identity. The proof derives
this from BindingMap.Typed, current-heap ownership, and the strict activation
ordering already required by actual restore frames. No new admission premise,
owner table, source analysis, or runtime transition was introduced.

HasType.allocated_unique_owner combines that invariant with actual allocation
tracking: every newly allocated cell still live at any checked execution
prefix has exactly one owning map, active or retained. This is storage-map
ownership, not a claim that structurally equal values denote the same resource.
The strengthened invariant is consumed by the existing general source
soundness and normal/infinite behavior theorems.

All 30 strict Lean jobs passed after integration. Inspected exclusivity, unique
owner, general/source soundness, noncopyable-read, exact-cleanup and replacement
safety proofs use only propext, Classical.choice and Quot.sound. These checks
establish the stated core contracts, not whole-language completion.

### Accepted milestone: safety of the currently admitted core

The user selected safety of the currently admitted core, not expansion of
source admission. Checking and elaboration remain unchanged. The static
operand-completion index and unreachable-continuation admission are explicitly
deferred alongside feature expansion, not completed and not prerequisites for
this bounded safety milestone. The checker can still reject valid programs.

The acceptance audit follows the existing general proofs, rather than adding
examples or a second ownership analysis:

| Guarantee | Existing proof |
|---|---|
| Preservation, progress and ownership at every reached prefix | `HasType.soundness` |
| Moves update physical residents and masks together; immediate retake fails | `BindingMap.take.progress` |
| No noncopyable read or nondiscardable direct discard | `HasType.no_noncopyable_read`, `HasType.no_nondiscardable_discard` |
| No exact resident scheduled for cleanup or erased by replacement | `HasType.no_exact_cleanup`, `HasType.no_exact_overwrite` |
| Nondiscardable descendants survive lexical/indexed retirement and cannot be overwritten | `HasType.scope_preserves_nondiscardable`, `HasType.retirement_preserves_nondiscardable`, `HasType.no_nondiscardable_overwrite` |
| Caller restoration preserves unconsumed exact descendants | `HasType.restore_preserves_exact` |
| Active/retained storage exclusivity and unique ownership of new live cells | `ConfigurationTyped.exclusive_ownership`, `HasType.allocated_unique_owner` |
| Normal scalar/pack completion retires temporary storage; infinite execution retains prefix safety | `Run.terminal_retires_all`, `HasType.behavior`, `HasTypes.behavior` |
| Bottom execution does not resume pending continuations | `HasType.never_continuation_prefix` |
| Named source admission consumes the same safety and behavior contracts | `SourceClosure.Admitted.soundness`, `SourceClosure.Admitted.behavior` |

These are conditional on checked declarations, elaboration/checking and a typed
initial store with an issued activation. They do not assume future readiness,
successful cleanup or termination. Structural values are not physical resource
identities; storage-map uniqueness is not an end-to-end resource-trace theorem
for the deferred raw-memory, borrowing or foreign-runtime features.

Final acceptance check: `lake build Grounded` passed all 30 jobs. The 18
theorems listed above were inspected with `#print axioms`; their dependencies
are only `propext`, `Classical.choice` and `Quot.sound`. No proof or admission
rule was changed for this scope clarification. This closes the selected
admitted-core ownership-safety milestone, not whole-language soundness or
admission completeness.

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
  (state.environment.bindings.map Prod.fst).Nodup ∧ state.OwnershipSafe program
```

Call sites check declaration signatures, not callee bodies. `Program.Checked`
checks nominal layout and manual-principal validity, alias expansion and layout,
structural constant declarations, function-interface layouts, and each function
body against its interface. It contains no termination,
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
dependencies, with checked normalized names and collision rejection, and
visibility-checked traversal through actual module bindings. Calls and callable
imports interpret decoded `self`/`crate`/`super`/dependency anchors through the same
producer, including nested callable import groups with complete namespace validation.
Selected callable preludes use the same producer and respect suppression flags.
Module aliases, other namespaces, library/runtime profile contracts and parsing remain open.

`HasType.evaluation_soundness` proves declared result typing, sound output-mask
realization, issued activation and consumption-only immutable framing for every
completed execution, including recursive executions. Source return contracts
preserve the returned resident's principal across every valid typing. General
maximal behavior constructs either a normal result with that unique principal
or an infinite execution retaining prefix safety. `Configuration.OwnershipSafe`
also classifies current results, argument packs, protected cleanup/installation
payloads and values retained in tuple/argument continuation frames through the
same finite resident evidence. Its recursive control invariant carries disposal
authority for active and protected cleanup queues before any saved queue resumes.
This is not a closure-capture or reference model.

`correctness` constructs a unique completed execution when supplied
`FiniteCalls program expression`: accessibility of the static subexpression/
call-body dependency relation. This is an optional termination criterion, not
part of ordinary admission or prefix safety.

Structural constants terminate directly from their checking derivation through
`constant_correctness`, independently of `Program.Checked` and `FiniteCalls`.
Certified source-pattern normalization consumes this theorem. Its public safety
consumer exports the complete prefix contract above; its terminating correctness
consumer separately requires finite call expansion.

The admitted logical fragment supports initialized and partially consumed storage,
named moves, restoration, mutable lexical storage, projected access and recursive
declared functions over one shared heap with generative activation identities.
Owned nominal construction does not require Copy. Copy and MayDiscard use one
structural permission producer. Final masks admit fully consumed exact owners
and field-sensitive residual cleanup, including conservative maybe-initialized
branch joins restricted to discardable uncertainty; manually exact shells
preserve consumed/live status without freezing affine descendant masks. Custom
destruction, relationally correlated branch states, loans and physical memory remain open.



| Module | Authoritative responsibility |
| --- | --- |
| `Model` | Decoded vocabulary, declarations and identity-indexed lookup/replacement; no checking/execution certificates |
| `Types` | Alias resolution, finite layout and shared Copy/MayDiscard derivation |
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

`StorageOperations` owns the address-based `StorageAddress.take` and `StorageAddress.restore`
operations. Their former root-only definitions and consumers were removed;
empty paths are the whole-owner case of the same operations. General progress
and preservation consume checked paths, current cell typing and, for moves,
current source-state readiness. They prove same-cell updates, preserved
activation/type, global resident typing and outside-cell framing.
`StorageAddress.take.restore` composes an actual move and restoration at any field
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



## Verified module-binding visibility for callable lookup

Decoded inline/external child declarations now retain their module-binding
visibility alongside the name and body. `ModuleReachable` traverses actual
included declarations from package roots, checking each child binding with the
existing `Visibility.Allows` relation at its declaring parent. A public
function does not itself expose a hidden containing module.

The authoritative closure resolver now requires both explicit package access
and a visibility-checked module traversal. Source import admission uses the
same traversal requirement. Dependency-derived call soundness, original
identity/owner preservation, general body safety and finite-call correctness
all consume the strengthened resolver. Re-export lookup still checks the
exporting namespace rather than inventing visibility for the original path.

`PackagesLoad.children_distinct` derives child-name uniqueness from actual
inclusion. `child_visibility` combines that fact with admitted module-owner
uniqueness to show that traversal cannot substitute another visibility for a
selected binding. `call_child_visibility` carries the result through actual
source call elaboration: caller access to the selected child must satisfy that
binding's declared visibility. No independent module-permission table is used.

Fresh source-only `lake build Grounded` passed (30 jobs). The imported audit
covered 3,416 `Grounded` declarations; only standard Lean axioms occur. Module
visibility, call-site visibility, dependency-derived call safety, function-body
soundness, finite-call correctness and file-order admission invariance received
explicit axiom inspection. No unit tests, examples or proof placeholders were
added.

This covers visibility traversal for the modeled callable namespace with
decoded module identities. Textual anchors/path parsing, module aliases/groups,
other namespaces, prelude profiles, frontend spans/UTF-8 and whole-language
completion remain open. Source parsing still has to supply omitted-visibility
defaults and reject invalid restricted-visibility syntax.



## Verified enclosing-module visibility for arbitrary descendant calls

`ModuleReachable.ancestor` proves accessibility of every enclosing module
from accessibility of a descendant. The public call theorem is strengthened
from an immediate-child equality to an arbitrary same-package path prefix:
`SourceClosure.Admitted.call_ancestor_visibility` derives each enclosing
binding's declared permission from actual source call elaboration. Deeper public
children cannot bypass a private or restricted ancestor. The superseded
`call_child_visibility` theorem is removed, not retained as an alias.

Strict `lake build Grounded` passed. The imported audit covered 3,417
`Grounded` declarations with only standard Lean axioms; ancestor accessibility,
the strengthened call theorem and general function soundness received explicit
axiom inspection. No examples or tests were added. Textual path elaboration and
the other previously recorded whole-language obligations remain open.


## Verified anchored source-call paths through general soundness

Qualified function names now carry decoded `ModulePath` syntax, not an arbitrary
pre-resolved `Module`. The shared interpreter handles `self`, `crate`, a
positive number of `super` steps, and a checked dependency spelling. Its result
is only a module identity: the existing package-access, declared-module
reachability and function-visibility checks still grant authority.

`resolvePackageDependency` first selects the caller's own manifest and uses
`PackageSource.resolveDependency`, preserving the existing normalized-name
producer. Source expressions and declaration bodies now use the same composed
`SourceClosure.functionNames` producer. `FunctionName.owner` and the
pre-resolved qualified-name constructor are removed; all expression, pattern-arm,
declaration, closure, identity, visibility and public safety/correctness consumers
use the migrated contract. The lower binding resolver remains the existing
seeded import closure, not a second name analysis.

General proofs establish exact parent-suffix removal and failure beyond the
package root. `call_super_depth` carries the bound through actual source call
elaboration; `call_namespace_missing` excludes fallback after failed namespace
interpretation. `call_dependency_spelling` derives the precise manifest spelling
and declared module reachability from an elaborated call, including dependencies
that target the caller's own package. Another alias of a package cannot stand in
for an absent spelling. `dependency_call_soundness` constructs lookup and call
elaboration from the actual manifest binding and static visible candidate, then
proves the existing general preservation/progress/framing contract. It does not
accept a completed resolver result or execution success as an admission premise.
File-order admission invariance, ancestor visibility, declaration identity,
function-body soundness and finite-call correctness remain proved.

Fresh source-only `lake build Grounded` passed (30 jobs). An exhaustive imported
audit checked 3,486 `Grounded` declarations, including private/generated ones;
only `propext`, `Quot.sound` and `Classical.choice` occur. The path laws and
public source consumers received explicit axiom inspection. No unit tests,
examples, new axioms or proof placeholders were added.

This closes interpretation of the modeled decoded call anchors, not byte-level
path parsing, module-alias/unanchored-name disambiguation, inherent namespaces,
or complete source resolution. Import targets still carry decoded module
identities and require their own cutover to the same path producer. Import
groups, other namespaces, preludes, UTF-8/spans and the previously tracked
ownership, effects, physical-memory and whole-language obligations remain open.


## Verified source-import paths through closure construction and soundness

`FunctionImportSyntax.target` now contains `ModulePath`, not a pre-resolved
module identity. `FunctionImportSyntax.resolve` invokes the same path interpreter
as calls and produces the resolved edge with its source owner, import kind and
visibility. `resolveFunctionImports` preserves failure and input position;
it never filters out an unresolved import. The superseded direct
`LoadedModule.imports` mapping is removed.

`SourceClosure` now owns the complete elaborated import product, certified by
equality with `elaborateModuleImports`. The executable `fromModules` constructor
produces that product or rejects it. `fromModules_complete` proves every such
closure is reconstructed by the constructor, and `fromModules_exists_iff`
proves its exact success criterion: every declared source import path has an
interpretation. This is finite source interpretation, not an assumed name-lookup
success, execution, progress or post-state invariant. Namespace existence,
module visibility, dependency validity, import ambiguity and body checking
remain separate requirements of `SourceClosure.Admitted`.

The bidirectional position proofs yield `import_source` (no omitted source
imports) and `import_origin` (no invented edges or changed owners/kinds/visibility).
`Admitted.source_import_access` derives dependency authorization and declared
module reachability for each source import from the actual admitted product.
The seeded least import resolver, recursive declaration admission, call identity,
general source/function safety and finite-call correctness consume these same
resolved edges. No second source walker or permission table was introduced.
Closure uniqueness and file-order admission invariance were migrated and proved.

Fresh source-only `lake build Grounded` passed (30 jobs). The exhaustive import
audit checked 3,513 `Grounded` declarations with only the standard Lean axioms
`propext`, `Quot.sound` and `Classical.choice`. Construction, source/edge
provenance, admitted import access, uniqueness, file-order invariance and the
public safety/correctness consumers received explicit axiom inspection. No
unit tests, examples, proof placeholders or additional axioms were added.

Calls and callable imports now share decoded anchor interpretation. Module
aliases and unanchored qualifier disambiguation, import groups, inherent/other
namespaces, preludes, byte parsing/UTF-8/spans, and the previously recorded
whole-language obligations remain open. This is not whole-language completion.


## Verified grouped callable imports through source soundness

`ImportSelection` models callable leaves, relative namespace descent and
arbitrarily nested groups. A single emission pass produces typed `ImportEntry`
values: either a namespace obligation or a resolved binding. Descent and group
nodes retain their namespace obligations even when a group is empty. Binding
leaves preserve the source import's owner, visibility and explicit/glob kind.

`ImportSelection.Emits` gives the source rules. `emit_sound` and
`Emits.complete` prove both directions between these rules and the actual
emitter, including nested group membership and relative path composition.
`SourceClosure` owns the complete per-statement entry batches. Its entry and
binding lists are projections of this product, not independently reconstructed
source facts. The old atomic source `kind` field is replaced by the selection
syntax; there is no parallel atomic-only import route.

Admission checks package authorization and declared-module reachability for
**every entry**, including namespace-only entries. The seeded callable resolver
consumes only binding entries. `import_source`, `import_origin` and
`import_emitted` connect the actual source rules to this same product;
`Admitted.source_import_entry_access` proves all emitted namespace obligations
hold, whether or not any subsequent call selects a leaf. An empty group cannot
hide an inaccessible or absent namespace. Unknown dependency anchors still fail
construction; other missing/inaccessible namespaces fail admission. Construction
success alone is not complete source admission.

The public call-identity theorem, general source/function soundness and finite-call
correctness consume the migrated product. Closure uniqueness, exact construction
criteria and file-order admission invariance remain proved. No future lookup,
execution, progress, cleanup or post-state invariant was added as a premise.

Fresh source-only `lake build Grounded` passed (30 jobs). Exhaustive imported
axiom inspection covered 3,631 `Grounded` declarations, including private and
generated declarations; only `propext`, `Quot.sound` and `Classical.choice`
occur. The source-rule equivalence, provenance, all-entry access, construction,
uniqueness, file-order invariance and public soundness/correctness theorems
received explicit axiom inspection. No unit tests, examples, additional axioms
or proof placeholders were added.

This covers decoded grouped **callable** imports, not module aliases, type/effect
family imports, inherent namespaces, unanchored qualifier disambiguation, preludes
or parsing. Those source boundaries and the previously tracked ownership,
effects, raw-memory, foreign/ABI and whole-language obligations remain open.


## Verified imported-call construction from finite source provenance

Explicit-import admission in `FunctionImportsValid` now requires finite,
declaration-seeded visible-candidate derivations, not a supplied successful
`functionNames` result. Namespace membership and global unique-identity
requirements are unchanged. The actual resolver derives its result from these
facts; unresolved cycles have no declaration seed, and conflicting candidates
still violate uniqueness. No second resolver or alternate import table exists.

`SourceClosure.Admitted.imported_call_soundness` consumes an actual import
statement in an included module and one of its source-rule-emitted explicit
bindings, including arbitrarily nested groups. It constructs a unique callable
identity and the actual admitted core declaration **before** quantifying over
arguments. Under namespace and binding access, selection of that identity is
equivalent to the original declaration being accessible to the caller. For an
authorized caller it constructs call elaboration and derives general configuration
typing, terminal-or-step progress, storage consumption framing and environment
binding uniqueness for every typed execution prefix. No successful callable
lookup, completed execution or future-state readiness is a premise.

The constructed declaration comes from the existing exact source-declaration
product. Visibility and dependency checks remain distinct: exposing a binding
does not erase the original declaration's visibility. Source-level lexical
shadowing remains checked before call elaboration. General source/function
soundness, finite-call correctness and file-order admission invariance consume
the migrated admission contract.

Fresh source-only `lake build Grounded` passed (30 jobs). Exhaustive imported
axiom inspection covered 3,635 `Grounded` declarations; only `propext`,
`Quot.sound` and `Classical.choice` occur. Explicit binding construction,
imported-call soundness, file-order invariance, function soundness and correctness
received explicit axiom inspection. No unit tests, concrete examples, proof
placeholders or additional axioms were added.

This closes the constructive explicit-import call boundary, not the outstanding
module aliases, other namespaces, preludes, parsing or whole-language obligations.


## Verified declaration-time visibility scope validation

`Visibility.ValidAt` reuses the authoritative access relation: a declared scope
must contain its declaring module. The general `validAt_iff` theorem establishes
exact acceptance: private, package and public scopes are valid at every owner;
a parent scope is valid exactly when the owner is not the parentless package
root. There is no separate visibility classifier with potentially different rules.

`SourceClosure.Admitted` now validates the scopes of every function declaration,
import statement and child-module binding in every included module, whether used
or not. Validation uses inclusion-derived module owners, not physical file names.
It is separate from namespace reachability and call-site access checking.
`root_visibility` proves rejection of parent-restricted declarations for all
three modeled source item kinds at roots. Empty import groups cannot evade this
check. No access attempt or successful execution is needed to detect an invalid
scope.

`declaration_visibility` transports validation through the exact emitted
source-function relation to actual runtime declarations. The general
`function_soundness` theorem now returns valid declaration scope alongside
source provenance, fresh function entry, preservation, progress and storage
framing. Imported-call soundness, finite-call correctness and file-order admission
invariance consume the migrated admission contract.

Fresh source-only `lake build Grounded` passed (30 jobs). Exhaustive imported
axiom inspection covered 3,647 declarations; only standard Lean axioms occur.
Exact visibility acceptance, root rejection, emitted declaration validity,
function soundness, imported-call soundness, correctness and file-order invariance
received explicit axiom inspection. No unit tests, examples, placeholders or
additional axioms were added.

This covers the function/import/module source forms currently modeled. Nominal
source declarations and field visibility elaboration, module aliases, other
namespaces, preludes, parsing and the remaining whole-language tasks remain open.


## Verified automatic callable prelude injection through source soundness

Each decoded `PackageSource` carries the driver-selected standard prelude path
and the decoded `noStd` / `noImplicitPrelude` controls. A single request
producer injects that prelude only when a profile supplies a path and neither
suppression flag is set. It generates a private automatic-prelude request, feeding
the same path elaborator, complete import batches, namespace admission, seeded
provenance relation and callable resolver as authored imports. The original
shared glob/prelude tier was superseded by the lowest-priority repair below;
no special runtime dispatch or spelling-based intrinsic authority is introduced.

`preludeRequest_selected` proves the exact enabling condition and generated
shape. `resolvePackagePrelude.origin` ties every automatic request to its
supplied owning package. `LoadedModule.importRequests_origin` distinguishes
authored imports from injected requests. `importRequests_suppressed` proves
that either suppression flag leaves **exactly** the authored import list: it
does not erase explicit imports or dependency declarations.

Source closure now constructs its complete import product from these requests.
The construction criterion includes automatic paths, and admission checks their
actual namespace accessibility. A missing dependency or inaccessible prelude
cannot silently become an empty prelude. The declaration visibility proof covers
both authored and automatically generated requests. General construction,
provenance, closure uniqueness and file-order admission invariance are migrated;
file permutation leaves the selected profile and suppression policy unchanged.

`SourceClosure.Admitted.prelude_call_soundness` constructs the actual selected
callee from the profile, emitted automatic edge and finite visible target
candidate, under explicit/glob shadowing exclusion and namespace-access checks.
It constructs selection before argument checking and proves configuration typing,
terminal-or-step progress, consumption framing and binding uniqueness for every
typed execution prefix. Lexical shadowing remains checked; original-declaration
visibility is derived from resolved provenance, not separately supplied. No
completed callable lookup, execution or post-state readiness is assumed.

Fresh source-only `lake build Grounded` passed (30 jobs). Exhaustive imported
axiom inspection covered 3,677 declarations; only standard Lean axioms occur.
Policy equivalence, exact suppression, source provenance, request visibility,
prelude-call soundness, file-order invariance and public function soundness and
correctness received explicit axiom inspection. No tests, examples, proof
placeholders or additional axioms were added.

This establishes decoded **callable prelude injection** and its suppression,
not the entire library profile contract. Hosted-library acquisition/selection,
intrinsic/runtime service admission, literal manifests, other namespace preludes,
attribute parsing, module aliases and the other whole-language tasks remain open.


## Verified inclusion-derived local namespace authority

Local namespace reachability is now derived from declaration-driven inclusion
and validated visibility scopes, not supplied to prelude-call soundness.
`Visibility.Allows.descendant` proves access is preserved for descendants in
the same package. `ModuleReachable.descendant_caller` carries that fact through
the actual module-binding traversal, without granting cross-package access.

A mutual proof over `ModuleSource.Loads` / `ModuleChildrenLoad` constructs
self-reachability through both inline and external module declarations. Each
child step uses the included parent's actual child binding and its validated
visibility. Package roots come from the supplied inclusion product; no independent
module table, guessed path or assumed successful resolver result is used.

`SourceClosure.Admitted.local_resolution` combines this constructive access
proof with inclusion-derived package provenance and the shared candidate resolver.
`prelude_call_soundness` consumes it directly: the former `homeReachable`
premise is removed. Original-declaration visibility is now derived from lookup;
argument, shadowing and execution-prefix guarantees remain unchanged.

Fresh source-only `lake build Grounded` passed (30 jobs). Exhaustive imported
axiom inspection covered 3,684 declarations; only standard Lean axioms occur.
Mutual inclusion access, local resolution, prelude-call soundness and public
function soundness/correctness received explicit axiom inspection. No tests,
examples, proof placeholders or additional axioms were added.

The previously listed module-alias, namespace, parsing, library/runtime and
whole-language obligations remain open.


## Verified owned nominal construction without a Copy requirement

The former `HasType.construct` rule implied `Duplicable` for every constructed
nominal type; a general inversion proof confirmed that restriction before the
change. Construction owns its already-evaluated fields and does not copy the
result. The restriction was not required by resident typing or the actual
constructor transition.

Removed the constructor-only Copy premise from source elaboration, Core checking
and constructor continuation typing. Migrated their consumers in general
preservation/progress, flow-slot preservation, structural constant execution and
finite-call execution. The actual constructor transition and its evaluation
order are unchanged. Layout, constructor selection, declared field types,
declaration visibility and field access remain required. Copy, projection,
assignment and disposal permissions were not relaxed.

The general source correctness theorem now applies to construction without a
Copy premise, including exact-restricted nominal types. A universally quantified
proof checked via Lean stdin constructed source elaboration and derived actual
finite execution, nominal result typing, exact output masks, immutable consumption
framing and result/state uniqueness. Separate general proofs confirmed that
reads still require Copy and exact-restricted nominal types cannot derive Copy.
These were proof checks, not concrete examples or unit tests; no temporary proof
files or duplicated permanent theorems were added.

Fresh source-only `lake build Grounded` passed (30 jobs). Exhaustive imported
axiom inspection covered 3,684 declarations; only standard Lean axioms occur.
General preservation, progress, execution and public source/function correctness
received explicit axiom inspection.

This corrects owned construction, not the remaining ownership/disposal boundary.
At this checkpoint local binding, parameter and pattern-binding cleanup still
imposed duplicability restrictions. The next checkpoint replaces that conflation;
residual exact-owner disposition and whole-language ownership soundness remain open.


## Verified shared Copy and MayDiscard authority

Replaced `Duplicable` with one indexed structural relation, `UsePermitted`,
producing either `.copy` or `.discard` evidence. There is no independent
second ownership walker or compatibility alias. Nominal restrictions and all
resident fields contribute to the same derivation: affine restrictions admit
discard but not Copy; exact restrictions admit neither. Empty arrays retain
their no-resident rule. The general `copy_discard` theorem proves the permission
implication structurally, including nominal fields.

Migrated every source/Core consumer: reads require Copy; sequencing, local
binding, projected-value residue, overwritten values, wildcard/literal patterns,
pattern-bound locals, function parameters, scope frames and caller restoration
require MayDiscard. The existing general preservation/progress and finite-call
execution proofs consume those contracts directly. No operational success,
post-state readiness or termination assumption was added to ordinary admission.
The fragment has no custom Drop hooks, references or raw owning representations;
this change does not claim their destruction semantics.

A general inversion proof verified the former sequence-discard Copy restriction
before changing it. Fresh source-only `lake build Grounded` passed (30 jobs).
A universally quantified Lean proof then derived named affine local binding,
actual execution through scope cleanup, the unit result, final storage typing,
issued activation and immutable consumption framing from the public source
correctness theorem. General negative proofs established that affine nominal
owners cannot acquire Copy and exact nominal owners cannot acquire MayDiscard.
These stdin proof checks used no concrete examples or unit tests.

Exhaustive imported axiom inspection covered 3,710 declarations; only standard
Lean axioms occur. General preservation, progress, source/function correctness,
finite execution and Copy-to-discard transport received explicit inspection.

At this checkpoint fully consumed exact locals and parameters were still rejected
by the type-wide scope restriction. The next checkpoint moves scope disposition
to final residual masks without granting discard permission to exact types.


## Verified residual scope disposition through public source soundness

Scope disposal now consumes the same final initialization masks produced by
flow checking. `Initialization.Disposable` admits a fully empty shell or an
ordinary MayDiscard type. `Initialization.Empty` covers nested empty masks;
`PartialValue.Typed.empty` proves that such a mask contains no actual resident.
This does not manufacture Copy or MayDiscard for an exact type.

Migrated lexical binders, function bodies/parameters, pattern-bound locals,
invocation continuations and scope continuations. Function signatures and
pattern binders no longer require type-wide disposal before their bodies run.
Instead, their bodies must statically establish disposition of every final
local state. Removed the obsolete parameter/binder disposal derivations.
Wildcard and literal-pattern disposal still require MayDiscard; reads still
require Copy. Moves retain their original definite-initialization requirements.

`BindingMap.Typed.disposable` connects static disposition to the actual cells
selected for retirement. `ConfigurationTyped.ownership_safe` proves that
before each lexical-scope or caller-restoration cleanup, every selected live
cell is empty or its type permits discard. This is now a conclusion of the
general prefix soundness theorem, propagated through named expressions, source
patterns, declarations, package/source closures and imported/prelude calls.
It is not an assumed successful cleanup or a supplied future runtime state.

Fresh source-only `lake build Grounded` passed (30 jobs). Universal Lean stdin
proofs established local whole-owner transfer followed by actual execution and
cleanup safety for every prefix, checked whole-owner parameter transfer for
arbitrary types, and rejected disposal of a still-present exact nominal owner.
The prior verified source freeze proved the old rule rejected every exact local
binding regardless of its body. No concrete examples or unit tests were added.
Exhaustive imported axiom inspection covered 3,739 declarations, with only
standard Lean axioms. The mask-to-resident bridge, selected-cell disposition,
cleanup safety and strengthened public source/function soundness received
explicit axiom inspection.

At this checkpoint mixed residual aggregates and assignment restoration remained
restricted. The next checkpoint corrects assignment restoration. Field-sensitive
residual permission, custom hooks and their order/divergence, conditional ownership,
loans, nonlocal exits and the other whole-language boundaries remain open.


## Verified residual restoration and actual overwritten-resident safety

Assignment now checks the destination's selected residual mask after RHS
execution, through the existing `Initialization.Disposable` authority. An empty
exact destination may be restored without granting MayDiscard or Copy to its
type. Replacing a still-present exact owner remains rejected. Mutability,
projection typing, definite availability for moves, and RHS-before-write order
are unchanged.

Migrated source assignment elaboration, lexical resolution, core checking,
assignment continuations, preservation, progress and finite execution. The
runtime restoration operation is unchanged. `BindingMap.Typed.replacement_safe`
uses `PathType.select_partial` to identify the actual selected old resident in
the same heap path that restoration overwrites, then proves it empty or legally
discardable. No independent path reconstruction or future-state premise occurs.

The public predicate is now `Configuration.OwnershipSafe`, with the general
`ConfigurationTyped.ownership_safe` proof covering both retirement and
replacement. All source, declaration, package-closure, imported-call and prelude
soundness consumers expose this strengthened conclusion. The previous
scope-only names were removed rather than retained as aliases.

Fresh source-only `lake build Grounded` passed (30 jobs). Universal Lean proofs
constructed a move/restore/move execution for arbitrary owner types and typed
input stores, deriving a correctly typed final absent slot and storage cleanup
safety for every execution prefix. A separate general proof rejected replacement
permission for every still-present exact nominal owner. Exhaustive imported
axiom inspection covered 3,741 declarations; only standard Lean axioms occurred.
No unit tests, concrete examples, new axioms or proof placeholders were added.

At this checkpoint mixed residual aggregates still required an empty-or-whole-type
rule. The following checkpoint adds field-sensitive residual disposition. Custom
destruction and ordering/divergence, correlated branch states, loans, nonlocal
cleanup and the other tracked semantic boundaries remain unproved.


## Verified field-sensitive residual disposition through general soundness

`Initialization.Disposable` is now the authoritative structural residual
judgment. It preserves empty-shell retirement and whole-type MayDiscard, and
additionally admits tuple and nominal residual fields individually. Moved-out
exact children need no discard permission; remaining residents still do.
Nominal rules retain the declaration's explicit principal restriction and check
constructor schemas rather than inferring permission from absent fields.

`Initialization.Disposable.realizes` derives `PartialValue.Disposable` for the
actual typed residual value. This latter relation interprets permission for
runtime residents; it does not reconstruct source flow or supply checking facts.
The existing binding-map retirement and selected-replacement consumers now use
this proof. Consequently the general preservation/progress and public
`OwnershipSafe` results cover mixed residual aggregates in the modeled
hook-free fragment, including source/function/package/import consumers.

`present_iff` proves that whole initialized values still require exactly their
ordinary MayDiscard evidence. Static and runtime `exact_nominal_empty` theorems
prove that an explicit exact nominal restriction admits only fully empty shells,
not partially consumed shells with remaining residents.

Fresh source-only `lake build Grounded` passed (30 jobs). General Lean proofs
constructed a checked mixed-owner local, moved its arbitrary first field out,
and derived actual terminating execution and cleanup safety for every prefix
when the initializer has finite call expansion. Only the remaining field
requires MayDiscard. A universally quantified struct-schema proof checked the
nominal residual rule. Exhaustive imported axiom inspection covered 3,788
declarations; only standard Lean axioms occurred. No concrete examples, unit
tests, additional axioms or proof placeholders were added.

This closes mixed residual disposition for the currently modeled tuple/struct
storage paths, not full ownership or language soundness. The following checkpoint
repairs rvalue projection permission. Custom hooks, destruction order/divergence,
correlated branch masks, loans, nonlocal exits and the remaining tracked boundaries
stay open. Unresolved constructor-dependent masks are not assumed compatible.


## Verified owned rvalue projection with residual cleanup

Rvalue projection no longer requires MayDiscard for the entire parent, which
incorrectly included the selected owner being transferred. Source elaboration,
core checking and projection continuations now consume the existing residual
mask obtained by clearing only the selected field. Only that remainder must
satisfy `Initialization.Disposable`. Field visibility and the shared
`ProjectionType` authority are unchanged.

`ProjectionType.cleanup_safe` constructs the actual typed selected value and
the remaining partial aggregate using the existing field operations. The
selected slot is proved absent from the remainder, whose resident disposition
is derived through `Initialization.Disposable.realizes`. This is an
interpretation of the discarded temporary value, not a new heap mutation or
source-flow analysis. Runtime projection and evaluation order are unchanged.

The general `OwnershipSafe` predicate now includes projection continuations.
Its proof and all public source/function/package soundness consumers therefore
cover projection remainder disposal in addition to scope retirement and
assignment replacement. Preservation, progress, structural normalization and
finite execution consume the migrated checking rules.

Fresh source-only `lake build Grounded` passed (30 jobs). General Lean proofs
admitted projection of an arbitrary selected owner without Copy or MayDiscard
for that owner, derived actual execution from finite source expansion, and
proved cleanup safety for every execution prefix. A general exclusion proof
rejected projection when its unselected sibling lacks MayDiscard. Exhaustive
imported axiom inspection covered 3,790 declarations; only standard Lean axioms
occurred. No concrete examples, unit tests, new axioms or placeholders were added.

Full language completion remains open. In particular, these proofs do not model
custom destruction hooks or establish ordered/diverging destruction, correlated
branch masks, loans, cancellation/nonlocal cleanup, physical allocation limits
or the remaining normative language and compiler obligations.


## Verified direct-discard safety for actual execution prefixes

The existing MayDiscard check on sequence results now feeds the shared runtime
cleanup predicate. `ConfigurationTyped.ownership_safe` proves disposal
permission for the actual value about to be discarded by `Step.sequenceResult`.
All existing public source/function soundness consumers inherit this conclusion;
source admission and execution rules are unchanged.

`PartialValue.Disposable.not_exact_resident` excludes every live nominal value
whose declaration has an explicit exact restriction, including zero-field
payloads. Such a value is not confused with an empty partial shell.
`HasType.no_exact_discard` consumes the general prefix soundness theorem to prove
that no checked execution reaches a direct discard of such a value. The result
requires neither termination nor a completed evaluation.

`lake build Grounded` passed (30 jobs). Explicit axiom inspection covered the
runtime exclusion, general reachable-state exclusion, preservation, progress and
public source soundness; exhaustive inspection covered 3,792 declarations with
only standard Lean axioms. No concrete examples, unit tests, new axioms or proof
placeholders were added. This is direct-discard safety in the modeled fragment,
not complete destruction semantics or whole-language soundness. The previously
recorded custom-hook, borrowing, nonlocal-control and other obligations remain.


## Verified exact-owner protection through actual retirement and overwrite events

`BindingMap.Disposable.release_preserves_exact` protects every cell containing
an unconsumed exact nominal descendant selected by a checked path. The descendant
may be partially initialized and unreadable. Shared residual permission descends
through that path; `PartialValue.Disposable.exact_nominal_empty` would require
complete structural absence if the cell were retired. This excludes the cell
from the release list, so the actual retirement producer preserves it unchanged.
The owner need not be in the current lexical environment.

`HasType.scope_preserves_exact` consumes constructive scope retirement after an
arbitrary checked execution prefix, preserving continuation typing and the
containing cell without requiring an observed cleanup step or readable owner.
`HasType.return_restores` constructs caller restoration from the reached return
frame, preserving the returned payload and continuation typing, retiring all
callee bindings and retaining caller cells exactly.
`HasType.restore_preserves_exact` consumes that producer: it constructs the
actual restoration and proves the containing cell is unchanged, rather than
requiring a completed return. `Step.unique` identifies any observed restoration
with the constructed transition. No termination or future readiness is assumed.

Verification of the generalized partial-owner contract: all 30 Lean build jobs
passed. Axiom inspection of the residual producer, retirement theorem, both
constructive consumers and maximal source behavior found only standard Lean
axioms. This does not add custom Drop or field-by-field destruction execution.

`HasType.no_exact_overwrite` now excludes every unconsumed exact descendant
beneath the destination immediately after RHS evaluation, even when that
descendant is partially consumed and unreadable. The runtime binding map, heap
lookup and nested checked selection identify the actual old owner. Shared
residual permission would force it to be structurally empty; its remaining
ownership contradicts that conclusion. A fully moved-out slot may still be
restored. Both the replacement producer and source-prefix consumer were migrated.
All 30 Lean build jobs and standard-axiom inspection of replacement exclusion,
the public source theorem and maximal source behavior passed after this change.

`lake build Grounded` passed (30 jobs). Exhaustive imported axiom inspection
covered 3,799 declarations with only standard Lean axioms. The actual release,
scope/caller retirement, overwrite and direct-discard theorems received explicit
axiom inspection. No concrete examples, unit tests, additional axioms or proof
placeholders were added. These results concern the modeled logical heap and
explicit exact nominal restrictions; they do not establish physical allocation,
custom hooks, borrowing, nonlocal cleanup or complete language soundness.


## Repaired zero-field ownership and representation-independent cleanup safety

A general constructor proof exposed a modeling error: the former vacuous
`Empty` predicate classified every zero-field partial nominal as consumed while
`PartialValue.read` still reconstructed its whole value. The runtime disposal
relation therefore admitted such shells without checking an exact restriction.
This was a defect in the emptiness contract, not evidence of language soundness.

`Initialization.Empty` and `PartialValue.Empty` now require consumed storage:
a field shell must have at least one field and every field must itself be empty.
A zero-field aggregate remains a whole owner; moving the whole owner still leaves
an ordinary hole. The typed mask-to-resident proof preserves actual list arity.
`PartialValue.Empty.read_none` proves for every partial representation that
emptiness excludes a successful read. This general theorem rules out the former
modeling error rather than special-casing an input program.

`PartialValue.Disposable.not_exact_read` proves exclusion for any representation
that reads as a live exact nominal, including reconstructed aggregate fields.
Actual release, source scope/caller retirement and overwrite theorems now consume
read observations rather than demanding a syntactic `.resident` wrapper.
The stronger contract has been migrated through its real consumers. Existing
whole-owner direct-discard protection remains a constituent proof case.

Fresh source-only `lake build Grounded` passed (30 jobs). General proof checking
established zero-field exact-owner exclusion and incompatibility of typed empty
storage with read readiness. Mixed residual transfer and owned projection proofs
still construct actual executions and prefix cleanup safety. Exhaustive imported
axiom inspection covered 3,804 declarations; only standard Lean axioms occurred.
The absence/read exclusion and strengthened actual retirement/overwrite results
received explicit axiom inspection. No unit tests, concrete example files,
additional axioms or proof placeholders were added.

Whole-language completion remains open. This fixes the hook-free logical
ownership boundary; it does not supply custom destructors, ordered/diverging
cleanup, borrowing, correlated control state, nonlocal cleanup, physical memory
or the other outstanding language/compiler semantics.


## General structural-principal preservation through retirement

`Initialization.Disposable.ready` now proves that a readable residual mask
can be disposable only when the original whole type permits discard. This is
not limited to explicit nominal restrictions: tuples, arrays and nominal
principals inherited from fields are covered. For nominal types the proof
recovers every declared constructor, so inactive variants cannot be ignored.
Readiness and consumed-mask emptiness are proved incompatible generally.

The existing `BindingMap.Typed.disposable` producer derives the whole-owner
permission from actual resident reads and the authoritative final masks. Its
runtime cleanup contract is strengthened in place; all public prefix/source
soundness consumers inherit the stronger guarantee. No second analysis or
future-state admission premise is introduced.

`BindingMap.Disposable.release_preserves_nondiscardable` and the public
`HasType.scope_preserves_nondiscardable` / `restore_preserves_nondiscardable`
construct retirement and preserve any cell containing a selected partial resident
that lacks residual disposal permission. Neither the selected descendant nor its
containing owner must remain readable. No explicit exact annotation is required.
Exact-owner guarantees remain valid, including outside the current lexical scope. Both scope
and return consumers construct cleanup through their authoritative producers
before applying owner protection. No successful retirement/restoration step is
a premise. All 30 build jobs and explicit producer/consumer axiom inspection
passed after this migration. This remains logical owned-cell cleanup, not
custom Drop or physical release.

`lake build Grounded` passed all 30 jobs. Explicit axiom inspection of residual
permission recovery, both general retirement theorems and source-function
soundness found only standard Lean axioms. No unit tests or concrete examples
were added. General preservation and progress consume the strengthened cleanup
contract; whole-language completion and the outstanding custom-hook, borrowing,
control-flow and physical-memory obligations remain open.


## General structural-principal protection at replacement

The runtime replacement contract now retains the existing checked path and
proves that a readable selected old resident permits discard at that path's
type. This permission is derived from the same final mask after RHS execution,
not a second resource analysis. Field/path result uniqueness is proved across
module visibility contexts, so the existentially selected type cannot conceal
another structural principal.

`HasType.no_nondiscardable_overwrite` consumes the general public prefix
soundness contract. It excludes overwrites above any selected partial descendant
that lacks residual disposal permission, including unreadable aggregates with
remaining ownership obligations. It does not assume termination. Moved-out holes
remain restorable; no additional restriction was imposed on source admission.

`lake build Grounded` passed all 30 jobs. Explicit axiom inspection covered
path uniqueness, the strengthened replacement producer, general overwrite
exclusion, preservation, progress and source-function soundness. Only standard
Lean axioms occurred. No unit tests, examples or assumed completion conditions
were introduced. Custom destruction, correlated branch states, loans, nonlocal
cleanup and the other whole-language obligations remain open.

The generalized retirement and replacement producers now share residual
`PartialValue.Disposable` evidence. Exact-nominal consumers derive their
protection from these producers and structural nonemptiness, rather than
duplicating the heap and path argument. All 30 build jobs passed after the
cutover. Axiom inspection of both producers, the three public general protection
theorems, exact-owner consumers and maximal source behavior reported only
standard Lean axioms. No tests or examples were added. This is logical
retirement and overwrite protection, not custom Drop or field destruction.


## Repaired the runtime disposal authority itself

A general pre-fix proof reproduced a remaining modeling defect: the independent
runtime nominal-disposal rule authorized a readable fieldless variant even when
the nominal type's inactive variants made its principal nondiscardable. The
source-mask checks and recently strengthened cleanup contracts blocked this in
checked execution, but the runtime relation itself was too permissive.

`PartialValue.Disposable` is now indexed by the actual storage/selected type.
It interprets the single `Initialization.Disposable` authority through the
existing physical-resident/mask typing relation. The duplicate runtime inductive
rules were deleted. No future source state, completed execution or additional
analysis is assumed. `read_permission` derives the whole-type permission from
an actual read; it covers inactive variants and reconstructed representations.

Retirement, replacement, temporary projection remainders and sequence-result
cleanup all consume this same interpretation. The separate whole-read permission
fields introduced in the preceding checkpoints were removed, as was duplicate
resident typing in replacement safety. The specialized resident-only exclusion
was removed; its real consumer now uses representation-independent read exclusion.
General preservation, progress and public source soundness retain the stronger
cleanup guarantees through the canonical relation.

Fresh source-only `lake build Grounded` passed all 30 jobs. General negative
proofs reject readable nondiscardable residents and reject a fieldless variant
of a nondiscardable nominal under every proposed runtime type witness. The
pre-fix reproduction and post-fix proofs were checked via stdin, with no test or
example files added. Exhaustive axiom inspection covered 3,799 imported Grounded
declarations and found only standard Lean axioms. The public preservation,
progress, retirement, overwrite and source-function results received explicit
axiom inspection.

This closes the duplicate disposal-authority defect, not the full language.
Custom hooks and their order/divergence, correlated ownership branches, loans,
nonlocal cleanup and the remaining tracked boundaries are still unproved.


## General direct-discard exclusion and principal invariance

`ValueHasType.use_permission` proves that Copy and MayDiscard cannot change
between two valid typings of the same logical value. The proof covers nested
aggregates and the legitimate element-type ambiguity of empty arrays; it does
not assume type uniqueness where that assumption would be false.

The canonical runtime disposal relation uses this result in
`read_permission_as`. Its existential typing witnesses cannot hide a weaker
principal. `HasType.no_nondiscardable_discard` carries the result through general
prefix soundness to direct sequence-result disposal, covering every structurally
nondiscardable type rather than only explicitly exact nominal annotations.
The proof requires an actual typing of the observed value, not a future-state
readiness or execution-completion assumption.

`lake build Grounded` passed all 30 jobs. Explicit axiom inspection of permission
invariance, runtime interpretation, general direct-discard exclusion and public
source-function soundness found only standard Lean axioms. No unit tests or
concrete example files were introduced. The full-language obligations remain
open; these results concern the current hook-free logical ownership semantics.


## Live descendant protection inside partially consumed storage

`PathType.disposable` now carries the canonical residual permission through
arbitrary-depth checked tuple/struct field paths. It follows the existing
physical field-opening and selection operations. Whole permission, empty masks,
mixed tuple masks and nominal constructor masks all use the same authoritative
permission rules. No ancestor readability assumption or parallel resource walk
is added.

`selected_permission` derives MayDiscard for an actually readable descendant.
The real retirement and overwrite consumers now use it. The public scope/caller
retirement theorems preserve the entire containing heap cell whenever a checked
path observes a live nondiscardable owner, even if other fields are holes. The
public overwrite theorem likewise excludes replacing a partially consumed
ancestor of such an owner after RHS evaluation. Their former whole-root cases
are instances with empty descendant paths; the existing APIs were generalized
rather than retaining a second proof path.

`lake build Grounded` passed all 30 jobs. Exhaustive imported axiom inspection
covered 3,808 Grounded declarations and found only standard Lean axioms. Explicit
inspection included path disposal preservation, actual scope/caller retirement,
partial-destination overwrite exclusion, preservation, progress and public
source-function soundness. No concrete examples or unit tests were added.

These proofs strengthen the current hook-free logical ownership contract. They
do not establish custom destruction or its ordering/divergence, correlated
branch cleanup, borrowing, nonlocal control, physical allocation or the other
remaining whole-language boundaries. None of the broad completion tasks is
claimed complete.


## Unified actual Copy and disposal safety through public source soundness

`Configuration.OwnershipSafe` now covers actual storage reads as well as all
modeled disposal sites. `BindingMap.Typed.copy_safe` constructs the real read
result and its Copy permission from the existing addressed-read producer and
checked field path. No second resource analysis or future execution assumption
is introduced.

`HasType.no_noncopyable_read` proves that an actual read transition after a
checked prefix cannot duplicate an owner whose principal forbids Copy. It covers
affine and exact restrictions, inherited aggregate restrictions, and alternative
valid typings of the observed value through the previously proved principal
invariance theorem.

All expression, pattern, declaration, supplied-package, imported-call and prelude
soundness consumers now export the unified ownership predicate. The old
cleanup-only predicate and proof names were migrated rather than retained as
aliases. Existing actual retirement, descendant protection, replacement and
direct-discard proofs consume the same strengthened public contract.

`lake build Grounded` passed all 30 jobs. Exhaustive imported axiom inspection
covered 3,813 declarations and found only standard Lean axioms. The Copy producer,
general ownership invariant, actual-read exclusion, preservation, progress and
public source-function soundness received explicit axiom inspection. No unit
tests or concrete example files were added. Full-language completion remains
open, including custom destruction, correlated branches, borrowing and the other
tracked boundaries.


## Actual mutation framing for disjoint fields of shared storage

`PathDisjoint` expresses pre-state separation using resolved field indices from
`ProjectionType`, not source spelling or an assumed post-state observation.
Its recursive descent permits arbitrary shared prefixes before distinct fields.
`write_frame` proves that actual partial-value replacement preserves the exact
selection result at the disjoint path, including failed observations and partial
ancestors. No post-state typing or read-success premise is supplied.

The proof is consumed by actual heap move/restore operations, binding-map access,
and `Step.assignment_frame_disjoint` / `Step.move_frame_disjoint`. These
machine theorems preserve complete read results even when both lexical places
resolve to the same storage identity. They complement the existing distinct-root
assignment guarantee rather than blanket-banning shared storage. Readiness,
Copy, disposal and execution remain separate contracts; this geometry does not
grant access permission or establish borrowing semantics.

`lake build Grounded` passed all 30 jobs, including general preservation,
progress and public source soundness. Exhaustive axiom inspection covered 3,838
declarations and found only standard Lean axioms. Explicit inspection included
physical writes, heap transfers/restoration and both actual machine framing
results. No unit tests or concrete example files were added.

The full specification remains incomplete. This closes disjoint tuple/struct
field mutation framing in the logical model, not loan compatibility, custom
cleanup, correlated control state, physical memory or the other tracked
whole-language obligations.


## Disjoint readiness through constructive move/restoration

The existing `StorageAddress.take.restore` progress contract now derives unchanged
initialization-mask selections and runtime reads for every pre-state-disjoint
path, both in its intermediate moved-out heap and in its restored heap.
`PathDisjoint.initialization_frame` uses the same resolved projection geometry
as physical framing. `Ty.fieldInfo_layout` establishes that different fields
open the same canonical parent layout; no independent shape reconstruction or
post-state readiness assumption is introduced.

The existing typed result, absent/present updates, intermediate repeat-move
rejection, identity preservation and outside-cell framing remain part of the
contract. Thus any previously ready disjoint mask remains ready through both
actual transitions. This is not a proof of general input-batch admission with
loans, custody or allocation claims; those boundaries remain open.

Verification: `lake build Grounded` passed all 30 jobs, including general
preservation/progress and source soundness. Exhaustive imported axiom inspection
covered 3,844 declarations with only standard Lean axioms. Both the static
framing theorem and its composed progress consumer received explicit inspection.


## Pre-state admission of arbitrary ordered owned-move arguments

`PlaceDisjoint` combines distinct resolved roots with disjoint checked fields
inside one root. It uses the existing slot and projection authorities; it does
not assert future readiness or blanket-ban shared storage.

`HasTypes.disjoint_moves` derives the ordinary sequential argument judgment
for any list of explicit owned moves from pairwise pre-state separation and
pre-state path typing/readiness. Static path and context updates are constructed.
Each update transports pending readiness using `initialization_frame`; slot
preservation transports compatibility for the remaining batch. No intermediate
context or successful runtime operation is supplied by admission.

`HasType.call_disjoint_moves` connects the result to existing function signature,
visibility and argument-shape checks. `HasType.disjoint_call_soundness` consumes
general preservation/progress and exports the complete prefix contract through
argument evaluation, entry and recursive callee execution: current typing,
terminal-or-step progress, caller consumption framing, distinct binding names
and ownership safety. It does not require termination or a completed execution.

Independent source-only verification in
`/tmp/grandiose-ordered-moves-verified.5ECk28` passed all 30 Lean build jobs.
Exhaustive axiom inspection covered 3,857 declarations; only standard Lean axioms
occurred. Ordered admission and both call consumers were inspected explicitly.
No unit tests or concrete examples were added.

This proves the explicit owned-move input boundary of the current logical
fragment. Mixed Copy/move input compatibility, borrowing/reborrowing, guards,
custody, physical allocation/exhaustion and the remaining whole-language
obligations are not established by this theorem. All broad completion tasks
remain open.


## Mode-aware mixed Copy/move input composition

`InputCompatible` now records ordered pre-state access compatibility over the
existing expression forms. Copy may precede another access to the same place;
a move requires disjointness from a later read or move. A Copy constructor is
not permission: each input must still have its ordinary pre-state checking
proof, including Copy permission and readiness where required.

`PlaceDisjoint.write_frame` transports the selected slot and exact mask through
an actual static context update. `InputCompatible.admit_next` uses that result
to derive pending admission. `HasTypes.compatible_inputs` composes an arbitrary
list with no supplied intermediate admission or runtime-success premise. The
former independent move-only induction was removed; `disjoint_moves` now
constructs individual admissions and consumes this same composition theorem.

`HasType.call_compatible_inputs` and `compatible_call_soundness` connect the
mixed relation to existing call checking and the complete general prefix-safety
contract. `InputCompatible.move_self_excluded` proves that move-then-read and
move-then-move of the identical place cannot satisfy compatibility, while
Copy-before-move and overlapping Copy reads remain admitted by the relation.
This is an ordered relation, not a symmetric blanket separation policy.

`lake build Grounded` passed all 30 jobs. Exhaustive axiom inspection covered
3,871 declarations with only standard Lean axioms; transport, overlap exclusion,
ordered composition and general call soundness were inspected explicitly.

This extends the preceding owned-move result to mixed accesses in the current
logical fragment. It is not shared-loan compatibility: borrowing, guards,
custody, physical exhaustion, custom destruction and whole-language soundness
remain open. Arbitrary inputs not handled by the compatibility constructors
are not silently declared compatible.


## Constructive pre-entry progress for mixed place inputs

`HasTypes.executes` constructs an actual ordered argument-machine run from
checked arguments and finite static expansion of those arguments alone.
`HasType.call_entry` consumes it, prepares the complete parameter binding list,
and constructs the actual `Step.call` / `Step.callInputs` run into fresh
`enterBindings` storage. General soundness proves entered-state typing, a next
step, retained caller consumption framing, distinct binding names and ownership
safety. Neither a supplied prepared binding list nor successful entry is assumed.
The callee body need not have finite call expansion and may recurse or diverge.

`HasType.compatible_access_entry` closes the pre-state admission-to-entry chain
for arbitrary mixed direct Copy/move arguments. It derives the ordered checking
judgment from `InputCompatible`, proves argument termination directly from
read/move syntax, and obtains actual argument evaluation, binding preparation,
entry and the complete entered-state safety contract. No future readiness,
completed execution or argument-termination certificate is supplied for this
place-access consumer.

A fresh source-only build in `/tmp/grandiose-input-entry-verified.hdR3QH` passed
all 30 jobs. Exhaustive axiom inspection covered 3,876 declarations with only
standard Lean axioms. The argument execution, general entry and mixed-place
entry theorems were explicitly inspected together with preservation, progress
and public source-function soundness. No unit tests or concrete examples were
added.

Scope remains the current logical heap and direct place-access fragment.
Physical allocation exhaustion, loan/reborrow permissions, guarded or captured
inputs, custody, custom cleanup and the remaining whole-language obligations
are not proved by this result. None of the 15 broad completion tasks is closed.


## Source-admitted uncertain branch outputs and conditional cleanup

Pattern arms no longer require identical output masks. Both core and named-source
arm admission check each body's own output context and a structural
`BindingContextApprox` into the common continuation context. Approximation
preserves binding identities, declared types and mutability; it can forget
initialization at a root or within a partial aggregate. It supplies no runtime
state, successful execution or cleanup result.

`Initialization.maybe` separates possible occupancy from definite availability.
`PartialValue.Typed.read_sound` now establishes `MayRead`, not `Ready`:
a physical read cannot retroactively authorize a source read or move from an
uncertain mask. `maybe_not_ready` proves this exclusion. `Disposable.maybe_iff`
proves that uncertain whole-owner cleanup requires the actual type's discard
permission; uncertainty cannot erase an exact-linear obligation. The former
`Disposable.ready` consumer is replaced by `Disposable.may_read`.

`PartialValue.Typed.approximate` and `BindingMap.Typed.approximate` prove
realization transport. `ProjectionType.open_partial` preserves uncertainty
through the existing projection authority. Selected-arm execution retains the
body's actual output context until its scope frame retires local storage, then
transports the surviving heap bindings to the joined context. General
preservation, progress, ownership safety, immutable consumption framing,
terminating execution and public source-function soundness consume this path.
No parallel runtime state or duplicate permission analysis was added.

Fresh source-only verification in
`/tmp/grandiose-branch-join-verified.EZAmae` passed all 30 Lean build jobs.
Exhaustive imported axiom inspection covered 3,957 declarations, with only
`propext`, `Classical.choice` and `Quot.sound`. The approximation producers,
selected-arm consumer, uncertainty exclusions and general soundness endpoints
received explicit dependency inspection. No unit tests or concrete examples
were added.

This closes conservative affine maybe-initialized branch cleanup in the current
hook-free logical fragment. It does not preserve relational correlations between
places or recover constructor-dependent availability from later discriminant
checks. Custom destruction and ordering/divergence, loans, nonlocal cleanup,
physical memory and the remaining whole-language obligations remain open.
None of the 15 broad completion tasks is marked complete.


## Uncertain descendant access and actual assignment restoration

`Initialization.select_maybe` proves that arbitrarily deep field projection
cannot turn an uncertain aggregate into definite availability. The general
`HasType.no_uncertain_read` and `no_uncertain_move` results consume it and
exclude source accesses when either the root or selected place is uncertain.
These are statements over arbitrary checking derivations, not concrete examples.

`HasType.assignment_restores` follows an arbitrary checked execution prefix
and constructs its next assignment transition. It derives the current binding
realization, destination type at the actual assignment module, context update, resulting heap
realization, exact readback of the assigned value, and a present mask at the
selected path. Every pre-state-disjoint path retains its previous mask, including
uncertainty. It requires neither old readiness nor supplied post-state typing.
The proof consumes general soundness, the authoritative assignment producer and
the existing path-framing theorem; it introduces no separate state analysis.

Verification: `lake build Grounded` passed all 30 jobs. Exhaustive axiom
inspection covered 3,962 declarations; only standard Lean axioms occurred.
The new projection, access-exclusion and public assignment results were inspected
explicitly alongside preservation, progress and public source-function soundness.
This strengthens the conservative branch-join boundary; relational correlations,
custom cleanup and all previously listed whole-language obligations remain open.


## Manual principal coherence in authoritative program admission

A general pre-repair proof showed that an empty function table satisfied
`Program.Checked` for arbitrary data declarations. Thus a manual affine or
duplicable class unsupported by owned fields was not rejected by admission;
structural permission intersection merely made the resulting type stricter.
That does not implement a checked declaration of the advertised principal.

`DataDecl.PrincipalValid` now checks explicit duplicable declarations against
Copy permission for every owned field of every variant, and explicit affine
declarations against discard permission. An exact restriction requires neither;
absence of a manual declaration retains structural inference. The validator
consumes `UsePermitted`, the existing permission producer, rather than introducing
a second capability analysis.

`Program.Checked` now requires principal validity alongside function-body
checking. `NamedProgramAdmitted` validates the same decoded declaration product
and derives the strengthened program contract. Invocation, termination, source
closure and declaration-resolution consumers were migrated without an old
function-only admission alias. No runtime progress or execution outcome was
added as an admission premise.

`DataDeclarations.PrincipalsValid.principal` proves that every admitted
explicit principal has exactly its advertised permissions.
`SourceClosure.Admitted.principal` exposes that result at public
source admission. `no_principal_widening` rejects an unsupported field in any
variant, including inactive variants and unused declarations. General
preservation, progress and source-function soundness retain their contracts
under the repaired admission boundary.

A fresh source-only build in
`/tmp/grandiose-principal-coherence-verified.hWN6PQ` passed all 30 Lean jobs.
Exhaustive axiom inspection covered 3,975 declarations; only standard Lean
axioms occurred. The new principal characterization and source rejection
proofs, admission producer and general soundness consumers were inspected
explicitly. No concrete examples or routine unit tests were added.

This repairs coherence of explicit restrictions in the current decoded nominal
declaration model. Source syntax/elaboration for data declarations, generic
quantity restrictions, indirection-aware recursive fixed points and custom Drop
remain separate open obligations; it is not whole-language completion.


## Declaration-wide layout admission and general inline-cycle exclusion

A general pre-repair proof established that principal validity plus an empty
function table still admitted arbitrary nominal layouts. Constructor-local
layout checks therefore did not reject invalid unused declarations. Function
interfaces also lacked their own layout obligations: nonreturning bodies are
not evidence that a declared parameter or result type is valid.

`DataDeclarations.Valid` now combines the existing principal validator with
`FiniteLayout` for every declared nominal identity. `Program.Checked.data`
and `NamedProgramAdmitted` consume this single declaration-admission product.
The superseded principal-only program field is removed. `FunctionChecked`
checks every parameter and result layout. Named parameter and result elaboration
produce those same obligations, including for recursive or unused functions.
No body termination premise was introduced.

`InlineChild` describes direct inline containment through tuples, fixed arrays
and declared nominal fields. It is not a pointer/referent graph.
`FiniteLayout.accessible` derives well-foundedness from the existing layout
proof, and `no_inline_cycle` excludes arbitrary nonempty transitive cycles.
The public source consumers `SourceClosure.Admitted.no_inline_cycle`,
`interface_layout` and `no_interface_inline_cycle` connect this result to actual
admitted declaration identities and function signatures. Existing schema
validity and array bounds remain part of `FiniteLayout`.

Fresh source-only verification in
`/tmp/grandiose-declaration-layout-verified.KSHWBW` passed all 30 Lean jobs.
Exhaustive axiom inspection covered 4,001 declarations; only standard Lean
axioms occurred. Layout accessibility, cycle exclusion, source parameter
elaboration and public source guarantees were explicitly inspected together
with general preservation/progress and source-function soundness.

The decoded fragment still has no pointer/reference type constructors;
indirection-aware recursive representation and capability fixed points remain
open. This does not establish byte sizes, alignment, physical allocation,
source data-declaration elaboration or whole-language soundness. The 15 broad
completion tasks remain open.


## Declaration-wide alias validation and expansion correctness

The pre-repair admission contract still accepted arbitrary alias tables when
functions were absent and nominal declarations valid. Alias checks ran only
when a type use requested expansion. A general Lean proof reproduced this
unused-declaration bypass before the repair.

`Aliases.Valid` now requires every declared body to resolve through the existing
`ResolvesType` relation to a finite-layout type. `NamedProgramAdmitted` and
`Program.Checked.aliases` consume this contract; no alternate expander or
runtime-success assumption was introduced.

`ResolvesType.alias_dependencies` derives declaration existence and
well-founded alias dependencies from actual expansion derivations, including
references nested in tuples and arrays. `ResolvesType.no_alias_cycle` excludes
arbitrary nonempty dependency cycles. Public source admission now derives
`alias_resolution` (existence, finite layout and uniqueness), `no_alias_cycle`
and `no_unresolved_alias` for every declared alias, used or unused.

Verification: `lake build Grounded` passed all 30 jobs. Exhaustive axiom
inspection covered 4,029 declarations; only standard Lean axioms occurred.
The two expansion/dependency theorems themselves require no axioms. Source
alias consumers and general preservation/progress and source-function soundness
were inspected explicitly. No unit tests or concrete examples were added.

This covers the current decoded nongeneric alias model. Generic substitution,
alias-qualified trait coherence, namespace/visibility resolution for source type
names, and the remaining whole-language obligations remain open.


## Declaration-wide structural constant admission and normalization

A general pre-repair proof showed that valid nominal/alias declarations and an
empty function table admitted arbitrary unchecked constants. The program and
named-source admission contracts now require `Program.ConstantsChecked` for
all decoded constants, including unused declarations. `ConstantChecked` uses
exactly the existing structural-syntax, alias-resolution and body-typing
premises of constant access; it assumes no completed evaluation.

`SourceClosure.Admitted.constant_correctness` now starts from an included source
constant, derives its emitted identity, and consumes declaration checking through
`HasType.constant` and shared structural normalization. It constructs a typed value and actual evaluation from
any caller environment, proves preservation of that caller's lexical scope and
heap, and proves uniqueness of both returned value and final environment.
Function termination is not required. No alternate evaluator was introduced.

Fresh source-only verification in
`/tmp/grandiose-declaration-admission-verified.btT50s` passed all 30 Lean build
jobs. Exhaustive imported axiom inspection covered 4,040 declarations; only
standard Lean axioms occurred. Constant normalization, alias expansion,
layout validity, general preservation/progress and public source-function
soundness were inspected explicitly. No unit tests or concrete examples were
added.

This validates decoded nongeneric constants; it does not supply source constant
declaration elaboration, generic constant schemes, additional namespaces or
trait coherence. Physical memory, loans, custom cleanup and the other tracked
whole-language obligations remain open. None of the 15 broad completion tasks
is closed by this boundary repair.

## Explicit-import declaration privacy

The source-closure audit against §§2.1–2.3 and §3.1 found an admission defect:
an explicit import checked the target binding's visibility but not the original
declaration's visibility. A public alias could therefore admit an unused import
of a private function into another package. Call elaboration already rejected
invoking that function; deferring the import error until invocation was wrong.

The repair now lives in the shared `FunctionAccess` contract consumed by
`FunctionProvenance`, glob discovery and visible selection. `FunctionImportsValid`
requires a visible seeded candidate for every explicit import, including unused
ones; the duplicate original-authority conjunct is removed. `explicit_binding`
still carries that authority with its existing seeded candidate.

`VisibleFunctionCandidate.origin_access` and
`SourceClosure.Admitted.candidate_visibility` replace the explicit-only privacy
APIs. They transfer original authority through actual named declaration
elaboration for any selected import kind. `imported_call_soundness` exports
original-declaration authority at the import owner and characterizes caller
selection by the original declaration visibility. Public aliases cannot enlarge
private authority. Public declarations re-exported through hidden module paths
retain identity-preserving behavior.

Strict scoped `lake build Grounded.SourceClosure` passed in an isolated source-only
workspace. Transient parametric Lean proofs established that the previous
contract admitted the private-function/public-alias/cross-package-import graph
for arbitrary declarations and names, and the repaired contract rejects the
same graph. These diagnostic proofs were removed, not installed as routine
examples. Axiom inspection of the new general import guarantees, imported-call
soundness and source-function soundness found only `propext`, `Classical.choice`
and `Quot.sound`.

Identifier classification remains unchanged: the existing checked decoder and
grammar theorem exactly implement ASCII identifiers with wildcard exclusion.
Decoded identifiers are not a proof of UTF-8 decoding, token boundaries, nested
comments, structural-word grammar, or spans. Source inclusion still follows only
declared inline/external modules and the self-named-directory rule; existing file
permutation and module-owner proofs remain checked. Other namespaces, module
aliases, parser/source-map obligations, library profiles, and whole-language
semantics remain open. The then-shared glob/prelude candidate kind was subsequently
replaced by the lowest-priority repair recorded below.

## Ordered admitted-call execution decomposition

The direct-call boundary now has an elimination theorem as well as execution
constructors. Previously the evaluation API composed supplied argument/body
runs but did not recover those phases from an arbitrary completed invocation.
Under normative §5.2, order is a property of every actual execution, not merely
of a chosen construction of one execution.

`Step.unextend` and `Run.unextend` prove that retained caller frames cannot
participate before the computation above them reaches terminal control.
`Evaluates.call_iff` uses this operational boundary to extract the complete
argument evaluation, exact parameter preparation, selected body execution in
fresh storage, and caller restoration from any completed direct call.
`EvaluatesMany.cons_iff` and `EvaluatesMany.append_iff` recover actual sequential
runs at each argument and arbitrary argument-list cuts. No second evaluator or
proof-only evaluation-order relation is introduced.

`HasType.call_signature` connects the uniquely selected declaration to the
ordered checking judgment. `HasTypes.evaluation_soundness` derives typed
argument values, output storage masks, issued activation, and consumption-only
framing from the actual argument run. The public
`HasType.call_evaluation_soundness` consumes these producers and exports all
three invocation phases, typed parameter bindings, argument-phase and returned
state safety, and every prefix-before-suffix argument cut. Its completion
premise is the observed run being characterized, not an admission requirement.

`Evaluates.call_body_noncompletion` proves that a body with no completed run
after the actual arguments cannot yield a completed call. This raw statement
is not by itself a divergence/progress theorem; existing admitted-prefix
soundness excludes stuck prefixes. `Program.Checked`, `FiniteCalls`,
`HasType.call_entry` and its constructive mixed-place consumer are unchanged:
recursive bodies still need no termination certificate, while finite argument
execution remains constructed rather than supplied to the admitted-entry API.

Scoped Lean checking in `/tmp/grandiose-function-evaluation-IPAZyY` passed
`lake build Grounded.Soundness`. Explicit axiom inspection of the nine new
theorems and both existing entry consumers reported only `propext`,
`Classical.choice` and `Quot.sound`. No examples or unit tests were introduced.

This closes the general completed direct-call/order boundary in the existing
fragment, not full callable application. `Expr.call` still selects a numeric
declaration identity rather than evaluating a callee expression; `Ty` and
`Value` contain no callable/environment representation. First-class function
items, closures, callee-expression evaluation, capture formation/invocation,
callable evidence and nonlocal control therefore still require an authoritative
model extension and corresponding checking/preservation/source consumers.
Pattern application retains its existing machine and safety semantics; this
new direct-call decomposition does not claim a pattern-application inverse.

## Ownership-safe uncorrelated branch joins

The former type-free `Initialization.Approximates.unknown` admitted every
initialization mask as `maybe`, including exact-linear occupancy. Residual
cleanup already refused to discard such an owner, but branch admission could
still forget the correlation required by language §7.4. Rejecting a later
cleanup is not the contract for crossing that uncorrelated boundary.

Approximation now uses the authoritative declared resident type and data table.
A fresh unknown requires ordinary `MayDiscard`; tuple and nominal fields are
checked recursively. Manual exact nominal restrictions additionally preserve
whether the shell is consumed: `Empty (.fields before) ↔ Empty (.fields after)`.
This does not freeze its whole mask. A retained present sibling permits another
discardable field to become uncertain, including inside a manually exact struct.
The uncertain field may then be restored before a whole move. Conversely, a
consumed shell and a live shell cannot share a join. Reflexive joins remain
available for all ownership classes.

`BindingContextApprox`, core arm checking, named arm elaboration and actual
scope-frame preservation consume this same relation. No alternate join model or
post-state certificate was added. `PathType.approximate_initialization` derives
the type-indexed join relation at arbitrary checked descendant paths from the
actual resident. `HasType.scope_join_preserves_ownership` now constructs the
scope-retirement transition from a reached cleanup state, without taking the
completed step as an input. It derives disposal permission and newest-owner-first
order, retires every selected local identity, and preserves continuation typing.
Retained heap cells are unchanged, both branch and joined contexts type the
resulting store, no nondiscardable descendant gains a fresh unknown mask, and
every manually exact nominal descendant retains its consumed-versus-live status.
Its inputs are ordinary program/body checking, actual entry-store typing, issued
activation and the run reaching cleanup; neither cleanup success nor future
typing is supplied. The strengthened theorem passed all 30 Lean build jobs and
standard-axiom inspection. Custom Drop execution remains outside this fragment.

Integrated verification: `lake build Grounded` passed all 30 jobs, including
the recently integrated import-privacy and ordered-call proof consumers. A
general Lean proof additionally established that any two exact-shell states
admitting a common join agree on their consumed status.
Lean axiom inspection of the new public theorem, ordinary soundness, descendant
approximation and runtime typing approximation reports only `propext`,
`Classical.choice` and `Quot.sound`. Independent general Lean probes against
the corrected production declarations establish anchored affine-field join
admission, unchanged actual residents under those joins, and exclusion of a
common join for consumed/live exact-shell alternatives. No examples or unit
tests were added.

Relational control islands that retain differing exact-shell consumption states
remain unimplemented; they must not use this correlation-forgetting
join. Custom Drop, cleanup order with observable hooks, loans, cancellation and
nonlocal exits, and physical storage semantics remain whole-language obligations.


## Actual pattern invocation and normalized-source execution

`Evaluates.applyPatterns_iff` now characterizes completed pattern invocations
through the existing machine: ordered argument execution, actual first-arm
selection, execution in extended binding storage, and scope retirement. The
reverse implication constructs the same run; there is no alternate evaluator.

`SourceArmsChecked.evaluation_soundness` consumes this characterization through
existing normalized-source admission and arm selection. It derives typed
argument values and binding packs, realized argument-output and final contexts,
issued final activation, consumption framing, result typing and actual sequential
execution at every argument-list cut. No `FiniteCalls` premise or assumed future
completion is introduced into admission. Completion is an observation for this
partial-correctness theorem; existing prefix soundness still provides progress
for recursive and nonterminating computations.

Verification: `lake build Grounded` passed all 30 jobs. Explicit axiom inspection
of the operational characterization, new source consumer, existing source-prefix
soundness and public source-function soundness found only standard Lean axioms.
No examples or unit tests were added. First-class pattern callable values,
captured environments, borrowing and nonlocal control remain separate open
representation and proof obligations.


## Actual execution preserves retirement and retained-scope liveness

The existing `RuntimeHeap.Retired.history` result previously consumed a heap
history without connecting that history to machine execution. Actual allocation,
move/write, scope exit and caller restoration now produce that same history:
`Step.heap_history` and `Run.heap_history` cover every current transition.
There is no new heap, allocator, evaluator or assumed simulation relation.

`Run.retired` proves non-resurrection through arbitrary actual execution prefixes.
`Run.retired_inaccessible` carries it through actual lexical read, move and
restoration operations, including arbitrary descendant paths and stale binding
maps. `Run.scope_retired` and `Run.return_retired` derive permanent retirement
from the actual scope-exit/return transitions and the released binding identities.

`ConfigurationTyped.typed_scopes` establishes present heap realization, actual
owning activation and typed partial occupancy at every continuation-prefix
scope, not only the active or outermost frame. Consequently retired identities
cannot occur in any of those realized binding maps.
`SourceClosure.Admitted.storage_lifetime_safety` composes actual function entry,
source-derived prefix soundness, heap-history production and retained-scope
liveness. It requires neither termination nor future-state liveness assumptions.

The same public source contract now also preserves allocation provenance:
every surviving previously issued cell retains its original activation owner
and declared type. `Step.storage_origin` proves this from actual resident updates,
allocation and retirement; `Run.storage_origin` composes it across arbitrary
execution. The allocation frontier is derived monotone from the existing heap
history. No post-state identity or typing premise is supplied. Explicit axiom
inspection of both operational producers and the strengthened public source
consumer found only standard Lean axioms; the 30-job build passed.

Verification: `lake build Grounded` passed all 30 jobs. Explicit dependency
inspection of the new operational and source endpoints and existing general
preservation/progress found only standard Lean axioms. No examples or unit tests
were added. No bounded runner was introduced.

This establishes logical storage-identity lifetime safety for the current owned
fragment. Reference carriers, loan permissions, reborrowing, outlives and return
provenance, and custom Drop remain unimplemented. Storage liveness alone grants
no reference access permission; none of the broad completion tasks is closed.


## Canonical storage addresses and the source projection bridge

Actual reads, moves and restoration now operate on `StorageAddress`, whose
storage root is independent of lexical binding identity. `BindingMap.resolve`
produces that address; all three lexical access operations consume it. The old
`takeStorage`/`restoreStorage` APIs were removed rather than retained as aliases.
This is a logical root/path address, not a byte offset or a physical ABI claim.

`StorageAddress.Typed` records the exact projected type of the current heap
cell using the existing `PathType` judgment. Its type is unique. It supplies
neither initialized contents nor loan permission. `BindingMap.Typed.resolve`
constructs the actual resolution result and address typing from source binding
realization and the checked source projection. The read/move/restoration
progress proofs consume that same result; they no longer independently rebuild
the source-to-cell projection bridge. Initialization evidence remains a separate
pre-state requirement for reads and moves, while restoration can fill a hole.

The migrated operations and proofs feed existing machine preservation/progress
and public source soundness. `Run.address_type` uses actual allocation-provenance
preservation to retain exact address typing when its root survives;
`Run.retired_untyped` rejects address typing after retirement. Observed root
liveness in the former theorem is not assumed as a future source-admission fact.

Verification: `lake build Grounded` passed all 30 jobs. Explicit axiom inspection
covered the source bridge, address-type uniqueness, all three operation-progress
producers, lifetime transport/rejection, general preservation/progress and public
source-function/lifetime soundness; only standard Lean axioms occurred. No
examples or unit tests were added. Reference carriers, loan authority, reborrowing
and region/return contracts remain the next integrated representation boundary;
this address cutover alone does not admit borrowing or establish full soundness.


## Address separation through constructive mixed-input entry

`StorageAddress.Disjoint` lifts the existing checked field geometry into the
actual pre-state heap; distinct-root separation uses storage identities, not
lexical names. `BindingMap.Typed.separated` derives it from the source relation
and actual address resolution, using binding-map injectivity. No second alias
analysis or independently reconstructed field layout is introduced.

Actual take/restoration framing consumes this relation, including disjoint
fields in one cell. The existing lexical and machine framing consumers use the
same address-level producer. `HasTypes.compatible_inputs_execute` constructs
arbitrary ordered batches of admitted direct Copy/move inputs. It proves that
each returned value equals that input's original pre-state observation, derives
the intermediate heaps and checking contexts, and preserves scope and activation
supply. Pending observations survive each real move by address framing; their
future readiness or future contents are not assumed.

`HasType.compatible_call_entry` consumes that batch, performs actual parameter
preparation and callee allocation, constructs the machine run to the selected
body with its caller-restoration frame, and obtains reached-state typing and a
next transition from general preservation/progress. The body may recurse or
diverge: neither completion nor body termination is assumed.

Verification: `lake build Grounded` passed all 30 jobs. Explicit axiom inspection
of address separation, both mutation-frame producers, constructive batch/entry,
general preservation/progress and public source-function soundness found only
`propext`, `Classical.choice` and `Quot.sound`. No unit tests or concrete
examples were added.

The initial owned-move-only construction was generalized through the existing
ordered `InputCompatible` relation; its two narrower theorem APIs were removed.
Copy may overlap later Copy or move inputs. A preceding move must preserve the
later read/move through pre-state address separation. The syntax premise only
identifies direct place inputs; it assumes no successful read or completed run.
`Expr.inputObservation` records the same addressed read for either input mode,
not a second storage semantics. Arbitrary effectful/computing argument expressions
retain general prefix safety, not an unconditional termination claim.

The mixed construction passed all 30 jobs; explicit inspection of its two
endpoints, pending-admission producer, call-prefix safety, general machine
preservation/progress and public source soundness found only standard Lean axioms.
No unit tests or concrete examples were added.

This is entry in the current logical allocator. It does not construct borrowed
inputs, prove shared/unique loan compatibility, interpret physical allocation
exhaustion, or discharge the whole-language obligations.


## Lowest-priority automatic preludes through actual source admission

A general pre-repair Lean proof showed that an authored glob and the actual
automatically emitted prelude competed as equal-strength candidates: distinct
declaration identities forced `functionNames` to return `none`. That was not
§2.5's lowest-priority prelude contract.

Automatic requests now emit `FunctionImportKind.prelude`, not `glob`. One
`FunctionProvenance` relation generates finite declaration-seeded import paths;
discovery and priority-filtered selection instantiate that same producer with
different admissible-edge policies. Discovery is not an independently supplied
name table. Selected paths enforce priority at every import hop. Explicit
bindings suppress both weak tiers; an authored glob with an accessible declared
name suppresses the automatic tier. Merely having an unrelated glob does not
suppress every prelude name. Unknown/unresolved evidence does not grant fallback.

`FunctionImport.Selects.prelude_excluded` derives exclusion from an actual
authored-glob candidate. `functionNames.glob_over_prelude` proves successful
selection for one authored incoming glob against any number of automatic edges,
using unique target resolution but no successful local lookup or global
uniqueness premise. Import-order invariance and rejection of unseeded cycles
continue through the shared provenance relation.

Source admission now checks `ImportSelection.Authored` through
`LoadedModule.Valid`. Groups and descents cannot forge the driver-only marker.
`SourceClosure.Admitted.automatic_import_origin` derives every automatic edge's
actual owning package, enabled suppression flags, selected profile path, private
visibility and resolved target. The existing prelude-call soundness theorem
consumes the corrected priority rule and still reaches general machine safety.

Verification: an independent source-only workspace with no copied `.olean`
files passed all 30 jobs. Explicit axiom inspection covered priority selection,
exclusion, grouped-import provenance, leastness, unseeded cycles, import/file
order invariance, automatic origin, prelude/source-function soundness, mixed
input entry and general preservation/progress. Only standard Lean axioms occur.
No unit tests or concrete examples were added.

This repairs decoded callable-prelude priority. Other namespaces, source-text
parsing, library/runtime profiles and the remaining whole-language obligations
remain open; no broad completion task is marked complete.


## Explicit shadowing in discovery and constructive prelude fallback

A general pre-repair proof established that discovery admitted a weak import
route even while an explicit binding prohibited selecting that same route.
That could turn a public route hidden by a private local declaration into a
phantom authored-glob claim, incorrectly suppressing a caller's prelude.

`FunctionImport.Routes` now consumes the same explicit-binding exclusion as
selection. `Routes.weak_excluded` rules out both weak discovery routes under a
strong binding. `RawFunctionCandidate.selected_without_prelude` proves discovery
and selection agree on authored-only graphs, including arbitrary finite paths
through cyclic imports. `hidden_local` and
`GlobFunctionBinding.absent_of_hidden_locals` prove inaccessible local bindings
cannot expose shadowed routes or create phantom glob claims.

`functionNames.prelude_without_glob` constructs local fallback from unique
target resolution and actual name-specific absence, without assuming successful
local lookup. `SourceClosure.Admitted.automatic_import_unique` derives the
single automatic edge from package identity, profile and path resolution.
The existing `prelude_call_soundness` consumer now uses that producer and the
constructive fallback theorem rather than invoking global uniqueness at the
caller namespace to select the prelude. Original declaration visibility,
argument elaboration and the complete execution-prefix safety contract remain.

Verification: `lake build Grounded` passed all 30 jobs. Explicit axiom inspection
covered exclusion, discovery exactness, private-name exclusion, fallback,
authored-glob precedence, automatic-edge uniqueness, source/prelude soundness,
file-order invariance and general machine preservation/progress. Only standard
Lean axioms occurred. No unit tests or concrete examples were added. The broad
source-resolution and whole-language obligations remain open.

## Original-declaration privacy in discovery and selected lookup

A parametric pre-repair Lean proof established that a public alias was a visible
callable candidate even when its original declaration was private to the caller.
Later invocation checking rejected the call, but lookup and glob/prelude priority
had already counted the inaccessible identity.

The shared `FunctionProvenance` producer now checks `FunctionAccess` at every
import hop. That contract reads the original declaration identity and visibility;
it is not a separate name analysis or permission table. Discovery, glob name
claims and final visible selection consume it. Explicit-import admission no longer
carries a duplicate declaration-access premise. `functionNames.selected` now
returns the accessible original declaration, and `functionNames.inaccessible`
excludes its selection through arbitrary alias/re-export paths.

`GlobFunctionBinding.absent_of_private_origins` proves that inaccessible origins
cannot suppress a prelude merely because their alias bindings are public. The
existing authored-glob precedence, constructive fallback and import-order proofs
continue through the repaired shared relation. Authorized public declarations
re-exported through hidden modules are not blanket-rejected.

`SourceClosure.Admitted.candidate_visibility` and `resolved_visibility` transport
this authority through actual named-function elaboration. Dependency and prelude
call soundness now derive original-declaration visibility instead of asking the
caller to supply it again. Explicit-alias call soundness constructs the original
core declaration and proves an exact equivalence: with the stated namespace and
binding access, selection of that identity holds iff its original declaration
is accessible to the caller. It then constructs the authorized call and retains
general configuration typing, progress, consumption framing and ownership safety
for every execution prefix. The superseded explicit-only privacy APIs are removed.

Verification: an independent source-only `lake build Grounded` passed all 30
jobs. Axiom inspection of privacy exclusion, discovery/fallback, source call
soundness, file-order admission invariance and general machine preservation and
progress found only `propext`, `Classical.choice` and `Quot.sound`. No unit tests
or concrete examples were added. Whole-language soundness and the broad source
and invocation boundaries remain open.

## Maximal source-admitted execution: typed return or safe divergence

The finite-prefix safety contract now has a whole-execution consequence for the
current logical machine. `InfiniteRun` is an unbounded sequence of actual
`Step` transitions, not a second evaluator, bounded runner or stuttering rule.
Its prefixes produce the existing `Run` relation. Step determinism proves
infinite-trace uniqueness and excludes an infinite trace whenever a finite
terminal run exists.

`Run.terminal_or_infinite` constructs an infinite trace from reachable-state
progress when no terminal configuration is reachable. This is a theorem about
the existing transition relation, not a new source-admission premise.
`HasType.behavior` supplies that progress from general preservation and carries
the result into either an actual typed normal evaluation with final storage and
consumption framing, or an infinite trace whose every state preserves
configuration typing, ownership safety and the same consumption frame.

`SourceClosure.Admitted.behavior` consumes actual source elaboration and the
source-produced checked program. It assumes neither a completed execution nor
`FiniteCalls`, termination, future readiness or a run-progress certificate.
The two behavior classes are exhaustive for admitted code in this machine and
are exclusive by `Run.excludes_infinite`.

Verification: `lake build Grounded` passed all 30 jobs. Explicit axiom inspection
of trace construction, prefix extraction, trace uniqueness, exclusivity and the
public source behavior theorem found only standard Lean axioms. No examples or
unit tests were added. Physical exhaustion, effects, foreign boundaries and
whole-language completion remain separate open obligations; this theorem does
not reinterpret their missing transitions as divergence.

## Maximal invocation behavior includes actual caller restoration and cleanup

`ConfigurationTyped.behavior` now owns maximal behavior for arbitrary typed
control and continuations. `HasType.behavior` consumes that theorem; its duplicated
trace-construction proof is removed. This includes already-evaluated arguments
waiting in a real `Frame.call`, not only expressions with empty continuations.

`Run.body_return_retires` decomposes actual execution at the return frame and
uses the body's scope-preservation proof to identify the original entry bindings.
`Run.call_cleanup` extracts real parameter preparation and proves permanent
retirement of every corresponding callee cell on completed invocation. Nested
calls and lexical allocations are covered; future heap readiness and a supplied
cleanup result are not premises.

`SourceClosure.Admitted.invocation_behavior` consumes resolved source authority,
typed actual argument values and the current caller store. It derives a typed
return with the original caller scope restored and all parameter cells retired,
or an infinite actual execution preserving configuration typing, caller framing
and ownership safety at every index. The supplied store is the caller state
after argument evaluation; this is not a theorem assuming arbitrary argument
expressions terminate. Source-expression behavior covers those expressions.

Verification: all 30 `lake build Grounded` jobs passed. Axiom inspection of actual
cleanup, generalized maximal behavior and both public source consumers found only
standard Lean axioms. The scope remains the current logical owned-value machine;
custom destruction, loans, physical resource limits and whole-language completion
remain open. No unit tests or concrete examples were added.

## Ordered pre-state-compatible inputs reach complete invocation behavior

`SourceClosure.Admitted.compatible_call_behavior` now consumes the constructive
ordered Copy/move batch and entry theorem all the way through maximal invocation.
It derives original-declaration visibility from source resolution, retains each
argument's original pre-state observation, and constructs parameter preparation
and the actual run to the callee body with its return frame.

From that reached configuration, general preservation/progress yields either an
actual typed return with caller consumption framing and permanent retirement of
every callee parameter cell, or an infinite actual call execution preserving
typing, framing and ownership safety at every index. `Run.prepend_infinite`
composes the constructed finite setup with the divergent callee execution using
the existing steps. There is no second invocation evaluator.

The compatibility premise is the existing ordered `InputCompatible` relation,
not blanket disjointness. Copy overlap is retained, and moves preserve pending
observations through the shared address-framing producer. All input admission
uses the original context; actual values, intermediate readiness and body
termination are conclusions or absent, never supplied successful execution.
Inputs here are resolved Core read/move places, not a newly implemented source
parser or borrowed-input contract.

Verification: `lake build Grounded` passed all 30 jobs. Explicit axiom inspection
of finite/infinite composition and the public source-selected call theorem found
only standard Lean axioms. No examples or unit tests were added. Reference/loan
compatibility, physical exhaustion and the other whole-language obligations remain
open; this closes the maximal-behavior consumer of the logical Copy/move chain.

## Non-exhaustive enum authority reaches source coverage and machine progress

Decoded enum shapes now carry their specified non-exhaustive marker. The shared
`DataDecl.ClosedAt` contract permits closed constructor reasoning inside the
defining package and for exhaustive enums; it does not grant visibility. Both
owned constructor-pattern access and coverage splitting consume this authority.

Coverage now carries the checking module through Core admission, named-source
elaboration, normalized constant-pattern admission and actual pattern frames.
Its constructor-independent fallback matrix retains only wildcard/whole-binder
rows. The general `Covers.selectArm` proof constructs the actual first match for
this rule, and existing general preservation/progress and maximal source behavior
consume the migrated contract. Runtime matching is unchanged; no extra evaluator
or parallel declaration table supplies permission.

General exclusion proofs establish that an external non-exhaustive enum requires
a whole-value coverage row, including when its currently declared variant list
is empty. For an owner without discard permission, every admitted owned pattern
is a whole binder with exactly that owner's type and binding. Thus neither a
wildcard, a constant pattern nor field extraction can erase an exact-linear
external owner. Nested matrix columns use the same rule. Whole forwarding does
not acquire Copy or discard permission; body checking still owns that obligation.

Verification: an independent source-only `lake build Grounded` passed all 30
jobs. Axiom inspection of coverage construction, both general exclusion proofs,
named-pattern checking, general preservation/progress and both maximal source
behavior consumers found only `propext`, `Classical.choice` and `Quot.sound`.
No examples, unit tests, new axioms or assumed matching outcomes were introduced.
This is decoded owned-value semantics, not attribute parsing, borrowed matching,
separate-compilation compatibility or whole-language completion. Those and the
other broad obligations remain open.

## Newest-owner-first retirement through actual source execution

A general pre-repair Lean derivation exposed the shared release implementation's
ordering mismatch: two arbitrary inputs allocate older then newer storage, while
`releaseBindings` threaded retirement through the same lexical list. Lexical
presentation is not acquisition order; reversing that list indiscriminately
would also mishandle scopes containing prepended locals.

The existing fresh storage identities provide the authoritative acquisition
order. `BindingMap.releaseOrder` derives a descending permutation of those
identities, and the actual shared `releaseBindings` operation consumes it. No
second allocation clock or ownership stack is introduced. General proofs show
that this order contains precisely the scope's cells, strictly newest-first,
and that arbitrary source-ordered input batches retire in reverse acquisition
order. Parameter acquisition itself remains left-to-right.

`releaseBindings.prefix_step` factors the real retirement operation at every
position into actual prefix, single-cell and suffix heap transitions. The scope
exit and caller-return consumers derive this factorization from reached-state
`Configuration.OwnershipSafe`. That public invariant now includes retirement
order alongside existing disposal permission. General source-prefix soundness
and maximal source behavior therefore retain the stronger contract; it is not
a standalone ordering fact. Exact-owner and nondiscardable-descendant protection,
caller framing, permanent retirement and constructive release progress all
consume the changed operation.

Verification: an independent source-only build passed all 30 Lean jobs. Explicit
axiom inspection of batch ordering, retirement factorization, actual scope/return
consumers, ownership safety, preservation/progress, call cleanup and public
source behavior found only standard Lean axioms. No unit tests or concrete
examples were added. The preliminary ordering derivation was checked through
stdin; no throwaway source file remains in the repository.

This specifies logical cell-retirement order. Custom Drop execution, ordered
resident-field destruction, divergence during hooks, references/loans and
physical-resource behavior remain open; atomic retirement is not claimed to
implement those missing semantics. No broad completion obligation is closed.

## Disposal permission survives every intermediate retirement prefix

`BindingMap.Disposable.release_prefix` derives the exact original cell and its
residual disposal permission immediately before each retirement in a scope.
Its conclusion identifies the same cell in both the pre-cleanup and intermediate
heaps. Strict acquisition order excludes its identity from the completed
prefix; the shared heap-framing theorem preserves the resident. No intermediate
readiness or replacement resident is assumed.

For every checked path to a manually exact nominal descendant, this same
producer now constructs the selected partial resident and proves it is
structurally empty immediately before retirement. Neither whole-value
readability nor future absence is assumed. Both configuration-level retirement
consumers and the constructive source scope-exit and caller-return theorems
export this guarantee for every split of the actual retirement order.
All 30 Lean build jobs and explicit standard-axiom inspection of the producer,
constructive source consumers and maximal source behavior passed.

Both `Configuration.OwnershipSafe.scope_retirement` and `return_retirement`
consume this producer and export the stronger intermediate-state guarantee.
`HasType.scope_join_preserves_ownership` and `HasType.return_restores` consume
these intermediate-state guarantees for the cleanup transitions they construct.
For every split of the actual retirement order, they expose the actual prefix
heap, next retirement, remaining suffix and unchanged original eligible cell.
The suffix reaches the same constructed final heap. No completed cleanup or
intermediate-state readiness is an admission premise. The composed producer,
both constructive consumers and maximal source behavior passed all 30 Lean
build jobs and standard-axiom inspection. This extends the real retirement
consumers, rather than merely recording a separate pre-state permission list.

Verification: all 30 `lake build Grounded` jobs passed. Axiom inspection of the
new producer, both consumers and public source soundness found only standard
Lean axioms. No examples or unit tests were added. Custom Drop and field-by-field
destruction remain outside the current logical retirement operation.

## Complete storage accountability through maximal source behavior

The prior invocation cleanup result covered entry parameters, not every cell
allocated by nested calls, local bindings and pattern bindings. The operational
chain now closes that gap generally:

- `allocateBindings.outside` frames identities outside the actual output map.
- `Step.untracked_origin` and `Run.untracked_origin` prove that a live cell
  outside every active/retained scope was already live and untracked before
  execution. `Configuration.Untracked` inspects existing binding maps and restore
  frames; it is not another owner table or assumed frame invariant.
- `Run.allocated_tracked` therefore excludes orphaned fresh live storage at
  every reachable prefix, including prefixes of infinite execution.
- `Run.return_retires_all` proves retirement of every issued identity between
  the initial and final allocation frontiers. General configuration typing
  derives its outer-scope bound from current retained-scope liveness, rather
  than supplying a future cleanup guarantee.

`ConfigurationTyped.behavior`, `HasType.behavior` and all three public source
maximal-behavior consumers now export this contract. Normal completion retires
all newly allocated cells; divergence keeps every new live cell tracked by the
actual active or retained binding maps. The ordered-input consumer composes from
before argument evaluation, not just from after parameter allocation. Existing
parameter-preparation and exact parameter-retirement witnesses remain exported.

Verification: an independent source-only build passed all 30 Lean jobs. An
imported-module audit traversed all 4,511 Grounded declarations and checked their
transitive axiom dependencies: only `propext`, `Classical.choice` and `Quot.sound`
were used. The audit ran through stdin; no tests, examples or audit scaffolding
were added to the repository.

Completion audit remains negative. This contract concerns logical cell storage;
values cannot yet contain loans, raw allocations or captured environments.
Language §7.6 custom hooks and reverse field destruction, §7.7 nonlocal cleanup,
and library §§22/30 physical ownership and suspension contracts are not modeled
by logical retirement. The declarations checked by source admission remain the
decoded fragment described above, not the complete normative language or library.
No broad completion obligation is marked complete.

## Explicit normative completion audit after storage accountability

Result: **not complete**. The audit compared the public theorem signatures and
admission premises with language §§2–21 and the language/library conformance
inventories (L01–L48 and S01–S96). Kernel-checked proofs of the decoded fragment
are not evidence that missing source constructs have semantics. No conformance
case is credited merely because its input cannot be expressed or admitted.

The checked `Ty` constructors are unit, integer, character, tuple, array and
nominal identity. `NamedExpr` has direct calls and immediate pattern application,
not callable values, borrows, effects, labels or foreign leaves. `Program` carries
target, aliases, constants, nominal data and direct functions. `Program.Checked`
checks these products. `SourceClosure.Admitted` derives direct-function checking
from source elaboration, but still requires supplied nominal/alias validity and
constant checking through `NamedProgramAdmitted`. It is not full source admission.

| Completion family | Proved boundary | Missing normative boundary |
| --- | --- | --- |
| Ownership, partial initialization, destruction (§7) | Structural Copy/discard, residual masks, ordered logical retirement, complete new-cell accounting | Custom Drop, reverse field destruction, hook divergence, cleanup-bearing nonlocal outcomes and correlated exact states |
| Namespaces, source closure, lexing (§§2–3,20) | Decoded modules, direct-callable resolution, visibility, selected preludes, identifier/scalar validation | Complete namespace/declaration inventory, byte-level lexing/parsing and all literal materialization |
| Types, aliases, representation (§4) | Finite owned layouts, nominal constructors, aliases and external non-exhaustive matching restrictions | Generic type families, references, pointers, callable types, floats and exact target/ABI layouts |
| Application and patterns (§§5–6) | Ordered direct calls, named patterns, first-arm selection and coverage | First-class/contextual callables, receiver modes and full callable inference |
| Captures and guarded control (§8) | Ordinary argument compatibility and consumption framing | Captured environments in the same invocation relation, guarded alternative ownership and nonescape |
| Lifetimes, borrowing, refinements (§9) | Stable logical addresses and retired-address exclusion | Loan creation/termination, reference carriers, unique holes, NLL, higher-ranked lifetimes and refinement evidence |
| Effects and resumptions (§10) | No claim | Exact-instance routing, deep handlers, quantities, replay, cancellation and terminal cleanup |
| Labels and proper tail calls (§§11–12) | Recursive ordinary call safety, not a tail-space bound | Generative destinations, protected transfers, fusion and bounded live control |
| Traits and generics (§13) | Monomorphic structural permission derivation | Kinds, substitutions, coherence, associated projections, higher ranks and bounded inference |
| Operators and conversion (§14) | Structural constant normalization for the decoded fragment | Fixity resolution, generic constants, conversion contracts and scalar operation laws |
| Unsafe memory and safe libraries (§15) | Logical heap identity and resident movement only | Physical allocation/provenance, raw operations and private invariant establishment |
| Foreign boundaries (§16) | No claim | C layouts, configured imports, callbacks, retention and cross-boundary lifetimes |
| VM/native ABI and compilation (§§17,19) | Source-to-logical-machine preservation/progress | Artifact admission, concrete representation, shared backing storage and backend refinement |
| Failures, determinism and limits (§18) | Deterministic logical steps and finite/infinite exclusivity | Distinct abort/fault/resource outcomes, host nondeterminism and bounded static solvers |

Language L01–L11 and L19–L21 intersect the current fragment only partially;
L13's clause scope is modeled but its bottom clause is not. These are not full
conformance results. L12, L14–L18 and L22–L48 require boundaries absent above.
In particular, L22 cannot be inferred from cell-retirement order, L38 cannot be
inferred from ordinary recursive safety, and L43 cannot be inferred from logical
storage identity.

Library S01–S30 require canonical generic declarations, traits, first-class
control or labels beyond the direct-call fragment. S31–S35 require scalar
operation/conversion/float laws, not merely integer literal bounds. S36–S64
require actual text, view, collection, iterator, algorithm, hashing and formatting
contracts. S65–S79 require physical/foreign storage and bounded compiler-library
contracts. S80–S96 require hosted effects, I/O and task/resumption protocols.
Owned-value lemmas support some prerequisites (for example S07/S21 wildcard or
discard restrictions), but do not establish those source-owned library APIs.
The optional compiler-library profile does not become a mandatory bootstrap
profile through this inventory; obligations apply when the profile is supported.

Audit evidence: Lean printed the actual type/source/program constructors and
admission definitions, and checked the general preservation, progress and source
behavior signatures. The independent 30-job build and 4,511-declaration axiom
audit above establish proof integrity of that scope, not its normative adequacy.
The completion audit is performed; all fourteen semantic completion families
remain open. Continue the authoritative ownership/cleanup dependency chain,
including reference semantics needed by custom Drop, rather than treating this
negative audit or another isolated lemma as whole-language completion.

## External live storage is framed through maximal source behavior

`Step.untracked_frame` now proves that an initially live cell outside every
active and retained scope survives each actual machine transition unchanged
and remains outside those scopes. Allocation freshness, resolved write targets,
and the shared release operation discharge the cases; no post-state liveness
or execution success is supplied. `Run.external_frame` composes this guarantee.

`ConfigurationTyped.behavior`, `HasType.behavior`, and all three public source
behavior contracts now expose `Configuration.ExternalFrame` on normal return
and at every divergence prefix. The guarantee preserves the entire cell,
including partial residents, owner and type, alongside the existing retirement
and live-allocation accountability conclusions.

Verification: all 30 `lake build Grounded` jobs passed. Lean axiom inspection
of both framing producers, general maximal behavior and the three source
consumers found only `propext`, `Classical.choice` and `Quot.sound`. No examples
or unit tests were added. This is the current logical owned-value machine:
scope exclusion will not suffice once values can carry references. The
reference-aware reachable-storage and loan contract remains an obligation,
as do custom Drop execution and the other completion families above.

## Retained caller cells survive actual callee execution

`Run.decompose_extension` factors arbitrary execution prefixes at the first
terminal control above a saved continuation. The previous completed-run
`Run.unextend` theorem now consumes this general producer. `Run.body_frame`
uses that factorization and external framing to preserve cells outside the
callee entry bindings through nested execution and the actual return cleanup.
`Run.call_frame` derives this isolation for every initially live caller cell
from fresh parameter allocation, without typing or termination premises.

The public source-selected invocation behavior now preserves complete caller
cells on return and at every divergence prefix. Ordered Copy/move invocation
exports the corresponding guarantee from its constructed post-input heap
through every callee prefix. Input moves are not rolled back: preservation
begins after those actual ordered input transitions. No independent runtime
analysis, assumed post-state liveness or successful-execution premise is added.

Verification: all 30 `lake build Grounded` jobs passed. Axiom inspection of
the decomposition and framing producers and both public consumers found only
standard Lean axioms. This remains direct owned-value invocation; references,
captured environments, custom Drop and the broad completion obligations remain
open. In particular, future borrowed calls must preserve permissions and
authorized effects rather than promise unconditional equality of caller cells.

## Returned owned-value calls restore all heap observations

`Run.call_heap` combines caller-cell preservation, permanent retirement and
complete allocation accounting: every address reads exactly as it did before
callee entry when the call returns. This includes absent addresses, so the
conclusion excludes residual live callee allocations rather than merely
preserving known caller cells. The allocation frontier is not reset.

Both public source invocation contracts consume this theorem. Ordered
Copy/move calls compare against the constructed post-input heap, preserving
input consumption rather than rolling it back. Their existing typed-result,
retirement and divergence guarantees remain intact.

Verification: all 30 `lake build Grounded` jobs passed; axiom inspection of
the producer and both source consumers found only standard Lean axioms.
This closes heap-observation reclamation for the current direct owned-value
fragment, not reference-bearing, captured, foreign or effectful invocation.
No broad semantic completion item is marked complete.

## First-selected pattern ownership enters the public safety invariant

`Configuration.OwnershipSafe` previously had no pattern-selection case despite
covering the other modeled disposal sites. It now requires the actual subject
typing and selected pattern ownership derivation, including the original
source-order split and failure of every preceding clause. A later matching
clause cannot supply permission for an earlier selected clause.

The existing `ArmsType.selected` producer now retains that evidence alongside
the selected body and binding derivations. Preservation and termination
consumers were migrated; `ConfigurationTyped.ownership_safe` consumes the
same product. General source-prefix soundness and maximal behavior therefore
carry structural wildcard/constant discard permission and deconstruction
authority through the authoritative `PatternType` rules, rather than a new
disposal analysis or an assumed successful cleanup.

Verification: all 30 `lake build Grounded` jobs passed. Axiom inspection of
selection, ownership safety, preservation, source-prefix soundness and maximal
source consumers found only standard Lean axioms. No examples or tests were
added. Borrowed matching and custom Drop execution remain open; this repair
does not mark the principal-ownership or pattern-callable family complete.

The runtime consequence is now explicit: `selectArm.first_unique` identifies
the selected clause itself even when distinct clauses share bodies and binding
outputs. `Configuration.OwnershipSafe.selected_pattern` recovers authority for
that exact clause. `HasType.pattern_discard_permission` consumes general
source-prefix soundness and proves zero-use permission for every reached
wildcard or constant-pattern disposal, including arbitrarily nested subjects,
under any valid typing of the actual discarded resident. It also proves that
the same runtime matcher succeeds with no bindings at that disposal site.
`Pattern.SubjectAt` is only a positional observation in the original matched
pattern and value: it assumes neither successful matching nor permission.
Success is derived from the enclosing match; resident typing and permission
are derived from the existing recursive `PatternType` authority. Thus
nondiscardable subjects cannot take these disposal paths, including inside
tuples, arrays and nominal variants. These are general theorems over programs,
execution prefixes and nesting, not examples or a second matching evaluator.
All 30 build jobs passed; the new producers and public consumer depend only
on standard Lean axioms. Borrowed matching and custom Drop remain open.

Nested binder transfer is constructive as well: `Pattern.SubjectAt.matched`
now derives the exact contiguous output segment produced by the observed
subpattern, preserving order through arbitrary nesting. `allocateBindings.at`
derives the actual cell contents and fresh identity for every input position.
`HasType.pattern_binding` consumes both producers and source-prefix ownership
safety to construct the real pattern-entry step with the exact nested resident
installed in its new binding, with its original type and activation. General
preservation establishes post-entry binding uniqueness, so the original
lexical name resolves to that exact fresh identity, not merely to some
equal-valued cell elsewhere in the heap. Neither successful allocation nor
post-state typing is an admission premise. This is
logical unbounded allocation, not a physical allocation/exhaustion theorem.
All 30 build jobs passed; inspection of both transfer producers and the source
transfer/disposal consumers found only standard Lean axioms.

## Pattern deconstruction preserves its actual source module

The runtime pattern frame previously erased its checking module. Consequently
the public ownership invariant retained only an existential permission scope,
not authority at the actual matched source location. `Expr.applyPatterns` now
records the module produced by elaboration, and the real entry transition
carries it into `Frame.patterns`. Checking requires exactly that module.
`OwnershipSafe` and `selected_pattern` no longer existentially choose a module.

All normalized/named elaboration, machine evaluation, termination, preservation,
disposal and binding consumers use the same module-bearing constructors; the
old constructor interfaces are removed. `HasType.pattern_deconstruction` proves
authority for every reached nested owned deconstruction at the module stored
in its actual frame. For nominal heads this includes declaration and field
visibility and the package authority required to open non-exhaustive enums.

`HasType.pattern_external_exact_transfer` consumes this module-specific
authority and the existing non-exhaustive ownership rule: any reached nested
external non-exhaustive owner lacking discard permission must be matched by a
whole-owner binder. It then constructs the actual entry step and fresh cell,
including successful lexical lookup and the unchanged nominal resident. Thus
the negative restriction feeds a positive runtime transfer theorem, not just
an isolated static rejection. Permission absence may be structural or explicit.
This theorem also passed the full build and standard-axiom inspection.

Verification: all 30 `lake build Grounded` jobs passed. Axiom inspection of
deconstruction, general preservation, source maximal behavior and nested binding
found only standard Lean axioms. No examples, tests or parallel authority table
were added. Borrowed matching, custom Drop and the other broad completion
obligations remain open.

## Projection transfer preserves source-module authority

Projection expressions and runtime frames now retain the module produced by
source elaboration. `Value.ProjectionCleanupSafe` retains the existing
`ProjectionType` evidence at that module along with residual disposal; it no
longer erases field-access authority. General preservation and every source
behavior consumer carry this strengthened ownership invariant.

`HasType.projection_transfer` consumes it to construct the actual field-transfer
step with the selected resident typed and the exact residual aggregate
discardable, including the hole left by transfer. Authority comes from the
real elaborated module, not an existential alternative scope. Evaluation and
termination consumers use the same module-bearing constructors.

The transfer theorem also derives disposal permission for every original
resident in any disjoint sibling path. `PathDisjoint.write_frame` proves that
the very same resident remains in the residual aggregate; the existing
descendant-disposal producer then supplies its permission. No future readiness
or assumed sibling disappearance occurs. The conclusion covers both the
declared path type and every independently valid type of the observed resident,
so type ambiguity cannot launder a nondiscardable owner. Arbitrary observing
modules may describe the path without changing the actual projection authority.

All 30 Lean build jobs passed. Axiom inspection of the transfer theorem, general
preservation and source maximal behavior found only standard Lean axioms.
No examples or tests were added. This does not implement custom destructor
execution, borrowed projection or physical cleanup; all fourteen broad
completion obligations remain open.

## Assignment authority survives RHS evaluation and restoration

Assignment expressions and frames retain their source module. The authoritative
`BindingMap.ReplacementSafe` contract now requires the destination path at that
module instead of existentially choosing an alternative permission scope.
Elaboration, evaluation, framing, termination, general preservation and source
behavior use this same fact. Existing exact and nondiscardable overwrite
rejection proofs consume the strengthened contract.

`HasType.assignment_restores` no longer assumes a completed write. After any
checked prefix reaching assignment, it constructs the actual transition and
derives mutable-binding authority, path permission at the stored module,
inserted-value typing, legal old-resident disposal, resulting heap realization,
exact readback and restored initialization, with disjoint masks unchanged.
No pre-write readiness, post-state typing or execution-success premise is added.

All 30 Lean build jobs passed. Axiom inspection covered constructive restoration,
nondiscardable overwrite rejection, general preservation and source maximal
behavior; only standard Lean axioms occur. No tests or subagents were used.
Custom Drop and reference-bearing assignment remain open, as do all fourteen
broad completion obligations.

## Reached source moves preserve a live initialization hole

`PartialValue.write_select` derives exact runtime readback from the real path
update, without typing or post-state assumptions. `StorageAddress.take.hole`
and its addressed-environment consumer distinguish an initialization hole from
retirement: the same resolved cell remains live, with its original activation
and declared type, and the moved path selects exactly `.hole`.

`HasType.move_transfers` consumes the actual move producer after an arbitrary
checked execution prefix. It constructs the transition, proves the transferred
value is the original pre-move resident, preserves the complete continuation
typing through general preservation, and exposes the concrete live-cell hole.
Both immediate rereading and retaking fail; scope, activation supply and heap
frontier are unchanged. Every typed retained caller at another activation
keeps its cells exactly and remains well typed. No completed move or future
readiness is supplied. This covers whole and partial owned-place movement.

`Initialization.Disposable.write_absent` proves residual disposal is closed
under the actual arbitrary-depth mask update, preserving nominal restrictions
and empty-shell distinctions. `PartialValue.Disposable.write_hole` pairs that
result with runtime erasure through the existing checked-path producer. The
storage and addressed move producers expose the actual old-to-new resident
update. `HasType.move_transfers` consumes this evidence and source-derived layout
and path typing: whenever the original containing resident was disposable,
the constructed moved-from resident remains disposable. No post-move disposal
or mask-realization premise is supplied. All 30 build jobs and standard-axiom
inspection of the producer, runtime bridge, source move and maximal behavior
passed after this integration.

No tests,
examples or subagents were used. These are logical owned-cell semantics, not
reference-hole restoration, custom Drop or physical memory proofs; none of the
fourteen broad completion obligations is closed.

## Immutable descendant observations cannot change or resurrect

`PartialValue.write_hole_unreadable` proves that actual erasure of any path
prevents reconstruction of the whole owner. The proof follows field replacement
and reconstruction; it does not require typing or post-state readiness.
`PartialValue.write_hole_read_before` extends the result to arbitrary observed
paths, including overlap with the erased path. Equal field positions use the
same declared child type even when field keys differ; distinct positions retain
the original child. Hole traversal never invents a readable descendant.
`StorageCell.Consumption.read_before` lifts this through the existing history,
and `AddressedEnvironment.ConsumptionFrame.read_before` connects it to lexical
lookup and actual heap reads. The whole-binding-only interfaces are replaced.

`SourceClosure.Admitted.immutable_read` consumes general source soundness and
slot preservation. Between any two execution prefixes, every path beneath an
immutable source binding is either unreadable or yields exactly its earlier
value, including across nested calls observed in the outer environment. Once
a descendant becomes unreadable, no later execution can resurrect it.
This uses preservation at the earlier prefix and consumption framing of the
actual suffix, rather than merely comparing every state to program entry.
No second history relation, successful-read premise, or future-state admission
assumption is added to the source theorem.

`PartialValue.Empty.write_hole` separately proves structural absence is
preserved by erasure. It does not confuse unreadability of a partial owner with
complete consumption, nor classify a zero-field nominal owner as absent.
`PartialValue.Empty.write_hole_selected` preserves structural absence at
arbitrary descendant paths, including ancestor and overlapping erasure. The
shared `Ty.fieldInfo_child_unique` supplies canonical child types to both
read-stability and absence proofs. `StorageCell.Consumption.empty` lifts this
through the existing history, preserving the live cell, type and activation.
`SourceClosure.Admitted.immutable_empty` consumes the generalized result between
arbitrary reached prefixes, preserving lexical identity and descendant absence.
No after-state absence or replacement cell is supplied. Missing paths are not
treated as access permission; the conclusion excludes newly inhabited children.
All 30 build jobs and standard-axiom inspection of the generalized producer,
history, source theorem and maximal behavior passed.

All 30 Lean build jobs passed. Axiom inspection of the erasure producer,
consumption lemma, source observation theorem, general preservation and maximal
source behavior reported only `propext`, `Classical.choice` and `Quot.sound`.
No tests or examples were added. This establishes arbitrary-depth observation
stability in the logical owned fragment, not reference/loan semantics or
custom destruction; all fourteen broad completion obligations remain open.

## Residual disposal survives complete immutable consumption histories

`PartialValue.Typed.open_fields` separates declared-layout opening from source
visibility; `ProjectionType.open_partial` consumes that shared producer without
changing access authority. `Ty.fieldTypes_finite_child` similarly supplies the
physical child layout to both source projections and runtime erasure proofs.
`PartialValue.Typed.write_hole` derives a matching initialization-mask update
and typed resident from every actual successful arbitrary-depth hole write.
No second source path judgment or post-state typing is supplied.

`PartialValue.Disposable.write_hole` now consumes this physical preservation
result; the existing source-move consumer is migrated. The authoritative
`StorageCell.Consumption` history preserves resident typing, live-cell metadata
and existing residual disposal permission through arbitrary compositions. Its
permission guarantee covers every checked descendant independently of siblings: 
`PartialValue.Disposable.write_hole_selected` handles descendant, ancestor and
overlapping erasure without requiring the containing owner to be disposable.
`SourceClosure.Admitted.immutable_disposable` derives entry layout from binding
typing, carries it to the earlier reached state through the actual prefix, then
constructs a selected descendant with preserved disposal permission after every
later source suffix. The result includes actual successful path selection, not
merely a conditional permission for an assumed future selection. Lexical identity,
activation and declared type remain unchanged. Neither future cleanup success
nor post-state permission is an admission premise.

The generalized erasure/history/source chain and general preservation and maximal
source behavior passed all 30 build jobs and standard-axiom inspection.

Verification: all 30 `lake build Grounded` jobs passed. Axiom inspection of shared
opening, child layout, runtime erasure, disposal closure, consumption preservation,
the source-suffix theorem, source moves and maximal source behavior reported only
`propext`, `Classical.choice` and `Quot.sound`. No tests or examples were added.
These remain logical owned-cell results: custom Drop, reverse-field destruction
execution, reference/loan semantics and physical memory are not established.
All fourteen broad completion obligations remain open.


## Explicit reverse-field destruction of sequence temporaries

Sequence discard no longer jumps directly to the next expression. The actual
machine enters a `Control.cleanup` worklist. `DisposalTask.expand` uses the
existing `Value.children` producer in reverse order and places an enclosing
shell release after its children. Shell markers contain only `Head`, not a
second runtime copy of child values. The saved expression is enabled only by
`Step.cleanupDone` on an empty worklist.

`Run.cleanup_value` proves constructive termination for every finite logical
value through these actual transitions. `Run.cleanup` handles arbitrary
pending mixtures of values and shell releases. `Evaluates.sequence` consumes
that execution rather than retaining the superseded one-step discard.

`ValueHasType.children_disposable` derives typing and zero-use authority for
every active child from the existing structural permission, including private
nominal fields and the selected enum variant. No source projection visibility
is invented for destruction. `ControlTyped.cleanup` carries permission for
each current work item; general preservation derives it at entry and preserves
it at every expansion/release. General progress, consumption framing, optional
termination, and maximal source behavior all consume the changed machine.

`SourceClosure.Admitted.cleanup` constructs completion of every reached
sequence cleanup, preserves its continuation typing, and proves disposal
authority in every later reached cleanup state. It assumes neither cleanup
success nor future-state permissions.

Verification: all 30 `lake build Grounded` jobs passed. Inspected child
permission, constructive destruction, general preservation, source cleanup, and
maximal source behavior depend only on `propext`, `Classical.choice`, and
`Quot.sound`. No tests, examples, axioms, or admission assumptions were added.

This closes destruction execution for fully initialized discarded sequence
results in the current no-hook logical fragment. Scope retirement, caller
restoration, replacement, and projection residuals still require migration to
explicit destruction of partial residents. Custom Drop, hook divergence,
physical release, and the other whole-language obligations remain open; none
of the fourteen broad completion obligations is marked complete.


## Owning projection executes residual destruction

`Value.takeField` now produces the selected position, transferred value, and
actual partial residual together. `ProjectionType.eraseProjected` proves the
residual is exactly the existing checked field erasure; `take_progress` derives
success, result typing, the selected hole, and residual disposal permission.
The read-only field lookup remains shared with ordinary access, but owning
projection no longer discards the other residents in a single result step.

`PartialValue.disposalTasks` interprets actual partial occupancy. Holes contribute
no work, whole residents enter the existing destruction machine, partial fields
are scheduled in reverse order, and their shell is released last. Its general
safety theorem consumes the authoritative residual initialization permission.
It includes uncertain static masks, private fields, empty consumed exact shells,
and the distinction between consumed shells and live zero-field nominal owners.

Cleanup now saves a typed control rather than only an expression. The projection
transition protects the selected result there while executing the residual work;
only an empty worklist restores that result. `HasType.projection_transfer` now
constructs this transition and cleanup run, rather than claiming instantaneous
projection completion. General preservation, progress, evaluation, structural
constant evaluation, optional termination, and source-admitted cleanup and
maximal behavior have migrated to the actual producer and machine.

Verification: all 30 `lake build Grounded` jobs passed. Axiom inspection of the
erasure bridge, owning projection producer, partial-worklist safety, reached
projection theorem, preservation, source cleanup and maximal source behavior
reported only `propext`, `Classical.choice`, and `Quot.sound`. No tests or examples
were added. Scope retirement, caller restoration, and replacement still require
explicit partial-resident destruction. Custom Drop, hook divergence and physical
release remain open, as do all fourteen broad completion obligations.


## Structural cleanup is inevitable in maximal source behavior

`SourceClosure.Admitted.cleanup` now proves more than existence of a completing
cleanup run. Every terminating execution from the original source entry factors
through the resumed control, and every infinite execution from that entry reaches
that exact control, environment, and continuation at a finite trace index. Thus
later source divergence cannot be confused with divergence inside the current
no-hook structural cleanup. Neither source termination nor a future execution
guarantee is an admission premise.

The proof uses general deterministic prefix results, `Run.terminal_suffix` and
`InfiniteRun.reaches`. The existing finite/infinite exclusivity theorem now
consumes the same eventuality producer instead of repeating its trace induction.
All 30 build jobs passed; inspected prefix, eventuality, exclusivity, source
cleanup and maximal source behavior proofs use only standard Lean axioms. No
tests or examples were added. This does not cover custom hooks, whose permitted
divergence must prevent later cleanup, or close any of the fourteen broad tasks.


## Replacement destroys actual old occupancy before installation

The assignment-result transition no longer overwrites the old resident. It uses
`BindingMap.selectPartial`, which resolves the ordinary address and applies the
shared field selector, to enter the existing partial-resident cleanup machine.
The replacement value, destination and continuation remain protected in
`Control.install`. Only after cleanup completes does `Step.install` invoke the
authoritative addressed write. Holes contribute no tasks; resident fields are
destroyed in reverse order, followed by their enclosing shell.

`ReplacementSafe.selection` derives the selected residual and its disposal
permission from the existing checked replacement contract. Preservation and
progress consume it at cleanup entry; installation retains the checked path,
mutability, mask restoration and continuation obligations. Heap-history, exact
cell framing, disjoint observations and lexical-shadowing consumers now track
the actual installation transition rather than the preceding cleanup entry.
Evaluation and constructive termination run cleanup before writing.

`HasType.assignment_restores` constructs the entire cleanup-and-installation run,
exposes the actual selected residual and its permission, and retains readback
and disjoint-mask guarantees. General source safety, inevitable cleanup and
maximal behavior cover the new states without a completed-cleanup or future
realization assumption.

`Run.cleanup_decompose` additionally classifies every actual cleanup prefix:
either cleanup still retains the exact original heap/environment, protected
control and caller frames, or execution has passed through that exact saved
control. `SourceClosure.Admitted.cleanup` consumes this barrier theorem. It
covers partial projection handoff and delayed installation as well as sequence
discard; no intermediate heap mutation or payload substitution is permitted.
All 30 strict build jobs and inspected barrier/source axiom closures passed.

Verification: all 30 strict Lean build jobs passed. Inspected assignment,
preservation, progress, source-cleanup and maximal-behavior proofs depend only
on `propext`, `Classical.choice`, and `Quot.sound`. No tests or examples were
added. This is structural no-hook destruction over the logical heap, not custom
Drop or physical release. Scope retirement and caller restoration still need
explicit partial-resident destruction; all fourteen broad obligations remain open.


## Remaining bindings stay realized during retirement prefixes

`BindingMap.Typed.retirement_prefix` derives typing in each actual intermediate
retirement heap for exactly the bindings whose storage identities have not yet
been retired. The remaining source context is a sublist of the original context:
its complete binding states, including initialization masks, are retained
verbatim. Neither a future realization nor reconstructed readiness is assumed.
The shared filter proof preserves both lexical and storage identity uniqueness.
`BindingMap.Disposable.retirement_prefix` carries actual residual disposal
permission through the same physical prefix. The reached-source scope theorem
now retains cleanup authority for every pending local as well as realization
for all surviving bindings; nondiscardable outer bindings are not accidentally
classified as disposable. The proof frames the original selected cells rather
than assuming later successful reads or a fresh permission derivation.
The strict 30-job build and producer/source axiom inspections passed for this
extension as well.

`HasType.scope_join_preserves_ownership` consumes this result at reached source
scope cleanup, alongside its existing ordered retirement and branch-join
guarantees. This supplies the binding-realization invariant needed to stage
per-owner destruction without retaining maps to dead cells. It does not yet
change the atomic scope/return transitions into interleaved resident destruction
and single-owner retirement. That operational cutover, custom hooks and physical
release remain open; no broad completion obligation is closed.

All 30 strict Lean build jobs passed. Inspected retirement-prefix, source scope
cleanup and maximal source behavior proofs use only standard Lean axioms. No
tests or examples were added.

`BindingMap.Typed.retire_at_progress` now constructs single-owner retirement
and removes exactly the corresponding index from both runtime bindings and
source states. It proves disappearance of the retired cell, unchanged allocation
frontier, and typing of the remaining map. The reached-source scope theorem
consumes it for a selected pending local at the head of the authoritative
release order, deriving that resident's disposal permission from the preserved
prefix contract. It does not assume successful next retirement or post-state
realization. All 30 strict build jobs and inspected producer/source axiom
closures passed. This closes the indexed binding-state transition prerequisite,
not the remaining operational scope/return destruction integration.

The reached-source prefix result now constructs the next owner rather than
accepting an indexed winner as a premise. `BindingMap.release_next` derives an
actual binding at the head of the existing `releaseOrder`; source cleanup
returns either an empty pending-local batch or that owner's live resident,
disposal permission, successful retirement and synchronized binding/state
removal. The strict 30-job build and producer/source axiom inspections passed.
This removes the conditional-selection gap without introducing a second
scheduler. The operational scope/return cutover remains open.

Next-owner selection now uses executable `BindingMap.nextRelease`: the existing
release order supplies the identity and the actual binding map supplies its
deterministic index. `release_next` derives successful selection and exact
pending membership from storage-identity uniqueness, rather than choosing an
arbitrary index. `AddressedEnvironment.retireBinding` synchronizes physical cell
retirement with removal from the runtime map. Its progress theorem transports
the corresponding source-state removal, preserves activation and both supplies,
and frames all other cells and retained caller activations. The source scope
prefix theorem consumes both executable producers and derives their results.
All 30 strict build jobs passed; inspected producer and source proofs use only
standard Lean axioms. The machine still needs staged scope/return controls that
interleave each resident's destruction with this retirement operation; no broad
completion obligation is closed.
The executable selector is also proved to stay within the remaining local
prefix. `BindingMap.nextRelease.in_prefix` derives the strict index bound from
the actual search result and prefix relation, including prefixes shortened by
previous retirements. The source scope theorem consumes this bound; the next
retirement cannot select a retained outer binding. The strict build and axiom
checks passed.

The operational cutover can preserve `ControlTyped.slots`: retirement belongs
in a continuation frame, alongside the existing scope and restoration frames,
rather than in a control that violates the unchanged-slot invariant. Such a
frame must project its one binding removal through `Frame.environment` and
the existing declaration, consumption-frame and live-scope consumers. Scope
and return completion must be derived through the resulting intermediate
states, not assumed as a final cleanup run.

`BindingMap.Typed.index` now connects the selected runtime index to its exact
source binding state and physical resident typing. `Typed.eraseIdx` preserves
the projected remaining map before physical retirement; the existing physical
retirement theorem preserves that same map afterward. The reached-source scope
theorem consumes both results, retaining the actual initialization mask rather
than reconstructing readiness. All 30 strict build jobs and inspected axiom
closures passed. This establishes the typing bridge needed by the retirement
frame, not the unimplemented operational scope/return cutover.

The constructed single-owner operation now closes back into the same retirement
prefix invariant. Its heap is exactly the result of retiring `front ++ [owner]`
from the original heap, and its binding map is exactly the original map filtered
by that extended prefix. `BindingMap.eraseIdx_filter` proves that synchronized
indexed removal deletes precisely that storage identity; injectivity prevents
another binding from disappearing. The reached-source theorem derives both
equalities alongside source-state preservation, local-index confinement and
caller framing. Thus a subsequent prefix instantiation consumes the actual
produced state, not a promised future realization. All 30 strict build jobs and
inspected axiom closures passed. The staged scope/return machine cutover remains
open; no broad completion obligation is closed.

`ConfigurationTyped.retire_scope` now preserves the complete remaining scope
continuation through a real indexed environment retirement. It removes the
corresponding local source state, decrements the scope count, preserves disposal
authority for the surviving locals, and transports retained caller frames.
`ConfigurationTyped.scope_next` constructs this operation and its fully typed
result for every nonempty typed scope; the empty alternative is exactly count
zero. The reached-source scope theorem consumes this general producer rather
than reconstructing selection or assuming its post-state continuation. All 30
strict build jobs passed, and inspected producer/source proofs use only
standard Lean axioms. These are constructive storage-operation preservation
and progress results; they do not assert a new machine `Step` or an interleaved
destruction run. The operational retirement-frame cutover remains open.

Return retirement now has the corresponding complete-continuation boundary.
`ConfigurationTyped.retire_restore` preserves the returned value, saved caller,
and all older frames through one synchronized owner retirement.
`restore_prefix` preserves that invariant across every actually executed
callee-owned retirement prefix, using pre-state activation separation to frame
callers and retaining the surviving source states verbatim. `restore_next`
constructs the canonical next retirement or proves that the callee map is empty.
`HasType.return_restores` consumes these results at every executed prefix of the
existing acquisition order. Neither intermediate caller typing nor pending
post-state readiness is assumed. All 30 strict build jobs passed; the inspected
retirement, prefix, progress, reached-source return and maximal-behavior proofs
depend only on `propext`, `Classical.choice`, and `Quot.sound`. This does not
change the atomic return machine transition or establish interleaved resident
destruction. The retirement-frame cutover and all broad completion obligations
remain open.

The same return-prefix boundary now preserves observations, not only typing.
`ConfigurationTyped.restore_prefix_consumption` frames the entire caller stack
through actual callee-owned retirement. The source return theorem composes this
with the executed source prefix, so its consumption guarantee starts at the
original source-entry environment. No intermediate observation or caller
readiness is assumed. All 30 strict build jobs and the inspected producer/source
axiom closures passed. This strengthens the storage-prefix invariant; the
interleaved destruction/retirement machine integration is still open.

Indexed local retirement also preserves the full outer consumption frame.
`BindingMap.eraseIdx_drop` relates the decremented pending-local count to the
unchanged retained suffix. `ConfigurationTyped.retire_scope_consumption` uses
that identity and actual heap framing to protect all remaining continuation
observations. The reached-source scope theorem composes this with the source
execution prefix, starting its guarantee at the original entry environment.
All 30 strict build jobs and inspected source/producer axiom closures passed.
The scope and return machine transitions still need interleaved destruction;
this closes their storage-operation observation obligation, not that cutover.

Canonical single-owner retirement now preserves the exact remaining release
queue. Filtering a typed owner map commutes with acquisition-order sorting;
removing its selected newest owner leaves exactly the old queue tail. The
constructive return producer and its reached-source prefix consumer carry
this equality for the actual produced binding map. This connects successive
indexed retirements to the existing batch order without a second scheduler
or a post-state ordering assumption. All 30 strict build jobs and inspected
axiom closures passed. Operational interleaving remains open.

The indexed and prefix operations now factor the authoritative batch return
operation exactly. Continuing restoration after one canonical retirement, or
after any executed canonical prefix, produces the same environment as the
original restoration, including its heap, caller bindings and supply. The
source return theorem derives the exact remaining queue and the same previously
constructed final environment at every prefix. It does not assume a new final
result or an intermediate realization. All 30 strict build jobs passed, with
only standard Lean axioms in the inspected producer and source closures. This
closes batch/staged storage-result correspondence for return; the machine still
needs to interleave resident destruction and retirement.

Scope exit now has the same exact factorization through canonical indexed
retirement. Removing a local shortens precisely the pending prefix while
preserving the outer suffix. Exiting the smaller scope from the actual produced
environment equals the original batch exit, including its heap, activation and
supply. General typed scope progress and the reached-source scope theorem
consume this equality. All 30 strict build jobs and inspected proof closures
passed. This supplies result correspondence for the scope machine cutover;
interleaved destruction itself remains unimplemented.

General typed scope and return states now construct complete finite canonical
storage-retirement traces. Each successful indexed retirement removes exactly
one binding. Well-founded construction therefore consumes one owner per stage,
using the existing selector and physical operation, preserving the full typed
continuation and the original batch result at every intermediate state. Scope
traces end at the exact batch-exit environment; return traces empty the callee
map and retain the same final caller-restoration result. The reached-source
scope and return theorems consume these constructions. No supplied trace or
intermediate readiness is a premise. All 30 strict build jobs passed, and the
inspected trace/source proofs use only standard Lean axioms. These finite
traces describe actual storage operations, not a new machine `Run`; resident
destruction must still be interleaved through the retirement-frame cutover.

Every stage of both reached-source traces now exposes the actual selected
resident and its disposal permission in that stage’s physical heap. The shared
`BindingMap.nextRelease.member` theorem derives pending-owner membership from
the executable selection; lexical confinement and both source trace consumers
reuse it. Permission comes from the preserved configuration invariant, not a
new readiness premise or the original resident before earlier transitions.
Canonical selection now requires only a nonempty pending lexical prefix, not
typing or global storage uniqueness. Raw indexed retirement has an exact
operational decomposition. Scope/return factorization consumes that operation
and uniqueness of the retired batch alone, independently of typed progress.
Successful physical batches themselves prove distinctness and initial liveness;
the actual-prefix order/disposal consumers derive strict acquisition order from
these facts rather than accepting an additional ordering premise. All existing
typed progress and source consumers use the migrated contracts. All 30 strict
build jobs and inspected producer/source axiom closures passed. These results
prepare the untyped completed-evaluation boundary as well as source safety.

The retirement-frame machine cutover is now integrated. Nonempty scope and
return states select the canonical newest resident, execute its existing
partial-resident cleanup, retire exactly that indexed owner, then repeat on
the resulting binding map. Empty scope/return transitions alone resume the
continuation. No atomic batch-retirement execution rule remains.

`Run.scope` and `Run.restore` construct complete interleaved executions from
successful batch storage operations; their result inversions recover exactly
the original environment and protected payload from completed staged runs.
General configuration preservation/progress, immutable consumption framing,
callee external-cell framing, evaluation composition/inversion, finite-call
termination, and reached-source cleanup guarantees use the new transitions.
Source scope/return guarantees construct `Run`, not a fictitious single `Step`.
Disposal authority comes from the current source masks and actual resident.
Indexed continuation projection retains all other source observations.

All 30 strict build jobs passed. The inspected construction, inversion,
preservation, progress, framing, source cleanup and admitted maximal-behavior
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. This
closes operational interleaving for the currently modeled structural cleanup;
custom destructor bodies, effects/divergence within destructors and the other
whole-language completion obligations remain open.

The source retirement traces now also carry an actual `Run` for every edge:
each selected resident is structurally cleaned before its indexed storage
retirement, with the protected payload and remaining scope/caller stack
preserved. Complete batch execution reuses these same per-owner constructors.
The storage trace is therefore connected stage-by-stage to the machine, not
merely related by its final heap. All 30 strict build jobs and the inspected
source-safety/maximal-behavior axiom closures passed.

`OwnershipSafe` now exposes disposal permission for the actual selected cell
at `.retire` states as well as at scope/return entry. The general preserved
configuration invariant derives this from the indexed source mask and current
resident. `HasType.retirement_preserves_nondiscardable` proves that every actual
indexed retirement preserves a cell containing an outstanding nondiscardable
descendant, including partially consumed owners. It requires neither completed
cleanup nor future termination. The strengthened fact propagates through
source admission and maximal behavior. All 30 strict build jobs passed; the
inspected ownership, source-retirement and admitted-behavior proofs use only
the three standard Lean axioms listed above.


## Selected-pattern residents execute cleanup before the body

The binding-only matcher previously lost wildcard and literal subjects:
`Step.selectedPattern` allocated the returned bindings and entered the body
without visiting the cleanup machine. A general Lean witness reproduced that
transition for every wildcard subject, rather than relying on a concrete test.

`PatternMatch` now carries both retained bindings and discarded residents.
The existing recursive matcher is the sole producer. Composition preserves
source binding order and reverses field order for disposal; failed alternatives
produce no executable cleanup. There is no second pattern walker or retained
binding-only compatibility path.

Selected entry protects the bindings in fresh storage, then executes the
matcher-produced queue through `Control.cleanup` before the body. Coverage,
first-match provenance, nested subject observation, general preservation and
progress, physical framing, evaluation construction/inversion, termination,
and source consumers all use this result. `PatternType.discarded` derives
zero-use permission for every scheduled resident from the actual source
pattern and its typed subject.

`HasType.pattern_cleanup` constructs the selected transition and cleanup run
from any reached source boundary. Every prefix either remains in cleanup with
the protected environment and continuation unchanged, or has resumed the
selected body. `SourceArmsChecked.evaluation_soundness` consumes that theorem
and exposes the actual cleanup segment and disposal authority. A general
negative proof also establishes that no pattern-entry step can jump directly
to an expression control state.

All 30 strict Lean build jobs passed. Inspected discard authority, general
preservation/progress, reached-source cleanup, decoded-source evaluation, and
admitted maximal-behavior closures use only `propext`, `Classical.choice`,
and `Quot.sound`. No unit tests, axioms, or proof placeholders were added.
This closes the selected-pattern structural-disposal omission, not custom Drop
execution or whole-language soundness. Custom destructor bodies and divergence,
and the fourteen broad completion obligations, remain open.


Cleanup ordering now holds for arbitrary execution prefixes, not only the
constructed terminating schedule. `Run.cleanup_append_decompose` proves that
a later worklist suffix stays intact while earlier cleanup is active, including
prefixes inside nested aggregate destruction. Once the prefix is exhausted,
execution factors through the exact original suffix boundary. The reached-source
`HasType.pattern_cleanup` contract and decoded-source evaluation theorem
consume this property for every split of the matcher's reverse-order resident
queue. All 30 strict jobs passed; inspected execution, source-ordering and
admitted-behavior closures contain only the standard three Lean axioms. This
does not add custom destructor execution or assume its termination.


## Ordinary owned source uses select Copy or move

A general inversion proof exposed another ownership mismatch: the former bare
named-place elaboration admitted only Copy-capable types. Nonduplicable owners
therefore required explicit `move`, contrary to language §5.3.

The existing `NamedExpr.Elaborates` relation now has complementary guarded
cases for ordinary syntax: Copy-capable types retain the existing Core read;
nonduplicable types produce the existing Core move and its authoritative mask
update. Explicit move still forces transfer without a non-Copy restriction.
No additional source walker, capability producer, or runtime operation was added.

`ordinary_exists` constructs the elaboration and static successor from only
resolved pre-state availability, using `Initialization.write_exists` and
`replaceBinding.exists` for the move case. `ordinary_progress` consumes it
through general source soundness and preservation to construct an actual typed
machine successor. The changed elaboration rule is also consumed by ordinary
function/declaration/closure admission and maximal behavior.

All 30 strict jobs passed. General inversion checks establish that ordinary
Core reads require Copy, ordinary Core moves require non-Copy, and explicit
moves always elaborate to Core moves. Inspected construction, progress, source
soundness and admitted-behavior closures contain only the standard three Lean
axioms. This establishes ordinary owned acquisition for the modeled type family;
expected-reference-driven reborrowing remains part of the unimplemented
reference/lifetime boundary, not an implicit exception in this rule.


## Constructive ordered source inputs through callee entry

Independent ordinary source admissions now compose through the existing
mode-sensitive Core `InputCompatible` contract. `recheck_input` transports
an already-selected source input using the Core framing result, preserving
source identity and its automatic or explicit Copy/move choice. It does not
postulate pending source readiness in the intermediate context.

`NamedExprsElaborate.compatible_inputs` constructs the ordered source batch.
Its execution consumer proves actual argument execution with exactly the
original pre-state observations, final binding realization, and unchanged
caller scope and activation supply. Copy overlap remains admitted; destructive
inputs use the same pre-state separation contract as Core, with no second alias
analysis or blanket ban on overlapping reads.

`NamedExpr.Elaborates.compatible_call_entry` consumes that batch through the
real named-call admission, argument execution, parameter preparation and fresh
activation allocation. It constructs the callee-entry run and proves the general
configuration invariant, terminal-or-step progress, caller consumption frame,
binding uniqueness and ownership safety for every subsequent execution prefix,
including recursive body execution and return cleanup. Neither a completed
call nor future heap readiness is supplied. The argument types are checked
against the actual selected declaration.

All 30 strict jobs passed. Inspected reconstruction, ordered source admission,
execution, callee-entry and admitted-behavior closures use only the standard
three Lean axioms. This closes the source-to-entry composition for the modeled
owned Copy/move inputs. Loan creation, reborrowing, custody-sensitive resources,
physical exhaustion and full-language input compatibility remain separate open
obligations; the logical heap theorem does not establish them.


## Ordinary acquisition returns the selected resident and records actual holes

`NamedExpr.Elaborates.ordinary_progress` now constructs a completed value
transition, rather than only an unspecified typed successor. The returned value
is typed and equals the incoming addressed read. Copy leaves the environment
unchanged. Non-Copy executes the actual `take`, cannot take the path again,
and leaves a concrete hole in the original live cell, preserving its activation
and declared type. The original resident's actual field write produces that
hole; unreadability is not substituted for a storage-retirement claim.

The producer uses existing source resolution, physical read/take progress and
source soundness. No successful operation or post-state readiness is an input.
All 30 strict jobs passed; the inspected acquisition, constructed-call and
admitted-behavior closures use only the standard three Lean axioms. This remains
a theorem of the modeled owned-value fragment, not reference reborrowing,
custom destruction, physical exhaustion or whole-language completion.

## Quantitative principals feed actual admission and acquisition

`Principal.Permits` interprets the three public intervals over owned-use counts.
`Principal.Satisfies` is interval containment, with a general characterization
of all admitted principal/request combinations. `UsePermission.Allows` now
uses that containment directly: copying requests the duplicable interval;
MayDiscard requests the affine interval. Existing checking, residual disposal,
preservation and progress therefore consume the quantitative interpretation,
not a parallel principal analysis.

`Ty.HasPrincipal` interprets the existing structural permission producer.
`Ty.principal_exists` and `Ty.HasPrincipal.unique` prove there is exactly one
such class; `Ty.HasPrincipal.satisfies` proves the public bound interpretation.
An exact-once request accepts all three ordinary principals and grants neither
Copy nor MayDiscard by itself. Classification now requires finite type evidence.
`FiniteLayout.permission_cases` constructs positive permissions or refutations
from the finite derivation, checking every field of every nominal variant and
handling empty arrays separately. It does not treat unresolved evidence as denial.

Manual declarations produce this same contract through
`DataDeclarations.PrincipalsValid.principal` and
`SourceClosure.Admitted.principal`. The no-widening consumer is migrated.
Constructive `NamedExpr.Elaborates.ordinary_progress` now returns the principal
and its bound interpretation along with the actual typed resident transition:
Copy for a duplicable principal, physical take and an initialized-cell hole for
either nonduplicable principal. Mode selection does not confuse an exact-once
request with an exact-linear principal. Its classification evidence comes from
the actual incoming addressed resident and the existing `ValueHasType.finite`
theorem, not an additional readiness premise or a parallel type traversal.
The ordinary source-elaboration producer also consumes finite type evidence
and the same `permission_cases` result. Acquisition supplies it from its
incoming resident; no separate classical permission split selects the source
Copy/move branch. The strict 30-job gate and inspected acquisition/admission
closures passed after this producer migration.

All 30 strict Lean jobs passed. Inspected interval, unique-class, bound,
acquisition, source-admission, no-widening and maximal-behavior theorem closures
use only `propext`, `Classical.choice` and `Quot.sound`. This closes the
quantitative interpretation of current ordinary owned types, not generic
constraint inference, reference/capture classes, custom Drop or whole-language
soundness. Those broader obligations remain open.

## Cleanup states carry quantitative ownership safety

`Configuration.OwnershipSafe` no longer defaults to `True` during cleanup.
It carries the current queue's disposal authority and proves zero-use permission
for each queued resident under every valid typing and principal interpretation.
`DisposalTask.Safe.zero_use` derives this from the existing permission producer
and resident-typing invariance; no future cleanup success is a premise.

The general configuration theorem and all source soundness/maximal-behavior
consumers carry this strengthened invariant. `HasType.no_exact_cleanup`
excludes a positive-lower resident from any reached cleanup queue, including
nested aggregate fields and selected-pattern discards. It covers inferred as
well as manually declared exact principals. Partial shell release still uses
its residual disposal authority; it is not incorrectly treated as destruction
of the original fully initialized owner.

All 30 strict jobs passed. Inspected zero-use, configuration ownership,
exact-cleanup exclusion and public source safety/behavior closures contain only
the standard three Lean axioms. This does not supply custom destructor bodies,
references, nonlocal cleanup or a full-language soundness result.

The same general invariant now gives quantitative authority for actual Copy
reads: every finite owned-use count is permitted under every valid typing and
principal interpretation of the read resident. `BindingMap.CopySafe.permitted_uses`
derives this through the existing addressed-read and resident-typing producer.
The noncopyable-read exclusion consumer is migrated. All 30 strict jobs and
the inspected Copy, general ownership and admitted-behavior axiom closures
passed; no new axioms or source permission premises were introduced.

## Returning the same resident cannot erase its principal

`ValueHasType.principal` transports a resident's full principal through any
other valid typing using the existing structural permission-invariance theorem.
This includes inferred exact principals and empty-array typing ambiguity.
It does not reconstruct ownership from a different field analysis.

Completed named-expression, named-program and source-closure evaluation
contracts now expose this preservation for the actual returned resident. A
by-value computation that returns the same value cannot make that value affine
merely by changing its valid result annotation. The result is conditional on
an observed completed execution; it does not assert termination, preserve the
class when an expression constructs a different value, or model references.

All 30 strict jobs passed. Inspected resident-principal, completed-source and
maximal-behavior proof closures use only the standard three Lean axioms.
Custom Drop, borrowing and the remaining full-language obligations stay open.

The finite-call source correctness chain also constructs the returned principal
from the produced resident and proves it agrees with every other valid typing
and principal interpretation of that resident. Named-expression, named-program
and source-closure consumers carry the result with their constructed execution,
heap framing and execution uniqueness. No result typing or principal is supplied
as a future-state assumption. All 30 strict jobs and inspected source-correctness
and maximal-behavior proof dependencies passed after this integration.

Principal construction now reaches unrestricted maximal behavior as well, not
only the optional finite-call corollary. `ConfigurationTyped.behavior` produces
the unique returned principal in its normal alternative from the preserved
resident; its infinite alternative keeps the existing per-prefix ownership,
framing and allocation-tracking guarantees. General Core/source behavior,
resolved invocation and compatible-input call behavior all consume that result.
Neither termination nor successful callee execution is a new premise.
The finite-call theorem reuses the same resident producer. All 30 strict jobs
and the inspected general/source/invocation behavior axiom closures passed.
This closes this result-principal integration, not custom Drop or any of the
fourteen whole-language completion obligations.

The general ownership invariant now carries consistent principal classification
for every current result and each resident in a current argument pack. This is
derived from actual control typing through the existing finite-resident
permission producer. Pack membership is shared with structural disposal; no
additional classification analysis or admission premise was added. Existing
Copy, cleanup, overwrite, pattern and indexed-retirement consumers are migrated
without weakening their guarantees. General source prefix safety and maximal
behavior now carry this fact through intermediate as well as final results.
All 30 strict jobs passed; inspected ownership, general/source safety, exact
cleanup exclusion and invocation-behavior closures use only the standard three
Lean axioms. References, retained capture environments and custom Drop remain
outside this modeled result/pack boundary.

Protected payloads and retained tuple/argument frames now share that invariant.
`Control.PrincipalConsistent` follows the actual saved control through nested
cleanup, classifies every queued enter-resident and covers installation
replacements; `Frame.PrincipalConsistent` covers already-evaluated residents
retained while later operands execute.
Control and continuation typing derive these facts from the existing resident
producer, and `ConfigurationTyped.ownership_safe` carries both through general
source prefix safety and maximal behavior. The superseded result-only inline
predicate is removed. No runtime class metadata or second permission analysis
is introduced. All 30 strict jobs passed; inspected control, continuation,
ownership and source-behavior closures contain only the standard Lean axioms.
This does not supply callable capture environments, loans or custom destructors.
Queued residents obtain their classification from `DisposalTask.Safe`; release
markers remain shell metadata, not duplicated owners. The strengthened cleanup
case passed all 30 strict jobs and the inspected general ownership, exact-cleanup
exclusion and public source-behavior dependency checks.

## Retained scopes preserve actual partial-resident typing

The previous retained-scope theorem exposed only live cells. Its replacement
`ConfigurationTyped.typed_scopes` derives each cell's actual owning activation
and `StorageCell.Typed` witness in the current heap, including partial occupancy
and finite declared layout. `BindingMap.Typed.live_typed` supplies the shared
producer; ordinary liveness is now its projection. Scope traversal consumes
the existing frame declaration transport instead of recovering storage facts
from source syntax or using a saved heap.

The public `SourceClosure.Admitted.storage_lifetime_safety` contract now exposes
these facts after every body-execution prefix. Retired-address exclusion and
maximal behavior are migrated to the stronger producer; old `live_scopes`
entry points are removed. All 30 strict jobs passed. Inspected stored-typing,
retained-scope, retirement-exclusion and source-behavior closures use only the
standard Lean axioms. This is owned storage, not a proof of reference loans or
the outstanding full-language obligations.

Typed scope realization is also a component of the authoritative
`Configuration.OwnershipSafe` invariant, alongside current/protected resident
principal consistency and retained-frame consistency. General Core and named
source prefix safety, maximal behavior and compatible-input invocation behavior
therefore preserve actual active/caller partial-storage typing at every reached
state, rather than exporting it only from the specialized function-storage
theorem. The retained-scope producer was promoted before its invariant consumer;
no duplicate derivation was introduced. All 30 strict jobs and inspected general
ownership/source/invocation behavior axiom closures passed after integration.

## Actual retirement protects inferred exact descendants

`PartialValue.Disposable.zero_use` derives the quantitative zero-use obligation
from actual readable occupancy and its principal, using the existing residual
disposal and read-soundness path. `HasType.retirement_preserves_exact_resident`
consumes it in the actual indexed retirement transition: a readable exact
descendant protects its containing cell even when the enclosing aggregate has
already been partially moved. This covers inferred as well as manually declared
exact classes without supplying nondisposability as a separate premise.

The observation is of the reached pre-state. No later termination, cleanup
success or future initialization is assumed. The stronger existing manual-shell
protection remains: this readable-descendant result does not prohibit legal
cleanup of an inferred-exact aggregate after all exact descendants have moved.
All 30 strict jobs passed; inspected quantitative retirement, general ownership
and public source-soundness/behavior closures use only the standard Lean axioms.
Custom destructor and reference restoration obligations remain open.

The same quantitative producer now rules out ancestor replacement of a
readable exact descendant after RHS evaluation.
`HasType.no_exact_resident_overwrite` derives nondisposability from the selected
descendant's principal and reached occupancy, including inferred classes and
partially moved enclosing destinations. It consumes the existing general
replacement invariant; no target read, future cleanup or extra admission
certificate is assumed. All 30 strict jobs and inspected replacement, retirement
and public source-soundness/behavior axiom closures passed.


## Branch approximation preserves exactly residual disposal authority

`Initialization.Approximates.disposable_iff` proves that disposal permission
holds after a join exactly when it held for the incoming mask. The backward
direction excludes invented destruction authority; the forward direction
preserves legal residual cleanup. Both derive from the same approximation
constructors, including every nominal variant and explicit exact-shell
consumption. No runtime realization is assumed by this static theorem.

`BindingContextApprox.disposable_iff` lifts the same equivalence to permission
to retire every binding in a context. `HasType.scope_join_preserves_ownership`
consumes both results for the actual reached branch and joined contexts and
their selected descendants. Existing unknown-state and explicit exact-shell
guarantees remain unchanged. The directional mask inductions are private;
public boundaries expose the complete equivalence. All 30 strict Lean jobs
passed; inspected context, join, general soundness and public source-soundness
closures use only the standard Lean axioms. Custom destruction, reference
restoration and whole-language completion remain open.

## Protected cleanup queues retain disposal authority before resumption

The previous control invariant classified protected residents but exported
disposal authority only for the active cleanup queue. The authoritative
`Control.OwnershipSafe` invariant now follows actual saved controls, carrying
`DisposalTask.Safe` for every pending item at every nesting depth.
`ControlTyped.ownership_safe` derives it directly from control typing;
`ConfigurationTyped.ownership_safe` carries it through the existing general
source prefix and maximal-behavior contracts. The weaker control predicate and
duplicated active-only cleanup case are removed.

`Control.Queued` observes membership in active or protected runtime queues;
it is not a second execution relation or stored analysis. Its `safe` theorem
supplies actual disposal authority. `HasType.no_exact_cleanup` now excludes
exact residents from any such queue without assuming that preceding cleanup
finishes. Principal consistency of queued residents remains derivable from
their existing typed disposal evidence, including inferred exact classes.

Branch approximation and actual partial cleanup also share
`InitializationsDisposable.of_empty`; the duplicate typed-list induction was
removed. All 30 strict Lean jobs passed. Inspected control, queue, general
soundness and public source/invocation behavior closures use only the standard
Lean axioms. Custom hooks, reference restoration and all fourteen broad
whole-language completion obligations remain open.


## Constructive residual cleanup admission for named functions

`FiniteLayout.disposable_cases` derives either disposal authority or its
refutation for an arbitrary initialization mask. It handles absence, definite
and conditional occupancy, residual tuples, every nominal variant, explicit
principal restrictions and malformed field-mask lengths. A zero-field shell
is not mistaken for consumed storage. Whole-owner permission reuses
`FiniteLayout.permission_cases`; list decisions share the promoted existing
`finite_permissions` producer. No second capability definition is introduced.

`BindingState.disposable_context_cases` composes these proofs into either
complete context disposition or a particular binding with denied authority.
`NamedFunction.BodyElaborates` is the authoritative signature/body product,
including the actual final mask. Its `disposition_cases` theorem obtains finite
types from parameter elaboration and slot preservation, then decides the masks.
`NamedFunction.Elaborates` consumes that product plus certified cleanup; it no
longer has an independent body-elaboration constructor. The former one-function
`elaborate_disposition` interface is removed.

`NamedFunctionBodiesElaborate` retains ordered body products before cleanup
certification. `NamedFunctionsElaborate.disposition_cases` constructs admission
for the exact emitted declaration list or a `NamedCleanupRejected` witness. The
witness preserves the source/emission index, chosen body derivation, final mask
and denied binding. No later function is substituted for a failed declaration.

`NamedProgramAdmitted.disposition_cases` and `SourceClosure.disposition_cases`
consume the batch decision together with ordinary declaration, namespace,
visibility and package checks. They produce the same admission and
`Program.Checked` contracts used by general prefix preservation/progress,
maximal behavior and invocation consumers, without supplied final cleanup
permission. Declaration-owner and visibility consumers are migrated to the
shared emitted-origin proof.

This decides the cleanup obligation of the supplied body elaboration; it is
not a complete type-inference algorithm or a refutation of every possible
alternative elaboration. It assumes no execution, termination, future readiness
or successful cleanup. All 30 strict Lean jobs passed; inspected emptiness,
residual/context decisions, named-function admission and public source
soundness/behavior closures use only the standard Lean axioms. Custom Drop,
reference restoration and the fourteen whole-language obligations remain open.


## Public quantity requests are intervals, not principal declarations

The previous `Ty.SatisfiesUse` interface restricted requests to the three
`Principal` constructors. Sections 7.1 and 7.6 distinguish arbitrary requested
intervals from the three legal ordinary principal declarations. The interface
now accepts `QuantityBound`: a natural lower endpoint and optional finite upper
endpoint. Public requests must be nonempty, correctly ordered intervals and
cannot be the zero-only interval. Unbounded upper endpoints are explicit.
Nominal principal declarations remain restricted to the same three classes.

`Principal.Satisfies` requires public admissibility and inclusion of every
requested count in the actual principal. `Principal.satisfies_iff` proves the
complete characterization by zero-use and repeated-use requirements.
`Ty.SatisfiesUse` interprets those requirements through the existing shared
`UsePermitted` relation. `Ty.HasPrincipal.satisfies` proves equivalence for every
interval, not only the three conventional bounds. Copy/MayDiscard requests use
this same interval interpretation; exact-once still accepts every principal
without independently granting Copy or disposal. Existing destruction and Copy
proofs now select actual count membership from the interval contract.

`NamedExpr.Elaborates.ordinary_progress` returns the generalized interpretation
alongside its actual Copy/take transition. `Value.PrincipalConsistent` also
carries it under every valid typing of each reached resident, so the general
ownership invariant and public source soundness/maximal-behavior consumers
preserve all requested intervals through current results, protected payloads
and retained value frames. No second permission inference or runtime metadata
is introduced.

All 30 strict Lean jobs passed. The checked acquisition theorem quantifies over
`QuantityBound`; inspected classification, acquisition, ownership, exact-cleanup
and source soundness/behavior closures use only standard Lean axioms. This
corrects public bound semantics; generic elaboration, custom Drop, references
and the fourteen broad completion obligations remain open.


## Nominal declarations originate in included source modules

`ModuleSource` now contains decoded `DataSyntax` declarations. Emission assigns
`DataDecl.home` from the actual included module and preserves the source
visibility, shape and explicit restriction. `SourceClosure.nominals` computes
the ordered named declaration product from that same module list; there is no
separately supplied nominal owner table.

Public `SourceClosure.Admitted` now requires the entire runtime `Program.data`
table to equal indexed nominal emission. It also rejects duplicate qualified
nominal names and invalid declaration/field visibility in the inclusion-derived
scope. `nominal_selected`, `nominal_origin` and `nominal_emitted` prove both
lookup correspondence and complete emission, including unused declarations.
`nominal_visibility` transports source visibility validity to the runtime
consumer. `source_principal` derives the declared principal at its actual
emitted identity using the existing checked resident-permission producer.

Declaration-wide cleanup admission consumes the strengthened source contract;
general source safety, maximal behavior and compatible invocation retain it.
Supplied-file permutation preserves admission with the same nominal identities.
All 30 strict Lean jobs passed. Inspected origin, complete emission, visibility,
principal, permutation, admission and public safety/behavior proof closures use
only `propext`, `Classical.choice` and `Quot.sound`.

This closes nominal source ownership, not source type-name elaboration. Decoded
field types still contain resolved Core types. Type namespace/import resolution,
generic nominal elaboration, custom Drop
and references remain open; none of the fourteen broad completion obligations
is marked complete.


## Constant identities and ownership originate in source inclusion

The independently supplied string-keyed constant table is removed. Constants
now use indexed declaration identities consistently in Core expressions,
decoded expressions/patterns, structural checking, execution and normalization.
`ConstantSyntax` retains the source name, visibility, type and decoded body;
inclusion supplies its owner. `SourceClosure.ConstantsAdmitted` requires the
entire `Program.constants` table to equal the ordered source emission, validates
visibility at that owner, and rejects duplicate function/constant names in the
same module. Different modules may retain the same source spelling.

`constant_selected` and `constant_origin` exclude ambient entries and forged
owners. `constant_emitted` proves every included constant is emitted. The
public `SourceClosure.Admitted.constant_correctness` theorem now starts from
an included source declaration, constructs its emitted identity, and derives
both its structural pattern normal form and unique actual materialization from
any caller environment. Heap and lexical-scope preservation are unchanged. No
normalization result, completed evaluation or function termination is supplied.

Public admission, soundness, maximal behavior, compatible invocation and file
permutation consumers retain exact constant emission. All 30 strict Lean jobs
passed; inspected source-origin, source constant correctness, normalization
uniqueness, admission, permutation and general public proof closures use only
`propext`, `Classical.choice` and `Quot.sound`.

This is declaration-origin integration, not a claim of full constant source
syntax. Constant path/import resolution, bare-pattern identifier versus constant
selection, generic constant schemes, alias access-path resolution, references and
custom Drop remain open. Constant bodies still enter as decoded Core expressions;
all fourteen broad completion obligations remain open.


## Alias expansion is tied to included declarations

`Aliases` and `TypeExpr.alias` now use declaration indices, not unscoped string
keys. The existing expansion, uniqueness, dependency and cycle proofs consume
these identities directly. `AliasSyntax` retains name, visibility and decoded
body; `SourceClosure.aliases` assigns its scope from the included module.
`AliasesAdmitted` requires exact body-table emission, valid visibility and
unique qualified names across nominal declarations and aliases in the type
namespace. No second expansion algorithm or runtime alias identity is added.

`alias_selected`, `alias_origin` and `alias_emitted` prove correspondence
between the actual expansion table and included declarations. The general
`SourceClosure.Admitted.source_alias_resolution` consumes complete emission:
every included alias, even unused, has an emitted identity and a unique finite
resolved type; cycles are excluded. Each alias reference in its body has an
included source declaration and well-founded expansion dependencies. The proof
uses the existing `ResolvesType.alias_dependencies`, not a separate analysis.

Source admission construction, public safety/behavior, constant materialization
and supplied-file permutation preserve the exact alias contract. All 30 strict
Lean jobs passed. Inspected source expansion/origin, missing-reference rejection,
permutation, admission, constant correctness and public soundness/behavior proof
closures use only the standard Lean axioms.

All four current declaration tables—functions, nominal data, constants and
aliases—are now tied to included source emission. This is not full source
elaboration: alias and nominal access paths/imports, visibility authorization
at each type reference, generics, and decoding into resolved declaration
identities remain obligations. No broad completion item is marked complete.


## Signed mathematical constants in Core

A general pre-change Lean proof established that every Core integer step could
produce only a nonnegative value: `Expr.integer` stored a `Nat` even though
runtime values and the scalar range contract use `Int`. This excluded all
negative decoded integer constants, including signed minima.

Core integer expressions now store `Int`. Structural checking, scalar execution,
evaluation, exact range admission, general preservation/progress and source
constant normalization/materialization consume that same number. The general
`integer_behavior` theorem derives either exact typed evaluation with the
unchanged environment and a unique result, or rejection by both typing and
execution for every continuation. There is no wraparound result.

`NamedExpr.integer` deliberately retains a natural magnitude. Its elaboration
embeds that magnitude into the signed Core domain; it does not reinterpret a
leading minus as part of a token or bypass ordinary operator resolution.
Decoded constant bodies can now carry negative mathematical values through
`ConstantChecked` and the existing source-owned constant correctness theorem.

All 30 strict Lean jobs passed. General transient proof checks established
signed-minimum execution for every target/width/environment, rejection of every
negative unsigned scalar, admission of every in-range decoded scalar constant,
and unchanged natural-magnitude source elaboration. Inspected scalar and public
constant/source correctness closures use only standard Lean axioms. No concrete
examples or permanent test fixtures were added.

This repairs the Core representation, not numeric lexing, width inference,
immediately-negated literal elaboration or operator calls. Those obligations,
and the fourteen broad completion obligations, remain open.

## Owned positional remainder patterns

Named patterns now represent one positional `..` marker with explicit leading
and trailing patterns. The declaration-selected `HeadType` determines the
omitted arity; admission rejects overfull patterns before natural subtraction.
Positional syntax is restricted to tuples, fixed arrays and tuple-shaped nominal
constructors (including zero-field shapes), not scalar constants or record fields.
Existing constructor visibility and closed-deconstruction authority still apply.

Elaboration expands the omitted segment into ordinary wildcards and feeds the
same `NamedPatternsElaborate` producer used by explicit fields. No separate
permission analysis, matching procedure or cleanup mechanism is introduced.
Duplicate-binder admission includes both explicit segments. The syntax admits
one marker per constructor pattern; nested field patterns remain independent.

`remainder_permissions` proves zero-use authority for every omitted field type.
`no_exact_remainder` rejects an omitted must-move subtree even when constructor
coverage would otherwise succeed. `remainder_matching` connects the actual
emitted Core pattern to the runtime matcher: omitted residents add no bindings
and occur in reverse order between suffix and prefix discards. Its matching
identity does not assume that either explicit segment succeeds.

The extended `NamedPattern.Elaborates.checked` is consumed by ordinary clause,
expression, function and source-closure admission. General preservation/progress,
maximal behavior and the reached-state prohibition on exact-owner cleanup retain
the same contracts. All 30 strict Lean jobs passed. A general transient proof
also constructed whole-remainder admission for every authorized positional
constructor whose fields permit disposal. Inspected new and public proof closures
use only `propext`, `Classical.choice` and `Quot.sound`; no concrete examples or
permanent test fixtures were added.

This closes owned positional remainder elaboration and matching, not parsing,
named record-field/remainder elaboration, reference-pattern ergonomics, custom
Drop, or whole-language soundness. All fourteen broad completion obligations
remain open.

## Declaration-ordered named record patterns

Decoded named patterns now carry nominal record identities, variant tags and
source field-label/subpattern pairs. Admission checks distinct supplied labels
and resolves every supplied label through the selected constructor schema's
existing `Fields.index`. Unknown labels cannot silently disappear.
`recordPatternFields` emits subpatterns in declaration order, selecting supplied
subpatterns by label and expanding omitted fields to ordinary wildcards.

The same `NamedPatternsElaborate` allocates clause bindings and checks field
ownership. The existing clause admission checks duplicate binder names across
all supplied subpatterns. No second matching, ownership or cleanup analysis was
added; the resulting Core node is consumed by existing coverage, first-match,
execution, preservation/progress and public source-behavior proofs.

`record_field` connects a supplied named subpattern to its actual declaration
index, allocated lexical scopes and runtime subject observation. `record_omitted`
derives both zero-use permission and membership of the actual omitted resident
in a successful match's discard queue. `no_exact_record_omission` rejects an
omitted exact-owned field, including a zero-field nominal resource. Visibility
and closed-deconstruction authority are unchanged.

All 30 strict Lean jobs passed. General transient proofs constructed admission
for every authorized record whose omitted fields permit disposal and checked
whole-record matching's reverse-order discard result. Inspected record and public
source safety/behavior closures use only the standard Lean axioms. No concrete
examples or permanent test fixtures were added.

This is decoded record-pattern elaboration, not a parser or constructor-path
resolver. Surface remainder-marker validation, reference-pattern ergonomics,
custom Drop and all fourteen broad completion obligations remain open.

## Named record field permutation preserves execution

`recordPatternFields.permute` proves that unique source field labels may be
permuted without changing declaration-order normalization. Duplicate-label
rejection is essential to the lookup proof; it is not replaced by first-wins
normalization. `NamedPattern.Elaborates.record_permute` preserves the exact Core
pattern, allocated binding identities and final lexical scope.

`NamedArmsElaborate.record_permute` carries this through a top-level record
pattern in any clause position, preserving the body, incoming/final masks,
coverage history and first-match priority. `NamedExpr.Elaborates.record_permute`
then preserves the entire pattern-call expression's Core and final masks.
Arguments and clause order are unchanged. The same Core execution therefore
supplies matching, cleanup and public soundness/behavior after permutation;
no alternative evaluator or assumed execution equivalence is introduced.

All 30 strict Lean jobs passed. Inspected permutation, source safety, maximal
behavior and compatible-call proof closures use only standard Lean axioms.
This strengthens the decoded record-pattern boundary; it does not close parsing,
references, custom Drop or any of the fourteen broad completion obligations.


## Source-ordered named record construction

Decoded named record expressions now elaborate their initializers in written
order through the existing Core binding machine. Each result enters a fresh
anonymous lexical binding. Only the generated moves are reordered into the
selected declaration's field order. Positional source construction now requires
a tuple schema; it cannot bypass record-label admission.

One RecordConstructor witness supplies the actual declaration, record schema,
finite layout and constructor/field visibility. Label permutation against that
schema, together with its derived uniqueness, rejects missing, unknown and
repeated labels. recordMoves.ordered relates every declaration index to the
same-name source-produced temporary. The terminal generated move list is
checked by HasTypes; every temporary's final mask must be absent. There is no
Copy or discard requirement on an initialized field merely to assemble it.

SourceScope uses optional spellings with the same fresh identity allocator for
named bindings and anonymous temporaries. enter_anonymous_resolve proves that
these temporaries cannot shadow source names. Named patterns, parameters and
ordinary bindings use the migrated named entry contract.

NamedExpr.Elaborates.checked consumes the complete record-building derivation
in its mutual proof, connecting it to existing source safety, maximal behavior,
result ownership and compatible-invocation consumers. Evaluates.bind_iff
inverts actual machine runs, including scope retirement;
NamedRecordBuild.first_execution extracts the first initializer's execution and
the remaining source-order continuation in its actual output heap. No future
successful execution is an admission premise and no alternate evaluator is
introduced. All 30 strict Lean jobs passed. Inspected transfer, label, ordering,
hygiene and public soundness/behavior proofs use only propext, Classical.choice
and Quot.sound.

This closes the decoded named-record construction cutover, not textual parsing,
constructor-path resolution, references, custom Drop or whole-language soundness.
All fourteen broad completion obligations remain open.

## Record execution exposes its actual assembly cut

Evaluates.construct_iff derives the selected nominal identity, exact variant
tag and ordered resident evaluation from the machine run. Nominal result typing
alone would not establish preservation of the selected variant.

NamedRecordBuild.assembly carries this inversion through every generated
initializer binding. It extracts an actual run prefix to the declaration-ordered
move list, the move-list evaluation and a suffix that constructs the result and
retires exactly one generated scope per source initializer. Intermediate heaps
and the pending constructor/scope stack come from the execution; none is an
admission assumption. NamedExpr.Elaborates.record_execution exposes this at the
source boundary and consumes recordMoves.ordered for declaration-indexed
source-temporary correspondence.

All 30 strict Lean jobs passed. The new inversion, assembly and source execution
proofs, together with public source soundness and behavior, use only the standard
Lean axioms. This strengthens execution fidelity of the admitted decoded record
boundary; all fourteen whole-language completion obligations remain open.

## Bottom values and source-admitted infinite behavior

Ty.never now represents the language's uninhabited bottom type. FiniteLayout
and UsePermitted treat it as a finite structural type; no ValueHasType rule
constructs a resident of that type. ValueHasType.not_never establishes the
impossibility generally, not by enumerating programs. Residual-disposal
classification and the existing general preservation/progress consumers have
been migrated.

HasType.never_behavior eliminates the normal alternative of the existing
maximal-behavior theorem using value impossibility. It derives an actual
InfiniteRun, preserving configuration typing, the consumption frame, ownership
safety, external storage and tracking of newly allocated live cells at every
prefix. SourceClosure.Admitted.never_behavior consumes the real elaboration
and declaration admission. Neither theorem assumes divergence or supplies a
normal output environment. This infinite-only conclusion is specific to the
current fault-free fragment; adding abort, fault or resource outcomes requires
extending the outcome theorem, not treating those outcomes as divergence.

All 30 strict Lean jobs passed. The inspected bottom and public source
soundness/behavior proofs depend only on propext, Classical.choice and
Quot.sound.

The next boundary remains nonreturning expression/branch composition. HasType
and ArmsType still index checking by a FlowContext for normal completion;
ArmsType.clause requires local disposal and a normal environment join for every
body. Bottom-valued calls are now expressible and cannot return, but this does
not yet admit a bottom body in an arbitrary expected result position or exclude
it from normal branch joins. Repair that authoritative checking/continuation
contract with an explicit nonreturning outcome and migrate source elaboration,
continuation typing, preservation and progress together. Do not coerce bottom
by manufacturing a normal post-state, erase pending owners, or interpret abort
as ordinary cleanup. L13 and all fourteen whole-language completion obligations
remain open.

## Nonreturning execution preserves its pending continuation

InfiniteRun.extend and InfiniteRun.extend_prefix establish exact operational
composition beneath an arbitrary pending stack. Every finite run from that
extended state is a prefix of the extended infinite run and exposes the same
pending frames verbatim. InfiniteRun.no_resume rules out delivering an inner
terminal result to those frames, including when the continuation itself would
diverge. Infinite execution of the whole machine alone would not establish
that stronger exclusion.

HasType.never_continuation_prefix derives the inner infinite run from bottom
checking and carries configuration typing, consumption framing, ownership
safety, external framing and allocation tracking into every observed prefix.
SourceClosure.Admitted.never_continuation_prefix and never_no_resume consume
actual source admission and elaboration. No future state, successful cleanup,
normal output value or independently supplied divergence is assumed. Pending
frames remain intact; arbitrary pending frames are not thereby certified as
well typed and receive no permission to dispose values.

All 30 strict Lean jobs passed. New operational and source proofs, together
with public soundness/behavior, use only propext, Classical.choice and
Quot.sound. This closes continuation isolation for already bottom-typed bodies.
The static nonreturning-outcome cutover, bottom elimination and mixed normal/
diverging branch admission remain open, as do the fourteen completion families.

## Return-sensitive function cleanup admission

FunctionChecked.body and NamedFunction.Elaborates now produce the same
ReturnDisposition consumed by ConfigurationTyped.invoke and FrameTyped.restore.
The returning alternative requires ordinary residual disposal. The nonreturning
alternative requires the actual declared result to be bottom; it does not grant
zero-use permission to any parameter or local resident.

The source disposition decision now admits bottom bodies without an impossible
return-cleanup obligation. NamedCleanupRejected explicitly excludes bottom
results and retains the same indexed source/body/failed-binding evidence.
NamedFunction.BodyElaborates.bottom_admitted proves general admission for every
already elaborated bottom body, independent of its residual masks.

ReturnDisposition.on_return consumes the actual typed returned value and
recovers ordinary disposal permission; its nonreturning case is impossible by
ValueHasType.not_never. Actual restore-owner cleanup and OwnershipSafe consume
that result. Retirement and retained-frame transport preserve the same
return disposition. No cleanup transition was removed or suppressed, and normal
returning functions still require full disposal certification.

All 30 strict Lean jobs passed. The new admission and return-permission proofs,
the source disposition decision, public soundness/behavior and continuation
nonresumption theorem depend only on the standard Lean axioms. This repairs
the function-return boundary, not arbitrary expected-result bottom elimination,
lexical binding exits or mixed returning/diverging clause joins. Those consumers
still require coordinated migration; all fourteen completion families remain open.

## Shared return-sensitive lexical disposition

The same ReturnDisposition now governs HasType.bind, ArmsType.clause,
FrameTyped.bind and FrameTyped.scope, rather than leaving lexical exits on an
independent unconditional disposal path. Named expression/clause elaboration
and SourceScope.bind_checked produce that contract. Generated record temporaries
use its ordinary returning alternative with the existing absent-mask proof.

Scope-owner cleanup derives its permission from the actual typed returned
value through ReturnDisposition.on_return. Scope retirement restricts the same
disposition to remaining locals; OwnershipSafe uses the same permission producer.
Bottom-typed lexical bodies can therefore retain nondiscardable locals during
infinite execution without gaining permission to clean them up. No runtime
step changes, fake return value or absent-mask fabrication is involved.

All 30 strict Lean jobs passed. Public source soundness, maximal behavior,
nonresumption, no-exact-cleanup and record-execution proofs were checked and use
only standard Lean axioms. Mixed normal/diverging clauses still require a
return-sensitive result/environment join; their current common-result type and
BindingContextApprox premise remain unchanged. Arbitrary expected-result bottom
elimination and the fourteen completion families remain open.

## Mixed returning and bottom clause joins

ReturnJoin is now the authoritative clause result/environment contract.
A returning branch retains its exact result type and BindingContextApprox;
a bottom branch contributes neither a runtime result nor a normal mask join.
Both preserve declaration slots, which remain necessary for retained-storage
framing. ReturnJoin.on_return derives the normal relation from an actual typed
resident; the bottom alternative is impossible by ValueHasType.not_never.

ArmsType.clause, its selected-body theorem, NamedArmsElaborate.clause and the
physical FrameTyped.scope consume that same contract. Scope return preservation
uses the derived normal relation. Declaration/consumption framing uses only
slot equality. Reached-scope ownership and retirement proofs derive normal mask
approximation from the actual returned value rather than assuming it for every
clause. Termination and source pattern consumers carry the selected branch's
own result type. Runtime steps are unchanged.

SourceClosure.Admitted.nonreturning_suffix composes an observed prefix reaching
an admitted bottom source body with its proved infinite execution under the
actual pending scope/caller frames. The enclosing caller need not have bottom
result type. The observed prefix is a theorem premise about execution, not a
source-admission or progress premise.

All 30 strict Lean jobs passed. Inspected return-join, public source soundness,
maximal behavior, nonreturning-suffix and no-exact-cleanup proofs depend only on
propext, Classical.choice and Quot.sound. This closes mixed clause joins for
the current admitted fragment, not arbitrary expected-result bottom elimination.
All fourteen whole-language completion families remain open.

## Bottom bodies against declared function results

FunctionChecked.body and NamedFunction.BodyElaborates now retain the actual
inferred body result separately from the declared signature. The same ReturnJoin
used by clauses validates that boundary. Cleanup admission uses the actual body
result, so a bottom body is admitted against any finite declared result without
acquiring disposal authority. Ordered body products and rejection witnesses now
retain that actual result alongside their final masks; no second elaboration
chooses different evidence for cleanup.

ConfigurationTyped.invoke and FrameTyped.restore consume that join. Actual
restoration derives declared-result typing from the returned resident;
retirement preserves the result coercion with ReturnJoin.same_context while
independently restricting cleanup permission. Constant invocation uses the
identity join. General preservation, progress, finite-call correctness and
source behavior consume the migrated function contract. Runtime steps remain
unchanged.

NamedFunction.Elaborates.bottom proves the general source admission rule.
FunctionChecked.evaluation_result proves that every actual returned body value
has the declared result type. Public function_soundness exposes inferred-body
prefix typing together with the join and this declared-result guarantee; its
storage_lifetime_safety consumer preserves the existing storage conclusions.

All 30 strict Lean jobs passed. Inspected source admission, cleanup decision,
declared-result, public soundness/behavior, storage-lifetime and no-exact-cleanup
proofs use only propext, Classical.choice and Quot.sound. This closes the
function-result boundary, not bottom elimination in every expression operand.
All fourteen whole-language completion families remain open.

## Whole-call divergence for bottom bodies with normal signatures

HasType.call_bottom_behavior derives an infinite execution of the complete
call from ordinary caller admission and a bottom-typed selected body. It does
not assume argument termination or body entry. General maximal behavior supplies
the alternatives; a putative normal run exposes actual argument evaluation,
parameter preparation and fresh binding storage. Body preservation would then
produce a resident of bottom type, which ValueHasType.not_never excludes.

NamedFunction.BodyElaborates.checked_body is shared by function admission and
the public SourceClosure.Admitted.bottom_function_call consumer. The source
theorem retains configuration typing, consumption framing, ownership safety,
external-storage protection and allocation tracking at every infinite prefix.
It also excludes resuming any pending stack with a terminal result, including
when the selected function has an ordinary declared return type.

All 30 strict Lean jobs passed. Inspected whole-call and source-call divergence,
public soundness/behavior and storage-lifetime proofs use only propext,
Classical.choice and Quot.sound. Bottom elimination in arbitrary expression
operands and all fourteen whole-language completion families remain open.

## Expected types for ordered operands

HasTypes.cons now retains the operand's inferred type and a ReturnJoin to its
expected argument type. NamedExprsElaborate.cons produces the same evidence;
FrameTyped.argumentHead consumes it. The machine constructs an argument value
at the expected type only after an actual return. Bottom contributes no value,
no disposal permission and no claim that later operands execute. Runtime
transitions are unchanged.

General preservation, structural evaluation, finite-call execution, ordered
ordinary-input observations and source checking have been migrated. Existing
compatible Copy/move admission uses identity joins and retains its pre-state
observation theorem. Source arrays, constructors and pattern/direct-call input
lists use the shared ordered relation rather than a separate coercion analysis.

NamedExprsElaborate.bottom_operand admits bottom at any argument position using
its real prefix and suffix derivations. HasTypes.bottom_no_evaluation derives
intermediate readiness from an observed prefix and rules out completed packs.
HasType.call_bottom_argument_behavior derives whole-call divergence without
assuming prefix termination. SourceClosure.Admitted.bottom_argument_call uses
the same source products to construct the actual selected call's admission and
prove infinite behavior, prefix safety and pending-stack nonresumption.

All 30 strict Lean jobs passed. Inspected operand/source-call proofs, public
soundness/behavior, compatible-call behavior and no-exact-cleanup use only
propext, Classical.choice and Quot.sound. This closes expected-type admission
for ordered operand lists; binding initializers, assignment values and other
scalar expected positions still require migration. It does not make unreachable
suffix checking disappear. All fourteen completion families remain open.

## Bottom initializers through source annotations and record fields

HasType.bind and FrameTyped.bind retain the initializer's inferred type and
consume ReturnJoin at actual binding installation. Source Annotation moved to
the checking layer: absent annotations preserve the inferred type; explicit
annotations resolve the expected type and use that same join. The old exact-type
annotation path has been removed. SourceScope.bind_checked, finite-call
execution, source checking and general preservation consume the new contract.

NamedRecordBuild.field also keeps the inferred initializer type and joins it to
the selected field's declared type. Generated temporary binding uses the same
Core rule. Its first-execution theorem exposes the inferred type and join;
source-ordered evaluation, declaration-ordered movement and actual constructor
assembly remain proved, not assumed.

SourceClosure.Admitted.bottom_initializer constructs admission for an explicitly
annotated bottom initializer and proves whole-binding divergence, prefix
ownership/storage safety and nonresumption of pending frames. No initialized
local or successful body execution is supplied. All 30 strict Lean jobs passed;
inspected initializer, record execution, public soundness/behavior and
no-exact-cleanup proofs use only propext, Classical.choice and Quot.sound.

This migrates expected initializer types, not unreachable-suffix admission:
the body still has a static checking derivation and return-disposition obligation.
Assignment values and other scalar expected positions remain to be migrated.
All fourteen whole-language completion families remain open.

## Assignment RHS return joins and physical replacement safety

Source assignment, SourceScope.assign_checked, HasType.assign and the actual
assignment frame now share ReturnJoin from the inferred RHS type to the selected
destination type. The physical install control still requires a real value of
the destination type; preservation derives it only from an actual RHS return.
Replacement permission, partial-initialization masks, writable-place checks and
cleanup-before-install order remain unchanged. Finite-call execution and the
general assignment replacement proof consume the same join.

HasType.assign_bottom_behavior composes the actual assignment-entry transition
with infinite RHS execution under the pending assignment frame. A completed
assignment is impossible. SourceClosure.Admitted.bottom_assignment carries this
through source admission to whole-assignment divergence, prefix ownership and
storage safety, and nonresumption of any pending outer continuation.

All 30 strict Lean jobs passed. Inspected assignment divergence, public source
soundness/behavior, no-exact-cleanup and no-exact-resident-overwrite proofs use
only propext, Classical.choice and Quot.sound. No operational rule or disposal
permission was weakened.

Unreachable-suffix admission is still restrictive: a bottom RHS does not yet
remove static obligations on the hypothetical destination or continuation.
This change repairs expected RHS typing, not that separate flow boundary.
Other scalar checking contexts and all fourteen completion families remain open.

## Disposal obligations follow actual initializer and RHS return

Binding cleanup admission is now guarded by the initializer's inferred type
being non-bottom. Assignment replacement permission has the corresponding RHS
guard. These guards are static type propositions, not supplied execution or
value evidence. Source elaboration, Core checking and their actual pending
frames carry the same contracts. A returned resident proves its inferred type
is non-bottom, discharging the guard before ordinary scope cleanup or replacement
permission can be consumed. Install control and cleanup tasks retain their
unconditional physical safety requirements.

SourceClosure.Admitted.bottom_initializer no longer requires disposal permission
for the never-created local. SourceClosure.Admitted.bottom_assignment now
constructs the source admission from resolution, place typing, bottom RHS and
continuation derivations without disposal permission for the old resident.
Both results include whole-expression divergence, prefix safety and outer-stack
nonresumption. This admits these nonreturning operations even when their local
or destination resident is nondiscardable; it does not authorize destruction.

All 30 strict Lean jobs passed. Both strengthened source theorems, public source
soundness/behavior, no-exact-cleanup and no-exact-resident-overwrite were inspected
and use only propext, Classical.choice and Quot.sound. No runtime step changed.

The remaining unreachable-flow boundary includes static continuation and
hypothetical mask derivations, propagation of nonreturning outcomes through
compound expressions, and outer function cleanup admission. All fourteen
whole-language completion families remain open.

## Sequential bottom propagates into function return admission

Ty.sequenceResult is the shared result composition for source sequences, Core
sequence checking and sequence frames. A bottom first expression makes the
whole sequence bottom; otherwise the tail supplies the result type. At the
actual sequence-result transition, the returned value proves the first type is
non-bottom, so preservation recovers the tail's type before entering cleanup
and the continuation. No bottom value or normal-return mask is manufactured.

SourceClosure.Admitted.bottom_sequence derives source admission and infinite
execution with all prefix ownership/storage guarantees and pending-stack
nonresumption. NamedFunction.Elaborates.bottom_sequence carries that inferred
bottom into declared function admission, without a normal-exit cleanup witness
even when the syntactic continuation has a normal result. Thus outer cleanup
admission now recognizes this compound nonreturning case through its existing
authoritative result contract rather than an independent divergence analysis.

All 30 strict Lean jobs passed. Inspected sequence/function admission, source
behavior, function soundness and no-exact-cleanup proofs use only propext,
Classical.choice and Quot.sound. Continuations still require static checking;
propagation through other compound forms remains open. All fourteen completion
families remain open.

## Assignment result propagation uses sequential composition

Source assignment, Core assignment and its pending frame now use the same
Ty.sequenceResult as ordinary sequencing. Bottom on the RHS makes the entire
assignment bottom, rather than preserving a fictitious normal continuation
result. The actual return transition derives the ordinary continuation result
from its returned RHS resident before cleanup/install. SourceScope.assign_checked
and general preservation consume this contract.

SourceClosure.Admitted.bottom_assignment now concludes source elaboration at
bottom and preserves that type at every prefix. Its existing divergence and
pending-stack exclusion proof remains valid. The inferred bottom can therefore
feed NamedFunction.Elaborates.bottom and the existing return-disposition path;
no separate nontermination table or new runtime rule is introduced.

All 30 strict Lean jobs passed. Inspected assignment/source behavior, function
bottom admission and no-exact-resident-overwrite proofs use only propext,
Classical.choice and Quot.sound. Other compound forms and unreachable static
continuation checking remain open, as do all fourteen completion families.

## Binding and named-record result propagation

Source bindings, Core bindings and their pending frames now compose initializer
and body results with Ty.sequenceResult. The actual binding-return transition
recovers the body's normal type from its real initializer value before creating
local storage. SourceScope.bind_checked and source checking use the same result.
SourceClosure.Admitted.bottom_initializer now concludes bottom typing for the
whole binding, so outer function return admission sees the unreachable exit.

NamedRecordBuild now carries its inferred result type as an authoritative index.
The terminal constructor supplies the selected nominal type; each source-order
initializer composes its type with the remaining build through the same Core
binding rule. Named source record elaboration consumes that result rather than
forcing every build to be nominal. NamedRecordBuild.result_shape proves that
inference produces only bottom or that exact selected nominal identity.

The first-execution theorem retains both initializer and continuation types and
their composition equality. Actual assembly and record-execution proofs are
migrated: completed executions still contain declaration-ordered transfers,
the selected constructor and generated-scope retirement. General preservation,
source soundness/behavior and no-exact-cleanup consume the new contracts.

All 30 strict Lean jobs passed. Inspected result-shape, record execution,
bottom-initializer and public safety proofs use only propext, Classical.choice
and Quot.sound. Runtime transitions are unchanged. Operand-list outcome
propagation and unreachable continuation checking remain open, as do all
fourteen whole-language completion families.

## Tuple-head result composition

Tuple checking, source elaboration and the physical tuple-head frame now use
Ty.sequenceResult for the head computation. A bottom head makes the entire
tuple expression bottom rather than inventing a normal tuple result. On an
actual head return, its typed resident recovers the ordinary tuple result before
the machine evaluates the tail. Structural termination uses the same witness.

SourceClosure.Admitted.bottom_tuple_head derives source admission, infinite
execution, prefix ownership/storage safety and pending-frame nonresumption from
general source soundness. It assumes no tuple resident or tail execution.
All 30 strict Lean jobs passed; the new theorem and inspected public soundness,
behavior and cleanup proofs use only propext, Classical.choice and Quot.sound.
Runtime transitions and cleanup permissions are unchanged. Outcome propagation
from an operand list (including tuple tails) and unreachable-continuation
checking remain open, along with all fourteen completion families.

## Projection operands use actual return evidence

HasType.project, source projection elaboration and FrameTyped.project retain the
operand's inferred type and use ReturnJoin to the selected aggregate type.
Residual disposal authority is guarded by the operand being non-bottom. The
whole projection result uses Ty.sequenceResult. Neither a projected field nor
an aggregate requiring disposal is fabricated for a nonreturning computation.

Actual projection progress, preservation, structural and finite evaluation,
and the general cleanup-safety proof discharge both conversion and disposal
from the returned resident. Field selection, visibility and residual-mask
checking remain mandatory. Runtime projection and cleanup steps are unchanged.
SourceClosure.Admitted.bottom_projection proves admission, whole-expression
infinite execution, prefix ownership/storage safety and pending-stack isolation
without aggregate disposal permission or a successful execution premise.

All 30 strict Lean jobs passed. Inspected bottom-projection, public source
soundness/behavior and no-exact-cleanup proofs use only propext,
Classical.choice and Quot.sound. General operand-list outcome propagation,
unreachable continuation checking and all fourteen completion families remain
open.

## Returned record types preserve nominal identity

SourceClosure.Admitted.record_return_type connects the inferred record-result
index to actual execution. General evaluation soundness supplies the returned
resident, excluding bottom; NamedRecordBuild.result_shape then fixes its type
to the selected nominal identity. No successful execution or resident is added
to source admission. All 30 strict Lean jobs passed, and the public theorem
uses only propext, Classical.choice and Quot.sound. This closes the returning
side of the record result-index migration, not operand-list outcomes or any
of the fourteen still-open whole-language completion families.

## Shared maximal behavior for scalar control and operand packs

ConfigurationTyped.maximal_behavior now constructs a terminal execution or an
infinite execution for either ResultType through the same preservation/progress
producer. The existing scalar ConfigurationTyped.behavior consumes it rather
than retaining a separate terminal-or-infinite construction. Scalar principal
uniqueness and return-retirement guarantees are preserved.

HasTypes.behavior derives a returned typed pack with realized storage, issued
activation, ownership safety, exterior framing and allocation tracking, or an
infinite ordered-pack execution preserving the same prefix invariants. It does
not assume argument termination or an output environment. HasTypes.bottom_behavior
excludes normal completion when any ordered operand is bottom, deriving the
intermediate readiness from actual prefix execution only when needed.

Whole-call bottom-argument behavior now composes this actual infinite pack run
with the real call setup step and pending callee frame. The prior proof by a
separate whole-call behavior split is removed. The public source call theorem
consumes that composition. SourceClosure.Admitted.bottom_operand_pack additionally
constructs source pack admission and proves divergence and pending-stack
nonresumption directly, without inventing argument values or granting disposal
rights to retained owners.

All 30 strict Lean jobs passed. Inspected shared maximal behavior, pack behavior,
whole-call composition and public source proofs use only propext,
Classical.choice and Quot.sound. This closes operational maximal behavior for
ordered packs in the admitted fragment. It does not yet give HasTypes a static
normal-result outcome index or propagate that index through aggregate/call
result inference. That migration, unreachable continuation checking and all
fourteen whole-language completion families remain open.

## Terminal operand packs retire their temporary storage

Run.terminal_retires_all generalizes the authoritative allocation-retirement
proof to either terminal result form. It derives an empty continuation from
Terminal, then combines preserved outer scope with actual allocation tracking.
Scalar returns and completed operand packs both retire every storage identity
allocated during the run. No post-state retirement assumption is introduced.

The scalar-only Run.return_retires_all is removed and all real consumers are
migrated, including call-heap restoration and public function behavior.
ConfigurationTyped.maximal_behavior produces terminal retirement once; scalar
behavior and HasTypes.behavior consume that same result. The pack's normal
alternative now proves retirement, not merely tracking of temporary cells.
Infinite prefixes retain their live-allocation tracking guarantee.

All 30 strict Lean jobs passed. Inspected terminal-retirement, maximal behavior,
pack behavior and public source safety proofs use only propext, Classical.choice
and Quot.sound. This concerns the admitted value/storage fragment; references,
raw allocations and other whole-language completion families remain open, as do
static operand-outcome propagation and unreachable continuation checking.

## Source-admitted ordered operand behavior

SourceClosure.Admitted.operand_behavior exposes the complete ordered-pack
behavior directly from named source elaboration and ordinary closure admission.
The normal alternative has actual typed values, realized output storage,
framing and retirement of temporary allocations; the infinite alternative
retains typing, ownership, framing and allocation tracking at every prefix.
The existing public bottom-operand-pack theorem now consumes this shared source
behavior. No operand termination or successful output is assumed by admission.

All 30 strict Lean jobs passed. Inspected source operand behavior and its bottom
consumer use only propext, Classical.choice and Quot.sound. The result remains
bounded to the current admitted fragment: static normal-result outcome indexing,
unreachable-continuation checking and fourteen completion families remain open.

## Immediate integration boundary: static ordered-pack outcomes

The operational pack boundary is proved; another execution wrapper does not
repair the remaining static information loss. HasTypes.cons currently records
an inferred head type only inside its premise, then exposes solely the expected
operand types. Result inference therefore cannot see a bottom operand through
that judgment. The next coherent migration must change this authoritative
judgment and its consumers together, not add a source walker or fact table.

Planned contract: give HasTypes and NamedExprsElaborate an explicit completion
index while keeping expected resident types separate. A nil pack completes
normally; cons composes the head's inferred result with tail completion.
Using the existing Ty.sequenceResult algebra, unit can represent normal pack
completion and never nonreturning completion. Establish that these are the only
indices derivable and that an actual returned pack implies normal completion.
Do not default the new index to normal at old call sites.

Carry completion through ControlTyped.arguments, ResultType.many and the
argument-head/tail frames. Actual ControlTyped.results supplies normal
completion. Tuple tails, arrays, constructors, calls and pattern applications
must compose that outcome with their normal result type. Keep selected callable
identity and declared result separate from the calling expression's inferred
result: migrate HasType.call_signature and its actual-execution consumers.

Migrate mutual induction motives, structural termination, finite evaluation,
ordinary compatible-input producers, source list append/bottom admission,
NamedRecordBuild.finish and public source behavior. A normal operand prefix
must derive its intermediate storage from actual execution; no pending
post-state readiness or disposal permission may be assumed. The existing
maximal behavior, allocation retirement and bottom-pack proofs are acceptance
consumers, not substitutes for the new producer-to-consumer connection.

This is a pending design, not an implemented outcome index. Unreachable-flow
checking and all fourteen whole-language completion families remain open.

Ordered-completion algebra prerequisites now check: Ty.sequenceResult.assoc
and Ty.sequenceResult.never_right. NamedRecordBuild.result_shape consumes the
absorbing-bottom law, preserving its public actual-record-return consumer.
All 30 strict Lean jobs passed; the algebra proofs use only propext and the
inspected record proofs use only standard Lean axioms. These are prerequisites,
not the indexed-judgment migration; no completion item is closed by them.
