# Grandiose Ownership/Control MIR and Optimizer Design

Status: normative compiler-backend design companion to
[architecture.md](architecture.md) and [bytecode.md](bytecode.md). The language
semantics remain governed by
[the language core](../glorious-branded-environment-core-spec.md).

This document fixes the representation and pass contracts used between Typed
Core and bytecode. “MIR” below means this representation after Typed Core has
been type checked; it is not a second source-language type system.

## 1. Design goals and phase boundary

MIR must simultaneously make these already checked facts explicit:

- control flow and value joins;
- left-to-right evaluation order;
- ownership, partial moves, initialization, and loans over places;
- normal, cleanup, label, handler, performance, resumption, and cancellation
  control;
- exact custom-drop and structural-destruction order;
- static `Use`, `RunsIn`, lifetime, and effect conclusions needed to validate
  transformations;
- enough SSA structure for sparse analyses and compact optimization;
- enough lexical scope information to emit bytecode cleanup maps.

MIR does not contain source `if`, `match`, loop, return, Boolean, operator,
`yield`, or `await` semantics. Those have already become ordinary calls,
decision DAGs, labels, effects, and primitives. It does not run trait selection,
infer open environments, or decide whether a trailing block was callable.

The frontend hands the backend one `MirBody` plus immutable semantic tables. A
compact phase tag advances monotonically through:

```text
Raw
  -> Owned       // frontend PlaceFlow facts imported and mapping validated
  -> Cleanup     // every abandoning edge has an exact cleanup plan
  -> Optimized   // semantics-preserving transforms complete
  -> Lowered     // loans/SSA destroyed, bytecode tables and registers selected
```

Only the named phase transition may change the tag. There are no generic wrapper
types or parallel body objects. Debug and test builds run the relevant validator
after every transformation pass; release builds validate phase boundaries.

## 2. Identity and storage model

All MIR entities are arena indexed. Each ID is a dense `u32` local to one body,
except `BodyId`, `TypeId`, `CallableId`, `ProtocolId`, `ConstantId`, `StringId`,
and `HostImportId`, which index compilation-wide immutable tables.

```text
BodyId CallableId TypeId ConstantId ProtocolId OperationId
BlockId LocalId LoanId MovePathId ScopeId
LabelId HandlerSiteId PerformSiteId ResumptionSiteId
CleanupPlanId RegionId StringId SourceScopeId SourceInfoId HostImportId
```

`u32::MAX` is never a valid MIR ID. Arenas never reuse an ID during one pass.
Deletion leaves a tombstone. Lowering builds dense block/register maps for live
entries without rewriting the MIR arenas. Optimization decisions must not depend
on numeric IDs; IDs are only deterministic tie breakers.

All `Vec<T>` fields below are logical notation. The compact implementation stores
them as `(start,count)` ranges into a handful of flat side arrays for locals,
operands, edges, projections, actions, and IDs. Per-record heap allocation is
forbidden in the self-hosted compiler.

### 2.1 Body

```text
MirBody {
    phase: Raw | Owned | Cleanup | Optimized | Lowered,
    id: BodyId,
    owner: CallableId,
    signature: Signature,
    entry: BlockId,
    blocks: Arena<BlockData>,
    locals: Arena<LocalData>,
    loans: Arena<LoanData>,
    move_paths: Arena<MovePathData>,
    scopes: Arena<ScopeData>,
    labels: Arena<LabelData>,
    handlers: Arena<HandlerSiteData>,
    performs: Arena<PerformSiteData>,
    resumptions: Arena<ResumptionSiteData>,
    cleanup_plans: Arena<CleanupPlanData>,
    source_info: Arena<SourceInfo>,
    properties: BodyProperties,
    invalid_analyses: u8,
}
```

`Signature` is exact:

```text
Signature {
    receiver: Option<TypeId>,          // exactly F, &F, or &mut F
    capture_type: TypeId,             // Unit when receiver is None
    parameters: Vec<TypeId>,
    result: TypeId,
    outward_protocols: SortedSet<ProtocolId>,
}
```

The hidden receiver is separate from user parameters in MIR and becomes bytecode
register 0 only during lowering.

`BodyProperties` records whether the body is a drop hook, may suspend, may
perform, contains a host call or label transfer, is duplicable as continuation
state, and has already had loans or cleanup elaborated. Passes may read but only
phase transitions may set these properties.

### 2.2 Locals

One `LocalId` universe represents SSA temporaries, source storage, parameters,
captures, block parameters, and drop flags:

```text
LocalData {
    ty: TypeId,
    storage: Ssa | Place | Erased,
    mutability: Immutable | Mutable,
    ownership: Owned | SharedRef | UniqueRef | CopyValue | ZstErased,
    scope: ScopeId,
    kind: Parameter(u32) | Capture | User | Temporary | BlockParameter | DropFlag,
    source: SourceInfoId,
}
```

An `Ssa` local is defined once. A `Place` local begins dead, becomes uninitialized
at `StorageLive`, and may be stored only while uninitialized; replacement requires
compiler-mediated zero-use destruction of the old value, including
`Use<[0,0]>` evidence. A drop flag is an ordinary compiler-created `u32` SSA/place
local and needs no separate arena. This single table removes value/slot conversion
maps from liveness, move paths, cleanup, capture analysis, and register lowering.

### 2.3 Places and move paths

```text
Place {
    base: LocalId,
    projection: Vec<Projection>,
}

Projection =
    Deref
  | Field { variant: Option<u32>, field: u32 }
  | ConstantIndex(u32)
  | DynamicIndex(LocalId)
  | Subslice { from: u32, to_from_end: u32 }
```

`Deref` is legal only through a live reference. A `Field` on an enum requires a
dominating proven discriminant or a decision-DAG edge fact. Dynamic array
projections conservatively overlap every dynamic projection of the same base
unless constant-range analysis proves disjointness.

The move-path tree contains a node for every statically distinguishable owned
projection. Array elements selected dynamically share one summary child.

```text
MovePathData {
    parent: Option<MovePathId>,
    projection: Option<Projection>, // none for a local root
    children: Vec<MovePathId>,
}

InitState = Uninitialized | Initialized | Partial
Disposition = Live | Transferred | Deconstructed | ZeroDestroyed
```

Moving a leaf makes it uninitialized and all ancestors partial. Reinitializing a
leaf recomputes ancestors. Moving a parent makes every descendant uninitialized.
Moving any field of a custom-`Drop` type is invalid. An enum has move paths only
for its active variant; a discriminant change is expressed by destroying the old
enum with zero-use evidence and constructing a new value, never by mutating the
tag in place. Without zero-use evidence the old enum must instead be transferred
or exhaustively deconstructed before the slot is reinitialized.

Continuation residual metadata follows the same rule. A partial tuple or struct
shell is capturable only when it has no custom hook. A known enum variant can be
represented by its variant fact plus initialized payload bitmap, which the
bytecode verifier already understands; the bootstrap frontend does not yet emit
that pair. Machine arrays require a different summary because dynamic indices
are not fixed move-path children. The VM preserves empty slots during snapshot
cloning, but a frontend may exploit a drained slot only after it can emit and
validate a conservative slot-initialization fact.

The bootstrap emits one field-initialization bitmap per live aggregate register,
not a single bitmap per source expression. Multiple disjoint `ProjectMove`
instructions clear multiple bits of the same shell. Moving an aggregate field
to a new register and then projecting that child produces two independently
tracked residual shells; exact, optional, and multi-shot captures preserve both
records. This compositional owner chain avoids flattening nested source paths
and lets the existing bytecode `FieldInit` state validate cleanup and snapshot
cloning without a bytecode-format change.

`Disposition` is tracked in addition to initialization. `Transferred` means the
whole owner crossed a by-value call, return, aggregate-construction, or control
edge. `Deconstructed` means a frontend visibility proof exposed the complete
layout and an exhaustiveness proof split the owner into independently accounted
child move paths. `ZeroDestroyed` means disposal without an ordinary owned use;
it is legal only with exact `Use<[0,0]>` evidence at that operation. Merely
projecting one field is a partial move, not a deconstruction proof.

Drop flags are referenced by `LocalId` from their owning move path.

One move path has at most one flag. Flags are introduced only where reachability
makes initialization conditional; they are not a replacement for rejecting
incompatible source ownership post-states.

### 2.4 Scopes, labels, and handler stacks

Scopes form a tree rooted at the function scope:

```text
ScopeData {
    parent: Option<ScopeId>,
    owners: Vec<MovePathId>,         // initialization order
    end_borrows: Vec<LoanId>,
    entered_label: Option<LabelId>,
    entered_handler: Option<HandlerSiteId>,
}

Owner cleanup uses the move path and its optional drop-flag `LocalId`.
```

Every block has one lexical `ScopeId`. Its active labels and handlers are derived
by walking/caching scope ancestry rather than storing two persistent stacks on
every block. A normal edge may remain in the same scope, enter one child, or exit
through a cleanup chain. It may not jump directly into a sibling/descendant scope.

```text
LabelData {
    result_type: TypeId,
    scope: ScopeId,
    destination: BlockId,
    call_destination: bool,
}

HandlerSiteData {
    handler_type: TypeId,
    protocols: SortedSet<ProtocolId>,
    result_type: TypeId,
    enclosing: Option<HandlerSiteId>,
    scope: ScopeId,
    partial: bool,
}
```

Static label and environment brands have already served type checking. `LabelId`
is the runtime realization linked from the erased brand; it cannot be constructed
as a value. Handler stacks refer to lexical sites, not runtime frame addresses.

## 3. CFG and instruction data model

### 3.1 Blocks and parameters

```text
BlockData {
    kind: Normal | Cleanup(CleanupKind) | HandlerClause | ResumeEntry,
    params: Vec<BlockParam>,
    statements: Vec<Statement>,
    terminator: Terminator,
    scope: ScopeId,
    source: SourceInfoId,
}

BlockParam {
    local: LocalId,
    ty: TypeId,
    role: Ordinary | ProtectedExitValue | CallResult | ResumeResult,
}

Edge {
    target: BlockId,
    args: Vec<Operand>,
    kind: Normal | Cleanup | Resume | HandlerReturn,
}
```

For a plain edge there is exactly one argument per target parameter with the same
type. A call/host-call/resume/handle edge has one implicit terminator result matching the
first specially-role-marked parameter and one explicit argument per remaining
parameter. A move argument consumes its place only on that predecessor edge;
mutually exclusive edges analyze independent successor states. Parallel edge
arguments are evaluated left to right into conceptual temporaries, so
`goto b(move x, move y)` cannot let the first parameter overwrite a source of the
second. Cycles are resolved only during bytecode lowering.

Block parameters are the only phi mechanism. A parameter may be removed when all
reachable predecessors pass the same dominating value or when it is unused.
Cleanup blocks use protected parameters to carry a return/leave/effect payload
through destruction without placing that payload in the cleanup owner list.

### 3.2 Operands and rvalues

```text
Operand =
    Move(Place)
  | Copy(Place)
  | Constant(ConstantId)
  | Function(CallableId)
  | ErasedZst(TypeId)

Rvalue =
    Use(Operand)
  | Aggregate { ty, variant: Option<u32>, fields: Vec<Operand> }
  | Borrow { loan, kind: Shared | Unique, place, region }
  | Reborrow { loan, kind: Shared | Unique, reference: Operand, region }
  | Discriminant(Place)
  | Len(Place)
  | Primitive { id, args: Vec<Operand>, may_trap: bool }
  | Callable { ty, target: CallableId, captures: Vec<Operand> }
  | Handler { ty, definition, clauses: Vec<Operand> }
  | BindingPack { ty, payloads: Vec<Operand> }
```

`Move`, `Copy`, constants, and function items are pure with respect to runtime
effects, but their order still fixes ownership diagnostics. `Copy` requires
principal upper use greater than one and structurally duplicable runtime state.
`ErasedZst` is allowed only for compiler-created erased evidence and generates no
register.

A `Copy(Place)` whose final projection is `Deref` reads through a live shared or
unique loan and copies the referent without consuming the reference. After loan
checking and register selection it lowers to bytecode `DEREF_COPY`, not ordinary
`COPY`: the reference register and its loan remain live, while the destination
receives an independently accounted duplicable `T`. Copying a non-duplicable
referent, reading a suspended unique parent, or treating the operation as a move
is invalid.

A `Move(Place)` whose final projection is `Deref` is permitted only through a
live, unsuspended unique loan. It lowers to `DEREF_MOVE`, leaving the referent
temporarily uninitialized while the unique-reference local and loan remain live.
The corresponding `Store` to that dereferenced place lowers to `DEREF_STORE` and
must occur on every continuing control-flow path before the reference can be
read, reborrowed, ended, cleaned up, returned, or passed onward. MIR place-
initialization analysis carries this hole state across blocks and requires exact
agreement at joins. Non-returning abort edges need not restore the referent.

A primitive is the exact frozen primitive selected during Typed Core lowering.
The MIR does not have generic Add/Compare nodes. `may_trap` is derived from the
primitive ID and operands; a pass may change it to false only with a proof from
range/constant analysis.

### 3.3 Statements

```text
Statement =
    Define { local: LocalId, rvalue: Rvalue }
  | StorageLive(LocalId)
  | StorageDead(LocalId)
  | Store { destination: Place, value: Operand }
  | EndBorrow(LoanId)
  | SetDropFlag { flag: LocalId, value: bool }
  | Destroy { place: Place, mode: ExplicitZero | Implicit | Cancellation }
  | DestroyIf { place: Place, flag: LocalId, mode: Implicit | Cancellation }
  | Nop
```

Statement order is execution order. `Define` evaluates rvalue operands left to
right, then makes the result live. `Store` evaluates its operand before mutating
the destination.

Source assignment lowers to an already-evaluated operand followed by either
`Store` into an uninitialized move path, or `Destroy` of an initialized exact
destination followed by `Store`. The latter form is legal only with
`Use<[0,0]>` evidence for the old resident subtree. Structural duplicability is
not a substitute for that evidence when the resident has a positive principal
lower bound. A `Store` never silently replaces or destroys an initialized
resident. Consequently generic `replace` and `swap` are expressed by moving the
old referent out, storing into the now-uninitialized place, and transferring the
old owner; neither operation requires zero-use permission for the transferred
type.

`EndBorrow` consumes only the static `LoanId`; a surviving reference value must
already be dead. It becomes `Nop` when loan evidence is erased. `StorageDead`
requires the slot uninitialized and unborrowed; it never destroys implicitly.

Every `Move` is classified as a whole-owner `Transfer` or as one member of a
frontend-proven `Deconstruct`. A deconstruction certificate names the visible
aggregate definition, the proven enum variant where applicable, and the complete
set of payload fields, and proves that the aggregate has no custom `Drop` hook.
Bound fields transfer into new owners. A wildcard,
omitted field, or non-binding subpattern requests `Destroy` for that remainder
and therefore requires `Use<[0,0]>`; it never silently counts as a move.

`Destroy` first ends loans that are proved dead at the point, then invokes custom
drop glue exactly once if present, destroys initialized active fields in reverse
declaration order, and releases storage. All three modes are zero-use disposal
paths and require `Use<[0,0]>`. `ExplicitZero` is compiler-only: a normal
by-value `destroy(value)` function call would first transfer `value` into the
callee and therefore cannot express zero-use disposal. A source wrapper needs a
dedicated compiler disposal argument mode or must not be offered.

### 3.4 Terminators

Every block has exactly one terminator:

```text
Terminator =
    Goto(Edge)
  | Switch {
        discr: Operand,
        cases: Vec<(ConstantId, Edge)>,
        otherwise: Edge,
    }
  | Call {
        result: Option<LocalId>,
        callee: CallTarget,
        receiver: Option<Operand>,
        args: Vec<Operand>,
        effects: SortedSet<ProtocolId>,
        normal: Edge,
    }
  | HostCall {
        result: Option<LocalId>,
        import: HostImportId,
        args: Vec<Operand>,
        normal: Edge,
    }
  | Handle {
        result: LocalId,
        site: HandlerSiteId,
        handler: Operand,
        body: Operand,
        args: Vec<Operand>,
        normal: Edge,
    }
  | Perform {
        site: PerformSiteId,
        result: Option<LocalId>,
        protocol: ProtocolId,
        operation: OperationId,
        payloads: Vec<Operand>,
        resume: Option<Edge>,
    }
  | Resume {
        site: ResumptionSiteId,
        result: LocalId,
        resumption: Operand,
        value: Operand,
        normal: Edge,
    }
  | Cancel {
        site: ResumptionSiteId,
        result: LocalId,
        resumption: Operand,
        normal: Edge,
    }
  | TailCall {
        callee: CallTarget,
        receiver: Option<Operand>,
        args: Vec<Operand>,
        effects: SortedSet<ProtocolId>,
    }
  | Return(Operand)
  | Leave { label: LabelId, value: Operand }
  | Abort { message: Option<StringId> }
  | Unreachable
```

`CallTarget` is `Direct(CallableId)` or `Indirect(Operand)`. `HostCall` is emitted
only for a manifest-bound leaf declaration and names one exact capability,
symbol, and signature. A terminator result is defined only on its normal/resume
edge and must dominate every use. The target
block conventionally receives it as a `CallResult`/`ResumeResult` first parameter;
the edge does not repeat it in `args`. All other edge parameters follow it.

Calls and host calls have no language exception edge. Primitive/host faults and `Abort` terminate
without cleanup. An effectful callee may suspend or transfer through its declared
protocols, which is represented by `effects` and the active handler stack rather
than a statically named CFG successor.

`Perform` has a resume edge exactly when the declaration-site operation is
resumptive. Its result is the operation result delivered on resumption. A terminal
perform has neither result nor resume edge. Both forms have a dynamic handler edge
described by `PerformSiteData`; terminal abandonment and continuation capture are
part of that edge, even though its target clause may be dynamically selected.

```text
PerformSiteData {
    block: BlockId,
    handler_candidates: Vec<HandlerSiteId>, // innermost first
    frame_cleanup: CleanupPlanId,
    captured_locals: BitSet<LocalId>,
    captured_loans: BitSet<LoanId>,
    resumption_type: Option<TypeId>,
}
```

The cleanup plan referenced by a dynamic effect/cancellation edge is immutable:

```text
CleanupPlanData {
    source_scope: ScopeId,
    target_scope: ScopeId,
    actions: Vec<EndBorrow(LoanId) | Destroy(MovePathId) | StorageDead(LocalId)>,
    protected_types: Vec<TypeId>,
}
```

Actions are in execution order. Plans contain no source-level use decision; every
`Destroy` has already been proven to have `Use<[0,0]>` evidence for
implicit/cancellation cleanup.

```text
ResumptionSiteData {
    resumption_type: TypeId,
    originating_handler: HandlerSiteId,
    capture_plan: CleanupPlanId,
    captures: BitSet<LocalId>,
    loans: BitSet<LoanId>,
    lower_uses: u32,
    upper: Finite(u32) | Infinite,
    duplicable: bool,
    cancellation_safe: bool,
}
```

The quantity and Boolean fields are derived from checked source evidence and are
revalidated against captures whenever a pass changes escape/capture facts.

`Resume` returns when the resumed continuation eventually yields its handler
result. Deep resumption reinstalls the handler recorded in `ResumptionSiteData`.
`Cancel` destroys the captured continuation and then follows its normal edge with
unit. One-shot resume is move-only; multi-shot borrowed resume requires every
captured owner and handler dependency to be duplicable and no captured unique
loan.

`Return` and `Leave` appear only at the end of cleanup chains when the body phase
is `Cleanup` or later.
`TailCall` likewise appears only after outgoing cleanup. `Abort` is never routed
through cleanup.

## 4. Ownership, Use, borrowing, and cleanup

Sections 4.1 and 4.2 describe the `PlaceFlow` facts imported from the frontend.
MIR stores and queries them for cleanup and optimization legality; it does not
rerun a second ownership, quantity, or region inference.

### 4.1 Ownership dataflow

For each reachable program point, `MoveInitAnalysis` computes every move path as
`Uninitialized`, `Initialized`, or `Partial` and retains its disposition proof.
Transfer rules are exactly those in section 2.3. CFG joins require identical
state unless cleanup elaboration inserts a drop-flag local; it never inserts
destruction merely to force unequal source branch post-states to unify.

Each operand also contributes a quantitative use event:

- whole-owner `Transfer`, payload ownership created by a proven `Deconstruct`,
  owned callable receiver, owned environment transition, and consumed resumption
  add one;
- `Copy` is both a use of the source and creation of an independently accounted
  owner; it leaves the source live and cannot by itself discharge that source's
  must-move obligation;
- shared/unique borrows add no owned use;
- `Destroy` adds zero; it is legal only when the destroyed move path has
  `Use<[0,0]>` evidence, recursively including every initialized remainder;
- mutually exclusive successors take interval hulls;
- loops with an executable use widen the upper bound to infinity unless a proven
  finite trip count supplies a tighter multiplication;
- nested callable/resumption execution multiplies intervals.

`UseAnalysis` stores the inferred interval per binding/environment/resumption and
the exact evidence used at each operation. Optimization must preserve containment
in the principal interval. It may remove a zero-observation operation only when
that removal does not lower a required minimum use. Cleanup never satisfies a
positive lower bound.

Pattern lowering may mark an owner `Deconstructed` only when the definition is
visible at the pattern site and the decision DAG proves exhaustive coverage of
the active layout. Struct patterns must account for every field; enum patterns
must have a dominating variant fact, and an exhaustive match must cover every
possible variant. Bindings transfer their payloads. `_`, `..`, omitted fields,
and literal-only/non-binding payloads are zero-use destruction requests and need
`Use<[0,0]>` for precisely the discarded remainder. Private, opaque, and
non-exhaustive layouts can be transferred whole but cannot be deconstructed.

### 4.2 Loans and regions

```text
LoanData {
    kind: Shared | Unique,
    borrowed: Place,
    issued_at: Location,
    region: RegionId,
    parent: Option<LoanId>,
}
```

Region inference produces a bitset of MIR locations per loan. Shared loans may
overlap shared loans. A unique loan conflicts with every overlapping live loan,
and its base place cannot be read, moved, destroyed, or independently reborrowed.
A reborrow suspends the parent unique loan for the child's live region. Place
overlap uses move-path ancestry plus conservative dynamic-index aliasing.

Every normal and nonlocal edge checks that reference values and loans fit the
destination scope. A performance site records all loans crossing capture. A
multi-shot resumption rejects any unique crossing loan; cancellation requires
every abandoned borrowed owner to remain valid through destruction. Drop checking
treats a custom hook as observing all borrowed fields.

Loan erasure removes region/loan IDs and redundant borrow scaffolding only after:

1. all ownership-, capture-, cleanup-, and drop-sensitive transforms finish;
2. every remaining reference value has a concrete bytecode reference type;
3. every nonescaping borrow scalarized to direct place access is proven not to
   cross a call, handler, perform, resume, label, or host barrier.

“Borrow erasure” does not erase a reference that survives at runtime; it erases
proof data and lowers that reference to bytecode borrow/reborrow/end-borrow
instructions.

### 4.3 Cleanup elaboration

Cleanup elaboration processes each edge that exits a scope, including normal
return, tail call, `Leave`, terminal perform, cancellation, handler completion,
failed partial initialization, and destruction of a captured continuation.

For a source and target scope it computes:

1. loans ending in exited scopes, innermost first;
2. protected exit operands, moved into cleanup block parameters;
3. live owners introduced after the target boundary, in reverse initialization
   order;
4. for each owner, custom hook then initialized fields in reverse declaration
   order;
5. storage-dead operations;
6. the final transfer.

Every item selected for explicit, implicit, or cancellation destruction must
have `ZERO_USE_ALLOWED`/`Use<[0,0]>` evidence. Owners without that evidence must
already be `Transferred` or be completely `Deconstructed`, with each child
independently transferred or zero-legally destroyed. A custom-`Drop` owner must
be fully initialized and itself prove `Use<[0,0]>`. A partially initialized
structural aggregate destroys only initialized leaves, each with zero-use proof.

Conditional initialization creates a drop flag. The compiler sets it immediately
after initialization and clears it immediately before a move or explicit destroy.
Flags are never source-visible and are not merged by guessing. `DropFlagAnalysis`
may replace `DestroyIf` with `Destroy` or remove it when the flag is constant.

Cleanup blocks are hash-consed by:

```text
(target scope, ordered destruction actions, protected parameter types,
 final transfer kind, target label/handler depth)
```

Source locations do not affect sharing. Shared cleanup preserves the original
operation's source info on each `Destroy`. Cleanup CFG is acyclic except for a
diverging custom drop hook call. `Cleanup` validation proves that a cleanup edge
only reduces scope, label, and handler stacks, contains no owner lacking zero-use
evidence, and cannot be entered from a normal edge.

Terminal performance retains a frame cleanup plan at the perform site rather
than running cleanup before handler lookup. Once a handler is found, the runtime
destroys the abandoned frames using those plans before invoking the clause. An
unhandled-effect fault and `Abort` perform no cleanup.

### 4.4 Label, handler, and continuation invariants

- A `Leave` target label is on the source block's active stack and its result type
  equals the value type.
- Its cleanup target is the label scope; destination cleanup owners form a suffix
  of the source cleanup list.
- Ordinary edges cannot enter or bypass a label or handler region.
- Handler candidate lists are the exact active lexical stack filtered by protocol,
  innermost first. Partial misses continue outward.
- Resumptive performs capture frames up to and including the dynamic delimiter
  boundary specified by the handler site; terminal performs create no resumption.
- A one-shot resumption is consumed on `Resume` or `Cancel` along every path.
- Multi-shot capture is legal only when structural copy, `Use`, loan, handler,
  and drop facts all permit duplication. Copying must not duplicate a custom hook
  observation that source `Use` forbids.
- Cancellation is legal only if every captured owner's path admits zero ordinary
  uses; destruction still occurs in cleanup order.
- Deep resume restores the original handler before the first captured frame runs.

## 5. MIR validity contracts

`validate_mir(body, level)` is deterministic, linear in body size apart from
dominator and alias queries, and reports body/function/source locations rather
than panicking.

### 5.1 Structural validity (`Raw`)

- Every ID/reference/type is valid; entry exists; every live block terminates.
- SSA-local definitions are unique and dominate uses, including terminator results.
- Block parameter counts/types and special result positions match every edge.
- All operand evaluation orders are explicit and types agree.
- Place-local storage state, projection types, enum facts, and primitive signatures agree.
- CFG edges obey lexical scope/label/handler entry rules.
- No prohibited Typed Core/source-control node exists.

### 5.2 Ownership validity (`Owned`)

This validator does not infer ownership again. It checks that imported
`PlaceFlow` facts name the corresponding MIR locals/locations and that the
frontend proof conclusions below are represented without loss.

- Move/init states agree at joins or are represented by explicit flags.
- Copy, move, borrow, reborrow, mutation, destruction, and receiver access types are
  legal for the principal `Use` interval and current loans.
- Every consumed owner is classified as a whole transfer, visibility- and
  exhaustiveness-proven deconstruction, or zero-legally destroyed remainder.
- Actual `Use` intervals fit principal intervals and branch post-environments
  agree on normal edges.
- No dependency escapes its reference, label, environment, handler, or refinement
  lifetime.
- Custom drop restrictions, handler coverage, effect rows, resumption quantity,
  and cancellation conditions hold.

### 5.3 Cleanup validity (`Cleanup` and later)

- Every scope-exiting edge uses the unique correct cleanup sequence.
- Every owner is transferred, completely deconstructed, or destroyed with
  `Use<[0,0]>` evidence exactly once per runtime path; custom hooks and fields
  follow required order.
- Protected values cannot be destroyed by their cleanup chain.
- Drop flags are set/cleared on every corresponding state transition.
- Terminal effects and captured continuations reference complete frame plans.
- Return/leave/tail-call terminators occur only after cleanup. `Abort` is the
  explicit exception: it terminates the worker without transfer, destruction,
  hooks, or cleanup and needs no disposition proof for live owners.

### 5.4 Optimization validity (`Optimized`)

In addition to all prior rules, block params contain no trivial cycles, deleted IDs
have no uses, declared effect summaries are conservative, tail calls satisfy frame
replacement constraints, and every pass-specific proof annotation has either
been consumed or remains valid in the current phase.

## 6. Analysis framework

### 6.1 Manager and mutation API

Passes use a small checked mutation API for edge redirection, statement removal,
block splitting, operand replacement, and terminator replacement. A mutation ORs
an `u8` invalidation mask into the body:

```text
CFG=1  USES=2  FLOW=4  EFFECTS=8  VALUES=16  COST=32
```

Six optional analysis slots are recomputed lazily when their bit is set. There is
no revision-keyed cache, incremental repair, transactional editor, change-set
object, or preservation certificate. Passes that need rollback build their
replacement in the reusable scratch arena and commit once. This trades occasional
linear recomputation for much less compiler code and metadata.

```text
run_pass(pass_id, body, analysis_slots, scratch, budget)
    -> Unchanged | Changed(invalidation_mask) | BudgetExhausted
```

Worklists use reverse postorder then numeric ID. Lookup-map iteration never
controls a rewrite; output-affecting candidates are sorted once before selection.

### 6.2 Analysis bundles

| Bundle | Lazily contains |
|---|---|
| CFG | predecessors, successors, reachability, RPO, dominators, loop headers |
| Uses | definitions, use ranges, and block-edge liveness for unified locals |
| Flow | move/init, loans/regions, alias overlap, quantitative intervals, drop facts |
| Effects | trap/effect/handler/capture/call summaries and call-graph SCCs |
| Values | SCCP lattice, integer ranges, and value numbers |
| Cost | body/call weights used only by inlining and specialization |

Each bundle is a group of flat arrays sharing the body's dense IDs. Subresults are
filled only when requested. Liveness, flow, effects, and SCCP use sparse worklists;
the straightforward iterative dominator algorithm is preferred until profiling
shows a body large enough for Lengauer-Tarjan. Recursive interprocedural summaries
widen after four changes in one call-graph SCC.

## 7. Transformation legality

### 7.1 Universal rules

Every transformation must preserve:

1. value/result and trap behavior;
2. left-to-right order of observable operations;
3. exact custom-drop count and relative order;
4. host-call order and arguments;
5. perform protocol/operation, nearest-handler selection, payload order, and
   capture point;
6. label destination and cleanup boundary;
7. resumption quantity, deep-handler reinstatement, and cancellation legality;
8. ownership, loan, lifetime, `Use`, and post-environment validity;
9. guaranteed tail-call stack bound where one already existed.

An operation is observable if it is a host call, effect, handler enter/exit,
resume, cancel, leave, custom drop, abort, or a primitive that may trap. Structural
destruction without a custom hook is still ordered relative to observable drops
because its fields may contain hooks.

Two operations may commute only when `Effects` proves both nonobservable/nontrapping,
`AliasSets` proves disjoint memory, `Loans` remains valid, `UseIntervals` is
unchanged, and `DropFacts` proves no changed destruction order.

### 7.2 Specific optimization constraints

- **Constant folding/SCCP:** fold only frozen primitives. A trapping fold becomes
  the same trap at the same evaluation point, not `Unreachable`. Aggregate folds
  preserve field evaluation order. Floating-point arithmetic and comparisons use
  IEEE semantics, preserve signed zero, and canonicalize NaNs to the frozen VM
  bit patterns. Checked float/integer conversions remain dynamic unless the
  optimizer can preserve their exact trap behavior. Integer neutral and absorbing
  elements simplify only when the known operand proves the original operation
  cannot trap; notably, signed division or remainder by `-1` is never treated as
  an identity because the minimum signed value would trap.
- **Copy propagation:** never turn a borrow into ownership, duplicate a
  nonduplicable value, extend a loan, or move a use across cleanup/effect barriers.
- **Dead-code elimination:** removing a definition also removes its operands only
  when they are pure, nontrapping, require no minimum `Use`, and own no value that
  would thereby change cleanup. Dead explicit `Destroy` is never removed merely
  because structural runtime data is unused. The initial primitive DCE slice is
  restricted to copy-mode predefined scalars and removes complete unused chains
  with a deterministic transactional worklist.
- **Scalar replacement:** forbidden for custom-`Drop` aggregates unless the hook
  remains applied to a fully materialized value. Partial moves and reverse field
  destruction must remain representable. Enum scalar replacement requires a
  proven tag on every use.
- **GVN/CSE:** keys include primitive ID, type, operands, relevant place version,
  trap proof, and active handler identity. Borrows, allocation, handler values,
  resumptions, host calls, and drop glue are never commoned. The initial local
  slice only reuses identical nontrapping predefined-scalar primitives within one
  basic block, with copy-mode operands and conservative invalidation at ownership
  or effect barriers.
- **Load/store forwarding:** requires one dominating exact-place store, no
  overlapping write/call/effect, and compatible loan state. A moved field cannot
  be forwarded as initialized.
- **Devirtualization:** indirect callable targets must be a singleton after type,
  value-number, and capture analysis. Receiver type/access and capture layout cannot
  change. Multi-target specialization emits a guard/switch only when the runtime
  callable identity is already observable in representation.
- **Capture shrinking:** preserves source capture evaluation order, drop order,
  environment lifetime dependence, and invariant brand dependence. An apparently
  unused capture remains if required by `Use`, drop, loan, label, handler, or
  cancellation facts.
- **Closure scalarization:** requires nonescape and no identity observation. A
  call may become direct, but borrowed receiver duration and capture destruction
  stay unchanged.
- **Effect specialization:** may remove a handler only when every reachable
  operation is statically resolved and the handler has no observable construction,
  drop, partial forwarding, or deep-resumption role. Terminal handler folding must
  retain abandoned-continuation cleanup before clause execution.
- **Continuation allocation elision:** requires the resumption not escape the
  clause and all resume/cancel uses be known. One-shot resume can become a direct
  control edge; cancellation becomes the same cleanup chain. Multi-shot state may
  be shared only through verifier-approved copy glue.
- **Drop optimization:** a `DestroyIf` may simplify from constant flags. A
  structural no-hook drop may disappear only when all recursively owned storage
  is zero-sized or already moved, the destruction had zero-use evidence, and no
  required disposition or hook is removed. Cleanup
  blocks merge only with identical ordered actions and protected types.
- **Inlining:** substitutes scopes, labels, handler sites, loans, move paths,
  source info, and cleanup actions with fresh IDs. It cannot inline a drop hook
  into a context that would expose effects or label transfer. Capturing calls keep
  their receiver access duration. Handler delimiters may not be accidentally
  merged.
- **Tail-call formation:** the call result must flow only to cleanup then return,
  with no observable work after the call. Outgoing cleanup occurs before frame
  replacement but moved arguments/receiver are protected. Borrowed indirect
  receivers are not tail-callable in G1; copy a duplicable callable then move it.
- **Loop-invariant motion:** requires dominance of all uses, safe execution on
  zero iterations, nontrapping/effect-free operation, no cleanup/drop order
  change, stable alias version, no captured loan, and no movement across a handler
  or resumption boundary.

## 8. Optimization schedule

Pass names and order are fixed so bootstrap output is reproducible. “FP” means
repeat the enclosed sequence until no pass changes MIR or three rounds complete.
Hitting the cap is not an error and emits an optimization remark in diagnostic
builds.

### 8.1 Mandatory pipeline (`-O0` and above)

1. `ValidateRawMir`
2. `ImportAndValidatePlaceFlow` (reuses frontend local/move/loan/use IDs)
3. `ElaborateCleanup`
4. `ValidateCleanupMir`
5. `NormalizeCfg` (unreachable removal, block parameters, critical edges, merges)

`-O0` then runs loan-proof erasure, register lowering, and bytecode emission. It
does not fold source operations except mandatory representation legalization.

### 8.2 Local optimization (`-O1`)

1. FP: `SparseSimplify` runs SCCP, switch/block simplification, copy propagation,
   projection/tag folding, redundant construction, local forwarding, and dead
   statement/storage rules in one RPO sweep plus sparse value worklist.
2. `ScalarizeLocals` performs profitable aggregate scalar replacement.
3. `SimplifyCleanup` folds drop flags and merges identical cleanup tails.

### 8.3 Self-host optimization (`-O2`)

After `-O1`:

1. `GlobalSimplify` combines value numbering/CSE, direct target propagation, and
   callable devirtualization in one dominator walk.
2. `ScalarizeCallables` shrinks captures and scalarizes nonescaping closures.
3. `SpecializeControl` resolves effect rows/static handlers, simplifies terminal
   handlers, elides one-shot continuation allocation, specializes resumptions,
   and shares multi-shot copy glue using the same control-site walk.
4. `SpecializeCleanup` simplifies destruction chains after capture/control
   specialization.
5. `InlineByCost`.
6. FP: `SparseSimplify`, with global value-number facts when still valid.
7. `EraseLoanProofsAndScalarizedReferences`.
8. `FormTailCallsAndHoist` discovers tail calls and performs legal invariant
   motion using the same dominator/loop information.
9. `ValidateBytecodeInput` rechecks optimized MIR and cleanup boundaries.
10. `LowerRegistersAndEdges` using dense maps of live IDs.
11. `LayoutAndPeephole` lays out blocks, pools constants, and performs bytecode
    peepholes.
12. `ValidateFinalArtifact` runs the hostile-input verifier and cross-validates
    serialized cleanup maps against the MIR ownership facts.

Each sweep has a required body-property mask and individual rewrite rules check
more specific bits. Aggregate, indirect-call, handler, resumption, drop-hook, and
loop logic never scans bodies lacking the corresponding feature.

### 8.4 Aggressive optimization (`-O3`)

`-O3` uses the same semantic order as `-O2`, but runs devirtualization/effect/
resumption specialization and inlining twice, with the larger budgets below. It
never relaxes a legality condition.

## 9. Cost and complexity limits

The compiler rejects a single body before optimization if it exceeds any of:

```text
1,000,000 blocks
4,000,000 statements + terminators
4,000,000 locals
8,000,000 move paths
65,535 nested lexical scopes, labels, or handlers
```

The diagnostic reports the exceeded category and source owner. Limits prevent ID
overflow and hostile compile-time memory use; ordinary programs should remain far
below them.

Pass work is budgeted in “work units”: visiting one statement/terminator/edge is
one unit, cloning one is two. A body pass receives `max(100_000, 32 * body_size)`
units; exceeding it stops that optional pass before its scratch result commits and
emits a remark. A compilation-wide optional budget of `64 * total_initial_ops`
prevents many medium bodies from multiplying the nominal per-body cap. Mandatory
correctness passes are not abandoned; they use sparse algorithms and fail with a
resource diagnostic if process limits intervene.

Inlining uses this stable weighted cost:

```text
ordinary statement       1
branch/edge               2
direct call               5
indirect call             8
destroy/custom cleanup    4 / 12
handler/perform/resume    20
host call or abort        20
```

- Always inline nonrecursive cost <= 12 when legal.
- `-O2`: candidate cost <= 60, caller growth cap `2 * original_cost + 256`,
  depth 8, at most 8 specialized clones per source function.
- `-O3`: candidate cost <= 120, growth cap `4 * original_cost + 1024`, depth 16,
  at most 16 specialized clones per source function.
- Never inline within the same recursive call-graph SCC. Tail-recursive calls are
  optimized by tail-call formation instead.
- Program-wide specialization is capped at 4096 cloned bodies.

Constant aggregates larger than 64 KiB, arrays longer than 1024 elements, text/
bytes results larger than 1 MiB, and loops without a proven trip count <= 256 are
not materialized by constant folding. Value numbering tables cap at four times
body operations and then disable new entries without changing correctness.

## 10. Bytecode lowering

Lowering consumes a body whose phase is `Optimized` and must not make semantic
decisions.

### 10.1 Loan and SSA destruction

Remaining runtime references become the bytecode reference types and
borrow/reborrow/end-borrow instructions. Proof-only loans and ended references
produce no code. Addressable slots and owned values receive virtual registers;
erased ZST evidence receives none.

Each block parameter becomes a virtual register. For every edge, lowering emits
a parallel transfer from argument places to parameter registers. It first protects
all moved sources, emits acyclic moves in destination-safe order, and breaks a
cycle with one typed temporary. Copy edges emit `COPY`; erased arguments vanish.
Critical-edge splitting guarantees transfers have a unique insertion block.

### 10.2 Register allocation

Live intervals are computed over final block order with separate classes for
owned values, shared references, and unique references. Linear scan reuses a
register only after its prior value is empty and all loans ended. Values with
different bytecode types may share a numeric register because verification tracks
type by program point; block joins must agree. Register 0 is reserved for the
hidden receiver, parameters occupy 1 onward, and allocator-created registers
follow.

Spilling means retaining an addressable VM register/place; G1 has no untyped stack
spill instruction. The allocator therefore minimizes register count but never
fails due to pressure.

### 10.3 Instruction selection

- constants, moves, copies, aggregates, projections, borrows, callables, handlers,
  binding packs, drops, calls, switches, labels, effects, resumptions, host calls,
  primitives, and abort map directly to their frozen bytecode operations;
- block parameter transfers precede `JUMP`/`SWITCH` targets;
- a direct label region receives one lexical label slot and emits push/pop/leave;
- handler sites produce handler-definition records in source first-match order;
- protocol and operation IDs are already normalized and are not renumbered by
  profile/layout decisions;
- indirect bytecode receiver modes are derived mechanically from the ordinary
  receiver operand type (`F`, `&F`, or `&mut F`), and guaranteed tail calls are
  preserved exactly;
- unit/never destinations use `NONE32` where the bytecode permits it.

Moves and stores through a final dereference projection select `DEREF_MOVE` and
`DEREF_STORE`; ordinary register `MOVE` never models the transient referent hole.

Block layout is entry first, then hot/RPO normal successors, then cleanup blocks,
then handler/resume cold blocks. Tie breaks use original BlockId. Jumps are always
instruction ordinals and are patched after layout.

### 10.4 Cleanup maps

At every final instruction, lowering records the active owner list newest first.
Adjacent instructions with identical lists become one `CLEANUPS` interval. Owners
already moved, protected transfer values, erased ZSTs, and proof-only references
are absent. For ordinary cleanup, `DestroyIf` lowers to a `u32`-discriminated
switch followed by `DROP` or the skip edge; `SetDropFlag` becomes SSA constants/
edge arguments and does not survive as a bytecode operation. For frame
abandonment, the cleanup list contains the owner's register and the VM's Empty
state is the runtime drop flag, so no separate flag is serialized. Terminal
perform and continuation capture entries use the same owner order as their MIR
cleanup plans.

The target list for a `LEAVE` must be a suffix of its source list. A tail call
moves arguments/receiver to protected VM temporaries, zero-destroys the remaining
zero-use-legal list, then replaces the frame. Cleanup-table emission is validated
against MIR `DropFacts` before serialization.

### 10.5 Peepholes

The implemented ordinal peephole folds non-branch-entry transfer-temporary
`Move`/`Copy` chains across independent straight-line parallel snapshots,
removes target-safe `NOP` instructions and fallthrough jumps before
cleanup-plan generation, and deterministically repatches switch, jump, and
label destinations while retaining a referenced trailing target and the
required nonempty function body.

Switch arms without arguments target their MIR successor directly and never
materialize an empty synthetic transfer block. Argument-carrying arms alone
receive deterministic out-of-line transfer blocks.

Bytecode peepholes may remove `NOP`, move-to-next-move chains, empty edge-transfer
blocks, redundant borrow endings, and jumps to the immediately following
instruction. They may not reorder instructions, cross cleanup interval boundaries,
change instruction ordinal targets without repatching all tables, combine trapping
primitives, or alter label/handler nesting. The bytecode verifier is run on the
in-memory artifact before it is written.

## 11. Differential execution

The self-hosted compiler contains no MIR interpreter. For optimizer tests it
lowers a selected MIR prefix with optimization disabled, emits an in-memory G1
artifact, and executes that artifact in `grvm` with deterministic mock host
capabilities. The optimized prefix is lowered and executed the same way. The
For programs first accepted by the compiler and confined to the documented
bootstrap subset, the AST evaluator supplies
an independent source-level behavioral oracle. It is not an ownership,
borrowing, privacy, or cleanup-conformance oracle: those properties are checked
by the frontend, MIR validation, artifact verification, and VM execution.

The harness compares return/trap/abort outcome, ordered host/effect/clause/
resume/cancel/leave/custom-drop trace, and final mock host state. A test-only VM
step/allocation limit makes divergent comparisons bounded. This shares one
implementation of deep handlers, continuation capture, primitive traps, and
cleanup instead of duplicating the entire dynamic control machine in Grandiose.

## 12. Optimization testing

Every transformation pass has four test layers:

1. golden MIR input/output for its intended rewrite and each legality barrier;
2. validator tests that deliberately corrupt one invariant and require a precise
   rejection;
3. differential VM execution of bytecode lowered immediately before and after the
   pass;
4. end-to-end comparison of the AST evaluator, `-O0`, and optimized bytecode for
   compiler-accepted programs in the evaluator's documented subset;
   otherwise comparison of `-O0` and optimized bytecode.

The differential harness supplies the same serialized parameters and mock host
state, runs each artifact to the same test-only bound, and requires identical
observations. It explores every switch/handler alternative for small finite inputs
and uses deterministic seeded generation for larger cases. A result is discarded
only when all compared versions reach the same step limit without an observable
prefix difference.

Property generators construct MIR through the checked builder, so generated
bodies are typed and ownership valid. Separate mutational fuzzers target the MIR
validator. Generated cases emphasize partial initialization, branch joins,
borrow/reborrow boundaries, nested labels, partial/deep handlers, terminal versus
resumptive effects, one-shot cancellation, multi-shot copy restrictions, custom
drop order, tail calls, and trapping primitives.

Required regression properties include:

- no pass changes left-to-right host/effect/drop traces;
- stage-specific validators accept every committed pass result;
- optimization never converts a compile-time `Use` rejection into accepted MIR;
- removing a handler or continuation allocation retains dynamic clause choice and
  cleanup timing;
- SROA and projection folding preserve partial-move and custom-drop restrictions;
- inlining preserves label/handler identity and nonescape;
- tail-call formation keeps bounded VM stack and protects transferred arguments;
- every emitted bytecode cleanup list matches source-oracle and `-O0` destruction
  order;
- `-O2` output is deterministic across hash seeds and repeated stage builds.

Release testing runs each pass independently, every optimization prefix, and the
complete `-O0`/`-O1`/`-O2`/`-O3` pipelines. A minimized differential failure is
checked in as textual MIR before the pass can be enabled for self-host builds.

## 13. Bootstrap implementation status (2026-07-19)

The bootstrap in `crates/grandiose` realizes the phase contracts above on the
compact register MIR rather than the full arena representation. The exact
boundary:

- **Carrier.** Instructions stay in the compact register `Function`. Each body
  carries a `PlaceFlow` fact sidecar with the normative typed identities and
  arenas: per-local facts (type, storage class, ownership category,
  mutability, declared `Use` interval, drop glue, entry initialization, scope,
  kind, source), places with field/deref/dynamic projections and exact
  conservative overlap, interned move-path trees, loans/regions, scopes,
  labels, handler/perform/resumption sites, drop flags, cleanup plans, and
  source records. `LocalId` is unified with the virtual register index.
- **Export and import.** `MirLowerer` exports the facts during lowering
  (provenance `Exported`). `ImportAndValidatePlaceFlow` validates them against
  the instruction stream (local types, loan multisets, control sites),
  materializes bridged facts for optimizer-allocated registers, runs the
  ownership fixed point, and advances `Raw -> Owned`. It is never
  `SkippedUnavailable`. Hand-assembled MIR without exported facts uses the
  documented `Synthesized` bridge: deterministic cleanup lists and structural
  loan discipline without exported-only obligations.
- **Ownership engine.** One deterministic fixed-point engine
  (`compiler_regions.rs`) interprets every statement and terminator over
  arbitrary CFG joins: whole/partial/conditional initialization with
  residual-shell bitmaps and shell-age reconstruction, verifier-order owner
  age lists, loans with reborrow suspension, external (caller-managed)
  provenance, and dereference holes, plus quantitative `Use` intervals with
  hull joins and loop widening. Joins require agreement except through
  registered drop flags; the VM `Empty` register state is the runtime flag,
  so no flag value is serialized.
- **Cleanup elaboration.** `ElaborateCleanup` attaches an exact plan (ordered
  `Destroy`/`DestroyResidual`/`DestroyIf`/`EndBorrow` actions plus protected
  transfer values) to every return, tail-call, terminal-perform, and
  cancellation edge, and advances `Owned -> Cleanup`. `ValidateCleanupMir`
  re-derives and compares the plans, and runs at every pass checkpoint and at
  the `Optimized` boundary; a changed pass ORs the `analysis` invalidation
  mask and stale facts are recomputed, never trusted.
- **Backend.** The serialized cleanup maps still come from the verifier
  generator, but they are cross-validated against the MIR facts before an
  artifact is released: at the program counter of every MIR statement and
  terminator start (through the peephole ordinal relocation), the installed
  plan's newest-first register list must equal the engine's list. The engine
  mirrors the verifier's owner-age semantics exactly, so this is an
  independent two-sided proof. Direct serialization of the MIR-derived lists
  (covering the edge-transfer temporary PCs inside one terminator) is the
  remaining migration step. Mandatory lower-register preparation now consumes
  deterministic final-block-order live intervals classified as owned, shared
  reference, unique reference, copy, or erased, and records addressable places.
  It retains the frozen ABI prefix and compacts live identities monotonically;
  physical reuse still awaits an explicit empty/ended-loan certificate in the
  lowered representation. Checked typed block kinds also group entry/RPO-normal,
  label, cleanup, handler, and resumption seeds deterministically before
  emission; successor-region propagation and lexical cleanup boundaries remain.
  A distinct reported `ValidateBytecodeInput` checkpoint now revalidates
  optimized MIR, re-derives every statement/terminator cleanup state, checks
  recorded destruction/drop-flag references against source-block ownership,
  and proves arbitrary public-`LEAVE` source/target suffix boundaries directly
  from MIR. Final label serialization now consumes that same centralized proof
  to build the exact protected-source/protected-result anchors. The enclosing
  compiler appends measured `LowerRegistersAndEdges`, `LayoutAndPeephole`, and
  `ValidateFinalArtifact` entries only after those stages run; their work and
  changed/unchanged outcomes are deterministic and never speculative. It still needs
  to derive all edge-transfer-temporary lists directly and thereby remove the
  seeded-bytecode-anchor completion step.
- **Not yet realized.** `Store`/`StorageLive`/`StorageDead` statements,
  persistent typed arenas for frozen move paths and source-storage scopes,
  multi-scope lexical export for cleanup, and frontend-emitted drop flags
  (branch post-states must agree at source level). Places and locals already
  have typed arenas; frozen typed control tables publish label, handler,
  performance, and resumption identities. Freezing derives the full lexical
  label/handler scope tree and validates innermost-first handler candidates.
  Typed `BlockId`/`BlockKind` and `MirOperationId` checked editors now perform
  transactional tombstoned deletion and precisely invalidated
  block/instruction mutation, and canonical resource limits fail structurally
  before optimization. Reusable, deterministic checked analyses
  now provide predecessors, reachability/RPO, dominators, natural loops and
  preheaders, irreducible SCCs, and edge liveness with structured work budgets
  and dependency-specific invalidation; LICM and identity-phi simplification
  consume them. Remaining mutation migration covers edge redirection, block
  splitting/merging, and operand/terminator replacement, while remaining
  analysis work covers place/alias/value/cost facts and lazy caching; the outer
  pass runner still invalidates changed passes conservatively. Source labels
  and `Leave` are implemented through MIR, cleanup validation, bytecode
  lowering, and O0-O3 execution.
