# Self-hosted compiler architecture

Status: architectural direction and migration contract for the Grandiose
self-hosted compiler.

This document describes the target shape of the compiler under `self-host/` and
the invariants that architectural refactors must preserve. It complements the
language, MIR, bytecode, and standard-library specifications; those documents
remain authoritative for semantics and wire compatibility.

## Goals

The self-hosted compiler should be small because it has a small number of shared
mechanisms, not because semantic cases are omitted or hidden in the VM.

The design aims to:

- compile one body at a time and release body-local syntax and Core scratch as
  soon as lowering finishes;
- keep source semantics in the compiler and runtime invariants in the verifier;
- use typed arena identities and borrowed semantic views at phase boundaries;
- avoid parallel representations of the same fact;
- keep deterministic ordering at diagnostic and artifact boundaries rather than
  forcing canonical allocation order throughout compilation;
- make ownership, borrowing, effects, cleanup, and nonlocal control explicit in
  the eventual MIR;
- permit library-defined control and compiler-building abstractions to
  specialize into direct loops, branches, and label transfers;
- preserve stage-2/stage-3 byte identity as the final bootstrap convergence
  criterion.

Compactness is a consequence of these rules. It is not permission to weaken
checking, diagnostics, cleanup, or artifact validation.

## Top-level ownership

The source tree has three top-level implementation roles:

```text
main.glorious
    |
    v
compiler/                orchestration, session ownership, host boundary
    |\
    | +-- frontend/       source-facing phase libraries
    |
    +---- backend/        lowering and artifact phase libraries
```

`frontend` and `backend` do not own the executable application. They expose
phase operations. The top-level `compiler` module decides phase order, owns
cross-phase state, and is the only self-host module called by the package entry
point.

This prevents filesystem, process-argument, and host-diagnostic capabilities
from becoming ambient dependencies of semantic phase APIs.

## Compilation session

A `CompilerSession` retains state whose lifetime spans more than one body and
borrows the original source text:

```text
CompilerSession
    borrowed source text
    parsed declaration headers
    declaration index
    global resolution index
    typed interfaces and shared semantic types
```

The session deliberately does **not** own a whole-program body AST or a
whole-program collection of resolved bodies.

Stage one currently visits every collected callable. For each callable, the
pipeline creates one `BodyCompilation`; demand-driven reachability is a later
optimization:

```text
BodyCompilation
    typed callable identity
    resolved name
    parsed body syntax
    body-local resolution
```

The body object is elaborated to Typed Core and immediately lowered. Its syntax,
resolution data, and Typed Core scratch then leave scope before the next body is
processed. The earlier driver already scoped these values per callback; stage
one makes that existing lifetime and its owner explicit. A later memory audit
must measure retention before claiming a release or peak-memory improvement.

Generic bodies may eventually retain compact Core while reachable
specializations are produced, but that exception must remain explicit and must
not turn into a duplicated persistent HIR.

## Semantic representations

There are exactly three persistent semantic representations:

1. declaration headers plus token ranges for unparsed bodies;
2. Typed Core for the language's trusted static and dynamic calculus;
3. ownership/control MIR with explicit control, cleanup, cancellation,
   resumption, and place semantics.

The body AST is transient. Encoder records, canonical pools, and temporary
instruction-selection data are serialization scratch, not additional semantic
IRs.

The current Stage-A backend is a migration representation. It should evolve
into the real ownership/control MIR or disappear when that MIR is introduced.
The final pipeline must not retain both a full MIR and an equivalent Stage
program.

## Phase contract

The intended pipeline is:

```text
source bundle
    -> lex
    -> structural declaration scan
    -> header, fixity, trait, impl, and effect collection
    -> global declaration index
    -> typed interfaces
    -> for each demanded body:
         parse body
         resolve body-local names
         elaborate expected types and static relations
         produce Typed Core
         lower to MIR and PlaceFlow facts
         release body-local scratch
    -> MIR optimization
    -> deterministic instruction selection and canonical pools
    -> GRBC artifact writer
    -> independent VM verification
```

A phase may consume a representation or borrow it, but should not copy it into a
parallel table solely to adapt storage layout. Phase boundaries expose semantic
views and typed identities rather than private arena tags or magic integer
codes.

## Shared kernels

The complete compiler should be organized around four reusable semantic
kernels:

### Callable

Named functions, anonymous callables, closures, handler clauses, and
resumptions share call checking, receiver modes, effect rows, capture layout,
`Fn`/`RunsIn` evidence, and lowering paths.

### Brand

Labels, execution environments, refinement environments, continuation
identities, and binder keys share one nominal identity mechanism with an
explicit kind and lifetime.

### Quantity

Ordinary ownership use, callable invocation, environment transitions,
resumption use, cancellation, and availability use one interval arithmetic and
containment implementation.

### PlaceFlow

Initialization, moves, loans, captures, continuation state, cleanup, and final
use are analyses or views over one sparse place-fact graph. New language
features must extend this shared graph rather than create a second ownership or
cleanup implementation.

## Shared implementation substrate

The next architecture stages should introduce a small compiler toolkit rather
than feature-specific utility layers:

- `IdRange<Tag>` for typed contiguous arena ranges;
- one source span and token span model;
- one token cursor backed by a precomputed delimiter-pair table;
- one lexical `ScopeMap` with journaled scope restoration;
- one structured diagnostic model with primary and related spans;
- one canonical pool abstraction with freeze-and-remap at serialization;
- one body-local Core builder;
- one checked MIR editor and analysis invalidation mask;
- small worklist and fixed-point runners.

These abstractions are justified only when they replace repeated mechanisms in
at least two real compiler phases.

## Diagnostics and failure

Compiler phases return structured errors or emit structured diagnostics. The
host application is responsible for rendering them.

The target diagnostic model contains:

```text
Diagnostic
    stable code
    primary span
    zero or more labeled related spans
    typed formatting arguments
    applicability when a fix is available
```

Internal invariant failures remain distinct from source diagnostics. Resource
limits are structured diagnostics rather than silent fallback or unbounded
recursion.

The stage-one session currently preserves the existing phase error enums while
reporting the failing phase at the host boundary. A later migration will replace
per-phase `code`, `token`, and `related` projection functions with the shared
model.

## Determinism

Arena allocation order is local to one compilation and need not be canonical.
Only externally observed products must be deterministic:

- diagnostics are sorted by stable source and code keys;
- strings, constants, signatures, and artifact records are frozen through
  canonical pools;
- map iteration never directly determines serialized order;
- once stage-2 and stage-3 bootstrapping exists, their compiler artifacts must
  be byte-identical before convergence is considered proven.

This separates efficient construction from reproducible output.

## Library-defined control

The compiler knows structural callable, label, effect, handler, and pattern
mechanisms. It does not recognize standard-library names such as `if`, `loop`,
`break`, `continue`, `return`, `try`, or traversal helper names.

Compiler-oriented helpers may use:

- effect-polymorphic range traversal;
- statically branded labels for early exit and propagation;
- label-indexed loop-control effects;
- cleanup-backed checkpoint guards;
- contextual callable blocks;
- typed builders and walkers.

The optimizer and control inliner must prove that hot helpers lower to direct
loops, branches, and `LEAVE` operations without residual runtime label objects,
dynamic handler lookup, or avoidable closure allocation.

Embedded compiler DSLs are a later layer on top of the explicit session,
representation, and PlaceFlow architecture. They must not precede or obscure
those foundations.

## Migration stages

### Stage 1: phase ownership and session boundaries

Implemented by the initial architecture change:

- move executable orchestration out of `backend`;
- make `frontend` and `backend` top-level phase libraries;
- introduce one `CompilerSession` for cross-body state;
- introduce one `BodyCompilation` for transient body syntax and resolution;
- make the existing one-body-at-a-time scope an explicit ownership contract;
- report the failing compiler phase at the host boundary;
- preserve existing frontend, Typed Core, lowering, emission, and artifact
  semantics.

### Stage 2: shared substrate and direct semantic views

- unify typed ranges and source spans;
- add delimiter pairing and a shared token cursor;
- replace duplicated numeric tags plus semantic enums with one source of truth;
- replace adapter maps between resolution and elaboration with direct typed
  tables;
- centralize diagnostics and resource-limit reporting;
- extract phase snapshot applications into a test/probe layer.

### Stage 3: ownership/control MIR and PlaceFlow

- evolve or replace Stage-A with the final MIR;
- move final-use inference from syntax walks to PlaceFlow;
- centralize moves, loans, captures, cleanup, and cancellation facts;
- introduce checked transactional MIR editing;
- export and validate the single PlaceFlow fact source used by bytecode cleanup
  metadata.

### Stage 4: deterministic backend substrate

- introduce canonical pools with freeze-and-remap;
- compute semantic type facts once outside emission;
- make artifact section and opcode layout schema-driven;
- keep assembler data transient and avoid a fourth semantic IR.

### Stage 5: compiler-oriented control and embedded DSLs

- control-aware walkers and worklists;
- parser checkpoint and grammar helpers;
- typed Core and MIR builder effects;
- declarative PlaceFlow event descriptions;
- pattern-directed checked rewrite rules;
- control-specialization and residual-allocation inspection tools.

Each abstraction/toolkit stage must retain a direct implementation escape hatch
and must show a net reduction after including its shared toolkit. Stage one is
an ownership-boundary refactor; its value is the explicit boundary that enables
later consolidation, not an immediate line-count reduction.

## Review rules

Architectural changes to the self-hosted compiler should answer:

1. Which representation owns this fact?
2. Is the fact copied into another persistent representation?
3. Is the state session-wide, body-local, or operation-local?
4. Does this create a new ownership, cleanup, effect, or control mechanism?
5. Can the abstraction preserve exact callback effects and use quantities?
6. Does `-O2` erase the abstraction where required?
7. Are diagnostics and artifacts deterministic?
8. Can body-local scratch be released at the intended boundary?
9. Is the new code smaller after counting shared infrastructure?
10. Does the change preserve independent bytecode verification?

A change that cannot identify a clear owner for its data should not add another
adapter table. A change that introduces a fourth semantic representation
requires an explicit architecture review.
