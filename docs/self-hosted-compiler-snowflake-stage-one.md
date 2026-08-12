# Snowflake Stage One: The Ideal Self-Hosted Glorious Compiler

> **The Glorious compiler should be a deterministic, queryable, incrementally cached semantic engine that treats a program as a graph of facts, lowers each demanded body through a small number of explicit representations, produces independently verified executable artifacts, and can explain every conclusion, dependency, optimization, and cache decision it makes.**

## The compiler we want

We do not want the self-hosted Glorious compiler to be merely a translation program that accepts source files and eventually emits bytecode. We want it to be the authoritative semantic intelligence for the entire Glorious ecosystem.

The command-line compiler, package manager, language server, formatter, documentation generator, test runner, editor integrations, static-analysis tools, and future refactoring tools should all be clients of the same compiler library. There should not be one compiler for builds, a second approximation inside the language server, and a third partial parser inside the formatter. There should be one semantic engine with several ways of asking it questions.

The compiler should understand a Glorious package as a durable, queryable body of knowledge:

- what declarations exist;
- what each name resolves to;
- what type, effect row, use interval, and lifetime every expression has;
- which value is moved, copied, borrowed, captured, resumed, cancelled, or destroyed;
- why a trait or effect obligation was accepted or rejected;
- how source-defined control was specialized;
- which MIR operation arose from a source expression;
- which bytecode range implements a function;
- which previous result was reused from cache;
- and exactly why a change caused another result to be recomputed.

A successful build is only one large query over this database. An editor hover, a rename, a documentation page, a compile-fail test, and an optimizer inspection are smaller queries over the same underlying facts.

The compiler should therefore be designed less like a one-way assembly line and more like a **semantic database with a lowering and verification engine attached to it**.

## The overall shape

The complete toolchain should have a strict separation between orchestration and semantics.

The `grand` build tool should own package acquisition, lockfiles, workspaces, filesystem discovery, dependency fetching, vendoring, and user-facing build orchestration. It should convert the outside world into a hermetic compilation request containing:

- the exact source files;
- the package and module layout;
- dependency interfaces;
- compiler options;
- optimization level;
- target information;
- the standard-library identity;
- the capability manifest;
- and explicit resource limits.

The compiler core should not perform network access or discover dependencies on its own. It should receive complete inputs and return complete outputs. Its semantic phases should not depend on ambient process arguments, current directories, environment variables, or arbitrary filesystem access.

At the center of the compiler should be a `CompilerDatabase`. This database should own immutable source revisions, stable declaration identities, interned names and types, query caches, dependency information, diagnostics, and persistent artifact references. A single request should observe one coherent source revision; results from two revisions must never be mixed accidentally.

Around that database, the compiler should expose typed query families. Conceptually, these would include queries such as:

```text
tokens(file)
module_outline(module)
item_header(definition)
package_interface(package)
body_syntax(body)
resolved_body(body)
typed_core(body)
place_flow(body)
mir(body)
optimized_mir(instance, optimization_level)
emitted_function(instance, target)
linked_artifact(package, target)
verified_artifact(package, target)
```

There should also be source-facing semantic queries:

```text
definition_at(file, position)
type_at(file, position)
effects_at(file, position)
quantity_at(file, position)
borrow_state_at(file, position)
references_to(definition)
implementations_of(trait)
callers_of(function)
control_plan(body)
why_recompiled(query)
```

These are not separate tools bolted onto the compiler. They are the compiler.

## A typed query system rather than a dynamic framework

The query engine should be powerful, but it should remain small enough to self-host and audit.

We should not build a highly reflective framework in which every query accepts and returns dynamically typed boxes. Each query family should have a statically known key and value type. The shared engine should provide dependency tracking, memoization, cycle detection, persistence, invalidation, cancellation, and statistics, while the query implementations remain ordinary typed Glorious functions.

Conceptually:

```text
typed_core(body: BodyKey) -> Analysis<TypedCoreBody>
layout(ty: TypeKey, target: TargetKey) -> Analysis<Layout>
trait_goal(goal: CanonicalGoal) -> Analysis<GoalResult>
```

An `Analysis<T>` should be able to carry a successful value, structured diagnostics, dependency fingerprints, source mappings, and an indication that the result is incomplete because an editor request encountered broken source. Compiler queries used for release builds may require complete values, while IDE queries may use recovered or provisional values.

Whenever one query asks for another, the engine should record that dependency automatically. This could be implemented with a narrow internal query effect or with an explicit `QueryContext`, but query authors should not manually maintain dependency lists. The semantic code should express what it needs; the engine should remember why the result depends on those inputs.

The same mechanism should support explanation. A user should be able to ask why a body was rechecked and receive a chain such as:

```text
optimized_mir(Parser::parse<u8>)
  changed because mir(Parser::parse<u8>) changed
  changed because typed_core(Parser::parse) changed
  changed because the interface of Result<T, E> changed
  changed because dependency package core changed its exported interface
```

This is as important for compiler developers as it is for users.

## Stable identities and local identities

The compiler needs two kinds of identity.

Stable identities should identify packages, modules, declarations, generic instances, source files, and externally visible facts across compiler invocations. They should be derived from semantic paths, package identities, declaration kinds, and stable disambiguators rather than from arena allocation order.

Local identities should be compact typed indices used inside one query or one body compilation:

```text
ExprId
TypeId
LocalId
PlaceId
BlockId
LoanId
ControlSiteId
```

Local IDs should never be mistaken for persistent cache keys. They may be allocated in whatever order is efficient. When a query result is persisted, its externally meaningful data should be serialized canonically, without depending on accidental arena numbering.

Anonymous callables, closures, handlers, and generated control sites should receive stable keys derived from their owning definition and a stable syntax anchor. Small edits should not invalidate every anonymous object later in the file merely because its temporary numeric index changed.

The rule should be simple:

> Stable identities cross query, package, and process boundaries. Typed arena identities remain local to one semantic result.

## Three semantic representations

The compiler should aggressively resist representation growth. The ideal design has three semantic strata.

### 1. The source model

The source model contains immutable text, lossless tokens, delimiter pairing, module structure, declaration headers, fixities, visibility, and token ranges for bodies.

It should not retain a complete whole-program body AST by default. Top-level scanning should identify interfaces and body boundaries cheaply. A body should be parsed when a query actually demands it. Its syntax tree may then be discarded after elaboration unless an active editor or formatter request still needs it.

The lossless token layer should be shared by diagnostics, formatting, source mapping, semantic highlighting, and refactoring. There should not be a separate lexer for the formatter or editor.

The parser should understand structural syntax, not standard-library control names. It should know calls, blocks, labels, effects, handlers, patterns, declarations, and operator streams. Fixity collection should happen before operator grouping. A declaration named `if` or `loop` should have no privileged parser status.

### 2. Typed Core

Typed Core should express the smallest trusted semantic calculus of Glorious.

It should contain ordinary and anonymous callables, nominal values, projections, calls, labels and transfers, effects, handlers, resumptions, cancellation, borrowing, construction, destruction, host imports, and finite machine primitives.

It should not contain compiler-known nodes called `if`, `match`, `loop`, `return`, `await`, or `yield`. Those names remain source-library abstractions. By the time source reaches Typed Core, their behavior should have been expressed through the real structural mechanisms of the language.

Typed Core should carry enough evidence to establish types, traits, effects, quantities, lifetimes, and control legality. Evidence that exists only for static checking should be erased before code generation, but it should remain queryable for diagnostics and tooling.

### 3. Ownership and control MIR

MIR should be the single explicit operational representation.

It should be an SSA-like control-flow graph with typed block parameters, places, moves, copies, borrows, calls, switches, effects, handlers, resumptions, cancellation, labels, cleanup, destruction, host calls, returns, tail calls, and aborts.

All important control edges should be explicit:

- ordinary successors;
- cleanup successors;
- cancellation successors;
- handler dispatch;
- resumption entry;
- nonlocal label transfer;
- failed initialization;
- and unwinding-like abandonment where Glorious permits it.

MIR should be accompanied by one shared `PlaceFlow` fact graph. Initialization, moves, partial moves, loans, captures, final use, continuation snapshots, cleanup obligations, and must-move checking should all be views over this one graph. We should never create one ownership model for ordinary code, a second for closures, a third for handlers, and a fourth for cleanup.

The bytecode artifact is not a fourth semantic IR. Encoder records, constant pools, relocation tables, and register assignments are serialization scratch derived from MIR.

## The four shared semantic kernels

The compiler should be organized around a small number of mechanisms that recur throughout the language.

### Callable

Named functions, closures, anonymous blocks, handler clauses, function items, and resumptions should share call checking, receiver modes, capture layout, effect rows, quantitative invocation, and lowering rules.

A resumption is unusual, but it is still callable. A handler clause is unusual, but it still has arguments, captures, effects, and a result. The compiler should exploit those commonalities rather than implement each feature independently.

### Brand

Labels, callable environments, refinement environments, handler identities, continuation identities, and binder keys all require fresh nominal identity. They should use one branded-identity substrate with explicit kinds and lifetimes.

### Quantity

Ordinary value use, callable invocation, environment entry, continuation resumption, cancellation, and availability should use one interval arithmetic and containment engine.

This is the heart of Glorious. The compiler must be able to explain not merely that a quantity check failed, but how the interval was computed across sequencing, branching, repetition, capture, replay, and cancellation.

### PlaceFlow

Moves, initialization, borrowing, captures, cleanup, partial destruction, and continuation state should be derived from one sparse place graph and one family of fixed-point analyses.

These four kernels should shape the compiler’s modules, tests, diagnostics, and query APIs.

## The end-to-end compilation path

A full build should proceed conceptually as follows.

First, `grand` constructs a complete compilation request and passes it into the compiler library.

The compiler fingerprints all direct inputs and creates or reuses a source revision. It lexes changed files, pairs delimiters, and structurally scans modules. It collects declaration headers, effect declarations, trait and implementation heads, visibility, fixities, aliases, and exported interfaces.

Package dependencies should normally be consumed through compact interface artifacts rather than by reparsing their entire source. A dependency interface should contain exported types, signatures, traits, implementations, effects, fixities, layout-relevant facts, and any generic bodies required for downstream specialization. A downstream package should not be invalidated when a dependency changes an unexported implementation detail.

Bodies should then be compiled on demand. For each reachable body, the compiler should:

1. parse the body from its recorded token range;
2. resolve local and global names;
3. elaborate expected types;
4. solve traits, associated types, effects, quantities, and const relationships;
5. infer captures and lifetimes;
6. produce Typed Core;
7. lower immediately into MIR and PlaceFlow;
8. validate the resulting MIR;
9. release body-local syntax and inference scratch.

Generic instances should be discovered demand-first. A query key should identify a declaration plus canonical type, const, lifetime, effect, and quantity substitutions. Monomorphized or otherwise specialized MIR should be cached per instance.

The optimizer should operate per body or per instance wherever possible. It may request interprocedural summaries of callees without forcing every body into memory. Reachable emitted functions should then be assembled into one deterministic artifact with canonical pools, sealed host capabilities, stable metadata, and complete source maps.

Finally, `grvm` should independently decode and verify the artifact before execution or release.

## Incremental compilation and caching

Caching should exist at three levels.

### In-memory memoization

Within one compiler process, every query result should be memoized by its typed key and input fingerprint. Repeated editor requests, diagnostics, hovers, and build steps should reuse the same facts.

Memory pressure should be managed deliberately. Compact interfaces, type tables, and summaries may remain resident, while large syntax trees, Typed Core bodies, MIR bodies, and optimizer scratch can be evicted through a deterministic LRU policy. Eviction must never change compiler semantics.

### Persistent semantic caching

Expensive query results should be serialized into a content-addressed persistent store. Suitable entries include:

- package interfaces;
- parsed body summaries;
- Typed Core bodies;
- trait-solver tables where safely reusable;
- validated MIR;
- optimized MIR;
- emitted function fragments;
- native object fragments;
- and verified bytecode sections.

A persistent cache key should include every semantic input that can affect the result:

- compiler build identity;
- query schema version;
- language generation;
- standard-library fingerprint;
- package and dependency interface fingerprints;
- source or body fingerprint;
- target;
- optimization level;
- enabled features;
- lint policy where relevant;
- capability manifest where relevant;
- and code-generation options.

Cache entries should be treated as untrusted optimization hints. They should have checksums and schema identifiers. Deserialized Core and MIR should pass structural validation. A malformed, stale, or incompatible entry should be ignored rather than trusted.

A warm build and a cold build must produce byte-for-byte identical final artifacts.

### Final artifact caching

A verified package artifact may be cached by the complete build manifest. When all inputs are identical, the compiler should be able to return the previously verified `.grbc` artifact without reconstructing its intermediate state.

The build manifest should record enough information to reproduce the artifact exactly.

## Precise invalidation

Incrementality is only valuable when invalidation is narrow and understandable.

Changing a function body should normally invalidate that body’s parsing, elaboration, MIR, optimization, and emitted function. It should not invalidate unrelated bodies.

Changing a private function signature should invalidate its callers inside the package.

Changing an exported interface should invalidate downstream packages that depend on that interface.

Changing a generic body should invalidate only discovered instances that depend on that body.

Changing an implementation may invalidate canonical trait goals that could select it, but the trait solver should record these dependencies explicitly rather than flushing every table.

Changing a fixity should invalidate bodies whose operator grouping depends on it.

Changing a capability manifest should invalidate linking and verification, and any semantic query whose host-import legality depends on that manifest.

The compiler should expose an invalidation trace so that unexpectedly large rebuilds can be treated as compiler bugs.

## Cycles and fixed points

A query engine for a real compiler must understand cycles.

Some cycles are legal and require a fixed point:

- mutually recursive declarations;
- recursive trait reasoning;
- effect-row relationships;
- quantitative recursion;
- layout or ownership facts for recursive nominal types;
- call-graph summaries;
- and dataflow analyses over loops.

Other cycles are errors:

- forbidden constant initialization cycles;
- unsound type aliases;
- cyclic module definitions without a legal interface boundary;
- or query recursion caused by an internal architectural mistake.

The query engine should not merely report “cycle detected.” Each query family should declare whether it is acyclic, SCC-based, coinductive, or fixed-point driven. Legal cycles should use deterministic worklists with explicit widening or convergence rules. Illegal cycles should produce structured source diagnostics or internal invariant failures, depending on their origin.

## Diagnostics as first-class results

Diagnostics should not be strings printed from deep inside compiler phases.

A diagnostic should have:

- a stable code;
- a severity and class;
- a primary source location;
- related locations;
- the owning declaration;
- expected and observed semantic facts;
- notes;
- machine-applicable fixes where safe;
- and an optional explanation chain.

User errors, resource-limit failures, cancelled requests, corrupted cache entries, verifier failures, and compiler invariant failures must remain distinct.

Inside the self-hosted compiler, an internal `Report` effect may make recoverable diagnostics convenient, while terminal phase failure may use a typed abort effect or label. The outer query boundary should handle those effects and return diagnostics as data.

The compiler should be particularly good at explaining Glorious-specific failures:

- why a value’s computed use interval does not fit its principal interval;
- which path failed to consume a must-move value;
- why continuation replay duplicates a captured owner;
- why cancellation would abandon an exact-positive obligation;
- why a private field prevents deconstruction;
- why an effect escaped a handler;
- why a loan crosses a suspension point;
- or why source-defined control could not be fused.

A language with sophisticated semantics must have unusually sophisticated explanations.

## A compiler that can explain itself

Every important intermediate fact should be inspectable.

A developer should be able to ask for:

- the tokens and structural outline of a source file;
- a declaration’s resolved interface;
- the inferred type, effects, quantities, and lifetimes of an expression;
- canonical trait goals and selected implementations;
- capture and environment summaries;
- PlaceFlow facts;
- raw and optimized MIR;
- cleanup plans;
- continuation capture plans;
- register assignments;
- bytecode ranges;
- verifier states;
- control-fusion results;
- optimization pass reports;
- and query dependency graphs.

The compiler should support focused inspection by source span, declaration, function, MIR block, bytecode program counter, or query key.

It should also support comparison:

```text
compare O0 and O2 MIR
compare cold and warm builds
compare Rust bootstrap and self-hosted results
compare stage 2 and stage 3 artifacts
compare a query before and after an edit
```

This is not optional debugging luxury. A self-hosting compiler with effects, quantities, borrowing, cleanup, and resumptions will otherwise become impossible to evolve confidently.

## Optimization

The optimizer should be deterministic, query-driven, and semantically conservative.

Analyses should be grouped into reusable bundles such as:

- CFG and reachability;
- liveness and uses;
- ownership, loans, and cleanup;
- effects, captures, and call summaries;
- scalar and aggregate facts;
- cost and code-size estimates.

Each transformation should declare which bundles it invalidates. Passes should run to bounded fixed points, with explicit budgets and deterministic ordering.

The optimizer’s most important Glorious-specific responsibility is source-defined control specialization. It should identify when library abstractions representing conditionals, loops, pattern selection, propagation, early exit, and effect handling can be transformed into direct MIR control.

A `control_plan` query should explain:

- which callables are statically known;
- which labels are proof-only;
- which handlers are removable;
- which continuation is one-shot;
- which quantities justify specialization;
- what direct loop or branch was formed;
- and what residual runtime machinery remains.

If an abstraction fails to fuse, the compiler should say why.

Ordinary optimizations should include constant propagation, CFG simplification, aggregate scalar replacement, devirtualization, capture shrinking, handler specialization, continuation-allocation elimination, inlining, cleanup merging, borrow erasure after proof, tail-call formation, register reuse, and bytecode peepholes.

No optimization may weaken:

- traps;
- left-to-right evaluation;
- quantitative use;
- borrow legality;
- cleanup order;
- custom destruction;
- effect boundaries;
- cancellation behavior;
- or host-capability checks.

Optimized MIR should pass the same validators as unoptimized MIR.

## Determinism and reproducibility

Internal construction should be efficient rather than artificially canonical. Arena allocation order may vary locally. Hash tables may be used where appropriate.

Externally observable results must be deterministic.

Diagnostics should be sorted by stable source keys. Interfaces should be canonical. Constant pools, strings, signatures, function records, and bytecode sections should be frozen into deterministic order. Map iteration must never directly determine artifact order.

The compiler should be able to build the same inputs twice and produce byte-identical artifacts regardless of cache warmth.

Self-hosting raises the standard further: stage 2 and stage 3 compiler artifacts must be byte-identical before bootstrap convergence is declared.

## Resource limits and cancellation

The compiler must remain safe under hostile or pathological source.

Every recursive or expanding subsystem should have explicit structural limits:

- tokens;
- nesting;
- declarations;
- type depth;
- trait goals;
- monomorphizations;
- MIR blocks;
- places;
- loans;
- control sites;
- continuation captures;
- optimizer work;
- artifact sections;
- and diagnostic volume.

Limits should produce structured resource diagnostics rather than stack overflow, unbounded allocation, or silent degradation.

Queries should support cancellation. An editor should be able to abandon an obsolete revision without corrupting caches. Cancelled or budget-exhausted results should not be persisted as successful facts.

The self-hosted compiler should compile one body at a time and release transient storage promptly. Its memory architecture should be measured continuously, especially when compiling itself.

## The compiler written in Glorious

The compiler should use Glorious’s strengths without turning into a demonstration of cleverness at the expense of clarity.

Typed IDs, private fields, deterministic collections, quantitative guards, algebraic data, exact effect rows, branded labels, and cleanup-backed rollback are all natural tools for compiler construction.

Parser transactions can use affine checkpoint guards that must either commit or restore state. Diagnostic propagation can use effects. Search, traversal, and fixed-point algorithms can use source-defined control that the optimizer fuses into direct loops. Typed arenas can prevent one identity space from being confused with another.

Hot compiler state should still be explicit. We should not hide every mutation behind a general effect. A `CompilerSession`, `BodyContext`, `LoweringContext`, and `EmissionContext` should own clear data. Effects should be reserved for genuine nonlocal concerns such as diagnostics, cancellation, query demands, and phase termination.

The release compiler must not depend on a hidden Rust evaluator for Glorious semantics. Rust may remain the implementation language of the bootstrap compiler, VM, supervisor, and verifier during the transition, but the self-hosted compiler’s semantic decisions must eventually be authoritative and independently comparable.

## Bootstrap and release

The bootstrap story should be explicit.

A trusted stage-0 Rust compiler should compile the Glorious compiler source into a stage-1 verified bytecode compiler.

Stage 1 should compile the same source into stage 2.

Stage 2 should compile the same source into stage 3.

Stage 2 and stage 3 must be byte-for-byte identical under a fixed source bundle, standard library, manifest, target, and optimization configuration.

A release should contain:

- the Glorious compiler source;
- the standard-library source;
- the canonical seed artifact;
- the VM and verifier;
- the exact build manifest;
- checksums;
- the cache and artifact schema versions;
- and commands that reproduce the convergence check.

“Self-hosted” should mean that the Glorious compiler can compile itself. “Bootstrap-converged” should be reserved for the stronger stage-2/stage-3 identity result.

## The user-facing compiler

The ideal compiler should feel like a precise instrument rather than a black box.

Ordinary users should have simple commands for checking, building, running, testing, formatting, documenting, and fixing code.

Advanced users should be able to ask questions such as:

```text
What is the exact type and effect row here?
Why is this value moved instead of copied?
Which path fails to consume this resource?
What does this continuation capture?
Why can this handler resume twice?
Which implementation satisfied this trait goal?
Did this source-defined loop fuse?
Why did this body rebuild?
Which cache entry was used?
Which MIR block corresponds to this line?
Which bytecode instructions implement this function?
```

The language server should answer these through the same query database used by release builds. Documentation should use resolved interfaces from the same database. Refactoring should use the same identity and reference maps. Compile-fail tests should compare structured diagnostics rather than loosely matching terminal text.

## Architectural guardrails

Several rules should remain non-negotiable:

- No compiler-known semantics for standard-library control names.
- No second compiler hidden inside the language server.
- No ambient filesystem or network access in semantic phases.
- No persistent whole-program body AST unless measurement proves it necessary.
- No untyped numeric identity crossing phase boundaries.
- No parallel ownership models for closures, effects, cleanup, and ordinary code.
- No fourth persistent semantic IR between MIR and bytecode.
- No cache result that can change semantics.
- No optimization that cannot be inspected.
- No bootstrap-convergence claim without byte identity.
- No verifier claim confused with formal verification.
- No large invalidation event without an explainable dependency cause.

## The first snowflake

The compiler we are designing is therefore not merely a Glorious program that compiles Glorious programs.

It is a self-describing semantic machine.

It reads a hermetic package snapshot and turns it into a graph of stable, queryable facts. It computes only the bodies and instances that are demanded. It remembers valid work across requests and compiler runs. It invalidates narrowly when inputs change. It lowers source through a compact Typed Core into one explicit ownership-and-control MIR. It specializes source-defined control into efficient direct execution. It emits deterministic bytecode, seals exact capabilities, and submits the artifact to an independent verifier.

At every stage, it can answer not just **what** it concluded, but **why**.

That should be the defining character of the best compiler written in Glorious, for Glorious: not only powerful and correct, but inspectable, reproducible, incremental, self-hosting, and honest about every decision it makes.
