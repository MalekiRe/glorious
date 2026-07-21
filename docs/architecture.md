# Grandiose VM and Self-Hosting Compiler Architecture

Status: normative architecture for bytecode generation 1. The binary contract is
specified in [bytecode.md](bytecode.md). Language semantics are specified by
[the language core](../glorious-branded-environment-core-spec.md); where this
document disagrees with the language specification, the language specification
wins.

The standard-library and source-bundle contract is [std-lib.md](std-lib.md).
The compact implementation constraints are summarized in
[size-speed-review.md](size-speed-review.md); the detailed frontend and MIR
contracts are [frontend-design.md](frontend-design.md) and
[mir-design.md](mir-design.md).

## 1. Goals and boundaries

The implementation has three deliverables:

1. `grvm`, a safe Rust verifier and bytecode virtual machine;
2. `grc`, a compiler written in Grandiose and distributed as verified bytecode;
3. a Grandiose bootstrap standard library that defines conventional control,
   collections, formatting, and compiler-building utilities in source rather
   than in the compiler or VM.

The compiler must compile its own source and standard library at `-O2` in less
than 120 seconds and 4096 MiB in a cold supervised process. Stage 2 and stage 3
compiler artifacts must be byte-for-byte identical. Compactness is pursued through shared
representations, arenas, table-driven logic, and few abstraction layers. The
stretch budgets are 6,000 nonblank noncomment Grandiose lines for the
frontend/static core, 3,000–5,000 for MIR optimization and bytecode emission, and
6,000–9,000 for the complete bootstrap standard library. Thus 9,000–12,000
compiler lines is the expected complete range, plus the standard library.
Crossing 14,000 compiler lines triggers an architecture review;
conformance or optimization is never removed merely to meet a budget.
The library budget includes the deliberately explicit checked-conversion
matrix, deterministic collections, diagnostic/source-map support, and the
compiler toolkit; mechanically repetitive APIs are reviewed for generation or
generic expression but are not deleted merely to hit a line count.

The compiler provides structured source modules and explicit package roots, but
does not itself provide package acquisition/version selection, FFI, unsafe
Grandiose, threads, distributed builds, or a native backend in generation 1. The compiler
must not recognize source declarations named `if`, `match`, `loop`, `return`,
`yield`, `await`, arithmetic operators, or any other standard-library control
name.

## 2. Component model

```text
standard library + Grandiose source files
        |
        v
 lexer -> structural parser -> interface/fixity collection -> resolution
        -> typed elaboration -> Typed Core -> ownership/control MIR
        -> MIR optimization -> deterministic bytecode writer
                                      |
                                      v
                              .grbc artifact
                                      |
                 +--------------------+--------------------+
                 |                                         |
          decoder + verifier                         supervisor process
                 |                                         |
                 +--------------> safe VM worker <----------+
                                      |
                              capability host calls
```

The Rust runtime crate owns decoding, verification, execution, host capability
adaptation, and process supervision. It contains no parser or language type
checker. The Grandiose compiler owns all source semantics, cleanup insertion,
and optimization. The bytecode verifier checks the lowered runtime invariants;
it does not repeat trait solving or source borrow inference.

The existing AST interpreter may execute the first compiler generation and
remains a recovery bootstrap tool. It is a differential oracle only for the
documented compatibility intersection: the compared program must first be
accepted by the current compiler and must avoid semantics the interpreter does
not model, including ownership disposition, cleanup, and private-field
authority. Interpreter acceptance is never evidence that a source program
satisfies `Use`, must-move, borrowing, privacy, or cleanup rules. Existing
compiler code is neither an architectural input nor part of the bootstrap
chain.

## 3. Compiler architecture

The implementation has four reusable kernels, not one subsystem per language
feature:

1. **Callable:** named/anonymous functions, closures, handler clauses, and
   resumptions share one record, call checker, capture layout, `Fn`/`RunsIn`
   synthesis path, and lowering path.
2. **Brand:** label identities, execution/refinement/continuation environments,
   and binder keys share one fresh nominal identity table with a kind tag,
   lifetime, evidence range, and optional runtime realization.
3. **Quantity:** ordinary consumption, callable invocation, environment
   transition, resumption use, cancellation, and availability all use the same
   principal/actual interval arithmetic and containment check.
4. **PlaceFlow:** initialization, moves, loans, captures, environment summaries,
   continuation capture, and cleanup are views over one sparse place-fact graph.

Traits and evidence connect these kernels; they do not create parallel ownership
or control implementations.

### 3.1 Shared representation rules

The compiler uses append-only `u32` arena IDs for declarations, types, regions,
places, blocks, values, trait goals, and strings. IDs are local to one
compilation and never form a bytecode ABI. Allocation order therefore need not be
canonical: only diagnostics and serialized output are sorted. Strings and fully
resolved type/goal terms are interned; terms containing inference variables stay
in a temporary body arena and are interned once when zonked. Source spans are the
inline pair `(start, end)` into the concatenated source bundle; a segment table
recovers original file names and lines and supplies the source-entry identity
used for private-field access checks. Spans never participate in semantic
equality, and source-entry identity is erased after those checks.

There are exactly three semantic program representations:

- declaration headers plus token ranges for bodies, preserving source order and
  spans; an individual body AST exists only while that body is checked;
- Typed Core, representing only the trusted static/dynamic calculus from the
  language specification;
- ownership/control MIR, an SSA-style CFG with explicit places and cleanup,
  cancellation, resumption, and nonlocal-control edges.

After interface and fixity collection, a body is parsed, resolved, elaborated to
Typed Core, lowered to MIR, and its AST/Core scratch arenas are reclaimed. Generic
bodies retain compact Core only until their reachable monomorphizations exist.
There is no duplicated HIR or whole-program body AST.

### 3.2 Frontend and elaboration

The declaration scanner recognizes top-level boundaries and records body token
ranges without building body trees. The body parser recognizes callable syntax,
labels, handlers, core `is`, and ungrouped operator streams and does not classify
a trailing block as eager or delayed. Compilation then proceeds in this order:

1. collect declaration interfaces, source fixities, trait/impl heads, and
   effect declarations;
2. parse each demanded body, resolve names, and group its flat operators using
   the already collected fixities;
3. create fresh callable, label, binder-key, and provisional environment brands;
4. elaborate expressions against expected types and select call candidates;
5. interpret a trailing block as a callable only when the selected parameter is
   constrained by an applicable `Fn<Args>` goal; otherwise elaborate it eagerly;
6. solve static relations, lower `is`, insert cleanup, and seal environments;
7. erase static evidence and lower that body before moving to the next body.

Expected-type ambiguity is an error. Argument evaluation and construction-field
evaluation are always left to right.

### 3.3 Static checking

One checking state implements the specification's
`Gamma ; Delta ; Omega ; Lambda ; Pi` judgment:

- `Gamma`: declarations, nominal types, traits, impls, const quantities,
  lifetimes, variance, and effect rows;
- `Delta`: initialized places, moves, shared/unique loans, and ordinary owners;
- `Omega`: open/sealed environment brands and their access and post-states;
- `Lambda`: label brands, destination evidence, lifetimes, and runtime targets;
- `Pi`: normalized active protocols and handler evidence.

Trait solving is canonicalized and tabled. It supports coherent nominal impls,
orphan rules, associated types/effect rows, structural const values, GATs,
higher-ranked lifetime placeholders, associated-type equality, and restricted
negative reasoning. It has no specialization, overlapping impl selection, or
trait objects. Compiler-generated evidence for unnameable types is lexical and
does not enter global coherence.

`Use` is solved by a dedicated principal-interval engine. Sequential paths add,
exclusive paths take their hull, repetition widens, and nested execution
multiplies. A requested interval must be contained in the type's single
principal interval. A positive principal lower bound creates a must-move
obligation on every normally completing path. Whole transfer propagates that
obligation. Opaque explicit or implicit destruction contributes zero and requires
`Use<[0,0]>`; cleanup cannot satisfy or discard a must-move value. Immediate
abort and proven nontermination are the only no-successor exceptions.
For duplicable values, bare owned use may copy and leaves the original owner
live; contextual `move value` forces transfer. Every copy receives its own
obligation, so copies alone never discharge the original must-move place.

G1 memoized globals require the unrestricted principal `Use` interval. A global
can be read from an unbounded number of call sites and executions, so the
compiler rejects a restricted-use global result rather than manufacturing
singleton or bounded-read evidence.

The bootstrap exports the `PlaceFlow` conclusions from MIR lowering as a
per-body fact table; the backend's `ImportAndValidatePlaceFlow` phase validates
them against the instructions and a deterministic ownership fixed point instead
of re-deriving them, `ElaborateCleanup` attaches exact cleanup plans to every
abandoning edge, and the serialized bytecode cleanup maps are cross-validated
against those facts (see `docs/mir-design.md` section 13).

Borrow checking operates on the shared `PlaceFlow` CFG and move paths. It
performs nonlexical region inference, shared and unique reborrowing,
variance/outlives propagation, higher-ranked leak checking, and drop checking.
It rejects partial moves from a custom-`Drop` type and escape of any reference,
label, environment, handler, or refinement dependency.

Open environment elaboration remains open across the complete linked call or
operator expression. Each body contributes places, access modes, effects,
lifetime requirements, and a post-state. The compiler checks overlap and joins,
synthesizes `RunsIn` evidence, and then seals the fresh nominal identity.

One pattern decision-DAG builder serves handler clauses and `is`. `is` evaluates
its subject once, creates positive and negative binding environments, and is
fully lowered to ordinary handler dispatch, enum construction, and binding-pack
values before Typed Core.

An exhaustive ownership-moving pattern consumes the aggregate shell and creates
field move paths with their own obligations. Field visibility is checked before
that transition, so private fields make the shell opaque outside authorized
scope. Wildcards, rest patterns, and omissions are zero-use subtree destruction
and require `Use<[0,0]>` for what they discard.

### 3.4 Typed Core

Typed Core contains construction, projection, values, calls, guaranteed tail
calls, labels and `leave`, effects and deep handlers, resumptions and
cancellation, explicit destruction, finite machine primitives, and manifest-bound
host-import calls at the finite trusted boundary. It may carry
static evidence while being checked, but label/environment brands, lifetimes,
`Fn`/`RunsIn`/`Use` evidence, and refinement facts are erased before bytecode.

It never contains semantic nodes equivalent to `if`, `else`, `match`, loops,
`break`, `continue`, `return`, `yield`, `await`, failure, Boolean operations,
arithmetic, or comparison. The standard library constructs those facilities from
callables, nominal data, labels, handlers, and primitives.

### 3.5 MIR

MIR uses blocks with typed parameters and these operations:

- operands: constants, callable references, `Move`, and `Copy`;
- rvalues: primitives, aggregates, projections, borrows, closures, and handlers;
- statements: storage live/dead, assignment, borrow end, and destruction;
- terminators: jump, switch, call, host call, tail call, return, leave, perform,
  resume, cancel, abort, and unreachable.

Normal, cleanup, cancellation, resumption, and nonlocal-transfer edges are
explicit. Cleanup blocks are shared by normal exit, terminal effects, labels,
cancellation, and failed initialization only when every abandoned subtree permits
zero use. Nonlocal cleanup may not discard a must-move value. `Drop` has the
frozen bound `Use<[0,0]>`, so positive-lower types cannot implement it; hooks run
once before active zero-use fields are destroyed in reverse declaration order.
Panic is immediate abort and has no cleanup edge.

Optimizer differential tests lower each selected MIR prefix to bytecode and run
it in the VM. Together with the existing source interpreter this avoids embedding
a second complete effect/continuation runtime in the self-hosted compiler.

### 3.6 Optimization contract

Analyses are computed on demand in six body-local bundles: CFG, uses/liveness,
ownership/loans/drop, effects/captures/calls, scalar value facts, and cost. A
mutation invalidates bundles through a compact bit mask; generation 1 has no
incremental repair or preservation-certificate framework. Transformation groups
run to a bounded fixed point where useful:

1. CFG normalization, unreachable removal, critical-edge splitting, and block
   parameter simplification;
2. constant evaluation, SCCP, copy propagation, switch simplification, and dead
   assignment/storage removal;
3. scalar replacement, projection/tag propagation, redundant aggregate removal,
   combined value numbering/CSE, and local memory forwarding;
4. devirtualization, function-item propagation, capture shrinking, and
   nonescaping closure scalarization;
5. effect-row and handler specialization, terminal-handler simplification,
   continuation-allocation elision, and resumption specialization;
6. drop-flag simplification, legal dead-drop removal, cleanup merging, and
   destruction-chain specialization;
7. borrow/reference erasure after ownership-sensitive passes;
8. costed inlining with recursion limits, followed by another CFG/scalar fixed
   point;
9. tail-position discovery, guaranteed tail-call formation, and legal invariant
   motion;
10. register allocation, block layout, constant pooling, and bytecode
    peepholes.

Pass families are skipped from cheap body-property flags: a body without
aggregates does no SROA, a body without indirect calls does no devirtualization,
and a body without handlers or resumptions does no control specialization. `-O2`
runs at most three local fixed-point rounds and enforces a compilation-wide
optional-optimization work budget. Exhausting that budget preserves correct MIR
and stops optional optimization rather than failing compilation.

Observable host calls, custom drop hooks, effect operations, handler boundaries,
cancellation, label transfer, and trapping primitives are optimization barriers.
No pass may reorder destruction or left-to-right evaluation. `-O0` performs only
correctness lowering and bytecode cleanup; `-O1` enables local simplification;
`-O2` is the self-host default; `-O3` raises inlining/specialization budgets.

## 4. Runtime architecture

### 4.1 Load boundary

The loader copies an encoded artifact once into an immutable owned container,
validates borrowed section slices, and verifies private decoded tables without
constructing the public mutable `Artifact`. The frozen execution image keeps
text/blob constants, descriptor names, and inline abort messages as checked
ranges into that container. It stores opcodes in packed words, variable register
lists in one shared operand array, and instruction offsets in a compact index;
the public representation is materialized only on an explicit compatibility
request. Verification retains dataflow states only at block leaders, while the
runtime layout retains only function ranges and continuation-boundary capture
plans. Capture register sets are delta-compressed verifier products. Multi-shot
plans retain exactly the proved continuation-live set; cancellation-only plans
also retain every dead value whose early destruction could run an observable
hook or violate a positive use obligation. Execution never branches on untrusted
offsets or unchecked table indices.
Unknown required features or critical sections are compatibility errors; unknown
noncritical sections are skipped.

### 4.2 Values, places, and frames

The VM is a typed register machine. Each register is `Empty` or contains one
owned value, copyable value, shared reference, or unique reference. `MOVE`
empties its source. `COPY` requires a descriptor marked structurally duplicable.

Functions, closures, handler clauses, and resumptions use one callable runtime
record: code identity plus hidden capture/continuation storage and receiver mode.
A small kind tag controls whether invocation enters ordinary code or restores a
continuation; there are no independent closure, callback, or async executors.

Heap-backed values live behind arena handles containing an index and generation.
References identify a checked handle/place projection rather than a native
pointer. The verifier establishes ordinary lifetime and alias legality; runtime
generation and bounds checks defend against corrupted state. Owned aggregates
are destroyed deterministically. Statically shareable immutable storage may use
reference counting; no tracing garbage collector is required. Cyclic owned type
layouts are rejected.

The bytecode format carries structural reference-return contracts rather than
named source lifetimes. A contract maps every reference result leaf to an exact
parameter or receiver leaf path. The verifier independently proves each
declared mapping from function bodies, including calls, callable targets,
handlers, `perform`, and `resume`; forged, duplicate, path-incompatible, or
branch-inconsistent mappings fail closed. Recursive call graphs converge over
whole multi-leaf mappings rather than guessing one compatible root. A local
borrow, inconsistent path, ambiguous producer set, or overlapping unique-origin
split invalidates the contract.

A frame contains its verified function, registers, instruction ordinal, active
labels, and handler/cleanup state. Tail call replaces the frame after required
outgoing cleanup. Register cleanup maps specify live lexical owners at each
suspension or abandonment point.

### 4.3 Labels and cleanup

A label brand has no runtime representation. Bytecode label slots refer to
lexically verified entries containing a destination instruction, result
register, and cleanup boundary. `LEAVE` resolves an active slot, destroys the
intervening state using the same cleanup mechanism as ordinary exit, writes the
result, and jumps. Static checking rejects the `LEAVE` if that intervening state
contains an untransferred must-move obligation. It cannot convert a static brand
into an address.

Destruction performs the custom hook, active fields in reverse declaration
order, then storage release, and is legal only for a subtree whose static
principal interval permits zero use. The compiler requires every owner to be
transferred, exhaustively deconstructed, or legally zero-use destroyed on every
normally completing path; the verifier enforces the resulting move and cleanup
maps without reconstructing principal intervals. Empty registers let one cleanup
map safely describe conditionally initialized values without running hooks twice.

### 4.4 Effects and continuations

`HANDLE` installs a delimiter and invokes a body callable. `PERFORM` evaluates
payloads before the instruction, selects the nearest matching normalized
protocol/operation entry, and invokes its clause. A source callable may let the
operation escape dynamically only when that exact protocol instance is present
in its declared outward row; each intervening caller must handle it or declare
the same capability. The artifact entry callable has an empty outward row. An
embedder that invokes an outward-effectful callable without installing a handler
observes the normative `UnhandledEffect` fault.

For a resumptive operation the VM detaches frames from the performance point to
the delimiter into a resumption value. Resuming a one-shot value moves those
frames back; cancelling destroys them only after static zero-use cleanup proof.
Multi-shot resumption clones only through
verified copy glue and may not contain a unique reference or nonduplicable
dependency. Deep resume reinstalls the originating delimiter.

The proof is move-path-sensitive for partially moved aggregates. Capture and
cleanup retain the aggregate shell plus only its initialized field slots;
moved-out slots remain empty. Cancellation tests zero-use permission and
multi-shot capture tests snapshot safety over that residual field set rather
than conservatively rechecking fields transferred before suspension.
Multiple disjoint fields may be transferred from one tuple or visible struct.
Nested transfers create a chain of residual aggregate owners, each with its own
canonical bitmap; continuation capture and cleanup preserve every live shell in
that chain.

The residual shell itself must not have custom `Drop`: a hook is entitled to a
fully initialized owner and cannot be replayed over a shell whose fields were
already transferred. The compiler, bytecode verifier, and VM preserve active
variants and empty slots of enum residuals, exact statically indexed
machine-array slots, and the nested tuple/struct shells that contain them.
Dynamic or path-dependent array indices still require a slot-initialization
summary and therefore remain conservative; the compiler never claims an exact
transport fact for those cases.

For a terminal operation no resumption is created. The abandoned continuation is
destroyed before clause code starts only when every captured subtree permits
zero use; otherwise compilation rejects the terminal transfer. Uncovered operations pass to the next outer
handler. Pattern order is compiled into clause decision code, not implemented by
the VM.

Calls, labels, handlers, resumptions, and cancellation share one frame-stack
unwind/transfer routine parameterized by destination delimiter and whether the
detached frames are destroyed, resumed once, or copied. Tail calls are its
zero-capture frame-replacement case. This is the VM's single dynamic control
machine.

### 4.5 Host boundary and supervision

Bytecode cannot access OS facilities directly. Each import names a capability,
symbol, and exact bytecode signature. The loader resolves all imports and checks
grants before executing the entry function. Host values are copied/translated at
the boundary; bytecode never receives a Rust pointer.

`grvm run --time-limit 120s --memory-limit 4096MiB` is a supervisor. It launches
a hidden worker, applies OS memory limits, watches wall time, and terminates the
worker on violation. A close-on-exec status pipe lets the worker distinguish a
reported allocation-limit failure from an otherwise identical internal signal;
the allocation hook resolves that inherited pipe without allocating even before
`main`, so startup allocation failures do not lose their classification. The
two cases have separate diagnostics and exit classifications. The VM loop
does not charge instruction fuel. Safe Rust is
used throughout execution; narrowly isolated process-limit setup is the only
permitted unsafe Rust. The generation-1 supervisor distribution is explicitly
Linux-only: it relies on Unix process groups, `SIGKILL`, and Linux address-space
limits. The bytecode format and in-process VM remain portable; non-Linux worker
supervision requires a future platform adapter and is not claimed here.

## 5. Bootstrap and compatibility

The compiler and bootstrap-standard-library implementation initially stay inside
a conservative subset accepted by the existing interpreter: nominal data,
functions, lexical locals, integer/text/bytes/list values, ordinary calls, and
existing file/console effects. They avoid relying on features being introduced
by that same compiler generation. Manifest-bound leaf operations may be provided
by equivalent interpreter intrinsics during this recovery-only stage.

Bootstrap is reproducible:

1. the existing interpreter runs the canonical
   `std-lib.glorious + compiler.glorious` bundle and emits `stage1.grbc`;
2. `grvm` runs stage 1 on those exact bundled bytes to emit stage 2;
3. `grvm` runs stage 2 on those exact bundled bytes to emit stage 3;
4. stage 2 and stage 3 must be byte-identical;
5. stage 2 becomes the checked-in seed and routine development uses it;
6. interpreter bootstrap remains a recovery test and, for compiler-accepted
   programs in the documented compatibility intersection, a differential test.

Bytecode changes are additive. A new VM lands first and must run every previously
released valid artifact. The previous compiler then builds a bridge compiler that
can optionally emit the new feature. Compiler source uses no new feature until
that bridge exists. Existing IDs and semantics are never changed or reused; old
encodings remain implemented. An older VM may reject a newer artifact cleanly.

### 5.1 Compact implementation profile

The bootstrap compiler is deliberately table driven and body local:

- one crate transaction, flat tagged records, and append-only arrays rather than a
  hierarchy of visitors, query objects, or per-node heap allocations;
- open-addressed hash tables for lookup, followed by sorting only at diagnostic
  and bytecode boundaries;
- flat side arrays and `(start,count)` ranges for variable-length children;
- reusable scratch arenas for parsing, inference, solver canonicalization, CFG
  worklists, and optimization;
- undo-log checkpoints for candidate and branch checking instead of cloning the
  checking state;
- one shared place-flow engine feeding loans, `Use`, environments, captures, and
  cleanup instead of five independently constructed ledgers;
- bitsets for liveness, regions, captures, initialization, and work queues;
- a default diagnostic cap of 100 errors, after which independent checking stops;
- phase telemetry reporting time, peak arena sizes, solver steps, MIR operations,
  and emitted bytes when `--stats` is enabled.

The compiler must not retain tokens, body AST, Typed Core, MIR, and emitted
bytecode for the same monomorphic body simultaneously. At each phase boundary it
keeps only the next representation plus compact source provenance. Abstract
interface serialization is produced only by conformance/debug modes in G1; the
module loader consumes compact in-session interface tables rather than a
serialized intermediate format.

## 6. Delivery and acceptance gates

1. **Contract:** freeze generation-1 bytecode IDs/layouts and golden hand-written
   artifacts.
2. **Runtime:** decoder, canonical encoder, verifier, VM, supervisor, labels,
   ownership/drop, handlers, resumptions, imports, and hostile-artifact tests.
3. **Bootstrap compiler:** frontend, minimal static core, minimal MIR/emitter, and
   successful bytecode-hosted stage 2/stage 3 convergence.
4. **Full static core:** traits, const quantities, GAT/HRTB/lifetimes, NLL,
   variance, `Use`, `Drop`, environments, and diagnostics.
5. **Full dynamic core:** refinements, decision DAGs, labels, handlers,
   resumptions/cancellation, and source-defined standard-library control.
6. **Optimization:** complete pass pipeline and supervised self-compilation below
   120 seconds and 4096 MiB.

Each gate adds golden decode/encode cases, verifier rejection cases, VM semantic
tests, compiler compile-fail cases, and MIR differential tests. The newest VM is
continuously tested against every released compiler seed. Fuzzing requires that
arbitrary input cannot panic the host or violate memory safety.

## 7. Command-line contracts

```text
grvm verify program.grbc
grvm run [--time-limit 120s] [--memory-limit 4096MiB]
         [--allow CAPABILITY]... program.grbc -- [ARGS]...
grc [-O0|-O1|-O2|-O3] [--emit mir|bytecode] SOURCE [SOURCE...] -o OUTPUT
```

`grc` is the compiler bytecode invoked through `grvm`; a native `grc` executable,
if supplied, is only a launcher and contains no compiler logic. The launcher or
compiler driver prepends its distribution's `std-lib.glorious`; the first
explicit source is the crate root. Its declared external modules are discovered
recursively under the hybrid layout in `std-lib.md`. Explicit additional inputs
remain a hermetic embedding API and must correspond to declared modules whenever
the crate uses module syntax.
