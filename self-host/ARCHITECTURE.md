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

The source tree has four top-level implementation roles:

```text
main.glorious
    |
    v
diagnostics/             structured compiler boundary and host rendering
    |
    +---- compiler/         orchestration and session ownership
             |\
             | +-- frontend/    source-facing phase libraries
             |
             +---- backend/     lowering and artifact phase libraries
```

`frontend` and `backend` do not own the executable application. They expose
phase operations. The top-level `compiler` module decides phase order and owns
cross-phase state. The `diagnostics` module converts phase errors into the stable
cross-phase diagnostic contract and owns host rendering. The package entry point
calls that diagnostic boundary.

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

`MirProgram` is the ownership/control MIR for the currently implemented
language subset. Effects, cancellation, resumption, loans, and captures must
extend it directly; a parallel Stage program must not be introduced.

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

The architecture stages introduce a small compiler toolkit rather than
feature-specific utility layers:

- `IdRange<Tag>` for typed contiguous arena ranges;
- one source span and token span model;
- one token cursor backed by a precomputed delimiter-pair table;
- one lexical `ScopeMap` with journaled scope restoration;
- one structured diagnostic model with typed primary, related, and owner sites;
- one canonical pool abstraction with freeze-and-remap at serialization;
- one body-local Core builder;
- one checked MIR editor and analysis invalidation mask;
- small worklist and fixed-point runners.

The cross-phase diagnostic model is implemented. The remaining items continue to
require at least two real compiler uses before becoming shared abstractions.

`IdRange<Tag>` now owns contiguous arena-range storage across headers, transient
body syntax, resolution, interfaces, and Typed Core. Header and body token
ranges use the shared `TokenSpan`, and the shared `SourceSpan` is an alias of the
lexer-owned source span rather than a second structure. Header and body parsers
also store their bounds and current position in the shared `TokenCursor`. This
migration exposed an existing MIR refinement-join defect: locals removed from
one predecessor were removed from the join parameters without being marked
unavailable in the joined state. That bootstrap prerequisite is fixed and
covered by a focused regression plus the O0 integrated Typed Core check.
VM/native phase snapshots remain identical after the substrate migration.

## Diagnostics and failure

Compiler phases return their own structured semantic errors. The diagnostic
boundary normalizes those errors and the host application renders them.

The implemented cross-phase model contains:

```text
CompilerDiagnostic
    stable phase-local code
    diagnostic class
    typed primary site
    optional typed related site
    optional owning declaration
    expected/found words
    deterministic message
```

Location spaces distinguish source bytes, tokens, declarations, interfaces,
expressions, resolution occurrences, types, locals, Core identities, backend
identities, and artifact failures. Internal invariant failures remain distinct
from source diagnostics. Resource limits are structured diagnostics rather than
silent fallback or unbounded recursion.

Phase-local error enums remain authoritative inside their phases. Exhaustive
adapters convert every current phase variant into `CompilerDiagnostic`; adding a
variant therefore requires updating the diagnostic contract. Production phases
no longer publish separate numeric code, primary-token, and related-token
projections. Historical numeric encodings live only in test probes, while the
production boundary constructs typed diagnostic shapes directly. The
command-line entry point and VM/LLVM self-host parity fixture both run through
this boundary. See `DIAGNOSTICS.md` for stable codes, identity spaces, and
extension rules.

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

Run `self-host/count-lines.sh` to report both physical lines and normalized
nonblank, non-comment lines. The report separates production compiler modules
from compatibility probes so test protocol code cannot obscure production-size
trends. At this architecture checkpoint the production tree contains 22,909
physical and 21,377 normalized lines; probes contain 3,127 physical and 2,999
normalized lines. These numbers are a reproducible baseline, not a claim that
the longer-term size target has been reached.

### Stage 1: phase ownership and session boundaries

Implemented by the initial architecture change:

- move executable orchestration out of `backend`;
- make `frontend` and `backend` top-level phase libraries;
- introduce one `CompilerSession` for cross-body state;
- introduce one `BodyCompilation` for transient body syntax and resolution;
- use `MirBuilder` as the body-local lowering context and `EmissionContext` as
  the artifact-local owner of canonical pools, operand/span scratch, and the
  schema-driven writer;
- make the existing one-body-at-a-time scope an explicit ownership contract;
- report the failing compiler phase at the host boundary;
- preserve existing frontend, Typed Core, lowering, emission, and artifact
  semantics.

### Stage 2: shared substrate and direct semantic views

Implemented diagnostic slice:

- centralize stable cross-phase diagnostics and resource-limit reporting;
- distinguish user errors, resource limits, emission failures, and internal
  invariant failures;
- attach typed primary, related, and owner identity spaces;
- route the package host boundary through deterministic structured rendering;
- validate the model through real frontend failures, synthetic backend failures,
  and the VM/LLVM self-host parity path.

Stage 2 shared-range work completed:

- refinement joins now preserve unavailability for locals removed while
  intersecting predecessor state;
- the O0 integrated Typed Core self-host check covers this join path without an
  internal invariant failure;
- header, body, resolution, interface, and Core arena ranges share
  `IdRange<Tag>`;
- range-producing parsers and builders take one shared `range_mark` before
  appending and construct the typed range from the completed end mark; manual
  count subtraction and per-range integer conversion are removed. Thin typed
  constructors remain because the bootstrap compiler cannot carry a result-only
  generic range tag across callback resumptions;
- scanner, header, and body token bounds share `TokenSpan`, while source bounds
  have one lexer-owned nominal representation;
- header and body parsers use the shared `TokenCursor`; delimiter pairing is
  built once and consumed by scanning;
- lexer, scanner, headers, bodies, and integrated Typed Core retain VM/native
  differential parity.

Stage 2 probe extraction completed:

- all lexer, scanner, header, body, resolution, and elaboration snapshot
  encoders and host applications live under the
  root-level `probe` tree, which the production compiler does not declare;
- those production modules no longer request process, filesystem,
  host-diagnostic, or binary-writer capabilities; packed header type storage
  remains private behind `HeaderTypeView` and typed declaration accessors;
  transient body expressions expose one exhaustive `BodyExpressionView` over
  their direct semantic representation;
- callable-header and nominal-interface probes retain byte-for-byte Rust-oracle
  parity in VM and native execution, as do lexer, scanner, body, resolution,
  and Typed Core probes;
- the Typed Core probe traverses finalized Core exclusively through
  `CoreValueView` and `CoreComputationView`; serializer-only local-use walks no
  longer depend on Core arena storage.

Stage 2 diagnostic-projection cleanup completed:

- lexer and scanner legacy numeric wire codes are owned by their test probes;
- body, header, resolution, and elaboration phases no longer expose parallel
  code/primary/related accessor families;
- production phase failures are converted through structured diagnostic shapes
  with typed site spaces;
- stable diagnostic codes and probe snapshots remain unchanged.

Stage 2 typed declaration-order slice completed:

- `NominalIndex` stores source declaration order in one exhaustive
  `HeaderOrder` enum stream with category-specific typed header IDs rather than
  synchronized numeric-kind and raw-index vectors;
- the production header parser dispatches directly on scanner
  `DeclarationKind`; numeric header and shell codes remain compatibility
  projections for probes and legacy consumers only;
- type-name lookup returns an exhaustive alias/struct/enum target instead of a
  numeric kind plus raw index, and all three cases share one resolution path;
- parsed headers retain declaration identity in one `ParsedDefTable`: every
  entry carries its stable scanner `ShellId` and one
  exhaustive `HeaderOrder` payload whose category index is itself a typed ID;
- the scanner-owned declaration table now builds one
  `(module, name, Namespace)` index, and function resolution consumes its
  ambiguity-preserving `DefSearch` instead of rebuilding a function-only map;
- elaboration resolves type names through that same namespace index and the
  shell-keyed `ParsedDefTable`, replacing three category-by-category linear
  searches and returning typed alias/struct/enum header IDs;
- struct and enum expression resolution now consumes the scanner-owned type
  namespace rather than scanning category arenas, and resolved struct and
  variant targets retain typed header IDs through the elaboration boundary;
- `ParsedDefTable` owns an enum-member index keyed by typed `EnumHeaderId` and
  interned member name, replacing the recursive linear variant search while
  preserving the enum namespace as the member's owner;
- the lexer interns maximal operator runs as canonical names, and parsed
  headers index fixities by lexical owner, interned operator name, and
  prefix/infix class; body parsing performs direct scoped lookup with root
  fallback and retains conflict detection without scanning all fixity headers.

Stage 2 resolution-map simplification completed:

- `ResolvedBody` owns one expression-indexed
  `IndexVec<ExprTag, Option<ResolvedTarget>>` for O(1) semantic lookup;
- a compact expression-ID order journal preserves diagnostic and probe
  occurrence order without duplicating targets;
- elaboration consumes `ResolvedTarget`, resolved handler arms, and resolved
  binder slices directly; `ElaborationTarget`, its copied target vector, and
  the copied handler-resolution map are removed;
- body-local names resolve through one `ScopeMap` with hash-based lookup and a
  reversible shadowing journal; block and handler-arm scope exit share the
  same restoration operation instead of truncating a linearly searched binding
  vector.

Stage 2 semantic-dispatch work completed:

- production resolution and elaboration dispatch exhaustively through
  `BodyExpressionView`;
- transient body nodes store one direct `ExprKind` enum with variant-specific
  child, operator, name, edge-range, and handler-arm payloads; the former
  numeric kind code and universal name/child/operator/metadata slots are
  removed;
- variadic body edges store one typed `ExprEdgeKind`, while distinct typed
  ranges identify expression names, variadic edges, pattern binders, and
  handler arms; scalar probe accessors are derived compatibility views rather
  than parallel storage;
- header type nodes store one direct `HeaderTypeKind` enum with only their
  variant-specific path, referent, lifetime, tuple, or application payloads;
  generic parameters likewise store `GenericParamKind`; their numeric probe
  codes are derived compatibility projections rather than semantic storage;
- lexer tokens store only `TokenKind` and source span; numeric token and
  keyword codes are exhaustive compatibility projections for probes, and
  number-base codes are likewise derived from `NumberBase` rather than stored
  beside it;
- parser punctuation and category predicates use the nominal `TokenPattern`
  enum through the shared cursor; headers and bodies no longer dispatch on
  numeric token codes, while probe encoders retain derived wire-code accessors;
- resolution consumes typed child IDs, construction names, and handler-arm
  slices directly rather than rediscovering them through generic edge slots;
- MIR type dispatch uses `MirTypeKind` instead of numeric tags, and
  emission consumes variant-specific semantic accessors; unsupported internal
  tag values are no longer representable;
- MirType payloads remain in the proven single arena for bootstrap safety.
  Splitting borrowed payloads across variant arenas currently exposes an O2
  borrowed-return cleanup-metadata defect and belongs with the MIR/PlaceFlow
  migration rather than the storage-only change;
- scanner parity now covers a leading unmatched closing delimiter, including
  its logical EOF-related token, and the integrated diagnostic matrix uses the
  same stable scanner code as the Rust oracle.

Stage 2 Core-builder work completed:

- `BodyContext` owns source-local checking state while its nested `CoreBuilder`
  exclusively owns Core locals, values, computations, operand packs,
  construction fields, match tables, and integer constants;
- `CorePrefix` owns pending ANF bindings, with shared bind and finish operations
  producing values or wrapping computations in source evaluation order;
- call, tuple, struct, and enum elaboration no longer thread unused let-wrapper
  vectors; only blocks, projections, and matches create Core prefixes;
- final `TypedBody` construction consumes `CoreBuilder` explicitly, making the
  body-local Core scratch boundary visible in the type structure.

Stage 2 lookup consolidation is complete. Future declaration categories must
extend `Namespace` and `ParsedDefTable` rather than introduce category-local
search loops.

### Stage 3: ownership/control MIR and PlaceFlow

Initial PlaceFlow slice completed:

- `BodyContext` owns one ordered stream of source expression and typed
  local-place uses;
- every ordinary local use is a transfer candidate except callable receivers,
  whose ownership remains governed by callable mode;
- repeated uses, constructions, projections, and control flow no longer create
  syntax-specific eligibility exceptions: lowering decides from CFG facts.

PlaceFlow lowering boundary completed:

- Typed Core local nodes now contain only a typed local identity; the former
  `CoreLocalAccess` copy/move payload has been removed;
- PlaceFlow exports transfer candidates through a Core-value-indexed side table;
  the test-only Typed Core probe normalizes projection and repeated-construction
  uses to preserve its historical copy/move snapshot without restoring those
  syntax rules to production Core;
- source PlaceFlow records ordinary transfer eligibility and no longer computes
  or stores a final expression for each local;
- lowering is the sole phase that selects a final eligible use, emits `Move`,
  and retires its local place; all other uses emit `Copy`.

CFG-aware final-use slice completed:

- lowering performs one reverse liveness walk over the Core control tree rather
  than counting arena-allocated local nodes and consuming those counts in
  lowering order;
- `Let` analyzes the continuation before its initializer and removes the bound
  local at its definition boundary, so liveness follows execution and lexical
  scope rather than allocation order;
- `VariantDispatch` analyzes each arm from the same live-out state and unions
  arm live-in facts before analyzing the subject;
- every match records its sparse live-out mask; branch-local final transfers
  are enabled, and each arm drops only dead-on-exit locals that it did not
  consume so cleanup and local state converge by construction;
- the resulting Core-value-indexed final-transfer table is the only input used
  by instruction selection to choose `Move` versus `Copy`.

Typed Core names this sum eliminator `VariantDispatch`; source-library spellings
such as `match` do not select or leak into a persistent Core node kind.

Cleanup and move selection consume one transfer-fact object. When loans,
captures, cancellation, and resumptions enter the self-hosted language subset,
they must extend these CFG facts rather than introduce syntax-local ownership
analyses.

MIR representation boundary completed:

- the ownership-aware backend representation is explicitly `MirProgram`, with
  `MirFunction`, `MirInstruction`, `MirCleanup`, typed blocks, switch packs,
  types, and cached type facts;
- lowering, compiler orchestration, diagnostics, and emission use MIR naming
  directly; the temporary Stage-A vocabulary and API surface are removed;
- future control and ownership features must extend `MirProgram`; no parallel
  Stage representation is permitted.

Checked MIR construction slice completed:

- each body lowers into a private `MirBuilder`; no `MirFunction` is published
  until validation succeeds, so failed construction discards the entire body
  transaction;
- validation exhaustively checks register operands, optional results, register
  packs, switch packs and targets, bound block offsets, callable identities,
  one cleanup entry per instruction, cleanup ranges, and cleanup registers;
- invariant failures remain typed `LoweringError` variants with structured MIR
  diagnostic spaces rather than becoming source errors or unchecked traps.

### Stage 4: deterministic backend substrate

Canonical-pool slice completed:

- strings, signatures, and constants share one hash-indexed `CanonicalPool`
  representation and ID lookup path;
- pool freezing follows the artifact schema: strings and constant wire keys are
  sorted and deduplicated, while signatures preserve their canonical
  first-occurrence order;
- instruction and switch constant references are remapped through the frozen
  pool instead of recursively scanning the lowering arena;
- signature records and function signature IDs are emitted from the same
  frozen pool, eliminating the parallel signature-key search;
- the O2 self-hosted compiler artifact verifies, and its emitted fixture passes
  exact canonical decode/re-encode plus VM/native behavior parity.

Opcode-schema slice completed:

- every supported MIR instruction header is produced from one exhaustive
  `OpcodeSpec` containing its wire opcode and operand-word count;
- instruction emission no longer embeds precombined opcode/width words, and
  optional artifact references share one named absent-ID encoding;
- the canonical self-host artifact passes independent encode/load verification
  after the migration.

Artifact-section schema slice completed:

- each GRBC section has one exhaustive `SectionSpec` containing its wire
  ordinal, variable/fixed encoding, fixed width, and initial payload policy;
- `ArtifactWriter` stores typed section slots, so initialization, fixed-width
  validation, directory emission, and section replacement consume the same
  schema instead of relying on parallel numeric-index conventions;
- header sizing and section counts are derived from the schema-backed slot
  collection, and the artifact module owns the shared absent-ID encoding.

Type-fact slice completed:

- freezing `MirProgram` computes one side table of zero-sized and zero-use
  facts for every custom type;
- a monotone fixed-point pass handles forward and recursive type references
  deliberately instead of recursively walking type structure during writing;
- emission combines cached semantic facts with the existing copyability flag
  and no longer owns semantic type-property traversal.

Assembler pools, remap tables, and artifact records remain local to emission;
there is no persistent fourth semantic IR.

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
