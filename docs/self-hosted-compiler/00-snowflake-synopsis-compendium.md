# Self-Hosted Glorious Compiler — 32-Document Synopsis Compendium

Status: breadth-first snowflake design. This document expands every entry in the
[32-document roadmap](00-snowflake-document-roadmap.md) into a substantial
implementation synopsis before the remaining individual specifications are
written in full.

Parent design: [Snowflake Stage One: The Ideal Self-Hosted Glorious
Compiler](../self-hosted-compiler-snowflake-stage-one.md).

Existing detailed specifications:

- [01. Architecture and Trust Boundaries](01-architecture-and-trust-boundaries.md)
- [02. Compilation Inputs, Revisions, and Session Ownership](02-compilation-inputs-revisions-and-session-ownership.md)

This compendium is intentionally broader and less normative than the individual
documents. Its purpose is to expose contradictions early, establish shared
vocabulary, and make the complete compiler visible as one system. The language
core specification and bytecode specification remain authoritative where this
text discusses language or artifact semantics.

The repository currently uses **Grandiose** in existing component names and
some documents. This snowflake series uses **Glorious** as the language name.
Existing commands and suffixes remain `grand`, `grc`, `grvm`, `.glorious`, and
`.grbc`.

---

# Volume I — The Compiler’s System Spine

## 01. Architecture and Trust Boundaries

The first design defines the compiler as a set of narrow authorities rather than
one omnipotent executable. `grand` owns package and workspace discovery,
lockfiles, dependency acquisition, source-file reading, target selection,
capability policy, and output placement. The self-hosted compiler library owns
all Glorious source semantics. The deterministic emitter constructs candidate
artifacts, but the independent decoder and verifier decide whether those bytes
satisfy the G1 runtime contract. The supervisor decides which resources and host
capabilities an accepted program receives, while `grvm` executes only the
verifier’s frozen image. Editor, formatter, documentation, testing, and
inspection tools are clients of the same compiler service rather than parallel
implementations.

The architecture is built around typed immutable boundaries. Orchestration
converts the mutable outside world into a complete `CompilationRequest` holding
source bytes, logical identities, dependency interfaces, the standard-library
identity, target and optimization options, lint policy, runtime capabilities,
and explicit limits. Semantic phases never reopen paths, consult the current
directory, inspect unspecified environment variables, or access the network.
Compiler output is returned as structured diagnostics, interfaces, manifests,
inspection products, and artifact bytes. The host decides where and whether to
write those products. This contract enables reproducible builds, coherent editor
snapshots, remote execution in the future, and a bootstrap process that does not
hide host state inside semantic computation.

Trust is deliberately divided. The compiler is trusted to implement source
semantics, including name resolution, traits, effects, quantities, borrowing,
privacy, cleanup insertion, and optimization legality. The verifier is trusted
to reject malformed or unsafe bytecode according to the lower-level artifact
contract, but it does not repeat full source checking. The supervisor and host
adapters are trusted to enforce execution isolation, time and memory limits, and
exact capability grants. `grand` is trusted to assemble the requested package
world faithfully. Persistent caches and imported interface blobs are not
trusted; they are validated inputs whose failure merely causes rejection or
recomputation. The bootstrap seed and stage-zero compiler form a separate
supply-chain trust concern.

Several architectural laws follow. Every semantic fact has one authoritative
producer. A failed or cancelled phase publishes no successful result. Recovered
IDE facts are explicitly marked and cannot become release-build evidence.
Boundary products are canonical even though internal arena allocation need not
be. Runtime authority is exact rather than ambient. Compiler spelling must not
confer privilege: the VM and compiler may not recognize ordinary declarations
named `if`, `match`, `loop`, or `return` as magical. Machine primitives and host
imports are granted only by finite manifest-bound declaration identity.

The principal interfaces should be stable enough to support both a short-lived
CLI and a long-lived compiler service. `grc` becomes a thin command adapter over
compiler queries. `grand-lsp` owns protocol transport, document versioning, and
request cancellation, but not alternate parsing or type checking. The formatter
uses the same lossless source model. Documentation uses the same resolved
interfaces. Tests compare the same structured diagnostics and verified runtime
path used by normal builds. Inspection commands ask for tokens, Core, MIR,
control plans, verifier states, or source-to-PC mappings through typed service
queries.

Implementation should proceed by removing ambient authority before adding
sophisticated incrementality. Phase-local filesystem, process-argument, and
host-diagnostic effects move to outer adapters. Source and dependency bytes
become explicit request fields. The compiler returns outputs rather than writing
them. The emitter and verifier receive separate types so an emitted artifact
cannot be mistaken for a verified one. The VM constructor accepts only a private
`FrozenExecutionImage`. These type boundaries should make forbidden authority
difficult to express, not merely discouraged by comments.

The completed architecture is successful when equivalent `grand`, direct `grc`,
and LSP requests reach the same semantic engine; semantic phases have no ambient
host capabilities; dependency and cache records are defensively decoded; warm
and cold builds are byte-identical; the VM cannot execute raw artifacts; and the
stage-two/stage-three compiler comparison uses one canonical manifest. Later
documents refine these interfaces, but none may silently move authority across a
boundary.

## 02. Compilation Inputs, Revisions, and Session Ownership

The second design defines what a compiler invocation means in a long-lived,
queryable system. The host first assembles a raw request, then the compiler
normalizes, validates, canonically orders, and fingerprints that request into an
immutable `NormalizedInputWorld`. Every semantic request pins exactly one
revision of that world. A source edit, dependency-interface replacement,
standard-library change, target change, or semantic option change creates a new
world or a new projected request identity; no in-flight query observes a mixture
of old and new facts.

Input accounting is comprehensive. Source inputs contain database-owned bytes,
content digests, stable file keys, logical package paths, encoding status, and
provenance. Logical paths are labels used for module resolution, diagnostics,
and privacy; they are not permission to reopen host files. Package input records
workspace topology, roots, dependency names, selected features, and package
kinds. Dependency inputs carry canonical interface bytes and exact package
identities. The distinguished standard-library input also carries the trusted
primitive and host-import manifest. Target, code generation, lint, diagnostic,
capability, and resource-limit policies are typed records rather than hidden
flags.

Not every input affects every query. The normalized world exposes projected
fingerprints: a source-semantic fingerprint, an interface fingerprint, a target
layout fingerprint, an optimization fingerprint, an artifact fingerprint, a
runtime-capability fingerprint, and a presentation fingerprint. This prevents a
terminal-color option from invalidating MIR while still ensuring that anything
which can change legality or bytes enters the appropriate key. Projection rules
must be explicit and tested; omitting a real dependency is a correctness defect,
while including irrelevant fields is an incremental-performance defect.

`CompilerDatabase` owns immutable source blobs, validated interface records,
interners, query memoization, revision records, and eviction metadata. A
`RevisionRecord` names one complete input world and may reference a parent plus a
verified change summary. A `DatabaseSnapshot` pins that record. `RequestSession`
adds cancellation, hierarchical budgets, diagnostic staging, demanded roots,
and publication guards. `PackageSession`, `BodySession`, `LoweringContext`, and
`EmissionSession` own progressively shorter-lived mutable state. The design has
no ambient global “current compilation.”

Body ownership is especially important for self-hosting. A `BodySession` owns
transient syntax, local resolution, inference variables, temporary semantic
terms, a Typed Core builder, and lowering scratch. Once a complete body product
has been validated and published, that scratch is released. Compact interfaces,
canonical types, summaries, and cacheable body products may outlive the session,
but a mutable whole-program body AST is not mandatory. Generic bodies may retain
a compact representation only when downstream specialization truly needs it,
and that exception must not evolve into a duplicate persistent HIR.

Editor overlays use the same model. An unsaved document is a new immutable
source blob in a new revision, not a mutation of a shared syntax tree. Atomic
multi-file edits create one revision containing all changed files. Old requests
may finish against their pinned snapshot or be cancelled; they cannot publish
into a newer revision. Several recent revisions may remain live for editor
latency, then retire when no snapshot, query, or diagnostic publication holds a
pin. Stale generation-tagged keys fail closed.

Publication is transactional. Query values, interfaces, manifests, diagnostics,
and artifacts become visible only after validation and cancellation checks.
Failure unwinds body arenas, child budgets, temporary pools, and publication
guards. Completed immutable subqueries may remain memoized when their contracts
are independent of the cancelled parent, but incomplete results never masquerade
as complete. Memory accounting attributes every retained allocation to a
lifetime and retention class so self-compilation leaks can be diagnosed.

The implemented design is accepted when every entry point constructs an
explicit immutable request; multiple revisions can coexist without ID confusion;
source paths are never reopened by semantic phases; transient body state is
reclaimed; editor overlays are coherent; cancelled work cannot publish stale
results; retired revisions are collectable; and bootstrap manifests capture the
entire normalized world. These ownership rules are the substrate on which the
query engine and caches are allowed to optimize.

## 03. The Typed Query Engine

The third design turns the compiler into a typed semantic database. A query is
not an arbitrary string dispatched through reflection. Each query family has a
statically known key, value, durability, cycle policy, persistence policy,
validation function, and presentation name. Examples include
`Tokens(FileKey)`, `ItemHeader(DefKey)`, `TypedCore(BodyKey)`,
`TraitGoal(CanonicalGoal)`, `Mir(BodyKey)`,
`OptimizedMir(InstanceKey, OptimizationLevel)`, and
`VerifiedArtifact(BuildKey)`. Glorious code implements these as ordinary typed
functions over a small shared engine.

The engine records dependencies automatically whenever one query demands
another or reads an input leaf. Query authors should state what they need, not
manually maintain invalidation lists. A query frame records its revision,
canonical key, parent, direct dependencies, diagnostics, cancellation state,
budget use, and staged result. Successful publication atomically installs the
value, fingerprint, dependency set, and explanation metadata. Failure or
cancellation publishes no completed value. Reentrant requests for an executing
key enter the query’s declared cycle policy rather than deadlocking or recursing
without bound.

Results need more structure than `Result<T, Error>`. A semantic query can be
complete, rejected with diagnostics, recovered for IDE use, cancelled,
resource-limited, corrupt-input blocked, or failed by an internal invariant.
`Analysis<T>` should distinguish these states and carry deterministic
structured diagnostics, source mappings, provenance, dependency fingerprints,
and optional explanation records. Release-build roots accept only complete
products. Editor queries may consume recovered products when the downstream
query explicitly supports recovery. Recovery status propagates and is never
silently erased.

Incremental validation should use a red-green model or an equivalently precise
algorithm. On a new revision, a memoized query is green when its key remains
valid and every relevant dependency produces the same semantic fingerprint. If
a direct input changed, the query recomputes. If a dependency reruns but emits
an identical value fingerprint, downstream queries may remain green. The engine
must separate value equality from diagnostic or presentation equality where
appropriate: a semantic value might remain stable while a source span changes,
requiring tooling invalidation but not code generation.

Cycles are query-family specific. File lexing must be acyclic. Mutually
recursive declaration interfaces may be solved as an SCC. Trait goals may use
tabling, coinductive assumptions, or explicit overflow. Recursive type facts may
run a bounded fixed point. Call summaries may widen over SCCs. Query metadata
therefore declares `Acyclic`, `Scc`, `FixedPoint`, or a specialized solver
policy. Cycle reports include the typed key chain and owning declarations.
Internal accidental cycles are invariant failures, while language-permitted
cycles are handled by their semantic algorithm.

The engine should be inspectable. `why_recompiled` walks changed dependency
edges from a root to an input. `query_trace` records execution, reuse,
validation, cycle handling, cancellation, and cache decisions. `query_graph`
exports typed nodes without exposing raw arena addresses. Statistics include
hits, validated reuses, recomputations, wait time, retained bytes, and budget
consumption. These tools make unexpectedly broad rebuilds and performance
regressions first-class compiler bugs.

Generation 1 should favor deterministic single-threaded execution with a clean
future concurrency boundary. A query’s immutable inputs and atomic publication
make parallel scheduling possible later, but self-hosting should not depend on
threads. Shared mutable interners and caches need explicit database ownership;
body-local mutation remains confined to one query. Reentrancy through algebraic
effects must not obscure the query dependency graph: a narrow `Demand<Query>`
effect may be useful, but its handler should be the typed engine, not a general
dynamic service locator.

The minimal implementation starts with typed wrappers, memo tables, input leaf
queries, dependency journals, cancellation checks, and deterministic tracing.
Persistent caching is added only after in-memory correctness is proven. The
engine is complete when all compiler clients use the same query definitions,
queries can explain their reuse or recomputation, recovered values cannot enter
release roots, legal cycles converge deterministically, failed frames publish
nothing, and compiler output is independent of query request order.

## 04. Stable Identity, Interning, and Typed Arenas

The fourth design gives every long-lived fact a stable name while keeping local
compiler storage compact. The compiler needs persistent identities for packages,
modules, source files, definitions, bodies, generic instances, trusted
manifests, and query families. It also needs cheap local indices for tokens,
syntax nodes, inference variables, semantic terms, locals, places, loans, blocks,
operations, and control sites. These two categories must never be confused.
Stable keys cross revisions, processes, interfaces, or cache records; local IDs
are meaningful only inside the arena and revision that owns them.

A stable package key derives from canonical dependency identity rather than a
host path. A module key combines package identity and logical module path. A
definition key combines the owning module, namespace, declaration kind, stable
name, and a deterministic disambiguator. Named declarations should survive
unrelated insertions. Anonymous callables, handler clauses, generated labels,
and closure bodies use a stable syntax anchor based on their owner and a
structural path or content neighborhood, with explicit collision handling. The
design must avoid an ordinal scheme where inserting one closure invalidates all
later closures.

Keys are typed newtypes, not raw `u32` values. `DefKey`, `BodyKey`, `InstanceKey`,
`TypeKey`, and `FileKey` cannot be interchanged without an explicit conversion.
Database keys carry generation or database identity so stale references fail
closed after eviction or process restart. Arena IDs similarly carry phantom
tags and, where necessary, an owner generation. Public APIs expose borrowed
views keyed by typed IDs rather than parallel numeric tag/code accessors.

Interning canonicalizes immutable semantic values. Names, module paths, fully
resolved types, effect rows, const values, canonical trait goals, signatures,
and perhaps stable source strings should be interned. Terms containing inference
variables remain body-local until zonked. Interners use semantic equality that
excludes source spans and local allocation order. Each interned record may carry
a stable content fingerprint for queries and persistence. Interning is an
optimization and identity service, not a license to make every value immortal;
large or revision-specific records can use weak tables or eviction-aware
segments.

Typed arenas provide append-only, cache-friendly storage for local compiler
products. The shared substrate should include `Id<Tag>`, `IdRange<Tag>`, arena
marks, `range_since(mark)`, checked indexing, borrowed slices, and deterministic
iteration. Body parsing, resolution, Typed Core construction, and MIR lowering
may use separate arenas or typed regions within a body owner. A phase can consume
or borrow an arena-backed product, but it should not duplicate the same semantic
fact into a second representation merely to change storage shape.

Persistent serialization never writes raw local IDs as global truth. A cache or
interface encoder freezes records in canonical dependency order and remaps local
IDs to compact artifact-local indices. Decoding creates fresh typed arenas after
validating every index and graph invariant. Stable keys may be serialized when
their defining identity contract is versioned; otherwise the encoder writes the
semantic components from which a key can be reconstructed. Hashes include schema
and identity-algorithm generations.

Identity across edits is observable through tooling. Rename, references,
incremental invalidation, diagnostic anchoring, and cache reuse all depend on it.
The compiler should provide an identity-diff inspector that explains whether a
definition was preserved, moved, replaced, or ambiguously rematched between
revisions. Stable identity is not guessed from text alone when package or module
ownership changed. Conflicts produce deterministic new identities rather than
silently merging declarations.

The design succeeds when unrelated edits preserve named and anonymous identities
where semantically justified; local IDs cannot escape their owner; cache records
remain independent of arena allocation order; stale generations fail closed;
interned terms are source-span independent; and every identity algorithm has
adversarial tests for collisions, moves, duplicate declarations, module changes,
and editor recovery. This foundation lets invalidation be narrow without making
semantic correctness depend on fragile text offsets.

---

# Volume II — Incrementality and Operational Safety

## 05. Dependency Tracking and Invalidation

The fifth design specifies how a change propagates through the semantic graph.
Every completed query publishes a typed set of dependencies: direct input leaves,
other query keys, imported interface records, trusted manifest entries, target
facts, and relevant option projections. The dependency graph is discovered by
execution, not handwritten as a separate approximation. Invalidation asks
whether those exact dependencies still denote the same semantic facts in the new
revision.

Dependencies have kinds because not every consumer needs the same equality.
A body parser depends on token structure and fixities, while formatting may also
depend on trivia. Type checking depends on resolved interfaces, trait and impl
heads, effect declarations, const values, and body syntax. Code generation
depends on typed and operational facts plus target layout. Diagnostics depend on
source spans and presentation policy. The graph can therefore record semantic,
structural, source-location, artifact, and presentation edges, or represent
these as separate query values with separate fingerprints. This avoids both
under-invalidation and needless recompilation.

A new revision begins with an input change set computed from canonical worlds,
not trusted host hints. File-watcher hints may accelerate comparison, but source
hashes establish truth. Changed dependency interfaces are decoded and compared
at exported-fact granularity. A private implementation edit should not invalidate
downstream packages when the interface fingerprint is unchanged. A public trait
implementation change may invalidate canonical goals whose candidate sets can
change. A fixity change invalidates only bodies containing affected operator
names in its scope. A generic body change invalidates discovered instances and
callers that depend on their summaries.

The preferred validation algorithm is demand-driven. When a root query is
requested, the engine checks whether its old value can be reused. It recursively
validates dependencies, short-circuiting on the first changed fingerprint. A
query that recomputes to the same value becomes green and can stop propagation.
The engine stores dependency order deterministically so explanations are stable.
High-fanout nodes such as package interfaces may use reverse indexes for
scheduling and statistics, but correctness derives from forward dependencies
recorded by each result.

Trait solving, method selection, and coherence require special care. A goal may
depend not only on the chosen implementation but on the absence of a competing
implementation. Candidate-set or impl-index fingerprints must therefore be
recorded at the correct namespace and visibility scope. Negative reasoning and
coinductive goals need explicit dependency summaries. Likewise, overload
selection and contextual callable-block elaboration depend on the complete
applicable candidate set, not merely the selected callee.

Invalidation is observable. `why_recompiled` should produce a chain from a root
through changed query values to a concrete input, including old and new
fingerprints and a human description such as “exported effect row changed” or
“operator `|>` fixity changed in module prelude.” `invalidation_summary` groups
recomputed work by change source. Tests establish expected invalidation sets for
common edits. A change that unexpectedly rebuilds the world is a regression even
when the final bytes are correct.

The design also governs diagnostics and IDE behavior. A source-span-only edit
may preserve semantic Core while requiring new diagnostics and reference
locations. Recovered syntax can invalidate only editor-facing products until a
complete body becomes available. Requests pinned to old revisions keep their old
dependency graph; graph mutation for a new revision cannot change an in-flight
answer. Cancellation may leave validated old results intact but publishes no
new partial dependency set.

Implementation begins with exact dependencies at coarse query boundaries, then
splits expensive nodes only when measurement justifies it. Granularity is not a
goal by itself. The system is correct when changing any declared input cannot
leave a stale successful fact, while semantically irrelevant edits reuse
expensive results. It is useful when those decisions are explainable, stable,
and testable across source, traits, generics, effects, quantities, targets, and
capability policy.

## 06. Caching, Persistence, Eviction, and Schema Evolution

The sixth design distinguishes three reuse layers. In-memory memoization reuses
query values inside a compiler process. Persistent semantic caching stores
selected immutable query products across processes. Final artifact caching
returns an already verified package artifact when the complete build manifest
matches. Each layer has different costs and trust requirements, but none may
change compiler meaning.

The in-memory cache belongs to `CompilerDatabase`. Entries contain the typed
query key, revision-independent input identity where available, value and
presentation fingerprints, dependency records, diagnostics, provenance,
validation state, retained byte count, and eviction class. Small interfaces,
canonical terms, and summaries may be strongly retained. Large syntax trees,
Typed Core bodies, MIR, optimization analyses, and emitted fragments are
eligible for deterministic eviction. Eviction removes an optimization; it does
not alter a stable key or a published artifact.

Persistent storage is content-addressed. A record envelope names the compiler
build identity, language generation, query schema, value schema, key encoding,
complete semantic input fingerprint, compression method, payload length,
checksum, and validation policy. The payload is canonical and independent of
local arena numbering. Candidate values include validated package interfaces,
Typed Core for stable bodies, validated MIR, optimized MIR, interprocedural
summaries, emitted function fragments, native fragments if a backend exists,
and verifier products whose reuse contract is sufficiently narrow.

All persistent bytes are untrusted. Loading verifies envelope lengths, digest,
schema compatibility, feature support, key identity, and product invariants.
Core and MIR records pass structural validators; interface records pass
coherence and identity checks appropriate to imported facts; artifact fragments
are rechecked when linked. A bad record is quarantined or deleted and treated as
a miss. It is never reported as a source error. Remote caches, if added, obey the
same protocol and may add signatures for provenance, but signatures do not
replace semantic validation.

Cache keys include every input that can affect the value and exclude inputs that
cannot. The query document defines the canonical key; the cache layer does not
invent one from timestamps. Build identity should be decomposable so compatible
products can survive changes to unrelated compiler components, but the first
implementation may conservatively key on the complete compiler fingerprint.
Schema evolution is explicit: readers declare supported versions and migrations
operate on typed canonical values, not ad hoc byte reinterpretation. Unknown
critical fields fail closed.

Eviction has process and disk policies. Memory eviction uses deterministic
classes, recency counters, cost estimates, and pinning by active snapshots. Disk
eviction uses content reachability from recent manifests, size quotas, and
atomic deletion. Active writes use temporary records followed by an atomic
publish. Concurrent or interrupted writers cannot expose a truncated entry.
Cache garbage collection does not delete blobs referenced by a pinned build or
bootstrap manifest. Statistics report hit rate, validation time, recomputation
cost avoided, bytes retained, and corrupt records.

Final artifact caching keys the complete normalized build manifest, including
source and dependency interface hashes, standard library and trusted manifest,
target, optimization, relevant lints, capability declaration, compiler and
artifact generations, and linkage options. The cached result must include the
exact `.grbc` bytes, interface output, diagnostics policy if applicable, build
manifest, and verification evidence. The release path may still rerun cheap
verification unless the verifier-product cache contract proves equivalent
safety.

Correctness tests compare cold, warm-memory, warm-disk, evicted, corrupted, and
schema-migrated builds. All successful cases must produce byte-identical
interfaces, diagnostics, manifests, and artifacts. Fault injection truncates or
mutates records and interrupts publication. Performance tests ensure validation
is cheaper than recomputation. The cache design is complete when it is optional,
observable, self-validating, bounded, and unable to convert corruption into a
semantic success.

## 07. Determinism and Reproducibility

The seventh design makes reproducibility a property of every externally visible
product, not merely the final linker. For a complete normalized input world,
compiler build identity, target, and options, the system must produce identical
exported interfaces, diagnostics and ordering, optimization decisions that
affect output, build manifests, `.grbc` bytes, verification outcomes, and
bootstrap artifacts. Cache warmth, request history, memory addresses, hash-table
seeds, host enumeration order, absolute checkout path, and wall-clock time must
not influence those products.

Internal allocation is allowed to be efficient. Typed arenas can append in
source or discovery order. Hash maps can serve lookups. Work queues can use local
IDs. Determinism is imposed at observation and serialization boundaries through
stable sorting, canonical pools, freeze-and-remap operations, and deterministic
fixed-point scheduling. The design should not force all internal IDs to be
canonical, because doing so would complicate incremental construction and make
identity depend on global allocation.

Canonical ordering rules are specified for every product. Diagnostics sort by
logical source identity, primary position, stable code, owner, and deterministic
tiebreakers. Package interfaces sort modules, declarations, impls, effects,
fixities, and canonical terms by stable semantic keys. MIR printing uses block
and value traversal rules independent of pointer order. Constant, string, type,
signature, operand, cleanup, and function pools freeze by canonical encoded
value. Artifact sections have a fixed order and each section defines record
ordering. Build manifests encode maps as sorted sequences.

Algorithms that can select among equivalent answers need a policy. Trait
candidate ordering is semantic and deterministic. Ambiguity reports select
stable representative locations. Register allocation uses fixed block order,
register classes, and tie breakers. Inlining and specialization use stable cost
models and priority queues. SCC discovery and fixed-point worklists visit stable
successor order. Randomized optimization is excluded unless a fixed semantic
seed becomes an explicit input—and generation 1 should not need it.

Parallel execution, if introduced later, may change completion order but not
publication order or values. Query results are keyed and canonical; race winners
cannot choose artifact ordering. Interners must return equivalent semantic keys
regardless of insertion race, perhaps by using content keys and a deterministic
freeze. Logs and performance statistics may contain timing data, but those are
nonsemantic side products excluded from fingerprints and bootstrap comparisons.

Reproducibility also requires path and environment discipline. Source files use
logical package-relative paths. Diagnostics may optionally render host paths at
the outer client, but canonical diagnostics and artifacts contain logical
identities. Locale-independent formatting is mandatory. Integer and float
serialization is fixed-endian and versioned. The compiler never embeds build
time, process ID, temporary directory, or cache location unless a deliberately
nonreproducible metadata section is explicitly marked and excluded from release
artifacts.

The test strategy builds the same world under different source enumeration,
hash seeds, cache states, memory limits, request orders, and process histories.
It compares every canonical product. Optimizer determinism tests perturb internal
arena allocation and worklist insertion. Interface tests ensure private changes
do not affect public bytes. Stage-two and stage-three self-host builds are the
strongest integration test: their compiler artifacts must be byte-for-byte
identical under the canonical bootstrap manifest.

When nondeterminism is found, inspection tools should locate the first differing
section, record, function, MIR block, or query value. A reproducibility report
includes product fingerprints at phase boundaries so the defect is not debugged
only from a whole-file binary diff. The design is complete when determinism is
specified locally enough to be maintained and tested, while internal data
structures retain freedom to optimize.

## 08. Cancellation, Resource Limits, Corruption Handling, and Security

The eighth design ensures that the compiler remains responsive in an editor,
bounded during self-hosting, and safe against hostile source or persisted data.
Cancellation, resource limits, corruption, user diagnostics, and internal
invariant failures are separate outcomes. None may be flattened into a generic
“compilation failed,” and none may publish a partial result as complete.

Cancellation is hierarchical. A `RequestSession` owns a token; package, body,
query, optimizer, and emission work derive child tokens. Long-running loops and
allocation points check cancellation at deterministic safe points. Cancelling a
parent prevents new publication and unwinds child-owned scratch. An already
completed immutable subquery may remain cached when it was independently valid,
but a frame whose dependencies or output were not committed disappears. Editor
requests carry document versions so obsolete results cannot be delivered to a
newer buffer even if they finish after cancellation.

Resource accounting is similarly hierarchical. The request supplies ceilings
for source bytes, tokens, nesting, declarations, generic parameters, inference
terms, trait goals, solver steps, recursion, monomorphizations, Core nodes, MIR
blocks and operations, places, loans, labels, handlers, continuation captures,
optimizer work, artifact sections, output bytes, diagnostics, and retained
memory where enforceable. Child budgets reserve from parents, return unused
capacity, and produce structured `ResourceLimit` diagnostics with the relevant
owner and limit name.

Algorithms should avoid using the native call stack for untrusted depth.
Lexing, parsing, type normalization, solver recursion, dataflow, verifier graph
walks, and VM execution use explicit stacks or bounded recursion. Fixed points
have work budgets and convergence diagnostics. Monomorphization and control
specialization have cycle and expansion guards. Diagnostic recovery itself is
budgeted so malformed input cannot generate an unbounded cascade. Limits must
fail predictably rather than trigger allocator death or host stack overflow.

Corruption boundaries include dependency interfaces, cache records, compiler
snapshots loaded from disk, artifacts, source encodings, and optional remote
responses. Decoders validate lengths before allocation, use checked arithmetic,
limit nesting and counts, reject unknown required features, verify checksums,
and construct typed records only after index ranges are proven. A corrupt cache
entry becomes a miss. A corrupt dependency interface becomes an orchestration or
import failure. Corrupt `.grbc` becomes a verifier rejection. These failures do
not blame user source at an unrelated span.

Internal security follows least authority. Semantic phases receive no
filesystem or network capabilities. Temporary paths and outputs are owned by
outer adapters and written atomically. Cache keys and manifests avoid secrets or
absolute paths. Host-provided strings and diagnostic payloads are length-limited
and escaped by renderers. Runtime capabilities are not available to compile-time
queries. Compiler effects such as `Report`, `Demand`, or `Cancel` are handled by
internal typed boundaries and cannot be forged into host access.

Fault injection is part of normal testing. Tests cancel each phase before and
after publication, exhaust each budget, corrupt every persisted record family,
force allocation failures where the host supports it, and feed pathological
source graphs. They assert that pins, guards, temporary files, arenas, and cache
writes are cleaned up. Fuzzers target lexing, interface decoding, artifact
decoding, verifier state joins, and query-key decoding. Memory-profile tests run
the compiler on itself under strict limits.

The design is successful when hostile input can at worst produce a bounded,
classified failure; cancellation is prompt enough for interactive use; no stale
result crosses revisions; no corrupt cache alters a successful build; and every
resource-intensive subsystem exposes both a limit and an explanation. Safety is
then an architectural property rather than a collection of emergency checks.

---

# Volume III — Source and Frontend

## 09. Source Model, Spans, Lossless Lexing, and Delimiter Pairing

The ninth design defines one immutable source substrate shared by compilation,
formatting, diagnostics, refactoring, and editor analysis. A `SourceBlob` holds
validated bytes and a digest. A `SourceFile` associates the blob with a stable
file key, logical package path, source-entry identity, and line index. A source
bundle provides deterministic segment order for the standard library, package
files, generated inputs if allowed, and dependency source used by special tools.
Semantic phases never reopen the logical path.

Spans are compact half-open byte ranges qualified by file or bundle segment.
Token spans and source spans are distinct typed values. Line and UTF-16 editor
coordinates are derived views, not stored as semantic identity. Spans do not
participate in type or term equality. Source-entry identity may participate in
privacy and trusted-declaration checks, then is erased from runtime semantics.
Every mapping operation uses checked offsets and can report malformed encodings
without panicking.

The lexer is lossless. It emits significant tokens plus comments, whitespace,
newlines, and malformed fragments so formatting can round-trip and diagnostics
can underline exact input. Token records contain a direct semantic `TokenKind`
and source span; they do not mirror that kind through several numeric code
fields. Keyword recognition is structural and versioned. Standard-library
control names remain identifiers unless they are actual reserved structural
vocabulary from the language specification.

Lexing supports nested comments, complete numeric literal validation, strings,
characters, operator tokens, label sigils, and recovery from malformed input.
Errors are structured with stable codes and precise spans. The lexer always
advances or terminates, even on arbitrary bytes. It records enough state for
incremental relexing—such as comment or string mode at safe boundaries—but a
first implementation may relex a changed file completely and rely on file-level
queries. Incremental lexing is introduced only with equivalence tests against a
full lex.

A single delimiter pass constructs a `DelimiterMap` for parentheses, brackets,
braces, and any other structural pairs. It uses an explicit stack, records
matching open and close token IDs, and emits diagnostics for mismatches and
unclosed delimiters. Structural scanning and body parsers use this map to jump
over balanced regions in constant time rather than recursively searching for
closures. Recovery pairs may be marked synthetic or uncertain so release
parsing cannot mistake them for valid structure.

The source model supplies stable syntax anchors for definitions and anonymous
bodies. Anchors combine owning structure, token kinds, local context, and source
ranges without making raw offsets the sole identity. It also builds occurrence
and trivia indexes used by formatting and refactoring. Memory is organized in
typed arenas or immutable vectors with shared blobs, allowing multiple revisions
to reuse unchanged source bytes while owning distinct token and line products.

Queries include `source_blob`, `line_index`, `lossless_tokens`,
`significant_tokens`, `delimiter_map`, `token_at_position`, and
`source_slice`. Consumers depend on the narrow product they need. Formatting may
observe trivia changes; semantic scanning may depend only on significant token
fingerprints. Diagnostics retain logical file identity and map to host paths
only at rendering.

Acceptance tests include byte-for-byte lossless round trips, malformed UTF-8,
nested comments, every literal boundary, delimiter adversaries, random input
termination, source-map localization, editor coordinate conversion, and
incremental/full-lex equivalence. This document is complete when every later
phase and tool uses one source representation, spans are typed and safe, and no
private lexer or path reader is hidden in a client.

## 10. Packages, Modules, Structural Scanning, Interfaces, and Fixity

The tenth design extracts the complete package and declaration skeleton without
parsing all bodies. `grand` supplies package topology and source files; the
compiler validates that logical module relationships obey the language’s module
layout. A structural scanner walks significant tokens with the delimiter map,
identifies top-level items and body ranges, and records declaration shells in
source order. It never needs to build a whole-program body AST.

The module graph has stable package and module keys, parent relationships,
visibility context, source ownership, and deterministic child order. External
and inline modules resolve through logical package paths supplied in the request,
not filesystem discovery inside the scanner. Missing, duplicate, orphaned, or
cyclic module relationships produce structured diagnostics. Inline modules
advance the logical directory according to the language contract, and all
clients use the same resolution rules.

Declaration collection creates a unified `DefTable`. Each definition has a
stable key, owning module, namespace, name, visibility, span, declaration kind,
header token range, optional body token range, and typed payload. Kinds include
callables, structs, enums, variants, aliases, traits, implementations, effects,
consts, modules, imports, and fixities. Separate typed arenas may store payloads,
but ambiguity, visibility, ownership, and diagnostic identity use the common
definition substrate.

Header parsing collects semantic interfaces before body checking. It resolves
generic parameter binders, callable signatures, fields, variants, trait members,
associated items, effect operations, implementation heads, where clauses,
const expressions permitted in interfaces, and visibility. Header terms may
contain symbolic generics but no body-local inference variables. Mutually
recursive headers are processed by an SCC-aware interface phase with explicit
forward declarations and completion states.

Fixity is ordinary source data. The collector records operator declaration,
precedence, associativity, scope, visibility, and declaration identity. Body
parsing initially retains flat operator sequences; grouping occurs only after
all applicable fixities are known. Duplicate or conflicting fixities are
reported deterministically. Imported fixity changes have a narrow fingerprint so
only affected bodies regroup.

The package interface is a canonical downstream contract. It includes exported
definitions, semantic signatures, visible traits and coherent implementation
heads, effect operations, associated-item contracts, fixities, public layout
facts when part of the ABI, and generic bodies or canonical Core required for
downstream specialization. It excludes private implementation details and local
arena identities. Encoding is versioned, canonical, hashed, and defensively
decoded. The downstream compiler validates producer identities and required
features before importing facts.

Queries include `module_outline`, `declaration_shells`, `item_header`,
`module_index`, `visible_definitions`, `fixity_environment`,
`package_interface`, and `interface_fingerprint`. The interface query depends on
public facts, allowing private body changes to leave downstream builds green.
Documentation and symbol tools consume the same tables. The LSP can expose
headers even when bodies are malformed.

Testing uses declaration-only programs, malformed boundaries, nested modules,
visibility matrices, recursive types and traits, fixity conflicts, canonical
interface round trips, private-change stability, and dependency import
corruption. The design succeeds when source structure and exported meaning can
be known cheaply and deterministically, bodies remain demand-parsed, and no
package client duplicates module or visibility logic.

## 11. Body Parsing, Contextual Blocks, Operator Grouping, and Recovery

The eleventh design defines a transient, demand-driven body parser. Given a
validated body token range, delimiter map, declaration context, and fixity
environment, it produces a typed body syntax arena with exact source spans. The
arena belongs to a `BodySession` and can be released after elaboration unless an
active tooling request pins it. Parsing does not perform full type checking or
assign meaning based on standard-library names.

The grammar recognizes literals, paths, calls, projections, constructions,
borrows, moves, assignments, blocks, named and anonymous callables, closures,
labels and label transfer, effects, handlers, patterns, `is` tests, declarations
inside permitted scopes, and flat operator chains. It recognizes only the
structural keywords and sigils defined by the language core. A call to a binding
named `if` is parsed as a call. A block following a call is represented without
prematurely deciding whether it is an eager block value or a delayed callable.

Contextual block interpretation is deferred to elaboration. The parser records a
`ContextualBlock` syntax form with its token range and body. Candidate selection
and expected parameter type determine whether it becomes a fresh anonymous
callable constrained by `Fn<Args>` or an eagerly evaluated block. Ambiguity is a
type error, not a parser heuristic. The same mechanism applies to blocks used as
operator operands. Explicit closures and typed anonymous callables remain
unambiguous syntax.

Operators are initially parsed into operand/operator streams. A deterministic
grouper applies source-defined fixity after name and scope resolution identifies
the applicable operator declarations. The grouper detects missing operands,
nonassociative chains, precedence conflicts, and ambiguous imported fixities.
It creates normal call-shaped syntax or a grouped expression tree without
inventing compiler-known arithmetic nodes. Grouping dependencies are recorded
per operator occurrence for narrow invalidation.

Patterns use one structural representation shared later by handlers and `is`.
The parser validates binder uniqueness, rest placement, basic aggregate shape,
and syntax but leaves type-dependent exhaustiveness and move semantics to later
phases. Handler clauses record operation paths, payload patterns, continuation
binders, guards only if the language permits them, and result expressions. Label
binders occupy a lexical label namespace separate from ordinary names.

Recovery is explicit and bounded. The parser has synchronization sets for items,
statements, delimiters, handler clauses, and patterns. Recovered nodes carry
`RecoveryId` and expected-token facts. Parser checkpoints remember cursor and
arena marks; a cleanup-backed guard rolls back speculative allocations on
failure. Every loop advances or consumes a recovery budget. A release build
rejects recovered bodies, while IDE queries may elaborate supported recovered
forms into provisional semantic values.

The parser exposes `body_syntax`, `syntax_node_at`, `body_occurrences`, and
`formatting_shape` queries. It uses a shared `TokenCursor` with `peek`, `eat`,
`expect`, `mark`, `span_from`, and delimiter entry operations. It should not
publish phase-specific binary encoders or standalone applications inside
production modules; differential probes live in test tooling.

Tests cover arbitrary-source termination, exact spans, contextual blocks,
whitespace-sensitive ambiguities, every fixity combination, nested handlers,
labels, patterns, malformed recovery, checkpoint rollback, and parser parity
between the Rust bootstrap and self-hosted implementation. The body parser is
successful when it is structurally faithful, name-agnostic about library
control, recoverable for editors, and cheap enough to create and discard one
body at a time.

## 12. Name Resolution, Scopes, Visibility, and Reference Indexing

The twelfth design binds every source occurrence to a stable semantic identity.
Global resolution operates over the package module graph and unified definition
table. Body-local resolution operates in source evaluation order over parameters,
generic binders, local declarations, pattern binders, label binders, imports,
and nested scopes. The result should be a typed occurrence table or direct
annotations consumed by elaboration, not a loosely keyed vector later copied
into a parallel map.

Namespaces are explicit. Types, values, traits, modules, effects, variants,
operators, labels, lifetimes, consts, and generic parameters may have distinct
lookup rules. A `ScopeMap<NameId, BindingId>` uses a journal or stack per name so
entering and leaving scope is constant-time and rollback is automatic. Temporary
overrides used during pattern or refinement elaboration are guarded. Shadowing,
duplicate bindings, use-before-definition, and namespace ambiguity have stable
diagnostics.

Global paths resolve from a lexical module and package context. The resolver
handles `crate`, `self`, `super`, explicit dependency roots, imports, aliases,
glob policy if supported, variants, associated items, and visibility. Privacy is
checked against source-entry and module ownership. Private representation is not
just a diagnostic concern: successful field and pattern resolution carries the
authority later required to deconstruct an opaque owner. Resolution never grants
primitive authority from spelling alone.

Call and method resolution is staged. Basic path resolution identifies callable,
trait, implementation, and associated-item candidates. Full overload or method
selection may require expected types and trait solving, so elaboration owns the
final selection. The resolver exposes complete candidate sets and their scopes,
not merely the first match. This distinction is critical for invalidation:
adding a new applicable implementation can change a call even if the previously
selected declaration is unchanged.

Every identifier, path segment, field, operator, label, type name, and pattern
binder receives an occurrence record with source span, namespace, resolution
state, stable target, and role such as definition, read, write, move, type use,
import, or label transfer. The reference index groups occurrences by stable
identity and revision. Tooling queries—definition, references, document symbols,
workspace symbols, rename, and semantic highlighting—consume this same index.
Recovered or ambiguous occurrences are labeled and cannot authorize edits.

Rename is a semantic operation. It computes the target definition, all exact
references in the selected package graph, visibility and collision checks, and
text edits tied to a snapshot. It rejects stale document versions and ambiguous
recovered code. Module or file renames may require orchestrator cooperation but
use compiler-provided logical identity changes. A preview explains conflicts
before any client writes source.

Resolution queries depend on module indexes, imports, visibility, declaration
headers, body syntax, and local scope structure. Source-location changes may
update occurrence products without invalidating downstream typed Core when
stable targets remain identical. The resolver publishes deterministic ambiguity
sets and reference ordering. It has no filesystem access and no LSP-specific
state.

Tests cover every namespace, shadowing, imports, private fields, module paths,
ambiguous candidates, associated items, operators, labels, generic binders,
recovery, and rename safety. Differential probes compare stable target identities
rather than private arena codes. The design is complete when all tools and
semantic phases agree on one resolution product and local scope lookup no longer
requires repeated reverse scans through unrelated bindings.

---

# Volume IV — Static Semantics

## 13. Semantic Types, Normalization, and Inference

The thirteenth design defines one semantic type language used from interfaces
through MIR lowering. Types include nominal structs and enums, scalar machine
types, tuples or arrays if supported, shared and unique references with regions,
callable and closure identities, label and environment evidence, effect and
resumption types, associated projections, generic parameters, const arguments,
unit, and never. Source syntax types are elaborated into these canonical terms;
backend modules do not create parallel copies with unrelated tags.

Fully resolved terms are interned as `TypeKey`. Body-local types containing
inference variables live in an inference arena owned by `BodySession`. Variables
have kinds—type, region, const, effect row, quantity, perhaps callable output—and
carry origin information for diagnostics. Once constraints are solved, zonking
replaces variables with canonical terms and rejects unresolved ambiguity.
Interning occurs only after zonking so temporary identities cannot escape.

Inference is expected-type directed. Every expression checker receives an
optional expected type and produces a typed value plus constraints and ownership
state. Calls first resolve candidate declarations and instantiate generics, then
use parameter expectations to elaborate arguments, including contextual blocks.
Constructions use field expectations in source evaluation order. Branches infer
a common result under explicit coercion rules. The language should keep coercions
small and named: reborrowing, never-to-any, safe numeric literal selection, and
other approved relations are preferable to a large implicit conversion lattice.

Unification is kind-checked and occurs-safe. Nominal types unify by identity and
arguments; references generate equality and outlives constraints according to
variance; associated types normalize through the trait solver; effect rows and
quantities use their own canonical solvers. Error recovery can bind a variable
to an explicit `ErrorType` for IDE continuation, but release completeness tracks
that poison. Error types must not accidentally satisfy traits, `Use`, or layout
requirements without a recovery rule.

Normalization is a query family. It reduces aliases, associated projections,
const expressions, effect-row aliases if supported, and canonical type functions
under a recursion and work budget. Results record dependencies on definitions
and impl candidate sets. Recursive aliases and nonconvergent projections produce
structured cycles. Normalization never depends on source spans, enabling reuse
across bodies and revisions when semantic definitions are stable.

The type engine also computes memoized facts: representation category,
copyability evidence, principal use requirements where delegated, zero-sized
status, drop requirements, variance, sizedness, and layout prerequisites. Some
facts belong to later target-specific layout queries; source-level facts remain
target independent. Emitters consume these shared facts rather than recursively
rediscovering type properties.

Diagnostics preserve constraint provenance. A mismatch explains the expected
source, observed source, normalization steps, selected candidate, and relevant
generic substitutions. An ambiguity lists unsolved variables and the choices
that would constrain them. Tooling queries expose `type_at`, normalized type,
generic arguments, coercions, and inference state for recovered code.

Tests use principal typing examples, recursive terms, associated projections,
variance, contextual blocks, error recovery, literal boundaries, never flow,
and stable normalization fingerprints. The design is successful when one type
representation supports checking, diagnostics, queries, caching, MIR, and
emission without numeric mirrors, while body-local uncertainty remains strictly
local.

## 14. Generics, Traits, Associated Items, GATs, HRTBs, and Consts

The fourteenth design provides the canonical goal solver behind generic
programming. Declarations may quantify over types, lifetimes, consts, effect
rows, and quantities as permitted by the language. Instantiation creates fresh
inference variables or rigid placeholders depending on context. Bounds and where
clauses elaborate into typed goals. The solver returns proof evidence and
substitutions, not merely a boolean, so later phases can explain selection and
lower associated facts.

Goals include trait implementation, associated type or effect equality,
well-formedness, outlives, const equality and ordering, callable relations such
as `Fn` and `RunsIn`, `Use` evidence, label evidence, and compiler-generated
relations for unnameable closure or environment types. Canonicalization replaces
local inference variables with ordered placeholders and records universes for
higher-ranked reasoning. Canonical goals form stable query keys independent of a
body’s temporary variable numbers.

The solver is tabled. A goal table stores answers, dependencies, ambiguity,
overflow, and cycle state. Coinductive traits or auto-like relations, if any,
declare their cycle semantics explicitly. Ordinary recursive goals use SCCs or
bounded recursion. Higher-ranked bounds introduce fresh universes and perform
leak checking so placeholders cannot escape. GAT normalization instantiates
lifetime and type binders under the same universe discipline.

Coherence is checked at interface collection and package linking. Orphan rules
determine which package may implement a trait for a type. Overlap checking asks
whether two impl heads can unify under satisfiable where clauses. Generation 1
should avoid specialization unless the language specification explicitly adds
it; coherent selection should normally yield zero or one applicable impl.
Compiler-generated impls for fresh anonymous types are lexical and finite, and
do not enter global overlap as user-definable producers.

Candidate discovery and dependency tracking are inseparable. A trait goal
depends on the relevant trait definition, type constructors, visible impl index,
negative reasoning policy, associated declarations, and nested goals. Recording
only the selected impl is unsound because adding another candidate may create an
ambiguity. The solver exposes an explanation tree containing candidate rejection
reasons, chosen impl, normalized associated values, and cyclic assumptions.

Const generics use a structural canonical value language. Literal scalars,
booleans, enums, tuples, arrays, and approved arithmetic or comparison forms may
be evaluated at compile time through a finite machine-intrinsic boundary.
General source execution is not silently invoked during type checking. Const
normalization is deterministic, resource-bounded, checked for overflow according
to the operation, and suitable for hashing. Quantities are structural consts but
use specialized interval operations for efficiency and diagnostics.

Associated items are selected through trait evidence and explicit receiver or
type context. The compiler distinguishes declaration identity from normalized
value. Methods, associated functions, types, consts, and effect rows share
lookup infrastructure but have typed result categories. Interface artifacts
encode the contracts necessary for downstream selection without exposing
body-local solver tables.

Testing includes coherence matrices, orphan boundaries, overlap adversaries,
recursive and coinductive goals, GATs, HRTB leak cases, associated equality,
const normalization, candidate-set invalidation, and deterministic proof trees.
The solver is complete when it is canonical, tabled, explainable, and shared by
all language features rather than duplicated for callables, effects, and
ownership.

## 15. Effects, Effect Rows, Handlers, Resumptions, and Cancellation

The fifteenth design defines effects as ordinary nominal declarations with
statically checked rows. An effect declaration has generic parameters and
operations. Each operation has payload parameters, result type, and a
continuation-use contract—terminal, one-shot, optional, finite multi-shot, or
another supported quantity. A callable signature carries an outward effect row.
Rows are canonical sets or maps of effect instances plus an open tail variable,
with deterministic normalization and exact subset constraints.

Performing an operation requires the corresponding effect instance in the
current protocol environment. A handler introduces clauses for selected
operations, a result clause, and possibly forwarding for unmatched operations.
Deep handlers reinstall themselves around resumed continuations according to
the language semantics. The type checker verifies payload patterns, continuation
input and output, clause effects, handler result joins, captured environment, and
outward row after handled operations are removed or transformed.

A resumption is a compiler-generated callable identity tied to one operation
performance and handler environment. Its quantitative use is part of ordinary
ownership reasoning. Resuming it executes the captured continuation; replaying
it multiplies every captured use and may require copyability or an allowed
principal interval. Cancelling it abandons the continuation and triggers only
cleanup that is legal for captured owners. Exact-positive obligations cannot be
cancelled. Unique references, custom-drop values, or other restricted captures
across multi-shot resumptions are rejected unless the runtime and verifier have
an explicit sound representation.

Effect rows participate in generic inference. A higher-order function may be
polymorphic over the callback’s effects and preserve the exact row. Associated
effect rows and GAT-like effect families use the trait solver. Row unification
handles duplicates, aliases if supported, open tails, and outward mismatches.
Diagnostics show which operation introduced an effect, where handling stopped,
and how a callback’s row propagated through calls.

Handler elaboration uses the shared callable, brand, quantity, and PlaceFlow
kernels. Clauses are anonymous callables with captures. Handler identities and
continuations are fresh brands. Pattern dispatch uses the common decision DAG.
Continuation snapshots are explicit in MIR and bytecode. There is no separate
“effect ownership” checker: moves, loans, capture, replay, cancellation, and
cleanup are facts over the same places used by ordinary code.

Static restrictions should fail closed. The initial language may support
terminal, one-shot, and finite multi-shot resumptions while excluding unbounded
multiplicity, unique loans across replay, custom-drop snapshots, or cancellation
of exact-positive continuations. These are product boundaries with precise
diagnostics, not silent unsound fallbacks. The remaining-work ledger records
which restrictions await runtime representation or proof improvements.

Optimizer interaction is designed in from the start. Queries expose handler
producer sets, operation frequency, forwarding paths, resumption quantity,
capture summaries, and escape status. Source-defined control often lowers
through effects, so static handlers and one-shot continuations should specialize
to direct branches, loops, resume, cancel, and `LEAVE` edges when proven. A
`control_plan` explains residual runtime machinery.

Tests cover nested deep handlers, forwarding, polymorphic rows, generic effect
instances, references in payloads, optional and multi-shot resumptions,
cancellation cleanup, replayed captures, outward mismatches, and interpreter/VM
parity. The design is successful when effects compose with Rust-shaped ownership
without a second ad hoc control system, and every continuation action is
quantitatively and operationally explicit.

## 16. Quantitative Use and Ownership Obligations

The sixteenth design implements Glorious’s central interval algebra. A type has a
principal `Use<[lower, upper]>` relation describing permitted consumption. A
program path computes actual use for every owned place, callable environment,
label capability, and resumption. Checking succeeds when the requested interval
is contained in the principal interval and every exact-positive obligation is
fulfilled on each normally completing path.

The quantity domain uses finite lower bounds and finite or infinite upper
bounds, with checked addition, multiplication, hull, containment, widening, and
normalization. Sequential execution adds intervals. Mutually exclusive branches
take a hull. Nested callable execution and continuation replay multiply capture
usage by invocation quantity. Loops solve a fixed point and widen when repeated
use is not statically bounded. Nontermination and immediate abort have no normal
successor, but ordinary cleanup is not a loophole for must-move values.

A positive lower bound creates an obligation. Whole transfer moves that
obligation to the destination. Destructuring an authorized representation
splits it into field obligations. Copying a duplicable value creates a new owner
with its own obligation while leaving the original live. Destroying or dropping
contributes zero use and therefore requires zero-use permission; it cannot
satisfy `[1,1]`. Private fields control who may perform final deconstruction,
turning representation visibility into consumption authority.

Final-use inference should be driven by PlaceFlow, not repeated syntax walks. A
bare use of a duplicable owner may become `Move` when reverse liveness proves it
is the final legal use along the path; otherwise it is `Copy`. Explicit `move`
forces a transfer when inference cannot or should not choose it. Partial moves,
branch joins, loops, closures, handler captures, and continuation snapshots all
update the same place state. Custom destruction has a frozen zero-use contract
and cannot dispose of exact-positive owners.

Quantitative checking needs both local constraints and summaries. Callable
interfaces describe argument consumption, invocation quantity, captures, and
post-state through `Fn` and `RunsIn` evidence. Generic quantity variables and
const intervals are solved through the trait/const engine but use specialized
operations. Recursive callables and data may require SCC summaries and widening.
The compiler should reject cycles with no finite principal derivation rather than
silently assume unrestricted use.

Diagnostics are derivations, not only endpoint mismatches. A failure report
shows the declared principal interval, computed actual interval, operations that
contributed, branch or loop combination, and the path leaving an obligation
unsatisfied. Replay errors identify the captured owner and multiplication.
Cancellation errors identify abandoned exact-positive places. Private-destruction
errors name the module or function authorized to finish consumption. Tooling can
show `quantity_at` and a compact use trace.

Optimization must preserve quantity semantics. Inlining, copy propagation,
scalar replacement, handler fusion, and register reuse operate on MIR ownership
facts and rerun validators. They may erase proof-only evidence but cannot weaken
move, cleanup, or custom-drop obligations. The bytecode verifier independently
checks the encoded ownership modes and cleanup maps even though it does not
reconstruct the source interval proof.

Tests include every interval combination, branches, bounded and unbounded loops,
recursive values, partial moves, copies, opaque resources, captures, one-shot
and multi-shot resumptions, cancellation, abort, and optimizer equivalence. The
engine is successful when one arithmetic explains ordinary ownership and control
multiplicity together, and its errors remain understandable enough for real
programming.

---

# Volume V — Semantic Core and Ownership

## 17. Regions, Lifetimes, Borrowing, and Reborrowing

The seventeenth design adds Rust-shaped region reasoning to the quantitative
system. References are typed by mutability, referent type, and region. Places
record origin paths, initialization state, and loans. The checker supports shared
borrows, unique borrows, reborrowing, nonlexical lifetimes, variance, higher-
ranked bounds, drop checking, references in aggregates, and reference-bearing
effect payloads. It rejects any reference or proof object whose dependencies
escape their valid scope.

Region inference is constraint-based. Creating a borrow introduces a loan and a
region variable with origin and use constraints. Uses require the region to
cover relevant control points. Assignments and returns add outlives relations.
Reborrowing a unique reference creates a child loan whose lifetime suspends or
restricts the parent appropriately. Variance determines how regions flow through
nominal, callable, and associated types. Solving computes minimal regions over
MIR control points or an equivalent sparse representation.

The analysis is nonlexical and place-sensitive. A borrow may end after its last
use rather than at the enclosing block. Disjoint projections can be borrowed
independently when layout and alias rules prove separation. Partial moves and
loans interact through one move-path graph. Shared and unique access conflicts
are checked at each PlaceFlow event. An `EndBorrow` in MIR may represent runtime
state or proof-only structure, and the optimizer can erase it only after proving
that verification and execution do not need it.

Suspension is the distinctive challenge. Performing an effect may capture the
current continuation, including references and active loans. The checker records
which places and regions enter a snapshot. One-shot suspension may preserve some
unique references when the continuation cannot be duplicated and the handler
discipline is sound. Multi-shot replay generally requires shared or duplicable
state and rejects unique loans unless a future representation proves safe.
Cancellation must end or clean up loans without permitting use-after-abandonment.

Higher-ranked bounds use universe placeholders. Checking `for<'a>` obligations
creates rigid regions that cannot unify with outer inference variables. Leak
checking ensures placeholders do not escape through associated types,
environments, or captured values. GATs and callable bounds invoke the same
universe machinery. Region terms are canonicalized for query keys without making
body-local control points persistent identities.

Drop checking ensures references outlive destruction and custom-drop execution.
A type’s drop implementation cannot observe fields already moved or references
whose origins ended. Cleanup edges carry region and initialization state. Labels,
environment brands, handler identities, and refinement evidence also have
lifetime dependencies and are rejected when transferred beyond their generating
scope.

Diagnostics show loan creation, conflicting access, last valid point, suspension
or return causing escape, and relevant reborrow chains. `borrow_state_at` exposes
active loans and place availability to tooling. Source mappings connect MIR
control points back to expressions. Recovered IDE checking may shorten regions or
use poison states but cannot declare release validity.

Tests cover NLL examples, nested reborrows, variance, HRTB leaks, partial moves,
drop order, aggregate references, effect payloads, suspension, cancellation,
labels, and optimizer borrow erasure. The design succeeds when borrowing is not a
separate pass over syntax but a shared PlaceFlow analysis that composes with
quantities and effects.

## 18. Callables, Captures, Brands, Environments, and Refinements

The eighteenth design unifies every executable body through one callable kernel.
Named functions, anonymous typed callables, inferred closures, contextual blocks,
handler clauses, function items, and resumptions receive fresh nominal callable
identities. Each has parameters, result, effect row, receiver or invocation mode,
quantity, captures, environment brand, source owner, and lowering entry. Common
call checking and layout code handles them rather than feature-specific paths.

`Fn<Args>` describes ordinary call shape, output, and effects. `RunsIn` describes
whether the body may execute against a particular compile-time environment and
what ownership state results. The environment contains captured places, access
modes, lifetimes, active labels, effects, refinement facts, and post-state. During
elaboration it is open: nested expressions contribute requirements. Once the
body and its surrounding call expression are complete, the compiler verifies
overlap, solves quantities and lifetimes, and seals a fresh environment brand.

Capture inference is place-based. A closure may capture an entire local or a
projection by shared borrow, unique borrow, copy, or move. The checker chooses
the least authority consistent with body uses, explicit `move`, lifetime, and
invocation quantity. Capture layout preserves deterministic declaration or
place order. Moving one field need not capture an unrelated field. Handler
clauses and resumptions use the same capture representation, enabling shared
PlaceFlow and bytecode snapshot logic.

Brands are one generative nominal substrate with explicit kinds. Label brands,
callable environments, refinement environments, handler identities,
continuation identities, and binder keys all mint fresh IDs scoped by owner and
lifetime. A typed `Label<T>` value is proof of transfer to a destination;
passing it generically preserves the destination brand. Runtime realization is
optional: fully specialized labels and environments should erase to direct
control or static layout. Brand identity never derives solely from a source
name.

Refinement environments are generated by `is` pattern tests and handler pattern
dispatch. Positive and negative branches receive branded evidence about enum
variants, fields, bindings, and place availability. Refinements cannot leak past
the value, loan, or control context that justifies them. Joins retain only facts
valid on all predecessors and mark unavailable places correctly. The same
mechanism may support compiler-generated binder identities for pattern decision
DAGs.

Call selection uses complete callable evidence. Contextual blocks become fresh
callable types only after a selected parameter requires an applicable `Fn`
relation. Indirect calls carry finite producer sets or sealed callable metadata
for verifier safety. Host-created opaque callables are excluded unless the
runtime has a trusted producer contract. Tail calls must preserve environment,
cleanup, loan, and quantity obligations.

Queries expose callable interface, capture summary, environment state,
producer set, label evidence, and refinement facts. Diagnostics explain why a
capture moved instead of borrowed, why a closure cannot be called twice, why an
environment does not satisfy `RunsIn`, or why a label escaped. The optimizer uses
these summaries for inlining, scalarization, capture shrinking, and direct label
formation.

Tests span every callable form, capture mode, nested environment, contextual
block, generic label helper, refinement join, indirect producer set, tail call,
and resumption. The kernel is successful when new executable abstractions extend
one model instead of adding another call checker, capture layout, or environment
analysis.

## 19. Typed Core

The nineteenth design freezes the smallest trusted semantic calculus between
source elaboration and operational MIR. Typed Core is body-oriented, explicit
enough to validate, and independent of standard-library control spellings. It
contains canonical values and computations for nominal construction,
projections, callable values, ordinary and tail calls, labels and transfer,
effect performance, deep handlers, resumptions, cancellation, borrowing,
explicit destruction, finite machine primitives, and manifest-bound host
imports.

Core distinguishes pure values from computations while avoiding repetitive
manual wrapping. A body-local `CoreBuilder` offers operations such as
`value(form)`, `bind(computation)`, `emit`, `scope`, and `finish`. Elaborating an
argument left-to-right can bind preceding computations into temporaries and
return a value ID. The builder owns typed arenas for values, computations,
patterns or binding packs, evidence, and source mappings. It rejects references
to unfinalized local IDs.

Static evidence may appear while Core is checked: selected trait impls,
associated values, `Use`, `Fn`, `RunsIn`, label evidence, environment brands,
region constraints, and refinement facts. Erasure is explicit and validated.
Evidence needed for MIR legality becomes PlaceFlow facts or control metadata;
proof-only values disappear. A debug or inspection product can retain evidence
without making it part of runtime representation.

Core has strong negative rules. There is no semantic node named `If`, `Match`,
`Loop`, `Break`, `Continue`, `Return`, `Yield`, `Await`, arithmetic, comparison,
or failure merely because the source library uses those names. Source-defined
control elaborates through callables, effects, handlers, patterns, and labels.
A low-level sum-dispatch form may exist if it belongs to the trusted calculus,
but it is named and specified structurally rather than confused with the
library’s `match` binding.

Every Core body is validated before lowering. Validation checks type and effect
consistency, operand ownership, source order, selected evidence identity,
environment sealing, label scope, pattern-binding shape, handler clause
coverage, resumption quantity, and absence of unresolved inference variables or
recovered poison in release mode. Invalid imported Core from a cache or
interface is rejected, never trusted because it was compiler-produced.

Core is transient by default. A body query may cache canonical Core when reuse is
valuable, and exported generic bodies may encode Core for downstream
specialization. Otherwise lowering happens immediately and body-local arenas are
released. The design must avoid retaining Core and a second HIR for the same
body. Stable source mappings use owner-qualified syntax anchors rather than raw
arena identity.

Queries and tools can request a canonical Core dump, selected evidence,
source-to-Core map, dependency set, and erasure report. Differential tests compare
Rust-bootstrap and self-hosted Core through a canonical serializer. Core
fingerprints exclude local numbering by freezing reachable nodes in deterministic
order. Optimizer work does not mutate Core; it starts from MIR.

The design succeeds when accepted source has one small, inspectable semantic
meaning before control-flow lowering; every Core form has explicit typing and
ownership rules; library-defined control remains library-defined; and cached or
exported Core is canonical, validated, and no larger than required for
specialization.

## 20. PlaceFlow

The twentieth design makes PlaceFlow the single source of truth for ownership
and place state. A place is a local, argument, capture, temporary, static owner,
or projection through fields, variants, indices where statically addressable,
and dereferences. Move paths form a tree or sparse graph over these places.
PlaceFlow records initialization, availability, moves, copies, borrows, captures,
partial destruction, continuation snapshots, cleanup obligations, and final use
across the body’s control graph.

The analysis begins during Core-to-MIR lowering. Each semantic action emits a
place event: storage live, initialize, read, copy, move, borrow shared, borrow
unique, reborrow, end loan, project, capture, resume, cancel, destroy, or storage
dead. Control edges carry outgoing place state. Joins merge predecessor states,
retaining availability only when valid on all incoming paths and preserving
conditional initialization through explicit flags or facts. Loops run a bounded
fixed point with widening for quantities and liveness.

Final-use selection is a reverse analysis over the graph. For a duplicable whole
place, the last legal use on a path may become a move; earlier uses remain
copies. The analysis respects branches, loops, calls, captures, loans, cleanup,
and protected results. It prevents the syntax-directed repeated subtree walks
that otherwise grow with every expression feature. Explicit `move` is represented
as a required transfer and diagnosed if illegal.

Loans are views over the same graph. A loan references an origin place, access
mode, region, creation event, and active range. Conflicts use alias and move-path
relationships. Captures create edges from source places to environment fields.
Continuation snapshots create edges to continuation storage with resumption
quantity and cancellation policy. Cleanup plans query the exact set of live,
initialized, legally destroyable subtrees on an abandoning edge.

PlaceFlow is not merely an optimizer analysis. The frontend’s ownership and
borrow conclusions are published as a per-body fact product, and MIR validation
checks that instructions realize those facts. Later transformations update the
graph through a checked MIR editor or invalidate and recompute affected analyses.
The bytecode emitter derives cleanup and ownership metadata from the final
validated source, while the verifier independently checks encoded consistency.

The representation should be sparse and typed: `PlaceId`, `MovePathId`,
`LoanId`, `EventId`, `ControlSiteId`, and `StateId` are distinct. Common state
uses persistent bitsets, compact interval facts, or indexed maps rather than a
full clone per instruction. Source mappings connect facts to expressions and
owners. Queries expose place state at a source point, move history, active loans,
capture origin, cleanup plan, and use derivation.

Diagnostics are naturally graph explanations. A use-after-move points to the
transfer event and intervening path. A partial-move error identifies the moved
projection and custom-drop boundary. A borrow conflict shows both loans and the
aliasing place. A must-move failure shows the exit state. A cancellation error
shows the snapshot subtree that cannot be abandoned.

Tests construct focused CFGs for joins, loops, irreducible flow, partial moves,
loans, captures, handlers, labels, resume/cancel, cleanup, and optimizer edits.
Property tests compare event interpretation with a slower reference model. The
design is successful when all ownership-sensitive features extend this graph,
not parallel analyses that can disagree.

---

# Volume VI — MIR and Optimization

## 21. Ownership-and-Control MIR, Lowering, Cleanup, and Validation

The twenty-first design defines the compiler’s single operational IR. MIR is an
SSA-like control-flow graph with typed block parameters and explicit places.
Functions own locals, scopes, move paths, loans, labels, handlers, resumptions,
cleanup plans, source mappings, and blocks. Statements manage storage,
assignment, borrow end, destruction, and other nonterminating actions.
Terminators include jump, switch, call, host call, tail call, return, label
transfer, perform, resume, cancel, abort, and unreachable.

Core-to-MIR lowering is body-local and left-to-right. The lowering context owns a
checked builder, PlaceFlow event writer, scope stack, cleanup stack, handler
stack, label destinations, and temporary allocation. Pure Core values lower to
operands or rvalues. Computations create blocks and terminators. Nominal
construction tracks field initialization so failure or transfer cleans only
initialized fields. Pattern decision DAGs lower to switches, projections, and
binding packs.

All nonlocal edges are explicit. A label transfer routes through the exact
cleanup required between source and destination, then reaches a typed `Leave`
destination. Terminal effects abandon the continuation according to operation
semantics. Resume and cancel have separate edges. Handler dispatch and deep
reinstatement are represented, not hidden in emitter conventions. Failed
initialization, normal scope exit, return, tail call, and abort each have specified
cleanup behavior. Immediate abort has no cleanup successor.

Cleanup is derived from PlaceFlow and lexical scope. A plan lists active owners
and subtrees in reverse destruction order, custom-drop invocation, conditional
flags, and protected values. Sharing cleanup blocks is permitted only when plans
and incoming ownership states are equivalent. Nonlocal control may not discard
must-move owners. Custom drop runs exactly once before legal remaining fields are
destroyed. Cleanup metadata stays attached through optimization.

A checked MIR editor is the only mutation API after construction. It creates
fresh typed IDs, verifies block kinds and parameter signatures, updates edge
arguments, tombstones removed blocks transactionally, and reports which analysis
bundles are invalidated. Passes cannot mutate private vectors directly. The
editor supports rollback on budget failure or invariant violation so a failed
optimization does not corrupt the body.

Validation runs after lowering and every optimization stage. Structural checks
cover ID ranges, terminator presence, edge signatures, dominance prerequisites,
block ownership, and source-map validity. Type checks validate operands, rvalues,
projections, calls, and returns. Ownership checks interpret moves, copies, loans,
and cleanup against PlaceFlow. Control checks validate labels, handlers,
resumption identities, producer sets, and cancellation. Release emission accepts
only fully validated MIR.

MIR queries expose raw and optimized forms, CFG, dominators, loops, cleanup
plans, source-to-block maps, and validation reports. Canonical printing and
serialization remap local IDs deterministically. Body products can be cached
after validation. Generic instance substitution produces new validated MIR or
starts from canonical Core according to the monomorphization design.

Testing includes lowering goldens, interpreter/VM differential cases, cleanup
oracles, hostile cached MIR, editor transaction rollback, and optimizer
revalidation. The design succeeds when every runtime-relevant source semantic is
visible in one inspectable graph and no emitter-only convention silently changes
meaning.

## 22. Generic Instances, Monomorphization, and Interprocedural Summaries

The twenty-second design makes specialization demand-driven. An `InstanceKey`
contains a stable callable definition plus canonical type, lifetime, const,
effect-row, quantity, callable-producer, and perhaps target substitutions needed
to determine executable code. Equivalent substitutions canonicalize to the same
key. Body-local inference variables and source spans never enter the key.

Roots come from package entry points, exported callable requirements, tests,
reflection-free finite runtime producers, and explicit inspection requests. The
instance discovery query asks for a declaration’s canonical body, substitutes
arguments, resolves associated values, and records direct callable and data
dependencies. Newly discovered instances enter a deterministic work queue.
Recursive calls reuse an in-progress key and form an SCC rather than recursively
cloning without bound.

Not every generic requires full monomorphization at every phase. Interfaces can
retain parametric signatures and canonical Core. Typed Core may be substituted
and lowered per instance when target and ownership facts differ. Some
interprocedural analyses can operate on generic summaries with symbolic terms.
The detailed document should choose a small implementation strategy, likely
canonical generic Core plus per-reachable-instance MIR, and resist creating a
separate generic HIR.

Cross-package specialization uses dependency interfaces. An exported generic
body includes canonical Core, required private helper visibility under a sealed
package scheme, trusted primitive identities, and semantic fingerprints. The
downstream compiler validates the body and substitutes only allowed terms.
Private implementation details not required for specialization remain absent.
Changing a generic body invalidates its instances through a body fingerprint;
changing an unrelated private body does not.

Interprocedural summaries avoid loading every callee MIR. A callable summary may
include effects, quantity, captures, escape behavior, may-abort, cleanup cost,
return ownership, alias behavior, constant results for approved cases, producer
sets, control summary, and optimization cost. Summaries are query values and
fixed points over recursive SCCs. Widening guarantees convergence. A pass can
request a full callee body only when it decides to inline or specialize.

Explosion controls are explicit. Limits apply to total instances, instances per
definition, substitution depth, recursive clone depth, body size after
specialization, and optimizer-generated variants. Diagnostics show the root path
that caused growth and the substitutions involved. The compiler may fall back
to a legal indirect or generic runtime representation only when the language and
bytecode support it; otherwise it rejects with a resource diagnostic rather than
silently changing semantics.

Instance ordering and symbol identity are deterministic. Emitted names derive
from stable definition and canonical substitution fingerprints, not discovery
order. Identical functions may be deduplicated after proving equivalent layout,
cleanup, and source-mapping policy. Artifact linkage uses stable instance keys
and canonical function records.

Tests cover recursive generics, associated types, effect and quantity parameters,
consts, cross-package bodies, instance invalidation, producer sets, limit
failures, and deterministic discovery. The design is successful when the
compiler materializes only demanded executable bodies, can explain why each
instance exists, and keeps generic reuse compatible with self-host memory and
bootstrap determinism.

## 23. Optimizer Framework, Analyses, Budgets, and Invalidations

The twenty-third design treats optimization as a checked service over MIR rather
than a sequence of unstructured mutations. Optimization levels select a
published pass pipeline and budget policy. O0 performs canonical lowering and
required legality cleanup. O1 adds inexpensive local simplification. O2 is the
normal release pipeline and includes proven control specialization. O3 may spend
more work but obeys exactly the same legality rules as O2.

Analyses are grouped into reusable bundles: CFG and predecessor structure,
reachability and reverse postorder, dominators, loops and SCCs, liveness and use
counts, PlaceFlow and ownership, regions and alias sets, scalar constants and
ranges, aggregate facts, callable and effect summaries, cleanup cost, and code
size. Each bundle has a typed key, construction function, dependencies, and
invalidation mask. The checked MIR editor reports mutations so unaffected
analyses remain cached.

Passes implement a common contract: inspect validated input, reserve a work
budget, stage edits transactionally, declare preserved analyses, validate the
result, and emit a deterministic report. A failed profitability test makes no
edit. A resource limit ends the pass cleanly and either retains the previous
valid MIR or emits a configured remark. An internal invariant failure discards
the transaction and is never converted into a source diagnostic.

The pipeline includes CFG simplification, unreachable removal, block merging,
branch folding, constant and copy propagation, phi or block-parameter
simplification, aggregate scalar replacement, load/store forwarding under alias
proofs, loan-proof erasure, devirtualization, callable and capture scalarization,
inlining, tail formation, handler and resumption specialization, cleanup
simplification, register-friendly canonicalization, and final peephole-oriented
forms. Each transformation must preserve traps, evaluation order, `Use`, loans,
cleanup order, custom drop, effects, cancellation, and host authority.

Fixed-point iteration is bounded and deterministic. Pass groups run until no
semantic change or budget exhaustion. Fingerprints detect stability. Worklists
use stable block and value ordering. Profitability uses explicit target- and
optimization-level inputs. Recursive specialization has strict depth and size
limits. A pass that depends on target layout records that dependency so
architecture-independent MIR can remain reusable.

Optimization is observable. `optimization_report` lists passes, changes,
invalidated analyses, costs, budgets, remarks, and source owners. `compare_mir`
shows canonical O0/O2 differences. Trace-equivalence tests execute selected
programs before and after each pass. `why_not_inlined`, `why_not_scalarized`, and
control-specific explanations expose barriers such as escape, custom drop,
unique loan, dynamic producer set, or cost.

Caching may store validated optimized MIR by instance, target, level, pipeline
generation, and semantic input fingerprint. Cached optimized bodies rerun
structural validation. Pass statistics and wall-clock timings are nonsemantic and
excluded from artifact keys, while pipeline version and decisions affecting
bytes are included.

The framework is successful when adding a pass does not require intimate access
to every MIR vector, analysis reuse is safe and measurable, budget failure leaves
valid input intact, and differential validation can isolate the first
transformation that changes semantics. This infrastructure is what lets the
Glorious-specific optimizer remain ambitious without becoming unreviewable.

## 24. Source-Defined Control Specialization

The twenty-fourth design is the optimizer’s defining Glorious feature. Familiar
control is ordinary library code built from callables, effects, handlers,
patterns, labels, and quantitative relations. The compiler must not recognize a
callee named `loop` or `if`; it derives name-independent `ControlSummary` facts
from the selected callable, producer set, environment, effects, resumption
quantity, labels, and captures. Specialization then replaces proven abstraction
machinery with direct MIR control.

A control summary describes invocation count, delayed parameters, branch
exclusivity, tail positions, label transfers, performed operations, handler
producer sets, resumption behavior, captured places, cleanup effects, and
post-state. Summaries compose through generic calls and effect-polymorphic
callbacks. A trusted library helper and an equivalent user-defined helper should
receive the same summary when their semantics match. Names appear only in
human-facing reports.

Conditional specialization recognizes a selected callable that invokes one of
several delayed bodies according to a static control protocol. It forms direct
switch or branch blocks while preserving left-to-right evaluation, captures,
and result joins. Loop specialization recognizes state-threading callables or
label-indexed `LoopControl` effects and creates natural MIR loops, `break`
destinations, `continue` edges, and loop-carried parameters. Generic early-exit
labels become cleanup plus direct `Leave` without runtime label objects.

Handler specialization removes static dispatch when the performed effect and
handler producer are known. Terminal operations fuse to direct exits. Canonical
one-shot performance with a single resume or cancel becomes direct control and
can eliminate continuation allocation. Forwarding through one or more known
handlers composes when effect rows and captures permit. Multi-shot or escaping
continuations remain runtime objects unless copy, cleanup, and replay proofs are
complete.

Pattern-selection helpers can specialize through the common decision DAG and
handler representation. Propagation helpers using `Result`, effects, or labels
become direct error or success edges. Traversal helpers such as `fold_until`,
worklist runners, and parser transactions can inline into loops with cleanup-
backed rollback. The optimizer must avoid expanding abstractions when code size,
dynamic producers, custom drop, loans, or unknown quantities make specialization
illegal or unprofitable.

`control_plan` is a first-class query. For a source call or MIR site it reports
the selected callable, exact producers, delayed arguments, quantity facts,
handler stack, labels, captures, formed branches or loops, residual allocations,
and failure reasons. Development lints warn when an intended hot control helper
remains dynamic because of an avoidable abstraction barrier. Machine-applicable
fixes may suggest annotations or restructuring but never hard-code library
names.

Validation compares unspecialized and specialized execution at O0–O3, including
cleanup, abort, effect forwarding, nested loops, labels, and captures. MIR
validators rerun after formation. Performance tests assert the absence of
residual callables, handlers, label objects, or continuation allocations for
canonical cases and measure code size.

The design is successful when source libraries can invent control abstractions
without compiler patches, ordinary hot constructs lower as efficiently as
built-ins, and every success or failure is explainable from structural facts.
That is the point where library-defined control becomes a practical systems-
language feature rather than only an elegant semantic claim.

---

# Volume VII — Emission and Runtime

## 25. Register Allocation, Instruction Selection, and Function Emission

The twenty-fifth design turns final validated MIR into deterministic per-function
bytecode fragments. Emission is not another semantic IR. It uses temporary
assembler records, physical register assignments, block layout, relocation
entries, and canonical-pool references, all owned by an `EmissionSession` and
released after the fragment is frozen.

Register allocation starts from typed MIR locals and temporaries. Addressable
places that can be borrowed or partially moved receive stable storage according
to the bytecode model. Pure SSA values can share physical registers when exact
type, representation, ownership state, loan state, and cleanup requirements are
compatible. Generation 1 should favor a deterministic linear or graph allocator
with conservative one-to-one storage for difficult owners, then add broader
cross-block reuse only under proven interchangeability.

Block layout uses entry, reverse postorder, lexical cleanup, handler,
resumption, and label grouping. The order is deterministic and attempts to
maximize fallthrough while preserving stable source and cleanup intervals. Edge
arguments become parallel transfers. A cycle-breaking algorithm uses typed
temporary registers and distinguishes move from copy according to final
ownership state. Transfer snapshots prevent one edge copy from observing a
partially updated register set.

Instruction selection maps each MIR operation to a specified opcode sequence.
It handles scalars, aggregates, projections, borrows, calls, host calls, tail
calls, switches, labels, effects, handler installation, perform, resume, cancel,
destruction, and abort. Cleanup and continuation-capture maps are generated from
final MIR and PlaceFlow, not guessed from register liveness. Unsupported MIR
forms are internal emission failures, never silently encoded as generic host
calls.

Canonical pools hold strings, constants, types, signatures, operand packs,
binding packs, cleanup plans, capture layouts, and source-map records. During
construction they may use noncanonical local IDs and hash lookup. Freeze sorts
canonical encodings, deduplicates values, creates old-to-final remaps, and patches
all references. Per-function fragments include compatibility fingerprints for
pool schemas and target representation so the linker can combine or reject
them safely.

Function emission is independently cacheable. The key includes instance,
validated optimized MIR fingerprint, target, bytecode generation, instruction-
selection generation, and relevant manifests. A cached fragment is defensively
decoded and checked before linkage. Source-to-PC maps retain logical source
identities and inlining chains without embedding absolute paths. Emitted symbol
names derive from stable instance keys.

Peepholes at this layer are restricted to encoding-equivalent local rewrites:
fallthrough jumps, target-safe NOP removal, transfer-temporary collapse, and
constant-pool-aware simplification. Any rewrite involving ownership, cleanup,
handlers, or labels must either be represented and validated at MIR or run a
bytecode-level validator. Emission never changes high-level legality.

Tests compare canonical fragments across allocation perturbations, exercise
parallel-copy cycles, register reuse, every opcode family, cleanup and capture
maps, cache round trips, source mapping, and verifier acceptance. The design is
complete when function emission is deterministic, incremental, inspectable, and
small enough that assembler scratch cannot become a fourth persistent program
representation.

## 26. Interface Artifacts, Executable Artifacts, Linking, and Serialization

The twenty-sixth design specifies two principal persistent products. A package
interface describes exported source semantics for downstream compilation. A
`.grbc` executable artifact describes verified-runtime candidates for the VM.
They share canonical encoding infrastructure but have different trust and
compatibility contracts. Neither serializes private compiler arenas directly.

Every binary format has a fixed header containing magic, format generation,
required and optional feature sets, producer identity, section directory,
content digest policy, and resource-relevant counts. Sections are described by a
schema table with ID, criticality, cardinality, encoding, alignment, and fixed
width where applicable. Unknown critical sections fail closed. Optional
noncritical sections can be skipped. All integer widths, endianness, sentinel
values, and length limits are specified rather than embedded as magic numbers.

The interface artifact contains package identity, modules, exported definitions,
visibility, generic binders, semantic signatures, traits, impl heads, associated
contracts, effects, fixities, public consts, required generic Core or summaries,
layout or ABI facts where stable, trusted producer declarations, source-independent
names, and dependency fingerprints. It excludes private bodies unless required
under a sealed specialization contract. The decoder reconstructs typed values
and verifies all references, producer ownership, and schema features.

The executable artifact contains canonical types and signatures, functions,
constants, host imports, capability declarations, instruction streams, block and
edge metadata, cleanup plans, handler and resumption tables, continuation
capture layouts, source maps, and optional optimization or inspection metadata.
It carries no claim that raw bytes are safe. The independent verifier produces
that judgment after decoding.

Linking begins from deterministic instance roots and combines emitted fragments,
deduplicating canonical pools and compatible functions. It verifies that each
fragment uses the same target, bytecode generation, primitive manifest,
representation rules, and interface assumptions. Symbols resolve by stable
instance identity. Unresolved, duplicate, incompatible, or cyclic initialization
relationships produce linker diagnostics. Capability declarations are the exact
union of authorized host imports actually reachable, constrained by the request
manifest.

Serialization is canonical. Records are ordered by stable keys or canonical
encoded value. Local indices are assigned only after freeze. Maps encode as sorted
sequences. Checksums cover the precise canonical bytes. Optional debug sections
must not perturb executable semantic sections; release policy decides whether
they participate in the whole-artifact digest. Atomic publication writes a
complete temporary blob and manifest before exposing the output.

Compatibility policy distinguishes source, interface, and bytecode generations.
A compiler may read older interface schemas through explicit migrations, but it
never guesses. The VM advertises supported artifact features. Released seeds
record exact compiler, standard-library, interface, bytecode, and verifier
identities. Golden fixtures test backwards compatibility for promised G1
artifacts.

Testing includes round trips, canonical-order perturbations, truncation and
length attacks, unknown features, interface private-change stability, fragment
linking, capability reachability, source maps, and cross-version fixtures. The
design is successful when persistent products are compact, deterministic,
self-describing, defensively decodable, and independent of internal compiler
layout.

## 27. Bytecode Decoder and Verifier

The twenty-seventh design defines the independent artifact acceptance boundary.
The decoder treats `.grbc` as hostile bytes. It validates the header, section
directory, ranges, alignment, counts, lengths, integer conversions, feature
requirements, canonical ordering where required, and allocation budgets before
constructing typed views. It never indexes an unvalidated table or allocates
according to an unchecked attacker-controlled product.

Decoding yields an immutable candidate artifact with typed IDs scoped to that
artifact. The verifier then checks global tables and each function. Type and
signature records are well formed and finite. Constants match their types.
Function bodies reference valid pools. Block boundaries and instruction targets
are exact. Host imports correspond to declared capabilities and trusted runtime
roles. Producer sets for callables, handlers, and resumptions are finite and
sealed according to the bytecode specification.

Function verification is a deterministic dataflow over program counters and
control states. A state records each register’s type, ownership mode,
availability, place or reference origin, active loans as represented at runtime,
initialized aggregate fields, handler stack, label environment, resumption
identity, cleanup obligations, and protected result state. Instructions have
specified preconditions and state transitions. Joins require compatible states
and produce canonical merged summaries.

Move and copy checking ensures owners are not reused, copies are permitted, and
partial aggregate states match binding or cleanup packs. Borrow instructions
validate origins, mutability, and encoded lifetime/control restrictions.
Calls match signatures and receiver modes. Tail calls satisfy cleanup and
protected-argument rules. `Leave`, `Perform`, `Resume`, and `Cancel` validate
brands, destinations, handler identity, continuation quantity, capture layout,
and abandonment cleanup.

Cleanup maps are independently cross-checked against reachable register and
place state. Every abandoning edge destroys exactly the permitted live owners in
valid reverse order, invokes custom drop correctly, and preserves protected
values. Missing, duplicated, or overbroad cleanup is rejected. The verifier does
not infer source `Use` proofs, but it checks the concrete ownership protocol the
compiler encoded.

Successful verification constructs a private `FrozenExecutionImage` containing
only normalized, checked tables and precomputed runtime metadata. Raw mutable
artifact structures are not exposed to the VM constructor. Verification failure
returns a stable artifact diagnostic with section, function, PC, expected state,
observed state, and bounded context. Development inspectors can print a selected
verified or seeded state without recompiling source.

The verifier is resource-bounded. It caps sections, functions, registers, blocks,
instructions, state size, producer sets, aggregate depth, and dataflow updates.
Sparse hostile namespaces and allocation-amplification inputs are tested.
Worklists use stable order. Memoized state uses checked arenas. A verifier cache,
if used, keys the complete artifact digest and verifier generation and remains an
optional optimization.

Testing includes hand-built valid fixtures, compiler-generated corpora, every
opcode transition, mutation and truncation fuzzing, hostile length fields,
cleanup adversaries, label/handler/resumption identities, recursive callables,
and VM differential execution. The boundary is successful when no compiler
assertion is required for VM safety and an invalid artifact cannot obtain an
execution image.

## 28. VM, Supervisor, Host Capabilities, and Runtime Limits

The twenty-eighth design executes only a `FrozenExecutionImage`. The VM is a
safe typed register machine, not a source interpreter. It owns call frames,
register storage, aggregate and place arenas, callable environments, handler
frames, continuation snapshots, cleanup execution, and host-call requests. It
assumes verifier-established invariants but retains bounds checks and safe handle
access so implementation defects do not become arbitrary memory access.

A frame references one verified function, program counter, physical registers,
place state, return destination, active handlers, and cleanup context. Values use
a finite runtime representation for scalars, aggregates, references, callables,
labels where not erased, handlers, and resumptions. Arena handles include
generations to reject stale access. Move empties the source register; copy uses
verified copy glue; destruction follows verified plans. Tail calls reuse or
replace frames only under the encoded contract.

Effects install and traverse handler frames according to deep-handler semantics.
Perform packages payload and continuation state from a verified capture plan.
Resume restores or copies a snapshot according to quantity. Cancel runs verified
abandonment cleanup. Multishot representations are finite and reject runtime
operations outside the verifier’s summary. Cycle reclamation, if required by
callables or continuations, uses a bounded safe scheme with explicit accounting;
generation 1 should avoid general garbage collection.

The worker has no ambient filesystem, process, network, or diagnostic authority.
A host instruction emits a typed request naming one finite capability role and
arguments. The supervisor compares it against exact grants from both artifact
manifest and invocation policy, then routes it to a host adapter. There is no
prefix wildcard. Adapters validate paths, encodings, sizes, and policy again.
Denied requests produce a classified runtime capability failure.

The supervisor owns isolation. It starts the worker process or equivalent
sandbox, enforces wall-clock or instruction time, memory and allocation limits,
output limits, and termination policy, and distinguishes verifier rejection from
worker crash, timeout, memory exhaustion, program abort, and normal exit. Runtime
capabilities cannot be inherited from the compiler process. A package with no
manifest receives an empty grant set.

Execution is deterministic inside the language’s specified host boundary.
Pure bytecode has deterministic results. Host inputs such as process arguments or
files are explicit requests and may be recorded for reproducible tests. The VM
uses checked integer semantics and fixed float behavior specified by G1. Runtime
profiling and progress sampling are opt-in side channels excluded from program
state.

Diagnostics report function and PC, source mapping, call stack, operation, and
bounded value context without leaking arbitrary host data. Development tools
support instruction traces, memory profiles, hot-function sampling, and seeded
artifact replay. Production defaults remain low overhead and resource bounded.

Tests cover every instruction, move/copy/destruction, calls and tail calls,
handlers, one-shot and multi-shot resumptions, cancellation, capability grants,
time and memory limits, hostile verified-but-expensive programs, supervisor
classification, and source-level end-to-end examples. The runtime design is
successful when verification, execution, and host authority remain visibly
separate and untrusted programs cannot acquire the compiler’s ambient powers.

---

# Volume VIII — User Experience, Validation, and Self-Hosting

## 29. Diagnostics, Explanations, and Machine-Applicable Fixes

The twenty-ninth design treats diagnostics as structured semantic products.
Every diagnostic has a stable code, class, severity, primary typed site, related
sites, owning declaration, expected and observed facts, message arguments,
notes, explanation references, and optional fixes. Phase-local error enums remain
useful internally, but exhaustive adapters map them into one cross-phase model.
Rendering to terminal text, JSON, LSP, or test goldens happens at the outer
client.

Location spaces are typed: source bytes, tokens, definitions, syntax expressions,
resolution occurrences, semantic types, inference variables, trait goals,
places, loans, Core nodes, MIR blocks and operations, artifact sections,
functions, and PCs. A diagnostic may cite several spaces and resolve them through
source maps. Raw numeric IDs never appear as user-facing identity. When a
location no longer maps exactly after an edit, the diagnostic is tied to its
snapshot rather than guessed onto new text.

Explanations preserve proof provenance selectively. Type mismatches show
expected-type origin, observed expression, normalization, and substitutions.
Trait failures show candidate search and nested goals. Effect failures show the
operation path and unhandled row. Quantity failures show interval composition
and the path leaving an obligation. Borrow errors show loan creation and
conflict. Control-plan remarks show specialization barriers. Query explanations
show invalidation or cache decisions. Compact default messages link to richer
views rather than dumping entire proof trees.

Recovery and failure classes remain distinct. User source diagnostics can be
reported together. Resource limits identify the subsystem and configured bound.
Cancelled requests normally do not surface as errors. Corrupt cache or interface
records are infrastructure diagnostics. Internal invariants include a stable
compiler code and development context but are not disguised as source mistakes.
Verifier and runtime diagnostics belong to their own domains and preserve
artifact or execution locations.

Fixes are typed edits with applicability. `MachineApplicable` fixes have exact
snapshot spans, replacement text, preconditions, and no unresolved ambiguity.
`MaybeIncorrect` suggestions are never auto-applied silently. Multi-file fixes
include atomic edit groups. Examples include redundant `move`, missing effect
row, import insertion, explicit type argument, fixity declaration, or control-
fusion annotation where the language defines one. Fix generation may query
semantics but cannot write files.

Deterministic ordering and suppression are specified. Diagnostics sort by
logical path, span, code, owner, and stable tiebreaker. Lint levels come from
manifest and command policy and affect only relevant diagnostic queries unless a
deny level changes build success. Cascades are limited through error roots and
budgets. Compile-fail tests compare structured codes, sites, and arguments, with
rendered text goldens only where presentation itself is under test.

Tooling queries include diagnostics for a package, explanation by diagnostic ID,
proof tree, fixes, type/quantity/borrow state at a position, and source-to-MIR or
PC navigation. The language server streams only results for the current document
version. Documentation can link diagnostic codes to stable reference pages.

The design is successful when Glorious’s sophisticated semantics are teachable
through errors, every domain of failure is honest, fixes are safe, output is
stable, and neither compiler phases nor the VM print directly as a substitute
for structured information.

## 30. Compiler Service APIs and Tooling

The thirtieth design exposes one compiler service to every user-facing tool. The
service can run in-process as a library, behind a long-lived local daemon, or
through a stable request protocol, but all modes invoke the same typed queries.
The first self-hosted release may prioritize an in-process API plus `grand-lsp`;
the data contracts should leave room for a daemon without turning queries into
dynamically typed RPC strings.

The core API creates or interns normalized input worlds, opens snapshots, starts
request sessions, demands typed query roots, streams structured diagnostics, and
returns immutable products. High-level operations include `check`, `build`,
`test`, `format`, `document`, and `inspect`, but they are orchestration recipes
over lower queries. Clients cannot construct private `DefKey`, `TypeKey`, or MIR
IDs without validation.

`grc` parses options, reads explicit inputs when used alone, creates a request,
and selects outputs such as interface, Core, MIR, bytecode, JSON diagnostics,
control plan, or bundle-token inspection. `grand` supplies workspace and
dependency orchestration and writes artifacts atomically. Equivalent requests
must share compiler code paths and produce equivalent manifests.

`grand-lsp` maintains document versions and editor overlays as immutable
revisions. It maps LSP UTF-16 positions to compiler spans, cancels obsolete
requests, and answers diagnostics, hover, completion, signature help, definitions,
references, rename, symbols, semantic tokens, formatting, and code actions.
Completion may use recovered syntax and partial semantic results, but each item
carries confidence and snapshot identity. Expensive workspace queries are
budgeted and cancellable.

The formatter consumes lossless tokens and shared syntax shape. It preserves
comments, normalizes accepted optional syntax, and is idempotent. Formatting
broken code uses bounded structural recovery. Documentation consumes exported
interfaces, resolved links, signatures, effects, quantities, visibility, and
source excerpts. Test tooling compiles source and compile-fail cases, executes
only through verified `grvm`, and records structured outcomes.

Inspection is a supported product rather than ad hoc environment variables
alone. Queries expose tokens, delimiter pairs, module outlines, resolution,
interfaces, inferred types, trait goals, effect rows, quantities, captures,
PlaceFlow, Core, raw and optimized MIR, optimization reports, control plans,
register allocation, emitted fragments, artifact sections, verifier states,
source-to-PC maps, cache decisions, and invalidation chains. Filters by owner,
span, function, block, or PC keep output bounded.

A service protocol, if used, is versioned and capability-limited. Requests carry
compiler build, revision, operation, budget, and cancellation identity. Responses
are framed, length-bounded, and typed by schema. The daemon never inherits a
client’s arbitrary runtime capabilities. Source writes remain client-controlled
edits. Crashes or invariant failures cannot corrupt persisted semantic state
because publication is atomic.

End-to-end tests run the same package through direct library calls, `grc`,
`grand`, and LSP-backed checks and compare semantic outputs. Editor tests cover
rapid revisions, cancellation, stale responses, rename, formatting, and broken
code. The service is successful when tooling breadth grows by adding queries and
presentation, not by cloning compiler logic.

## 31. Testing, Differential Oracles, Fuzzing, and Performance

The thirty-first design makes validation part of the architecture. Unit tests
cover small pure mechanisms such as interval arithmetic, typed arenas, canonical
encoding, scope journals, delimiter pairing, and MIR editor invariants.
Component tests exercise each query family with focused source fixtures.
Integration tests compile real packages through interface, Core, MIR, emission,
verification, and execution. Every test records the exact compiler build and
input manifest needed for reproduction.

Compile-pass tests assert acceptance and selected semantic facts. Compile-fail
tests compare stable diagnostic codes, typed sites, arguments, and fixes.
Runtime tests execute only verified artifacts and assert output, exit class, host
requests, and cleanup traces where observable. Golden text is used for canonical
IR, bytecode, or rendering only when the textual format is itself a contract;
semantic comparisons prefer structured values.

Differential testing bridges the Rust bootstrap and self-hosted compiler during
migration. The same source corpus is lexed, scanned, parsed, resolved,
elaborated, lowered, emitted, verified, and where possible executed through both
implementations. Comparisons use canonical phase snapshots and accepted/rejected
outcomes, not private allocation IDs. The AST evaluator remains an oracle only
for its documented subset and never proves ownership or cleanup it does not
model.

Optimizer validation compares O0 and optimized execution, pass-by-pass trace
semantics for selected programs, verifier acceptance, and ownership/cleanup
facts. Random small MIR generators create valid bodies, apply one transformation,
and compare reference interpretation. Each pass has regression fixtures for
previous defects. Source-defined control tests assert both semantics and the
absence of residual machinery in canonical optimized cases.

Fuzzing targets lossless lexing, delimiter pairing, body recovery, interface
decoding, cache decoding, artifact decoding, verifier dataflow, VM instruction
sequences from verified corpora, and service framing. Coverage-guided mutation,
fixed-seed arbitrary input, truncation, length amplification, sparse extreme IDs,
and structured grammar generators are used. Fuzzers have memory and time limits
and save minimized reproducers with schema/build identity.

Incremental tests define edit scenarios and expected invalidation sets. They
compare clean and incremental outputs, warm and cold caches, reordered input
discovery, multiple live revisions, cancellation, and corrupted records.
Determinism tests vary hash seeds, worklist order, arena padding, process history,
and cache state, then compare all canonical products. Bootstrap stage identity
is the final determinism gate.

Performance testing separates latency, throughput, memory, artifact size, and
runtime. Benchmarks cover cold check/build, one-line body edit, public interface
edit, LSP hover and completion, self-compilation, verifier load, VM execution,
and pathological bounded failures. Reports include query counts, hit rates,
retained bytes, hot functions, optimizer work, emitted size, and instruction
rate. Regression gates use stable machines or normalized metrics and distinguish
correctness budgets from aspirational targets.

Release readiness requires a green matrix for compiler, VM, tooling, editors,
real `grc`–`grand`–`grvm` contracts, hostile artifact corpora, reproducibility,
self-host parity, and bootstrap convergence when implemented. CI may shard
expensive suites but must run automatically for protected changes. The testing
design is successful when a defect can be localized to the first differing
phase and performance claims are reproducible rather than anecdotal.

## 32. Self-Hosting, Bootstrap Convergence, Migration, and Release

The thirty-second design turns the target architecture into a staged program of
work. The Rust stage-zero compiler remains the behavioral source while semantics
are frozen and the self-hosted implementation reaches parity. The Glorious
compiler source is organized around the same boundaries described in this
series: diagnostics, compiler database, frontend, static semantics, Core,
PlaceFlow/MIR, optimization, emission, and probes. Bootstrap-only adapters are
kept separate from production modules.

Migration proceeds by authoritative slices, not a flag-day rewrite. Lossless
lexing, structural scanning, headers, body parsing, resolution, interfaces,
Typed Core, PlaceFlow, MIR, emission, and standard-library surfaces each receive
canonical differential tests. A parity ledger records whether every Rust test
family is unported, partially covered, or covered by named self-host tests.
Moving a row to covered requires both acceptance/rejection parity and semantic
product parity where applicable.

The first stage-zero build compiles the self-hosted source and standard library
into a stage-one verified compiler artifact. Stage one compiles the same
canonical input world into stage two. Stage two compiles it into stage three.
All stages use the same pinned source bundle, dependency interfaces, target,
capabilities, optimization level, compiler limits, primitive manifest, and build
manifest. The verifier checks each produced artifact before it becomes the next
compiler.

“Self-hosted” means a Glorious compiler can compile its own source. “Bootstrap-
converged” is the stronger claim that stage-two and stage-three compiler artifacts
are byte-for-byte identical. A mismatch is investigated through phase
fingerprints, interfaces, instance sets, MIR, emitted fragments, and artifact
sections. Convergence is not declared from equivalent runtime output alone.

The release seed is a supply-chain product. A release contains compiler source,
standard-library source, canonical seed `.grbc`, Rust verifier and VM sources or
binaries according to distribution policy, complete build manifest, schema and
feature generations, checksums, compatibility fixtures, license data, and exact
commands for rebuilding stages. Seed provenance and signatures are documented.
Reproducible builders can verify the checked-in seed and stage convergence.

Performance gates matter because a theoretically self-hosted compiler that
cannot compile itself within bounded resources is not viable. The architecture
currently targets a supervised cold self-compilation budget, with explicit time
and memory goals recorded in the normative architecture. Query, cache, memory,
and hot-function profiles identify bottlenecks. Optimizations that improve the
compiler must remain semantically ordinary Glorious features rather than hidden
host evaluators.

Release compatibility distinguishes source language, interface, bytecode,
standard-library, and tooling guarantees. Pre-alpha releases may break all with
clear generations. A stable G1 release freezes artifact contracts and declares
which old interfaces or seeds can be read. Bootstrap-only Rust shortcuts,
compatibility probes, injected preludes, or primitive-name fallbacks are tracked
and removed or made into explicit manifest contracts before final convergence.

The migration plan ends by making CI and review reflect the trust story. Pull
requests run automatic compiler, verifier, VM, tooling, editor, differential,
determinism, and bounded self-host suites appropriate to their scope. Release
candidates run the complete stage chain and hostile corpora. Architecture and
remaining-work documents are updated from measured facts, not optimistic
percentages.

The project is complete at this layer when the self-hosted compiler is the
single source-semantic authority, produces independently verified artifacts,
compiles itself reproducibly within the resource gate, yields identical stage-two
and stage-three bytes, and ships enough source, manifests, and tooling for another
party to reproduce that claim.

---

# Using the Compendium

These synopses are the breadth-first layer of the snowflake. They should now be
reviewed together for conflicts in vocabulary, authority, identity, data
ownership, query boundaries, caching, failure classes, and bootstrap assumptions.
The individual documents can then expand one synopsis at a time using the shared
fifteen-part structure from the roadmap:

1. purpose and scope;
2. goals and non-goals;
3. public queries and interfaces;
4. data structures and ownership;
5. algorithms and phase order;
6. semantic invariants;
7. cycles and fixed points;
8. incremental dependencies and invalidation;
9. caching and persistence;
10. diagnostics and explanation;
11. cancellation and resource limits;
12. determinism requirements;
13. testing strategy;
14. migration from the current implementation;
15. open questions and rejected alternatives.

The detailed documents may refine these proposals, but a refinement should name
which other synopses it affects. No document should introduce a new persistent
semantic representation, authority boundary, identity space, cache truth source,
or failure class without updating the system-level designs. The value of this
compendium is that every local implementation choice remains visible as part of
one compiler.