# Self-Hosted Glorious Compiler — Expanded Synopsis Working Draft

Status: **work in progress**. This file is the current expansion pass toward a
much larger breadth-first synopsis compendium. It is intentionally published as
a separate draft rather than replacing the merged
[`00-snowflake-synopsis-compendium.md`](00-snowflake-synopsis-compendium.md)
until the expanded version has reached full breadth, internal consistency, and
the intended scale.

Parent documents:

- [Snowflake Stage One: The Ideal Self-Hosted Glorious Compiler](../self-hosted-compiler-snowflake-stage-one.md)
- [32-Document Snowflake Roadmap](00-snowflake-document-roadmap.md)
- [Current 32-Document Synopsis Compendium](00-snowflake-synopsis-compendium.md)
- [01. Architecture and Trust Boundaries](01-architecture-and-trust-boundaries.md)
- [02. Compilation Inputs, Revisions, and Session Ownership](02-compilation-inputs-revisions-and-session-ownership.md)

This pass deepens each document around a common implementation frame:

1. desired outcome;
2. authoritative component;
3. primary data model;
4. public query and service surface;
5. ownership and lifetime;
6. algorithms and phase order;
7. incremental dependencies;
8. caching and persistence;
9. diagnostics and explanation;
10. cancellation and resource limits;
11. determinism and security;
12. tests, migration, and completion criteria.

The final expanded compendium should be read horizontally before the remaining
individual specifications are completed. Its purpose is to expose conflicts
between local designs while they are still cheap to change.

This working draft currently expands **Volume I and Volume II**, documents
**01–08**. Documents 09–32 remain represented by the merged synopsis compendium
until their expanded passes are added here.

---

# Volume I — The Compiler’s System Spine

## 01. Architecture and Trust Boundaries

### Desired outcome

The compiler should exist as a collection of narrowly authorized components,
not as one executable that can read arbitrary files, mutate global state,
compile source, verify bytecode, execute programs, and grant host access simply
because it happens to contain all of those functions.

The architecture must make the following claims separately:

- `grand` assembled the requested package world;
- the compiler decided the meaning and legality of Glorious source;
- the emitter encoded a candidate artifact;
- the verifier accepted the artifact-level runtime contract;
- the supervisor granted a finite runtime authority set;
- the VM executed within that authority set;
- the bootstrap chain reproduced the compiler artifact.

No single word such as “verified” should collapse these claims.

### Authoritative components

`grand` owns package acquisition, lockfiles, workspace expansion, filesystem
discovery, vendoring, target selection, runtime policy, and output placement.

The self-hosted compiler library owns all source semantics:

- lexing and structural syntax;
- module and name resolution;
- types, traits, effects, quantities, and lifetimes;
- privacy and opaque-representation authority;
- Typed Core construction;
- PlaceFlow and MIR construction;
- optimization legality;
- deterministic artifact emission.

The decoder and verifier own artifact acceptance.

The supervisor and host adapters own runtime isolation and external authority.

Tooling clients ask the same compiler service for semantic facts.

### Primary boundary records

The architecture should define typed records for:

```text
CompilationRequest
CompilationOutcome
DependencyInterfaceBytes
CandidateArtifact
VerifiedArtifact
FrozenExecutionImage
RuntimeGrantSet
RuntimeOutcome
BootstrapManifest
```

These types must not be aliases for one byte buffer.

A `CandidateArtifact` must not be accepted by the VM constructor.

A `VerifiedArtifact` should carry the exact verifier generation and compatible
feature set that established its validity.

A `FrozenExecutionImage` should be private to the verifier/VM boundary and
contain only normalized, bounds-checked runtime structures.

### The orchestration boundary

The mutable outside world is normalized before it reaches semantic code.

The host may begin with paths, environment variables, command-line flags, open
editor buffers, package selections, and lockfile state. It converts those into
immutable bytes and typed metadata.

The compiler receives:

- exact source bytes;
- exact logical paths;
- exact package identities;
- exact dependency interfaces;
- exact standard-library identity;
- exact target and language options;
- exact runtime capability declarations;
- exact structural limits.

The compiler does not reopen a path later. A path is a logical label over
supplied bytes, not permission to read the filesystem.

This rule prevents a request from observing a file before and after an edit,
allows editor overlays to be coherent, and makes remote or sandboxed execution
possible without changing semantic APIs.

### Authority rules

Semantic phases receive immutable source and validated compiler-owned data.
They receive no ambient filesystem, process, environment, network, or host
rendering capability.

The emitter may construct bytes but may not execute them.

The verifier may inspect bytes but may not resolve packages or import source
semantics from the compiler.

The VM may issue only typed host requests represented in the verified image and
allowed by the supervisor’s exact grant set.

The LSP may read open-document snapshots supplied by the editor adapter, but a
semantic query may not silently modify source.

The formatter may produce a text edit but may not apply it without an explicit
host action.

### Semantic authority

All normal clients must use the same compiler library.

A direct `grc` command, a `grand check`, an LSP diagnostic request, a hover, a
documentation build, and a compile-fail test may demand different root queries,
but they must not use different definitions of parsing, visibility, trait
selection, effect checking, quantity checking, or borrowing.

The language server must not contain a lightweight type checker that later
disagrees with release builds.

The formatter must not contain a second lexer whose token boundaries differ
from compiler diagnostics.

The verifier must not become a second source compiler. It validates the lowered
runtime contract, not source-level trait or privacy semantics.

### Candidate, verified, and executable artifacts

The architecture should make artifact state explicit in the type system.

```text
MIR
  -> CandidateArtifact
  -> VerificationResult
  -> VerifiedArtifact
  -> FrozenExecutionImage
  -> RuntimeOutcome
```

A candidate artifact is untrusted even when emitted by the compiler in the same
process.

Verification should defensively decode the candidate from bytes or from an
interface equivalent to the byte representation, so the compiler cannot bypass
wire-format checks by handing the VM private mutable structures.

A verified artifact may still be denied execution when its requested capability
set exceeds supervisor policy.

A frozen image is immutable after verification. The VM must not receive mutable
section tables that can be changed after checks.

### Host capability model

Source effects and runtime authority are related but distinct.

The compiler checks that a program’s source-level host imports and effects are
legal under its declared manifest.

The artifact records the exact host operations it may request.

The supervisor intersects that declaration with user and environment policy.

The host adapter checks each actual request independently.

A broad spelling prefix is not a capability grant. Generation 1 should use a
finite exact set such as:

```text
process.args
fs.read
fs.write
diagnostic
```

Each operation has typed arguments, size limits, and policy validation.

### Standard-library and primitive authority

The standard library is ordinary source plus a trusted declaration manifest.

The compiler must not grant machine-primitive authority to any declaration
merely because it has a familiar name such as `wrapping_add`, `if`, or `loop`.

Primitive authority comes from a manifest-bound stable declaration identity in
the distinguished standard-library input.

The VM recognizes bytecode operations, not source names.

The optimizer recognizes structural control summaries, not a whitelist of
standard-library spellings.

### End-to-end build flow

A normal build should follow this flow:

```text
host state
  -> grand normalization
  -> immutable CompilationRequest
  -> CompilerDatabase snapshot
  -> semantic query roots
  -> CandidateArtifact
  -> independent verification
  -> VerifiedArtifact + build manifest
  -> atomic host publication
```

A normal run adds:

```text
VerifiedArtifact
  -> supervisor policy intersection
  -> FrozenExecutionImage
  -> isolated grvm worker
  -> checked host requests
  -> RuntimeOutcome
```

An editor request stops at semantic query products and does not require artifact
emission unless the user explicitly asks to build or run.

### Failure classes

The boundary must preserve at least these failure classes:

- orchestration failure;
- source-diagnostic rejection;
- recovered IDE result;
- request cancellation;
- resource-limit exhaustion;
- dependency-interface corruption;
- cache corruption;
- compiler invariant failure;
- emission failure;
- verifier rejection;
- denied capability;
- supervised runtime failure.

Each class has a different owner and a different remediation path.

A corrupted cache entry should normally be a cache miss plus an optional
compiler-health warning, not a source error.

A compiler invariant failure must not be reformatted as “invalid syntax.”

A verifier rejection should identify an artifact/runtime-contract failure, even
when the compiler produced the bytes.

### Determinism and security

Externally visible records must be canonical.

Local arena allocation and hash-table order may vary internally, but they may
not alter diagnostics, interfaces, artifacts, manifests, verifier products, or
bootstrap stage bytes.

Untrusted inputs include source, dependency interfaces, cache records, artifact
bytes, runtime arguments, and host-returned byte sequences.

Every decoder must be bounded before allocation.

Every successful boundary publication must be atomic.

No failed or cancelled phase may expose a partially initialized successful
product.

### Testing strategy

Architecture tests should exercise forbidden authority as well as successful
flows.

Examples include:

- run semantic phases with no filesystem capability available;
- mutate a source file after request construction and prove the request remains
  unchanged;
- prove the VM cannot be constructed from a candidate artifact;
- corrupt one section after emission and require verifier rejection;
- request an undeclared host capability and require supervisor denial;
- issue equivalent `grand` and direct `grc` requests and compare semantic
  products;
- compare LSP diagnostics with command-line structured diagnostics;
- rebuild from a different checkout path and compare artifact bytes.

### Migration and completion

The first implementation step is to move host effects outward.

The second is to make compiler inputs explicit immutable records.

The third is to separate candidate, verified, and executable artifact types.

The fourth is to route `grand`, `grc`, LSP, formatter, docs, and tests through one
semantic library.

This design is complete when architectural review can answer, for every
function that crosses a major subsystem boundary:

- who calls it;
- who owns its inputs;
- what authority it receives;
- what fact it is allowed to establish;
- what validation it performs;
- what failure it returns;
- what product it may publish.

---

## 02. Compilation Inputs, Revisions, and Session Ownership

### Desired outcome

A request must see one coherent immutable compiler world from beginning to end.

A file edit, dependency replacement, standard-library update, target change, or
semantic option change creates a new world or a new projected request identity.

No query may combine headers from one revision with bodies from another.

No local numeric identity may become valid in a new revision merely because the
same integer was allocated again.

### Raw and normalized inputs

The host-facing request may begin as paths, flags, and package selections.

Before semantic work, it must become a canonical `NormalizedInputWorld` that
contains or references by validated digest:

- source bytes;
- stable logical file identities;
- package and module topology;
- dependency interfaces;
- standard-library source or interface data;
- trusted primitive and host-import manifests;
- target and layout policy;
- optimization and code-generation policy;
- language feature policy;
- lints and diagnostic policy;
- runtime capability declarations;
- structural resource limits;
- compiler and schema generations.

Absolute checkout paths must not participate in semantic identity.

### Source input model

A source record should contain at least:

```text
SourceInput {
    file: StableFileKey,
    package: PackageKey,
    logical_path: LogicalPath,
    bytes: SourceBlobRef,
    content_digest: Digest,
    encoding: SourceEncoding,
    provenance: SourceProvenance,
}
```

`SourceBlobRef` points into database-owned immutable storage.

The digest is checked when the host supplies bytes.

The compiler does not trust a host-provided digest without comparing it to the
actual bytes.

`SourceProvenance` may distinguish workspace source, dependency source,
standard-library source, editor overlay, generated test input, and bootstrap
bundle. Provenance supports diagnostics and policy but should not change
semantics unless explicitly specified.

### Package input model

A package input should record:

- stable package identity;
- project kind;
- root module or entry point;
- module-source mapping;
- selected features;
- direct dependency names and package keys;
- visibility boundary;
- runtime capability declaration;
- test and documentation roots;
- manifest fingerprint.

Package identity must not derive from an absolute host path.

Path dependencies use canonical logical dependency identity plus content
fingerprints.

Git dependencies include the resolved immutable revision.

### Dependency interface input

A dependency record includes:

```text
DependencyInput {
    package: PackageKey,
    identity: DependencyIdentity,
    interface_bytes: Bytes,
    interface_digest: Digest,
    producer: ProducerIdentity,
}
```

The interface is untrusted until decoded and validated.

The producer identity assists compatibility decisions but does not replace
schema and semantic validation.

A malformed interface blocks the importing package with a corruption or
compatibility diagnostic, not a misleading unresolved-name cascade.

### Standard-library input

The distinguished standard-library input includes:

- source or canonical interface bytes;
- package identity;
- language-generation compatibility;
- primitive-manifest generation;
- host-import manifest generation;
- stable declaration identities for trusted leaves;
- complete content fingerprint.

Changing the standard library may invalidate source semantics even when user
source is unchanged.

The standard-library fingerprint therefore participates in every query whose
meaning depends on prelude declarations, traits, effects, operators, or trusted
primitives.

### Target and policy inputs

Target policy should be a typed record rather than an open bag of strings.

It may include:

- bytecode generation;
- integer and pointer representation rules;
- endianness where relevant to external artifacts;
- supported instruction features;
- verifier feature set;
- VM feature set;
- optimization level;
- debug/source-map policy;
- artifact compatibility policy.

Lint and diagnostic presentation should be separate from semantic legality where
possible.

Runtime capability policy affects host-import legality and artifact manifests,
but not lexing or most type inference.

### Fingerprint projections

One monolithic request hash would be correct but too broad.

The normalized world should expose explicit projections such as:

```text
SourceSemanticFingerprint
InterfaceFingerprint
TargetLayoutFingerprint
OptimizationFingerprint
ArtifactFingerprint
RuntimeAuthorityFingerprint
PresentationFingerprint
BootstrapWorldFingerprint
```

Every query declares which projection or input leaves it reads.

A terminal-color option should not invalidate Typed Core.

A target pointer-width change should not invalidate lexing.

A primitive-manifest change may invalidate lowering even when source bytes are
unchanged.

Projection definitions are normative. Omitting a true dependency is a
correctness defect. Including an irrelevant dependency is an incremental
performance defect.

### Revision records

`CompilerDatabase` should own immutable `RevisionRecord` values.

A revision contains:

- normalized input identity;
- source-blob references;
- validated dependency references;
- a parent revision when available;
- a verified change summary;
- generation-tagged stable-key tables;
- pin and retirement state;
- query-cache namespace information.

The change summary is an acceleration and explanation aid.

It is never trusted as the sole source of semantic invalidation.

### Revision keys

A `RevisionKey` should include a database generation and an index or stable
content key.

A stale key must fail closed after database reset, compaction, or incompatible
schema change.

Two revisions may refer to the same source blobs and validated interfaces when
content identity matches.

A revision can be an alias of another normalized world when all semantically
relevant inputs are identical, but that aliasing decision must be based on the
complete normalized identity, not timestamps or host hints.

### Snapshot and request ownership

A `DatabaseSnapshot` pins exactly one revision.

A `RequestSession` owns:

- one snapshot;
- cancellation state;
- a hierarchical work budget;
- diagnostic staging;
- demanded root queries;
- temporary publication records;
- request-local statistics;
- host-facing presentation options.

A `PackageSession` narrows work to one package.

A `BodySession` owns transient parsing, resolution, inference, Core, and lowering
scratch for one demanded body.

An `EmissionSession` owns canonical pools, relocation scratch, and artifact
publication staging.

### Body lifetime

The normal body pipeline is:

```text
recorded token range
  -> body parse arena
  -> local resolution
  -> inference and elaboration
  -> Typed Core builder
  -> PlaceFlow and MIR lowering
  -> validation
  -> immutable body products
  -> release transient body state
```

The compiler should not require a mutable whole-program body AST.

Generic definitions may retain compact canonical Core when downstream
specialization requires it.

That retention must be explicit, measured, and distinct from parser or inference
scratch.

### Package and request lifetime

A package session may retain:

- validated package outline;
- declaration index;
- public and private interfaces;
- name-resolution index;
- canonical semantic types;
- demanded body set;
- instance-discovery worklist;
- package-level diagnostics.

A request session may retain products from several packages but should release
package-local mutable work when no longer needed.

Immutable query products publish into database-owned memo storage according to
retention policy.

### Editor revisions

Unsaved text is a database-owned source blob in a new revision.

An atomic multi-file edit creates one revision containing every edit.

Old requests either finish against their pinned revision or observe
cancellation.

They may not publish diagnostics into the new document version.

Several recent revisions may be retained for low-latency editor requests.

Unpinned retired revisions become eviction candidates.

The LSP adapter maps editor document versions to revision keys explicitly.

### Transactional publication

A query or phase may build results in mutable scratch.

Publication occurs only after:

- structural validation;
- semantic validation where required;
- cancellation recheck;
- budget accounting;
- fingerprint construction;
- dependency-journal finalization;
- diagnostic normalization.

A failed publication releases its guards and exposes no completed result.

A completed child query may publish even when a parent is later cancelled if the
child’s key and dependencies make it independently valid.

### Resource accounting

Every retained allocation should have:

- an owner;
- a lifetime class;
- a retention reason;
- an approximate byte cost;
- an eviction policy;
- an inspector-visible attribution.

Self-compilation memory profiles should identify the largest live owners by
revision, package, query family, and body.

Arena high-water marks should be recorded for parser, elaborator, Core, MIR,
optimizer, verifier, and VM preparation.

### Failure and cleanup

Cancellation, resource limits, corruption, and invariant failure should unwind:

- revision pins;
- child budgets;
- arena checkpoints;
- diagnostic staging;
- temporary canonical pools;
- publication guards;
- output temp files owned by the host adapter.

Cleanup must not discard a successfully published immutable child product.

Cleanup must not leave a partially initialized memo slot.

### Testing strategy

Tests should cover:

- two live revisions with overlapping local ID values;
- editor overlays while disk source changes;
- atomic multi-file rename revisions;
- stale revision-key rejection;
- cancellation during parsing, solving, MIR, and emission;
- body scratch reclamation;
- revision retirement and eviction;
- identical normalized worlds from different checkout paths;
- source and dependency digest mismatch;
- projected fingerprint independence;
- bootstrap world manifest equality.

### Migration and completion

The current source bundle becomes an explicit source store.

Global compilation state becomes a database plus request-scoped contexts.

Body phases are moved behind a `BodySession` boundary.

Host output becomes a request outcome.

The design is complete when two revisions can remain live simultaneously,
answer independent queries, release body-local state, and retire without changing
outputs or confusing identities.

---

## 03. The Typed Query Engine

### Desired outcome

The compiler should be a typed semantic database in which a build, hover,
rename, documentation page, optimizer inspection, and bootstrap stage are all
root queries over the same facts.

The query engine should provide reuse and dependency tracking without becoming a
dynamic framework that hides types, ownership, or phase contracts.

### Query declaration

Every query family should declare:

- key type;
- value type;
- input durability;
- recovery policy;
- cycle policy;
- persistence policy;
- validation function;
- semantic fingerprint function;
- diagnostic fingerprint function;
- resource-budget class;
- human-readable name.

Conceptually:

```text
QuerySpec<K, V> {
    family,
    durability,
    recovery,
    cycle,
    persistence,
    execute,
    validate,
    fingerprint,
}
```

Glorious implementations remain ordinary typed functions.

### Query families

Representative source and semantic queries include:

```text
source_text(FileKey)
tokens(FileKey)
delimiter_map(FileKey)
module_outline(ModuleKey)
item_header(DefKey)
package_interface(PackageKey)
body_syntax(BodyKey)
resolved_body(BodyKey)
typed_core(BodyKey)
place_flow(BodyKey)
mir(BodyKey)
instance_mir(InstanceKey)
optimized_mir(InstanceKey, OptLevel)
emitted_function(InstanceKey, TargetKey)
linked_artifact(BuildKey)
verified_artifact(BuildKey)
```

Tooling queries include:

```text
definition_at(FilePosition)
type_at(FilePosition)
effects_at(FilePosition)
quantity_at(FilePosition)
borrow_state_at(FilePosition)
references_to(DefKey)
implementations_of(TraitKey)
control_plan(BodyKey)
why_recompiled(QueryKey)
```

Tooling queries should depend on semantic products rather than reproducing their
algorithms.

### Query result states

A query result should distinguish:

```text
Complete(V)
Rejected(DiagnosticSet)
Recovered(V, DiagnosticSet, RecoverySummary)
Cancelled
ResourceLimited(ResourceDiagnostic)
CorruptInput(CorruptionDiagnostic)
InvariantFailure(InvariantReport)
```

Release roots accept only complete results.

IDE queries may opt into recovered inputs.

Recovered status propagates and remains visible in tooling responses.

A query that cannot produce a meaningful recovered value should reject rather
than inventing a placeholder that downstream code mistakes for truth.

### Dependency recording

When a query reads an input leaf or demands another query, the engine records a
typed dependency edge automatically.

A query implementation should not maintain a hand-written invalidation list.

The dependency journal records:

- dependency query family;
- canonical key;
- observed value fingerprint;
- observed diagnostic fingerprint where relevant;
- dependency kind;
- optional explanation label.

Dependencies are finalized at publication.

Transient speculative reads that are rolled back should not become permanent
dependency edges unless they affected the published result or diagnostic.

### Query frame

An executing frame should contain:

```text
QueryFrame {
    request,
    revision,
    family,
    canonical_key,
    parent,
    dependency_journal,
    diagnostic_stage,
    cancellation,
    budget,
    scratch_owner,
    publication_guard,
}
```

The frame is not itself persistent.

It owns the mutable state needed to compute one result.

Nested demands create child frames or reuse completed memo records.

### Memoization state

A memo slot may be:

```text
Vacant
Executing(QueryFrameId)
Complete(MemoRecord<V>)
Rejected(RejectedRecord)
Recovered(RecoveredRecord<V>)
Retired
```

Executing frames are request-qualified.

Publication is atomic.

Cancellation cannot leave an `Executing` slot permanently poisoned.

Rejected results may be memoized when their diagnostics and dependencies are
stable. Resource-limited outcomes should usually remain request-specific because
a different limit may succeed.

### Incremental validation

On a new revision, a prior memo may be validated by checking its direct inputs
and dependency fingerprints.

A red dependency recomputes.

A dependency that recomputes to the same fingerprint may allow the parent to
remain green.

Semantic, source-map, diagnostic, and presentation fingerprints may be separate
so that a moved span invalidates editor output without forcing code generation.

Validation itself is a query operation with cancellation and work accounting.

A reused value must still satisfy its schema and in-memory invariants.

### Durability

Input leaves may have different expected change rates.

Examples:

- compiler build identity: process-stable;
- language generation: release-stable;
- dependency interface: package-revision stable;
- source file bytes: edit-revision stable;
- diagnostic presentation: request-local;
- cancellation token: never semantic.

Durability can accelerate validation but may not bypass actual dependency
identity.

### Cycle handling

Query families declare one of:

- acyclic;
- strongly connected component;
- monotone fixed point;
- tabled goal solving;
- coinductive assumption;
- explicitly forbidden cycle.

The engine detects cycles by typed query identity, not by string name.

A legal cycle enters the family’s solver.

An accidental architecture cycle produces an invariant report with the full
query chain.

A cycle policy must define:

- initial approximation;
- merge operation;
- convergence check;
- widening if any;
- iteration limit;
- diagnostic behavior;
- deterministic worklist order.

### Query effects versus explicit contexts

Glorious may express nested query demand through a narrow effect, conceptually:

```text
effect DemandQuery {
    demand<K, V>(spec: QuerySpec<K, V>, key: K) -> Analysis<V>
}
```

The engine handler records dependencies and executes or reuses the child.

This effect must not become a dynamic service locator.

The query family and key remain statically typed.

Hot local compiler state should remain explicit in body, lowering, and emission
contexts rather than hidden behind effects.

### Cancellation

Cancellation is checked:

- before starting expensive work;
- at bounded loop checkpoints;
- before recursive descent thresholds;
- before publication;
- before persistence.

Completed independent child queries may remain memoized.

The cancelled parent publishes nothing.

An obsolete editor request should be cancelled promptly without corrupting
shared interners or revision state.

### Resource accounting

Each query family declares a budget class.

Work may be charged in semantic units:

- tokens scanned;
- syntax nodes parsed;
- goals processed;
- fixed-point edges visited;
- MIR blocks transformed;
- bytes emitted.

Wall-clock time is observed for profiling but should not determine deterministic
optimization behavior.

### Observability

The engine should expose:

```text
query_trace(root)
query_graph(root)
why_recomputed(query)
why_green(query)
query_statistics(family)
query_memory(family)
query_budget_report(request)
```

Explanations should name semantic edges, not only numeric IDs.

Trace modes should be opt-in and bounded.

A trace should be replayable enough to identify request, revision, root, query
family, key, and dependency decisions without exposing unstable memory addresses.

### Persistence boundary

The query engine decides whether a product is eligible for persistence.

The cache adapter only stores and retrieves bytes.

A persistable query must provide:

- canonical key encoding;
- complete dependency identity;
- value schema;
- decoder and validator;
- stable fingerprint;
- recovery exclusion rule;
- size estimate.

Request-local, recovered, cancelled, or partially computed products are not
persisted.

### Concurrency direction

Generation 1 should favor deterministic single-threaded execution with a clean
future concurrency boundary.

A query’s immutable inputs and atomic publication make parallel scheduling
possible later, but self-hosting should not depend on threads.

Future parallel execution must preserve:

- deterministic final products;
- one execution owner per memo slot;
- cancellation safety;
- cycle-policy correctness;
- stable diagnostic ordering;
- bounded memory.

### Testing strategy

Tests should cover:

- repeated query reuse;
- equivalent root orders;
- dependency recording through nested demands;
- red-green validation;
- recomputation to equal fingerprint;
- legal SCC and fixed-point cycles;
- forbidden cycle reports;
- cancellation before and during execution;
- memo-slot cleanup after failure;
- recovered-value propagation;
- rejected-result reuse;
- persistence eligibility;
- explanation graph correctness;
- request-order independence.

### Migration and completion

The initial engine can be single-threaded.

It should first support input leaves, typed keys, memoization, dependency
journals, cancellation, and deterministic traces.

Red-green validation follows.

Persistent caching follows only after in-memory behavior is tested.

The engine is complete when equivalent root-query orders produce identical
facts and artifacts, every recomputation can be explained, and no recovered or
cancelled result can cross into a release root.

---

## 04. Stable Identity, Interning, and Typed Arenas

### Desired outcome

Stable identities should survive unrelated edits and process boundaries where
appropriate.

Local IDs should remain compact and cheap.

No raw local ID should escape the owner that gives it meaning.

Identity should support incremental reuse, tooling, diagnostics, caching, and
bootstrap reproducibility without making semantic correctness depend on fragile
source offsets.

### Identity classes

The compiler should distinguish:

1. content identities;
2. stable semantic identities;
3. revision-qualified identities;
4. local arena identities;
5. artifact-local identities;
6. runtime identities.

A content digest identifies exact canonical bytes.

A stable semantic identity names a package, module, or declaration across
compatible revisions.

A revision-qualified identity names a fact in one immutable world.

A local arena identity names an allocation within one owner.

An artifact-local identity names a canonical record within serialized output.

A runtime identity names a verified executable object according to the artifact
contract.

These categories must not be implicitly interchangeable.

### Stable key hierarchy

The persistent hierarchy should include:

```text
PackageKey
ModuleKey
StableFileKey
DefKey
BodyKey
AnonymousOwnerKey
InstanceKey
TrustedDeclKey
QueryFamilyKey
```

A package key derives from canonical dependency identity.

A module key derives from package identity and logical module path.

A named definition key derives from module, namespace, declaration kind, stable
name, and deterministic disambiguation.

A body key derives from its owning definition and body role.

An instance key derives from a stable generic definition plus canonical
substitutions.

### Named-definition identity

A declaration identity should preserve stability under unrelated edits.

For named declarations, inputs may include:

- owning module key;
- namespace;
- declaration kind;
- interned name;
- explicit overload or disambiguation data;
- stable parent definition;
- source-order tie-breaker only when unavoidable.

Duplicate declarations receive distinct deterministic identities so diagnostics
can reference both.

Changing a declaration from function to struct creates a new identity.

Moving a declaration across module boundaries creates a new identity unless an
explicit refactoring map is supplied for tooling purposes.

### Anonymous identity

Closures, handler clauses, anonymous callables, labels, and generated control
sites need stable anchors.

An anchor should use:

- owning stable definition;
- structural syntax path;
- local semantic role;
- nearby token fingerprint;
- deterministic collision ordinal.

Inserting one unrelated closure should not renumber every later closure.

Ambiguous rematching creates new identities rather than silently merging nodes.

The identity algorithm should support an edit mapping from the editor when a
rename or structured refactoring explicitly preserves identity.

### Typed local IDs

Local identities include:

```text
TokenId
ExprId
PatternId
InferenceVarId
LocalId
PlaceId
LoanId
CoreValueId
CoreComputationId
BlockId
OperationId
ControlSiteId
```

Each ID carries a phantom tag.

Where stale access is possible, it also carries an owner generation.

Checked indexing is the only public arena access path.

A `BlockId` cannot be used to index a `Local` arena.

A body-local `ExprId` cannot be persisted as a stable cross-revision identity.

### Interning

The database may intern:

- names;
- logical paths;
- fully resolved types;
- effect rows;
- const values;
- canonical trait goals;
- signatures;
- stable diagnostic symbols.

Terms containing inference variables remain body-local until zonked.

Spans never participate in semantic equality.

Interned values may carry stable fingerprints but are not automatically
immortal.

### Interner ownership

Interners are database-owned and segmented by compatibility generation where
needed.

An interner entry should be immutable after publication.

Large revision-specific values may use weak retention or reference-counted
segments if the language implementation can support them safely.

A simpler generation-1 alternative is append-only process lifetime with explicit
memory measurement and restart policy.

The design should choose deliberately rather than accidentally leaking all
semantic values forever.

### Arena substrate

The shared arena toolkit should provide:

```text
Id<Tag>
IdRange<Tag>
Arena<Tag, T>
ArenaMark<Tag>
range_since(mark)
checked_get(id)
borrow_range(range)
truncate_to(mark)
```

Parser transactions and speculative elaboration use marks plus cleanup-backed
rollback guards.

Arena marks are owner-specific.

A mark from one arena cannot truncate another.

Range construction uses start and completed end marks rather than repeated
manual integer subtraction and conversion.

### Borrowed views

Phase boundaries should expose semantic views rather than private packed storage.

Examples include:

```text
TokenView
DeclarationView
TypeSyntaxView
BodyExpressionView
ResolvedTargetView
CoreValueView
CoreComputationView
MirOperationView
```

Each view is exhaustive over the current representation.

Numeric tags remain private to storage or serialization modules.

A phase should not need a parallel family of `kind_code`, `primary_index`, and
payload accessors when one typed view can represent the same fact.

### Serialization

Persistent products freeze records in canonical dependency order.

Local IDs are remapped to artifact-local indices.

Decoders allocate fresh typed arenas and validate every edge.

Stable-key algorithms carry explicit schema generations.

A serialized record should never rely on in-memory pointer identity, hash-table
bucket order, or process allocation order.

### Stable remapping

When serializing a graph:

1. identify root records;
2. compute reachable records;
3. derive canonical semantic keys;
4. sort with stable tie-breakers;
5. assign artifact-local IDs;
6. remap every edge;
7. validate the frozen graph;
8. encode sections.

The same pattern can serve interfaces, caches, inspection snapshots, and
bytecode metadata.

### Identity diagnostics

An inspector should explain identity changes across revisions:

```text
preserved
moved within same owner
renamed with explicit edit mapping
replaced
split
merged rejected
ambiguous rematch
owner changed
```

This supports rename, reference maps, and incremental debugging.

Diagnostics should display stable names and source locations, not opaque numeric
keys, while machine output may include canonical key encodings.

### Testing strategy

Adversarial identity tests should cover:

- insertion before named declarations;
- reordering independent declarations;
- duplicate names;
- anonymous closure insertion;
- nested module moves;
- refactoring rename maps;
- stale-generation keys;
- hash collisions;
- cache decode remapping;
- arena truncation and stale local IDs;
- deterministic serialization under randomized allocation order.

### Migration and completion

Replace parallel raw integer spaces with typed wrappers.

Centralize ranges and arena marks.

Move stable identities out of allocation order.

Add identity-diff inspection.

The design is complete when serialized outputs and cache keys are independent of
local arena order and every cross-phase identity has one documented stability
contract.

---

# Volume II — Incrementality and Operational Safety

## 05. Dependency Tracking and Invalidation

### Desired outcome

A small edit should invalidate only the facts that semantically depend on that
edit.

When invalidation is broader than expected, the compiler should explain the
exact dependency chain.

Correctness comes first: no changed input may be hidden from a dependent query.
Precision comes second: irrelevant changes should not flush expensive products.

### Dependency categories

The engine should distinguish:

- direct-input dependency;
- source-text dependency;
- source-structure dependency;
- public-interface dependency;
- private-interface dependency;
- body dependency;
- trait candidate-set dependency;
- selected-implementation dependency;
- effect-declaration dependency;
- fixity dependency;
- target-layout dependency;
- optimization-summary dependency;
- capability-manifest dependency;
- diagnostic-presentation dependency.

Different categories support different fingerprint projections and explanation
language.

### Dependency edge model

A dependency edge should record:

```text
DependencyEdge {
    from: QueryKey,
    to: QueryOrInputKey,
    kind: DependencyKind,
    observed_value: Fingerprint,
    observed_diagnostics: OptionalFingerprint,
    explanation: OptionalStableLabel,
}
```

The edge is produced automatically by the query engine.

The semantic phase may attach an explanation label such as “selected trait
implementation,” “operator fixity,” or “public field layout.”

### Change-friendly phase products

Each frontend and semantic boundary should publish a change-friendly product:

```text
FileTextFingerprint
FileTokenFingerprint
DelimiterFingerprint
ModuleOutlineFingerprint
DefinitionHeaderFingerprint
PackageInterfaceFingerprint
BodySyntaxFingerprint
BodySemanticFingerprint
TypedCoreFingerprint
PlaceFlowFingerprint
MirFingerprint
SummaryFingerprint
EmittedFunctionFingerprint
```

A changed source file may preserve its token stream when only line endings in
trivia change under a normalized policy.

A changed token stream may preserve the module outline.

A changed private body may preserve its package interface.

A dependency implementation change may preserve every downstream source query.

### Red-green validation

A prior query is provisionally reusable when its stable key still exists.

The engine validates its direct dependencies.

If every observed dependency fingerprint is unchanged, the result is green.

If a dependency changed, the query recomputes.

If recomputation produces the same semantic fingerprint, downstream parents may
remain green.

A query may still need to refresh source maps or diagnostics even when its
semantic fingerprint remains equal.

### Input change sets

A `RevisionChangeSet` may identify:

- added, removed, and changed files;
- changed package manifests;
- changed dependency interfaces;
- changed target and policy inputs;
- stable-definition remapping information;
- editor-provided structured edit maps.

The change set accelerates candidate lookup.

It does not establish truth. The query engine still validates actual observed
fingerprints.

### Source invalidation

Editing one file initially invalidates its text leaf.

Lexing recomputes or incrementally updates.

If the token product is equal, parsing and semantics may remain green.

If the module outline changes, declaration and interface queries for that module
recompute.

Bodies not touched by outline changes may retain stable keys and validate
independently.

Source-map changes should invalidate diagnostics and editor mappings without
necessarily invalidating semantic code generation.

### Interface invalidation

A package interface should separate public and package-private projections.

A private body change that preserves signatures, trait/impl heads, effects,
fixities, layout-relevant public facts, and generic specialization inputs should
not invalidate downstream packages.

Changing an exported type or trait may invalidate only downstream queries that
observe that declaration.

The interface decoder should retain per-declaration fingerprints to avoid one
monolithic dependency edge where possible.

### Trait and effect invalidation

Trait selection depends not only on the selected implementation but on the
candidate universe that could affect coherence or ambiguity.

The solver should record dependencies on canonical candidate-set summaries.

Adding an unrelated implementation should not flush all goals.

Adding a potentially overlapping implementation must invalidate affected goals.

Associated types, GATs, supertraits, negative reasoning, and effect-associated
items need explicit dependency edges.

Effect-row normalization and operation lookup follow similar candidate-set
rules.

### Generic instance invalidation

An instance key depends on:

- stable generic definition;
- canonical substitutions;
- generic body fingerprint;
- selected trait/effect evidence summaries;
- target/layout policy;
- optimization policy.

Changing one generic body invalidates its discovered instances, not every
instance in the program.

A changed caller may alter reachability without altering the instance body.
Linking may change while the emitted function fragment remains reusable.

### Fixity invalidation

Fixity changes invalidate operator grouping for bodies that contain the affected
operator set.

The body parser should record a compact operator-name dependency summary.

Bodies without those operators remain green.

A fixity change may alter parsing and therefore every downstream body product for
affected bodies, even if the source token stream is unchanged.

### Capability invalidation

Changing the runtime capability manifest should invalidate:

- host-import legality queries;
- artifact linking;
- capability section emission;
- verification of capability declarations;
- final artifact and build manifest.

It should not invalidate ordinary parsing or type inference that does not depend
on host imports.

### Diagnostic invalidation

Diagnostics depend on semantic facts and source presentation.

A semantic fingerprint may remain equal while a span or logical path changes.

Diagnostic products should therefore record separate dependencies on source-map
and presentation inputs.

Changing lint levels may alter emitted diagnostics without altering Typed Core
or MIR.

### Explanation

`why_recompiled` should produce a chain such as:

```text
EmittedFunction(parse<u8>)
  because OptimizedMir(parse<u8>) changed
  because Mir(parse<u8>) changed
  because TypedCore(parse) changed
  because selected implementation changed
  because dependency interface added impl Parse for Bytes
```

Each edge includes old and new fingerprints and the first revision where the
change appeared.

A `why_green` explanation should also be possible:

```text
TypedCore(parse) reused
  body syntax unchanged
  referenced interfaces unchanged
  trait candidate summaries unchanged
  semantic options unchanged
```

### Broad invalidation budgets

The compiler should track invalidation breadth by query family.

A source edit report may show:

```text
files changed: 1
headers recomputed: 1
bodies parsed: 1
bodies elaborated: 1
MIR bodies rebuilt: 1
instances reoptimized: 3
functions re-emitted: 3
downstream packages invalidated: 0
```

Unexpectedly broad results become testable performance regressions.

### Testing and completion

Tests should perform one controlled edit at a time and assert:

- recomputed query set;
- retained green set;
- changed product fingerprints;
- diagnostic updates;
- artifact equality where expected;
- explanation-chain content;
- no dependence on host changed-file hints.

The design is complete when broad invalidation has a measurable budget and an
explanation, and incremental builds are observationally equivalent to cold
builds.

---

## 06. Caching, Persistence, Eviction, and Schema Evolution

### Desired outcome

The compiler should reuse expensive completed work across requests and process
runs without allowing cache contents to establish semantic truth.

A cold build and warm build must produce identical products.

Deleting every cache should affect only performance.

### Cache layers

The design should separate:

1. in-memory query memoization;
2. in-memory decoded-product retention;
3. persistent semantic query cache;
4. emitted-function fragment cache;
5. complete verified-artifact cache;
6. optional remote content-addressed transport.

Each layer has a different key, validator, trust model, and eviction policy.

### In-memory memoization

The typed query engine owns in-memory memoization.

Memo records include values, fingerprints, dependencies, diagnostics, revision
qualification, retained byte estimates, and last-use metadata.

Memoization may retain rejected complete results.

Recovered and request-limited results require stricter retention rules.

In-memory records are trusted only because they were produced and validated in
the current process, but stale-generation and owner checks still apply.

### Decoded-product retention

A persistent cache hit may decode into an immutable product arena.

The decoded value can be retained independently of the raw bytes.

The retention policy should weigh:

- decoded size;
- decode cost;
- recomputation cost;
- dependency fan-out;
- expected reuse;
- revision pinning.

Raw bytes may be discarded after validation when the content store can reload
them.

### Persistent cache key

A persistent key includes:

- query-family generation;
- value-schema generation;
- compiler semantic build identity;
- relevant input projection;
- canonical query key;
- target or optimization projection when relevant;
- standard-library and primitive-manifest identity;
- dependency product fingerprints.

The full key is encoded canonically and hashed.

A cache namespace may group compatible compiler builds, but compatibility must
be explicit rather than inferred from a version string prefix.

### Cache record

A record should contain:

```text
CacheHeader
CanonicalKeyDigest
DependencyDigestSet
ValueBytes
ValueFingerprint
DiagnosticFingerprint
ValidationSummary
Checksum
OptionalCompressionMetadata
```

The record is self-delimiting and length-bounded.

The header declares required features, schema, compression, and uncompressed
size before allocation.

### Persistable products

Good candidates include:

- canonical package interfaces;
- token streams when source bytes match exactly;
- body-syntax products with stable local remapping;
- zonked Typed Core;
- validated MIR;
- optimized MIR;
- interprocedural summaries;
- emitted function fragments;
- complete verified artifacts.

Inference scratch, temporary solver state, query frames, parser rollback state,
and request-local recovery products should not be persisted.

### Validation

On load, the compiler checks:

- checksum;
- schema generation;
- compiler compatibility;
- complete key match;
- size limits;
- index ranges;
- graph invariants;
- semantic product invariants appropriate to the layer.

Invalid records are ignored or quarantined.

They do not become source diagnostics.

A loaded MIR product should pass structural MIR validation.

A loaded emitted fragment should pass fragment schema and relocation validation.

A loaded verified artifact must prove compatibility with the current verifier
contract or be reverified.

### Artifact cache

A complete artifact cache key includes the complete canonical build manifest.

A hit may avoid semantic work only when every product identity and compatibility
constraint matches.

The safest generation-1 policy is to re-run independent artifact verification
unless the cached verifier result is itself a strongly keyed, validated product
of the same verifier generation.

The cache should distinguish “artifact bytes cached” from “artifact currently
accepted for execution.”

### Eviction

In-memory eviction should consider:

- retained bytes;
- recomputation cost;
- request recency;
- dependency fan-out;
- revision pinning;
- product layer;
- bootstrap criticality.

Eviction changes performance only.

It must never change output.

Pinned products cannot be evicted while borrowed.

Eviction should happen at safe points and produce optional memory traces.

### Persistent-store cleanup

Persistent cleanup may use:

- content-address reachability from recent manifests;
- total-size budgets;
- age and last-access hints;
- schema-generation pruning;
- explicit `grand clean --cache` policy.

Cleanup must tolerate races with readers through atomic file replacement or an
equivalent store transaction.

A missing record during a read becomes a miss.

### Schema evolution

Every persistent product has an explicit schema generation.

Compatible readers may support selected older generations.

Incompatible records become misses.

Migration tools may rewrite caches, but compiler correctness must never depend on
migration success.

Interface and artifact compatibility are distinct from cache compatibility.

A compiler may discard an old cache while still reading the old bytecode format.

### Compression

Compression is optional and must be bounded.

The header declares uncompressed size.

The decoder checks configured maximums before allocating.

Decompression bombs, malformed streams, and truncated records become cache
corruption, not process failure.

Compression settings do not participate in semantic fingerprints because they
change storage representation, not value meaning.

### Remote caches

A remote cache, if introduced, transports content-addressed records.

It remains outside the trust boundary.

TLS or signatures provide transport and provenance properties, not semantic
truth.

The compiler validates remote records exactly as local records.

Credentials belong to orchestration, not semantic phases.

### Observability

Cache inspection should report:

- lookup key family;
- hit, miss, incompatible, corrupt, or evicted status;
- bytes read and decoded;
- validation time;
- recomputation fallback;
- retained-memory effect;
- producing compiler identity;
- dependency digest summary.

`why_cache_miss` should identify the first incompatible key component.

### Testing and completion

Tests cover corruption, truncation, bit flips, huge lengths, wrong keys, old
schemas, cold/warm equality, random eviction, concurrent cleanup semantics,
remote-record distrust, and request-order independence.

The cache design is complete when disabling or deleting all caches cannot alter
successful output and every cache hit can be fully explained and validated.

---

## 07. Determinism and Reproducibility

### Desired outcome

Identical complete inputs must produce byte-identical externally visible
products regardless of host path, cache warmth, query order, map seed, arena
allocation order, or prior request history.

Determinism should be specified locally at each publication boundary rather than
achieved accidentally by avoiding efficient data structures.

### Deterministic products

The following products are canonical:

- normalized input world;
- dependency interface;
- structured diagnostic stream;
- query explanation output where promised stable;
- Typed Core and MIR inspection encodings;
- interprocedural summary encoding;
- emitted function fragments;
- `.grbc` artifacts;
- build manifests;
- bootstrap stage products.

Human progress logs may include elapsed time and remain noncanonical when
explicitly labeled observational.

### Internal freedom

Internal arenas need not allocate canonically.

Hash maps may be used.

Worklists may use efficient local representations.

Before publication, products are frozen through stable keys and deterministic
ordering.

This separation prevents global canonical allocation from becoming a pervasive
performance burden.

### Canonical key encoding

Every stable key used at a boundary should have one canonical byte encoding.

The encoding includes schema or identity generation where needed.

Variable-length integers use one minimal representation.

Strings use a defined Unicode and byte policy.

Map-like records serialize entries in canonical key order.

Optional values use explicit discriminants rather than sentinel integers that
could collide with future valid IDs.

### Canonical pools

Strings, constants, signatures, types, operand packs, capture plans, cleanup
plans, and section records should use one freeze-and-remap abstraction.

Construction order produces temporary IDs.

Freeze sorts by canonical semantic key.

Every reference is remapped.

Serialization then follows frozen order.

The pool reports duplicate semantic keys as deduplicated values, not ordering
ambiguities.

### Diagnostic ordering

Diagnostics should sort by:

1. stable source identity;
2. primary span;
3. diagnostic code;
4. owning definition;
5. stable tie-breaker.

Related labels preserve semantic order within the diagnostic.

Parallel or nested production must not change final order.

When two diagnostics are semantically identical, deduplication follows one
explicit policy.

### Source-map determinism

Source entries use logical paths and stable file keys.

Line and column tables derive from supplied bytes.

Absolute paths, temporary directories, usernames, and editor-internal IDs do not
enter artifact source maps.

Source-map record order follows stable source identity and span order.

### Query determinism

Equivalent root-query orders should produce identical memo values and products.

Queries may run or validate in different sequences, but publication uses
canonical values.

Dependency lists are sorted before persistence or explanation output.

Query statistics that depend on execution order are observational and excluded
from semantic fingerprints.

### Optimizer determinism

Pass order, worklist order, cost ties, clone naming, block layout, register
allocation, and canonicalization must have stable tie-breakers.

Optimization budgets count semantic work units rather than wall-clock time.

If two transformations have equal profitability, the choice uses stable block,
definition, and operation keys.

A pass must not iterate directly over nondeterministic map order when order can
affect the fixed point or output.

### Instance discovery determinism

Generic instances may be discovered from calls in different orders.

The compiler may allocate temporary instance IDs eagerly, but the published
instance set and emission order use canonical `InstanceKey` ordering.

Recursive discovery uses a deterministic worklist.

Duplicate demands coalesce by canonical key.

### Block and register determinism

MIR block IDs are local and need not be canonical during construction.

Before stable inspection or emission, block ordering follows explicit layout
rules with stable tie-breakers.

Register allocation uses deterministic traversal and tie-breaking.

Parallel-copy cycle temporaries receive stable names or positions derived from
the edge and cycle order.

### Path normalization

Absolute paths, temporary directories, usernames, and platform-separator details
must not enter artifacts or semantic fingerprints.

Logical paths use one normalized syntax.

Presentation may map logical paths back to host paths outside semantic hashes.

Case sensitivity follows the package/module contract, not the host filesystem’s
incidental behavior.

### Floating environment and host state

Compilation must not depend on locale, timezone, wall clock, process ID, random
seed, or host CPU feature detection unless explicitly supplied as a typed target
input.

Diagnostics use deterministic numeric and textual formatting.

Hash functions used for semantic fingerprints have a fixed algorithm and seed
per schema generation.

### Bootstrap convergence

Stage two and stage three use the same canonical source world and build manifest.

A mismatch is localized by comparing:

- package interfaces;
- demanded instance sets;
- body/Core fingerprints;
- MIR fingerprints;
- optimized MIR fingerprints;
- function fragments;
- artifact section digests.

Equivalent runtime behavior is not sufficient. Convergence requires byte
identity under the canonical manifest.

### Reproducibility manifest

A build manifest should record:

- compiler source/build identity;
- language, query, interface, bytecode, and verifier generations;
- source and dependency digests;
- standard-library and primitive-manifest digests;
- target and semantic options;
- optimization level;
- capability manifest;
- resource-limit policy where outcome-relevant;
- output artifact digest.

The manifest itself is canonically encoded.

### Testing and completion

Reproducibility tests randomize map seeds, request order, cache state, checkout
path, editor history, and permitted internal allocation order.

They compare interfaces, diagnostics, Core/MIR snapshots, function fragments,
artifacts, manifests, and bootstrap stages.

The design is complete when repeated builds produce identical bytes and every
remaining nondeterministic inspection product is explicitly labeled unstable or
observational.

---

## 08. Cancellation, Resource Limits, Corruption Handling, and Security

### Desired outcome

The compiler must remain responsive in an editor, bounded during self-hosting,
and safe when processing hostile source, interfaces, caches, and artifacts.

Cancellation, resource exhaustion, corruption, source rejection, and compiler
defects remain distinct.

No hostile input should cause unbounded recursion, unchecked allocation,
integer overflow, stale publication, or execution of unverified state.

### Cancellation tree

A request owns a root cancellation token.

Child queries borrow or derive child tokens.

Cancellation propagates downward.

A child cannot cancel an unrelated request.

Completed globally valid child results may publish before parent cancellation
when their contracts permit it.

The root request owns the final publication guard for diagnostics, interfaces,
and artifacts.

### Cancellation state

A token may be:

```text
Active
Cancelled(reason)
Completed
```

Cancellation reasons may include:

- obsolete editor revision;
- user interruption;
- parent request failure;
- resource supervisor request;
- process shutdown.

The reason is observational and does not enter semantic fingerprints.

### Checkpoints

Long-running algorithms check cancellation at deterministic work boundaries:

- token batches;
- declaration batches;
- parser recursion-depth transitions;
- solver worklist iterations;
- SCC iterations;
- MIR blocks;
- optimizer transformations;
- serialization sections;
- verifier function batches.

Checking on every scalar operation is unnecessary and expensive.

The maximum work between checkpoints should be bounded and measured.

### Publication after cancellation

A query checks cancellation immediately before publication.

If cancelled, it releases its publication guard and exposes no completed parent
result.

An already published independent child result remains valid.

Diagnostics staged by an obsolete editor request are discarded or tagged with
the old document version so the adapter cannot publish them to the new version.

Persistent cache writes occur only after cancellation recheck.

### Resource-budget hierarchy

The request carries limits for:

- source bytes;
- tokens;
- nesting;
- declarations;
- syntax nodes;
- inference variables;
- type depth;
- trait/effect goals;
- fixed-point iterations;
- monomorphizations;
- MIR entities;
- optimizer work;
- diagnostics;
- artifact size;
- retained memory.

Child budgets consume from parents.

A package or body may have a local sub-budget, but exhausting it also consumes or
reports against the request-level category.

### Semantic work units

Budgets should count deterministic semantic units:

- bytes and tokens processed;
- nodes allocated;
- goals dequeued;
- unification steps;
- CFG edges visited;
- MIR transformations attempted;
- emitted words;
- decoded records.

Wall-clock time and RSS remain supervisor and profiling measures, not deterministic
compiler-semantic budgets.

### Resource diagnostics

A limit failure identifies:

- limit kind;
- configured value;
- observed value;
- owning query or definition;
- source location when meaningful;
- work already completed;
- suggested remediation when safe.

It is not reported as an ordinary type error.

Examples include “trait solver goal limit exceeded while proving X” and “MIR
block limit exceeded while specializing Y,” rather than a generic “compilation
failed.”

### Recursion and stack safety

Recursive source structures should use explicit stacks or bounded recursion when
host stack depth could be attacker-controlled.

The lexer, parser, type normalizer, solver, pattern compiler, MIR traversal,
artifact decoder, and verifier all need explicit depth checks.

A depth limit failure is structured and deterministic.

Self-hosted Glorious code should prefer worklists and source-defined loops for
large traversals once optimization can fuse them.

### Integer and allocation safety

Every count, offset, range, and multiplication used for allocation is checked.

A decoder validates:

1. encoded count;
2. maximum allowed count;
3. element-width multiplication;
4. section bounds;
5. cumulative allocation budget;
6. index references.

No allocation occurs from an unvalidated hostile length.

The same principle applies to cache, interface, artifact, and runtime host-input
decoders.

### Corruption classes

Corruption should distinguish:

- dependency-interface corruption;
- cache-record corruption;
- artifact corruption;
- bootstrap-seed corruption;
- internal-memory invariant failure.

A corrupt dependency interface blocks imports.

A corrupt cache record becomes a miss or quarantine event.

A corrupt artifact fails verification.

A corrupt seed blocks bootstrap and release verification.

An internal invariant failure is a compiler defect and should preserve an
inspectable report.

### Defensive decoding

Every persisted format declares:

- magic and generation;
- required features;
- total length;
- section or record count;
- checksums where appropriate;
- maximum compatible sizes.

Unknown required features fail closed.

Unknown optional sections may be skipped only when the format explicitly permits
it and bounds are valid.

Duplicate sections, overlapping ranges, invalid UTF-8 where text is required,
and noncanonical encodings are rejected according to the format contract.

### Cache corruption policy

Cache corruption must not alter semantic output.

The compiler should:

1. detect corruption;
2. avoid publishing the record;
3. optionally quarantine or remove it through the cache adapter;
4. recompute when possible;
5. report an optional health event outside source diagnostics.

Repeated corruption may disable the cache namespace for the request.

### Interface corruption policy

A dependency interface is part of the requested package world, so silent
recomputation may not be possible without dependency source.

The compiler returns a precise compatibility or corruption diagnostic naming:

- dependency identity;
- interface generation;
- failing section or invariant;
- expected producer compatibility;
- remediation such as rebuilding the dependency.

It must not continue with partial imported facts.

### Artifact and verifier security

The verifier treats compiler-produced bytes as hostile.

It validates all section, type, signature, function, register, control-flow,
cleanup, label, handler, resumption, capture, and host-import relationships.

Verification uses its own bounded arenas and work budgets.

The VM receives only the frozen verified image.

A verifier failure from compiler output is both a build failure and a compiler
bug signal.

### Runtime supervision

The compiler’s structural limits do not replace runtime limits.

The supervisor enforces:

- memory limit;
- time or instruction limit;
- process isolation;
- host-call policy;
- output-size limits where appropriate;
- termination and cleanup.

The VM cannot expand its authority by issuing a differently spelled request.
Host adapters validate exact typed operations.

### Secret and path handling

Compiler manifests and diagnostics should avoid leaking absolute paths,
credentials, environment secrets, or cache tokens.

Orchestration owns credentials for dependency or remote-cache access.

Semantic inputs use logical paths.

Debug traces require explicit opt-in and redact sensitive host details by
default.

### Invariant failures

An invariant failure record should include:

- compiler build identity;
- query family and key;
- revision fingerprint;
- owning definition;
- phase;
- deterministic invariant code;
- bounded context snapshot;
- related product fingerprints;
- optional replay command.

It should not include unbounded memory dumps or secrets.

Invariant failures are not memoized as normal semantic rejections.

### Recovery boundaries

IDE recovery is allowed only in query families that define a recovered product.

Recovery must preserve:

- source ownership;
- stable error nodes;
- bounded node creation;
- explicit recovered status;
- no use as release evidence.

A resource-limit or corruption failure is not automatically recoverable by
inventing syntax or types.

### Testing strategy

Testing should include:

- cancellation at every publication boundary;
- cancellation inside every major worklist;
- nested-budget exhaustion;
- extreme token and nesting inputs;
- solver explosion corpora;
- monomorphization explosion corpora;
- huge and cyclic MIR inputs to validators;
- truncated and mutated interfaces;
- truncated and mutated cache records;
- hostile artifact sections and indices;
- decompression bombs;
- denied host capabilities;
- stale editor diagnostic publication attempts;
- invariant-report determinism;
- memory cleanup after failure.

### Migration and completion

The migration begins by introducing structured resource and cancellation outcomes
without changing semantic algorithms.

Next, recursive and allocating subsystems receive counters and checkpoints.

Persistent decoders receive shared bounded-reader infrastructure.

Publication guards are added to queries, interfaces, caches, and artifacts.

The design is complete when hostile inputs and obsolete requests can be stopped
without corrupting shared state, successful products remain deterministic, and
every failure is classified at the boundary that owns it.

---

# Current Expansion Frontier

This branch intentionally preserves the completed expanded pass through document
08 rather than pretending that documents 09–32 have already received equal
detail.

The remaining expansion order is:

1. documents 09–12: source model and frontend;
2. documents 13–16: static semantics;
3. documents 17–20: semantic core and ownership;
4. documents 21–24: MIR and optimization;
5. documents 25–28: emission and runtime;
6. documents 29–32: user experience, validation, and self-hosting.

For those documents, the current merged synopsis remains the active breadth-first
text. This draft should replace the merged compendium only after all 32 sections
have been expanded to comparable depth and reviewed for cross-volume
consistency.

The principal cross-document questions to reconcile during the next pass are:

- which identity is stable across revisions versus only within one product;
- which query products are complete, recovered, persistable, or evictable;
- where Type, Effect, Quantity, Region, Core, PlaceFlow, and MIR facts are
  authoritative;
- how trait and effect candidate dependencies are fingerprinted;
- which generic bodies cross dependency interfaces;
- how source-defined control specialization is explained and cached;
- which MIR facts the independent verifier rechecks;
- which products participate in stage-two/stage-three convergence;
- how memory ownership remains viable in Glorious without hidden garbage
  collection or ambient shared mutation.

The final large compendium should not merely be longer. Every added section must
make an implementation decision, identify an owner, define a boundary, state an
invariant, or expose an unresolved conflict.