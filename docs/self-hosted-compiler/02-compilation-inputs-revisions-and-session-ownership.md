# Self-Hosted Glorious Compiler — 02. Compilation Inputs, Revisions, and Session Ownership

Status: detailed snowflake design target. This document defines the intended
input, revision, snapshot, ownership, and lifetime model of the self-hosted
Glorious compiler. It is not a claim that every structure described here is
implemented today.

Parent design: [Snowflake Stage One: The Ideal Self-Hosted Glorious
Compiler](../self-hosted-compiler-snowflake-stage-one.md).

Previous document: [01. Architecture and Trust
Boundaries](01-architecture-and-trust-boundaries.md).

Related authoritative contracts:

- [language core specification](../../glorious-branded-environment-core-spec.md);
- [current compiler and VM architecture](../architecture.md);
- [self-hosted compiler migration architecture](../../self-host/ARCHITECTURE.md);
- [frontend design](../frontend-design.md);
- [MIR design](../mir-design.md);
- [G1 bytecode contract](../bytecode.md);
- [standard-library contract](../std-lib.md);
- [remaining implementation work](../remaining-work.md).

Where this document disagrees with the language or bytecode specifications,
those specifications win. Where it is more restrictive about immutable inputs,
revision isolation, state ownership, or transient lifetimes, this document
defines the target self-hosted architecture.

The repository currently uses **Grandiose** in existing component names and
documentation. This snowflake series uses **Glorious** as the language name.
Existing executable and artifact names remain `grand`, `grc`, `grvm`,
`.glorious`, and `.grbc`.

---

## 1. Purpose

The compiler cannot be queryable, incremental, reproducible, or safely
self-hosted unless it has a precise answer to four foundational questions:

1. What complete set of inputs determines a compiler result?
2. How is one immutable version of those inputs identified?
3. Which state may be shared between versions without mixing their meanings?
4. Which component owns every piece of compiler memory, and when is that memory
   released?

This document answers those questions.

The target compiler is a long-lived semantic service. It may serve a cold
command-line build, a sequence of incremental builds, hundreds of editor
queries, bootstrap stages, or inspection requests. In all of those modes, a
request must observe one coherent world. A source file may change while the
service remains alive, but no single request may see half of the old file graph
and half of the new one. A dependency interface may be replaced, but a query
must not combine the old trait table with the new exported signatures. A cache
entry may be reused, but only when its complete input identity matches the
request that consumes it.

The central rule is:

> **The host assembles a complete immutable input world; the compiler assigns
> that world a revision; every request pins one revision; and every mutable
> compiler object has one explicit owner and one bounded lifetime.**

This document deliberately stops before specifying the complete query scheduler,
red-green invalidation algorithm, persistent cache encoding, or stable-identity
scheme. Those are the subjects of documents 03 through 06. It defines the
contracts those mechanisms must obey.

## 2. Scope

This document covers:

- raw and normalized compiler inputs;
- build, language, interface, optimizer, and artifact identities;
- source blobs, logical paths, package topology, and dependency interfaces;
- standard-library and trusted primitive manifests;
- target, code-generation, lint, diagnostic, capability, and resource options;
- request normalization, validation, hashing, and provenance;
- immutable compiler revisions;
- database snapshots and revision pinning;
- editor overlays and multiple live document versions;
- the ownership hierarchy from `CompilerDatabase` to body-local scratch;
- process, database, revision, request, package, body, query, lowering, and
  emission lifetimes;
- publication and cancellation boundaries;
- memory retention and eviction responsibilities;
- failure classification at input and ownership boundaries;
- migration from the current compiler and self-host implementation.

This document does not fully define:

- how typed queries are registered or executed;
- how dependency edges are stored;
- how change propagation determines whether a result is green;
- how persistent query values are encoded;
- the algorithms of lexing, parsing, resolution, type checking, effect checking,
  quantitative use, borrow checking, MIR, optimization, emission, verification,
  or execution.

Those later mechanisms may refine the representations introduced here, but they
must preserve this document's revision and ownership invariants.

## 3. Design summary

The intended top-level ownership graph is:

```text
host client (`grand`, `grc`, LSP, tests, bootstrap driver)
    |
    | assembles immutable external inputs
    v
CompilationRequest
    |
    | normalize + validate + fingerprint
    v
NormalizedInputWorld
    |
    | intern or create
    v
CompilerDatabase
    |
    +-- SourceBlobStore                 process/database lifetime
    +-- validated interface store       process/database lifetime
    +-- interners and query caches       process/database lifetime
    +-- RevisionRecord[]                 database-owned immutable worlds
    |       |
    |       +-- source map
    |       +-- package graph
    |       +-- dependency inputs
    |       +-- standard-library input
    |       +-- target/options/limits
    |       +-- parent and change summary
    |
    +-- RequestSession(revision)         one command/editor request
            |
            +-- PackageSession           one demanded package
            |       |
            |       +-- BodySession      one demanded body
            |               |
            |               +-- parse/resolve/elaborate scratch
            |               +-- Typed Core builder
            |               +-- lowering/PlaceFlow scratch
            |
            +-- EmissionSession          one requested artifact
            +-- diagnostics, budgets, cancellation, publication staging
```

The architecture has no ambient mutable “current compilation.” Every operation
receives a database or session plus a revision-qualified key. No semantic key is
valid merely because it has the same numeric index as a key from another
revision.

The compiler may share immutable blobs, interned semantic values, and validated
query results between revisions. It may not share a result merely because the
same path, declaration ordinal, or arena index appears in both revisions.

## 4. Goals

### 4.1 Complete input accounting

Every fact that can affect source legality, diagnostics, generated code,
artifact bytes, verification expectations, or runtime capability declarations
must enter through a typed input field or a validated content reference.

The compiler must not consult:

- the current directory;
- unlisted environment variables;
- file modification times;
- arbitrary filesystem paths;
- network services;
- locale, wall-clock time, process ID, or random state;
- hidden host callbacks;
- mutable global command-line state.

### 4.2 Immutable request worlds

A compiler request observes one immutable world from start to finish. New source
text creates a new revision. Replacing a dependency interface creates a new
revision. Changing optimization level, target, standard library, lint policy, or
capability manifest creates a distinct request identity and, where relevant, a
distinct revision input.

### 4.3 Long-lived reuse without semantic mixing

The database should retain expensive immutable facts and memoized results across
requests. Reuse must be justified by fingerprints and dependency identity, not
by pointer equality or coincidental local IDs.

### 4.4 Explicit ownership and bounded retention

Every allocation belongs to one of a small number of lifetime classes.
Body-local syntax, inference variables, Core scratch, MIR editing scratch, and
emission scratch must not leak into database lifetime accidentally.

### 4.5 One-body-at-a-time viability

A complete release build must be implementable without retaining a mandatory
whole-program body AST or a whole-program collection of mutable body contexts.
Interfaces and compact summaries may remain resident; body syntax and
elaboration scratch should be reclaimable after each demanded body publishes its
result.

### 4.6 Editor coherence

The language server must be able to retain several recent immutable revisions,
select the exact document version for a request, cancel obsolete work, and
answer against editor overlays without reopening disk files.

### 4.7 Deterministic bootstrap

The same normalized input world must receive the same content identity and
produce the same externally visible products regardless of allocation order,
cache warmth, or request history.

### 4.8 Implementability in Glorious

The ownership model must fit Glorious itself. It should rely on:

- explicit owners;
- typed stable keys;
- append-only arenas where appropriate;
- immutable borrowed views;
- affine request/session tokens;
- cleanup-backed rollback;
- deterministic collections;
- structured effects only for genuinely nonlocal concerns.

It must not require garbage collection, arbitrary unsafe pointers, runtime
reflection, or general shared mutable reference counting.

## 5. Non-goals

This document does not require generation 1 to support:

- parallel query execution;
- distributed compiler sessions;
- a network-transparent database protocol;
- arbitrary long-lived borrowed pointers into mutable database storage;
- transparent filesystem watching inside the compiler core;
- automatic package discovery by semantic phases;
- incremental mutation of a syntax tree in place;
- retaining every historical editor revision indefinitely;
- replaying partially completed requests after process restart;
- sharing mutable body contexts between requests;
- allowing one request to change another request's inputs;
- using file timestamps as semantic evidence;
- making every compiler option part of every query key;
- serializing raw local arena IDs as persistent identities.

A later implementation may add safe parallelism or remote execution, but it
must preserve snapshot isolation and explicit ownership.

## 6. Terminology

### 6.1 External input

An external input is data assembled by a host client before entering the
semantic compiler. Examples include source bytes, package manifests, dependency
interfaces, compiler options, target descriptions, capability manifests, and
resource limits.

### 6.2 Input world

An input world is the complete normalized set of external inputs visible to one
compiler revision.

### 6.3 Revision

A revision is an immutable, database-owned record describing one input world.
It has a stable database-local key and a deterministic content fingerprint.

A revision is not merely a monotonically increasing number. The number may be
useful for ordering, but semantic equivalence comes from the normalized inputs
and fingerprints.

### 6.4 Snapshot

A snapshot is a request-scoped view that pins one revision and prevents the
request from observing later replacements. In the G1 single-threaded service, a
snapshot may be represented by an affine `RequestSession` holding a
`RevisionKey` and unique access to the mutable query engine. It need not be a
long-lived native pointer into revision memory.

### 6.5 Session

A session is a mutable owner for work with a bounded lifetime. This document
uses:

- database lifetime;
- revision lifetime;
- request lifetime;
- package lifetime;
- body lifetime;
- query-frame lifetime;
- lowering lifetime;
- emission lifetime.

### 6.6 Stable key

A stable key identifies a logical entity across queries and, where specified,
across revisions or processes. Stable-key construction is detailed in document
04.

### 6.7 Local ID

A local ID is a compact typed arena index valid only within its owning result or
session. Examples include `ExprId`, `LocalId`, `PlaceId`, and `BlockId`.

### 6.8 Published result

A published result is a complete value visible to later queries or returned to
the host. Scratch, provisional mutation, and partially serialized output are not
published results.

### 6.9 Provenance

Provenance records where an external input came from: workspace source, editor
overlay, vendored dependency, locked Git revision, generated host input, standard
library, cache record, or bootstrap seed. Provenance supports diagnostics and
supply-chain auditing but does not replace content validation.

## 7. Normative invariants

The following invariants apply to every implementation.

### Invariant 1: A request pins exactly one revision

Every semantic query executed for a request resolves direct inputs through one
`RevisionKey`. No operation may silently fall back to “latest revision.”

### Invariant 2: Revision inputs are immutable

After a `RevisionRecord` is published, its source blobs, package graph,
dependency interface identities, standard-library identity, target, semantic
options, and relevant limits never change.

### Invariant 3: Host paths are labels, not capabilities

A `logical_path` may affect module structure, privacy, diagnostics, or stable
identity. It does not authorize the compiler to reopen the path.

### Invariant 4: Content hashes are verified

When a request supplies bytes plus a digest, the compiler verifies the digest.
When it supplies a content-addressed reference, the receiving boundary verifies
that the returned bytes match the reference before importing them.

### Invariant 5: Local IDs never cross incompatible owners

A local ID carries or is statically tied to its owner type. It may not be used
with another body's arena, another revision's table, or another query result.

### Invariant 6: Completed immutable values may be shared; mutable contexts may
not

Source blobs, validated interfaces, interned semantic terms, frozen query
results, and canonical artifacts may be reused. Parser cursors, inference state,
MIR editors, diagnostic buffers, and emission builders remain uniquely owned.

### Invariant 7: Cancellation publishes no partial success

A cancelled request may leave completed, independently valid immutable subquery
results in memory only if the query engine has committed them atomically under
their own complete dependency identity. It may not publish a partial body,
interface, artifact, diagnostic batch, or persistent cache entry.

Document 03 defines the exact subquery commit rule. Request-level products are
always transactional.

### Invariant 8: Recovery status is explicit

Recovered editor syntax or provisional semantics cannot inhabit the same
“complete release-valid” state without a status tag and validation transition.

### Invariant 9: Retention is owned and measurable

Every retained object can be attributed to a database store, revision, query
cache, active request, or explicit persistent cache. Unattributed global
retention is an architectural defect.

### Invariant 10: Equivalent normalized worlds have equivalent fingerprints

Host discovery order, map iteration order, absolute checkout location, and
allocation order do not affect the normalized input-world digest.

## 8. Input taxonomy

Compiler inputs fall into six classes.

### 8.1 Build identity inputs

These identify the compiler and contracts interpreting all other inputs:

- compiler source or release identity;
- language generation;
- standard semantic manifest generation;
- query schema generation;
- dependency-interface schema generation;
- cache schema generation;
- MIR schema generation where persisted;
- bytecode generation;
- verifier contract generation;
- optimizer rule generation where not implied by compiler identity.

### 8.2 Source and package inputs

These define the package being compiled:

- package identity;
- package kind;
- package manifest fields relevant to semantics;
- module roots;
- logical source paths;
- immutable source bytes;
- source content hashes;
- workspace relationships;
- selected entry point;
- test roots and compile-fail roots where requested.

### 8.3 Dependency inputs

These define upstream semantic worlds:

- dependency package identity;
- exact resolved version or commit identity;
- canonical dependency interface bytes;
- interface content hash;
- required language/interface features;
- optional verified executable or library artifact reference;
- provenance and lockfile evidence.

### 8.4 Standard-library and trusted-manifest inputs

These define the distinguished source library and finite primitive boundary:

- standard-library source or interface bytes;
- standard-library content hash;
- trusted declaration identities;
- machine primitive identities;
- host-import leaf identities;
- machine type identities;
- standard effect and capability declarations;
- manifest generation.

### 8.5 Configuration inputs

These include:

- compilation mode;
- target triple and data layout;
- optimization level;
- code-generation features;
- language feature gates;
- lint levels;
- diagnostic presentation policy;
- capability manifest;
- deterministic build options;
- inspection requests.

### 8.6 Operational inputs

These bound work without supplying language meaning directly:

- cancellation token identity;
- token, declaration, type, solver, MIR, optimizer, artifact, and diagnostic
  limits;
- memory-retention policy;
- cache namespace and policy;
- request priority for an editor service;
- tracing and statistics selection.

Operational inputs must be classified carefully. Some affect only whether work
is attempted; some affect whether compilation succeeds; some affect diagnostics
or artifacts. The normalized request records all of them, while individual
query keys project only the relevant subset.

## 9. The external `CompilationRequest`

The host-facing request should be explicit and serializable. The following is
conceptual Glorious-shaped pseudocode, not frozen syntax.

```glorious
pub struct CompilationRequest {
    pub build: CompilerBuildIdentity,
    pub request: HostRequestIdentity,
    pub mode: CompilationMode,
    pub root: RootPackageInput,
    pub workspace: Vec<WorkspacePackageInput>,
    pub sources: Vec<SourceInput>,
    pub dependencies: Vec<DependencyInput>,
    pub standard_library: StandardLibraryInput,
    pub target: TargetInput,
    pub semantic: SemanticOptions,
    pub codegen: CodegenOptions,
    pub lints: LintOptions,
    pub diagnostics: DiagnosticOptions,
    pub runtime: CapabilityManifest,
    pub limits: CompilerLimits,
    pub cache: CachePolicy,
    pub provenance: RequestProvenance,
}
```

The request is owned by the host adapter until it is accepted. Acceptance moves
or copies its immutable byte payloads into compiler-owned stores and returns a
revision-qualified request handle.

### 9.1 `CompilerBuildIdentity`

```glorious
pub struct CompilerBuildIdentity {
    pub compiler: Digest,
    pub language_generation: u32,
    pub query_generation: u32,
    pub interface_generation: u32,
    pub cache_generation: u32,
    pub bytecode_generation: u32,
    pub verifier_generation: u32,
    pub primitive_manifest_generation: u32,
}
```

The compiler digest should identify the semantic and code-generation behavior
of the executable, not merely a marketing version. A release may map a version
to a digest, but the digest remains the exact identity used for reproducibility.

Development builds may derive it from the compiler source tree plus embedded
standard manifests. Bootstrap stages derive it from the canonical compiler
artifact or its source/build manifest as defined by document 32.

### 9.2 `HostRequestIdentity`

The host request identity is for tracing, cancellation, and response matching.
It is not a semantic fingerprint.

```glorious
pub struct HostRequestIdentity {
    pub client: ClientKey,
    pub sequence: u64,
    pub document_version: Option<u64>,
}
```

Wall-clock timestamps and random request IDs may appear in host logs, but they
must not enter semantic output or artifact fingerprints.

### 9.3 `CompilationMode`

```glorious
pub enum CompilationMode {
    Check,
    Build,
    Test(TestSelection),
    Inspect(InspectionSelection),
    Ide(IdeDepth),
    Bootstrap(BootstrapStage),
}
```

Mode chooses demanded roots and whether recovery is permitted. It must not
change the meaning of otherwise valid source.

For example:

- `Check` may stop before final emission;
- `Build` demands an artifact;
- `Test` demands selected test roots and verified execution metadata;
- `Inspect` demands intermediate facts;
- `Ide` permits explicitly recovered results;
- `Bootstrap` enables convergence manifests and stricter determinism checks.

### 9.4 `SourceInput`

```glorious
pub struct SourceInput {
    pub file: StableFileKey,
    pub package: PackageKey,
    pub logical_path: LogicalPath,
    pub module_hint: Option<ModulePath>,
    pub bytes: Bytes,
    pub digest: Digest,
    pub origin: SourceOrigin,
}
```

`SourceOrigin` may distinguish:

```glorious
pub enum SourceOrigin {
    Workspace,
    EditorOverlay { version: u64 },
    VendoredDependency,
    StandardLibrary,
    GeneratedHostInput { generator: String },
    BootstrapSource,
}
```

Origin never grants semantic privilege except where another explicit contract,
such as the trusted standard-library manifest, does so.

### 9.5 `RootPackageInput`

```glorious
pub struct RootPackageInput {
    pub package: PackageKey,
    pub name: String,
    pub version: PackageVersionIdentity,
    pub kind: PackageKind,
    pub roots: PackageRoots,
    pub manifest: SemanticPackageManifest,
}
```

The semantic compiler receives a normalized package manifest rather than raw
TOML. `grand` owns TOML parsing and workspace selection. The compiler validates
semantic consistency, such as duplicate roots or references to unknown supplied
files.

### 9.6 `WorkspacePackageInput`

A workspace request may include several local packages so the compiler can
produce interfaces or artifacts in dependency order without rediscovering the
workspace.

Each workspace package has:

- stable package identity;
- normalized semantic manifest;
- supplied source set;
- declared local dependency edges;
- requested products;
- provenance.

Workspace packages are not all forced into one semantic namespace. Each package
retains its own interface and visibility boundary.

### 9.7 `DependencyInput`

```glorious
pub struct DependencyInput {
    pub package: PackageKey,
    pub identity: DependencyIdentity,
    pub interface_bytes: Bytes,
    pub interface_digest: Digest,
    pub required_features: FeatureSet,
    pub artifact: Option<ArtifactReference>,
    pub origin: DependencyOrigin,
}
```

The compiler does not trust `identity` merely because it came from a lockfile.
It validates the interface bytes and verifies their digest. Package identity and
interface-declared identity must agree.

### 9.8 `StandardLibraryInput`

```glorious
pub struct StandardLibraryInput {
    pub package: PackageKey,
    pub interface_or_sources: StandardLibraryPayload,
    pub content_digest: Digest,
    pub trusted_manifest: TrustedRuntimeManifestInput,
    pub manifest_digest: Digest,
}
```

The standard library may be supplied as source during bootstrap or as a
canonical interface plus generic bodies in ordinary downstream builds. The
normalized semantic result must be equivalent.

Primitive authority is bound to exact trusted declaration identities after the
standard library is validated and indexed. Names alone never grant authority.

### 9.9 `TargetInput`

```glorious
pub struct TargetInput {
    pub target_key: TargetKey,
    pub triple: String,
    pub data_layout: String,
    pub pointer_width: u32,
    pub endian: Endianness,
    pub runtime_abi: RuntimeAbiIdentity,
    pub supported_features: FeatureSet,
}
```

For G1 bytecode, many source-semantic queries are target-independent. Layout,
code generation, host imports, native fragments, and final artifacts may depend
on the target. The input model keeps target data explicit so queries can project
it correctly.

### 9.10 `SemanticOptions`

Semantic options include only choices that can change source acceptance or
meaning:

- language feature gates;
- edition or generation mode, if introduced;
- coherence policy version;
- strictness flags explicitly defined by the language;
- standard prelude selection where supported;
- experimental semantic features.

The design should minimize semantic options. A language rule should not become a
hidden command-line toggle merely because implementation work is incomplete.

### 9.11 `CodegenOptions`

Code-generation options include:

- optimization level;
- optional optimization budget profile;
- debug/source-map detail;
- target-specific code-generation features;
- emission products;
- bytecode compression or section policy if deterministic;
- native backend selection when added;
- incremental function-fragment policy.

They may affect artifacts without affecting source acceptance.

### 9.12 `LintOptions`

Lint options are normalized into a deterministic map from stable lint code or
lint group to level:

```glorious
pub enum LintLevel { Allow, Warn, Deny }
```

A denied lint changes compilation success and therefore belongs to the relevant
request and diagnostic keys. Warning rendering policy does not necessarily
affect semantic Core or MIR.

### 9.13 `DiagnosticOptions`

Diagnostic options distinguish semantic diagnostic production from host
presentation. Relevant compiler inputs may include:

- maximum diagnostic count;
- inclusion of suggestions;
- explanation depth;
- source-context policy;
- whether recovered IDE diagnostics are requested;
- stable JSON schema generation.

Terminal color, pager selection, and output destination remain host concerns and
must not enter compiler semantic fingerprints.

### 9.14 `CapabilityManifest`

The capability manifest is an exact sorted set of runtime grants that may be
encoded into the artifact and checked against host imports.

```glorious
pub struct CapabilityManifest {
    pub grants: Vec<CapabilityGrant>,
    pub digest: Digest,
}
```

Duplicate, unknown, wildcard, malformed, or noncanonical grants are rejected.
The manifest is not permission for the compiler itself to perform those
operations.

### 9.15 `CompilerLimits`

Limits should be grouped by subsystem:

```glorious
pub struct CompilerLimits {
    pub source: SourceLimits,
    pub frontend: FrontendLimits,
    pub types: TypeLimits,
    pub solver: SolverLimits,
    pub ownership: OwnershipLimits,
    pub instances: InstanceLimits,
    pub mir: MirLimits,
    pub optimizer: OptimizerLimits,
    pub emission: EmissionLimits,
    pub diagnostics: DiagnosticLimits,
    pub retention: RetentionLimits,
}
```

Each limit has:

- a stable name;
- a numeric ceiling;
- an accounting unit;
- a structured failure code;
- a statement of whether exceeding it is a user resource diagnostic or an
  internal invariant failure.

Limits are part of reproducible request metadata. Later query and cache designs
may permit reuse under a new limit when a completed result records that its
observed cost is below both limits.

### 9.16 `CachePolicy`

Cache policy tells the compiler which optional stores it may consult or update.
It is not semantic authority.

```glorious
pub enum CachePolicy {
    Disabled,
    ReadOnly(CacheNamespace),
    ReadWrite(CacheNamespace),
    OfflineReadWrite(CacheNamespace),
}
```

A cache miss or invalid record always falls back to recomputation when permitted.
Document 06 defines persistence.

### 9.17 `RequestProvenance`

Provenance may record:

- workspace root identity with host paths redacted or normalized;
- lockfile digest;
- dependency source and exact revision;
- vendor directory digest;
- editor document versions;
- bootstrap seed identity;
- invocation class.

Provenance is emitted into manifests or diagnostics only through canonical,
privacy-aware fields. Absolute host paths must not affect semantic output.

## 10. Request normalization

The external request is not yet suitable as a semantic key. The compiler first
normalizes it into a canonical `NormalizedInputWorld`.

### 10.1 Normalization pipeline

The pipeline is:

```text
external CompilationRequest
    -> structural validation
    -> digest verification
    -> path normalization
    -> package graph validation
    -> source ownership validation
    -> dependency-interface decoding and validation
    -> standard-library manifest binding
    -> option normalization
    -> capability normalization
    -> deterministic sorting
    -> canonical fingerprint projection
    -> NormalizedInputWorld
```

No semantic query begins until the minimum input world required for that query
has passed normalization.

### 10.2 Structural validation

Structural validation rejects:

- duplicate stable file keys with different bytes;
- one file assigned to incompatible packages;
- unknown package references;
- duplicate package keys;
- package dependency cycles not permitted by the package model;
- missing declared roots;
- malformed logical paths;
- inconsistent package names or versions;
- duplicate dependency identities;
- standard-library identity collisions;
- unsupported required features;
- malformed target data;
- noncanonical capability grants;
- impossible or overflowing resource limits.

These are request or orchestration failures, not source diagnostics unless the
language contract explicitly places the error in source.

### 10.3 Digest verification

Every supplied byte payload is hashed before import. The implementation should
stream large payloads where possible and account hashing against explicit input
limits.

A digest mismatch reports:

- input class;
- logical identity;
- expected digest;
- observed digest;
- provenance without leaking unnecessary absolute paths.

The mismatched bytes are not interned as a valid content-addressed object.

### 10.4 Logical path normalization

Logical paths should use a platform-independent canonical representation:

- normalized separators;
- no empty components except the package root representation;
- no `.` or `..` traversal;
- valid Unicode or an explicitly defined byte-path policy;
- deterministic case policy independent of the host filesystem;
- no drive letters or host-specific roots in semantic identity.

Two host paths that map to the same logical path within a package are a request
conflict unless they supply identical content under an explicitly permitted
alias policy.

### 10.5 Deterministic collection order

The normalized world sorts or canonicalizes:

- packages by stable package key;
- files by package and logical path;
- dependency edges by package key;
- feature sets;
- capability grants;
- lint overrides;
- requested products;
- provenance entries that are externally emitted.

Internal hash maps may index these records after canonical order is established.

### 10.6 Option classification

Every option must be assigned to one or more projections:

| Projection | Examples |
|---|---|
| source semantics | language features, coherence generation |
| diagnostic semantics | deny lint, recovery depth, suggestion production |
| MIR/optimization | optimization level, optional work budget |
| emission | source-map detail, target features |
| runtime manifest | capability grants |
| operational only | request priority, tracing destination |

An option with no documented projection is not accepted into the target design.
This prevents accidental “global options” from invalidating the entire compiler
or, worse, influencing results without appearing in their dependencies.

## 11. `NormalizedInputWorld`

A normalized world is database-owned immutable data.

```glorious
pub struct NormalizedInputWorld {
    pub build: CompilerBuildIdentity,
    pub mode_class: ModeClass,
    pub packages: FrozenVec<NormalizedPackageInput>,
    pub files: FrozenVec<NormalizedSourceInput>,
    pub dependencies: FrozenVec<ValidatedDependencyInput>,
    pub standard_library: ValidatedStandardLibraryInput,
    pub target: TargetInput,
    pub semantic: SemanticOptions,
    pub codegen: CodegenOptions,
    pub lints: CanonicalLintOptions,
    pub diagnostics: CanonicalDiagnosticOptions,
    pub runtime: CanonicalCapabilityManifest,
    pub limits: CompilerLimits,
    pub provenance: CanonicalProvenance,
    pub fingerprint: InputWorldFingerprint,
}
```

`FrozenVec<T>` here means immutable after publication. It does not require a
specific standard-library type name.

### 11.1 Fingerprint families

The world should carry several related fingerprints rather than forcing every
query to depend on one monolithic digest:

```glorious
pub struct InputWorldFingerprint {
    pub complete: Digest,
    pub source_semantics: Digest,
    pub diagnostics: Digest,
    pub target_codegen: Digest,
    pub runtime_manifest: Digest,
    pub provenance_manifest: Digest,
}
```

The complete digest identifies the exact normalized request world. Projected
digests support narrow query dependencies. Their construction must be
schema-versioned and canonical.

### 11.2 Mode-class normalization

Modes that demand different products but share source semantics should not
produce different source-semantic fingerprints. `Check` and `Build` may share
frontend and semantic results while differing in requested roots and emission.

The world records both:

- semantic input identity;
- request demand identity.

This prevents the command name from invalidating reusable facts.

## 12. Database-owned input stores

`CompilerDatabase` should deduplicate large immutable values before creating a
revision.

### 12.1 Source blob store

```glorious
struct SourceBlobStore {
    blobs: Vec<SourceBlob>,
    by_digest: MultiMap<Digest, SourceBlobId>,
}

struct SourceBlob {
    digest: Digest,
    bytes: Bytes,
    line_index: OnceCell<LineIndex>,
}
```

`OnceCell` is conceptual. In Glorious it may be represented by an explicitly
owned slot whose initialization is controlled by the database. The resulting
line index is immutable.

Digest collision handling compares bytes before deduplicating. A cryptographic
digest narrows lookup; it does not replace equality when importing untrusted
bytes.

### 12.2 Logical file records

A revision maps stable file identities to source blob IDs plus logical metadata:

```glorious
struct RevisionFile {
    file: StableFileKey,
    package: PackageKey,
    logical_path: LogicalPath,
    module_hint: Option<ModulePath>,
    blob: SourceBlobId,
    origin: SourceOrigin,
}
```

The same source blob may appear under two logical file identities without
making those files semantically identical. Path and package affect modules,
privacy, diagnostics, and stable definitions.

### 12.3 Validated dependency store

Validated interface blobs may be deduplicated by interface digest and schema.
The store retains:

- original canonical bytes where needed for manifest reproduction;
- validated typed interface tables;
- package identity;
- required feature set;
- validation result and schema;
- content digest.

A revision references a validated interface ID, not raw host bytes.

### 12.4 Trusted manifest store

Trusted runtime manifests are validated, canonicalized, and interned separately
from ordinary dependency interfaces. The manifest record binds primitive roles
to exact declarations in one standard-library identity.

### 12.5 Target store

Canonical target records may be interned by target key and complete data-layout
digest. A familiar target name is not enough; two records with the same name but
different layouts are incompatible inputs.

## 13. Revision model

### 13.1 Revision key

A database-local revision key should detect stale reuse:

```glorious
pub struct RevisionKey {
    index: u32,
    generation: u32,
}
```

If revision slots are ever recycled, the generation changes. If slots remain
append-only until database shutdown, generation may remain zero in G1, but the
typed structure still prevents confusion with other key spaces.

### 13.2 Revision record

```glorious
struct RevisionRecord {
    key: RevisionKey,
    sequence: u64,
    world: NormalizedInputWorldId,
    parent: Option<RevisionKey>,
    changes: RevisionChangeSet,
    pin_count: u32,
    state: RevisionState,
    created_by: RevisionOrigin,
}
```

`sequence` orders revisions within one database for tracing and retention. It is
not part of semantic fingerprints.

### 13.3 Revision state

```glorious
pub enum RevisionState {
    Building,
    Published,
    Retired,
    Quarantined,
}
```

- `Building` is visible only to the normalization transaction.
- `Published` may be pinned by requests.
- `Retired` remains valid for active pins but is no longer selected by a host
  document version or workspace head.
- `Quarantined` records an internal validation defect and is never used for new
  requests.

A revision becomes `Published` only after its normalized world, indexes, and
parent/change metadata are complete.

### 13.4 Revision content identity

Two revision records may point to the same normalized input world. The database
may either return the existing revision or create a new sequence record for
host-version tracking. The policy should preserve:

- semantic deduplication;
- exact editor-version response matching;
- understandable tracing.

A recommended G1 policy is:

- reuse the same `NormalizedInputWorldId` whenever the complete fingerprint and
  validated contents match;
- create a distinct lightweight revision alias only when the host needs a new
  request/document sequence identity;
- allow semantic queries to depend on the shared world identity.

### 13.5 Parent revisions

A parent edge is an optimization and explanation aid, not proof of equivalence.
The parent records the world from which a host edit or incremental build was
derived.

A revision may have no parent when:

- it is the first request;
- it was restored from a manifest without prior in-memory state;
- the host cannot identify a coherent predecessor;
- the proposed parent belongs to an incompatible build identity.

### 13.6 Change set

```glorious
struct RevisionChangeSet {
    files_added: Vec<StableFileKey>,
    files_removed: Vec<StableFileKey>,
    files_changed: Vec<StableFileKey>,
    packages_changed: Vec<PackageKey>,
    dependencies_changed: Vec<PackageKey>,
    standard_library_changed: Bool,
    semantic_options_changed: Bool,
    target_changed: Bool,
    codegen_changed: Bool,
    lints_changed: Bool,
    capabilities_changed: Bool,
    limits_changed: Bool,
}
```

The compiler verifies the change set against parent and child worlds. Host-
supplied change hints may accelerate comparison but are never trusted without
verification.

## 14. Snapshot and request model

### 14.1 `DatabaseSnapshot`

A snapshot is the immutable semantic view of a revision:

```glorious
pub struct DatabaseSnapshot {
    revision: RevisionKey,
    world: NormalizedInputWorldId,
    build: CompilerBuildIdentity,
}
```

In G1, the public snapshot may be a small copyable descriptor used only while an
affine `RequestSession` owns access to the database. It does not expose raw
references into vectors that may reallocate.

### 14.2 `RequestSession`

```glorious
pub struct RequestSession<'db> {
    database: &'db mut CompilerDatabase,
    snapshot: DatabaseSnapshot,
    request: HostRequestIdentity,
    demand: RequestDemand,
    cancellation: CancellationState,
    budget: RequestBudget,
    diagnostics: DiagnosticAccumulator,
    publication: PublicationTransaction,
    trace: RequestTrace,
}
```

The request session is affine or linear: it must finish, cancel, or abort exactly
once. Its cleanup releases the revision pin and discards unpublished staging
state.

A request session uniquely borrows the mutable database in the initial
single-threaded implementation. This makes query-cache mutation and revision
pinning straightforward without general shared mutable reference counting.

Future parallel execution may split immutable stores from synchronized query
state, but the external snapshot contract remains unchanged.

### 14.3 Opening a request

Opening a request performs:

1. validate the requested revision key and generation;
2. ensure the revision is `Published` or validly `Retired` with an explicit pin;
3. increment or acquire its pin lease;
4. allocate request budgets and cancellation state;
5. construct the demand root set;
6. begin a publication transaction;
7. return the affine session.

Failure before step 3 publishes no session. Failure after step 3 unwinds through
cleanup and releases the pin.

### 14.4 Closing a request

A successful close:

1. verifies all requested products reached a complete allowed state;
2. canonicalizes and sorts returned diagnostics;
3. finalizes manifests and artifacts where requested;
4. atomically publishes request-level products;
5. records statistics and invalidation explanations;
6. releases the revision pin;
7. returns `CompilationOutcome`.

A cancelled or failed close:

- discards request-level staged products;
- retains only independently committed immutable query results allowed by
  document 03;
- records failure classification;
- releases the revision pin.

## 15. Revision selection by client type

### 15.1 Cold command-line build

`grand` assembles a complete request. The compiler normalizes it, interns or
creates a revision, opens one request session, executes demanded roots, returns
an outcome, and may retire the revision after the command if no long-lived
service is active.

### 15.2 Incremental command-line service

A resident compiler process accepts successive complete worlds or validated
world deltas. Each accepted world becomes a new revision with the previous
workspace head as parent. Old revisions remain until unpinned and evictable.

### 15.3 Language server

The LSP adapter tracks editor document versions. For each accepted edit batch it
assembles a new complete logical source world by combining:

- immutable workspace inputs;
- the latest accepted editor overlays;
- unchanged dependency interfaces;
- current compiler configuration.

It submits that world and associates the resulting revision with the editor
version vector. A request for version `N` pins the exact associated revision.
A request whose version has already been retired receives a structured stale-
request response or is recomputed from a retained normalized world if policy
allows.

### 15.4 Bootstrap driver

Each bootstrap stage uses a canonical immutable world containing:

- exact compiler source bundle;
- exact standard-library source;
- bootstrap target;
- fixed optimization level;
- fixed capabilities;
- fixed limits;
- exact stage producer identity;
- convergence manifest.

Stage identity changes build identity but not the normalized source world.
Stage-two and stage-three outputs are compared under the exact same semantic and
code-generation inputs.

## 16. Editor overlays

### 16.1 Overlay assembly belongs to the host

The compiler core never asks “is this file open in the editor?” The LSP adapter
or compiler-service host supplies the final `SourceInput` bytes and marks their
origin as an editor overlay.

### 16.2 Overlay precedence

A host may define precedence:

```text
editor overlay > generated in-memory input > workspace disk snapshot
```

The compiler receives only the resolved result plus provenance. It does not
merge bytes from competing sources.

### 16.3 Multi-file atomicity

An editor operation that changes several files, such as rename, should create
one new revision containing all accepted edits. Intermediate per-file states may
exist as host buffers but should not become semantic revisions unless the editor
actually requests analysis for them.

### 16.4 Unsaved files

Unsaved source is ordinary immutable source input with `EditorOverlay` origin.
It participates in module discovery, privacy, fingerprints, diagnostics, and
queries exactly like saved source.

### 16.5 Broken source

A revision may contain malformed source. The revision itself is still a valid
input world. Queries return source diagnostics or explicitly recovered results.
“Invalid source” does not make the revision mutable or corrupt.

## 17. Package and source ownership

### 17.1 One owning package per source file

Every semantic source file belongs to exactly one package in a normalized world.
A shared physical file used by two packages must appear as two logical source
identities or through an explicit generated/interface mechanism.

### 17.2 Module identity

Module identity derives from:

- package identity;
- normalized logical path;
- package root rules;
- inline module structure.

It does not derive from absolute host paths or source blob identity alone.

### 17.3 Privacy identity

Private-field and private-item authority depends on the source entry or module
identity defined by the language specification. The revision stores enough
logical metadata to reproduce that identity deterministically.

Moving identical bytes to another logical module may therefore change semantic
results even though the source blob digest is unchanged.

### 17.4 Generated source

Generated source must include:

- stable logical identity;
- generator identity;
- generated bytes and digest;
- declared owning package;
- provenance.

The semantic compiler does not invoke the generator. `grand` or another host
component runs it before constructing the request. Generation must be
reproducible if its output enters a reproducible build.

## 18. Dependency-interface ownership

### 18.1 Raw versus validated dependency inputs

Raw dependency bytes live only in request normalization or the immutable blob
store. Semantic queries consume a `ValidatedDependencyInterfaceId`.

```glorious
struct ValidatedDependencyInput {
    package: PackageKey,
    identity: DependencyIdentity,
    interface: ValidatedDependencyInterfaceId,
    digest: Digest,
    features: FeatureSet,
    artifact: Option<ArtifactReference>,
}
```

### 18.2 Interface lifetime

A validated interface may outlive the revision that first imported it. It is
immutable and content-addressed. Revisions refer to it by database-owned ID.

### 18.3 Cross-revision sharing

Two revisions may share a validated interface only when:

- canonical bytes match;
- schema and compiler-generation compatibility match;
- package identity matches;
- required features are supported;
- validation completed successfully.

### 18.4 Generic bodies

If dependency interfaces contain generic Typed Core or another specialization
payload, that payload is owned by the validated interface record. A
monomorphized body session borrows or imports an immutable view and publishes a
new instance result into the current database's query store.

The payload must not expose producer-local raw arena IDs without a canonical
remapping contract.

## 19. Standard-library ownership and primitive authority

The standard library is simultaneously:

- ordinary Glorious source or interface input;
- a distinguished package identity;
- the producer of conventional control and operators;
- the owner of declarations bound by the finite trusted runtime manifest.

These roles must remain separate in representation.

### 19.1 Validated standard-library record

```glorious
struct ValidatedStandardLibraryInput {
    package: PackageKey,
    interface: ValidatedDependencyInterfaceId,
    content_digest: Digest,
    runtime_manifest: TrustedRuntimeManifestId,
    manifest_digest: Digest,
}
```

### 19.2 Manifest binding

Binding performs:

1. validate the standard-library package and interface;
2. resolve manifest declaration selectors against exact canonical identities;
3. check each expected primitive/host leaf signature;
4. reject missing, duplicate, ambiguous, or incompatible leaves;
5. freeze a finite authority table;
6. include its digest in relevant worlds and artifacts.

A same-spelled user declaration outside that identity has no primitive
authority.

### 19.3 Bootstrap source mode

When compiling the standard library from source, the stage-zero or prior-stage
compiler constructs the canonical interface before dependent bodies request its
facts. The resulting interface must match the ordinary downstream contract.

## 20. Ownership hierarchy

The target implementation should make ownership visible in module and type
structure.

### 20.1 `CompilerDatabase` ownership

Database lifetime owns:

- source blobs;
- validated dependency interfaces;
- validated trusted manifests;
- target records;
- interned names and canonical semantic terms;
- revision records;
- query result storage;
- dependency graph storage;
- persistent cache adapters;
- global statistics;
- eviction indexes.

It does not own active parser cursors, body inference states, MIR editors, or
artifact builders except through an active request/session stack.

### 20.2 `RevisionRecord` ownership

Revision lifetime owns or references immutable:

- normalized package graph;
- logical file mapping;
- validated dependency IDs;
- standard-library ID;
- target and option projections;
- input fingerprints;
- parent/change metadata;
- host version aliases;
- pin and retention metadata.

It does not own mutable semantic phase state.

### 20.3 `RequestSession` ownership

Request lifetime owns:

- snapshot/revision pin;
- cancellation state;
- request budget and accounting;
- demand roots;
- diagnostic accumulator;
- publication transaction;
- active query stack;
- request-local scratch pools;
- trace and explanation selection;
- package-session registry for the request.

### 20.4 `PackageSession` ownership

Package lifetime owns:

- package-scoped demand worklist;
- root selection;
- package interface publication staging;
- reachable-instance discovery staging;
- package diagnostic context;
- package-level resource counters;
- package-local deterministic ordering indexes.

It borrows immutable package inputs and database services through the request.
It should not duplicate global interners or source blobs.

### 20.5 `BodySession` ownership

Body lifetime owns:

- transient body syntax where not served from an immutable query result;
- body-local resolution tables;
- lexical scope stacks;
- inference variables;
- expected-type constraints;
- local trait/effect/quantity goals;
- temporary semantic terms not yet internable;
- capture and environment construction state;
- Typed Core builder and scratch;
- body diagnostics before normalization;
- lowering handoff state.

After a complete body result is published, this mutable session is destroyed.
Any retained syntax, Core, MIR, source map, or summary is an immutable published
query product, not the old mutable session.

### 20.6 `LoweringContext` ownership

Lowering lifetime owns:

- current Typed Core body view;
- MIR builder;
- local/place/block/move-path arenas;
- PlaceFlow construction state;
- cleanup and control-site staging;
- source-to-MIR mapping scratch;
- lowering diagnostics and invariant checks.

It either publishes a validated immutable MIR/PlaceFlow product or publishes
nothing.

### 20.7 `EmissionSession` ownership

Emission lifetime owns:

- selected reachable instances;
- physical register assignment scratch;
- block layout scratch;
- canonical-pool builders;
- relocation/patch tables;
- emitted function fragments under construction;
- artifact section builders;
- build manifest staging;
- final verification request metadata.

The session publishes canonical bytes atomically. It does not become the owner
of the VM's frozen execution image.

### 20.8 Query-frame ownership

Each active query frame owns:

- typed query key;
- dependency recorder;
- cycle/fixed-point state appropriate to the query family;
- query-local budget;
- provisional value builder;
- publication guard;
- trace information.

Document 03 specifies how frames nest and commit.

## 21. Lifetime matrix

| Data | Database | Revision | Request | Package | Body | Query | Persistent |
|---|---:|---:|---:|---:|---:|---:|---:|
| source bytes | Yes | Ref | Ref | Ref | Ref | Ref | Optional blob |
| logical file map | Ref | Yes | Ref | Ref | Ref | Ref | Manifest only |
| validated dependency interface | Yes | Ref | Ref | Ref | Ref | Ref | Yes |
| canonical name/type interner | Yes | Ref | Ref | Ref | Ref | Ref | Optional canonical form |
| body parser cursor | No | No | No | No | Yes | Maybe | No |
| body syntax result | Cache | Ref/key | Ref | Ref | Builder | Yes | Optional |
| inference variables | No | No | No | No | Yes | Yes | No |
| Typed Core result | Cache | Ref/key | Ref | Ref | Builder | Yes | Optional |
| MIR/PlaceFlow result | Cache | Ref/key | Ref | Ref | Lowering builder | Yes | Optional |
| optimizer scratch | No | No | Request | Package | Instance | Query | No |
| optimized MIR result | Cache | Ref/key | Ref | Ref | No | Yes | Optional |
| diagnostic accumulator | No | No | Yes | View | Local buffer | Query buffer | Structured output |
| emitted artifact builder | No | No | Yes | Maybe | No | Query | No |
| final artifact bytes | Cache/output | Ref/key | Staged | Ref | No | Query | Yes |
| cancellation state | No | No | Yes | Borrow | Borrow | Borrow | No |
| resource counters | Global totals | Metadata | Yes | Child | Child | Child | Statistics only |

“Ref” means immutable reference by stable database key or scoped view, not raw
ownership transfer.

## 22. Glorious implementation discipline

### 22.1 Prefer stable handles over escaping borrows

The database may grow stores between requests. Long-lived objects should refer
to database-owned records through typed handles rather than retaining native-
style pointers into vectors that might move.

Within one short operation, a handle may be resolved to an immutable borrow.
The borrow must not escape the operation or survive mutation that can relocate
its owner.

### 22.2 Affine session guards

`RequestSession`, `PackageSession`, body publication guards, parser checkpoints,
and artifact transactions are natural affine values. They should require an
explicit successful commit or perform cleanup on destruction.

Conceptually:

```glorious
struct PublicationGuard<T> {
    private state: PublicationState<T>,
}

commit<T>(guard: PublicationGuard<T>, value: T) -> Published<T> { ... }
```

An uncommitted guard contributes zero-use cleanup that discards staging and
restores indexes. The guard itself must be permitted to clean up under the
language's `Use` rules.

### 22.3 No general shared mutable ownership

G1 should not require `Arc<Mutex<T>>`-style architecture. A single request
uniquely owns mutable database access while immutable records are referenced by
keys. The service scheduler serializes requests or explicit work slices.

This matches the current no-threads G1 boundary and makes determinism easier.

### 22.4 Explicit child budgets

A request budget should issue child budget leases to package, body, query,
solver, MIR, and optimizer work. Leases report consumption back on completion or
cleanup.

The budget mechanism should not use ambient global counters that cannot be
attributed to a request.

### 22.5 Private fields protect invariants

Session internals, revision state transitions, and database stores should use
private fields. External compiler modules receive typed views and methods rather
than direct mutation authority.

### 22.6 Effects for nonlocal concerns only

Good candidates for internal effects include:

- `Report<CompilerDiagnostic>`;
- cancellation checks;
- query demand/lookup;
- terminal phase abort;
- tracing hooks where statically erased or handled.

Ordinary hot state—cursor position, arenas, inference tables, MIR blocks—should
remain explicit in context structs.

## 23. Request demand model

A normalized input world says what exists. A request demand says what products
are required.

```glorious
pub struct RequestDemand {
    pub roots: Vec<DemandRoot>,
    pub products: ProductSet,
    pub depth: AnalysisDepth,
    pub recovery: RecoveryPolicy,
    pub inspection: InspectionSelection,
}
```

### 23.1 Demand roots

Demand roots may include:

- package entry point;
- exported package interface;
- selected tests;
- one declaration;
- one source position;
- one generic instance;
- all workspace members;
- compiler bootstrap entry;
- artifact verification.

### 23.2 Analysis depth

```glorious
pub enum AnalysisDepth {
    Lex,
    Structure,
    Resolve,
    Check,
    Lower,
    Optimize,
    Emit,
    Verify,
}
```

Depth controls which query roots are demanded. It does not define parallel
partial semantics.

### 23.3 Recovery policy

```glorious
pub enum RecoveryPolicy {
    None,
    SyntaxOnly,
    SemanticForIde,
}
```

Release build and bootstrap requests use `None`. IDE requests may use recovered
results, which remain explicitly status-tagged.

## 24. Input nodes exposed to the query system

Document 03 should expose normalized inputs as typed leaf queries rather than
allowing arbitrary reads from `RevisionRecord`.

Conceptual leaf families include:

```text
compiler_build_identity()
package_input(package)
source_file(file)
source_blob(file)
dependency_interface(package)
standard_library_interface()
trusted_runtime_manifest()
target_input()
semantic_options()
codegen_options()
lint_options()
diagnostic_options()
capability_manifest()
compiler_limits()
request_demand()
```

Each leaf records the exact revision and projection it read. A type-check query
should not automatically depend on terminal color or emission debug detail. An
artifact query must depend on code-generation and capability inputs.

Direct ad hoc field access from deep semantic phases should be prohibited or
wrapped by the typed input API, otherwise dependency tracking cannot be
complete.

## 25. Revision construction algorithm

A recommended algorithm is:

```text
accept_request(external_request, optional_parent):
    1. allocate normalization transaction
    2. verify build identity compatibility
    3. validate request structure
    4. verify byte digests
    5. intern/deduplicate source blobs
    6. decode and validate dependency interfaces
    7. bind standard-library trusted manifest
    8. normalize packages, paths, options, capabilities, and limits
    9. freeze canonical input tables
   10. compute projected and complete fingerprints
   11. find or create NormalizedInputWorld
   12. validate optional parent and compute verified change set
   13. allocate RevisionRecord in Building state
   14. attach host version/provenance aliases
   15. atomically transition to Published
   16. return RevisionKey
```

If any step fails:

- no `Published` revision exists;
- temporary imported blobs not referenced elsewhere may be reclaimed;
- validated immutable interfaces already present in the database may remain;
- the host receives a request/corruption/resource/invariant failure as
  appropriate.

## 26. Parent comparison algorithm

Given parent and child normalized worlds, comparison proceeds by stable keys and
projected digests:

1. compare compiler build compatibility;
2. compare package key sets;
3. compare stable file key sets;
4. compare each file's blob digest and logical metadata;
5. compare dependency package identities and interface digests;
6. compare standard-library content and manifest digests;
7. compare semantic option projection;
8. compare target/codegen projection;
9. compare lint, diagnostic, capability, and limit projections;
10. freeze a deterministic `RevisionChangeSet`.

Large source bytes are not compared when verified digests and stored collision
checks establish equality.

The change set is an optimization seed. Query validity still follows recorded
dependencies, as specified in documents 03 and 05.

## 27. Session creation and body processing

A typical checked body path is:

```text
RequestSession
    -> open PackageSession(package)
        -> demand body key
            -> open query frame: typed_core(body)
                -> create BodySession
                -> parse or borrow immutable body syntax
                -> resolve names
                -> elaborate static semantics
                -> construct Typed Core
                -> validate result
                -> atomically publish immutable Typed Core
                -> destroy BodySession scratch
            -> open query frame: mir(body)
                -> create LoweringContext
                -> lower Core + construct PlaceFlow
                -> validate MIR and facts
                -> atomically publish immutable MIR product
                -> destroy LoweringContext scratch
        -> complete package interface/reachability as demanded
    -> finalize diagnostics/outcome
```

The same body may be revisited by another request without reusing the old mutable
session. It reuses immutable query products or constructs a fresh session.

## 28. Memory retention policy

### 28.1 Retention classes

Every database allocation should be tagged or attributable to one class:

- essential database state;
- immutable content blob;
- live revision metadata;
- pinned revision data;
- in-memory query cache;
- active request;
- active body/query scratch;
- pending persistent write;
- diagnostics/statistics;
- quarantine/debug retention.

### 28.2 What should remain resident

Usually cheap and valuable to retain:

- source blobs used by live or recent revisions;
- line indexes;
- package/interface indexes;
- canonical names and semantic terms;
- small exported interfaces;
- query dependency metadata;
- compact summaries.

Potentially expensive and evictable:

- full body syntax results;
- Typed Core bodies;
- MIR bodies;
- optimized MIR variants;
- source-to-PC maps;
- emitted function fragments;
- large explanation traces.

### 28.3 Revision retirement

A revision may retire when:

- it is no longer a workspace/editor head;
- no active request pins it;
- no host alias requires exact response matching;
- retention policy permits retirement.

Retiring a revision removes its root from retention but does not immediately
free shared blobs or query results still referenced by another revision or
cache policy.

### 28.4 Pin accounting

Revision pinning should be explicit and bounded. A leaked pin is observable in
statistics and diagnostics for the compiler developer.

The G1 implementation may use an integer pin count managed only by the
single-threaded request scheduler. This is a narrow database mechanism, not a
general user-visible reference-counting facility.

### 28.5 Eviction safety

Eviction may reduce performance only. It may not change diagnostics, semantic
results, artifact bytes, or revision identity.

A value under active borrow or query use is not evictable. Eviction operates at
safe points between requests or through typed leases.

## 29. Cancellation and transactional publication

### 29.1 Cancellation source

Cancellation originates in the host client or supervisor of compiler work. The
request session receives a cancellation token/state as an operational input.

### 29.2 Safe points

Long-running operations should check cancellation at bounded intervals:

- source normalization loops;
- parsing and scanning loops;
- solver worklists;
- instance discovery;
- MIR fixed points;
- optimizer passes;
- large serialization operations.

Checking must be deterministic with respect to successful output. A cancelled
request has no artifact identity.

### 29.3 Publication levels

There are three publication levels:

1. **query publication** — one complete immutable query result;
2. **package publication** — one canonical interface or package product;
3. **request publication** — final diagnostics, manifests, and artifacts.

Each level has its own guard. Higher-level cancellation does not corrupt already
committed lower-level immutable facts, but whether those facts become reusable
is governed by complete dependency validation.

### 29.4 Persistent writes

Persistent cache or artifact writes are staged to temporary content and renamed
or committed atomically only after checksum, schema, and result validation.
Cancellation deletes or abandons temporary staging.

## 30. Resource accounting

### 30.1 Hierarchical budgets

```text
RequestBudget
    +-- PackageBudget
    |       +-- BodyBudget
    |       |       +-- QueryBudget
    |       |       +-- SolverBudget
    |       |       +-- LoweringBudget
    |       +-- InstanceBudget
    +-- EmissionBudget
    +-- DiagnosticBudget
```

A child budget cannot spend beyond its parent. Unused allocation returns on
completion or cleanup where the accounting scheme supports reservations.

### 30.2 Observed cost

Completed products should record bounded cost summaries useful for:

- performance regressions;
- safe cache reuse under different generous limits;
- invalidation explanation;
- self-host peak-memory audits.

Cost data does not affect semantic output unless explicitly requested in an
inspection product.

### 30.3 Limit failures

A limit failure includes:

- stable limit code;
- subsystem;
- configured ceiling;
- observed or attempted value;
- owning package/body/query when available;
- source location where meaningful;
- remediation guidance.

It remains distinct from cancellation and internal invariant failure.

## 31. Diagnostics and failure taxonomy

### 31.1 Request-construction failure

Examples:

- missing supplied source;
- duplicate file identity;
- invalid package graph;
- malformed option;
- unsupported target;
- inconsistent manifest.

Producer: host adapter or normalization boundary.

### 31.2 Input-corruption failure

Examples:

- digest mismatch;
- malformed dependency interface;
- impossible canonical record;
- trusted manifest mismatch.

Producer: defensive input decoder/validator.

### 31.3 Source diagnostic

Malformed or semantically invalid Glorious source inside a valid revision.
Producer: compiler semantic phases.

### 31.4 Recovery result

Incomplete but explicitly tagged IDE value derived from invalid or unfinished
source. Producer: recovery-capable frontend/semantic query.

### 31.5 Resource failure

A valid request exceeds an explicit compiler limit. Producer: budget owner.

### 31.6 Cancellation

The host abandons obsolete or unwanted work. Producer: request cancellation
boundary.

### 31.7 Internal invariant failure

The compiler observes impossible state, stale local identity, mismatched owner,
invalid publication transition, or failure of a supposedly validated product.
Producer: invariant check.

### 31.8 Persistence failure

The compiler cannot read or atomically write an optional cache or requested
output. Cache failure may fall back to recomputation; required output failure is
reported to orchestration.

No failure class may be flattened into “compilation failed” inside the semantic
core.

## 32. Determinism requirements

### 32.1 Revision fingerprints

Fingerprint serialization uses:

- explicit schema tags;
- fixed integer encodings;
- canonical string/byte encodings;
- deterministic record order;
- no memory addresses;
- no host timestamps;
- no absolute paths unless explicitly canonicalized as nonsemantic provenance;
- no raw hash-map iteration.

### 32.2 Stable diagnostic identity

Request and revision sequence numbers may appear in debug traces but not in
stable diagnostic codes or ordering keys.

### 32.3 Equivalent host assembly

Two hosts that supply the same normalized package graph, logical paths, bytes,
dependencies, manifests, target, and options must produce the same world
fingerprints even when their checkout directories and input enumeration orders
differ.

### 32.4 Warm and cold service history

Creating revisions in a different prior history must not affect the semantic
fingerprint or output of the current world. Database-local numeric IDs are
excluded from boundary products.

## 33. Security properties

The input and ownership model should establish the following properties.

### 33.1 No time-of-check/time-of-use source race

The compiler hashes and owns immutable bytes. It does not validate a path and
later reopen changed content.

### 33.2 No cross-revision fact confusion

Every query is revision-qualified, and shared results require validated
fingerprints. Coincident local IDs cannot alias semantic facts.

### 33.3 No cache authority

Cache bytes enter through the same validation and ownership transition as other
untrusted external blobs.

### 33.4 No ambient capability escalation

Runtime capabilities are request data encoded into an artifact, not authority
held by semantic sessions.

### 33.5 Bounded hostile input retention

Malformed requests and interfaces are rejected under explicit limits before
causing unbounded database retention. Quarantined/debug data obeys separate
small caps.

### 33.6 Stale-key defense

Typed key spaces and generation checks prevent a retired/recycled revision or
arena slot from being mistaken for a current one.

## 34. End-to-end scenarios

### 34.1 One-file edit with unchanged interface

1. LSP host receives new bytes for `parser.glorious` version 42.
2. Host assembles a complete world using overlays for open files and prior bytes
   for unchanged files.
3. Compiler verifies the new digest and reuses all unchanged source blobs and
   dependency interfaces.
4. New revision points to the changed blob and previous world as parent.
5. Request pins the new revision.
6. Queries read only revision-qualified inputs.
7. If the function body changes but exported interface does not, downstream
   package interface identity remains reusable according to documents 03 and 05.
8. Old editor requests remain pinned to version 41 or are cancelled.
9. When unpinned, version 41 may retire.

### 34.2 Lint-only change

1. Host changes one lint from `Warn` to `Deny`.
2. Source-semantic fingerprint remains the same.
3. Diagnostic/lint projection changes.
4. Parsed, resolved, typed, and lowered products may be reused if their query
   contracts do not depend on lint severity.
5. Diagnostic aggregation and final success are recomputed.

### 34.3 Target-only change

1. Host changes target layout or code-generation features.
2. Target-independent frontend and semantic products remain eligible for reuse.
3. Layout-dependent queries, emission, artifacts, and verification products are
   distinct.
4. Revision/world records preserve both target inputs; no mutable global target
   is switched in place.

### 34.4 Dependency interface replacement

1. `grand` resolves a new locked dependency revision and supplies its interface.
2. Compiler validates and interns the new interface.
3. New world references it under the same dependency package key but different
   identity/digest.
4. Parent comparison marks the dependency changed.
5. Queries that recorded dependencies on unaffected exported facts may be
   revalidated narrowly when documents 03 and 05 permit; others recompute.

### 34.5 Cancelled editor request

1. Version 50 request begins type checking.
2. Version 51 arrives and host cancels version 50.
3. Safe-point check aborts the request.
4. Body/session scratch is cleaned up.
5. No request diagnostics or artifact for version 50 are published.
6. Complete atomic subquery results may remain only under document 03's commit
   rule.
7. Revision 50 retires after all pins release.

### 34.6 Cold bootstrap stage

1. Bootstrap driver supplies exact compiler and standard-library sources,
   manifests, target, options, capabilities, and limits.
2. Compiler creates a canonical world independent of checkout path.
3. Bootstrap request pins it and demands the compiler artifact.
4. Stage output manifest records all input fingerprints.
5. Stage-two and stage-three requests use the same normalized semantic world and
   compare canonical artifacts.

## 35. Proposed self-hosted module layout

The exact source layout may evolve, but ownership should be visible:

```text
self-host/src/compiler/
    database/
        database.glorious
        stores.glorious
        revisions.glorious
        snapshots.glorious
        retention.glorious

    inputs/
        request.glorious
        normalize.glorious
        packages.glorious
        sources.glorious
        dependencies.glorious
        standard_library.glorious
        target.glorious
        options.glorious
        capabilities.glorious
        limits.glorious
        fingerprints.glorious

    sessions/
        request.glorious
        package.glorious
        body.glorious
        lowering.glorious
        emission.glorious
        publication.glorious
        budgets.glorious

    service/
        compile.glorious
        inspect.glorious
        ide.glorious
        bootstrap.glorious
```

The existing `frontend/`, `backend/`, and `diagnostics/` phase libraries remain
separate. The compiler ownership modules coordinate them; they do not absorb
their semantic implementations.

## 36. Conceptual service API

```glorious
pub create_database(
    configuration: DatabaseConfiguration
) -> CompilerDatabase;

pub import_world(
    database: &mut CompilerDatabase,
    request: CompilationRequest,
    parent: Option<RevisionKey>
) -> Result<RevisionKey, InputFailure>;

pub run_request(
    database: &mut CompilerDatabase,
    revision: RevisionKey,
    request: HostRequestIdentity,
    demand: RequestDemand,
    cancellation: CancellationInput
) -> CompilationOutcome;

pub retire_revision(
    database: &mut CompilerDatabase,
    revision: RevisionKey
) -> Result<(), RevisionFailure>;

pub collect_retired(
    database: &mut CompilerDatabase,
    policy: RetentionPolicy
) -> RetentionReport;
```

`run_request` constructs and consumes an affine `RequestSession` internally.
Hosts do not receive mutable access to session fields.

## 37. Testing strategy

### 37.1 Request normalization tests

Test:

- order-independent package and file inputs;
- path normalization;
- duplicate/conflicting file identities;
- package graph errors;
- malformed capabilities;
- option projection classification;
- digest mismatch;
- target validation;
- limit overflow.

### 37.2 Fingerprint tests

Assert identical fingerprints for:

- different host enumeration order;
- different absolute checkout roots;
- cache enabled versus disabled;
- equivalent normalized capability order;
- equivalent lint map order.

Assert different relevant fingerprints for:

- one byte of source change;
- logical path or owning package change;
- dependency interface change;
- standard manifest change;
- semantic option change;
- target/codegen change;
- capability change.

### 37.3 Revision isolation tests

Create two live revisions and prove:

- each source query returns its own bytes;
- same local numeric IDs cannot cross owners;
- old requests remain coherent after new revision creation;
- retired revisions remain valid while pinned;
- stale generation keys fail closed.

### 37.4 Session cleanup tests

Inject failure or cancellation at every acquisition stage and assert:

- revision pins release;
- publication guards remain uncommitted;
- body scratch is reclaimed;
- temporary indexes roll back;
- no partial interface or artifact is visible;
- resource leases settle correctly.

### 37.5 Editor overlay tests

Test:

- unsaved source precedence;
- atomic multi-file edit revisions;
- stale request handling;
- cancellation of obsolete versions;
- malformed overlay source with recovered results;
- disk changes that do not affect an open overlay.

### 37.6 Retention tests

Measure and assert:

- body-local memory returns after processing;
- unpinned retired revisions are collectible;
- shared blobs survive only while referenced;
- eviction does not alter outputs;
- leaked pin detection works;
- self-host peak memory remains within the release gate.

### 37.7 Differential tests

Run equivalent requests through:

- direct `grc` adapter;
- `grand`;
- language-server service request;
- Rust stage-zero compiler where contracts overlap;
- self-hosted VM and native execution paths where available.

Normalized worlds and semantic outputs should agree.

### 37.8 Determinism tests

Randomize host input order, request history, cache warmth, and eviction sequence;
assert byte-identical normalized manifests, diagnostics, and artifacts.

## 38. Migration from the current implementation

Migration should preserve existing parity tests while moving ownership in small
stages.

### Stage 1: Inventory ambient inputs

List every read of:

- filesystem;
- process arguments;
- environment variables;
- global standard-library state;
- target globals;
- diagnostic output;
- cache directories.

Classify each as host orchestration or explicit compiler input.

### Stage 2: Freeze one explicit request struct

Introduce a request value for the current integrated compiler path containing
source bundle, manifest, options, target, capabilities, and limits. Route
existing command adapters through it without yet adding revisions.

### Stage 3: Separate raw host request from normalized input world

Move digest checks, logical path normalization, package validation, and option
canonicalization into one boundary. Existing phase functions receive normalized
views.

### Stage 4: Introduce source blob and validated interface stores

Deduplicate immutable bytes and dependency interfaces behind typed database
IDs. Remove phase ownership of duplicate source strings.

### Stage 5: Introduce `RevisionRecord`

Wrap normalized inputs in immutable revision records and require direct compiler
entry points to name a revision. Initially one database may hold one live
revision.

### Stage 6: Introduce affine `RequestSession`

Move diagnostics, limits, cancellation, trace selection, and publication staging
into the request owner. Remove mutable global “current compilation” state.

### Stage 7: Make package and body lifetimes explicit

Route body parsing, resolution, elaboration, Core building, and lowering through
one body session whose scratch leaves scope after publication. Add memory tests.

### Stage 8: Support multiple revisions

Add editor overlays, parent/change metadata, revision pinning, retirement, and
stale-key checks. Keep execution single-threaded.

### Stage 9: Expose typed input leaf queries

Replace deep direct reads of request/options/source tables with query-visible
input accessors, preparing document 03's dependency tracking.

### Stage 10: Add retention and eviction

Classify all database allocations, implement safe-point eviction, and publish
memory statistics. Confirm cold/warm output equivalence.

### Stage 11: Canonical bootstrap worlds

Make self-host stages consume exact normalized input manifests and compare stage
artifacts independently of checkout path.

## 39. Rejected alternatives

### 39.1 Mutable global current compilation

Rejected because it prevents nested requests, revision isolation, precise
query dependencies, and safe language-server reuse.

### 39.2 Compiler phases reopen source paths

Rejected because it creates time-of-check/time-of-use races, ambient authority,
and nonreproducible snapshots.

### 39.3 Mutate one revision in place

Rejected because active queries could observe mixed worlds and old cache entries
would lose a clear input identity.

### 39.4 Whole-program mutable session retained forever

Rejected because body-local syntax and inference state would dominate memory,
complicate invalidation, and violate the one-body-at-a-time architecture.

### 39.5 Treat file path as file identity

Rejected because paths can move, differ across hosts, and alias. Stable file
identity, logical path, and content identity are distinct facts.

### 39.6 Use source digest alone as semantic identity

Rejected because package, logical module, standard-library, options, dependency,
and target context can change meaning for identical bytes.

### 39.7 General shared mutable reference counting

Rejected for G1 because it enlarges the runtime and ownership model, obscures
session lifetimes, and is unnecessary for a deterministic single-threaded
compiler service.

### 39.8 Trust host-supplied changed-file lists

Rejected as semantic evidence. They may seed comparison, but the compiler must
verify them against normalized worlds.

### 39.9 Keep recovery values indistinguishable from complete values

Rejected because editor approximations could leak into release builds or
persistent caches.

### 39.10 Make limits ambient process configuration

Rejected because failures would be irreproducible and unaccounted in request
manifests.

## 40. Open questions

1. Should semantically identical host document versions share one
   `RevisionKey`, or use lightweight revision aliases over one world?
2. How many recent LSP revisions should be retained by default?
3. Should G1 recycle revision slots or keep them append-only until process exit?
4. Which source blobs should be compressed in memory without harming editor
   latency?
5. How should absolute paths be redacted while preserving stable, useful
   provenance in local diagnostics?
6. Should the standard library normally enter downstream compilation as a
   canonical interface only, or as interface plus selected source maps?
7. Which request limits can be safely omitted from semantic fingerprints when a
   result records its observed cost?
8. Should completed subqueries from a cancelled request commit immediately or
   only after request success? Document 03 must choose a precise rule.
9. How should a future parallel compiler represent snapshot pins without
   introducing a general-purpose shared mutable ownership primitive?
10. Should generated source identity include the generator artifact digest, its
    declared version, or both?
11. How long should validated dependency interfaces remain resident when no live
    revision references them but persistent cache entries do?
12. Should inspection traces be retained as query products or streamed as
    request-local output?
13. How should revision provenance be canonicalized across local, vendored, and
    remote-execution hosts?
14. Can the compiler share target-independent normalized worlds across target
    variants while preserving a simple revision model?
15. Which current self-host data structures can be made immutable after
    publication without copying?

None of these questions weakens the requirement that a request see one complete
immutable world.

## 41. Acceptance criteria

This design is considered implemented when all of the following are true.

- [ ] Every compiler entry point accepts or constructs one explicit immutable
      compilation request.
- [ ] Semantic phases do not reopen source paths or inspect ambient host state.
- [ ] Raw requests are normalized, validated, canonically ordered, and
      fingerprinted before semantic use.
- [ ] Source bytes and dependency interfaces are digest-verified and
      database-owned.
- [ ] Logical paths are platform-independent labels, not read capabilities.
- [ ] Every request pins exactly one immutable revision.
- [ ] New source, dependency, standard-library, semantic-option, target, lint,
      capability, or relevant-limit input creates a distinct normalized world
      or projected identity.
- [ ] Two live revisions can be queried without fact or local-ID confusion.
- [ ] Revision keys fail closed when stale or generation-mismatched.
- [ ] The compiler can retain multiple editor versions and cancel obsolete
      requests safely.
- [ ] `CompilerDatabase`, `RevisionRecord`, `RequestSession`, `PackageSession`,
      `BodySession`, `LoweringContext`, query frames, and `EmissionSession` have
      explicit ownership contracts.
- [ ] Body-local syntax, inference, Core-building, and lowering scratch are
      released after body publication.
- [ ] No mandatory whole-program mutable body AST is retained.
- [ ] Cancellation and failure release revision pins, child budgets, and
      publication guards.
- [ ] Request-level diagnostics, interfaces, manifests, and artifacts publish
      atomically.
- [ ] Recovered IDE values are explicitly distinguishable from release-valid
      values.
- [ ] Every retained allocation is attributable to a documented lifetime and
      retention class.
- [ ] Unpinned retired revisions can be collected without changing outputs.
- [ ] Cache warmth, revision history, host enumeration order, and absolute
      checkout path do not alter normalized fingerprints or artifacts.
- [ ] Bootstrap stages consume canonical input worlds and record their complete
      manifests.
- [ ] Tests cover normalization, isolation, cleanup, editor overlays, retention,
      stale keys, determinism, and migration parity.

## 42. Consequences for later documents

Document 03, the typed query engine, must:

- take `DatabaseSnapshot` or `RequestSession` as the source of all direct inputs;
- expose typed input leaf queries rather than deep ad hoc request reads;
- make query publication atomic;
- preserve revision qualification through nested queries;
- define cancellation and completed-subquery commit precisely.

Document 04, stable identity and typed arenas, must:

- distinguish database, revision, package, definition, body, instance, query,
  and local arena key spaces;
- prevent raw local IDs from crossing owners;
- define identity stability across revisions and editor edits.

Document 05, dependency tracking and invalidation, must:

- derive change propagation from recorded input/query dependencies;
- use `RevisionChangeSet` only as a verified acceleration and explanation aid;
- never trust host changed-file hints as semantic truth.

Document 06, caching and persistence, must:

- persist only complete immutable products;
- include compatible build/schema/input identities;
- treat all returned bytes as untrusted;
- preserve cold/warm output identity;
- define retention and eviction interaction with the in-memory database.

All frontend, semantic, MIR, optimizer, emitter, tooling, and bootstrap documents
must name the owner and lifetime of every mutable context they introduce.

The compiler's later sophistication—queryability, incremental reuse, effect and
quantity reasoning, source-defined control specialization, independent
verification, and self-host convergence—depends on this simpler foundation:

- the world is explicit;
- the world is immutable;
- the request sees exactly one world;
- state has one owner;
- temporary work dies on time;
- completed facts cross boundaries only after validation.
