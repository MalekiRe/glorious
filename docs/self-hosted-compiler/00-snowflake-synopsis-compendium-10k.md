# Self-Hosted Glorious Compiler — 10,000-Line Synopsis Compendium

Status: breadth-first implementation design.

This document expands all thirty-two planned compiler documents into one
long-form specification inventory before the remaining individual documents are
written in full. It complements the shorter
[roadmap](00-snowflake-document-roadmap.md), the existing
[synopsis compendium](00-snowflake-synopsis-compendium.md), and the detailed
specifications already written for documents 01 and 02.

The purpose of this expansion is not to inflate prose.
It is to force every subsystem through the same design questions.
Each section addresses interfaces, ownership, algorithms, invariants,
incrementality, caching, diagnostics, limits, determinism, tests, and migration.

The language and bytecode specifications remain authoritative.
This compendium describes the target self-hosted implementation.
Existing executable names remain `grand`, `grc`, and `grvm`.
Existing suffixes remain `.glorious` and `.grbc`.

The common structure is:

1. purpose and scope;
2. goals and non-goals;
3. public queries and interfaces;
4. primary data structures;
5. ownership and lifetime model;
6. algorithms and phase order;
7. semantic invariants;
8. cycles and fixed points;
9. incremental dependencies and invalidation;
10. caching and persistence;
11. diagnostics and explanations;
12. cancellation, limits, and security;
13. determinism and reproducibility;
14. testing and observability;
15. migration and completion criteria.

---

# Volume I — The Compiler's System Spine

## 01. Architecture and Trust Boundaries

This section defines the authority split for the complete toolchain.
The compiler is treated as a semantic service rather than one omnipotent binary.
Every external capability crosses a typed boundary.
Every trust claim is named precisely.

### Purpose and scope

- **Separate orchestration from semantics.**
  `grand` assembles package inputs.
  The compiler decides source meaning.
  Neither component duplicates the other.
- **Separate emission from verification.**
  The emitter constructs candidate bytes.
  The verifier checks runtime invariants.
  Emission never implies acceptance.
- **Separate verification from execution.**
  `grvm` receives a frozen image.
  Raw artifacts remain unexecutable.
  Runtime authority comes from supervision.
- **Unify all semantic clients.**
  CLI, LSP, docs, and tests share queries.
  No client embeds a second checker.
  Presentation remains client-owned.
- **Define bootstrap authority.**
  Rust stage zero produces early artifacts.
  Self-host stages replace semantic authority.
  Convergence remains independently measured.

### Goals and non-goals

- **Goal: one semantic authority.**
  The compiler owns language legality.
  Tools request typed semantic facts.
  Divergent frontends are forbidden.
- **Goal: hermetic compilation.**
  Requests contain complete source bytes.
  Semantic phases read no ambient paths.
  Rebuilds become reproducible.
- **Goal: least authority.**
  Components receive narrow capabilities.
  Unneeded host effects are unavailable.
  Security follows the type boundary.
- **Non-goal: plugin execution.**
  G1 loads no compiler plugins.
  Procedural macros remain excluded.
  Extension points stay declarative.
- **Non-goal: verifier recompilation.**
  The verifier checks lowered contracts.
  It does not resolve source names.
  Trait solving remains compiler-owned.

### Public queries and interfaces

- **Compilation request interface.**
  Accept immutable sources and manifests.
  Include target and resource limits.
  Return structured products only.
- **Compilation outcome interface.**
  Return diagnostics and artifacts.
  Return interfaces and inspection data.
  Never print inside semantic phases.
- **Verification interface.**
  Accept untrusted `.grbc` bytes.
  Return a private frozen image.
  Preserve verification diagnostics.
- **Execution interface.**
  Accept frozen image and grants.
  Return supervised runtime outcome.
  Deny ambient host access.
- **Tooling service interface.**
  Expose semantic queries by snapshot.
  Support cancellation and recovery.
  Avoid private representation leakage.

### Primary data structures

- **`CompilationRequest`.**
  Stores immutable input world.
  Carries build and target identity.
  Owns no host handles.
- **`CompilationOutcome`.**
  Stores complete published products.
  Separates failure classes explicitly.
  Supports CLI and service clients.
- **`CandidateArtifact`.**
  Wraps emitted unverified bytes.
  Prevents accidental VM construction.
  Carries build manifest identity.
- **`FrozenExecutionImage`.**
  Is created only by verification.
  Exposes VM-ready immutable records.
  Hides raw decoder state.
- **`RuntimeGrantSet`.**
  Names exact allowed capabilities.
  Contains no wildcard inheritance.
  Is checked by every host adapter.

### Ownership and lifetime model

- **Orchestrator ownership.**
  Host clients own filesystem handles.
  They materialize immutable byte inputs.
  Handles die before semantic work.
- **Database ownership.**
  `CompilerDatabase` owns semantic state.
  Requests borrow immutable snapshots.
  Clients never mutate internal arenas.
- **Emitter ownership.**
  Emission sessions own serialization scratch.
  Canonical products publish atomically.
  Temporary buffers die after output.
- **Verifier ownership.**
  Decoder scratch remains verifier-local.
  Accepted records become frozen.
  Rejected artifacts publish nothing.
- **Runtime ownership.**
  Supervisor owns worker lifecycle.
  Worker owns execution frames.
  Host adapters own external resources.

### Algorithms and phase order

- **Assemble the input world.**
  `grand` resolves packages first.
  It reads every source deterministically.
  The compiler sees complete inputs.
- **Normalize before semantics.**
  Validate hashes and logical paths.
  Canonically order package records.
  Create a revision identity.
- **Compile through shared services.**
  Frontend, semantics, and MIR run.
  Emission produces candidate bytes.
  No phase acquires host authority.
- **Verify before execution.**
  Decode defensively under budgets.
  Check every lowered invariant.
  Produce the frozen image.
- **Supervise the runtime.**
  Create an isolated worker.
  Enforce time and memory policy.
  Route exact host requests.

### Semantic invariants

- **One authoritative producer.**
  Each fact has one owner.
  Clients may transform presentation only.
  Duplicated semantics are defects.
- **No spelling authority.**
  Names like `if` stay ordinary.
  Primitive power follows manifest identity.
  Renaming cannot change privilege.
- **No ambient input.**
  Semantic output depends on request data.
  Time and locale are excluded.
  Paths are labels, not handles.
- **No execution without verification.**
  VM constructors require frozen images.
  Candidate bytes cannot bypass checks.
  Test helpers obey the same rule.
- **No successful partial publication.**
  Failed boundaries publish nothing complete.
  Recovery products remain marked.
  Cache writes follow commit semantics.

### Cycles and fixed points

- **Architectural cycles are forbidden.**
  `grand` cannot call semantic callbacks.
  Semantic phases cannot reacquire orchestration.
  Boundaries remain directed.
- **Bootstrap cycles are staged.**
  Stage zero builds stage one.
  Stage one builds stage two.
  Stage two builds stage three.
- **Runtime callbacks are capability requests.**
  VM requests host operations.
  Adapters return typed responses.
  No arbitrary reverse execution occurs.
- **Tooling cycles use query policies.**
  LSP requests may nest queries.
  The query engine records dependencies.
  Protocol recursion stays external.
- **Trust cycles are documented.**
  Seed and verifier trust differ.
  Convergence reduces compiler dependence.
  It never erases supply-chain trust.

### Incremental dependencies and invalidation

- **Orchestration changes invalidate inputs.**
  Package graph changes create revisions.
  Source-byte changes are explicit.
  Host timestamps remain irrelevant.
- **Semantic boundaries expose fingerprints.**
  Interfaces fingerprint exported meaning.
  Artifacts fingerprint code generation.
  Diagnostics use presentation fingerprints.
- **Verifier changes affect acceptance.**
  Verifier generation enters manifests.
  Old frozen images are process-local.
  Artifacts may require rechecking.
- **Capability changes affect linking.**
  Host import legality depends on grants.
  Unrelated semantic queries remain reusable.
  Artifact roots are invalidated.
- **Tooling changes avoid semantic invalidation.**
  LSP formatting changes presentation only.
  Compiler facts remain reusable.
  Query projections enforce separation.

### Caching and persistence

- **Caches remain outside trust.**
  They return bytes only.
  The compiler validates every record.
  Misses fall back to recomputation.
- **Interfaces are canonical products.**
  Downstream builds import validated facts.
  Schema identity is mandatory.
  Unknown critical features reject.
- **Artifacts carry complete manifests.**
  Build inputs are recorded.
  Verification status is separate.
  Reuse requires exact compatibility.
- **Frozen images are not portable caches.**
  They may contain process-local views.
  Raw artifacts remain persistence format.
  Verification reconstructs authority.
- **Cache corruption is recoverable.**
  Bad records are ignored.
  Corruption never changes semantics.
  Diagnostics distinguish cache failures.

### Diagnostics and explanations

- **Authority diagnostics name the boundary.**
  Report compiler, verifier, or runtime origin.
  Avoid generic failure text.
  Preserve stable machine codes.
- **Hermeticity diagnostics identify missing inputs.**
  Name absent dependency blobs.
  Explain rejected logical paths.
  Never silently read the host.
- **Verification diagnostics cite artifact locations.**
  Report function and instruction.
  Include expected runtime state.
  Keep source mapping optional.
- **Capability diagnostics show exact denial.**
  Name requested capability.
  Show declared and granted sets.
  Separate compile-time and runtime checks.
- **Bootstrap diagnostics show stage ownership.**
  Name producing compiler stage.
  Include manifest fingerprints.
  Preserve first differing product.

### Cancellation, limits, and security

- **Cancellation crosses typed boundaries.**
  Requests carry cancellation state.
  Phases check bounded checkpoints.
  Published products remain atomic.
- **Semantic phases have structural budgets.**
  Tokens and declarations are bounded.
  Solvers and optimizers are metered.
  Exhaustion is a structured outcome.
- **Decoder treats bytes as hostile.**
  Lengths are checked before allocation.
  Indices are range-validated.
  Unsupported features fail closed.
- **Supervisor enforces runtime limits.**
  Memory and time remain external.
  Worker termination is classified.
  Host calls are metered.
- **Private types enforce authority.**
  Candidate and verified artifacts differ.
  Frozen images cannot be forged.
  Capability grants remain opaque.

### Determinism and reproducibility

- **Boundary serialization is canonical.**
  Maps never dictate output order.
  Pools freeze through sorted keys.
  Hashes exclude memory addresses.
- **Diagnostics have stable ordering.**
  Sort by source and code.
  Related labels use stable keys.
  Parallel scheduling cannot reorder output.
- **Artifact bytes ignore cache warmth.**
  Cold and warm builds match.
  Request history has no effect.
  Emission records deterministic evidence.
- **Verification is deterministic.**
  Worklists use stable order.
  Resource accounting is reproducible.
  Equivalent artifacts yield equal outcomes.
- **Bootstrap manifests are canonical.**
  Stage inputs are fully pinned.
  Stage two and three compare bytes.
  Differences expose phase fingerprints.

### Testing and observability

- **Authority tests inspect forbidden imports.**
  Semantic modules expose no host effects.
  VM constructors reject raw artifacts.
  Tooling has no duplicate checker.
- **Hermeticity tests mutate host state.**
  Working directory changes nothing.
  Locale changes nothing.
  File timestamps change nothing.
- **Boundary fuzzing targets every decoder.**
  Dependency interfaces are hostile.
  Cache records are hostile.
  `.grbc` bytes are hostile.
- **End-to-end tests use real components.**
  `grand` invokes shared compiler services.
  Verification precedes VM execution.
  Capability denials remain exact.
- **Tracing names component transitions.**
  Requests record phase boundaries.
  Products record producer identity.
  Failures retain provenance.

### Migration and completion criteria

- **Move host I/O outward first.**
  Extract phase-local filesystem effects.
  Return diagnostics as data.
  Preserve behavior through probes.
- **Introduce typed artifact states.**
  Separate candidate and verified forms.
  Restrict VM constructors.
  Update tests and tooling.
- **Unify compiler entry points.**
  Route `grand`, `grc`, and LSP.
  Remove duplicate adapters.
  Compare equivalent requests.
- **Harden imported boundaries.**
  Version interfaces and caches.
  Add defensive decoding.
  Add corruption tests.
- **Complete when trust claims are measurable.**
  CI checks authority boundaries.
  Builds are reproducible.
  Bootstrap stages converge.

## 02. Compilation Inputs, Revisions, and Session Ownership

This section defines the compiler's immutable world model.
It specifies every input that may affect results.
It defines revisions, snapshots, sessions, and memory ownership.
It prevents mixed-world queries and accidental retention.

### Purpose and scope

- **Define complete compiler inputs.**
  Sources, interfaces, options, and limits count.
  Hidden environment inputs are forbidden.
  Every result names its world.
- **Define immutable revisions.**
  Input changes create new records.
  Existing snapshots never mutate.
  Requests observe one coherent world.
- **Define session ownership.**
  Database, request, package, and body differ.
  Each mutable context has one owner.
  Lifetimes remain bounded.
- **Support editor overlays.**
  Unsaved bytes become revision inputs.
  Multiple versions may coexist.
  Stale work cannot publish forward.
- **Support one-body compilation.**
  Body scratch stays transient.
  Whole-program AST retention is optional.
  Memory remains self-host viable.

### Goals and non-goals

- **Goal: exhaustive input accounting.**
  Semantic options are typed.
  Standard library identity is explicit.
  Capability manifests are included.
- **Goal: snapshot isolation.**
  Every query pins a revision.
  Nested queries inherit it.
  Cross-revision IDs fail closed.
- **Goal: bounded retention.**
  Every allocation has a class.
  Retired revisions become collectable.
  Metrics expose retained bytes.
- **Non-goal: in-place syntax mutation.**
  Edits create new source blobs.
  Trees are rebuilt or reused immutably.
  Shared mutable ASTs are excluded.
- **Non-goal: ambient file watching.**
  Hosts detect external changes.
  The compiler receives new inputs.
  Semantic code watches nothing.

### Public queries and interfaces

- **`normalize_request`.**
  Accept raw host inputs.
  Validate ordering and hashes.
  Produce `NormalizedInputWorld`.
- **`intern_revision`.**
  Reuse identical normalized worlds.
  Create a generation-safe key.
  Record parent change hints.
- **`snapshot`.**
  Pin a revision record.
  Expose immutable input leaves.
  Release pin on cleanup.
- **`begin_request`.**
  Attach cancellation and budgets.
  Stage diagnostics and products.
  Publish atomically.
- **`diff_revisions`.**
  Compare normalized input identities.
  Produce verified change categories.
  Explain likely invalidation roots.

### Primary data structures

- **`RawCompilationRequest`.**
  Mirrors host-supplied records.
  Allows unordered external inputs.
  Carries provenance for errors.
- **`NormalizedInputWorld`.**
  Stores canonical package topology.
  Stores validated immutable blobs.
  Carries projected fingerprints.
- **`RevisionRecord`.**
  Owns one complete input world.
  Stores parent and change summary.
  Tracks lifecycle state.
- **`DatabaseSnapshot`.**
  Holds a revision pin.
  Resolves generation-safe keys.
  Exposes no mutation.
- **`RequestSession`.**
  Owns budgets and publication staging.
  Creates package and body sessions.
  Handles cleanup on failure.

### Ownership and lifetime model

- **Process lifetime.**
  Compiler build identity remains fixed.
  Global immutable tables may persist.
  Host handles remain outside.
- **Database lifetime.**
  Blob stores and interners persist.
  Revision records are database-owned.
  Eviction metadata remains mutable.
- **Revision lifetime.**
  Input world stays immutable.
  Pins prevent collection.
  Retired worlds reject new work.
- **Request lifetime.**
  Cancellation and budgets are scoped.
  Diagnostics stage privately.
  Publication commits once.
- **Body lifetime.**
  Syntax and inference scratch live briefly.
  Published products become immutable.
  Mutable body state never escapes.

### Algorithms and phase order

- **Validate raw request shape.**
  Check duplicate package identities.
  Check logical path normalization.
  Reject inconsistent dependency edges.
- **Verify every content digest.**
  Source bytes match supplied hashes.
  Interfaces match recorded identities.
  Standard library manifests match.
- **Canonicalize collection order.**
  Sort packages and sources.
  Normalize options and capabilities.
  Remove presentation-only noise.
- **Compute projected fingerprints.**
  Separate semantic and target inputs.
  Separate presentation and artifact inputs.
  Record projection generations.
- **Create or reuse revision.**
  Compare normalized world digest.
  Store parent relation if known.
  Return generation-safe key.

### Semantic invariants

- **One request sees one world.**
  No query changes revision midflight.
  Nested demands inherit snapshot.
  Publication targets the pinned world.
- **Logical paths are not capabilities.**
  They affect modules and diagnostics.
  They cannot reopen files.
  Absolute paths are normalized away.
- **Bytes are database-owned.**
  Host buffers may disappear.
  Snapshots retain immutable storage.
  Hashes always match contents.
- **Local IDs never imply revision identity.**
  Keys include owner context.
  Numeric equality proves nothing.
  Stale generations fail closed.
- **Transient work is unpublished.**
  Scratch has no stable key.
  Only validated products cross sessions.
  Failure releases mutable state.

### Cycles and fixed points

- **Package graph cycles are validated.**
  Illegal dependency cycles reject.
  Workspace grouping remains explicit.
  Interface SCCs use later policies.
- **Revision parent chains are bounded.**
  Parents aid explanation only.
  Semantic truth comes from content.
  Chains may be compacted.
- **Editor version cycles are impossible.**
  Versions form immutable successors.
  Undo creates another revision.
  Identity reuse remains content-based.
- **Session ownership is acyclic.**
  Database owns revisions.
  Requests pin revisions.
  Bodies borrow requests.
- **Retention cycles require explicit roots.**
  Caches cannot pin revisions accidentally.
  Diagnostics store stable anchors.
  Eviction can break optional links.

### Incremental dependencies and invalidation

- **Source changes identify leaf inputs.**
  File digest differences are exact.
  Host hints remain advisory.
  Query dependencies decide propagation.
- **Dependency interface changes are granular.**
  Export fingerprints can remain equal.
  Downstream bodies may stay green.
  Artifact changes remain separate.
- **Option projections narrow invalidation.**
  Color changes affect rendering only.
  Optimization changes affect later phases.
  Language flags affect semantics.
- **Limit changes are relevance-sensitive.**
  Unreached generous limits may reuse.
  Reached limits affect outcomes.
  Budget dependency is recorded.
- **Capability changes affect host legality.**
  Pure semantic facts may remain stable.
  Linking and verification roots rerun.
  Runtime manifests are replaced.

### Caching and persistence

- **Input blobs use content addressing.**
  Identical bytes share storage.
  Logical identities remain separate.
  Hash verification precedes interning.
- **Revision records are not persistent truth.**
  They may be reconstructed.
  Complete manifests remain serializable.
  Process-local generations stay private.
- **Request sessions are never persisted.**
  Cancellation state is ephemeral.
  Publication staging is ephemeral.
  Completed products persist separately.
- **Body products may persist.**
  Keys include semantic fingerprints.
  Local IDs are remapped canonically.
  Validation rebuilds typed arenas.
- **Editor overlays stay local.**
  Unsaved contents avoid shared caches.
  Stable semantic subproducts may reuse.
  Privacy of source is preserved.

### Diagnostics and explanations

- **Normalization diagnostics cite provenance.**
  Name duplicate external records.
  Show conflicting package identities.
  Preserve host input labels.
- **Digest diagnostics distinguish corruption.**
  Report expected and actual hash.
  Avoid source-error classification.
  Block semantic consumption.
- **Revision diagnostics explain mismatch.**
  Show stale generation.
  Show requested and active revision.
  Suggest reissuing the query.
- **Retention diagnostics expose owners.**
  Report bytes by lifetime class.
  Show pinned revision roots.
  Identify leaked body contexts.
- **Invalidation explanations show input changes.**
  Name changed source or option.
  Link to dependent query roots.
  Separate advisory change hints.

### Cancellation, limits, and security

- **Snapshot pins use cleanup.**
  Cancellation releases them.
  Failures cannot leak revisions.
  Collection remains safe.
- **Requests receive hierarchical budgets.**
  Child phases charge parent totals.
  Exhaustion remains deterministic.
  Sibling work cannot steal silently.
- **Source size is bounded early.**
  Hashing occurs under limits.
  Decoding avoids amplification.
  Oversized inputs reject structurally.
- **Provenance avoids path disclosure.**
  Diagnostics may redact host roots.
  Logical paths remain stable.
  Cache keys exclude secrets.
- **Retired revisions reject publication.**
  Old work may read pinned data.
  It cannot overwrite newer facts.
  Commit guards verify state.

### Determinism and reproducibility

- **Normalization order is canonical.**
  Host enumeration never leaks.
  Duplicate detection is stable.
  Hash input encoding is versioned.
- **Projected fingerprints are deterministic.**
  Each projection has a schema.
  Fields use canonical serialization.
  Unknown fields fail explicitly.
- **Revision keys avoid wall-clock values.**
  Content defines semantic identity.
  Generation protects process safety.
  History does not alter output.
- **Memory eviction is semantically invisible.**
  Recomputed values match cached values.
  Retention policy affects latency only.
  Tests compare outcomes.
- **Bootstrap worlds are fully pinned.**
  Source ordering is canonical.
  Standard library identity is exact.
  Limits and target are recorded.

### Testing and observability

- **Normalization property tests vary ordering.**
  Equivalent requests hash equally.
  Duplicate inputs reject consistently.
  Platform separators normalize.
- **Snapshot tests run concurrent revisions.**
  Queries never mix facts.
  Stale keys fail.
  Old pins remain readable.
- **Cancellation tests inspect cleanup.**
  Pins return to zero.
  Body arenas disappear.
  No product publishes.
- **Retention tests compile the compiler.**
  Peak memory remains bounded.
  Body scratch is reclaimed.
  Revision collection is measured.
- **Overlay tests simulate editor histories.**
  Unsaved text wins over disk.
  Atomic edits remain coherent.
  obsolete requests cancel safely.

### Migration and completion criteria

- **Introduce normalized request types.**
  Wrap current CLI inputs.
  Preserve existing behavior.
  Record missing ambient dependencies.
- **Move source bytes into database storage.**
  Stop reopening paths.
  Add logical path records.
  Verify digests.
- **Add immutable revision records.**
  Route phase entry through snapshots.
  Tag keys by owner.
  Reject stale generations.
- **Scope mutable contexts explicitly.**
  Create request and body sessions.
  Add cleanup guards.
  Measure retained memory.
- **Complete when mixed worlds are impossible.**
  All entry points use snapshots.
  Body scratch is bounded.
  Bootstrap manifests are complete.

## 03. The Typed Query Engine

This section defines the compiler's computation model.
Every reusable fact becomes a typed query.
Dependencies are recorded automatically.
Publication, cycles, recovery, and explanation share one engine.

### Purpose and scope

- **Model semantic computation explicitly.**
  Queries name repeatable facts.
  Keys and values are statically typed.
  Dynamic service lookup is excluded.
- **Record dependencies automatically.**
  Nested demands form edges.
  Input reads become leaf dependencies.
  Query authors avoid manual journals.
- **Support incremental validation.**
  Prior values may become green.
  Changed dependencies trigger recomputation.
  Equal fingerprints stop propagation.
- **Support all compiler clients.**
  Builds and editors share definitions.
  Inspection reads the same tables.
  Recovery policy remains explicit.
- **Support self-host implementation.**
  Engine mechanisms stay compact.
  Single-threaded execution is sufficient.
  Future parallelism remains possible.

### Goals and non-goals

- **Goal: typed registration.**
  Every family defines key and value.
  Cycle policy is declared.
  Persistence policy is declared.
- **Goal: atomic publication.**
  Value and dependencies commit together.
  Failure commits nothing.
  Cancellation cannot leave half entries.
- **Goal: explainability.**
  Reuse and recomputation are inspectable.
  Dependency paths are stable.
  Costs are attributed.
- **Non-goal: arbitrary reflection.**
  Queries are not stringly typed.
  Values are not universal boxes.
  Downcasts are forbidden.
- **Non-goal: mandatory parallelism.**
  Correctness precedes scheduling.
  Determinism remains simple.
  Threads are optional later.

### Public queries and interfaces

- **`demand<Q>`.**
  Accept a typed query key.
  Return `Analysis<Q::Value>`.
  Record the parent dependency.
- **`read_input<I>`.**
  Read a typed revision leaf.
  Record its fingerprint.
  Reject cross-snapshot access.
- **`query_status`.**
  Inspect absent, running, or complete state.
  Include recovery and failure class.
  Avoid exposing mutable internals.
- **`why_recompiled`.**
  Trace changed dependency edges.
  Reach a concrete input leaf.
  Include fingerprint differences.
- **`query_graph`.**
  Export typed graph records.
  Redact large values.
  Preserve stable node names.

### Primary data structures

- **`QueryFamily`.**
  Defines key and value types.
  Declares cycle and cache policy.
  Supplies compute and validate functions.
- **`QueryFrame`.**
  Holds active key and revision.
  Journals dependencies and diagnostics.
  Stages the result.
- **`MemoEntry`.**
  Stores complete published value.
  Stores value and dependency fingerprints.
  Stores provenance and cost.
- **`Analysis<T>`.**
  Distinguishes complete and recovered values.
  Represents rejection and cancellation.
  Carries diagnostics as data.
- **`DependencyEdge`.**
  Names parent and child facts.
  Records observed fingerprint.
  Carries dependency class.

### Ownership and lifetime model

- **Database owns memo tables.**
  Entries outlive requests when useful.
  Eviction may remove them.
  Recompute remains equivalent.
- **Request owns active stack.**
  Frames borrow the snapshot.
  Cancellation belongs to request.
  Stack disappears on completion.
- **Frame owns dependency journal.**
  Child completion appends an edge.
  Failure discards the journal.
  Publication moves it atomically.
- **Values are immutable after publication.**
  Consumers borrow shared views.
  Mutable builders stay query-local.
  Persistent encoders copy canonically.
- **Diagnostics follow product lifetime.**
  Semantic diagnostics may memoize.
  Presentation is regenerated separately.
  Stale source anchors are remapped.

### Algorithms and phase order

- **Canonicalize the query key.**
  Normalize substitutions and options.
  Attach revision qualification.
  Reject invalid local IDs.
- **Check the active stack.**
  Detect reentrant demand.
  Invoke declared cycle policy.
  Produce stable cycle traces.
- **Check memoized state.**
  Reuse same-revision entries directly.
  Attempt cross-revision validation.
  Consult persistent cache if allowed.
- **Compute under a frame.**
  Record every dependency.
  Charge budgets and check cancellation.
  Stage diagnostics and value.
- **Publish atomically.**
  Validate complete result.
  Compute canonical fingerprints.
  Install value and edges together.

### Semantic invariants

- **Keys determine computation class.**
  Equivalent keys mean equivalent work.
  Hidden inputs are prohibited.
  Family versions enter identity.
- **Dependencies are complete.**
  Every semantic read is recorded.
  Manual bypasses are forbidden.
  Missing edges are correctness bugs.
- **Recovery status never disappears.**
  Downstream complete queries reject it.
  IDE-aware queries propagate it.
  Cache encodings preserve it.
- **Running entries are private.**
  Other demands use cycle policy.
  Partial values never leak.
  Diagnostics remain staged.
- **Publication is immutable.**
  Memo entries never mutate semantically.
  New revisions create new validation state.
  Replacements use new fingerprints.

### Cycles and fixed points

- **Acyclic queries fail on recursion.**
  Lexing and direct decoding qualify.
  Cycle traces name keys.
  Internal cycles are invariants.
- **SCC queries collect participants.**
  Declaration interfaces may recurse.
  Participants compute as a group.
  Publication occurs after convergence.
- **Fixed-point queries iterate deterministically.**
  Worklists use stable ordering.
  Widening rules are query-specific.
  Budgets bound nonconvergence.
- **Tabled solvers manage logical cycles.**
  Trait goals store provisional states.
  Coinduction is explicit.
  Overflow is a semantic outcome.
- **Cycle dependencies remain explainable.**
  SCC membership is recorded.
  Iteration counts are observable.
  Changed members invalidate the group.

### Incremental dependencies and invalidation

- **Input leaves start validation.**
  Changed fingerprints mark red roots.
  Unchanged leaves stay green.
  Host hints only prioritize work.
- **Dependencies validate lazily.**
  A query checks children when demanded.
  Equal child values preserve green status.
  Source-only changes may affect presentation.
- **Value fingerprints are semantic.**
  Local arena order is excluded.
  Source spans may use separate fingerprints.
  Diagnostic order is separate.
- **Durability controls early checks.**
  Compiler build inputs are high durability.
  Source bytes are low durability.
  Durability is optimization only.
- **Invalidation explanations retain first cause.**
  Store changed edge and old fingerprint.
  Trace to a direct input.
  Avoid overwhelming duplicate paths.

### Caching and persistence

- **Only eligible families persist.**
  Keys and values need canonical codecs.
  Validators must exist.
  Recovery products usually stay local.
- **Persistent hits still validate.**
  Schema and build identities match.
  Dependency manifest is checked.
  Structural invariants are rechecked.
- **Memo eviction preserves edges optionally.**
  Lightweight fingerprints may remain.
  Values can be dropped.
  Recompute uses the same key.
- **Negative results need deliberate policy.**
  Stable source errors may memoize.
  Resource exhaustion usually does not.
  Cancellation never persists.
- **Cache statistics are query-native.**
  Record hit source and validation cost.
  Distinguish memory and disk reuse.
  Expose rejected cache causes.

### Diagnostics and explanations

- **Query failures name the family.**
  Include typed key presentation.
  Include owning source declaration.
  Separate user and invariant failures.
- **Cycle diagnostics show the chain.**
  Mark legal and illegal recursion.
  Include solver policy.
  Avoid raw internal IDs.
- **Recovery diagnostics remain attached.**
  Consumers can present partial facts.
  Release roots reject incomplete status.
  Tooling explains uncertainty.
- **Recompilation explanations are query paths.**
  Show changed child fingerprints.
  End at input leaves.
  Include cache decisions.
- **Cost explanations expose hot queries.**
  Report wall-independent counters.
  Show iterations and allocations.
  Support self-host profiling.

### Cancellation, limits, and security

- **Frames check cancellation at safe points.**
  Child demands inherit tokens.
  Tight loops check bounded intervals.
  Cleanup discards staged state.
- **Each family declares budgets.**
  Solver steps differ from tokens.
  Parent budgets aggregate children.
  Limits remain request inputs.
- **Recursion depth is bounded.**
  Active stacks use explicit limits.
  SCC solvers avoid host stack growth.
  Overflow reports structured diagnostics.
- **Persistent values are untrusted.**
  Decoders validate typed graphs.
  Malformed keys reject.
  Cache records cannot inject dependencies.
- **Inspection redacts sensitive values.**
  Query graphs omit source bytes by default.
  Paths use logical labels.
  Cache keys reveal no secrets.

### Determinism and reproducibility

- **Scheduling order cannot affect values.**
  Query functions are semantically pure.
  Shared interners use canonical results.
  Worklists are ordered.
- **Memo state cannot affect artifacts.**
  Reused and recomputed values match.
  Cold and warm builds compare.
  Eviction is observationally invisible.
- **Cycle iteration is stable.**
  Participants use stable keys.
  Widening order is specified.
  Diagnostics sort canonically.
- **Tracing is deterministic when enabled.**
  Events use logical counters.
  Wall time is supplemental only.
  Trace output sorts completed records.
- **Family versions are explicit.**
  Algorithm changes invalidate caches.
  Old entries do not reinterpret.
  Bootstrap manifests record generations.

### Testing and observability

- **Unit tests cover frame transitions.**
  Absent, running, and complete states.
  Failure discards journals.
  Publication remains atomic.
- **Dependency tests inject hidden reads.**
  Audits detect unrecorded access.
  Query wrappers enforce reads.
  Invalidation matches expectations.
- **Cycle tests cover every policy.**
  Acyclic errors are stable.
  SCCs converge.
  Fixed points respect budgets.
- **Incremental tests mutate one input.**
  Expected queries rerun only.
  Equal values stop propagation.
  Explanations name the cause.
- **Performance tests use query counters.**
  Self-host runs expose hot families.
  Retained bytes are measured.
  Cache validation cost is tracked.

### Migration and completion criteria

- **Wrap current phase functions as queries.**
  Start without cross-revision reuse.
  Preserve diagnostics and products.
  Add typed keys incrementally.
- **Introduce input leaf queries.**
  Remove deep request reads.
  Record all direct dependencies.
  Test hidden-input absence.
- **Add memoization and tracing.**
  Reuse same-revision results first.
  Verify request-order independence.
  Measure memory.
- **Add red-green validation.**
  Introduce semantic fingerprints.
  Explain recomputation.
  Compare clean builds.
- **Complete when every semantic client shares queries.**
  No alternate compiler path remains.
  Recovery stays explicit.
  Bootstrap output ignores query order.

## 04. Stable Identity, Interning, and Typed Arenas

This section defines persistent and local identity spaces.
It separates stable semantic keys from compact arena indices.
It defines canonical interning and serialization remapping.
It protects incrementality from incidental allocation order.

### Purpose and scope

- **Name long-lived semantic entities.**
  Packages and definitions need stable keys.
  Bodies and instances need derived keys.
  Keys survive process boundaries when specified.
- **Keep local processing compact.**
  Tokens and expressions use dense IDs.
  MIR entities use typed arena indices.
  Local IDs never become global truth.
- **Canonicalize immutable semantic terms.**
  Types and goals share interned storage.
  Source spans stay outside equality.
  Inference terms remain local.
- **Support identity across edits.**
  Unrelated insertions preserve keys.
  Anonymous items use stable anchors.
  Ambiguity fails deterministically.
- **Support safe persistence.**
  Encoders remap local graphs.
  Decoders rebuild typed arenas.
  Schema generations protect meaning.

### Goals and non-goals

- **Goal: typed key spaces.**
  `DefKey` cannot become `TypeKey`.
  Conversions are explicit.
  Stale generations fail closed.
- **Goal: stable named identities.**
  Module paths and names dominate.
  Source order is only a disambiguator.
  Unrelated declarations do not churn.
- **Goal: efficient arenas.**
  Append-only allocation is cheap.
  Ranges are contiguous and typed.
  Borrowed views avoid copying.
- **Non-goal: immortal everything.**
  Large interned values may evict.
  Revision-local terms may expire.
  Identity does not require permanent memory.
- **Non-goal: text-offset identity alone.**
  Edits shift byte positions.
  Structural anchors provide resilience.
  Collisions receive explicit handling.

### Public queries and interfaces

- **`package_key`.**
  Canonicalize dependency identity.
  Exclude absolute checkout paths.
  Include source provenance generation.
- **`definition_key`.**
  Combine module and namespace.
  Include declaration kind and disambiguator.
  Produce stable diagnostics names.
- **`body_key`.**
  Derive from owning definition.
  Distinguish clauses and closures.
  Preserve stable syntax anchors.
- **`intern_type`.**
  Accept fully resolved semantic type.
  Return canonical `TypeKey`.
  Exclude inference variables.
- **`identity_diff`.**
  Compare two revisions.
  Explain preserved and replaced identities.
  Report ambiguous matches.

### Primary data structures

- **`StableKey<Tag>`.**
  Stores canonical digest or tuple.
  Carries a phantom identity tag.
  Supports stable serialization.
- **`Id<Tag>`.**
  Stores compact local index.
  Requires the owning arena.
  Never serializes directly.
- **`IdRange<Tag>`.**
  Stores typed start and count.
  Represents contiguous children.
  Validates bounds once.
- **`Arena<Tag, T>`.**
  Owns append-only values.
  Supports marks and rollback.
  Returns borrowed typed views.
- **`Interner<Key, Value>`.**
  Maps semantic values canonically.
  Stores content fingerprints.
  Supports deterministic freeze.

### Ownership and lifetime model

- **Stable keys are value-owned.**
  They contain no borrowed pointers.
  They may cross requests.
  Their algorithm is versioned.
- **Arenas own local values.**
  IDs borrow meaning from arenas.
  Dropping the arena invalidates IDs.
  Owner generations catch stale use.
- **Body sessions own inference terms.**
  Unification variables stay local.
  Zonked types enter interners.
  Unresolved terms never persist.
- **Database owns canonical interners.**
  Published immutable values may share.
  Eviction preserves stable reconstruction.
  Mutation is synchronized by ownership.
- **Encoders own remap tables.**
  Artifact-local indices are temporary.
  Serialization scratch dies afterward.
  Stable products carry canonical order.

### Algorithms and phase order

- **Build stable package identities first.**
  Normalize dependency sources.
  Hash canonical package metadata.
  Detect duplicate identities.
- **Assign module identities structurally.**
  Use logical module paths.
  Validate inline and external ownership.
  Exclude source enumeration order.
- **Assign declaration identities.**
  Group by namespace and name.
  Apply deterministic disambiguation.
  Record source anchors.
- **Allocate local arenas during queries.**
  Use typed marks for child ranges.
  Roll back failed speculative work.
  Publish immutable products.
- **Freeze for persistence.**
  Traverse semantic dependency order.
  Remap local IDs canonically.
  Write versioned stable records.

### Semantic invariants

- **Stable keys contain stable components.**
  No memory addresses appear.
  No wall-clock values appear.
  Algorithm generation is explicit.
- **Local IDs require an owner.**
  Raw integers never cross APIs.
  Bounds checks use the correct arena.
  Mixed tags fail to type-check.
- **Interned equality ignores source spans.**
  Equivalent types share identity.
  Diagnostic origins remain side data.
  Local inference state is excluded.
- **Anonymous identity never relies solely on ordinal.**
  Structural context participates.
  Insertions minimize downstream churn.
  Collisions are detectable.
- **Persistent graphs validate all references.**
  Every index is in range.
  Required topological relationships hold.
  Unknown tags reject.

### Cycles and fixed points

- **Recursive semantic types use placeholders.**
  Allocate nominal identity first.
  Fill validated structure later.
  Infinite structural expansion is avoided.
- **Interner recursion is guarded.**
  Canonicalization tracks active terms.
  Illegal cycles report invariants.
  Nominal cycles remain representable.
- **Identity matching across edits may be ambiguous.**
  Candidate matching uses stable context.
  Ties produce replacement identities.
  No silent incorrect reuse occurs.
- **Arena ownership graph stays acyclic.**
  Parent products may reference children.
  Children do not own parents.
  Borrowed views avoid shared ownership cycles.
- **Serialization SCCs use canonical ordering.**
  Recursive records receive stable local indices.
  Ordering follows semantic keys.
  Decoding reconstructs the cycle safely.

### Incremental dependencies and invalidation

- **Named definition keys stabilize queries.**
  Body edits preserve header identities.
  Unrelated declarations stay green.
  Renames intentionally replace keys.
- **Anonymous anchors narrow churn.**
  Nearby edits may preserve identities.
  Structural moves can replace them.
  Identity diffs explain decisions.
- **Interner fingerprints stop propagation.**
  Recomputed types may remain equal.
  Downstream queries stay green.
  Span-only changes use separate facts.
- **Arena allocation never invalidates externally.**
  Local order is absent from fingerprints.
  Canonical encoders remap every graph.
  Rebuilds may allocate differently.
- **Identity algorithm changes are global inputs.**
  Cache generations advance.
  Old stable keys do not reinterpret.
  Migration tools may map explicitly.

### Caching and persistence

- **Stable keys may enter cache keys.**
  Their schema is versioned.
  Package identities remain canonical.
  Process generations are excluded.
- **Local arenas require canonical codecs.**
  Encode records and remap tables.
  Decode into fresh arenas.
  Validate every edge.
- **Interners may persist frozen tables.**
  Values sort by canonical bytes.
  Runtime hash-table shape is excluded.
  Loading rebuilds efficient maps.
- **Weak interning is allowed.**
  Evicted values reconstruct identically.
  Stable keys remain content-derived.
  Memory policy cannot change semantics.
- **Identity provenance may persist for tooling.**
  Store prior anchors and owners.
  Avoid absolute host paths.
  Redact private source content.

### Diagnostics and explanations

- **Type mismatches print semantic forms.**
  Interned IDs never appear alone.
  Stable names remain human-readable.
  Source spans are attached separately.
- **Stale-ID diagnostics name the owner.**
  Show expected arena generation.
  Show observed generation.
  Treat as internal failure.
- **Identity-diff reports explain replacements.**
  Name changed owner or namespace.
  Show anchor ambiguity.
  Support incremental debugging.
- **Collision diagnostics are deterministic.**
  Report all colliding declarations.
  Show chosen disambiguators.
  Never depend on map iteration.
- **Decoder diagnostics cite record paths.**
  Name malformed indices.
  Include schema generation.
  Classify corruption separately.

### Cancellation, limits, and security

- **Arena allocation is budgeted.**
  Each owner tracks element counts.
  Overflow fails before allocation.
  Rollback releases speculative growth.
- **Key construction limits path depth.**
  Malicious module nesting is bounded.
  Digest input size is checked.
  Recursion uses explicit stacks.
- **Interners resist amplification.**
  Large values charge memory budgets.
  Duplicate probes remain bounded.
  Hash collision behavior is controlled.
- **Decoded IDs are hostile.**
  Range checks precede indexing.
  Tag mismatches reject.
  Cyclic graphs use bounded validation.
- **Stable keys reveal minimal information.**
  Digests avoid embedding source bytes.
  Logical names follow visibility policy.
  Cache sharing respects privacy.

### Determinism and reproducibility

- **Disambiguation uses canonical order.**
  Sort by semantic source keys.
  Avoid host enumeration order.
  Duplicate diagnostics are stable.
- **Interner insertion order is irrelevant.**
  Semantic equality determines keys.
  Frozen serialization sorts values.
  Artifacts remain byte-identical.
- **Arena marks are local only.**
  Different allocation paths may occur.
  Published fingerprints remain equal.
  Tests randomize insertion order.
- **Identity algorithms are specified.**
  Inputs and encoding are documented.
  Versions enter build identity.
  Bootstrap stages use the same generation.
- **Decoder reconstruction is canonical.**
  Equivalent bytes yield equal values.
  Map shapes remain unobservable.
  Re-encoding reproduces canonical bytes.

### Testing and observability

- **Type-safety tests attempt mixed IDs.**
  APIs should reject compilation.
  Unsafe casts remain absent.
  Runtime checks cover decoded data.
- **Edit tests preserve stable definitions.**
  Insert unrelated declarations.
  Move bodies and comments.
  Inspect identity diffs.
- **Anonymous-anchor tests stress insertions.**
  Add closures before existing closures.
  Reorder handler clauses.
  Verify intended churn only.
- **Serialization tests randomize arenas.**
  Canonical bytes remain equal.
  Decoders validate hostile indices.
  Round trips preserve semantic keys.
- **Memory tests inspect interner retention.**
  Compile many revisions.
  Evict unpinned values.
  Ensure reconstruction remains equal.

### Migration and completion criteria

- **Wrap raw indices with typed newtypes.**
  Begin at phase boundaries.
  Remove implicit conversions.
  Add compile-time misuse tests.
- **Introduce shared arena substrate.**
  Replace duplicated range types.
  Add marks and typed slices.
  Preserve snapshot parity.
- **Separate spans from semantic equality.**
  Refactor type and goal records.
  Add side tables.
  Compare diagnostics.
- **Add stable declaration identities.**
  Drive queries and references.
  Build identity-diff tooling.
  Test editor edits.
- **Complete when allocation order is unobservable.**
  Cache and artifact bytes are canonical.
  Stale IDs fail closed.
  Incremental churn is explainable.

## 05. Dependency Tracking and Invalidation

This section defines change propagation through the compiler database.
Dependencies are semantic observations, not guessed file relationships.
Invalidation is narrow, typed, and explainable.
Equal recomputed values stop downstream work.

### Purpose and scope

- **Record every dependency class.**
  Source, interface, solver, and target edges count.
  Presentation dependencies remain separate.
  Hidden dependencies are forbidden.
- **Determine reuse after edits.**
  Changed inputs begin validation.
  Unchanged semantic values remain green.
  Downstream work is avoided safely.
- **Explain every recomputation.**
  Trace red edges to direct inputs.
  Name changed fingerprints.
  Surface broad invalidation bugs.
- **Support cross-package incrementality.**
  Interfaces isolate private changes.
  Generic bodies add precise edges.
  Artifacts depend on selected instances.
- **Support editor latency.**
  Small edits touch small query regions.
  Presentation facts update quickly.
  Obsolete work cancels.

### Goals and non-goals

- **Goal: correctness-first dependencies.**
  Over-invalidation is acceptable initially.
  Under-invalidation is never acceptable.
  Audits detect missing reads.
- **Goal: semantic fingerprints.**
  Values compare independent of allocation.
  Equal outputs stop propagation.
  Span changes use separate channels.
- **Goal: typed edge reasons.**
  Edges name their semantic role.
  Explanations remain useful.
  Policies can optimize by class.
- **Non-goal: timestamp builds.**
  Modification time proves nothing.
  Content and query facts decide.
  Host hints only schedule checks.
- **Non-goal: global cache flushing.**
  Compiler changes use generations.
  Source edits remain granular.
  Unrelated packages stay reusable.

### Public queries and interfaces

- **`record_dependency`.**
  Append a typed observed edge.
  Store child fingerprint.
  Reject cross-snapshot targets.
- **`validate_entry`.**
  Check previous dependency observations.
  Recompute changed children lazily.
  Return green or red reason.
- **`fingerprint_value`.**
  Produce canonical semantic digest.
  Separate source and presentation variants.
  Exclude local IDs.
- **`invalidation_trace`.**
  Walk first changed path.
  Include edge classes.
  Produce stable human output.
- **`expected_impact`.**
  Simulate changed input categories.
  Use recorded graph only.
  Support compiler performance tests.

### Primary data structures

- **`DependencySet`.**
  Stores ordered observed edges.
  Deduplicates equivalent reads.
  Freezes on publication.
- **`DependencyKind`.**
  Distinguishes semantic and presentation edges.
  Marks target and capability dependence.
  Guides invalidation projections.
- **`ValueFingerprintSet`.**
  Stores semantic and auxiliary digests.
  Supports selective equality.
  Is schema-versioned.
- **`ValidationState`.**
  Tracks unchecked, green, or red.
  Stores first red reason.
  Prevents duplicate work.
- **`RevisionChangeSet`.**
  Summarizes known direct changes.
  Is verified against input identities.
  Never replaces dependency validation.

### Ownership and lifetime model

- **Memo entries own frozen dependencies.**
  Consumers cannot mutate them.
  Eviction may drop details.
  Lightweight summaries may remain.
- **Validation frames own temporary states.**
  They avoid recursive duplication.
  Cancellation discards pending results.
  Publication updates atomically.
- **Revision records own direct change sets.**
  Parent relation is advisory.
  Content identities remain authoritative.
  Compaction may remove old chains.
- **Explanation products are derived.**
  They borrow graph snapshots.
  They may be regenerated.
  They do not pin large values.
- **Persistent manifests own external edges.**
  Cache records list required fingerprints.
  Imported edges are validated.
  Local memo graphs stay process-owned.

### Algorithms and phase order

- **Start from direct input differences.**
  Compare normalized world projections.
  Mark changed leaf fingerprints.
  Seed validation queues.
- **Validate a demanded parent.**
  Visit dependencies in stable order.
  Reuse green children.
  Stop on first relevant red edge.
- **Recompute red entries.**
  Run the typed query normally.
  Produce new value fingerprints.
  Compare old and new outputs.
- **Stop propagation on equality.**
  Mark new entry green-equivalent.
  Preserve updated source metadata separately.
  Avoid downstream recomputation.
- **Publish explanation metadata.**
  Record changed edge and cause.
  Store recomputation statistics.
  Expose broad fanout.

### Semantic invariants

- **Observed reads define dependencies.**
  Static guesswork is insufficient.
  Query wrappers capture every read.
  Direct global access is prohibited.
- **Fingerprint equality matches consumer needs.**
  Semantic consumers use semantic digest.
  Tooling may use source digest.
  Diagnostics may use presentation digest.
- **Red-green state is revision-qualified.**
  Green in one world proves nothing elsewhere.
  Parent relationships aid validation only.
  Generation-safe keys are mandatory.
- **Dependency order does not affect truth.**
  It only affects early exit.
  Canonical ordering stabilizes traces.
  Complete validation remains equivalent.
- **Change hints never establish reuse.**
  Host file lists are advisory.
  Query fingerprints confirm equality.
  Missing hints cannot cause stale results.

### Cycles and fixed points

- **SCC entries validate as groups.**
  A changed member may affect all members.
  Group fingerprints summarize outputs.
  Equal convergence can stop propagation.
- **Validation recursion uses explicit states.**
  Running validation detects cycles.
  Query cycle policy decides handling.
  Infinite recursion is avoided.
- **Trait tables expose logical dependencies.**
  Goals depend on relevant impl sets.
  Coinductive cycles stay solver-owned.
  External graph records solver summary.
- **Call-summary cycles use SCC fingerprints.**
  Recursive functions form stable groups.
  Widening results are fingerprinted.
  Instance changes invalidate the group.
- **Explanation cycles are collapsed.**
  Reports show SCC nodes once.
  Stable representatives prevent loops.
  Users receive finite traces.

### Incremental dependencies and invalidation

- **Body text affects body syntax first.**
  Header keys may remain unchanged.
  Interface consumers stay green.
  Body-dependent callers rerun as needed.
- **Private implementation changes stay local.**
  Export fingerprints remain equal.
  Downstream packages reuse interfaces.
  Link artifacts may still change.
- **Trait implementation changes affect selected goals.**
  Solver records candidate-set dependencies.
  Unrelated goals stay green.
  Coherence changes may broaden impact.
- **Fixity changes affect parsed operator streams.**
  Only bodies using the operator depend.
  Tokenization may remain green.
  Semantic grouping reruns.
- **Target changes begin after target-neutral phases.**
  Source semantics may reuse.
  Layout and emission rerun.
  Capability manifests invalidate host checks.

### Caching and persistence

- **Persistent entries store dependency manifests.**
  Child keys and fingerprints are canonical.
  Missing dependencies invalidate reuse.
  Unknown kinds reject.
- **Graph summaries may persist separately.**
  Full values can evict.
  Validation may remain cheap.
  Schema changes clear summaries.
- **Cross-machine reuse requires stable identities.**
  Paths are logical.
  Compiler generations match.
  Target identities are exact.
- **Negative dependency results may persist.**
  Stable missing declarations qualify.
  Cancellation never qualifies.
  Limit exhaustion needs policy.
- **Cache import cannot add trusted edges.**
  Manifest edges are revalidated.
  Decoders check key types.
  Query execution remains authoritative.

### Diagnostics and explanations

- **`why_recompiled` shows one causal path.**
  Start at requested root.
  Follow changed observations.
  End at direct input.
- **Impact reports show fanout.**
  Count invalidated queries by family.
  Highlight unexpectedly broad edges.
  Support regression thresholds.
- **Fingerprint reports show component differences.**
  Name semantic versus source changes.
  Avoid dumping opaque hashes only.
  Include owning declarations.
- **Missing-edge audits produce invariants.**
  Compare instrumented recomputation outcomes.
  Report stale reuse hazards.
  Block unsafe optimization.
- **User diagnostics avoid incremental jargon.**
  Rebuild explanations are opt-in.
  Ordinary source errors stay focused.
  Developer tools show full detail.

### Cancellation, limits, and security

- **Validation checks cancellation.**
  Long dependency walks stop.
  Green entries remain valid.
  Partial red states do not publish.
- **Fanout walks use limits.**
  Explanation graphs may be huge.
  Reports truncate deterministically.
  Core validation remains complete.
- **Hostile manifests are bounded.**
  Dependency counts are checked.
  Duplicate edges reject.
  Graph cycles use safe algorithms.
- **Fingerprints use collision-resistant digests.**
  Equality may confirm canonical bytes.
  Security policy is versioned.
  Cache poisoning fails closed.
- **Private source boundaries remain respected.**
  Explanations redact hidden paths.
  Cross-package reports use public identities.
  Remote caches reveal minimal metadata.

### Determinism and reproducibility

- **Dependency sets freeze canonically.**
  Sort by family and key.
  Deduplicate in stable order.
  Trace output remains reproducible.
- **Validation order is specified.**
  Stable order finds stable first cause.
  Parallelism cannot change result.
  Statistics remain comparable.
- **Fingerprints are canonical encodings.**
  Map shape is excluded.
  Local IDs are remapped.
  Algorithm generations are included.
- **Change-set production is deterministic.**
  Parent comparisons use stable ordering.
  Equivalent worlds yield empty changes.
  Host enumeration does not leak.
- **Clean and incremental builds match.**
  Artifacts and diagnostics compare.
  Query traces may differ only in reuse events.
  Semantic products remain equal.

### Testing and observability

- **Golden invalidation tests cover edits.**
  Body, header, and fixity edits.
  Trait and target edits.
  Capability and lint edits.
- **Clean-build differential tests run always.**
  Incremental outputs match fresh outputs.
  Random edit sequences are replayed.
  Mismatches localize by query.
- **Dependency-audit mode recomputes samples.**
  Compare reused and fresh values.
  Detect missing edges.
  Record offending query family.
- **Fanout benchmarks track regressions.**
  Measure queries rerun per edit.
  Set expected ceilings.
  Inspect first broad edge.
- **Graph inspectors support filtering.**
  Filter by package and body.
  Filter by dependency kind.
  Export machine-readable records.

### Migration and completion criteria

- **Instrument existing phase reads.**
  Wrap source and interface access.
  Record coarse dependencies first.
  Verify no stale results.
- **Introduce semantic fingerprints.**
  Start with canonical serialized values.
  Optimize hashing later.
  Compare collision-safe bytes.
- **Add red-green validation.**
  Reuse same-family results.
  Stop on equal outputs.
  Build explanation traces.
- **Narrow coarse edges iteratively.**
  Split package-wide dependencies.
  Add solver and fixity detail.
  Measure fanout reductions.
- **Complete when incremental equals clean.**
  Random histories pass.
  Every rerun is explainable.
  Cross-package private edits stay local.

## 06. Caching, Persistence, Eviction, and Schema Evolution

This section defines reusable compiler storage across processes.
Caches are performance hints, never semantic authorities.
Every record is content-addressed, versioned, validated, and disposable.
Eviction changes latency only.

### Purpose and scope

- **Persist expensive compiler products.**
  Interfaces, Core, MIR, and fragments qualify.
  Complete artifacts may qualify.
  Temporary sessions never qualify.
- **Separate memory and disk caching.**
  In-memory memoization serves live queries.
  Persistent records serve future processes.
  Policies remain independently tunable.
- **Define canonical cache keys.**
  Include every relevant input identity.
  Exclude local paths and timestamps.
  Include codec and algorithm generations.
- **Define defensive loading.**
  Returned bytes are hostile.
  Checksums and schemas are validated.
  Structural validators reconstruct trust.
- **Define schema evolution.**
  Old records reject or migrate explicitly.
  Silent reinterpretation is forbidden.
  Release tooling reports compatibility.

### Goals and non-goals

- **Goal: cold and warm equivalence.**
  Cache hits cannot change output.
  Recomputed products compare equal.
  Tests enforce byte identity.
- **Goal: bounded storage.**
  Eviction uses explicit policies.
  Large products report size.
  Pinned entries resist removal only deliberately.
- **Goal: useful provenance.**
  Records name producer build.
  Validation failures are inspectable.
  Cache decisions are explainable.
- **Non-goal: trusting remote caches.**
  Signatures may add provenance.
  Validation remains mandatory.
  Network origin grants no authority.
- **Non-goal: preserving every internal object.**
  Only stable products persist.
  Query frames and builders do not.
  Local pointers never serialize.

### Public queries and interfaces

- **`cache_key`.**
  Canonicalize family and semantic key.
  Include complete projected inputs.
  Return content-addressed digest.
- **`load_record`.**
  Retrieve bytes by digest.
  Enforce maximum size.
  Return untrusted payload.
- **`decode_and_validate`.**
  Check envelope and checksum.
  Rebuild typed graph.
  Return complete immutable product.
- **`store_record`.**
  Encode canonical product.
  Write atomically by digest.
  Return storage metadata.
- **`cache_explain`.**
  Report miss or rejection reason.
  Show key component differences.
  Redact sensitive inputs.

### Primary data structures

- **`CacheEnvelope`.**
  Stores schema and family.
  Stores producer build identity.
  Stores payload checksum and size.
- **`PersistentCacheKey`.**
  Contains canonical query identity.
  Contains projected dependency digest.
  Contains target when relevant.
- **`CacheRecordManifest`.**
  Lists child fingerprints.
  Lists validation feature requirements.
  Lists optional provenance.
- **`CacheIndex`.**
  Maps logical lookup to content digest.
  Is replaceable and rebuildable.
  Never proves payload validity.
- **`EvictionMetadata`.**
  Tracks size and recent use.
  Uses deterministic policy inputs.
  Is semantically irrelevant.

### Ownership and lifetime model

- **Cache adapter owns storage handles.**
  Semantic code requests bytes.
  It never reads paths directly.
  Adapter failures are recoverable.
- **Decoder owns temporary buffers.**
  Validated products move into arenas.
  Malformed buffers release promptly.
  No borrowed cache bytes escape.
- **Database owns loaded products.**
  Memo entries reference immutable values.
  Eviction coordinates with active borrows.
  Snapshots do not own storage files.
- **Encoder owns canonical remapping.**
  It traverses published values.
  Scratch dies after atomic write.
  Partial files remain invisible.
- **Index lifetime differs from records.**
  Lost index can rebuild.
  Orphan records may evict.
  Content digests remain authoritative.

### Algorithms and phase order

- **Construct the complete key.**
  Gather query family generation.
  Gather semantic input projections.
  Gather target and optimizer identities.
- **Probe memory cache first.**
  Validate revision suitability.
  Return immutable memoized value.
  Record hit statistics.
- **Probe persistent index second.**
  Retrieve candidate digest.
  Load envelope under size limits.
  Reject unknown critical features.
- **Decode and validate payload.**
  Check checksum before graph allocation.
  Validate indices and invariants.
  Compare dependency manifest.
- **Recompute and store on miss.**
  Publish semantic value first.
  Encode canonical bytes afterward.
  Write content record atomically.

### Semantic invariants

- **Cache absence never changes semantics.**
  Every product is recomputable.
  Missing storage is normal.
  Errors cannot force acceptance.
- **Cache presence never proves correctness.**
  Validation reconstructs typed authority.
  Producer identity is insufficient.
  Remote signatures remain supplemental.
- **Keys include all relevant inputs.**
  Hidden dependencies are forbidden.
  Family generations invalidate algorithms.
  Target-neutral values exclude targets.
- **Payloads are immutable.**
  Content digest names exact bytes.
  Updates create new records.
  Indices may repoint atomically.
- **Recovered values are policy-controlled.**
  Release cache usually excludes them.
  IDE-local caches mark recovery.
  Status cannot disappear on load.

### Cycles and fixed points

- **Recursive graphs encode explicit tables.**
  Local indices handle cycles.
  Decoder validates strongly connected records.
  Depth limits avoid stack exhaustion.
- **Record dependency cycles are allowed only semantically.**
  Manifests may reference SCC members.
  Group records can package fixed points.
  Missing members invalidate the group.
- **Index rebuild avoids recursive trust.**
  Scan envelopes under limits.
  Verify digests independently.
  Ignore malformed records.
- **Migration chains are bounded.**
  At most explicit supported versions.
  Multiple silent upgrades are forbidden.
  Old data may simply miss.
- **Eviction references cannot form pins accidentally.**
  Metadata points weakly to records.
  Active memo entries hold explicit pins.
  Cycles break on request completion.

### Incremental dependencies and invalidation

- **Cache keys reuse semantic fingerprints.**
  Equal outputs share records.
  Source-only changes may miss tooling caches.
  Code generation may still hit.
- **Dependency interfaces isolate packages.**
  Private changes preserve downstream keys.
  Export changes produce new keys.
  Generic bodies add body fingerprints.
- **Compiler upgrades advance generations.**
  Compatible codecs may remain readable.
  Semantic algorithm changes force misses.
  Migration is explicit.
- **Target changes affect target products only.**
  Parsing and typing caches may reuse.
  Layout and emission keys differ.
  Runtime capability keys differ.
- **Limit changes matter when observed.**
  Records note relevant budget use.
  Safe larger limits may reuse.
  Exhaustion results usually recompute.

### Caching and persistence

- **Use content-addressed record storage.**
  Duplicate products share bytes.
  Checksums detect corruption.
  Atomic rename publishes records.
- **Use separate namespaces by family.**
  Simplify eviction and debugging.
  Prevent type confusion.
  Apply family-specific size ceilings.
- **Use manifests for final artifacts.**
  Record complete build world.
  Store verification generation separately.
  Reverify when required.
- **Use deterministic LRU or clock policy.**
  Tie breaks use stable keys.
  Policy affects storage only.
  Tests avoid timing assumptions.
- **Support explicit cache cleaning.**
  `grand clean --cache` removes indexes.
  Corrupt quarantines are inspectable.
  Shared caches respect permissions.

### Diagnostics and explanations

- **Miss explanations list key differences.**
  Show changed compiler generation.
  Show changed dependency fingerprint.
  Avoid opaque hash-only output.
- **Corruption diagnostics name the record.**
  Include envelope and payload location.
  Classify as cache corruption.
  Continue by recomputing when safe.
- **Schema diagnostics show supported versions.**
  Report unknown critical features.
  Explain migration availability.
  Avoid source-error codes.
- **Validation diagnostics show invariant path.**
  Name malformed type or block.
  Redact raw source bytes.
  Preserve developer detail.
- **Eviction reports show reclaimed categories.**
  Count records and bytes.
  Show pinned blockers.
  Support memory investigations.

### Cancellation, limits, and security

- **Loads enforce envelope size first.**
  Reject allocation amplification.
  Stream checksum where possible.
  Bound decompression ratios.
- **Decoders charge structural budgets.**
  Nodes and edges are counted.
  Recursion uses explicit worklists.
  Cancellation stops validation.
- **Writes stage privately.**
  Cancellation removes temporary records.
  Partial indexes never publish.
  Crash recovery ignores temp files.
- **Remote transport is untrusted.**
  TLS does not replace validation.
  Signatures prove producer only.
  Poisoned records fail closed.
- **Cache paths avoid secret disclosure.**
  Keys use digests.
  Logical names are optional metadata.
  Permissions protect local records.

### Determinism and reproducibility

- **Canonical encoding defines content identity.**
  Sort maps and sets.
  Remap local IDs.
  Normalize optional fields.
- **Compression settings are fixed.**
  If compression is used.
  Version its algorithm and parameters.
  Avoid nondeterministic timestamps.
- **Eviction cannot affect build output.**
  Only reuse behavior changes.
  Clean and warm builds compare.
  Cache statistics remain external.
- **Record manifests sort dependencies.**
  Stable ordering aids diffing.
  Duplicate edges reject.
  Hashes reproduce across machines.
- **Cache migrations are deterministic.**
  Equivalent old records map equally.
  New encoding is canonical.
  Tests compare converted bytes.

### Testing and observability

- **Cold-warm differential tests are mandatory.**
  Compare artifacts and diagnostics.
  Compare phase fingerprints.
  Run across edit histories.
- **Corruption fuzzing targets every family.**
  Mutate lengths and tags.
  Truncate payloads.
  Inject extreme graph shapes.
- **Schema compatibility tests use fixtures.**
  Read supported old versions.
  Reject unsupported critical changes.
  Re-encode canonically.
- **Eviction stress tests use small budgets.**
  Force repeated loads.
  Verify semantic stability.
  Inspect pin leaks.
- **Cache traces expose decisions.**
  Record memory hit and disk hit.
  Record validation rejection.
  Attribute encode and decode cost.

### Migration and completion criteria

- **Start with artifact caching.**
  Complete build manifests already exist.
  Add validation and cold-warm tests.
  Keep semantic caches disabled.
- **Add interface record persistence.**
  Canonicalize exported facts.
  Harden decoder.
  Enable cross-package reuse.
- **Add selected body products.**
  Typed Core and MIR follow.
  Require canonical codecs.
  Measure size and benefit.
- **Add eviction and explanations.**
  Bound long-lived services.
  Expose rejected hits.
  Test clean equivalence.
- **Complete when cache deletion is harmless.**
  Any record can recompute.
  Corruption cannot change success.
  Bootstrap output ignores cache state.

## 07. Determinism and Reproducibility

This section defines canonical externally visible behavior.
Internal allocation may remain efficient and noncanonical.
Every serialized product and diagnostic order is specified.
Bootstrap convergence depends on this discipline.

### Purpose and scope

- **Define deterministic boundary products.**
  Interfaces and artifacts must match.
  Diagnostics and manifests must match.
  Verification outcomes must match.
- **Separate construction from publication order.**
  Arenas allocate efficiently.
  Freeze steps sort externally visible records.
  Local order remains private.
- **Define reproducible build inputs.**
  Complete manifests name every influence.
  Host state is excluded.
  Toolchain generations are recorded.
- **Support bootstrap byte identity.**
  Stage two and three compare exactly.
  Differences localize by phase.
  Equivalent execution is insufficient.
- **Support future parallelism.**
  Scheduling cannot alter output.
  Stable worklists and tie breaks are required.
  Tests randomize execution order.

### Goals and non-goals

- **Goal: byte-identical artifacts.**
  Same world yields same `.grbc`.
  Cache warmth is irrelevant.
  Machine path is irrelevant.
- **Goal: stable diagnostics.**
  Error ordering and wording are deterministic.
  Related labels sort stably.
  Presentation options remain explicit.
- **Goal: deterministic optimization.**
  Cost models avoid wall time.
  Pass ordering is fixed.
  Equal candidates use stable tie breaks.
- **Non-goal: canonical internal allocation.**
  Hash maps may be efficient.
  Arena IDs may differ.
  Freeze removes incidental order.
- **Non-goal: identical performance traces.**
  Wall-clock timing naturally varies.
  Logical counters remain comparable.
  Output bytes remain fixed.

### Public queries and interfaces

- **`canonical_interface`.**
  Freeze exported semantic facts.
  Sort declarations and implementations.
  Emit stable schema bytes.
- **`canonical_artifact`.**
  Freeze pools and functions.
  Patch indices after sorting.
  Produce exact `.grbc` bytes.
- **`determinism_manifest`.**
  Record algorithm generations.
  Record canonical ordering rules.
  Record phase fingerprints.
- **`compare_builds`.**
  Compare product fingerprints.
  Locate first differing phase.
  Produce structured difference report.
- **`bootstrap_compare`.**
  Compare stage two and three.
  Require byte equality.
  Retain differing section evidence.

### Primary data structures

- **`CanonicalPool<Key, Value>`.**
  Collect values in arbitrary order.
  Freeze by canonical key.
  Produce old-to-new remap.
- **`StableOrderKey`.**
  Combines source and semantic identity.
  Excludes allocation addresses.
  Defines deterministic ties.
- **`PhaseFingerprint`.**
  Names one semantic product.
  Uses canonical encoding.
  Supports first-difference localization.
- **`BuildManifest`.**
  Records normalized input world.
  Records compiler and schema generations.
  Records output checksums.
- **`DeterminismReport`.**
  Stores compared products.
  Stores mismatch class and path.
  Is machine-readable.

### Ownership and lifetime model

- **Construction contexts own unordered data.**
  Mutation remains phase-local.
  No consumer observes map iteration.
  Freeze creates immutable products.
- **Freeze contexts own remap tables.**
  They translate local identities.
  Scratch disappears after publication.
  Canonical bytes remain.
- **Manifests own stable provenance.**
  They avoid host-specific paths.
  They may persist with artifacts.
  They remain immutable.
- **Comparison sessions borrow products.**
  They create compact difference records.
  They do not retain full duplicate graphs.
  Cleanup releases temporary decoding.
- **Diagnostics own canonical presentation records.**
  Sorting occurs before rendering.
  Clients may choose formatting.
  Semantic order remains fixed.

### Algorithms and phase order

- **Normalize inputs first.**
  Sort package and source records.
  Normalize logical paths.
  Encode options canonically.
- **Compute semantic products independently.**
  Allocation order may vary.
  Query scheduling may vary.
  Product equality remains semantic.
- **Freeze every boundary product.**
  Sort keys and deduplicate.
  Remap local indices.
  Normalize optional records.
- **Serialize with fixed encodings.**
  Endianness and widths are specified.
  No timestamps enter bytes.
  Feature ordering is canonical.
- **Compare phase fingerprints.**
  On mismatch, find earliest phase.
  Then compare structured records.
  Preserve reproducible fixtures.

### Semantic invariants

- **Same normalized world means same output.**
  Request history cannot matter.
  Cache state cannot matter.
  Memory layout cannot matter.
- **Maps never directly serialize.**
  Keys are frozen first.
  Iteration order remains private.
  Tests audit encoders.
- **Diagnostics are sorted after collection.**
  Reporting order cannot depend on traversal.
  Stable codes break ties.
  Related labels follow stable order.
- **Optimization decisions use deterministic facts.**
  No wall-clock thresholds.
  No randomized heuristics.
  Stable costs and ties only.
- **Bootstrap stages use identical manifests.**
  Compiler executable differs by stage.
  Inputs and options do not.
  Stage identity is recorded separately.

### Cycles and fixed points

- **Fixed-point worklists use stable queues.**
  Block and goal ordering is defined.
  Duplicate insertion is deterministic.
  Convergence result is schedule-independent.
- **SCC representatives are canonical.**
  Choose smallest stable key.
  Sort members before processing.
  Serialize groups consistently.
- **Recursive serialization uses stable local indices.**
  Traverse canonical roots.
  Assign indices deterministically.
  Validate re-encoding.
- **Optimizer pass loops have fixed budgets.**
  Iteration counts are deterministic.
  Early exits use semantic conditions.
  Remarks sort by pass order.
- **Diagnostic cause cycles collapse stably.**
  Choose canonical cycle root.
  Show each member once.
  Avoid traversal-dependent output.

### Incremental dependencies and invalidation

- **Determinism rules enter build identity.**
  Changing canonical order advances generation.
  Old caches miss safely.
  Artifacts do not reinterpret.
- **Span-only changes affect mapped products.**
  Semantic Core may remain equal.
  Source maps and diagnostics rerun.
  Code bytes may stay stable.
- **Query scheduling changes are irrelevant.**
  Memoized values are immutable.
  Freeze sorts products.
  Clean builds verify equality.
- **Optimizer version changes affect later phases.**
  Frontend caches may reuse.
  Optimized MIR and artifacts rerun.
  Manifest records version.
- **Presentation settings remain separated.**
  Color and width do not alter semantic records.
  Rendered text may differ explicitly.
  JSON output stays canonical.

### Caching and persistence

- **Cache keys use canonical manifests.**
  Equivalent inputs share records.
  Host paths are excluded.
  Ordering differences collapse.
- **Cached values re-encode identically.**
  Decode and freeze yields same bytes.
  Local arena order may change.
  Semantic digest remains equal.
- **Artifact caches store canonical bytes.**
  Complete manifest accompanies them.
  Verification generation is recorded.
  Warm reuse preserves checksum.
- **Comparison fixtures persist first differences.**
  Store compact canonical slices.
  Avoid enormous opaque binaries.
  Support regression replay.
- **Cache metadata is not serialized into products.**
  Hit counts remain external.
  Last-access time affects eviction only.
  Build bytes remain clean.

### Diagnostics and explanations

- **Mismatch reports name the first phase.**
  Show old and new fingerprints.
  Link to structured product differences.
  Avoid only reporting final checksum.
- **Ordering violations identify the encoder.**
  Show unstable key sequence.
  Include query or pass owner.
  Produce an internal diagnostic.
- **Bootstrap mismatches name stages.**
  Include producing compiler checksums.
  Include canonical manifest checksum.
  Preserve differing artifact section.
- **Nondeterminism audits show varying facts.**
  Compare repeated runs.
  Highlight allocation-derived fields.
  Suggest missing freeze steps.
- **User-facing output remains stable.**
  Source diagnostics avoid internal hashes.
  Developer mode exposes them.
  Codes remain release contracts.

### Cancellation, limits, and security

- **Cancellation cannot publish unstable subsets.**
  Freeze commits atomically.
  Partial ordering tables discard.
  Prior complete products remain.
- **Canonical sorting has explicit limits.**
  Record counts charge budgets.
  Comparator recursion is bounded.
  Oversized products fail structurally.
- **Digests use approved algorithms.**
  Algorithm generation is explicit.
  Collision policy is documented.
  Security upgrades invalidate caches.
- **Manifests avoid secret environment data.**
  Only normalized logical values appear.
  Redaction is deterministic.
  Reproducibility remains possible.
- **Hostile artifact comparison is bounded.**
  Decoders validate before diffing.
  Difference output truncates safely.
  No untrusted index is followed unchecked.

### Determinism and reproducibility

- **Every boundary defines a canonical order.**
  Sources, definitions, goals, and functions.
  Pools, sections, and diagnostics.
  The specification names tie breaks.
- **Every hash defines canonical input bytes.**
  Structured encoders are shared.
  Field order is fixed.
  Missing values encode explicitly.
- **Every fixed point defines stable iteration.**
  Queue and widening rules are documented.
  Results ignore insertion history.
  Tests permute inputs.
- **Every artifact excludes ambient metadata.**
  No build timestamp.
  No absolute path.
  No process identifier.
- **Every bootstrap release publishes reproduction commands.**
  Inputs and limits are pinned.
  Checksums are included.
  Independent builders can compare.

### Testing and observability

- **Repeated-build tests vary process history.**
  Cold, warm, and evicted builds.
  Different query demand orders.
  Artifacts must match.
- **Permutation tests randomize collection insertion.**
  Maps and arenas receive varied order.
  Frozen bytes remain equal.
  Diagnostics remain equal.
- **Cross-platform tests normalize paths.**
  Logical module identities match.
  Line endings follow specified rules.
  Artifacts remain portable.
- **Bootstrap tests compare complete bytes.**
  Stage two and three must match.
  First difference is retained.
  CI blocks release mismatch.
- **Observability exposes phase fingerprints.**
  `grc` can emit them.
  Reports remain canonical.
  Performance counters stay separate.

### Migration and completion criteria

- **Inventory every serialized map.**
  Add freeze steps.
  Add deterministic ordering tests.
  Remove direct iteration encoding.
- **Canonicalize diagnostics centrally.**
  Sort structured records.
  Separate rendering options.
  Freeze stable codes.
- **Add phase fingerprints.**
  Start at interfaces and artifacts.
  Extend through Core and MIR.
  Build comparison tooling.
- **Run repeatability CI.**
  Rebuild with varied cache state.
  Compare all boundary products.
  Track nondeterminism regressions.
- **Complete when stage convergence is reliable.**
  Byte identity holds repeatedly.
  First differences localize quickly.
  Reproducible manifests ship.

## 08. Cancellation, Resource Limits, Corruption Handling, and Security

This section defines bounded and fail-closed compiler behavior.
Cancellation, limits, corruption, and internal defects remain distinct.
Hostile source and persisted data cannot force uncontrolled work.
Failed computations publish no successful facts.

### Purpose and scope

- **Define cancellation semantics.**
  Obsolete editor work stops safely.
  Completed facts may remain reusable.
  Partial facts never publish.
- **Define structural resource limits.**
  Tokens, goals, blocks, and bytes are bounded.
  Every expanding subsystem is metered.
  Exhaustion is a typed outcome.
- **Define corruption handling.**
  Interfaces, caches, and artifacts are hostile.
  Defensive decoders validate before use.
  Corruption differs from source errors.
- **Define compiler security posture.**
  Semantic phases have least authority.
  Imported data grants no trust.
  Runtime capabilities remain separate.
- **Define invariant failure behavior.**
  Compiler defects are not user diagnostics.
  They preserve debugging evidence.
  They never continue unsafely.

### Goals and non-goals

- **Goal: responsive long-lived service.**
  New editor revisions cancel old work.
  Cancellation checks are bounded.
  Cleanup releases memory quickly.
- **Goal: predictable self-host bounds.**
  Time and memory gates are measurable.
  Budgets expose dominant categories.
  Pathological source fails cleanly.
- **Goal: fail closed on malformed data.**
  Unknown critical tags reject.
  Invalid indices never reach storage.
  Unsupported features remain explicit.
- **Non-goal: guarantee completion for all valid source.**
  Limits may reject huge programs.
  Diagnostics explain the limit.
  Users may raise policy bounds.
- **Non-goal: hide compiler bugs.**
  Invariants remain visible.
  Recovery is not attempted blindly.
  CI turns failures into regressions.

### Public queries and interfaces

- **`CancellationToken`.**
  Exposes cheap checked state.
  Supports child token derivation.
  Carries stable cancellation reason.
- **`BudgetSet`.**
  Holds typed counters and ceilings.
  Supports hierarchical charging.
  Returns structured exhaustion.
- **`decode_interface`.**
  Accept hostile bytes and limits.
  Return validated immutable records.
  Preserve corruption diagnostics.
- **`validate_product`.**
  Check internal graph invariants.
  Run before publication.
  Distinguish invariant ownership.
- **`security_report`.**
  Summarize authorities and limits.
  Expose enabled critical features.
  Support release audits.

### Primary data structures

- **`CancellationState`.**
  Stores requested and observed state.
  Stores cancellation class.
  Is request-owned.
- **`BudgetCounter<Tag>`.**
  Uses typed quantity categories.
  Prevents cross-category confusion.
  Saturates safely before overflow.
- **`ResourceLimitDiagnostic`.**
  Names limit and observed count.
  Names owning phase.
  Suggests explicit policy change.
- **`CorruptInputDiagnostic`.**
  Names source kind and location.
  Carries schema and feature data.
  Avoids source-semantic classification.
- **`InvariantFailure`.**
  Captures component and assertion.
  Carries bounded context.
  Is never cacheable success.

### Ownership and lifetime model

- **Requests own cancellation.**
  Child sessions borrow or derive it.
  Database state remains reusable.
  Tokens die with the request.
- **Budgets form an ownership tree.**
  Parent owns total allowance.
  Children charge typed slices.
  Cleanup returns only reservations.
- **Decoders own hostile buffers.**
  Validated values move into safe arenas.
  Malformed buffers release promptly.
  Borrowed raw data does not escape.
- **Failure records own bounded evidence.**
  They avoid retaining full compiler graphs.
  Source snippets are size-limited.
  Developer traces are optional.
- **Quarantine storage owns corrupt records.**
  Semantic database does not.
  Operators may inspect them.
  Eviction removes them safely.

### Algorithms and phase order

- **Check coarse limits at boundaries.**
  Source and artifact size first.
  Reject before expensive decoding.
  Record exact measured size.
- **Charge work during expansion.**
  Every token and node increments counters.
  Solvers charge steps and tables.
  Optimizers charge transformations.
- **Check cancellation at bounded intervals.**
  Query demands check immediately.
  Long loops check scheduled checkpoints.
  Decoders check between sections.
- **Validate before publication.**
  Check graph bounds and invariants.
  Verify recovery status.
  Confirm request remains active.
- **Classify failure at the boundary.**
  Source, resource, corruption, cancellation.
  Invariant, verification, or runtime.
  Return typed outcome.

### Semantic invariants

- **Cancelled work publishes nothing new.**
  Completed prior values remain valid.
  Staged diagnostics discard.
  Persistent writes remain atomic.
- **Resource exhaustion is deterministic.**
  Counters use stable work order.
  Same limit yields same stopping point.
  Diagnostics sort stably.
- **Corrupt data never becomes semantic fact.**
  Every imported graph validates.
  Cache origin grants no exception.
  Partial decode state stays private.
- **Invariant failures never masquerade as user errors.**
  Stable internal codes identify them.
  Source labels may aid context.
  Compilation stops safely.
- **Authority remains explicit during failure.**
  Error rendering stays outside phases.
  Recovery cannot acquire host access.
  Runtime grants remain unchanged.

### Cycles and fixed points

- **Cycle algorithms charge budgets.**
  SCC nodes and edges count.
  Fixed-point iterations count.
  Nonconvergence produces resource outcome.
- **Cancellation breaks active cycles safely.**
  Query frames unwind as a group.
  Provisional solver states discard.
  No dead running markers remain.
- **Decoder graph cycles validate iteratively.**
  Explicit stacks avoid host overflow.
  Visitation states detect malformed loops.
  Legal recursive structures remain bounded.
- **Failure-report cycles collapse.**
  Diagnostic causes do not recurse forever.
  Stable representatives are shown.
  Context depth is limited.
- **Budget ownership avoids cyclic reservations.**
  Child budgets cannot own parents.
  Reservations return through cleanup.
  Sibling borrowing is explicit.

### Incremental dependencies and invalidation

- **Cancellation is not a semantic dependency.**
  Retrying may complete the same value.
  Cancelled outcomes never persist.
  Prior green entries remain.
- **Limits matter when observed.**
  Successful under-limit values may reuse.
  Exhaustion depends on the limit.
  Queries record relevant budget facts.
- **Corruption invalidates imported records only.**
  Recompute local products when possible.
  Source semantics remain unchanged.
  Quarantine does not poison caches.
- **Security policy changes affect boundaries.**
  Decoder feature policy may rerun.
  Semantic values may remain reusable.
  Verification roots change.
- **Invariant fixes advance family versions.**
  Suspect cached products are rejected.
  Unrelated families may reuse.
  Migration is explicit.

### Caching and persistence

- **Cancelled outcomes never cache.**
  They carry no complete value.
  Retry starts from valid dependencies.
  Staged bytes are removed.
- **Resource errors use cautious policy.**
  Exact low-limit failures may memoize locally.
  Persistent caching is usually disabled.
  Raised limits force recomputation.
- **Corrupt records are never rewritten blindly.**
  Recompute canonical replacement.
  Atomically repoint indexes.
  Preserve quarantine evidence optionally.
- **Invariant failures never become hits.**
  They may create crash reports.
  Reports are separate from query cache.
  Build products remain absent.
- **Security metadata persists with products.**
  Critical feature sets are recorded.
  Decoder generations are recorded.
  Unknown requirements reject.

### Diagnostics and explanations

- **Cancellation diagnostics are usually silent.**
  Editor obsolescence is expected.
  CLI cancellation may report once.
  Developer traces record origin.
- **Resource diagnostics name the exact counter.**
  Show ceiling and observed value.
  Show owning query or phase.
  Suggest configuration field.
- **Corruption diagnostics name the input class.**
  Interface, cache, or artifact.
  Include byte or record offset.
  Preserve checksum evidence.
- **Security diagnostics name denied authority.**
  Show requested feature or capability.
  Show allowed policy.
  Avoid generic permission failures.
- **Invariant diagnostics preserve bounded context.**
  Include stable component code.
  Include query key and revision.
  Avoid exposing private source by default.

### Cancellation, limits, and security

- **Every unbounded loop requires a checkpoint.**
  Parser, solver, optimizer, verifier.
  Check frequency is specified.
  Overhead is benchmarked.
- **Every expanding collection has a ceiling.**
  Nodes, edges, strings, and instances.
  Preflight checks avoid overflow.
  Counters use checked arithmetic.
- **Every decoder validates before allocation.**
  Count fields are bounded.
  Multiplication overflow is checked.
  Compression ratios are bounded.
- **Every external effect is capability-gated.**
  Compiler phases receive none.
  Runtime adapters validate each request.
  Supervisor policy is exact.
- **Every failure path has cleanup coverage.**
  Arena marks restore.
  Files remain atomic.
  Pins and reservations release.

### Determinism and reproducibility

- **Budget checks follow stable work order.**
  Equivalent inputs exhaust identically.
  Parallelism preserves logical ordering.
  Diagnostics remain stable.
- **Cancellation timing does not affect completed products.**
  Either commit completes or not.
  Partial data never leaks.
  Retried builds reproduce output.
- **Corruption handling is deterministic.**
  Same bytes yield same rejection.
  Quarantine names use content digests.
  Reports sort canonically.
- **Security policy encoding is canonical.**
  Capability sets are sorted.
  Feature sets are normalized.
  Manifest hashes reproduce.
- **Invariant context uses logical identities.**
  Avoid addresses and thread IDs.
  Stable query keys aid comparison.
  Wall time remains supplemental.

### Testing and observability

- **Cancellation tests interrupt every phase.**
  Check cleanup and publication.
  Repeat at many checkpoints.
  Compare successful retry.
- **Limit tests hit exact boundaries.**
  One below, at, and above.
  Verify deterministic diagnostics.
  Check integer overflow defenses.
- **Corruption fuzzing covers every imported format.**
  Truncate and mutate bytes.
  Inject extreme counts.
  Exercise recursive graphs.
- **Security tests inspect capability absence.**
  Semantic modules cannot perform host I/O.
  VM requests denied grants.
  Manifest mismatches reject.
- **Failure telemetry remains bounded.**
  Record counters and owning phase.
  Avoid unbounded trace payloads.
  Support self-host incident replay.

### Migration and completion criteria

- **Inventory unbounded recursion and growth.**
  Add typed counters.
  Replace host-stack recursion where needed.
  Add exact boundary tests.
- **Introduce request cancellation tokens.**
  Thread through query sessions.
  Add cleanup guards.
  Test stale editor work.
- **Harden imported decoders.**
  Interfaces, caches, then artifacts.
  Add hostile corpora.
  Separate corruption codes.
- **Separate invariant failure classes.**
  Remove generic source errors.
  Preserve bounded context.
  Add CI crash fixtures.
- **Complete when hostile input stays bounded.**
  Self-host limits are enforced.
  Cancellation leaks nothing.
  Corruption cannot change semantics.

---

# Volume III — Source and Frontend

## 09. Source Model, Spans, Lossless Lexing, and Delimiter Pairing

This section defines immutable source representation and lexical structure.
The same lossless token stream serves compiler, formatter, and editor tooling.
Spans remain stable logical coordinates over supplied bytes.
Delimiter pairing is constructed once and shared.

### Purpose and scope

- **Own source bytes immutably.**
  Database blobs are digest-verified.
  Logical files reference byte ranges.
  Semantic phases never reopen paths.
- **Produce a lossless token stream.**
  Preserve whitespace and comments.
  Preserve malformed token regions.
  Support exact source round trips.
- **Define one span model.**
  Byte spans are canonical.
  Line and column are derived.
  Source segments recover file identity.
- **Pair delimiters once.**
  Scanner and parsers share the map.
  Balanced regions support constant-time skips.
  Mismatches produce lexical structure diagnostics.
- **Support incremental source queries.**
  File-level token products are memoized.
  Editor overlays create new blobs.
  Stable anchors derive from token structure.

### Goals and non-goals

- **Goal: exact source preservation.**
  Formatter sees every trivia byte.
  Refactoring keeps comments.
  Diagnostics underline exact spans.
- **Goal: deterministic lexing.**
  Same bytes produce same tokens.
  Unicode policy is explicit.
  Malformed input terminates.
- **Goal: shared frontend substrate.**
  No formatter-specific lexer.
  No LSP-specific tokenization.
  All clients use source queries.
- **Non-goal: semantic classification.**
  Lexer does not resolve names.
  Operators remain lexical tokens.
  Contextual meaning comes later.
- **Non-goal: arbitrary text encodings.**
  Source encoding policy is explicit.
  Invalid UTF-8 produces structured input diagnostics.
  Byte offsets remain authoritative.

### Public queries and interfaces

- **`source_blob`.**
  Return immutable verified bytes.
  Expose content digest.
  Preserve logical file key.
- **`line_index`.**
  Map byte offsets to lines.
  Handle newline variants deterministically.
  Support bounded reverse lookup.
- **`lossless_tokens`.**
  Return token and trivia records.
  Include malformed token kinds.
  Attach byte spans.
- **`delimiter_map`.**
  Return paired token identities.
  Mark unmatched delimiters.
  Support direct balanced-range access.
- **`token_at_position`.**
  Resolve editor byte position.
  Define boundary bias explicitly.
  Return surrounding trivia when requested.

### Primary data structures

- **`SourceBlob`.**
  Owns immutable bytes and digest.
  Stores encoding status.
  Has database lifetime.
- **`SourceFileRecord`.**
  Maps logical file key to blob.
  Stores module and package labels.
  Contains no filesystem handle.
- **`SourceSpan`.**
  Stores start and end byte offsets.
  Refers to one stable file key.
  Validates ordering and bounds.
- **`LosslessToken`.**
  Stores kind, span, and flags.
  Trivia remains explicit tokens or ranges.
  Semantic codes are not duplicated.
- **`DelimiterPairTable`.**
  Maps token IDs bidirectionally.
  Stores mismatch classifications.
  Uses typed token indices.

### Ownership and lifetime model

- **Database owns source blobs.**
  Multiple revisions may share them.
  Content addressing avoids duplicates.
  Eviction respects snapshot pins.
- **Token query owns token arena.**
  Published token products are immutable.
  Local lexer scratch is released.
  Clients borrow typed views.
- **Line index shares blob lifetime.**
  It stores compact newline offsets.
  It may evict independently.
  Rebuilding is deterministic.
- **Delimiter table belongs to token product.**
  Token IDs remain owner-local.
  Parsers borrow the table.
  No duplicate pairing is built.
- **Editor positions stay client-owned.**
  LSP converts UTF coordinate variants.
  Compiler receives validated byte offsets.
  Conversion tables may cache separately.

### Algorithms and phase order

- **Validate source encoding.**
  Check UTF-8 according to language policy.
  Preserve raw bytes for diagnostics.
  Reject or recover deterministically.
- **Build newline index.**
  Scan bytes once.
  Normalize recognized newline sequences.
  Store offset table.
- **Lex losslessly.**
  Recognize tokens and trivia.
  Nest block comments safely.
  Emit malformed tokens on errors.
- **Pair delimiters.**
  Use an explicit typed stack.
  Record pairs and mismatches.
  Avoid recursive scans.
- **Publish lexical products.**
  Validate spans and token coverage.
  Compute semantic and lossless fingerprints.
  Attach diagnostics.

### Semantic invariants

- **Token coverage is gap-free.**
  Every source byte belongs somewhere.
  Round-trip concatenation reproduces bytes.
  Missing regions are invariants.
- **Spans remain within one blob.**
  Start never exceeds end.
  End never exceeds byte length.
  Cross-file spans use compound labels.
- **Delimiter pairs are symmetric.**
  Opening points to closing.
  Closing points to opening.
  Unmatched entries are explicit.
- **Lexical kinds contain no semantic privilege.**
  Keywords follow frozen lexical policy.
  User control names remain ordinary identifiers.
  Primitive authority is absent.
- **Diagnostics never mutate tokenization.**
  Recovery tokens are deterministic.
  Tooling sees the same stream.
  Release parsing may reject later.

### Cycles and fixed points

- **Lexing is acyclic.**
  One forward scan suffices.
  Nested comments use explicit depth.
  Delimiter pairing uses a stack.
- **Source segment maps remain acyclic.**
  Distributed bundles map to original files.
  Segments do not reference each other recursively.
  Lookups use sorted ranges.
- **Incremental line indexes avoid edit chains.**
  Rebuild from immutable bytes when needed.
  Optional delta indexes remain bounded.
  Semantic truth is the blob.
- **Malformed delimiter recovery does not loop.**
  Every step consumes a token.
  Stack operations are bounded.
  EOF closes the algorithm.
- **Unicode normalization is not recursive semantic work.**
  Identifier policy is one lexical pass.
  Canonical equivalence policy is explicit.
  Security checks remain bounded.

### Incremental dependencies and invalidation

- **Tokenization depends on source bytes and lexical generation.**
  Path changes do not alter tokens.
  Encoding policy changes do.
  Line indexes depend on bytes only.
- **Delimiter map depends on token sequence.**
  Trivia-only edits may preserve semantic token fingerprint.
  Lossless fingerprint still changes.
  Parsers choose the relevant dependency.
- **Source maps depend on logical file identity.**
  Module moves affect diagnostics and privacy.
  Token bytes may remain reusable.
  Key projections separate them.
- **Editor overlays invalidate one file leaf.**
  Shared unchanged blobs remain green.
  Package scans rerun as needed.
  Old revisions remain queryable.
- **Stable token anchors survive trivia edits.**
  Structural token neighborhoods provide matches.
  Semantic edits replace anchors.
  Identity diffs remain explainable.

### Caching and persistence

- **Source blobs use content-addressed storage.**
  Identical bytes share records.
  Logical file records stay separate.
  Private overlays may avoid disk.
- **Token products may persist.**
  Canonical encoding stores kinds and spans.
  Blob digest enters key.
  Validators check complete coverage.
- **Line indexes are cheap optional caches.**
  They may remain memory-only.
  Rebuild cost is linear and deterministic.
  Eviction has no semantic effect.
- **Delimiter tables persist with tokens.**
  Pair indices are validated.
  Malformed states are encoded explicitly.
  Unknown lexical features reject.
- **Raw source remains the ultimate truth.**
  Cached tokens cannot replace digest verification.
  Corrupt token records are recomputed.
  Round-trip validation catches damage.

### Diagnostics and explanations

- **Encoding diagnostics cite byte ranges.**
  Show invalid sequence boundaries.
  Preserve logical file identity.
  Avoid host path leakage.
- **Token diagnostics name lexical category.**
  Unterminated strings and comments.
  Malformed numeric literals.
  Invalid identifier characters.
- **Delimiter diagnostics show both sites.**
  Unexpected closing delimiter.
  Unclosed opening delimiter.
  Recovery pairing is explained.
- **Position diagnostics handle boundaries.**
  Explain invalid byte offset.
  Show nearest valid token.
  Distinguish UTF coordinate errors.
- **Developer inspection shows lossless stream.**
  Include token IDs and spans.
  Include delimiter partners.
  Preserve deterministic ordering.

### Cancellation, limits, and security

- **Source byte length is limited.**
  Reject oversized files before token allocation.
  Hashing remains bounded.
  Diagnostics name the limit.
- **Token count is limited.**
  Each emitted token charges budget.
  Trivia runs may be compacted safely.
  Overflow fails before index conversion.
- **Nested comment depth is limited.**
  Explicit counter avoids stack overflow.
  Excess depth is structured.
  Scanning still terminates.
- **Identifier security policy is explicit.**
  Confusable handling is deterministic.
  Normalization does not grant identity silently.
  Diagnostics may warn.
- **Line index arithmetic is checked.**
  Offsets use bounded integers.
  Addition and conversion are validated.
  Hostile files cannot wrap indexes.

### Determinism and reproducibility

- **Lexer tables are frozen.**
  Keyword and punctuation recognition is versioned.
  Table iteration does not affect tokens.
  Generated code is reproducible.
- **Newline handling is specified.**
  CRLF and LF behavior is explicit.
  Byte spans remain original.
  Line numbers reproduce across hosts.
- **Diagnostics sort by byte span.**
  Multiple lexical errors have stable order.
  Delimiter ties use token identity.
  Recovery remains stable.
- **Token serialization is canonical.**
  Kinds use frozen numeric encodings.
  Optional fields encode consistently.
  Re-encoding matches.
- **Source paths are logical.**
  Absolute checkout roots are excluded.
  Bundle ordering is canonical.
  Bootstrap source maps match.

### Testing and observability

- **Round-trip tests concatenate tokens.**
  Exact source bytes must return.
  Include malformed sources.
  Include nested comments.
- **Lexer conformance tests cover every token.**
  Valid and invalid literals.
  Unicode identifiers.
  Comment and whitespace boundaries.
- **Delimiter tests fuzz arbitrary streams.**
  Pair tables remain symmetric.
  Algorithms terminate.
  Depth limits hold.
- **Incremental tests edit trivia and tokens.**
  Check semantic versus lossless fingerprints.
  Inspect stable anchors.
  Compare clean lexing.
- **Inspection tooling prints bounded slices.**
  Filter by file and span.
  Include raw escaped bytes optionally.
  Support bundle token lookup.

### Migration and completion criteria

- **Adopt one source span type.**
  Remove duplicate phase spans.
  Add typed file keys.
  Preserve diagnostic parity.
- **Make lexer lossless.**
  Retain trivia and malformed ranges.
  Route formatter through it.
  Add round-trip tests.
- **Build one delimiter table.**
  Remove repeated recursive matching.
  Route scanner and parsers.
  Benchmark large sources.
- **Move line mapping into shared query.**
  Remove client-specific indexing.
  Support LSP conversions externally.
  Test platform newlines.
- **Complete when every source client shares facts.**
  No duplicate lexer remains.
  Round trips are exact.
  Hostile input stays bounded.

## 10. Packages, Modules, Structural Scanning, Interfaces, and Fixity

This section defines top-level structure before body parsing.
It discovers declarations, module ownership, interfaces, and operator fixities.
It builds compact package products for downstream compilation.
It avoids whole-program body trees.

### Purpose and scope

- **Define package source topology.**
  Packages have explicit roots.
  Workspaces remain orchestration inputs.
  Modules use logical paths.
- **Scan declarations structurally.**
  Record item shells and body ranges.
  Avoid parsing body expressions.
  Preserve source order and visibility.
- **Collect semantic interfaces.**
  Functions, types, traits, effects, impls.
  Associated items and fixities.
  Exported facts become dependency products.
- **Resolve module file ownership.**
  Inline and external modules coexist.
  Missing and orphan files diagnose.
  Privacy follows source identity.
- **Collect fixity before body grouping.**
  Operators remain source declarations.
  Bodies parse against collected fixities.
  Compiler names stay nonmagical.

### Goals and non-goals

- **Goal: cheap top-level discovery.**
  Large bodies remain unparsed.
  Interfaces emerge early.
  Editor outlines respond quickly.
- **Goal: deterministic module graph.**
  Logical paths define ownership.
  External source order is canonical.
  Ambiguities reject.
- **Goal: compact dependency interfaces.**
  Downstream builds avoid source parsing.
  Public semantic facts are canonical.
  Private implementation details stay hidden.
- **Non-goal: package acquisition.**
  `grand` resolves versions and Git.
  Compiler receives selected packages.
  Network access remains absent.
- **Non-goal: body semantics.**
  Scanner does not type-check.
  It records body token ranges.
  Body parser runs on demand.

### Public queries and interfaces

- **`package_sources`.**
  Return validated logical source set.
  Include roots and module labels.
  Exclude filesystem handles.
- **`module_outline`.**
  Return nested module shells.
  Include declaration ranges.
  Include structural diagnostics.
- **`item_header`.**
  Parse one declaration interface.
  Return typed header syntax.
  Leave body as token range.
- **`package_interface`.**
  Collect exported semantic contracts.
  Canonically serialize them.
  Include implementation heads.
- **`fixity_table`.**
  Resolve visible operator declarations.
  Detect conflicts and ambiguity.
  Provide body-grouping input.

### Primary data structures

- **`PackageInputGraph`.**
  Stores package roots and dependencies.
  Stores feature selections.
  Is normalized before semantics.
- **`ModuleRecord`.**
  Stores parent and logical path.
  Stores source file identity.
  Stores child declaration ranges.
- **`DeclarationShell`.**
  Stores kind and stable name.
  Stores visibility and spans.
  Stores header and body ranges.
- **`SemanticInterface`.**
  Stores resolved exported signatures.
  Stores traits, impls, effects, fixities.
  Uses canonical stable keys.
- **`FixityRecord`.**
  Stores operator identity and precedence.
  Stores associativity and visibility.
  Stores source declaration owner.

### Ownership and lifetime model

- **Revision owns package topology.**
  Package records are immutable.
  Snapshots borrow them.
  Parent revisions may share unchanged graphs.
- **Scanner query owns shell arenas.**
  Published outlines are immutable.
  Temporary delimiter cursors die.
  Body tokens remain borrowed ranges.
- **Header queries own transient parse scratch.**
  Resolved interface values publish separately.
  Raw syntax may evict.
  Stable declaration keys persist.
- **Interface products have package lifetime.**
  Downstream queries borrow them.
  Persistent encoders copy canonically.
  Private body state is absent.
- **Fixity tables belong to visibility contexts.**
  They may cache per module.
  Entries reference stable definitions.
  Body parsers borrow read-only views.

### Algorithms and phase order

- **Validate package source mapping.**
  Every logical module has one owner.
  Detect duplicate and orphan sources.
  Sort roots canonically.
- **Scan top-level token ranges.**
  Use delimiter table for skipping.
  Recognize declarations structurally.
  Recover at stable boundaries.
- **Assign stable declaration shells.**
  Group by module and namespace.
  Preserve source spans.
  Record body token ranges.
- **Parse and resolve headers.**
  Collect generics and where clauses.
  Collect trait, impl, and effect heads.
  Defer body checking.
- **Freeze interfaces and fixities.**
  Apply visibility and coherence prerequisites.
  Canonically order records.
  Publish package products.

### Semantic invariants

- **Every body range is balanced or diagnosed.**
  Delimiter table defines boundaries.
  Scanner never guesses through mismatches.
  Recovery remains deterministic.
- **Every declaration belongs to one module.**
  Parent path is explicit.
  Inline modules advance logical directory.
  External ownership is unique.
- **Interfaces contain resolved stable identities.**
  Raw local header IDs do not escape.
  Source spans remain auxiliary.
  Canonical keys drive equality.
- **Fixity authority follows declarations.**
  Names alone grant no precedence.
  Visibility controls availability.
  Conflicts are diagnosed.
- **Private bodies remain outside dependency interfaces.**
  Only required generic semantics cross.
  Exported facts are explicit.
  Downstream privacy remains enforceable.

### Cycles and fixed points

- **Module nesting cycles reject.**
  Logical parent graph must be acyclic.
  External file mapping cannot loop.
  Diagnostics show the path.
- **Mutually recursive headers form SCCs.**
  Stable shells exist before resolution.
  Interface checking handles recursive names.
  Publication waits for the group.
- **Trait and impl collection may reference later items.**
  Declaration index is built first.
  Header resolution then sees complete shells.
  Coherence runs after collection.
- **Type alias cycles use semantic policy.**
  Scanner records them.
  Type normalization later decides legality.
  Interface group retains dependencies.
- **Fixity imports may form module cycles only if modules permit.**
  Visibility resolution handles SCCs.
  Conflicts remain deterministic.
  Body grouping waits for stable table.

### Incremental dependencies and invalidation

- **Body-only edits preserve shells.**
  Header and interface fingerprints may remain equal.
  Downstream packages stay green.
  Body queries rerun.
- **Header edits invalidate interface consumers.**
  Stable declaration key may remain.
  Signature fingerprint changes.
  Callers and downstream packages validate.
- **Module path changes replace ownership.**
  Privacy and imports rerun.
  Token bytes may remain reusable.
  Stable keys may change intentionally.
- **Fixity edits target operator-using bodies.**
  Token streams remain unchanged.
  Grouped expression syntax reruns.
  Unused operators have no body fanout.
- **Private declaration additions stay package-local.**
  Export fingerprint remains equal.
  Outline tooling updates.
  Downstream interface caches reuse.

### Caching and persistence

- **Module outlines are cacheable.**
  Keyed by lossless token fingerprint.
  Decoder validates token ranges.
  Body syntax stays absent.
- **Header products are cacheable.**
  Keyed by declaration shell and visible names.
  Stable keys are canonical.
  Inference-free syntax persists safely.
- **Package interfaces are primary persistent products.**
  Canonical schema is versioned.
  Downstream builds validate them.
  Unknown critical facts reject.
- **Fixity tables may persist with interfaces.**
  Records reference stable definitions.
  Visibility context is encoded.
  Ordering is canonical.
- **Module graph caches avoid host paths.**
  Use logical package paths.
  Source digests establish contents.
  Absolute roots remain provenance only.

### Diagnostics and explanations

- **Module diagnostics name logical ownership.**
  Missing source and orphan source.
  Duplicate module definitions.
  Illegal inline-external combinations.
- **Scanner diagnostics cite item boundaries.**
  Malformed declarations recover.
  Unexpected tokens show stable spans.
  Body contents remain skipped safely.
- **Header diagnostics show declaration context.**
  Invalid generics and where clauses.
  Missing associated items.
  Unsupported interface features.
- **Fixity diagnostics show competing declarations.**
  Include precedence and associativity.
  Include import paths.
  Suggest qualification or removal.
- **Interface diagnostics distinguish corruption.**
  Imported malformed records are not source errors.
  Local coherence errors remain semantic.
  Developer mode shows record paths.

### Cancellation, limits, and security

- **Module count is bounded.**
  Package graph expansion charges budget.
  Deep nesting uses explicit stacks.
  Excess reports resource diagnostics.
- **Declaration count is bounded.**
  Scanner checks before arena growth.
  Stable key construction uses checked indices.
  Interfaces enforce count ceilings.
- **Header depth is bounded.**
  Generic and type syntax recursion charges limits.
  Host stack use is controlled.
  Malformed input still terminates.
- **Imported interfaces are hostile.**
  Every stable key and range validates.
  Impossible coherence claims reject.
  Producer identity grants no trust.
- **Logical paths are normalized securely.**
  Reject traversal semantics.
  Avoid case-fold ambiguity by policy.
  Preserve deterministic diagnostics.

### Determinism and reproducibility

- **Package graph ordering is canonical.**
  Sort by stable package identity.
  Dependency declaration order is preserved only semantically.
  Host file enumeration is excluded.
- **Declaration shells preserve source order.**
  Stable order aids diagnostics.
  Interface serialization uses semantic keys.
  Duplicate ties are deterministic.
- **Module resolution uses logical paths only.**
  Platform separators normalize.
  Absolute roots never enter output.
  Cross-platform artifacts match.
- **Fixity table construction sorts candidates.**
  Ambiguity reports are stable.
  Precedence values encode canonically.
  Map iteration cannot affect grouping.
- **Interface serialization freezes every collection.**
  Traits, impls, and effects sort.
  Local IDs remap.
  Re-encoding reproduces bytes.

### Testing and observability

- **Module conformance tests cover layouts.**
  Inline and external modules.
  Nested directory rules.
  Missing and orphan files.
- **Scanner fuzzing uses arbitrary token streams.**
  Algorithms terminate.
  Body ranges remain bounded.
  Recovery is deterministic.
- **Header tests cover recursive declarations.**
  Traits, effects, GATs, and consts.
  Compare Rust and self-host products.
  Verify exact spans.
- **Fixity tests vary import order.**
  Grouped bodies remain equal.
  Conflicts diagnose stably.
  Unused changes avoid fanout.
- **Interface round trips use hostile mutations.**
  Validate every record.
  Compare canonical bytes.
  Measure downstream reuse.

### Migration and completion criteria

- **Unify module source discovery contract.**
  Make `grand` assemble logical mapping.
  Stop compiler filesystem scanning.
  Add parity tests.
- **Extract structural scanner from body parser.**
  Record body ranges only.
  Reuse delimiter map.
  Measure large-file latency.
- **Create stable declaration shells.**
  Route resolution and diagnostics.
  Remove raw ordinal identities.
  Test edits.
- **Freeze package interface schema.**
  Add defensive decoder.
  Route dependency compilation.
  Validate private-change isolation.
- **Complete when bodies are demand-parsed.**
  Outlines and interfaces require no body AST.
  Fixities are shared.
  Downstream builds consume canonical interfaces.

## 11. Body Parsing, Contextual Blocks, Operator Grouping, and Recovery

This section defines on-demand body syntax construction.
It parses structural language forms without granting control-name privilege.
It groups operators after fixity collection.
It supports transactional recovery for editor and release modes.

### Purpose and scope

- **Parse one demanded body.**
  Use recorded token range.
  Build body-local typed arenas.
  Avoid whole-program syntax retention.
- **Represent structural syntax faithfully.**
  Calls, blocks, labels, handlers, and patterns.
  Operators remain flat until grouping.
  Contextual blocks remain undecided.
- **Interpret contextual callable blocks later.**
  Parsing records neutral block syntax.
  Type-directed elaboration chooses eagerness.
  Ambiguity becomes a semantic error.
- **Group source-defined operators.**
  Use visible fixity table.
  Preserve left-to-right operand evaluation.
  Diagnose conflicts and missing declarations.
- **Recover malformed editor bodies.**
  Produce marked syntax when safe.
  Release builds reject incomplete products.
  Recovery always consumes input.

### Goals and non-goals

- **Goal: deterministic termination.**
  Malformed source never loops.
  Every recovery step advances.
  Depth and node counts are bounded.
- **Goal: exact source spans.**
  Every syntax node maps to tokens.
  Delimiters and operators retain locations.
  Tooling can refactor precisely.
- **Goal: compact body-local representation.**
  Typed arenas and ranges are shared.
  Scratch dies after lowering.
  Views avoid accessor duplication.
- **Non-goal: type inference.**
  Parser records syntax only.
  Contextual meaning waits for elaboration.
  Name lookup remains separate.
- **Non-goal: parser combinator framework.**
  Use a small token cursor toolkit.
  Specialized grammar stays explicit.
  Complexity remains auditable.

### Public queries and interfaces

- **`body_tokens`.**
  Return bounded token slice.
  Include delimiter map view.
  Validate shell ownership.
- **`parse_body`.**
  Produce complete or recovered syntax.
  Attach structural diagnostics.
  Return body arena owner.
- **`group_operators`.**
  Consume flat operator expression.
  Use resolved fixity candidates.
  Produce grouped syntax view.
- **`syntax_at`.**
  Find smallest covering node.
  Support editor selection.
  Preserve recovered status.
- **`format_body_input`.**
  Expose lossless syntax structure.
  Avoid semantic reinterpretation.
  Share parser node kinds.

### Primary data structures

- **`BodySyntax`.**
  Owns expression and pattern arenas.
  Stores root and recovery status.
  Stores token span mappings.
- **`TokenCursor`.**
  Stores bounds and position.
  Borrows delimiter pairs.
  Supports marks and rollback.
- **`ExprKind`.**
  Uses direct algebraic variants.
  Carries typed child ranges.
  Avoids magic numeric tags.
- **`FlatOperatorChain`.**
  Stores operands and operator tokens.
  Preserves original evaluation order.
  Is grouped later.
- **`ParserCheckpoint`.**
  Stores cursor and arena marks.
  Rolls back on failure.
  Commits explicitly.

### Ownership and lifetime model

- **Body session owns syntax arenas.**
  Nodes cannot outlive owner.
  Queries publish immutable body product.
  Eviction drops entire body cleanly.
- **Cursor borrows token product.**
  It never owns source bytes.
  Checkpoints borrow the parser state.
  Cleanup restores marks.
- **Operator grouping may reuse arena.**
  Grouped nodes append deterministically.
  Flat chain remains source evidence.
  Final product freezes both mappings.
- **Recovery diagnostics belong to body product.**
  They may outlive parser scratch.
  Source anchors use stable tokens.
  Presentation remains separate.
- **Elaboration borrows syntax.**
  It never mutates parser nodes.
  Semantic side tables are separate.
  Body syntax can drop after lowering.

### Algorithms and phase order

- **Initialize bounded cursor.**
  Validate body token range.
  Attach delimiter table.
  Reserve body arena budget.
- **Parse declarations and expressions structurally.**
  Dispatch by token patterns.
  Use checkpoints for alternatives.
  Preserve contextual blocks neutrally.
- **Parse patterns and handlers.**
  Build typed binding syntax.
  Validate local structural rules.
  Defer name and type legality.
- **Build flat operator chains.**
  Parse primary operands first.
  Record operator token identities.
  Preserve source order.
- **Group operators after fixity lookup.**
  Use deterministic precedence algorithm.
  Diagnose ambiguity.
  Publish complete or recovered syntax.

### Semantic invariants

- **Every node span is within body range.**
  Child spans lie within parent structure.
  Token identities use the same owner.
  Cross-body IDs are impossible.
- **Parsing always advances or returns.**
  Recovery cannot revisit unchanged position.
  Loops assert progress.
  EOF handling is explicit.
- **Contextual blocks remain structurally neutral.**
  Parser does not invent callable meaning.
  Elaboration selects based on expected parameter.
  Syntax fingerprint remains context-independent.
- **Operator grouping preserves operand order.**
  Tree shape may change precedence.
  Evaluation order remains left to right.
  Fixity cannot reorder side effects.
- **Recovered syntax remains labeled.**
  Complete status cannot be forged.
  Release queries reject recovery.
  IDE consumers opt in.

### Cycles and fixed points

- **Grammar recursion uses explicit depth budgets.**
  Nested blocks and types are bounded.
  Tail loops replace simple recursion.
  Host stack remains safe.
- **Operator grouping is acyclic.**
  Shunting-yard or Pratt processing terminates.
  Each token is consumed once.
  Invalid fixity reports and advances.
- **Recovery checkpoints form a stack.**
  Guards restore in reverse order.
  Commit removes rollback obligation.
  No checkpoint owns its parent.
- **Recursive patterns are syntax trees only.**
  Cyclic syntax cannot arise from source.
  Arena graph validation enforces this.
  Malformed decoded caches reject cycles.
- **Contextual interpretation cycles belong to semantics.**
  Parser does not solve expected types.
  Elaboration query handles call cycles.
  Syntax query stays acyclic.

### Incremental dependencies and invalidation

- **Body parsing depends on body token fingerprint.**
  Header-only changes may leave body syntax green.
  Trivia changes affect lossless mappings.
  Semantic grouping may reuse tokens.
- **Operator grouping depends on visible fixities.**
  Only used operators record edges.
  Unrelated fixity changes stay green.
  Ambiguous candidate sets are dependencies.
- **Source span changes affect tooling products.**
  Semantic tree shape may remain equal.
  Source maps rerun.
  Code generation may stay green.
- **Recovery products are revision-specific.**
  Small edits may replace recovered nodes.
  Complete products supersede them.
  Persistent release caches exclude them.
- **Stable syntax anchors support identity.**
  Token neighborhoods preserve closures.
  Structural moves may replace keys.
  Identity diff explains outcomes.

### Caching and persistence

- **Complete body syntax may persist selectively.**
  Key includes token and fixity fingerprints.
  Canonical codec remaps node IDs.
  Validators enforce tree structure.
- **Recovered syntax stays memory-local by default.**
  Editor privacy and churn are high.
  Cheap reparsing is acceptable.
  Status must persist if cached.
- **Flat operator chains are cacheable.**
  They depend only on tokens.
  Grouped trees add fixity dependencies.
  Separate products improve reuse.
- **Parser checkpoints never persist.**
  They are mutable control state.
  Only committed syntax publishes.
  Failed alternatives leave no records.
- **Lossless mappings share token cache.**
  Avoid duplicate trivia storage.
  Node ranges reference token IDs.
  Decoder validates ownership.

### Diagnostics and explanations

- **Structural diagnostics cite exact tokens.**
  Missing delimiters and separators.
  Invalid declaration placement.
  Unexpected body termination.
- **Recovery diagnostics explain inserted structure.**
  Name synthetic missing token.
  Mark skipped token range.
  Tooling can present uncertainty.
- **Operator diagnostics show fixity sources.**
  Conflicting precedence declarations.
  Missing operand or operator.
  Ambiguous grouping alternatives.
- **Contextual block diagnostics remain semantic.**
  Parser only reports malformed block syntax.
  Elaboration reports eager-callable ambiguity.
  Boundaries stay clear.
- **Developer parser traces are bounded.**
  Show cursor and checkpoint events.
  Filter by body and token range.
  Avoid full-source dumps by default.

### Cancellation, limits, and security

- **Expression node counts are bounded.**
  Every allocation charges budget.
  Checked index conversion prevents overflow.
  Excess reports body context.
- **Nesting depth is bounded.**
  Delimited constructs increment depth.
  Explicit stacks replace vulnerable recursion.
  Diagnostics cite deepest span.
- **Speculative parsing has rollback limits.**
  Checkpoint count is bounded.
  Alternatives must make progress.
  Arena restoration is checked.
- **Malformed caches are hostile.**
  Node ranges and discriminants validate.
  Cyclic child graphs reject.
  Source span bounds are checked.
- **Cancellation checks occur between constructs.**
  Long operator chains check periodically.
  Rollback guards restore state.
  Partial syntax does not publish.

### Determinism and reproducibility

- **Alternative selection is ordered.**
  Grammar priorities are explicit.
  Recovery chooses stable boundaries.
  Diagnostics do not depend on hash order.
- **Arena allocation order follows source order.**
  Local IDs remain deterministic when convenient.
  Persistence still remaps them.
  Semantics never rely on the order.
- **Operator grouping uses stable fixity ordering.**
  Candidate ties diagnose.
  Worklists are deterministic.
  Grouped trees reproduce.
- **Recovery output is deterministic.**
  Same malformed bytes yield same nodes.
  Synthetic spans use fixed rules.
  Editor and CLI agree.
- **Parser serialization is canonical.**
  Variant tags are frozen.
  Child ranges encode consistently.
  Re-encoding matches.

### Testing and observability

- **Parser conformance covers every construct.**
  Calls, labels, handlers, and patterns.
  Contextual trailing blocks.
  Flat operator streams.
- **Malformed-source fuzzing checks termination.**
  Arbitrary bytes and token sequences.
  Bounded nodes and depth.
  Stable recovery diagnostics.
- **Checkpoint tests force every failure path.**
  Cursor and arenas restore.
  Nested checkpoints compose.
  Successful commit preserves nodes.
- **Fixity tests compare grouping oracles.**
  Precedence and associativity.
  Imports and ambiguity.
  Evaluation order remains stable.
- **Incremental tests edit local body regions.**
  Unrelated bodies stay green.
  Source mappings update.
  Clean parse matches reused parse.

### Migration and completion criteria

- **Introduce shared `TokenCursor`.**
  Replace duplicated parser cursors.
  Route delimiter jumps.
  Add rollback helpers.
- **Replace packed numeric nodes with typed views.**
  Prefer direct enums where viable.
  Keep storage private if packed.
  Remove magic codes from consumers.
- **Separate flat operator parsing.**
  Collect fixity edges explicitly.
  Preserve existing parse results.
  Add grouping inspection.
- **Add complete versus recovered status.**
  Route LSP recovery.
  Block release misuse.
  Test propagation.
- **Complete when bodies parse on demand.**
  No whole-program AST is required.
  Every malformed input terminates.
  Formatter and compiler share syntax.

## 12. Name Resolution, Scopes, Visibility, and Reference Indexing

This section binds syntax names to stable semantic identities.
It defines lexical scopes, module namespaces, imports, and privacy.
It builds occurrence indexes for tooling and incremental compilation.
Resolution remains separate from type-directed method selection where required.

### Purpose and scope

- **Resolve global declarations.**
  Bind module paths and imports.
  Distinguish namespaces explicitly.
  Enforce visibility and ambiguity rules.
- **Resolve body-local bindings.**
  Parameters, locals, patterns, and labels.
  Generic parameters and effect binders.
  Respect source evaluation order.
- **Build exact occurrence maps.**
  Every resolved token records target.
  Definitions and references share stable keys.
  Rename and navigation use one index.
- **Define privacy authority.**
  Source module identity controls private fields.
  Reexports preserve visibility rules.
  Downstream interfaces expose allowed facts only.
- **Support incomplete editor source.**
  Unresolved occurrences remain explicit.
  Recovery never invents stable targets silently.
  Suggestions come from separate candidate queries.

### Goals and non-goals

- **Goal: one resolution implementation.**
  Compiler and LSP share results.
  Elaboration consumes typed targets.
  No duplicate resolution map is built.
- **Goal: near-linear local lookup.**
  Scope maps avoid repeated reverse scans.
  Journaled frames restore efficiently.
  Shadowing is explicit.
- **Goal: precise reference indexing.**
  Token-level spans are retained.
  Generated references carry provenance.
  Cross-package references use interfaces.
- **Non-goal: final overload selection.**
  Resolution may return candidate sets.
  Types and traits choose later.
  Name lookup stays structurally defined.
- **Non-goal: global text search.**
  References are semantic occurrences.
  Comments and strings are separate.
  Rename relies on stable targets.

### Public queries and interfaces

- **`global_declaration_index`.**
  Index stable declarations by namespace.
  Include visibility and module ownership.
  Return ambiguity sets.
- **`resolved_imports`.**
  Expand module imports and reexports.
  Detect cycles and conflicts.
  Produce canonical bindings.
- **`resolved_body`.**
  Map syntax occurrences to targets.
  Include local binding identities.
  Attach recovery status.
- **`definition_at`.**
  Resolve source token or span.
  Return stable target and kind.
  Support generated-definition links.
- **`references_to`.**
  Return sorted semantic occurrences.
  Filter by package and visibility.
  Support rename safety checks.

### Primary data structures

- **`DefTable`.**
  Stores stable declarations and kinds.
  Stores parent module and visibility.
  Unifies nominal categories.
- **`NamespaceIndex`.**
  Maps module, name, and namespace.
  Returns small candidate ranges.
  Is canonical and immutable.
- **`ScopeMap`.**
  Stores active lexical bindings.
  Uses journaled insertion and rollback.
  Supports shadow chains.
- **`ResolvedTarget`.**
  Represents local, definition, label, or candidate set.
  Uses typed stable identities.
  Carries resolution class.
- **`OccurrenceIndex`.**
  Maps source token to target.
  Maps target to sorted occurrences.
  Stores access mode where known.

### Ownership and lifetime model

- **Global indexes have revision lifetime.**
  Built from package interfaces and shells.
  Shared by body queries.
  Immutable after publication.
- **Scope maps have body lifetime.**
  Body resolution owns mutable frames.
  Cleanup restores journals.
  Published occurrences use stable local keys.
- **Local binding identities belong to body.**
  They derive from stable body key.
  Dense IDs remain body-local.
  Tooling uses stable binding anchors.
- **Occurrence indexes may outlive syntax.**
  Store stable source anchors and targets.
  Avoid borrowing transient nodes.
  Rebuild presentation spans as needed.
- **Candidate sets borrow declaration indexes.**
  Published sets use stable key ranges.
  Elaboration may cache selections separately.
  Resolution does not mutate declarations.

### Algorithms and phase order

- **Build complete declaration table.**
  Collect all module shells first.
  Assign stable keys.
  Index by namespace.
- **Resolve imports and reexports.**
  Use module graph SCC handling.
  Apply visibility filters.
  Diagnose ambiguity deterministically.
- **Initialize body scope.**
  Insert generics and parameters.
  Insert visible labels and environments.
  Record owning declaration.
- **Walk body in source order.**
  Resolve references before later bindings.
  Enter and leave journaled scopes.
  Record every occurrence.
- **Publish resolution product.**
  Validate target ownership.
  Sort reverse-reference lists.
  Mark unresolved recovery entries.

### Semantic invariants

- **Every resolved target is visible.**
  Privacy checks use owning module identity.
  Reexports cannot increase authority improperly.
  Private fields require authorized source identity.
- **Every local binding has one lexical owner.**
  Shadowing creates a new identity.
  Scope exit removes it.
  Use before binding remains unresolved.
- **Namespaces are explicit.**
  Type and value names may coexist by policy.
  Label and effect spaces remain typed.
  Candidate sets never mix incompatible namespaces.
- **Occurrence maps are exhaustive for parsed names.**
  Every identifier token receives status.
  Unresolved is explicit.
  Synthetic names carry generated provenance.
- **Resolution never depends on type inference secretly.**
  Type-directed steps are modeled as later queries.
  Dependencies remain visible.
  Tooling can explain candidate selection.

### Cycles and fixed points

- **Import cycles use module SCCs.**
  Reexports may require fixed-point visibility.
  Illegal cycles diagnose.
  Canonical ordering stabilizes results.
- **Recursive declarations resolve through predeclared shells.**
  Bodies see complete global identities.
  Header legality is checked separately.
  No textual forward-reference hacks.
- **Trait method candidate cycles remain solver-owned.**
  Resolution supplies nominal candidates.
  Trait selection handles recursion.
  Occurrence target may be a selected method later.
- **Scope journals are acyclic stacks.**
  Frames record prior map state.
  Cleanup restores in reverse order.
  Bindings never own frames.
- **Reference-index backlinks avoid ownership cycles.**
  Store stable keys and ranges.
  Database owns both indexes.
  Eviction treats them as one product.

### Incremental dependencies and invalidation

- **Body resolution depends on visible declaration fingerprints.**
  Private unrelated modules stay irrelevant.
  Imported names create precise edges.
  Local edits stay body-local.
- **Import changes affect dependent modules.**
  Reexport fingerprints propagate downstream.
  Equal binding sets stop invalidation.
  Source spans may still update tooling.
- **Visibility changes affect access checks.**
  Target identities may remain stable.
  Resolution status changes.
  Downstream interfaces rerun.
- **Local rename changes local binding identity deliberately.**
  References in the body rerun.
  Other bodies remain green.
  Refactoring preview uses occurrence index.
- **Occurrence presentation depends on token spans.**
  Semantic target map may remain equal.
  Editor locations update separately.
  Code generation can reuse.

### Caching and persistence

- **Global declaration indexes persist with interfaces.**
  Canonical stable keys encode.
  Private package indexes may cache locally.
  Decoders validate namespaces.
- **Resolved imports may persist per module.**
  Keyed by interface and visibility fingerprints.
  Candidate lists sort canonically.
  Recovery results stay local.
- **Complete body resolution may persist.**
  Syntax and global-index fingerprints enter key.
  Local IDs remap canonically.
  Occurrence spans validate.
- **Reverse-reference indexes may be derived caches.**
  Forward occurrence map is authoritative.
  Backlinks rebuild deterministically.
  Large workspace indexes evict.
- **Rename plans never persist as semantic facts.**
  They depend on editor revision.
  They remain request-local.
  Stable occurrence products support recomputation.

### Diagnostics and explanations

- **Unresolved-name diagnostics show namespace.**
  Report searched module and scope.
  Offer visible candidates separately.
  Avoid misleading type suggestions.
- **Ambiguity diagnostics show all candidates.**
  Include import and declaration sites.
  Sort by stable key.
  Suggest qualification.
- **Privacy diagnostics show authority boundary.**
  Name defining module.
  Name attempted access site.
  Explain private representation role.
- **Shadowing diagnostics are lint-controlled.**
  Show previous and new binding.
  Respect deliberate pattern scopes.
  Stable codes enable policy.
- **Resolution explanations show lookup path.**
  Lexical scopes searched first.
  Then module and imports.
  Candidate filtering is inspectable.

### Cancellation, limits, and security

- **Scope depth is bounded.**
  Deep nested blocks charge budget.
  Journal restoration remains iterative.
  Excess reports body span.
- **Candidate counts are bounded.**
  Ambiguous imports cannot amplify memory.
  Lists truncate diagnostics safely.
  Full semantic rejection remains correct.
- **Import expansion is metered.**
  SCC nodes and edges charge limits.
  Malicious reexport graphs terminate.
  Cancellation checks between modules.
- **Imported indexes are hostile.**
  Stable keys and namespaces validate.
  Impossible visibility records reject.
  Cross-package private facts stay inaccessible.
- **Reference queries enforce package privacy.**
  Public tooling may redact hidden packages.
  Server policy controls cross-workspace exposure.
  Semantic compiler retains exact facts.

### Determinism and reproducibility

- **Candidate ordering uses stable keys.**
  Hash map insertion never affects ambiguity.
  Diagnostics remain stable.
  Method selection receives canonical lists.
- **Scope lookup follows lexical order.**
  Journal implementation cannot alter semantics.
  Shadow chains are deterministic.
  Recovery uses stable nearest scope.
- **Import fixed points use stable worklists.**
  Module SCC members sort.
  Reexport sets freeze canonically.
  Equal graphs reproduce.
- **Occurrence lists sort by logical source location.**
  Cross-package ties use stable package key.
  Editor results remain stable.
  Serialization matches.
- **Resolution fingerprints exclude local allocation.**
  Targets and binding anchors encode canonically.
  Span fingerprints remain separate.
  Clean and incremental products compare.

### Testing and observability

- **Namespace tests cover collisions.**
  Types, values, labels, and effects.
  Imports and local shadowing.
  Ambiguity remains precise.
- **Module visibility tests cover private fields.**
  Authorized and unauthorized destructuring.
  Reexports and nested modules.
  Downstream interfaces.
- **Scope tests exercise rollback.**
  Patterns, closures, and handlers.
  Early exits and recovery.
  Map state restores exactly.
- **Reference-index tests compare rename plans.**
  Include aliases and reexports.
  Exclude comments and strings.
  Preserve generated provenance.
- **Incremental tests edit imports and locals.**
  Expected queries rerun.
  Occurrence locations update.
  Clean resolution matches.

### Migration and completion criteria

- **Unify declaration namespaces.**
  Replace category-specific searches.
  Introduce `DefTable` and stable keys.
  Preserve diagnostic parity.
- **Introduce journaled `ScopeMap`.**
  Replace reverse linear scans.
  Add cleanup-backed frames.
  Benchmark compiler bodies.
- **Write resolution directly into typed occurrence tables.**
  Remove duplicate elaboration maps.
  Expose one semantic view.
  Update tooling.
- **Build reverse-reference query.**
  Derive from forward occurrences.
  Add rename safety.
  Route LSP features.
- **Complete when all clients share semantic resolution.**
  No text-search rename remains.
  Privacy is exact.
  Incremental fanout is narrow.

---

# Volume IV — Static Semantics

## 13. Semantic Types, Normalization, and Inference

This section defines semantic type representation and body-local inference.
It separates canonical resolved types from temporary inference terms.
Expected types guide elaboration without hiding dependencies.
Normalization and zonking produce stable published values.

### Purpose and scope

- **Represent every Glorious type.**
  Scalars, nominals, references, and callables.
  Effect rows and const arguments.
  Never and unit types.
- **Infer local unknowns.**
  Body sessions own inference variables.
  Expected types constrain expressions.
  Published products contain no unresolved variables.
- **Normalize semantic aliases.**
  Associated types and type aliases.
  Const and effect substitutions.
  Cycle policy is explicit.
- **Support precise diagnostics.**
  Keep origin constraints and expectations.
  Explain mismatches and ambiguity.
  Preserve source mapping separately.
- **Produce canonical type keys.**
  Zonk complete terms.
  Intern source-independent forms.
  Fingerprint semantic equality.

### Goals and non-goals

- **Goal: one semantic type model.**
  Frontend, Core, MIR, and tooling share keys.
  Backend copies are minimized.
  Layout facts use side tables.
- **Goal: expected-type elaboration.**
  Context guides literals and callables.
  Ambiguity is diagnosed.
  Inference remains deterministic.
- **Goal: explicit normalization.**
  Queries expose normalized forms.
  Cycles and overflow are typed outcomes.
  Caches record dependencies.
- **Non-goal: arbitrary coercion.**
  Conversions require specified rules.
  Hidden widening is avoided.
  Diagnostics show explicit choices.
- **Non-goal: persistent inference variables.**
  They never enter interfaces.
  They never enter cache keys.
  Incomplete IDE terms remain marked.

### Public queries and interfaces

- **`type_of_definition`.**
  Return canonical declared type.
  Include generic binders.
  Depend on interface facts.
- **`infer_body`.**
  Elaborate syntax under expected return type.
  Produce typed expressions and constraints.
  Return complete or recovered result.
- **`normalize_type`.**
  Reduce aliases and projections.
  Use canonical solver environment.
  Return normalized or blocked form.
- **`type_at`.**
  Map source occurrence to inferred type.
  Preserve recovery status.
  Support pretty presentation.
- **`type_facts`.**
  Return copyability and layout prerequisites.
  Memoize semantic properties.
  Avoid emitter recomputation.

### Primary data structures

- **`TypeKind`.**
  Direct algebraic semantic variants.
  Carries canonical child keys.
  Excludes source spans.
- **`InferType`.**
  Represents variable or structured term.
  Belongs to body inference arena.
  Stores origin for diagnostics.
- **`UnificationTable`.**
  Stores variable parents and values.
  Supports snapshots and rollback.
  Is body-local.
- **`TypeConstraint`.**
  Stores equality, subtype, or outlives relation.
  Carries cause and source owner.
  Uses typed operands.
- **`NormalizedTypeResult`.**
  Distinguishes complete, ambiguous, and cyclic.
  Carries dependencies and proof trace.
  Publishes canonical key when complete.

### Ownership and lifetime model

- **Database owns canonical types.**
  Interned values may share across revisions.
  Source origins are side data.
  Eviction permits reconstruction.
- **Body owns inference variables.**
  Variables never escape unzonked.
  Rollback supports speculative calls.
  Cleanup releases tables.
- **Constraint causes outlive solving locally.**
  Diagnostics retain compact explanation records.
  Full union-find history may drop.
  Published typed body stores final mapping.
- **Normalization queries own recursion state.**
  Active stacks are request-local.
  Complete normalized keys memoize.
  Blocked results follow policy.
- **Type presentation is client-owned.**
  Pretty names use source context.
  Canonical keys remain presentation-free.
  Width and color do not affect semantics.

### Algorithms and phase order

- **Create inference environment.**
  Insert generic and expected types.
  Allocate variables lazily.
  Set body-local budgets.
- **Elaborate expressions bidirectionally.**
  Check when expected type exists.
  Synthesize otherwise.
  Record every constraint cause.
- **Resolve overload candidates.**
  Instantiate generic signatures.
  Apply expected argument and result types.
  Leave trait obligations to solver.
- **Unify and normalize incrementally.**
  Propagate variable assignments.
  Normalize projections when evidence exists.
  Delay blocked goals safely.
- **Zonk and publish.**
  Reject unresolved release variables.
  Intern canonical types.
  Build source type map.

### Semantic invariants

- **Published types contain no body variables.**
  Zonk completes every reachable term.
  Recovery products mark unknowns explicitly.
  Interfaces remain canonical.
- **Type equality is source-independent.**
  Spans and diagnostic names are excluded.
  Aliases normalize according to rules.
  Equivalent terms intern equally.
- **Expected types never silently change evaluation.**
  They choose legal interpretations only.
  Argument order remains left to right.
  Ambiguous contextual blocks reject.
- **Normalization preserves kind correctness.**
  Type, effect, const, and lifetime arguments remain typed.
  Substitution cannot mix domains.
  Invalid decoded terms reject.
- **Inference rollback is complete.**
  Failed candidates restore assignments.
  Obligations and diagnostics roll back.
  Successful candidate commits once.

### Cycles and fixed points

- **Occurs checks prevent infinite inference terms.**
  Variable cannot contain itself structurally.
  Nominal recursion remains legal.
  Diagnostics show the cycle.
- **Alias normalization detects cycles.**
  Legal opaque boundaries stop expansion.
  Illegal transparent cycles reject.
  Active stacks use stable keys.
- **Associated type normalization uses tabled goals.**
  Solver cycles follow trait policy.
  Ambiguity remains explicit.
  Results memoize canonically.
- **Recursive type facts use SCC analysis.**
  Properties like zero-size may require fixed points.
  Widening is property-specific.
  Emission reads shared facts.
- **Inference dependency cycles resolve through constraints.**
  Worklists process changed variables.
  Nonprogress under unresolved ambiguity diagnoses.
  Iteration is budgeted.

### Incremental dependencies and invalidation

- **Declared type queries depend on headers and aliases.**
  Body edits do not affect them.
  Alias changes propagate through normalization.
  Equal canonical types stop fanout.
- **Body inference depends on syntax and visible signatures.**
  Unused declarations create no edge.
  Expected return type is explicit.
  Fixity grouping precedes inference.
- **Trait selections add solver dependencies.**
  Selected impl and candidate set matter.
  Unrelated impls may stay irrelevant.
  Coherence changes can broaden impact.
- **Source type maps depend on spans.**
  Semantic typed body may remain equal.
  Tooling maps rerun.
  Code generation may reuse.
- **Type-fact changes affect MIR and emission.**
  Copyability and drop facts are shared.
  Target layout facts remain separate.
  Optimizer invalidation is precise.

### Caching and persistence

- **Canonical type interner may persist frozen values.**
  Source spans are absent.
  Decoder validates kinds and children.
  Algorithm generation is included.
- **Complete typed bodies may persist.**
  Syntax and interface fingerprints enter key.
  Local IDs remap canonically.
  Recovery bodies usually stay local.
- **Normalization results are high-value caches.**
  Keyed by type and environment.
  Solver dependencies are recorded.
  Cyclic and ambiguous results use policy.
- **Unification tables never persist.**
  They are mutable body state.
  Only zonked products publish.
  Debug snapshots are optional traces.
- **Type facts persist separately.**
  Semantic properties are target-neutral.
  Layout facts key by target.
  Shared cache avoids emitter duplication.

### Diagnostics and explanations

- **Mismatch diagnostics retain both terms.**
  Pretty-print in source context.
  Show expected and found origins.
  Avoid only reporting IDs.
- **Inference ambiguity diagnostics list unresolved choices.**
  Candidate signatures are shown.
  Required annotations are suggested.
  Stable ordering is preserved.
- **Occurs-check diagnostics show recursive path.**
  Name variable origin.
  Show containing type structure.
  Bound output depth.
- **Normalization diagnostics explain blocked projections.**
  Show missing trait evidence.
  Show cyclic alias chain.
  Distinguish ambiguity from overflow.
- **Type-at explanations show derivation.**
  Declared, inferred, or coerced.
  List decisive constraints.
  Tooling can request deeper traces.

### Cancellation, limits, and security

- **Inference variable count is bounded.**
  Every allocation charges body budget.
  Overflow fails before index conversion.
  Diagnostics name the body.
- **Constraint processing is metered.**
  Worklist steps charge counters.
  Nonprogress cannot spin forever.
  Cancellation checks periodically.
- **Type depth is bounded.**
  Parsing, normalization, and printing.
  Explicit stacks avoid host overflow.
  Diagnostics truncate safely.
- **Imported types are hostile.**
  Kind arity and child indices validate.
  Recursive graphs follow schema rules.
  Impossible terms reject.
- **Pretty printers avoid source disclosure.**
  Private names follow visibility policy.
  Cache traces may redact full terms.
  User diagnostics remain useful.

### Determinism and reproducibility

- **Candidate selection uses stable ordering.**
  Equivalent candidates produce ambiguity.
  Hash order never selects silently.
  Diagnostics reproduce.
- **Unification worklists are deterministic.**
  Constraints process in stable order.
  Equivalent orderings yield equal zonked types.
  Tests permute inputs.
- **Interning is semantic.**
  Insertion order does not affect keys.
  Frozen tables sort values.
  Cache bytes reproduce.
- **Normalization traces use stable paths.**
  Alias and projection chains sort.
  Cycle representatives are canonical.
  Explanations remain stable.
- **Type presentation options are explicit.**
  Semantic fingerprints ignore formatting.
  JSON forms are canonical.
  Human width affects rendering only.

### Testing and observability

- **Inference tests cover bidirectional cases.**
  Literals, closures, and contextual blocks.
  Expected results and arguments.
  Ambiguity and annotations.
- **Normalization tests cover aliases and projections.**
  Cycles and recursive nominals.
  Associated types and consts.
  Compare canonical keys.
- **Rollback tests force candidate failure.**
  Unification state restores.
  Obligations disappear.
  Diagnostics do not leak.
- **Incremental tests change signatures and bodies.**
  Expected fanout is measured.
  Equal normalized types stop propagation.
  Clean typed bodies match.
- **Inspection exposes constraints and zonking.**
  Filter by expression.
  Show variable origins.
  Bound trace size.

### Migration and completion criteria

- **Unify semantic type representations.**
  Remove backend copies.
  Introduce canonical `TypeKey`.
  Preserve behavior through tests.
- **Move inference into body context.**
  Isolate temporary variables.
  Add rollback and causes.
  Measure memory release.
- **Add normalization queries.**
  Replace ad hoc recursive expansion.
  Record solver dependencies.
  Add cycle diagnostics.
- **Publish typed source maps.**
  Route hover and diagnostics.
  Separate span fingerprints.
  Remove alternate LSP inference.
- **Complete when interfaces contain canonical types.**
  No unresolved variables escape.
  Clean and incremental inference match.
  Type facts are shared downstream.

## 14. Generics, Traits, Associated Items, GATs, HRTBs, and Consts

This section defines generic abstraction and proof search.
Trait solving is canonicalized, tabled, coherent, and resource-bounded.
Associated types, effect rows, GATs, higher-ranked binders, and consts share typed substitution machinery.
Solver evidence is queryable and explainable.

### Purpose and scope

- **Represent generic binders.**
  Types, consts, lifetimes, effects, quantities.
  Binder order and kinds are explicit.
  Substitutions remain typed.
- **Solve trait obligations.**
  Select coherent implementations.
  Normalize associated items.
  Produce evidence for elaboration.
- **Support higher-ranked reasoning.**
  Introduce placeholder universes.
  Prevent leaked inference variables.
  Explain failed generality.
- **Support GATs and associated rows.**
  Instantiate nested binders safely.
  Enforce where clauses.
  Normalize through selected impls.
- **Support structural consts.**
  Canonicalize finite values.
  Evaluate allowed expressions.
  Integrate quantities and array-like types.

### Goals and non-goals

- **Goal: one canonical solver.**
  Compiler and tooling share answers.
  Query tables record dependencies.
  Evidence presentation is inspectable.
- **Goal: coherence before selection.**
  Overlap and orphan rules are explicit.
  Candidate order never decides semantics.
  Ambiguity is a result.
- **Goal: typed universes.**
  Higher-ranked placeholders cannot escape.
  Leak checking is explicit.
  Diagnostics name binder levels.
- **Non-goal: unrestricted specialization.**
  G1 avoids overlapping preference rules.
  Implementations are coherent.
  Future changes require explicit design.
- **Non-goal: arbitrary compile-time execution.**
  Const evaluation is finite and specified.
  Host effects are unavailable.
  Resource limits apply.

### Public queries and interfaces

- **`canonical_goal`.**
  Replace inference variables with binders.
  Record universe and environment.
  Produce stable solver key.
- **`solve_goal`.**
  Return unique, ambiguous, or impossible.
  Carry selected impl and evidence.
  Record candidate-set dependencies.
- **`normalize_projection`.**
  Resolve associated type or effect row.
  Use selected implementation evidence.
  Return blocked results explicitly.
- **`coherence_check`.**
  Validate impl set per trait.
  Enforce orphan rules.
  Produce overlap diagnostics.
- **`evaluate_const`.**
  Normalize structural const expression.
  Return canonical const key.
  Preserve resource and error status.

### Primary data structures

- **`GenericBinder`.**
  Stores kind and variance context.
  Stores defaults if supported.
  Uses stable declaration identity.
- **`Substitution`.**
  Stores typed argument vectors.
  Validates arity and kinds.
  Canonicalizes complete terms.
- **`CanonicalGoal`.**
  Stores predicate and bound variables.
  Stores environment and universes.
  Excludes source spans.
- **`SolverTableEntry`.**
  Stores running or complete state.
  Stores dependencies and answer set.
  Supports coinductive policy.
- **`EvidenceTerm`.**
  Represents selected implementation proof.
  Carries associated item mappings.
  Erases before runtime when static.

### Ownership and lifetime model

- **Trait and impl declarations have revision lifetime.**
  Interfaces publish stable records.
  Solver queries borrow them.
  Coherence products may persist.
- **Canonical goals are database-owned values.**
  Interned goals may share.
  Source causes remain body-local side data.
  Tables key by canonical goal.
- **Solver stacks are request-local.**
  Running entries use query frames.
  Provisional answers do not escape.
  Cancellation clears active state.
- **Evidence terms belong to typed products.**
  Body elaboration stores compact evidence.
  Static evidence may erase later.
  Diagnostics retain proof summaries.
- **Const-evaluation scratch is query-local.**
  Canonical values publish.
  Evaluation stacks release.
  Host state is unavailable.

### Algorithms and phase order

- **Collect trait and impl heads.**
  Resolve binders and where clauses.
  Build candidate indexes.
  Run coherence prerequisites.
- **Canonicalize an obligation.**
  Replace local variables with canonical binders.
  Normalize environment facts.
  Construct stable goal key.
- **Enumerate candidates deterministically.**
  Filter by trait and nominal head.
  Instantiate fresh variables.
  Apply where-clause subgoals.
- **Table and solve recursively.**
  Detect active goals.
  Apply cycle and coinduction policy.
  Accumulate unique answer set.
- **Reify evidence and normalization.**
  Map canonical answer to body variables.
  Resolve associated items.
  Publish proof summary.

### Semantic invariants

- **Substitutions are kind-correct.**
  Type arguments cannot fill const binders.
  Arity is exact.
  Higher-ranked binders preserve scope.
- **Implementation selection is coherent.**
  At most one applicable answer under rules.
  Ambiguity never selects by order.
  Orphan policy is enforced.
- **Placeholder universes do not leak.**
  Lower-universe variables cannot capture them.
  Leak check runs before success.
  Evidence records binder scope.
- **Associated normalization follows evidence.**
  No name-based shortcuts.
  Missing evidence remains blocked.
  Cycles are explicit.
- **Const evaluation is deterministic and pure.**
  No host effects or time.
  Arithmetic follows language semantics.
  Overflow policy is specified.

### Cycles and fixed points

- **Solver tables detect recursive goals.**
  Coinductive traits opt in explicitly.
  Inductive cycles remain ambiguous or fail.
  Cycle traces are stable.
- **Associated type cycles use normalization stacks.**
  Opaque boundaries stop expansion.
  Illegal cycles diagnose.
  Recursive nominal references remain legal.
- **Supertrait graphs use SCCs.**
  Cyclic inheritance policy is explicit.
  Evidence closure computes deterministically.
  Duplicate facts deduplicate.
- **Const recursion is tightly limited.**
  General recursion is excluded unless specified.
  Evaluation depth is bounded.
  Cycles report source chains.
- **Coherence checks compare impl pairs deterministically.**
  Candidate pair generation is canonical.
  Overlap subgoals use the same solver.
  Budgets bound quadratic growth.

### Incremental dependencies and invalidation

- **Goals depend on candidate sets.**
  Adding a relevant impl invalidates selection.
  Unrelated traits stay green.
  Head indexes narrow dependencies.
- **Associated normalization depends on selected impl.**
  Body changes of unrelated methods do not matter.
  Interface changes do.
  Equal normalized values stop fanout.
- **Coherence depends on all impl heads for a trait.**
  Private body edits remain irrelevant.
  New impls rerun pair checks.
  Trait declaration changes broaden impact.
- **Higher-ranked changes affect binder fingerprints.**
  Equivalent alpha-renaming remains equal.
  Universe structure is canonical.
  Diagnostics may update spans separately.
- **Const values depend on expression and primitive semantics.**
  Target-neutral evaluation may reuse.
  Target-dependent layout consts key by target.
  Limit observations are recorded.

### Caching and persistence

- **Canonical solver answers are cacheable.**
  Goal and environment enter key.
  Candidate-set fingerprints are dependencies.
  Validators check evidence identities.
- **Coherence products persist with interfaces.**
  Downstream compilers may trust only after validation.
  Impl heads serialize canonically.
  Impossible overlap claims are rechecked.
- **Associated normalization caches separately.**
  Common projections reuse widely.
  Cyclic and ambiguous outcomes use policy.
  Source causes are excluded.
- **Const values are canonical persistent terms.**
  Evaluation scratch does not persist.
  Arithmetic generation enters identity.
  Host paths remain absent.
- **Negative answers require closed-world evidence.**
  Cache only when candidate set is complete.
  Open effect rows may block certainty.
  Future impl additions invalidate.

### Diagnostics and explanations

- **Unsatisfied trait diagnostics show goal.**
  Pretty-print canonical predicate.
  Show relevant candidates and failures.
  Bound recursive explanation depth.
- **Ambiguity diagnostics list viable impls.**
  Sort by stable declaration key.
  Show unresolved subgoals.
  Suggest qualification or annotation.
- **Coherence diagnostics show overlap witness.**
  Point to both impl declarations.
  Show unifying substitution.
  Explain orphan context.
- **Higher-ranked diagnostics show leak path.**
  Name placeholder universe.
  Show captured variable.
  Explain required generality.
- **Const diagnostics show evaluation trace.**
  Identify overflow or unsupported operation.
  Report recursion or step limit.
  Preserve source locations.

### Cancellation, limits, and security

- **Goal table size is bounded.**
  Each canonical goal charges budget.
  Duplicate goals reuse entries.
  Excess reports owning body.
- **Candidate enumeration is bounded.**
  Trait indexes narrow search.
  Diagnostics truncate candidate display only.
  Semantic ambiguity remains exact.
- **Solver recursion uses explicit stacks.**
  Host stack overflow is avoided.
  Cancellation checks between subgoals.
  Active states clean up.
- **Const evaluation is metered.**
  Steps and memory charge budgets.
  No host capabilities are present.
  Malicious expressions terminate.
- **Imported evidence is hostile.**
  Stable impl identities validate.
  Proof structure is checked.
  Impossible associated mappings reject.

### Determinism and reproducibility

- **Candidate indexes freeze canonically.**
  Impl source order does not select answers.
  Ambiguity lists remain stable.
  Cache keys reproduce.
- **Canonicalization is alpha-stable.**
  Binder names do not affect goals.
  Universe numbering follows deterministic traversal.
  Equivalent goals share keys.
- **Solver worklists use stable order.**
  Subgoals and answers sort.
  Fixed-point behavior reproduces.
  Performance remains comparable.
- **Evidence serialization is canonical.**
  Selected impl and substitutions encode.
  Local variables remap.
  Re-encoding matches.
- **Const arithmetic is platform-independent.**
  Widths and overflow are explicit.
  Host integer behavior cannot leak.
  Bootstrap stages agree.

### Testing and observability

- **Trait tests cover positive and negative goals.**
  Generics, supertraits, and associated items.
  Ambiguity and coherence.
  Compare self-host and Rust results.
- **GAT tests cover nested binders.**
  Lifetimes, effects, and consts.
  Higher-ranked projections.
  Exact normalization results.
- **HRTB tests stress universe leaks.**
  Accepted general functions.
  Rejected captures.
  Stable diagnostics.
- **Const tests cover full-width values.**
  Overflow and conversions.
  Structural equality.
  Resource limits.
- **Solver inspection exports proof trees.**
  Filter by goal.
  Show table reuse and cycles.
  Bound output size.

### Migration and completion criteria

- **Canonicalize existing trait goals.**
  Wrap current solver entry points.
  Add stable key and table.
  Preserve acceptance parity.
- **Unify generic substitution machinery.**
  Types, lifetimes, effects, and consts.
  Remove ad hoc vectors.
  Add kind checks.
- **Add associated normalization queries.**
  Replace emitter-side recomputation.
  Record evidence dependencies.
  Add cycle diagnostics.
- **Port coherence and higher-ranked tests.**
  Expand self-host parity ledger.
  Add exact proof snapshots.
  Measure solver bounds.
- **Complete when solver answers are shared facts.**
  Tooling and compiler agree.
  Evidence is canonical.
  Relevant impl changes invalidate precisely.

## 15. Effects, Effect Rows, Handlers, Resumptions, and Cancellation

This section defines Glorious effect typing and resumptive control.
Effects are nominal, rows are exact, and continuation quantities are explicit.
Handlers, forwarding, replay, and cancellation integrate with ownership and borrowing.
No separate ad hoc control system is introduced.

### Purpose and scope

- **Represent nominal effects and operations.**
  Declarations define operation signatures.
  Instances carry generic arguments.
  Names alone grant no authority.
- **Represent open and closed effect rows.**
  Row variables support polymorphism.
  Duplicate instances normalize.
  Outward effects remain explicit.
- **Type deep handlers.**
  Clauses receive operation payload and continuation.
  Unhandled operations forward outward.
  Result types are unified.
- **Type resumptions and cancellation.**
  One-shot and finite multi-shot quantities.
  Captured owners are accounted.
  Illegal abandonment is rejected.
- **Lower effects into explicit control.**
  Typed Core and MIR preserve operations.
  Optimizer may specialize static handlers.
  VM executes verified handler machinery.

### Goals and non-goals

- **Goal: exact effect accounting.**
  Functions state possible effects.
  Calls compose rows.
  Handlers subtract handled instances.
- **Goal: ordinary typed continuations.**
  Resumptions share callable mechanisms.
  Quantities constrain invocation.
  Captures use normal ownership facts.
- **Goal: compositional forwarding.**
  Partial handlers preserve outward rows.
  Deep reinstatement is explicit.
  Nested suspension remains sound.
- **Non-goal: hidden exceptions.**
  Failure and return are source abstractions.
  Compiler-only unwinding is avoided.
  Effects remain visible in types.
- **Non-goal: unbounded replay in G1.**
  Finite quantities are supported.
  Unlimited multishot needs separate runtime policy.
  Unsupported cases reject.

### Public queries and interfaces

- **`effect_interface`.**
  Return nominal operations and binders.
  Include continuation quantity contracts.
  Use stable effect identity.
- **`normalize_effect_row`.**
  Sort instances and variables.
  Apply substitutions.
  Detect duplicates and conflicts.
- **`effects_of_body`.**
  Infer exact outward row.
  Attach operation source map.
  Return complete or recovered status.
- **`handler_plan`.**
  Match handled operations and clauses.
  Compute residual outward row.
  Determine continuation types.
- **`resumption_summary`.**
  Report quantity, captures, and legality.
  Include cancellation obligations.
  Support optimizer and diagnostics.

### Primary data structures

- **`EffectKey`.**
  Stable nominal effect identity.
  Carries generic binder schema.
  Serializes canonically.
- **`EffectInstance`.**
  Stores effect key and substitutions.
  Is interned after normalization.
  Excludes source spans.
- **`EffectRow`.**
  Stores sorted concrete instances.
  Stores optional row variable.
  Tracks openness explicitly.
- **`HandlerClause`.**
  Stores operation identity and binder mapping.
  Stores continuation callable type.
  Stores source owner.
- **`ResumptionType`.**
  Stores input, output, effects, and quantity.
  Stores environment brand.
  Integrates callable evidence.

### Ownership and lifetime model

- **Effect declarations have interface lifetime.**
  Stable keys cross packages.
  Operation signatures are immutable.
  Source spans remain auxiliary.
- **Effect-row inference is body-local.**
  Row variables live in inference tables.
  Normalized rows intern on publication.
  Unresolved rows stay recovered.
- **Handler clause syntax has body lifetime.**
  Typed handler plans may persist.
  Continuation captures publish through Core.
  Parser nodes can drop.
- **Resumption environments follow callable ownership.**
  Captured places belong to continuation state.
  One-shot moves consume the environment.
  Multishot requires copy-valid captures.
- **Runtime handler records belong to frames.**
  VM allocation follows verified plans.
  Cancellation cleanup uses encoded maps.
  Host effects remain separate capabilities.

### Algorithms and phase order

- **Collect effect declarations.**
  Resolve operation types and quantities.
  Build operation lookup index.
  Validate duplicate operation names.
- **Infer operation performance.**
  Resolve effect instance.
  Instantiate operation signature.
  Add instance to body row.
- **Elaborate handler clauses.**
  Match operations deterministically.
  Bind payload and continuation.
  Infer clause result and effects.
- **Compute residual row.**
  Remove handled instances.
  Add clause outward effects.
  Preserve open variables.
- **Check resumption actions.**
  Apply quantity and capture obligations.
  Validate resume or cancel paths.
  Lower explicit control to Core.

### Semantic invariants

- **Rows are canonical sets with openness.**
  Duplicate concrete instances collapse by rules.
  Order has no semantic meaning.
  Row variables remain typed.
- **Every perform targets one operation.**
  Effect instance and operation must match.
  Payload type is checked.
  Result type follows signature.
- **Handlers are deep according to specification.**
  Resumed continuations reinstall context.
  Forwarded operations preserve semantics.
  Optimizations must prove equivalent behavior.
- **Resumption quantity matches actual use.**
  Replay counts every invocation.
  Cancellation counts abandonment.
  Captured exact-use owners remain sound.
- **Borrowed payloads preserve origins.**
  Reference-bearing operations carry lifetime facts.
  Suspensions cannot extend illegal loans.
  VM summaries remain verifier-checkable.

### Cycles and fixed points

- **Effect-row aliases detect cycles.**
  Open aliases follow explicit policy.
  Illegal transparent cycles reject.
  Normalization uses active stacks.
- **Recursive handlers may call effectful bodies.**
  Call-summary SCCs infer outward rows.
  Widening preserves sound upper sets.
  Results are deterministic.
- **Deep handler reinstatement creates runtime cycles conceptually.**
  MIR represents explicit control edges.
  Verifier tracks handler identity.
  VM frames own finite records.
- **Multishot replay uses finite quantity loops.**
  Static checks account repeated captures.
  Runtime continuation state is cloneable only when valid.
  Unbounded replay remains excluded.
- **Solver cycles involving effects are tabled.**
  `Fn` and associated effect rows may recurse.
  Canonical goals handle cycles.
  Ambiguity remains explicit.

### Incremental dependencies and invalidation

- **Bodies depend on performed operation interfaces.**
  Unused effect changes stay irrelevant.
  Signature changes invalidate performers.
  Equal normalized rows stop fanout.
- **Handlers depend on operation sets they mention.**
  New unrelated operations do not matter.
  Partial-handler candidate changes may.
  Clause body edits stay local.
- **Callable summaries depend on exact effect rows.**
  Callers validate when callee rows change.
  Implementation-only changes may preserve summaries.
  Optimizer plans use separate edges.
- **Resumption summaries depend on capture and quantity facts.**
  Borrow or use changes invalidate handler lowering.
  Source span changes affect tooling only.
  Static equality may preserve code.
- **Runtime feature changes affect emission and verification.**
  Source typing may reuse.
  Artifact feature sets rerun.
  VM compatibility is explicit.

### Caching and persistence

- **Normalized effect rows are interned and cacheable.**
  Canonical instance order encodes.
  Row variables use stable binders.
  Source spans are excluded.
- **Effect interfaces persist across packages.**
  Operation signatures and quantities encode.
  Defensive decoders validate arity.
  Primitive authority remains manifest-bound.
- **Typed handler plans may persist with Core.**
  Local clause IDs remap.
  Capture summaries validate.
  Recovered plans stay local.
- **Call effect summaries are high-value caches.**
  Recursive SCC results may group.
  Candidate dependencies are recorded.
  Optimizer consumes the same summary.
- **Runtime specialization plans cache separately.**
  They depend on optimized MIR and known handlers.
  Source semantic caches remain reusable.
  Residual machinery is encoded explicitly.

### Diagnostics and explanations

- **Unhandled-effect diagnostics show outward row.**
  Name operation and effect instance.
  Show nearest handler boundaries.
  Suggest signature update or handling.
- **Handler mismatch diagnostics show clause contract.**
  Payload and continuation types.
  Duplicate or missing operation clauses.
  Residual row explanation.
- **Resumption diagnostics show quantity arithmetic.**
  Allowed versus actual resumes.
  Captured owner multiplied uses.
  Cancellation obligations.
- **Borrow-across-suspension diagnostics show origin path.**
  Loan creation and perform site.
  Continuation capture boundary.
  Required lifetime relation.
- **Control-plan explanations show specialization.**
  Static handler facts.
  Removed runtime machinery.
  Residual forwarding reasons.

### Cancellation, limits, and security

- **Effect-row size is bounded.**
  Concrete instances charge budget.
  Normalization deduplicates before growth.
  Excess reports callable context.
- **Handler clause count is bounded.**
  Decision structures use explicit limits.
  Duplicate diagnostics truncate presentation only.
  Semantic matching remains exact.
- **Continuation capture size is bounded.**
  Place count and payload size charge budgets.
  Runtime allocation plans are checked.
  Oversized captures reject.
- **Nested suspension depth is bounded for analysis.**
  Explicit control graphs avoid host recursion.
  VM runtime uses supervisor limits.
  Verifier work is metered.
- **Host effects require runtime capabilities separately.**
  Source row legality is insufficient.
  Artifact declares imports.
  Supervisor grants exact operations.

### Determinism and reproducibility

- **Effect rows sort by stable effect key.**
  Generic substitutions encode canonically.
  Equivalent rows share fingerprints.
  Diagnostics order follows source use.
- **Handler matching order is semantic.**
  Clause source order matters only where specified.
  Candidate maps are canonical.
  Ambiguity reports are stable.
- **Resumption quantity calculations use exact arithmetic.**
  Saturation policy is specified.
  No platform integer behavior leaks.
  Proof traces reproduce.
- **Specialization decisions use stable summaries.**
  Cost ties use stable keys.
  Pass order is fixed.
  Residual bytecode matches across runs.
- **Runtime feature manifests are canonical.**
  Effect opcodes and tables sort.
  Handler identities remap deterministically.
  Stage artifacts match.

### Testing and observability

- **Effect typing tests cover open and closed rows.**
  Generic effects and aliases.
  Partial handlers and forwarding.
  Exact inferred rows.
- **Resumption tests cover zero, one, and finite many.**
  Resume and cancel paths.
  Captured owners and references.
  Accepted and rejected programs.
- **Deep-handler tests compare interpreter and VM.**
  Nested forwarding and reinstatement.
  Clause effects and return values.
  Cleanup behavior.
- **Optimizer tests inspect control plans.**
  Static handler fusion.
  One-shot allocation elimination.
  Residual dynamic cases.
- **Verifier fuzzing mutates handler metadata.**
  Identity, capture, and cleanup records.
  Extreme counts and malformed edges.
  Bounded rejection.

### Migration and completion criteria

- **Canonicalize effect interfaces and rows.**
  Replace ad hoc vectors.
  Add stable effect keys.
  Preserve current acceptance.
- **Unify resumptions with callable kernel.**
  Share signatures and quantities.
  Share capture layout.
  Remove parallel machinery.
- **Lower all handler control explicitly.**
  Extend MIR directly.
  Avoid a parallel stage representation.
  Validate cleanup edges.
- **Add resumption proof explanations.**
  Connect quantity and borrowing diagnostics.
  Expose optimizer control plans.
  Expand parity tests.
- **Complete when effects are ordinary typed control.**
  Source, Core, MIR, verifier, and VM agree.
  No hidden exception path remains.
  Static specialization preserves semantics.

## 16. Quantitative Use and Ownership Obligations

This section defines Glorious's interval-based use system.
Every value, callable, environment, and continuation has quantitative obligations.
Branching, repetition, capture, replay, and cancellation share one arithmetic.
Private representation controls who may finish consumption.

### Purpose and scope

- **Represent principal use intervals.**
  Lower and upper bounds define permission.
  Exact, affine, unrestricted, and zero-use cases.
  Bounds are structural const values.
- **Compute actual path use.**
  Sequence, branch, loop, and call composition.
  Capture and continuation multiplication.
  Destruction contributes zero use.
- **Track must-move obligations.**
  Positive lower bounds require transfer.
  Every successful path discharges obligations.
  Abort and proven divergence are exceptions.
- **Infer copy versus move.**
  Final legal use may transfer automatically.
  Earlier duplicable uses copy.
  Explicit `move` overrides inference.
- **Enforce opaque consumption authority.**
  Private fields block external deconstruction.
  Authorized functions can finish obligations.
  Universal destroy escapes are forbidden.

### Goals and non-goals

- **Goal: one quantity engine.**
  Values and resumptions share arithmetic.
  Environment transitions share containment.
  Availability uses the same intervals.
- **Goal: explain every failure.**
  Show path-derived interval.
  Show principal permission.
  Show undisposed obligation origin.
- **Goal: support partial moves.**
  Aggregate shells and fields track separately.
  Patterns create move paths.
  Cleanup sees remaining active subtrees.
- **Non-goal: implicit obligation erasure.**
  Cleanup cannot satisfy positive use.
  Dropping is zero use.
  Opaque destruction requires permission.
- **Non-goal: unrestricted global restricted-use values.**
  Memoized globals require unrestricted use.
  Compiler does not invent singleton access.
  Unsupported patterns reject.

### Public queries and interfaces

- **`principal_use`.**
  Return canonical interval for a type.
  Use trait evidence and structural rules.
  Explain derivation.
- **`body_use_summary`.**
  Compute place uses across control flow.
  Return obligations and final-use choices.
  Attach source mapping.
- **`use_at`.**
  Explain a specific occurrence.
  Distinguish copy, move, borrow, destroy.
  Show remaining obligation state.
- **`resumption_quantity`.**
  Compute actual continuation invocation interval.
  Multiply captured owner uses.
  Check cancel legality.
- **`cleanup_eligibility`.**
  Determine whether abandoned subtree permits zero use.
  Return exact blocking place.
  Feed MIR cleanup construction.

### Primary data structures

- **`UseInterval`.**
  Stores lower and upper quantities.
  Supports infinity explicitly.
  Uses checked arithmetic.
- **`QuantityExpr`.**
  Represents symbolic generic quantities.
  Normalizes structural const operations.
  Has canonical key.
- **`PlaceUseState`.**
  Stores availability and obligation.
  Stores accumulated actual interval.
  Tracks partial paths.
- **`UseDerivation`.**
  Records sequence, branch, and repeat operations.
  Stores source causes.
  Supports bounded explanation.
- **`ObligationSet`.**
  Maps active move paths to required intervals.
  Merges at CFG joins.
  Publishes deterministic facts.

### Ownership and lifetime model

- **Principal intervals have type lifetime.**
  Canonical results may cache.
  Generic expressions stay interned.
  Source proof origins are side data.
- **Body use state is analysis-local.**
  Worklists mutate temporary tables.
  Published facts become immutable.
  Scratch releases after lowering.
- **Obligations belong to places.**
  Whole transfer moves the obligation.
  Copies create independent obligations when required.
  Destruction does not transfer it.
- **Use derivations may be compacted.**
  Diagnostics retain decisive paths.
  Full analysis history may drop.
  Developer traces can preserve more.
- **Cleanup plans borrow published facts.**
  MIR does not recompute quantities independently.
  Verifier consumes lowered summaries.
  Runtime follows validated plans.

### Algorithms and phase order

- **Compute principal type intervals.**
  Solve explicit `Use` evidence.
  Derive structural aggregate permissions.
  Detect cyclic type facts.
- **Build control-flow use graph.**
  Lower evaluation order explicitly.
  Create place and move paths.
  Seed initial obligations.
- **Propagate actual use.**
  Sequence adds quantities.
  Exclusive branches take hulls.
  Nested execution multiplies.
- **Handle repetition and recursion.**
  Widen intervals under loops.
  Use call summaries for recursion.
  Report nonconvergent bounds.
- **Check containment and disposition.**
  Actual interval fits principal interval.
  Positive obligations leave no successful path.
  Record copy-versus-move choices.

### Semantic invariants

- **Lower never exceeds upper.**
  Every interval validates.
  Infinity arithmetic is explicit.
  Overflow widens safely or errors.
- **Sequence and branch operators follow specification.**
  Implementations share one library.
  No feature-specific quantity math.
  Proof traces identify operations.
- **Positive lower bounds imply must-move.**
  Successful scope exit cannot abandon them.
  Cleanup cannot erase them.
  Transfer preserves obligation identity.
- **Copies do not discharge originals.**
  Each copy receives its own use state.
  Original remains active until transferred.
  Final-use inference is path-sensitive.
- **Private representation gates deconstruction.**
  Visibility is checked first.
  Unauthorized wildcard destruction requires zero-use permission.
  Opaque owners must be transferred.

### Cycles and fixed points

- **Loop use uses widening.**
  Repeated positive use may become unbounded.
  Stable fixed point is required.
  Budgets bound iteration.
- **Recursive call summaries form SCCs.**
  Quantities propagate across calls.
  Widening is conservative.
  Stable group fingerprints publish.
- **Recursive type principal uses use property SCCs.**
  Structural facts iterate.
  Explicit impl evidence may break cycles.
  Illegal principal ambiguity diagnoses.
- **Continuation replay multiplies nested cycles.**
  Finite resumption bounds remain exact.
  Unbounded cases reject in G1.
  Captured obligations feed the equation.
- **Obligation derivation cycles collapse for diagnostics.**
  Show representative loop.
  Report widened interval.
  Avoid infinite explanation trees.

### Incremental dependencies and invalidation

- **Principal use depends on type and impl evidence.**
  Body edits do not affect it.
  `Use` impl changes propagate.
  Equal intervals stop fanout.
- **Body use depends on typed Core and CFG shape.**
  Span-only changes affect explanations.
  Type-preserving expression changes may still alter use.
  Call summaries are explicit dependencies.
- **Final-use choices depend on occurrence order.**
  Inserted uses invalidate the relevant path.
  Unrelated places remain green.
  Source maps update separately.
- **Cleanup eligibility depends on obligations.**
  Quantity changes invalidate MIR cleanup.
  Optimizer transformations revalidate facts.
  Verifier summaries change with plans.
- **Private authority depends on module identity.**
  Moving source modules may alter legality.
  Type shape can remain equal.
  Visibility fingerprints propagate.

### Caching and persistence

- **Principal interval results are cacheable.**
  Canonical type and impl environment key them.
  Derivation summaries may persist.
  Decoders validate arithmetic terms.
- **Body use facts may persist with PlaceFlow.**
  Typed place IDs remap.
  Core and call-summary fingerprints enter key.
  Recovery analyses stay local.
- **Loop and call summaries cache by SCC.**
  Member set and inputs are canonical.
  Widened bounds encode explicitly.
  Changes invalidate the group.
- **Copy-versus-move decisions persist in typed products.**
  They are semantic lowering facts.
  Source spans remain auxiliary.
  Optimizer may refine only with proof.
- **Diagnostic derivations may be recomputed.**
  Compact facts remain authoritative.
  Full explanation caches are optional.
  Presentation settings stay external.

### Diagnostics and explanations

- **Containment failures show both intervals.**
  Actual versus principal.
  Show arithmetic by control path.
  Highlight first exceeding operation.
- **Must-move failures show undisposed place.**
  Point to creation and exit.
  Show paths that abandon it.
  Suggest transfer to authorized code.
- **Replay failures show captured multiplication.**
  Continuation count times owner use.
  Show offending capture.
  Explain one-shot alternatives.
- **Cleanup failures show zero-use barrier.**
  Name active subtree.
  Show its principal lower bound.
  Explain why destruction is illegal.
- **Private deconstruction failures explain authority.**
  Name defining module.
  Name hidden field.
  Suggest public consuming API.

### Cancellation, limits, and security

- **Quantity expression depth is bounded.**
  Generic arithmetic uses explicit limits.
  Normalization terminates.
  Diagnostics show the expression.
- **Place and move-path counts are bounded.**
  Aggregates cannot amplify indefinitely.
  Checked allocation prevents overflow.
  Resource errors name the body.
- **Fixed-point iterations are metered.**
  Loop and SCC analyses charge budgets.
  Widening guarantees progress where possible.
  Cancellation checks between rounds.
- **Imported quantity evidence is hostile.**
  Bounds and trait identities validate.
  Impossible intervals reject.
  Infinity encodings are checked.
- **No hidden destruction capability exists.**
  Runtime opcodes follow verified plans.
  Host calls cannot erase language obligations.
  Unsafe FFI remains excluded.

### Determinism and reproducibility

- **Interval arithmetic is platform-independent.**
  Quantity widths and saturation are specified.
  Infinity has canonical encoding.
  Proofs reproduce.
- **Worklists use stable place order.**
  Join and widening order is fixed.
  Equivalent CFGs yield equal facts.
  Tests permute insertion.
- **Final-use tie breaking follows source evaluation order.**
  No hash order influences moves.
  Explicit `move` remains decisive.
  MIR reproduces.
- **Derivation summaries use canonical paths.**
  Branch labels and SCC roots are stable.
  Diagnostics sort.
  Cache bytes match.
- **Private authority uses logical module identity.**
  Host paths do not affect legality.
  Cross-platform builds agree.
  Bootstrap stages match.

### Testing and observability

- **Arithmetic unit tests cover every operator.**
  Sequence, hull, multiplication, widening.
  Finite and infinite bounds.
  Overflow policy.
- **Path tests cover branches and loops.**
  Exact-positive owners.
  Affine and unrestricted values.
  Proven divergence and abort.
- **Capture tests cover closures and resumptions.**
  One-shot and multishot.
  Copies and unique references.
  Cancellation paths.
- **Privacy tests cover opaque resources.**
  Authorized and unauthorized destructuring.
  Wildcards and rest patterns.
  Public consuming functions.
- **Inspection exposes use facts by place.**
  Show current interval and obligation.
  Show move path and source uses.
  Filter derivation depth.

### Migration and completion criteria

- **Centralize interval arithmetic first.**
  Replace duplicated quantity logic.
  Add exhaustive unit tests.
  Preserve current acceptance.
- **Build shared place-use analysis.**
  Move syntax-specific final-use logic outward.
  Connect PlaceFlow.
  Compare MIR outcomes.
- **Integrate resumption quantities.**
  Remove separate continuation counters.
  Multiply captures through same engine.
  Add diagnostics.
- **Move cleanup legality to published facts.**
  MIR consumes one source.
  Verifier cross-checks summaries.
  Add hostile tests.
- **Complete when every consumption path is explainable.**
  No feature-specific escape remains.
  Private authority is enforced.
  Optimized and unoptimized facts agree.

---

# Volume V — Semantic Core and Ownership

## 17. Regions, Lifetimes, Borrowing, and Reborrowing

This section defines nonlexical region inference and loan legality.
Shared and unique references integrate with moves, effects, captures, and cleanup.
Region facts use PlaceFlow rather than a parallel ownership subsystem.
Higher-ranked placeholders and drop checking remain explicit.

### Purpose and scope

- **Represent reference origins and regions.**
  Every reference points to a place origin.
  Regions describe validity constraints.
  Shared and unique modes are distinct.
- **Infer nonlexical lifetimes.**
  Uses determine required regions.
  Loans end when no longer needed.
  CFG facts drive the solution.
- **Support reborrowing.**
  Shared and unique reborrows create derived loans.
  Parent availability is restricted appropriately.
  End-borrow restores access.
- **Integrate suspension and captures.**
  References crossing effects need valid origins.
  Continuations preserve lifetime summaries.
  Multishot unique captures reject.
- **Enforce drop and escape rules.**
  References cannot outlive owners.
  Labels and environments carry region dependencies.
  Custom destruction respects active loans.

### Goals and non-goals

- **Goal: one loan graph.**
  Ordinary code, closures, and handlers share facts.
  Cleanup sees the same loans.
  Optimizer reads proven end points.
- **Goal: precise NLL behavior.**
  Lexical scopes do not overconstrain.
  CFG use points define regions.
  Diagnostics show last relevant use.
- **Goal: higher-ranked soundness.**
  Placeholder universes are explicit.
  Leak checks prevent escaping references.
  Trait solver shares universe machinery.
- **Non-goal: unsafe references.**
  Raw pointers and unsafe escape remain absent.
  FFI is excluded.
  Every reference has a checked origin.
- **Non-goal: unique references in unsupported multishot snapshots.**
  G1 rejects them.
  Future support needs copy policy.
  Runtime cannot guess legality.

### Public queries and interfaces

- **`borrow_check_body`.**
  Consume typed Core and PlaceFlow.
  Return loans, regions, and diagnostics.
  Publish validated facts.
- **`region_of_reference`.**
  Return inferred region summary.
  Include origin and required uses.
  Support source inspection.
- **`loans_at`.**
  List active loans at CFG point.
  Distinguish shared and unique.
  Include reborrow ancestry.
- **`outlives_goal`.**
  Solve canonical region relation.
  Integrate higher-ranked universes.
  Return proof or failure.
- **`borrow_state_at`.**
  Map source position to availability.
  Explain blocked moves or writes.
  Preserve recovery status.

### Primary data structures

- **`RegionKey`.**
  Represents canonical or local region.
  Includes universe for placeholders.
  Uses typed identity.
- **`LoanRecord`.**
  Stores borrowed place and mode.
  Stores issuing CFG point.
  Stores parent reborrow link.
- **`RegionConstraint`.**
  Stores subset or liveness relation.
  Carries source cause.
  Uses typed points and regions.
- **`LoanState`.**
  Stores active, ended, or invalid status.
  Integrates place availability.
  Publishes through PlaceFlow.
- **`ReferenceOrigin`.**
  Describes local place or parameter origin.
  Carries projection and lifetime summary.
  Serializes for verifier use when needed.

### Ownership and lifetime model

- **Body session owns inference regions.**
  Local variables and constraints are mutable.
  Solved summaries publish.
  Scratch releases after analysis.
- **PlaceFlow owns canonical loan facts.**
  MIR and optimizer borrow them.
  No second cleanup loan table.
  Validated facts may persist.
- **Reference values carry origin evidence statically.**
  Static details erase when safe.
  Runtime summaries remain where verifier needs them.
  Source origins stay mapped.
- **Higher-ranked placeholders have solver lifetime.**
  They cannot enter published lower-universe values.
  Leak checking occurs before success.
  Tables store canonical summaries.
- **Diagnostics retain compact conflict causes.**
  Full constraint graph may evict.
  Decisive loan and use points persist.
  Presentation reconstructs paths.

### Algorithms and phase order

- **Build move paths and CFG points.**
  PlaceFlow establishes initialization and uses.
  Every borrow operation creates a loan.
  Every reference use creates liveness demand.
- **Generate region constraints.**
  Origins outlive references.
  Reborrows relate child and parent.
  Calls and returns add signature constraints.
- **Propagate region liveness.**
  Use deterministic dataflow.
  Compute minimal required point sets.
  Handle loops by fixed point.
- **Check loan conflicts.**
  Shared and unique modes interact.
  Moves and writes require availability.
  End-borrow transitions restore access.
- **Validate escapes and drops.**
  Return and capture origins are checked.
  Suspension boundaries are checked.
  Cleanup cannot violate active loans.

### Semantic invariants

- **Every reference has a valid origin.**
  Origin place is initialized.
  Projection is legal.
  Region does not exceed owner validity.
- **Unique loans exclude conflicting access.**
  Parent place is unavailable appropriately.
  Nested reborrows preserve exclusivity.
  End-borrow order is valid.
- **Shared loans prohibit mutation and move.**
  Compatible reads remain allowed.
  Custom drop waits for loan end.
  Cleanup honors active references.
- **Placeholder regions do not leak.**
  Universe checks happen on every solution.
  Canonical evidence records scope.
  Cache decoders validate universes.
- **Suspension preserves sound lifetime summaries.**
  Captured references remain valid on resume.
  Cancel cleanup cannot use ended loans.
  Multishot copying follows restrictions.

### Cycles and fixed points

- **CFG region propagation is a fixed point.**
  Point sets grow monotonically.
  Worklists use stable order.
  Budgets bound extreme graphs.
- **Recursive call outlives summaries use SCCs.**
  Parameter and return relations iterate.
  Widening remains conservative.
  Stable summaries publish.
- **Higher-ranked goals use tabled universes.**
  Recursive trait bounds follow solver policy.
  Leak checking closes each answer.
  Cycles remain explicit.
- **Reborrow ancestry is acyclic.**
  Child loans reference earlier parents.
  Decoder validates ordering.
  Cycles indicate corruption.
- **Diagnostic cause graphs collapse repeated constraints.**
  Show shortest stable conflict path.
  Avoid infinite loop explanations.
  Preserve loop point context.

### Incremental dependencies and invalidation

- **Borrow checking depends on typed body and PlaceFlow.**
  Span-only changes may preserve semantic facts.
  New uses or moves invalidate regions.
  Unrelated bodies stay green.
- **Signature lifetime changes affect callers.**
  Interface fingerprints propagate.
  Body implementation changes may preserve summary.
  Equal outlives facts stop fanout.
- **Effect capture changes affect suspension checks.**
  Handler and resumption summaries are dependencies.
  Unused effects remain irrelevant.
  Runtime feature changes affect emission later.
- **Custom drop changes affect loan end legality.**
  Type-fact dependencies capture it.
  Unrelated types remain green.
  Cleanup plans rerun.
- **Source position changes affect tooling maps.**
  Region sets may remain equal.
  `borrow_state_at` locations update.
  MIR bytes may remain stable.

### Caching and persistence

- **Solved borrow facts may persist with PlaceFlow.**
  CFG and type fingerprints key them.
  Local IDs remap canonically.
  Validators recompute consistency checks.
- **Outlives summaries are compact caches.**
  Useful across callers and packages.
  Canonical region binders encode.
  Candidate dependencies are recorded.
- **Inference constraint graphs usually stay memory-local.**
  They are large and diagnostic-oriented.
  Compact conflict summaries may persist.
  Recompute remains possible.
- **Higher-ranked solver answers share trait caches.**
  Universe encoding is canonical.
  Leak-check status validates on load.
  Source causes are excluded.
- **Runtime reference summaries persist in artifacts.**
  Verifier checks them independently.
  They are not source borrow proofs.
  VM consumes frozen forms.

### Diagnostics and explanations

- **Borrow conflicts show both accesses.**
  Loan creation and conflicting use.
  Shared versus unique mode.
  Last relevant use when available.
- **Move-while-borrowed diagnostics show place path.**
  Highlight borrowed projection.
  Show remaining loan region.
  Suggest narrower scope or reborrow.
- **Escape diagnostics show origin chain.**
  Local owner to returned reference.
  Capture or handler boundary.
  Required outlives relation.
- **Suspension diagnostics show perform site.**
  Reference captured across continuation.
  Explain replay or cancel restriction.
  Suggest owned value transfer.
- **Higher-ranked diagnostics show universe leak.**
  Placeholder and escaping variable.
  Bound declaration sites.
  Explain required generality.

### Cancellation, limits, and security

- **CFG point counts are bounded.**
  Every MIR operation charges budget.
  Region bitsets allocate under limits.
  Excess reports body context.
- **Loan and constraint counts are bounded.**
  Reborrow chains cannot amplify unchecked.
  Checked arithmetic prevents overflow.
  Diagnostics name the limit.
- **Fixed-point work is metered.**
  Edge relaxations charge steps.
  Cancellation checks between worklist pops.
  Partial facts never publish.
- **Imported borrow summaries are hostile.**
  Region and place IDs validate.
  Impossible cycles reject.
  Verifier does not trust source claims.
- **No runtime capability bypasses borrow rules.**
  Host imports receive copied or validated values.
  Opaque handles follow type contracts.
  Unsafe FFI remains excluded.

### Determinism and reproducibility

- **Point numbering follows canonical MIR order.**
  Local differences remap before persistence.
  Analysis worklists sort.
  Facts reproduce.
- **Conflict selection uses stable ordering.**
  Report earliest source-relevant pair.
  Ties use place key.
  Diagnostics remain stable.
- **Region set encoding is canonical.**
  Sort ranges or use fixed bitset order.
  Local IDs remap.
  Cache bytes match.
- **SCC summary iteration is stable.**
  Function keys sort.
  Widening rules are fixed.
  Bootstrap stages agree.
- **Pretty lifetime names are presentation-only.**
  Canonical regions use binders.
  Source names aid diagnostics.
  Hashes ignore spelling.

### Testing and observability

- **Borrow tests cover shared and unique modes.**
  Reborrows, moves, and writes.
  NLL shortening.
  Custom drop interactions.
- **Lifetime tests cover returns and captures.**
  Closures, handlers, and resumptions.
  Higher-ranked APIs.
  Accepted and rejected cases.
- **Suspension tests cover reference payloads.**
  One-shot resume.
  Forwarded effects.
  Multishot rejection barriers.
- **Incremental tests add and remove uses.**
  Region facts rerun narrowly.
  Source maps update.
  Clean analysis matches.
- **Inspection prints loans at CFG points.**
  Filter by place or source.
  Show region and ancestry.
  Bound output volume.

### Migration and completion criteria

- **Move borrow facts onto PlaceFlow.**
  Eliminate parallel ownership analyses.
  Export one validated table.
  Compare existing diagnostics.
- **Introduce explicit region constraints.**
  Replace ad hoc lifetime checks.
  Add deterministic solver.
  Add NLL tests.
- **Unify higher-ranked universe machinery.**
  Share trait and lifetime solvers.
  Add leak checking.
  Expand parity ledger.
- **Carry runtime reference summaries explicitly.**
  Extend MIR and bytecode.
  Harden verifier checks.
  Test hostile artifacts.
- **Complete when every reference has one origin story.**
  Source, Core, MIR, and VM agree.
  Suspensions are sound.
  Optimizer erases only proven loans.

## 18. Callables, Captures, Brands, Environments, and Refinements

This section defines the shared callable and nominal-control kernel.
Named functions, closures, handler clauses, and resumptions use common machinery.
Brands provide fresh identities for labels, environments, binders, and continuations.
Refinement and environment transitions remain explicit.

### Purpose and scope

- **Unify callable forms.**
  Named functions and anonymous blocks.
  Closures, handler clauses, resumptions.
  Share invocation and capture rules.
- **Infer capture layouts.**
  Determine moved, copied, shared, and unique captures.
  Preserve use and lifetime obligations.
  Produce deterministic environment records.
- **Represent fresh brands.**
  Labels and execution environments.
  Continuation identities and binder keys.
  Prevent accidental cross-target use.
- **Model environment transitions.**
  Open, sealed, and post-state facts.
  `RunsIn` evidence connects callables.
  Calls can transform refinements.
- **Model `is` refinements.**
  Positive and negative branches.
  Pattern bindings and availability.
  Lower to ordinary core control.

### Goals and non-goals

- **Goal: one call checker.**
  All callable kinds use shared signature logic.
  Receiver modes remain explicit.
  Effect and quantity summaries compose.
- **Goal: one capture engine.**
  Closures and continuations share PlaceFlow facts.
  Handler environments are not special copies.
  Capture layout is queryable.
- **Goal: proof-only brands erase.**
  Runtime realization occurs only when needed.
  Static identities still enforce control.
  Bytecode records finite runtime producers.
- **Non-goal: opaque host-created callables.**
  G1 trusts only artifact-defined producers.
  Host callbacks do not bypass summaries.
  Empty or unknown producer sets fail closed.
- **Non-goal: compiler-known control names.**
  Return and loop helpers remain library callables.
  Brands and labels provide structural power.
  Optimizer recognizes shape, not spelling.

### Public queries and interfaces

- **`callable_interface`.**
  Return parameters, result, effects, and quantity.
  Include receiver mode and generic binders.
  Use stable callable key.
- **`capture_summary`.**
  Return captured places and modes.
  Include lifetimes and obligations.
  Support closure and continuation forms.
- **`brand_record`.**
  Return kind, lifetime, and runtime realization.
  Include owning declaration.
  Preserve generative identity.
- **`environment_summary`.**
  Return access requirements and post-state.
  Include `RunsIn` evidence.
  Support open and sealed phases.
- **`refinement_at`.**
  Report type and availability refinement.
  Include positive or negative path.
  Map to source pattern.

### Primary data structures

- **`CallableKey`.**
  Stable named or anonymous identity.
  Derives from owner and syntax anchor.
  Carries callable kind.
- **`CallableSignature`.**
  Stores typed parameters and result.
  Stores effect row and invocation quantity.
  Stores receiver and environment requirements.
- **`CaptureRecord`.**
  Stores place, mode, and projected path.
  Stores region and use facts.
  Sorts by stable place order.
- **`BrandKey`.**
  Stores fresh nominal identity and kind.
  Carries lifetime and owner.
  May map to runtime identity.
- **`EnvironmentState`.**
  Stores accessible places and refinements.
  Stores open or sealed status.
  Stores post-state transitions.

### Ownership and lifetime model

- **Named callable interfaces have revision lifetime.**
  Packages export public signatures.
  Bodies may change independently.
  Stable keys persist.
- **Anonymous callable syntax has body lifetime.**
  Stable callable key derives from owner.
  Typed signature may persist.
  Parser nodes may drop.
- **Capture inference is body-local.**
  It borrows PlaceFlow and regions.
  Published layout becomes immutable.
  Scratch releases after elaboration.
- **Brands belong to semantic owners.**
  Label brand lives with destination scope.
  Environment brand lives with callable context.
  Stale brands cannot cross revisions.
- **Runtime environments belong to values or frames.**
  Ownership mode follows capture summary.
  VM allocation follows verifier plans.
  Proof-only brands erase.

### Algorithms and phase order

- **Create callable shell.**
  Resolve declared or inferred signature.
  Allocate generative environment brand.
  Seed parameter bindings.
- **Elaborate body under open environment.**
  Record place accesses and effects.
  Infer result and post-state.
  Collect nested callable uses.
- **Infer captures.**
  Compare free place accesses.
  Select move, copy, shared, or unique modes.
  Validate quantity and lifetime constraints.
- **Seal environment and synthesize evidence.**
  Freeze capture layout.
  Compute `Fn` and `RunsIn` facts.
  Publish callable summary.
- **Lower refinements and labels.**
  Convert `is` branches to explicit Core.
  Convert labels to transfer operations.
  Retain source mappings.

### Semantic invariants

- **Every callable has one canonical signature.**
  Parameters and effects are complete.
  Invocation quantity is explicit.
  Anonymous inference must resolve before publication.
- **Every capture has a legal mode.**
  Move consumes source availability.
  Copy requires permission.
  Borrow respects lifetime and suspension.
- **Every brand is generative.**
  Equal spelling does not imply equality.
  Owner and lifetime determine scope.
  Runtime identity cannot be forged.
- **Environment sealing is final.**
  No new access facts appear afterward.
  Post-state is validated.
  Cached summaries are immutable.
- **Refinement facts are path-scoped.**
  Positive bindings do not leak to negative paths.
  Joins remove unavailable facts.
  MIR parameters reflect joined state.

### Cycles and fixed points

- **Recursive callables use interface shells.**
  Signatures exist before bodies.
  Call summaries form SCCs.
  Capture layouts remain finite.
- **Mutually recursive closures require explicit support.**
  Environment cycles are represented deliberately.
  Unsupported self-capture rejects.
  Runtime cycle policy is verified.
- **Environment summaries over recursion use fixed points.**
  Access sets grow monotonically.
  Post-states join conservatively.
  Stable worklists converge.
- **Brand graphs remain acyclic by scope.**
  Brands may reference parent environments.
  Parent cannot depend on child runtime value implicitly.
  Decoder validates ancestry.
- **Refinement joins use CFG fixed points.**
  Loop-carried availability is explicit.
  Removed locals stay unavailable.
  Stable join order is specified.

### Incremental dependencies and invalidation

- **Callable interfaces depend on declarations and inferred body facts.**
  Explicit signatures isolate body edits.
  Inferred signatures rerun callers when changed.
  Equal summaries stop fanout.
- **Capture summaries depend on free-place accesses.**
  Internal expression changes may preserve layout.
  New capture invalidates environment construction.
  Source spans update separately.
- **Brand identities depend on stable owner anchors.**
  Unrelated edits preserve them.
  Moving callable ownership replaces brands.
  Identity diff explains churn.
- **Environment summaries affect callers and optimizer.**
  `RunsIn` evidence changes invalidate call checking.
  Static control fusion may rerun.
  Unrelated callables stay green.
- **Refinement maps depend on pattern and CFG shape.**
  Type-preserving body edits may alter availability.
  MIR lowering reruns as needed.
  Interface consumers remain isolated.

### Caching and persistence

- **Callable interfaces persist with packages.**
  Stable keys and canonical signatures encode.
  Generic binders validate.
  Public and private records follow policy.
- **Capture summaries may persist with Typed Core.**
  Place identities remap.
  Lifetime and use facts validate.
  Recovery summaries stay local.
- **Brand records persist only when semantic identity is stable.**
  Proof-only local brands may remap.
  Runtime producer sets encode canonically.
  Stale generations reject.
- **Environment summaries are high-value query caches.**
  Recursive SCCs may group.
  Callers record dependencies.
  Optimizer consumes same values.
- **Refinement source maps may evict separately.**
  Semantic facts persist.
  Editor positions can rebuild.
  Presentation changes avoid code invalidation.

### Diagnostics and explanations

- **Capture diagnostics show place and mode.**
  Explain why move or copy is required.
  Show conflicting lifetime or quantity.
  Suggest explicit move when appropriate.
- **Callable mismatch diagnostics show full signature.**
  Parameters, result, effects, and quantity.
  Receiver and environment requirements.
  Stable candidate ordering.
- **Brand diagnostics show wrong destination.**
  Label or environment identities.
  Owning scope and lifetime.
  Explain generativity.
- **Environment diagnostics show missing access.**
  Requested place and mode.
  Current open or sealed state.
  Relevant `RunsIn` obligation.
- **Refinement diagnostics show branch facts.**
  Pattern source and tested type.
  Available bindings on each path.
  Join reason for lost fact.

### Cancellation, limits, and security

- **Callable and capture counts are bounded.**
  Nested closures charge body budget.
  Capture arrays enforce size limits.
  Excess reports owner.
- **Environment fixed points are metered.**
  Access-set growth charges steps.
  Cancellation checks between iterations.
  Partial summaries do not publish.
- **Brand creation uses checked identity space.**
  Exhaustion is structured.
  Decoders validate kind and owner.
  Forged runtime producers reject.
- **Opaque host callables are denied.**
  Artifact producer sets are sealed.
  Verifier rejects unknown implementations.
  VM cannot fabricate summaries.
- **Capture contents respect privacy.**
  Diagnostics redact hidden fields.
  Cross-package interfaces expose only legal layout facts.
  Runtime representations remain sealed.

### Determinism and reproducibility

- **Capture order uses stable place keys.**
  Source access discovery order cannot alter layout.
  ABI records reproduce.
  Diagnostics sort by source.
- **Anonymous callable identity uses stable anchors.**
  Insertions minimize churn.
  Collision policy is deterministic.
  Bootstrap stages agree.
- **Environment joins use stable order.**
  Sets and post-states freeze canonically.
  SCC iteration is deterministic.
  Cache bytes match.
- **Runtime producer sets sort by callable key.**
  Empty and noncanonical sets reject.
  Verifier behavior reproduces.
  Artifacts remain stable.
- **Refinement presentation is separate.**
  Canonical facts ignore variable spelling.
  Source names aid diagnostics.
  Semantic fingerprints remain stable.

### Testing and observability

- **Callable tests cover all forms.**
  Named, closure, handler, resumption.
  Generic and effectful signatures.
  Receiver and quantity modes.
- **Capture tests cover every mode.**
  Moves, copies, shared and unique borrows.
  Partial projections.
  Suspension boundaries.
- **Brand tests attempt cross-scope misuse.**
  Labels and environments.
  Nested loops and returns.
  Stable rejection diagnostics.
- **Refinement tests cover joins and loops.**
  Positive and negative `is` paths.
  Unavailability propagation.
  MIR parameter correctness.
- **Inspection emits callable and environment plans.**
  Capture layout and post-state.
  Producer sets and runtime realization.
  Filter by stable key.

### Migration and completion criteria

- **Create one callable record and checker.**
  Route named and anonymous forms.
  Add handler clauses and resumptions.
  Remove parallel code paths.
- **Create one brand substrate.**
  Labels, environments, continuations, binders.
  Add kind and lifetime checks.
  Preserve behavior.
- **Move capture inference onto PlaceFlow.**
  Share move and loan facts.
  Publish canonical layout.
  Expand tests.
- **Seal environment summaries explicitly.**
  Add open and sealed states.
  Synthesize shared evidence.
  Expose inspection.
- **Complete when library control uses ordinary callables.**
  Optimizer relies on summaries, not names.
  Runtime producer sets are sealed.
  All callable forms share invariants.

## 19. Typed Core

This section defines the smallest trusted semantic calculus.
Typed Core contains only structural language mechanisms.
Source-library control names never become privileged nodes.
Core is body-local, typed, evidence-aware, and immediately lowerable.

### Purpose and scope

- **Represent accepted expression meaning.**
  Calls, construction, projection, and borrowing.
  Labels, effects, handlers, and resumptions.
  Destruction and finite machine primitives.
- **Carry static evidence during checking.**
  Types, effects, quantities, and environments.
  Trait and callable evidence.
  Erase proof-only facts before artifact emission.
- **Provide a compact lowering source.**
  Core maps cleanly to ownership MIR.
  Evaluation order is explicit.
  Source spans remain mapped.
- **Exclude source-level control names.**
  No compiler node named `if`.
  No compiler node named `loop`.
  Libraries express them structurally.
- **Support one-body-at-a-time compilation.**
  Core builder owns transient body values.
  Lower immediately to MIR.
  Release scratch afterward.

### Goals and non-goals

- **Goal: small trusted semantics.**
  Few orthogonal forms.
  Shared callable and effect kernels.
  No duplicated source sugar.
- **Goal: fully typed nodes.**
  Every value and computation has a type.
  Effects and ownership facts are attached.
  Invalid Core cannot publish.
- **Goal: explicit sequencing.**
  ANF-like binding exposes order.
  Calls and effects are computations.
  Operands are stable values.
- **Non-goal: optimizer convenience IR.**
  MIR owns CFG transformations.
  Core remains semantic.
  No extra persistent Stage program.
- **Non-goal: whole-program Core retention.**
  Only generic needs justify persistence.
  Body products may cache compactly.
  Mutable builders remain transient.

### Public queries and interfaces

- **`typed_core_body`.**
  Elaborate one resolved body.
  Return validated Core and evidence.
  Attach source map.
- **`core_interface_body`.**
  Return compact generic Core when needed.
  Erase private body facts appropriately.
  Support downstream specialization.
- **`core_value_at`.**
  Map source expression to Core value.
  Return type and effect metadata.
  Support inspection.
- **`core_validate`.**
  Check node typing and ownership prerequisites.
  Verify ranges and binders.
  Run before publication.
- **`emit_core`.**
  Serialize canonical inspection form.
  Remap local IDs.
  Exclude transient inference state.

### Primary data structures

- **`CoreBody`.**
  Owns value and computation arenas.
  Stores entry computation.
  Stores callable and source mappings.
- **`CoreValueKind`.**
  Represents constants, locals, aggregates, projections.
  Represents closures and handlers.
  Is pure according to Core rules.
- **`CoreComputationKind`.**
  Represents calls, effects, labels, destruction.
  Represents resume, cancel, and host import.
  Carries explicit continuations or blocks.
- **`CoreBuilder`.**
  Allocates typed nodes.
  Provides `bind` and `finish` operations.
  Owns let-prefix construction.
- **`CoreEvidenceTable`.**
  Stores proof references and summaries.
  Supports erasure decisions.
  Uses typed side-table identities.

### Ownership and lifetime model

- **Body session owns the builder.**
  Mutable node arenas are local.
  Validation freezes the result.
  Lowering borrows immutable Core.
- **Published Core has body-product lifetime.**
  It may memoize or persist.
  Source syntax can drop.
  Local IDs remain owner-bound.
- **Generic Core may cross package boundaries selectively.**
  Canonical encoding removes source-private facts.
  Stable dependencies are included.
  Downstream compilers validate it.
- **Evidence tables may partially erase.**
  Static-only evidence dies before MIR.
  Runtime-relevant summaries lower explicitly.
  Diagnostics retain compact proofs.
- **Source maps may evict separately.**
  Semantic Core can stay cached.
  Tooling locations reconstruct from anchors.
  Code generation ignores presentation.

### Algorithms and phase order

- **Create Core builder from typed environment.**
  Seed parameters and result expectation.
  Allocate local identities.
  Attach body-level effects.
- **Elaborate syntax recursively or iteratively.**
  Convert forms into values and computations.
  Use `bind` for sequencing.
  Preserve left-to-right evaluation.
- **Insert structural evidence.**
  Calls carry selected callable facts.
  Effects carry operation identity.
  Moves and borrows reference places.
- **Lower source abstractions structurally.**
  `is` becomes decision control.
  Library control remains ordinary calls.
  Labels become transfers.
- **Validate and publish.**
  Check types, binders, and ranges.
  Check effect and quantity summaries.
  Freeze source mappings.

### Semantic invariants

- **Every Core node is well typed.**
  Child result types match parents.
  Calls satisfy selected signatures.
  Effect operations match declarations.
- **Evaluation order is explicit.**
  Operand materialization uses bindings.
  Construction fields remain left to right.
  Optimizer cannot reinterpret source order.
- **No source-control magic exists.**
  Standard-library names remain definitions.
  Core forms are structural only.
  Primitive authority uses manifest identities.
- **Proof-only evidence is erasable safely.**
  Erasure cannot remove runtime behavior.
  Runtime identities lower explicitly.
  Validators check the distinction.
- **Core contains no unresolved inference.**
  Types and rows are canonical.
  Recovery Core remains marked and nonrelease.
  Published release Core is complete.

### Cycles and fixed points

- **Recursive callables reference stable keys.**
  Core bodies do not inline recursively by default.
  Instance discovery handles recursion later.
  Call graphs form SCCs.
- **Core arenas remain acyclic where structural.**
  Values may reference earlier or stable nodes by policy.
  Decoder validates allowed graph shape.
  Cycles indicate corruption unless explicit.
- **Generic recursive Core persists compactly.**
  Stable callable references break infinite expansion.
  Specialization uses instance SCCs.
  Cache keys remain finite.
- **Handler and continuation control cycles lower to MIR.**
  Core records structured operations.
  Runtime loops are not recursive Core graphs.
  Lowering creates explicit edges.
- **Evidence cycles remain solver-owned.**
  Core stores canonical proof references.
  It does not rerun fixed points.
  Dependencies link to solver queries.

### Incremental dependencies and invalidation

- **Core depends on resolved syntax and semantic selections.**
  Token span changes may preserve semantic Core.
  Type or impl changes invalidate affected nodes.
  Unused declarations create no edge.
- **Callable and effect summaries are explicit dependencies.**
  Equal summaries preserve Core.
  Body implementation changes may stay local.
  Generic interface changes propagate.
- **Source maps depend on syntax locations.**
  Core fingerprint may exclude spans.
  Tooling map reruns separately.
  MIR code may remain green.
- **Primitive manifest changes affect trusted leaves.**
  Ordinary calls remain unchanged.
  Core primitive nodes rerun.
  Build identity records generation.
- **Recovery status blocks cross-revision reuse into release roots.**
  Complete later revisions replace recovered Core.
  IDE consumers remain explicit.
  Persistent release cache excludes incomplete values.

### Caching and persistence

- **Complete Core bodies are cacheable.**
  Key includes typed body dependencies.
  Canonical codec remaps local IDs.
  Validator checks node typing.
- **Generic Core interfaces persist selectively.**
  Only downstream-needed bodies cross packages.
  Private identities are sealed.
  Schema is versioned.
- **Core evidence may use compact references.**
  Selected impl and callable keys encode.
  Full solver tables remain separate.
  Decoder verifies referents.
- **Source maps persist as optional companion records.**
  Semantic body can load without them.
  Tooling requests may reload or rebuild.
  Artifact debug data uses canonical mapping.
- **Builder scratch never persists.**
  Let wrappers and temporary queues are mutable.
  Only finished nodes encode.
  Failed builds leave no record.

### Diagnostics and explanations

- **Core validation diagnostics are internal.**
  Name node and expected invariant.
  Map back to source when available.
  Stop compilation safely.
- **Elaboration diagnostics remain source-facing.**
  Type, effect, quantity, and privacy causes.
  Core construction does not duplicate messages.
  Stable codes belong to semantic phases.
- **Inspection prints typed structural forms.**
  Show stable callable and effect identities.
  Show proof summaries optionally.
  Avoid raw arena addresses.
- **Erasure explanations show removed evidence.**
  Distinguish proof-only and runtime facts.
  Support compiler audits.
  Bound output size.
- **Source-to-Core mapping supports tooling.**
  Show node range for expression.
  Explain one-to-many lowering.
  Preserve deterministic ordering.

### Cancellation, limits, and security

- **Core node counts are bounded.**
  Every builder allocation charges budget.
  Generic expansion is not hidden here.
  Excess reports body owner.
- **Builder recursion is bounded.**
  Deep syntax uses explicit stacks where needed.
  Cancellation checks between expressions.
  Rollback releases temporary nodes.
- **Imported Core is hostile.**
  Node kinds, types, and child ranges validate.
  Stable references must exist.
  Impossible proof claims reject.
- **Primitive nodes require manifest authority.**
  Name matching is insufficient.
  Decoder validates trusted declaration identity.
  Cache records cannot forge it.
- **Source inspection redacts private data by policy.**
  Semantic compiler retains exact Core.
  External clients receive authorized views.
  Raw package internals stay protected.

### Determinism and reproducibility

- **Builder processes syntax in stable order.**
  Local IDs may remain deterministic.
  Persistence still remaps.
  Core fingerprint ignores incidental allocation.
- **Call candidate selection is already canonical.**
  Core stores selected stable key.
  Ambiguity never depends on order.
  Rebuilds match.
- **Evidence table ordering is frozen.**
  Sort by stable key and node use.
  Deduplicate canonically.
  Cache bytes reproduce.
- **Inspection format is canonical.**
  Node printing uses stable traversal.
  Optional source spans sort.
  Stage comparisons are meaningful.
- **Core-to-MIR lowering receives the same semantics.**
  Cache warmth cannot alter Core.
  Stage compilers compare fingerprints.
  Bootstrap differences localize.

### Testing and observability

- **Core conformance tests cover every form.**
  Values, calls, effects, labels, and destruction.
  Closures, handlers, resume, and cancel.
  Host imports and primitives.
- **Validation tests mutate Core records.**
  Wrong types and child ranges.
  Missing evidence.
  Unsupported node kinds.
- **Evaluation-order tests compare runtime traces.**
  Calls and construction fields.
  Effects and cleanup.
  O0 through O3.
- **No-magic tests rename library control.**
  Structural behavior remains.
  Optimizer still recognizes shape.
  Compiler does not special-case names.
- **Inspection tests snapshot canonical Core.**
  Rust and self-host products compare.
  Incremental and clean products match.
  Source maps remain exact.

### Migration and completion criteria

- **Introduce one Core builder.**
  Replace manual embedded computations.
  Centralize `bind` sequencing.
  Preserve evaluation order.
- **Unify Core node representations.**
  Remove numeric tag mirrors.
  Expose exhaustive typed views.
  Add validators.
- **Move source control lowering out of special nodes.**
  Keep structural calls and labels.
  Add no-magic regressions.
  Expose control plans later.
- **Lower each body immediately to MIR.**
  Release syntax and builder scratch.
  Measure memory.
  Persist only finished products.
- **Complete when Core is small and authoritative.**
  All accepted source lowers through it.
  No parallel HIR exists.
  Stage parity compares canonical Core.

## 20. PlaceFlow

This section defines the single sparse graph of place facts.
Initialization, moves, loans, captures, continuation state, cleanup, and final use share it.
PlaceFlow replaces syntax-specific ownership analyses.
MIR and verifier summaries consume validated facts.

### Purpose and scope

- **Represent places and projections.**
  Locals, fields, variants, and dereferences.
  Move paths form a typed hierarchy.
  Source origins remain mapped.
- **Track initialization and availability.**
  Every CFG point has relevant facts.
  Moves and assignments update states.
  Joins preserve unavailability correctly.
- **Track loans and references.**
  Shared and unique loans attach to places.
  End-borrow transitions are explicit.
  Region analysis shares points.
- **Track captures and continuations.**
  Closure and handler environments use place facts.
  Resume and cancel states are explicit.
  Quantities attach to captured owners.
- **Track cleanup and final use.**
  Active subtrees determine destruction plans.
  Final transfers are selected from use facts.
  Must-move obligations block abandonment.

### Goals and non-goals

- **Goal: one ownership source.**
  No closure-specific move checker.
  No cleanup-specific availability model.
  No verifier-only source duplicate.
- **Goal: sparse body-local analysis.**
  Store relevant facts only.
  Use typed IDs and compact ranges.
  Scale to compiler bodies.
- **Goal: validated import into backend.**
  Lowering exports facts.
  Backend checks them against MIR.
  Optimizers preserve or recompute selectively.
- **Non-goal: retain source AST semantics.**
  PlaceFlow follows typed operational structure.
  Source sugar is already lowered.
  Facts map back through spans only.
- **Non-goal: runtime dynamic ownership checker.**
  Verifier checks encoded invariants.
  VM executes fixed plans.
  Source proof remains compile-time.

### Public queries and interfaces

- **`place_flow`.**
  Build complete place graph for body.
  Return validated facts and summaries.
  Attach source mappings.
- **`place_state_at`.**
  Return initialization, obligation, and loan state.
  Accept MIR or source point.
  Support diagnostics and inspection.
- **`move_path_of`.**
  Resolve place projection hierarchy.
  Return parent and descendants.
  Explain partial moves.
- **`cleanup_state`.**
  Return active destructible subtrees.
  Identify zero-use barriers.
  Feed cleanup planning.
- **`validate_place_flow`.**
  Cross-check facts against MIR operations.
  Run deterministic ownership fixed point.
  Reject inconsistent imports.

### Primary data structures

- **`Place`.**
  Stores local root and projections.
  Uses canonical projection kinds.
  Has body-local typed ID.
- **`MovePath`.**
  Stores parent and child ranges.
  Represents ownership subtrees.
  Carries type and use facts.
- **`PlaceFact`.**
  Stores point, place, and fact kind.
  Includes init, move, loan, capture.
  Uses sparse sorted storage.
- **`ControlPoint`.**
  Identifies before and after operation positions.
  Maps to MIR block and index.
  Maps optionally to source.
- **`PlaceFlowSummary`.**
  Stores entry and exit states.
  Stores capture and cleanup plans.
  Stores validated fingerprint.

### Ownership and lifetime model

- **Body analysis owns mutable fact builders.**
  Worklists and sparse maps are temporary.
  Published graph becomes immutable.
  Scratch releases after validation.
- **MIR body and PlaceFlow have coordinated lifetime.**
  Place IDs refer to the body owner.
  Cached records load together or remap.
  Optimizer sees a consistent pair.
- **Source mappings may be companion data.**
  Semantic facts can persist alone.
  Tooling maps may evict.
  Diagnostics retain decisive anchors.
- **Capture and cleanup summaries borrow place identities.**
  They belong to the same product.
  Separate copies are forbidden.
  Emission remaps canonically.
- **Verifier receives encoded summaries only.**
  It does not own source PlaceFlow.
  Compiler facts are cross-validated during emission.
  Runtime uses frozen plans.

### Algorithms and phase order

- **Enumerate locals and projections.**
  Build move paths from types and operations.
  Create roots for parameters and temporaries.
  Bound aggregate expansion.
- **Emit local transfer facts from lowering.**
  Assignments initialize.
  Moves empty paths.
  Borrows create loans.
- **Propagate states across CFG.**
  Use deterministic worklist.
  Join initialization and availability.
  Preserve path-specific obligation facts.
- **Derive captures and cleanup.**
  Identify live places at closure and suspension.
  Compute active subtrees at exits.
  Check quantity and borrow barriers.
- **Validate against MIR.**
  Re-run deterministic ownership checks.
  Confirm every operation's preconditions.
  Publish paired product.

### Semantic invariants

- **Every place has one type.**
  Projections are legal for that type.
  Parent-child paths are consistent.
  Decoders validate all relationships.
- **Initialization state is conservative and precise enough.**
  A maybe-uninitialized place cannot be read.
  Joins never invent availability.
  Writes reinitialize legal paths.
- **Moves empty exactly one ownership subtree.**
  Parents and descendants update coherently.
  Partial moves retain active siblings.
  Custom drop restrictions are honored.
- **Loans and moves share availability.**
  Conflicting operations cannot both succeed.
  End-borrow restores only proven access.
  Suspension facts preserve origins.
- **Cleanup includes only legal active subtrees.**
  Reverse destruction order is specified.
  Positive-use obligations block destruction.
  Custom drop hooks run exactly once.

### Cycles and fixed points

- **CFG state propagation is a fixed point.**
  Facts move monotonically in analysis lattice.
  Stable worklists converge.
  Budgets bound irreducible graphs.
- **Loop-carried initialization uses join parameters.**
  Unavailable locals remain unavailable.
  Refinement join bugs are prevented.
  MIR block parameters reflect state.
- **Recursive call effects use summaries.**
  PlaceFlow remains intraprocedural primarily.
  Call summaries form SCCs separately.
  Unknown effects stay conservative.
- **Move-path hierarchy is acyclic.**
  Projections form a tree or DAG by policy.
  Decoder rejects parent cycles.
  Shared structural types do not share owner paths.
- **Diagnostic derivations collapse loop repetition.**
  Show representative iteration.
  Report entry and back-edge facts.
  Avoid infinite traces.

### Incremental dependencies and invalidation

- **PlaceFlow depends on typed body and MIR skeleton.**
  Type or control changes rerun.
  Span-only changes may preserve facts.
  Source maps update separately.
- **Type facts affect move paths.**
  Aggregate fields and custom drop.
  `Use` and copyability facts.
  Equal type summaries stop fanout.
- **Call summaries affect state transfer.**
  Callee moves, borrows, and effects.
  Unchanged summaries preserve callers.
  Body-internal callee edits may stay local.
- **Capture changes affect environment plans.**
  Closure and continuation construction rerun.
  Unrelated places remain green.
  Optimizer plans update.
- **Optimizer transformations invalidate selected facts.**
  Checked editor declares masks.
  Some local rewrites preserve PlaceFlow.
  Others trigger recomputation or validation.

### Caching and persistence

- **Validated PlaceFlow may persist with MIR.**
  Pair fingerprints are linked.
  Local IDs remap canonically.
  Decoder revalidates structure.
- **Sparse facts encode by stable point order.**
  Sort place facts.
  Compress repeated states safely.
  Canonical bytes reproduce.
- **Capture and cleanup summaries are cached companions.**
  Avoid recomputing from scratch.
  Validators cross-check detailed facts.
  Emission consumes summaries.
- **Source mappings may remain separate records.**
  Semantic reuse across location changes.
  Tooling can reload maps.
  Artifact debug data keys appropriately.
- **Failed or recovered analyses do not persist for release.**
  IDE may retain memory-local partial state.
  Status remains explicit.
  Clean recomputation is authoritative.

### Diagnostics and explanations

- **Use-after-move diagnostics show move path.**
  Original move and later use.
  Parent or field relationship.
  Possible reinitialization site.
- **Partial-move diagnostics show active siblings.**
  Aggregate shell state.
  Custom drop barrier.
  Legal consuming alternatives.
- **Loan diagnostics use shared PlaceFlow points.**
  Borrow creation and conflict.
  End point and source mapping.
  No separate narrative reconstruction.
- **Cleanup diagnostics show planned destruction tree.**
  Active fields and order.
  Blocking must-move obligation.
  Nonlocal exit destination.
- **Inspection can print state deltas.**
  Filter by block or place.
  Show only changed facts.
  Support optimizer debugging.

### Cancellation, limits, and security

- **Place and move-path counts are bounded.**
  Aggregate expansion checks limits.
  Checked IDs prevent overflow.
  Diagnostics name the owning type.
- **Fact edge counts are bounded.**
  Sparse storage charges budget.
  Duplicate facts deduplicate.
  Malicious CFGs terminate.
- **Fixed-point iterations are metered.**
  Worklist pops charge steps.
  Cancellation checks periodically.
  Partial facts never publish.
- **Imported PlaceFlow is hostile.**
  Every point and place validates.
  Inconsistent state transitions reject.
  Backend never trusts cache bytes blindly.
- **Runtime plans are independently verified.**
  Encoded cleanup and capture maps cross-check.
  VM cannot invent ownership facts.
  Unsafe bypasses remain absent.

### Determinism and reproducibility

- **Place enumeration follows stable local order.**
  Roots use declaration order.
  Projections use type field order.
  Persistence remaps anyway.
- **Worklists sort control points.**
  Join processing is deterministic.
  Diagnostics select stable conflicts.
  Facts reproduce.
- **Sparse fact serialization is canonical.**
  Sort by point, place, and kind.
  Normalize booleans and ranges.
  Re-encoding matches.
- **Cleanup ordering follows language rules.**
  Reverse declaration order where specified.
  Shared blocks use stable keys.
  Artifacts remain equal.
- **Validation has stable first failure.**
  Process blocks and operations canonically.
  Report deterministic context.
  Bootstrap comparisons localize.

### Testing and observability

- **Initialization tests cover joins and loops.**
  Maybe-uninitialized and reinitialized places.
  Refinement availability.
  Irreducible CFG cases.
- **Move-path tests cover nested aggregates.**
  Partial moves and reconstruction.
  Enums and patterns.
  Custom drop barriers.
- **Loan and capture tests share scenarios.**
  Closures and handlers.
  Suspensions and cancellations.
  Unique and shared references.
- **Optimizer differential tests validate facts.**
  Before and after each pass.
  Recompute sampled bodies.
  Compare runtime traces.
- **Inspection tests snapshot state deltas.**
  Raw MIR and pre-emission MIR.
  Cleanup and capture plans.
  Canonical formatting.

### Migration and completion criteria

- **Define typed place and move-path graph.**
  Unify existing ownership records.
  Add canonical projections.
  Port tests.
- **Emit facts during Core-to-MIR lowering.**
  Replace syntax-specific final-use scans.
  Connect quantities and loans.
  Validate immediately.
- **Build deterministic import validator.**
  Cross-check facts against MIR.
  Add hostile mutation tests.
  Use in backend and caches.
- **Route cleanup and captures through summaries.**
  Remove parallel recomputation.
  Extend bytecode maps.
  Harden verifier.
- **Complete when every ownership feature extends one graph.**
  Closures, handlers, and cleanup agree.
  Optimizer invalidation is explicit.
  Self-host memory remains bounded.

---

# Volume VI — MIR and Optimization

## 21. Ownership-and-Control MIR, Lowering, Cleanup, and Validation

This section defines the single operational IR.
MIR is a typed CFG with explicit ownership and nonlocal control.
Cleanup, cancellation, handler, resumption, and label edges are first-class.
Every transformation passes checked validation.

### Purpose and scope

- **Represent executable control flow.**
  Blocks, parameters, statements, and terminators.
  Calls, switches, returns, and aborts.
  Stable source mappings.
- **Represent ownership operations explicitly.**
  Moves, copies, borrows, and destruction.
  Storage liveness and place assignments.
  PlaceFlow facts align exactly.
- **Represent nonlocal control explicitly.**
  Labels and `leave`.
  Perform, resume, and cancel.
  Cleanup and handler edges.
- **Lower Typed Core deterministically.**
  Preserve evaluation order.
  Materialize operands and temporaries.
  Produce validated CFG.
- **Provide optimizer-ready structure.**
  Checked editors mutate safely.
  Analyses key by typed IDs.
  Artifact emission consumes MIR directly.

### Goals and non-goals

- **Goal: one operational representation.**
  No parallel Stage program.
  Encoder scratch is not semantic IR.
  Every feature extends MIR directly.
- **Goal: explicit cleanup semantics.**
  Every abandoning edge has a plan.
  Must-move barriers are enforced.
  Custom drop is represented.
- **Goal: typed checked editing.**
  Block and place IDs are distinct.
  Mutations invalidate declared analyses.
  Invalid MIR cannot publish.
- **Non-goal: preserve source syntax shape.**
  MIR reflects operational meaning.
  Source maps provide traceability.
  Optimizer may restructure CFG.
- **Non-goal: verifier duplication of source semantics.**
  MIR validation remains compiler-owned.
  Artifact verifier checks lower invariants.
  Trait proofs stay erased.

### Public queries and interfaces

- **`mir_body`.**
  Lower one complete Core body.
  Return MIR and PlaceFlow pair.
  Attach source and control mappings.
- **`validate_mir`.**
  Check structure, types, and ownership.
  Check cleanup and control identities.
  Return stable diagnostics.
- **`mir_at`.**
  Map source expression to operations.
  Return containing block and points.
  Support inspection.
- **`cleanup_plan`.**
  Return exact plan for an edge.
  Include reverse destruction order.
  Identify blockers.
- **`checked_edit`.**
  Apply typed mutation transaction.
  Validate affected region.
  Return invalidation mask.

### Primary data structures

- **`MirBody`.**
  Owns typed arenas for locals and blocks.
  Stores entry block and signature.
  Stores scopes and control sites.
- **`MirStatement`.**
  Represents assignment, storage, borrow end, destruction.
  Uses typed operands and places.
  Carries source identity.
- **`MirTerminator`.**
  Represents jump, switch, call, and return.
  Represents leave, perform, resume, cancel.
  Stores explicit successor transfers.
- **`CleanupPlan`.**
  Stores ordered actions and target.
  References move paths and drop hooks.
  Is validated against PlaceFlow.
- **`AnalysisInvalidationMask`.**
  Names affected analysis bundles.
  Is returned by checked edits.
  Prevents stale optimizer facts.

### Ownership and lifetime model

- **Lowering context owns mutable MIR builder.**
  Core is borrowed immutably.
  PlaceFlow builder is coordinated.
  Failure drops both.
- **Published MIR body owns all local IDs.**
  Blocks and locals cannot escape alone.
  Companion maps reference same owner.
  Caches load the product coherently.
- **Cleanup plans belong to MIR edges.**
  Shared plan bodies may intern locally.
  References remain body-local.
  Emission remaps canonically.
- **Optimizer owns transactional editors.**
  Edits borrow one mutable body.
  Analysis caches are invalidated.
  Failed edits roll back.
- **Emission borrows validated optimized MIR.**
  It cannot mutate semantic facts.
  Selection scratch is separate.
  MIR may evict after fragment publication.

### Algorithms and phase order

- **Create MIR locals and scopes.**
  Map parameters and Core temporaries.
  Allocate place roots.
  Seed entry availability.
- **Lower Core computations.**
  Emit statements in evaluation order.
  Split blocks for control.
  Build typed successor transfers.
- **Insert nonlocal control edges.**
  Labels resolve to branded destinations.
  Effects route through handler sites.
  Resume and cancel use continuation identities.
- **Elaborate cleanup plans.**
  Query PlaceFlow active subtrees.
  Add custom drop hooks.
  Share identical legal plans.
- **Validate complete MIR.**
  Structural and type checks.
  Ownership fixed point and cleanup checks.
  Publish paired products.

### Semantic invariants

- **Every block has one typed parameter list.**
  Predecessor transfers match exactly.
  Entry signature matches callable interface.
  Unreachable blocks still validate structurally.
- **Every local has one exact type.**
  Assignments and operands match.
  Representation compatibility is not assumed.
  Type facts come from canonical keys.
- **Every ownership transition is explicit.**
  Move empties source.
  Copy requires permission.
  Destroy follows legal cleanup.
- **Every nonlocal edge identifies its control site.**
  Label, handler, and continuation brands match.
  Runtime producer set is finite.
  Unknown targets reject.
- **Every abandoning edge carries complete cleanup.**
  Active zero-use subtrees are handled.
  Positive obligations block exit.
  Result protection is explicit.

### Cycles and fixed points

- **CFG analyses use deterministic fixed points.**
  Reachability, liveness, and ownership.
  Loops and irreducible SCCs are supported.
  Budgets bound iteration.
- **Recursive functions remain call-graph cycles.**
  MIR bodies reference callable keys.
  Instance summaries handle SCCs.
  Bodies stay finite.
- **Handler and resumption loops are explicit CFG cycles.**
  Verifier summaries track identities.
  No hidden host recursion is required.
  Optimizer preserves deep semantics.
- **Cleanup sharing graph is acyclic toward destinations.**
  Cleanup blocks may branch to final target.
  Cyclic cleanup requires explicit loop semantics.
  Validators reject accidental cycles.
- **Checked editor transactions avoid mutation cycles.**
  Each edit has one owner.
  Rollback restores prior graph.
  Analysis invalidation occurs after commit.

### Incremental dependencies and invalidation

- **MIR depends on Typed Core and type facts.**
  Source span changes may preserve semantic MIR.
  Core control changes rerun lowering.
  Call summary dependencies are explicit.
- **Cleanup depends on PlaceFlow and custom drop facts.**
  Quantity or loan changes rerun plans.
  Unrelated type changes stay green.
  Source mapping updates separately.
- **Optimizer edits declare invalidation masks.**
  CFG edits invalidate reachability.
  Operand edits may preserve dominators.
  Ownership changes always revalidate.
- **Target-neutral MIR may reuse across targets.**
  Layout-specific lowering remains later.
  Host import legality may be semantic input.
  Native backend future policy is explicit.
- **Call interface changes invalidate callers.**
  Body implementation changes may preserve signature.
  Interprocedural summaries decide optimization fanout.
  Equal MIR fingerprints stop emission changes.

### Caching and persistence

- **Validated raw MIR is cacheable.**
  Core and type fingerprints key it.
  Local IDs remap canonically.
  Decoder reruns structural validation.
- **PlaceFlow persists as linked companion.**
  Pair checksum prevents mismatch.
  Cleanup summaries cross-check.
  Hostile records reject.
- **Optimized MIR caches by level and policy.**
  Pass generation enters key.
  Analysis cache itself stays process-local.
  Final body validates before storage.
- **Source maps may persist separately.**
  Semantic MIR reuses across span-only changes.
  Debug and inspection requests load maps.
  Artifact mapping keys appropriately.
- **Edit transactions never persist.**
  Only committed validated bodies encode.
  Failed speculative rewrites disappear.
  Pass traces are optional side records.

### Diagnostics and explanations

- **Lowering diagnostics identify Core source.**
  Invalid impossible states are invariants.
  Resource failures name body and count.
  Source mappings aid debugging.
- **MIR validation diagnostics name block and operation.**
  Show expected and found type or state.
  Include predecessor context.
  Use stable local display numbering.
- **Cleanup diagnostics print action sequence.**
  Show protected results.
  Show blocking ownership obligation.
  Link to source exit.
- **Control diagnostics show brand mismatch.**
  Label or continuation identity.
  Producer and destination sites.
  Runtime realization status.
- **Inspection emits raw and optimized MIR.**
  Stable textual format.
  Optional state deltas.
  Source-to-MIR mappings.

### Cancellation, limits, and security

- **Block, local, and operation counts are bounded.**
  Builder checks before allocation.
  Typed ID exhaustion is structured.
  Diagnostics name category.
- **Cleanup action counts are bounded.**
  Aggregate destruction cannot amplify unchecked.
  Shared plans reduce duplication.
  Verifier enforces artifact limits.
- **Validation work is metered.**
  CFG edges and dataflow steps charge budgets.
  Cancellation checks in worklists.
  Partial validation does not publish.
- **Imported MIR is hostile.**
  Every local, block, and edge validates.
  Types and control identities cross-check.
  Cache producer grants no trust.
- **Host imports remain manifest-bound.**
  MIR cannot name arbitrary host operations.
  Emitter and verifier check exact imports.
  VM grants remain separate.

### Determinism and reproducibility

- **Lowering follows stable Core order.**
  Block creation uses deterministic traversal.
  Local IDs remain reproducible when possible.
  Persistence remaps regardless.
- **Cleanup plan sharing uses canonical keys.**
  Equal action sequences share deterministically.
  Hash order cannot choose representatives.
  Artifacts match.
- **Validation scans blocks canonically.**
  First failure is stable.
  Worklists use typed order.
  Reports reproduce.
- **Optimized MIR textual form is canonical.**
  Blocks use RPO or stable layout.
  Local names derive from typed IDs.
  Phase comparisons are useful.
- **MIR fingerprints exclude source presentation.**
  Optional source map digest is separate.
  Clean and incremental lowering match.
  Bootstrap stages compare semantic bodies.

### Testing and observability

- **Lowering tests cover every Core form.**
  Calls, effects, labels, and cleanup.
  Resumption and cancellation.
  Custom drop and partial moves.
- **MIR validator tests mutate every invariant.**
  Wrong types and transfers.
  Invalid ownership states.
  Mismatched control identities.
- **Cleanup tests cover all exit classes.**
  Return, leave, effect, cancel, failure.
  Protected results and partial initialization.
  Reverse order.
- **Differential tests execute O0 MIR artifacts.**
  Compare source oracle where valid.
  Compare optimized runtime traces.
  Preserve failing artifacts.
- **Inspection supports filtered tracing.**
  Function, block, and operation filters.
  State delta views.
  Pre-edge and raw MIR captures.

### Migration and completion criteria

- **Evolve existing MIR directly.**
  Add missing ownership and control forms.
  Do not introduce parallel Stage IR.
  Port validators continuously.
- **Create checked MIR editor.**
  Route mutations through transactions.
  Return invalidation masks.
  Add rollback tests.
- **Attach exact cleanup plans.**
  Consume PlaceFlow summaries.
  Remove duplicate backend inference.
  Cross-check bytecode maps.
- **Canonicalize MIR persistence and inspection.**
  Add stable codec.
  Add phase fingerprints.
  Compare self-host products.
- **Complete when emission needs no semantic reconstruction.**
  MIR and facts are sufficient.
  Every edge is explicit.
  All optimizer outputs revalidate.

## 22. Generic Instances, Monomorphization, and Interprocedural Summaries

This section defines demand-driven specialization and cross-body facts.
Instances are keyed by canonical substitutions.
Reachability and recursive call groups are explicit.
Interprocedural summaries avoid retaining every body simultaneously.

### Purpose and scope

- **Discover demanded generic instances.**
  Start from build roots.
  Follow direct and selected indirect calls.
  Canonicalize substitutions.
- **Specialize bodies when required.**
  Substitute types, consts, effects, and quantities.
  Reuse generic Core or MIR templates.
  Validate specialized ownership.
- **Handle recursive instance graphs.**
  Create stable instance shells.
  Form SCCs.
  Avoid infinite specialization.
- **Compute interprocedural summaries.**
  Effects, captures, use, cleanup, and costs.
  Calls depend on summaries rather than full bodies.
  Optimizer uses the same facts.
- **Bound instance growth.**
  Detect polymorphic recursion and explosion.
  Apply explicit G1 policies.
  Produce actionable diagnostics.

### Goals and non-goals

- **Goal: demand-first compilation.**
  Unreachable bodies need not lower.
  Package interfaces remain cheap.
  Self-host memory stays bounded.
- **Goal: canonical instance identity.**
  Equivalent substitutions share work.
  Local inference variables are absent.
  Target dependence is explicit.
- **Goal: compact summaries.**
  Callers avoid loading callee MIR.
  Recursive groups converge.
  Changes invalidate narrowly.
- **Non-goal: unlimited code cloning.**
  Budgets cap instances.
  Generalization may be required.
  Unsupported recursion rejects.
- **Non-goal: whole-program mandatory inlining.**
  Instance discovery is separate.
  Optimizer chooses inlining under budgets.
  Interfaces remain modular.

### Public queries and interfaces

- **`instance_key`.**
  Canonicalize callable and substitutions.
  Include specialization policy.
  Return stable key.
- **`reachable_instances`.**
  Traverse from package roots.
  Return canonical ordered set.
  Include producer reasons.
- **`specialized_mir`.**
  Instantiate and validate one body.
  Reuse generic products.
  Return complete MIR.
- **`call_summary`.**
  Return effects, ownership, and control facts.
  Use SCC fixed points.
  Support callers and optimizer.
- **`instance_explain`.**
  Show why an instance exists.
  Trace root and call chain.
  Show key substitutions.

### Primary data structures

- **`InstanceKey`.**
  Stores callable stable key.
  Stores canonical substitution tuple.
  Stores target policy when needed.
- **`InstanceState`.**
  Tracks discovered, lowering, or complete.
  Stores recursion SCC membership.
  Stores diagnostic provenance.
- **`ReachabilityEdge`.**
  Records caller and callee instance.
  Records direct or indirect cause.
  Carries source call site.
- **`CallSummary`.**
  Stores effects, quantity, captures, and cleanup class.
  Stores return and tail-call facts.
  Has canonical fingerprint.
- **`InstanceBudget`.**
  Tracks counts globally and per generic.
  Detects explosive families.
  Produces structured limits.

### Ownership and lifetime model

- **Database owns instance states.**
  Keys survive requests when cached.
  Mutable discovery is request-scoped transactionally.
  Complete products publish immutably.
- **Reachability session owns frontier worklist.**
  Roots and reasons are staged.
  Cancellation discards incomplete graph.
  Completed body products may remain memoized.
- **Specialization context owns substitution scratch.**
  Generic Core is borrowed.
  Specialized builders are local.
  Finished MIR publishes.
- **Summary SCC context owns provisional facts.**
  Iteration state stays local.
  Stable summaries publish as a group.
  Failure releases all provisional values.
- **Emission borrows reachable complete instances.**
  It does not own discovery semantics.
  Function fragments may persist.
  MIR may evict afterward.

### Algorithms and phase order

- **Seed roots.**
  Entry points, tests, and exported artifacts.
  Trusted runtime leaves are explicit.
  Sort roots canonically.
- **Canonicalize each call substitution.**
  Zonk and normalize arguments.
  Reject unresolved generic values.
  Create or reuse instance shell.
- **Traverse reachability.**
  Demand body or call summary.
  Add newly discovered callees.
  Record reason edges.
- **Handle recursive groups.**
  Detect SCCs in instance graph.
  Compute provisional summaries.
  Lower bodies with stable shells.
- **Publish reachable set and products.**
  Enforce budgets.
  Canonically order instances.
  Feed optimizer and emitter.

### Semantic invariants

- **Instance keys are fully canonical.**
  No inference variables remain.
  Alpha-equivalent binders normalize.
  Target dependence is declared.
- **Every emitted function is reachable.**
  Roots or call edges justify it.
  Dead instances may stay cached but not linked.
  Explanation records the path.
- **Recursive shells do not imply complete bodies.**
  Calls may reference a stable instance under construction.
  Publication waits for validation.
  Failed SCCs publish nothing.
- **Summaries conservatively describe bodies.**
  Callers may rely on them.
  Optimizer cannot assume stronger facts.
  Validation compares summaries to MIR.
- **Instance budgets fail before uncontrolled growth.**
  Counts use checked arithmetic.
  Diagnostics identify generic chain.
  Partial graphs do not link.

### Cycles and fixed points

- **Recursive instance graphs use SCCs.**
  Stable keys define members.
  Lowering order within group is canonical.
  Call references use shells.
- **Call summaries iterate to fixed point.**
  Effects and ownership facts widen conservatively.
  Costs may use bounded approximation.
  Stable results publish together.
- **Polymorphic recursion requires explicit policy.**
  Growing substitutions may never repeat.
  Detect monotonic key expansion.
  Reject or require annotation.
- **Indirect-call producer sets may form cycles.**
  Finite sealed producer analysis iterates.
  Unknown producers block specialization.
  Verifier sees finite runtime set.
- **Reachability explanation cycles collapse.**
  Show root path to SCC.
  List recursive members once.
  Avoid infinite call chains.

### Incremental dependencies and invalidation

- **Instance bodies depend on generic body and substitutions.**
  Unrelated instances remain green.
  Equal generic Core preserves products.
  Type-fact changes may rerun specialization.
- **Reachability depends on call targets and roots.**
  Body changes altering calls update frontier.
  Removed edges may unlink instances.
  Cached dead products remain harmless.
- **Summaries depend on SCC member MIR.**
  Equal summary can preserve callers.
  Body implementation changes may stop at summary.
  Optimizer may still rerun inlining decisions.
- **Target changes affect target-specific instances only.**
  Semantic generic Core reuses.
  Layout and native leaves key separately.
  Bytecode target policy is explicit.
- **Capability changes affect host-import reachability.**
  Pure instances may remain green.
  Artifact roots and verification rerun.
  Manifest fingerprint changes.

### Caching and persistence

- **Instance keys are persistent cache keys.**
  Callable and substitutions encode canonically.
  Compiler generations are included.
  Stable across processes.
- **Specialized MIR may cache per instance.**
  Generic body and summary dependencies manifest.
  Validators check substituted types.
  Local IDs remap.
- **Reachability sets may cache per build root.**
  Root and call-summary fingerprints key them.
  Dead cached bodies do not alter linking.
  Explanations may persist compactly.
- **SCC summaries may persist as group records.**
  Member list is canonical.
  All member fingerprints validate.
  Partial records reject.
- **Emitted fragments cache after specialization.**
  Key includes optimized MIR and target.
  Linker assembles reachable fragments.
  Final artifact remains canonical.

### Diagnostics and explanations

- **Instance explosion diagnostics show chain.**
  Generic declaration and substitutions.
  Root-to-growth path.
  Count and configured limit.
- **Polymorphic recursion diagnostics show changing key.**
  Compare successive substitutions.
  Explain unsupported pattern.
  Suggest explicit erasure or redesign.
- **Unresolved instance diagnostics show blocked goal.**
  Trait, const, or effect ambiguity.
  Call site and generic owner.
  Candidate evidence.
- **Reachability inspection shows producer reason.**
  Entry point, direct call, or sealed indirect set.
  Stable call path.
  Linked versus cached status.
- **Summary inspection shows conservative facts.**
  Effects, use, capture, cleanup, cost.
  SCC widening history.
  Optimizer consumers.

### Cancellation, limits, and security

- **Global and per-generic instance counts are bounded.**
  Discovery checks before insertion.
  Checked keys avoid overflow.
  Diagnostics remain structured.
- **Reachability edges are bounded.**
  Indirect producer expansion is metered.
  Duplicate edges deduplicate.
  Cancellation checks during traversal.
- **Specialization depth is bounded.**
  Nested generic substitutions charge depth.
  Explicit stacks avoid host recursion.
  Nonconvergence rejects.
- **Imported generic Core is hostile.**
  Substitution arity and visibility validate.
  Runtime primitive authority is checked.
  Cache cannot inject arbitrary instances.
- **Producer sets are sealed.**
  Unknown host-created callables reject.
  Empty or malformed sets fail closed.
  Verifier cross-checks artifact claims.

### Determinism and reproducibility

- **Instance keys use canonical substitutions.**
  Interning order is irrelevant.
  Alpha-renaming does not change identity.
  Cache keys reproduce.
- **Reachability worklist uses stable order.**
  Root and edge ties sort by key.
  Linked function order is canonical.
  Diagnostics remain stable.
- **SCC member order is canonical.**
  Representative is smallest stable key.
  Fixed-point iteration is deterministic.
  Summary bytes match.
- **Budget exhaustion occurs deterministically.**
  Discovery order is fixed.
  Same world hits same instance.
  Error path reproduces.
- **Fragment linking sorts reachable instances.**
  Internal discovery history is excluded.
  Function indices remap.
  Stage artifacts match.

### Testing and observability

- **Instance tests cover generic dimensions.**
  Types, consts, effects, quantities, lifetimes.
  Equivalent substitutions deduplicate.
  Invalid arity rejects.
- **Recursion tests cover finite and growing graphs.**
  Direct and mutual recursion.
  Polymorphic recursion barriers.
  Stable SCC summaries.
- **Reachability tests remove and add calls.**
  Linking updates exactly.
  Cached dead instances remain unlinked.
  Clean builds match.
- **Budget tests create controlled explosions.**
  Per-generic and global limits.
  Diagnostic chains are bounded.
  Cancellation cleanup is measured.
- **Inspection emits instance graph and summaries.**
  Filter by root or generic.
  Show cached, reachable, and linked states.
  Export canonical machine records.

### Migration and completion criteria

- **Introduce canonical `InstanceKey`.**
  Wrap current specialization paths.
  Remove raw substitution tuples.
  Add equality tests.
- **Make reachability demand-driven.**
  Replace compile-all driver gradually.
  Preserve current outputs.
  Measure memory reduction.
- **Build shared interprocedural summaries.**
  Effects, capture, use, and cost.
  Route callers and optimizer.
  Add SCC fixed points.
- **Add instance budgets and explanations.**
  Detect explosive cases early.
  Expose root paths.
  Expand self-host tests.
- **Complete when only reachable instances link.**
  Recursive graphs are bounded.
  Cache reuse is precise.
  Self-compilation stays within limits.

## 23. Optimizer Framework, Analyses, Budgets, and Invalidations

This section defines deterministic MIR optimization infrastructure.
Passes use shared analysis bundles and checked editors.
Every transformation declares invalidation and preserves ownership semantics.
Optimization remains bounded, inspectable, and differential-tested.

### Purpose and scope

- **Define optimizer pipeline architecture.**
  O0 through O3 share legality rules.
  Levels change enabled passes and budgets.
  Pass order is explicit.
- **Define reusable analyses.**
  CFG, dominators, loops, liveness, ownership.
  Scalar, aggregate, alias, and cost facts.
  Interprocedural summaries are queried.
- **Define checked transformations.**
  Mutations use MIR editor transactions.
  Invalidation masks update caches.
  Validation runs at boundaries.
- **Define resource budgets.**
  Pass work and code growth are bounded.
  Fixed points stop deterministically.
  Remarks explain limit barriers.
- **Define observability.**
  Pass traces and before-after MIR.
  Profitability and missed reasons.
  Source-defined control plans.

### Goals and non-goals

- **Goal: semantic conservatism.**
  Traps and evaluation order remain.
  Ownership and custom drop remain.
  Effects and capabilities remain.
- **Goal: deterministic profitability.**
  Cost models use stable facts.
  Ties use stable keys.
  No wall-clock heuristics.
- **Goal: shared analysis substrate.**
  Passes do not rebuild private CFG models.
  PlaceFlow remains ownership source.
  Invalidation is explicit.
- **Non-goal: different O3 legality.**
  Higher levels may spend more work.
  They cannot weaken semantics.
  Validation remains identical.
- **Non-goal: opaque monolithic optimization.**
  Pass effects are named.
  Inspection can isolate failures.
  Budgets and remarks are visible.

### Public queries and interfaces

- **`optimized_mir`.**
  Accept instance and optimization level.
  Return validated optimized body.
  Attach pass report.
- **`analysis_bundle`.**
  Demand typed analysis for MIR revision.
  Cache lazily.
  Respect invalidation mask.
- **`run_pass`.**
  Apply one named pass transactionally.
  Return changed flag and remarks.
  Validate declared invariants.
- **`optimizer_trace`.**
  Emit pass sequence and fingerprints.
  Include budget use.
  Support filtered functions.
- **`compare_optimization_levels`.**
  Diff O0 and optimized MIR.
  Show semantic trace equivalence.
  Localize first divergence.

### Primary data structures

- **`OptimizationPlan`.**
  Stores ordered pass groups.
  Stores level and budgets.
  Is compiler-generation input.
- **`AnalysisCache`.**
  Maps analysis kind to body fingerprint.
  Stores immutable results.
  Applies invalidation masks.
- **`PassContext`.**
  Owns checked editor and budget.
  Borrows summaries and target facts.
  Stages remarks.
- **`PassRemark`.**
  Stores success, missed, or limit reason.
  Maps to source and MIR site.
  Has stable code.
- **`OptimizationFingerprint`.**
  Includes raw MIR and pass generation.
  Includes level and target facts.
  Keys persistent optimized bodies.

### Ownership and lifetime model

- **Optimization request owns mutable MIR clone or transaction.**
  Raw MIR remains immutable.
  Checked editor owns changes.
  Failure discards the candidate.
- **Analysis cache belongs to body optimization session.**
  Results may persist in memory.
  Invalidated bundles drop.
  Published body excludes cache internals.
- **Interprocedural summaries are database-owned queries.**
  Passes borrow them.
  They remain immutable.
  Changes invalidate optimized callers.
- **Pass remarks belong to optimization product.**
  They may persist optionally.
  Presentation renders later.
  Large traces can evict.
- **Emission borrows final validated MIR.**
  It does not rerun optimizer semantics.
  Fragment cache may outlive MIR.
  Source maps remain companions.

### Algorithms and phase order

- **Validate raw MIR before optimization.**
  Reject impossible starting states.
  Compute initial fingerprint.
  Initialize budgets.
- **Run canonicalization passes.**
  Normalize CFG and operands.
  Remove unreachable blocks safely.
  Establish analysis prerequisites.
- **Run scalar and ownership-aware simplifications.**
  Constant propagation and copy folding.
  Loan-end and cleanup-safe rewrites.
  Validate after risky groups.
- **Run interprocedural specialization.**
  Inline under cost policy.
  Specialize callables and handlers.
  Recompute affected summaries.
- **Run final selection-oriented cleanup.**
  Tail formation and block layout hints.
  Peephole-ready canonical forms.
  Validate and publish.

### Semantic invariants

- **Every pass preserves observable behavior.**
  Values, traps, effects, and host calls.
  Evaluation order where observable.
  Runtime capability requirements.
- **Every pass preserves ownership.**
  Moves, copies, and cleanup.
  Custom drop order.
  Continuation cancellation semantics.
- **Every analysis matches current MIR.**
  Fingerprint or generation is checked.
  Invalidated results are inaccessible.
  Checked editor declares changes.
- **Every pass is deterministic.**
  Candidate order and tie breaks are stable.
  Budget consumption order is specified.
  Remarks reproduce.
- **Every published optimized body validates.**
  Structural, type, PlaceFlow, and cleanup checks.
  Failure keeps raw MIR available.
  No unsafe fallback artifact emits.

### Cycles and fixed points

- **Pass groups may iterate to fixed point.**
  Changed flag controls repetition.
  Maximum rounds are explicit.
  Stable order guarantees reproducibility.
- **CFG analyses handle loops and irreducible SCCs.**
  Dominators and liveness are deterministic.
  Loop transforms require proven preconditions.
  Nonconvergence is bounded.
- **Recursive inlining is controlled.**
  Depth and clone budgets apply.
  Recursive specialization needs explicit policy.
  Infinite expansion is prevented.
- **Interprocedural summaries use SCC fixed points.**
  Passes consume conservative facts.
  Changes may trigger group recomputation.
  Stable summaries stop propagation.
- **Optimization dependency cycles are broken by phases.**
  Raw summaries precede transformations.
  Refined summaries iterate under bounds.
  Publication occurs after convergence.

### Incremental dependencies and invalidation

- **Optimized MIR depends on raw MIR and plan.**
  Source-only mapping changes may preserve it.
  Pass generation changes rerun.
  Level changes select another key.
- **Target facts affect target-aware passes.**
  Target-neutral passes may reuse.
  Layout and cost changes invalidate later groups.
  Artifact emission always keys target.
- **Interprocedural summaries create caller dependencies.**
  Equal summaries preserve optimized callers.
  Inlining depends on callee body fingerprint.
  Noninlined calls may avoid that edge.
- **Analysis invalidation is local to transformations.**
  CFG edits drop CFG-related bundles.
  Operand replacements may preserve structure.
  Ownership changes trigger PlaceFlow validation.
- **Remarks depend on optimization diagnostics settings.**
  Semantic body can remain equal.
  Presentation records rerun.
  Cache keys separate them.

### Caching and persistence

- **Final optimized MIR is cacheable.**
  Key includes raw body and plan.
  Target facts and summaries manifest.
  Validator reruns on load.
- **Analysis bundles usually remain memory-local.**
  They are cheap relative to codec complexity.
  Selected expensive summaries may persist later.
  Eviction is harmless.
- **Pass traces are optional side records.**
  Enable on demand.
  Do not affect semantic fingerprints.
  Store bounded before-after snapshots.
- **Inlining caches may store specialized clones.**
  Clone identity includes caller context.
  Fresh brands and scopes remap canonically.
  Validators check ownership.
- **Artifact fragments key final optimized MIR.**
  Emission can reuse without rerunning passes.
  Clean builds compare bytes.
  Pass metadata stays external.

### Diagnostics and explanations

- **Missed optimization remarks name barrier.**
  Effect, alias, ownership, or cost.
  Source and MIR site.
  Stable machine code.
- **Limit remarks show exhausted budget.**
  Pass and counter.
  Candidate that was skipped.
  No silent partial optimization.
- **Validation failures name responsible pass.**
  Preserve pre-pass MIR.
  Preserve mutation trace.
  Classify as compiler invariant.
- **Control specialization explanations are first-class.**
  Static facts and residual machinery.
  Name failed proof.
  Link to source helper.
- **Optimization comparison shows semantic changes only when bugs occur.**
  Runtime trace mismatch localizes.
  MIR diff highlights transformed region.
  Reproduction command is emitted.

### Cancellation, limits, and security

- **Every pass charges typed work units.**
  Blocks, operations, clones, and solver steps.
  Parent optimizer budget aggregates.
  Limits are deterministic.
- **Code growth is bounded.**
  Inlining and specialization reserve size.
  Rollback releases reservation.
  Excess produces missed remark.
- **Cancellation checks between candidates and rounds.**
  Current transaction rolls back.
  Raw MIR remains valid.
  No optimized cache entry publishes.
- **Hostile cached MIR is revalidated.**
  Optimizer never trusts external graph.
  Checked editor protects invariants.
  Imported summaries validate.
- **Passes cannot acquire host authority.**
  Cost models use supplied target data.
  No profiling network or filesystem.
  Runtime capabilities remain semantic facts.

### Determinism and reproducibility

- **Pass order is frozen per generation.**
  Changing it advances optimizer identity.
  Cache keys miss safely.
  Release notes document changes.
- **Candidate enumeration is canonical.**
  Blocks and operations use stable order.
  Equal costs use stable keys.
  Budgets exhaust predictably.
- **Analysis worklists are deterministic.**
  SCC and loop orders are fixed.
  Hash maps never choose transformations.
  Results reproduce.
- **Remarks sort by pass and source key.**
  Parallel execution cannot reorder output.
  Machine records remain canonical.
  Human rendering is stable.
- **Optimized MIR serialization is canonical.**
  Local IDs remap.
  Dead internal allocation order disappears.
  Bootstrap stages compare.

### Testing and observability

- **Every pass has focused legality tests.**
  Positive and negative transformations.
  Ownership and cleanup barriers.
  Exact expected MIR.
- **Differential execution compares O0 and optimized.**
  Random and curated programs.
  Effects and resumptions included.
  Failing seeds persist.
- **Analysis invalidation tests mutate MIR.**
  Ensure stale bundles are rejected.
  Recomputed results match.
  Masks remain minimal.
- **Budget tests force each limit.**
  Stable missed remarks.
  No semantic changes.
  Transaction rollback verified.
- **Performance tests track compile time counters.**
  Pass work and code size.
  Self-host hot functions.
  Regression thresholds are explicit.

### Migration and completion criteria

- **Introduce checked editor before new passes.**
  Route current mutations.
  Add invalidation masks.
  Preserve optimizer behavior.
- **Group analyses into shared bundles.**
  Remove pass-local CFG copies.
  Add lazy cache.
  Benchmark reuse.
- **Add deterministic pass plans and budgets.**
  Freeze O0 through O3 policy.
  Emit remarks.
  Add repeatability tests.
- **Port transformations incrementally.**
  Validate after each group.
  Differential test VM behavior.
  Expand self-host parity.
- **Complete when every pass is inspectable and bounded.**
  All outputs validate.
  Clean and cached optimization match.
  O3 never weakens legality.

## 24. Source-Defined Control Specialization

This section defines optimization of library-defined control abstractions.
The compiler recognizes structural facts, never privileged names.
Conditionals, loops, propagation, labels, and handlers can lower to direct CFG.
Every successful or missed specialization is explainable.

### Purpose and scope

- **Recognize structural control summaries.**
  Known callables and labels.
  Exact effects and quantities.
  Static producer and environment facts.
- **Form direct branches and loops.**
  Eliminate avoidable callable allocation.
  Eliminate dynamic handler lookup.
  Preserve cleanup and evaluation order.
- **Specialize label-based transfers.**
  Proof-only labels become direct `leave`.
  Nested destinations remain branded.
  Cleanup runs before transfer.
- **Specialize effect-based helpers.**
  Static terminal handlers.
  One-shot resume and cancel composition.
  Partial handlers retain fallback.
- **Expose `control_plan`.**
  Show proofs and transformed shape.
  Show residual machinery.
  Show exact failure reason.

### Goals and non-goals

- **Goal: zero-cost source control.**
  Library abstraction should become direct CFG.
  Names remain ordinary.
  Performance is verified by inspection.
- **Goal: name independence.**
  Renamed custom helpers can specialize.
  Structural summaries drive recognition.
  Standard-library spelling is irrelevant.
- **Goal: ownership-safe fusion.**
  Captures, cleanup, and quantities are preserved.
  Nonlocal exits remain exact.
  Validation follows transformation.
- **Non-goal: heuristic semantic guessing.**
  Unknown callables remain calls.
  Missing proof blocks fusion.
  Compiler does not assume intent.
- **Non-goal: eliminate all runtime handlers.**
  Dynamic and multishot cases may remain.
  Residual behavior is correct.
  Future breadth is explicit.

### Public queries and interfaces

- **`control_summary`.**
  Return callable structural behavior.
  Include label, effect, and quantity facts.
  Be independent of name.
- **`control_plan`.**
  Analyze one call or region.
  Return direct CFG plan or barrier.
  Include residual runtime components.
- **`fuse_control`.**
  Apply plan through checked MIR editor.
  Return changed body and remarks.
  Validate ownership.
- **`control_lints`.**
  Detect helpers that fail intended fusion.
  Offer machine-applicable fixes.
  Use stable diagnostic codes.
- **`inspect_control_region`.**
  Map source helper to optimized MIR.
  Show before and after.
  Support custom libraries.

### Primary data structures

- **`ControlSummary`.**
  Stores invocation shape and effects.
  Stores label and environment requirements.
  Stores continuation quantity facts.
- **`ControlPlan`.**
  Stores direct branch, loop, or leave structure.
  Stores substitutions and transfers.
  Stores proof references.
- **`FusionBarrier`.**
  Enumerates dynamic callee, capture, effect, or cost reason.
  Carries source and MIR sites.
  Is stable and inspectable.
- **`ControlRegion`.**
  Identifies call and nested callable bodies.
  Stores cleanup and scope boundaries.
  Supports checked cloning.
- **`ResidualControlState`.**
  Records handlers, labels, or environments left at runtime.
  Feeds cost model and verifier.
  Serializes in inspection only.

### Ownership and lifetime model

- **Control summaries are database-owned queries.**
  Callables publish immutable summaries.
  Optimizer borrows them.
  Recursive groups use SCC products.
- **Plans are optimization-session values.**
  They reference one MIR revision.
  Applying or discarding ends them.
  They do not persist by default.
- **Cloned regions belong to checked editor transactions.**
  Fresh scopes and brands are allocated.
  Rollback removes them.
  Commit invalidates analyses.
- **Barriers may persist as remarks.**
  Semantic optimized body does not depend on presentation.
  Tooling can request explanations later.
  Compact proof summaries may cache.
- **Residual runtime state belongs to optimized MIR.**
  Handler and environment records remain explicit.
  Emitter does not reconstruct the decision.
  VM executes verified residuals.

### Algorithms and phase order

- **Compute callable control summary.**
  Analyze known body and signature.
  Identify tail invocation and label transfers.
  Record exact effects and quantities.
- **Match call-site static facts.**
  Resolve callee producer set.
  Check capture and environment constraints.
  Check cleanup region compatibility.
- **Construct direct control plan.**
  Map arguments and block parameters.
  Allocate fresh local scopes and brands.
  Preserve evaluation order.
- **Apply fusion transactionally.**
  Clone or redirect CFG.
  Insert cleanup-aware leaves.
  Remove proven runtime machinery.
- **Validate and report.**
  Recompute affected analyses.
  Check PlaceFlow and control identities.
  Emit success or barrier remark.

### Semantic invariants

- **Fusion is name-independent.**
  Only stable structural facts matter.
  Renaming cannot enable or disable.
  Primitive leaves remain manifest-bound separately.
- **Evaluation order is preserved.**
  Arguments and captures evaluate left to right.
  Lazy callable bodies execute only when selected.
  Traps and effects retain order.
- **Cleanup semantics are preserved.**
  Direct exits execute identical actions.
  Must-move barriers remain.
  Custom drop order remains.
- **Control brands remain fresh and scoped.**
  Cloning remaps labels and environments.
  No destination capture escapes.
  Verifier producer sets stay finite.
- **Residual runtime behavior is explicit.**
  Partial fusion does not silently discard fallback.
  Dynamic cases remain handlers or calls.
  Inspection shows them.

### Cycles and fixed points

- **Recursive control summaries use SCCs.**
  Tail recursion and loops may stabilize.
  Conservative summaries block unsafe fusion.
  Budgets bound analysis.
- **Loop formation creates CFG cycles deliberately.**
  Header and back-edge are explicit.
  State parameters are typed.
  PlaceFlow joins validate.
- **Nested label control uses brand hierarchy.**
  Transfers target exact destination.
  Fusion remaps nested brands.
  Cycles in hierarchy reject.
- **Forwarding handler graphs may contain cycles.**
  Static fusion handles proven finite paths.
  Deeper cyclic forwarding remains dynamic.
  Summary iteration is bounded.
- **Fixed-point pass application is bounded.**
  Newly exposed control may fuse in rounds.
  Round limit is deterministic.
  Stable body ends the loop.

### Incremental dependencies and invalidation

- **Control summaries depend on callable body summaries.**
  Internal edits may preserve structural shape.
  Equal summary keeps callers green.
  Source spans update remarks only.
- **Plans depend on call-site known producers.**
  New indirect producers can block fusion.
  Sealed unchanged sets preserve plan.
  Reachability changes propagate.
- **Capture and quantity changes invalidate plans.**
  Ownership barriers are explicit dependencies.
  Unrelated callee facts stay irrelevant.
  Optimized MIR reruns locally.
- **Cost policy changes affect decision only.**
  Semantic legality summary may reuse.
  Optimization generation advances.
  Artifact fragment reruns.
- **Library renaming does not invalidate structural summary unnecessarily.**
  Stable definition identity may change intentionally.
  Equivalent custom helper can produce equal summary.
  Name is presentation data.

### Caching and persistence

- **Control summaries are cacheable.**
  Keyed by callable interface and body facts.
  Canonical codec stores structural behavior.
  Validators check proof references.
- **Plans usually remain optimizer-local.**
  Applying them is cheap relative to validation.
  Final optimized MIR persists.
  Missed barrier records may persist optionally.
- **Control-plan inspection can cache compact explanations.**
  Key includes optimized MIR generation.
  Source mapping is companion data.
  Presentation settings are excluded.
- **Fused clones persist only within optimized MIR.**
  Fresh IDs remap canonically.
  No separate hidden IR is stored.
  Fragment cache follows final body.
- **Runtime residual summaries persist in artifact metadata if needed.**
  Verifier checks them.
  They do not grant source semantics.
  VM uses sealed identities.

### Diagnostics and explanations

- **Successful fusion explanations list proofs.**
  Static callee and quantity.
  Removed handlers or closures.
  Formed branch, loop, or leave.
- **Barrier diagnostics name exact missing fact.**
  Dynamic producer, escaping capture, or cleanup.
  Show source helper and call site.
  Suggest refactor when safe.
- **Control lints target developer intent.**
  Detect standard toolkit helpers expected to fuse.
  Machine fixes may expose static structure.
  Ordinary users can silence lints.
- **Ownership barrier explanations reuse PlaceFlow.**
  Show active obligation or loan.
  Avoid duplicate reasoning.
  Link to capture or exit.
- **Inspection shows residual runtime machinery.**
  Callable allocations and handler lookup.
  Label objects and continuation records.
  Estimated cost remains supplemental.

### Cancellation, limits, and security

- **Region clone size is bounded.**
  Blocks, locals, and operations reserve budget.
  Oversized fusion becomes missed optimization.
  Semantics remain unchanged.
- **Summary recursion is metered.**
  SCC iterations charge optimizer budget.
  Cancellation stops safely.
  Provisional summaries do not publish.
- **Fresh identity allocation is checked.**
  Scope and brand exhaustion is structured.
  Rollback releases failed clones.
  Verifier sets remain valid.
- **Unknown producer sets fail closed.**
  Optimizer leaves dynamic machinery.
  Verifier rejects impossible sealed claims.
  Host-created callables remain excluded.
- **Machine fixes never weaken semantics.**
  Fix applicability is proven.
  Source edits remain user-visible.
  Compiler does not auto-change code silently.

### Determinism and reproducibility

- **Summary construction uses stable traversal.**
  Calls and effects sort by source order.
  Recursive groups sort by key.
  Cache bytes reproduce.
- **Plan selection uses stable candidate order.**
  Equal legal plans use deterministic cost ties.
  Budgets exhaust predictably.
  Optimized MIR matches.
- **Fresh clone IDs derive from stable region order.**
  Persistence remaps anyway.
  Source mappings remain canonical.
  Bootstrap stages agree.
- **Barrier ordering is canonical.**
  Report first semantic barrier by priority.
  Full list sorts stably.
  Lint output reproduces.
- **Name independence is regression-tested.**
  Renamed helpers yield equal plans.
  Standard-library order does not matter.
  Artifacts remain equal.

### Testing and observability

- **Control-kernel tests cover branches and loops.**
  Range folds, early exits, and propagation.
  Nested branded control.
  Direct CFG expectations.
- **Custom helper tests prove name independence.**
  Rename and relocate declarations.
  Preserve structural summaries.
  Verify equal optimized MIR.
- **Effect fusion tests cover terminal and partial handlers.**
  One-hop forwarding.
  One-shot resume and cancel.
  Residual dynamic fallback.
- **Ownership tests cover cleanup and captures.**
  Exact-use owners.
  Loans and custom drop.
  Missed fusion barriers.
- **Inspection tests snapshot `control_plan`.**
  Success and failure reasons.
  Source-to-MIR mapping.
  O0 through O3 behavior.

### Migration and completion criteria

- **Formalize `ControlSummary`.**
  Extract existing optimizer facts.
  Remove name checks.
  Add canonical inspection.
- **Route structural control fusion through checked editor.**
  Preserve scopes and cleanup.
  Add invalidation masks.
  Differential test.
- **Add stable barrier taxonomy.**
  Emit lints and remarks.
  Connect PlaceFlow causes.
  Add machine fixes carefully.
- **Expand from direct to forwarded cases.**
  Terminal handlers first.
  One-shot compositions next.
  Leave complex multishot dynamic.
- **Complete when ordinary library control is predictably zero-cost.**
  No spelling hooks remain.
  Plans are explainable.
  Residual machinery is intentional.

---

# Volume VII — Emission and Runtime

## 25. Register Allocation, Instruction Selection, and Function Emission

This section defines translation from optimized MIR to function fragments.
Physical registers, block layout, edge transfers, cleanup maps, and opcodes are selected deterministically.
Emission is serialization mechanics, not a new semantic IR.
Every fragment remains unverified until artifact verification.

### Purpose and scope

- **Assign physical register storage.**
  Preserve exact types and ownership states.
  Reuse registers only after proven emptying.
  Keep addressable places distinct.
- **Lay out blocks deterministically.**
  Respect entry, normal, cleanup, handler, and resumption regions.
  Patch control targets.
  Preserve source mapping.
- **Select bytecode instructions.**
  Map MIR operations to frozen opcodes.
  Emit typed operands and tables.
  Handle primitives and host imports.
- **Materialize edge transfers.**
  Resolve block-parameter parallel copies.
  Break cycles with minimal temporaries.
  Preserve moves versus copies.
- **Emit canonical function fragments.**
  Pools and maps freeze.
  Fragment checksums are computed.
  Linker assembles reachable functions later.

### Goals and non-goals

- **Goal: direct MIR consumption.**
  No Stage program duplicates semantics.
  Temporary records remain emitter-local.
  MIR is the authoritative source.
- **Goal: deterministic compact bytecode.**
  Stable block and pool order.
  Minimal required temporaries.
  Canonical fragment encoding.
- **Goal: ownership-preserving allocation.**
  Register reuse respects moves and loans.
  Cleanup maps reference correct storage.
  Verifier can check plans independently.
- **Non-goal: source-level optimization.**
  Emission performs only local selection and peepholes.
  Semantic transforms belong to MIR optimizer.
  No hidden control recognition.
- **Non-goal: declare artifact safe.**
  Emitted bytes remain candidates.
  Independent verifier decides acceptance.
  VM cannot consume fragments directly.

### Public queries and interfaces

- **`register_plan`.**
  Return physical assignment per MIR local.
  Include reuse and addressability reasons.
  Support inspection.
- **`block_layout`.**
  Return ordered blocks and target labels.
  Include region classifications.
  Use deterministic keys.
- **`instruction_selection`.**
  Return emitter-local instruction records.
  Include source and MIR mappings.
  Validate operand shapes.
- **`emitted_function`.**
  Return canonical function fragment.
  Include pools, cleanup, and captures.
  Carry fragment manifest.
- **`emission_explain`.**
  Show register reuse and edge transfers.
  Show selected opcodes.
  Show local peephole results.

### Primary data structures

- **`PhysicalRegister`.**
  Stores representation and exact type identity.
  Stores reuse generation.
  Is fragment-local.
- **`RegisterAssignment`.**
  Maps MIR locals and places.
  Stores live intervals or proof summaries.
  Records addressability.
- **`BlockLayoutRecord`.**
  Stores ordered block and offset.
  Stores region kind.
  Stores fallthrough preference.
- **`SelectedInstruction`.**
  Stores typed opcode and operands.
  Stores patch sites and source identity.
  Is emitter-local scratch.
- **`FunctionFragment`.**
  Stores canonical code and tables.
  Stores signature and manifests.
  Is still unverified.

### Ownership and lifetime model

- **Emission session owns selection scratch.**
  Optimized MIR is borrowed.
  Mutable instruction records are local.
  Failure releases all buffers.
- **Register plan belongs to one MIR fingerprint.**
  It may memoize with fragment.
  Local IDs remap during encoding.
  It cannot outlive type table compatibility.
- **Patch tables belong to fragment builder.**
  They disappear after offsets resolve.
  Unresolved patches block publication.
  Final bytes are immutable.
- **Canonical pools belong to fragment or linker scope.**
  Per-function pools may remap globally.
  Freeze contexts own remap tables.
  Scratch releases.
- **Candidate fragment belongs to compiler output.**
  Cache may persist it.
  Linker borrows immutable bytes or records.
  Verifier later owns decoded view.

### Algorithms and phase order

- **Classify MIR storage.**
  Identify ZST, register, and addressable places.
  Compute exact representation facts.
  Seed allocation constraints.
- **Compute liveness and reuse opportunities.**
  Use validated analysis bundles.
  End loans and ownership before reuse.
  Respect cleanup reachability.
- **Assign physical registers deterministically.**
  Process locals in stable order.
  Choose compatible free register.
  Allocate new register on conflict.
- **Lay out blocks and select instructions.**
  Group control regions.
  Prefer safe fallthroughs.
  Emit typed patch records.
- **Resolve edge transfers and freeze fragment.**
  Plan parallel moves and copies.
  Patch targets and pools.
  Validate fragment structure.

### Semantic invariants

- **Register type compatibility is exact or proven.**
  Reuse cannot change drop identity.
  Representation compatibility needs explicit proof.
  Verifier sees final type state.
- **Moved-from registers are empty.**
  Reuse occurs only after legal transition.
  Copies leave source available.
  Parallel transfers preserve semantics.
- **Addressable places remain stable.**
  Borrowed storage cannot relocate unsafely.
  One-to-one allocation follows classification.
  End-borrow may release proof-only constraints.
- **Cleanup maps match emitted control sites.**
  Every public leave boundary has exact plan.
  Transfer temporaries are included.
  Verifier cross-checks maps.
- **Selected instructions implement MIR exactly.**
  Operand order and traps match.
  Host imports use manifest identities.
  No hidden source semantics appear.

### Cycles and fixed points

- **Register coloring may use iterative improvement.**
  G1 can start with deterministic greedy allocation.
  Future cross-block coloring remains bounded.
  Final assignment validates.
- **Parallel-copy cycles are detected explicitly.**
  Use one temporary per cycle as needed.
  Move and copy semantics are preserved.
  Algorithm terminates by removing edges.
- **Block layout graph may contain loops.**
  RPO and region grouping handle cycles.
  Stable tie breaks choose order.
  Jump patching remains finite.
- **Cleanup interval grouping may require region fixed points.**
  Shared boundaries are computed conservatively.
  Budgets bound complexity.
  Uncertain cases use separate blocks.
- **Pool canonicalization handles recursive type records.**
  Stable local indices encode SCCs.
  Linker remaps globally.
  Decoder validates cycles.

### Incremental dependencies and invalidation

- **Register plan depends on optimized MIR and type facts.**
  Source spans may not matter.
  Layout facts and target matter.
  Equal MIR preserves plan.
- **Block layout depends on CFG and cleanup regions.**
  Operand-only changes may preserve layout.
  Control changes rerun.
  Source map changes update companions.
- **Instruction selection depends on opcode generation.**
  Compiler upgrades invalidate fragments.
  Target-neutral semantics may reuse MIR.
  Host import manifest changes rerun selection.
- **Pool contents depend on referenced constants and signatures.**
  Unused package changes do not matter.
  Linker may remap without reselection.
  Canonical fragment key remains stable.
- **Peephole policy changes affect fragment fingerprint.**
  Optimized MIR may reuse.
  Emission generation advances.
  Final artifact reruns.

### Caching and persistence

- **Function fragments are high-value caches.**
  Key includes optimized MIR and target.
  Canonical bytes persist.
  Linker can assemble without MIR.
- **Register plans may persist as fragment metadata.**
  Useful for inspection and verifier debugging.
  Local IDs are canonicalized.
  Not required for runtime.
- **Block layout records may remain side data.**
  Source-to-PC mapping uses them.
  Debug records can evict.
  Code bytes remain authoritative.
- **Selection scratch never persists.**
  Patch lists and temporary pools are mutable.
  Only frozen fragment records encode.
  Failure leaves no cache entry.
- **Fragment validators run on load.**
  Check section sizes and internal references.
  Full artifact verification still occurs later.
  Cache origin grants no trust.

### Diagnostics and explanations

- **Allocation failures name incompatible constraints.**
  Type, loan, or addressability barrier.
  Usually an internal resource issue.
  Source mapping aids debugging.
- **Edge-transfer inspection shows parallel plan.**
  Source and destination registers.
  Temporary cycle breaks.
  Move versus copy reason.
- **Instruction-selection failures name MIR operation.**
  Unsupported runtime feature.
  Missing opcode or manifest leaf.
  Classify as compiler capability gap.
- **Cleanup-map failures show control boundary.**
  Missing anchor or temporary.
  Expected PlaceFlow plan.
  Preserve pre-emission MIR.
- **Emission traces map MIR to PC ranges.**
  Filter by function or operation.
  Show selected instruction words.
  Bound output safely.

### Cancellation, limits, and security

- **Physical register count is bounded.**
  Allocation checks before encoding widths.
  Excess reports function and count.
  No integer wrapping.
- **Instruction and patch counts are bounded.**
  Fragment size is preflighted.
  Target offsets use checked arithmetic.
  Cancellation checks between blocks.
- **Pool sizes are bounded.**
  Constants, signatures, and packs.
  Deduplication occurs before growth where possible.
  Artifact limits are enforced.
- **Cached fragments are hostile.**
  Internal offsets and type IDs validate.
  Manifest authority is rechecked.
  Linker cannot trust producer claims.
- **Host import selection is exact.**
  Only declared manifest identities emit.
  Arbitrary names cannot become opcodes.
  Verifier checks runtime grants.

### Determinism and reproducibility

- **Local processing order is stable.**
  Locals, blocks, and edges sort.
  Greedy allocation ties are fixed.
  Register plan reproduces.
- **Block layout uses canonical region order.**
  Entry, normal, cleanup, handler, resumption.
  Within regions use stable CFG order.
  Artifacts match.
- **Parallel-copy algorithm chooses stable cycles.**
  Smallest register starts.
  Temporary allocation is deterministic.
  Peepholes reproduce.
- **Pools freeze by canonical value bytes.**
  Insertion order disappears.
  Remap tables patch consistently.
  Fragment checksum reproduces.
- **Source maps use logical identities.**
  Host paths are excluded.
  PC ranges sort.
  Bootstrap fragments compare.

### Testing and observability

- **Allocation tests cover ownership reuse.**
  Empty registers, loans, and drop identity.
  Addressable places.
  Cross-block barriers.
- **Parallel-transfer tests cover cycles.**
  Move, copy, and mixed snapshots.
  Minimal temporary use.
  Runtime equivalence.
- **Selection tests cover every MIR operation.**
  Types, control, effects, and host imports.
  Exact opcode records.
  Unsupported features reject.
- **Fragment round-trip tests decode records.**
  Canonical bytes reproduce.
  Hostile mutations reject.
  Source maps remain exact.
- **Performance tests measure register and code counts.**
  Self-host functions and benchmarks.
  Track regressions by phase.
  Inspect hot emission paths.

### Migration and completion criteria

- **Make instruction selection consume MIR directly.**
  Remove parallel semantic stage records.
  Keep scratch private.
  Add equivalence tests.
- **Introduce deterministic register plan query.**
  Start with exact-type greedy reuse.
  Extend carefully.
  Expose inspection.
- **Centralize edge transfer planning.**
  Handle cycles and ownership.
  Remove ad hoc patches.
  Add verifier cross-checks.
- **Freeze function fragment schema.**
  Add canonical codec and cache.
  Harden validation.
  Route linker.
- **Complete when fragment reuse is safe and exact.**
  Emission is bounded.
  MIR semantics need no reconstruction.
  Clean and cached fragments match.

## 26. Interface Artifacts, Executable Artifacts, Linking, and Serialization

This section defines persistent compiler products and canonical linking.
Dependency interfaces and `.grbc` artifacts have distinct schemas and trust roles.
Linking assembles reachable fragments, capabilities, and metadata deterministically.
Serialization is schema-driven and defensively decodable.

### Purpose and scope

- **Define dependency interface artifacts.**
  Export semantic contracts for downstream compilation.
  Include required generic bodies or summaries.
  Exclude private implementation state.
- **Define executable artifact structure.**
  Sections for types, functions, code, and control metadata.
  Capability and feature declarations.
  Source maps as optional records.
- **Define deterministic linking.**
  Assemble reachable fragments and pools.
  Resolve package and function identities.
  Canonically assign artifact indices.
- **Define version and feature negotiation.**
  Critical unknown features reject.
  Noncritical metadata may skip.
  Schema generations are explicit.
- **Define defensive serialization contracts.**
  Widths, endianness, sentinels, and counts.
  Checksums and manifests.
  No raw internal IDs.

### Goals and non-goals

- **Goal: reproducible binary products.**
  Same inputs yield byte-identical artifacts.
  Pool order is canonical.
  Host paths are excluded.
- **Goal: modular downstream compilation.**
  Interfaces avoid reparsing dependencies.
  Private body edits remain isolated.
  Generic specialization remains possible.
- **Goal: independently checkable artifacts.**
  Verifier has complete runtime contract.
  Compiler claims are encoded explicitly.
  VM consumes only frozen verified products.
- **Non-goal: one universal schema.**
  Interfaces and executables serve different needs.
  Cache records remain separate.
  Conflation is avoided.
- **Non-goal: silently compatible evolution.**
  Every change has generation or feature.
  Unsupported critical changes reject.
  Migration is deliberate.

### Public queries and interfaces

- **`emit_interface`.**
  Freeze exported package semantics.
  Validate visibility and coherence.
  Return canonical bytes and manifest.
- **`decode_interface`.**
  Treat bytes as hostile.
  Rebuild stable semantic records.
  Return validated interface product.
- **`link_artifact`.**
  Accept reachable function fragments.
  Merge canonical pools and metadata.
  Return candidate `.grbc` bytes.
- **`artifact_manifest`.**
  Return complete build and feature identities.
  Include package and capability checksums.
  Support reproducibility.
- **`inspect_artifact`.**
  Decode bounded structural views.
  Show sections and mappings.
  Never imply verification success.

### Primary data structures

- **`InterfaceHeader`.**
  Stores schema and package identity.
  Stores compiler and language generations.
  Stores content checksum.
- **`InterfaceRecordSet`.**
  Stores definitions, signatures, impls, effects.
  Stores fixities and generic payloads.
  Uses artifact-local canonical indices.
- **`ArtifactHeader`.**
  Stores bytecode generation and features.
  Stores section directory.
  Stores manifest checksum.
- **`SectionSpec`.**
  Defines ID, encoding, and criticality.
  Defines element width and limits.
  Is shared by writer and decoder.
- **`LinkContext`.**
  Owns global pools and remap tables.
  Stages sections and patches.
  Publishes candidate bytes atomically.

### Ownership and lifetime model

- **Package compiler owns semantic interface product.**
  Encoder borrows it.
  Canonical bytes may persist.
  Downstream decoder owns reconstructed records.
- **Link session owns global remapping.**
  Function fragments remain immutable.
  Pool builders are mutable locally.
  Scratch releases after serialization.
- **Candidate artifact bytes belong to compiler outcome.**
  They may cache and write atomically.
  They remain unverified.
  Verifier later owns decoding.
- **Source-map sections are optional companions.**
  Runtime safety does not depend on them.
  Tooling may strip or retain.
  Checksums cover chosen product.
- **Manifests have artifact lifetime.**
  They persist beside releases.
  They contain canonical provenance.
  They own no host handles.

### Algorithms and phase order

- **Freeze package interface facts.**
  Collect exported definitions.
  Sort semantic keys.
  Remap child records.
- **Encode interface envelope.**
  Write header and feature set.
  Write bounded section directory.
  Compute checksum.
- **Collect reachable function fragments.**
  Verify compatibility and signatures.
  Sort by instance key.
  Gather referenced pools.
- **Freeze global artifact pools.**
  Deduplicate types, strings, constants, signatures.
  Produce fragment-to-global remaps.
  Patch code and metadata.
- **Serialize candidate artifact.**
  Write sections in canonical order.
  Validate lengths and offsets.
  Emit complete manifest.

### Semantic invariants

- **Interfaces expose only permitted semantics.**
  Visibility and privacy are already checked.
  Private local IDs never leak.
  Generic payloads are explicitly authorized.
- **Every artifact index refers within its section.**
  Optional references use frozen encoding.
  No sentinel ambiguity exists.
  Decoder checks every reference.
- **Every linked function has compatible signature.**
  Calls and producer sets resolve.
  Duplicate identities agree exactly.
  Conflicts reject.
- **Capability declarations match host imports.**
  No undeclared import appears.
  Unused grants may follow policy.
  Supervisor remains independent.
- **Serialization contains no semantic hidden state.**
  All runtime requirements are explicit.
  Cache metadata and host paths are absent.
  Local allocation order is erased.

### Cycles and fixed points

- **Recursive semantic records use canonical index tables.**
  Types and signatures may reference each other.
  SCC ordering is stable.
  Decoder reconstructs safely.
- **Function call cycles require no link fixed point.**
  Stable function indices resolve references.
  Reachability already computed.
  Patching is finite.
- **Pool deduplication may iterate across fragments.**
  Collect all keys before freezing.
  One canonical sort resolves them.
  No history-dependent insertion remains.
- **Feature dependency cycles are forbidden or explicit.**
  Required features form validated sets.
  Unknown critical dependencies reject.
  Metadata cannot enable runtime semantics silently.
- **Interface import cycles are package-graph policy.**
  Each interface remains independently decodable.
  SCC compilation uses prior declared contracts.
  Linker sees resolved packages.

### Incremental dependencies and invalidation

- **Interface bytes depend on exported semantic fingerprints.**
  Private body edits can preserve bytes.
  Source-map companions may change separately.
  Downstream packages reuse identical interfaces.
- **Artifact linking depends on reachable fragment set.**
  Unlinked cached instances do not matter.
  Fragment changes patch global pools.
  Equal fragment bytes preserve output.
- **Capability manifest changes affect artifact header and imports.**
  Pure function fragments may reuse.
  Verification and runtime products rerun.
  Semantic interfaces may stay equal.
- **Schema generation changes invalidate encoders and caches.**
  Old decoders may remain supported explicitly.
  Canonical products use new bytes.
  Migration is versioned.
- **Debug metadata changes can be isolated.**
  Stripped runtime artifact may remain equal.
  Full artifact checksum changes when included.
  Build mode is explicit.

### Caching and persistence

- **Interfaces are durable first-class cache records.**
  Content-addressed bytes.
  Complete package manifest.
  Defensive load path.
- **Function fragments cache independently.**
  Linker avoids re-emission.
  Global remapping occurs each build.
  Fragment schema is versioned.
- **Final candidate artifacts may cache by build manifest.**
  Exact inputs are required.
  Verification status remains separate.
  Reuse preserves checksum.
- **Decoded products may memoize in memory.**
  Raw bytes remain persistence source.
  Frozen stable records share.
  Eviction is harmless.
- **Schema migration tools operate out of band.**
  They never silently change semantic compilation.
  Converted bytes validate canonically.
  Release tooling reports provenance.

### Diagnostics and explanations

- **Interface encoding diagnostics name record.**
  Unsupported exported form.
  Invalid stable key or generic payload.
  Classify as compiler invariant or scope gap.
- **Interface decoding diagnostics name section and offset.**
  Unknown feature, count, or index.
  Distinguish corruption.
  Preserve package identity.
- **Link diagnostics show duplicate or missing symbol.**
  Stable instance and package keys.
  Conflicting signatures.
  Source call provenance where available.
- **Capability diagnostics compare imports and manifest.**
  Name exact operation.
  Show declaring package.
  Separate compile and runtime grant.
- **Artifact inspection shows canonical section inventory.**
  Sizes, counts, checksums, and features.
  Does not say verified unless verifier ran.
  Output is bounded.

### Cancellation, limits, and security

- **Section and record counts are bounded.**
  Writer checks before offsets.
  Decoder checks before allocation.
  Checked arithmetic prevents wrap.
- **Artifact size is bounded.**
  Linker preflights accumulated lengths.
  Cancellation checks between fragments.
  Oversized builds fail structurally.
- **String and constant sizes are bounded.**
  Deduplication does not bypass limits.
  Hostile interfaces cannot amplify.
  Diagnostics name record.
- **Checksums cover exact canonical bytes.**
  Tampering is detected.
  Signatures may add provenance.
  Verification still checks semantics.
- **Critical features fail closed.**
  Unknown semantics never skip.
  Noncritical debug sections may skip by policy.
  Feature sets are canonical.

### Determinism and reproducibility

- **Section order is schema-defined.**
  Writer never follows map iteration.
  Empty required sections encode consistently.
  Directory offsets reproduce.
- **Pool order uses canonical key bytes.**
  Old-to-new remaps are deterministic.
  Fragment discovery order is irrelevant.
  Artifacts match.
- **Function order uses stable instance keys.**
  Reachability history is excluded.
  Recursive calls patch after assignment.
  Stage builds agree.
- **Manifest encoding is canonical.**
  Packages, options, and capabilities sort.
  Absolute paths and timestamps are absent.
  Checksums reproduce.
- **Interface declaration order is specified.**
  Source order may remain for presentation.
  Semantic tables sort by stable key.
  Re-encoding matches exactly.

### Testing and observability

- **Interface round-trip tests cover every record.**
  Traits, effects, generics, and fixities.
  Recursive types.
  Canonical byte equality.
- **Artifact golden tests freeze compatible fixtures.**
  Old readers and new writers.
  Feature negotiation.
  Exact checksums.
- **Hostile decoder corpora mutate every section.**
  Counts, offsets, tags, and references.
  Allocation amplification.
  Bounded rejection.
- **Link tests vary fragment discovery order.**
  Artifact bytes remain equal.
  Duplicate conflicts diagnose.
  Dead fragments stay unlinked.
- **Inspection tests snapshot manifests and section tables.**
  Redaction and bounds.
  Candidate versus verified state.
  Source mapping optionality.

### Migration and completion criteria

- **Describe schemas in shared tables.**
  Replace manual numeric chains.
  Generate writer and decoder helpers.
  Add feature metadata.
- **Freeze dependency interface format.**
  Route downstream compilation.
  Harden decoder.
  Add private-change reuse tests.
- **Freeze function fragment format.**
  Add cache and validation.
  Link through canonical pools.
  Compare artifacts.
- **Separate candidate and verified artifact APIs.**
  Update `grand` and tests.
  Prevent VM bypass.
  Record manifests.
- **Complete when every persistent product is canonical and bounded.**
  Clean and warm links match.
  Old compatibility is explicit.
  Bootstrap artifacts reproduce.

## 27. Bytecode Decoder and Verifier

This section defines the independent artifact acceptance boundary.
The decoder treats every byte as hostile.
The verifier checks typed registers, ownership, references, cleanup, and control.
Successful verification yields a private frozen execution image.

### Purpose and scope

- **Decode `.grbc` defensively.**
  Validate envelope, sections, counts, and offsets.
  Avoid allocation amplification.
  Preserve artifact diagnostics.
- **Verify function and register typing.**
  Check signatures and operands.
  Track register availability and exact types.
  Validate calls and returns.
- **Verify ownership and references.**
  Moves, copies, loans, and place origins.
  Cleanup and custom drop plans.
  Aggregate binding packs.
- **Verify control identities.**
  Labels, handlers, resumptions, and producers.
  Continuation capture plans.
  Tail and nonlocal transfers.
- **Produce frozen runtime authority.**
  Normalize accepted records.
  Hide raw mutable representation.
  Permit VM construction only from success.

### Goals and non-goals

- **Goal: independent runtime contract checking.**
  Do not trust compiler-emitted summaries blindly.
  Cross-check every encoded invariant.
  Reject hostile artifacts safely.
- **Goal: bounded verification.**
  Memory and work are metered.
  Extreme graphs fail structurally.
  Worker remains responsive.
- **Goal: stable diagnostics.**
  Function, PC, and expected state.
  Machine-readable codes.
  Deterministic first failure.
- **Non-goal: repeat source compilation.**
  No name resolution or trait solving.
  No full source borrow inference.
  Lowered summaries are the contract.
- **Non-goal: execute during verification.**
  Abstract interpretation only.
  Host calls are never performed.
  Runtime side effects remain absent.

### Public queries and interfaces

- **`decode_artifact`.**
  Accept bytes and decoder limits.
  Return validated structural records.
  Preserve unknown-feature status.
- **`verify_artifact`.**
  Run complete runtime checks.
  Return frozen image or diagnostics.
  Record verifier generation.
- **`verify_function`.**
  Verify one decoded function under global tables.
  Return summary and failure context.
  Support parallel future scheduling.
- **`inspect_verified_state`.**
  Show bounded register state at PC.
  Require successful or seeded development mode.
  Never mutate verification.
- **`verification_manifest`.**
  Record artifact checksum and feature set.
  Record verifier build identity.
  Support execution and caching policy.

### Primary data structures

- **`DecodedArtifact`.**
  Owns validated section views.
  Uses checked typed indices.
  Remains unverified semantically.
- **`VerifierState`.**
  Stores register and place facts per block.
  Stores control-stack summaries.
  Uses deterministic worklists.
- **`RegisterState`.**
  Stores unavailable or typed value.
  Stores ownership mode and origin.
  Supports joins.
- **`ControlIdentityTable`.**
  Stores label, handler, and resumption producers.
  Validates finite sealed sets.
  Maps runtime IDs.
- **`FrozenExecutionImage`.**
  Stores normalized immutable code and tables.
  Is privately constructible.
  Carries verification manifest.

### Ownership and lifetime model

- **Decoder owns raw artifact bytes or bounded copy.**
  Section views borrow safely.
  Invalid bytes release promptly.
  No unchecked pointer escapes.
- **Verifier owns mutable analysis state.**
  Decoded records are immutable.
  Worklists and maps die after success.
  Compact frozen summaries publish.
- **Frozen image owns runtime-ready records.**
  VM borrows immutable tables.
  Artifact bytes may drop.
  Source maps may remain optional.
- **Diagnostics own bounded windows.**
  They retain function and PC context.
  Full verifier state does not leak.
  Development inspectors can replay artifacts.
- **Supervisor owns verification invocation policy.**
  It may cache accepted checksum metadata.
  It cannot forge frozen image.
  VM remains downstream.

### Algorithms and phase order

- **Validate artifact envelope.**
  Magic, generation, features, and directory.
  Check total size and checksum.
  Reject unknown critical features.
- **Decode canonical tables.**
  Types, signatures, constants, functions.
  Check every count and index.
  Build typed immutable views.
- **Validate instruction streams structurally.**
  Opcode widths and operands.
  Target PCs and block boundaries.
  Control-site references.
- **Run per-function abstract interpretation.**
  Seed entry register state.
  Propagate along CFG.
  Join exact-compatible states.
- **Cross-check global plans and freeze.**
  Cleanup, producer, and capture tables.
  Host imports and capabilities.
  Construct frozen image.

### Semantic invariants

- **Every instruction operand is well typed.**
  Register state matches opcode contract.
  Constants and signatures exist.
  Projection and aggregate layouts match.
- **Every move and copy is legal.**
  Moves require available source.
  Copies require copy permission.
  Destination state updates exactly.
- **Every reference origin remains valid.**
  Borrow summaries and place states agree.
  Unique and shared rules hold.
  End-borrow operations are valid.
- **Every control transfer targets compatible state.**
  Block parameters match.
  Labels and handlers have correct identity.
  Resumption producer and quantity rules hold.
- **Every cleanup plan matches abandonment state.**
  Active owners are handled exactly.
  Protected results remain.
  No positive obligation disappears.

### Cycles and fixed points

- **CFG verification is a fixed point.**
  Block input states join deterministically.
  Loops iterate until stable.
  Work budgets bound hostile graphs.
- **Recursive call graphs need signature checks only locally.**
  Functions reference verified signatures.
  Runtime recursion is allowed.
  No whole-program execution summary is required.
- **Handler and resumption control may form cycles.**
  Identity and stack summaries remain finite.
  Producer sets are sealed.
  Joins enforce compatible states.
- **Recursive type tables validate with SCCs.**
  Layout records follow artifact rules.
  Infinite expansion is avoided.
  Illegal cycles reject.
- **Diagnostic cause cycles collapse.**
  Report one stable failing path.
  Inspector can show bounded predecessor set.
  Verification remains complete.

### Incremental dependencies and invalidation

- **Verification depends on exact artifact bytes and verifier generation.**
  Source changes matter only through artifact.
  Equal bytes reuse acceptance policy if allowed.
  Frozen images remain process-local.
- **Feature policy changes require reverification.**
  Decoder support and security limits matter.
  Artifact checksum stays equal.
  Acceptance outcome may change.
- **Capability grants do not alter structural verification entirely.**
  Declared host imports are verified.
  Supervisor grants are checked at execution.
  Policy projection is explicit.
- **Source-map changes may avoid runtime-state changes.**
  If debug sections are noncritical.
  Verification of code may reuse selectively.
  Full artifact manifest still changes.
- **Cached verification summaries require exact compatibility.**
  Artifact checksum and verifier identity.
  Security policy and limits.
  Otherwise rerun.

### Caching and persistence

- **Raw artifacts are the durable format.**
  Frozen images need not persist.
  Verification reconstructs authority.
  Artifacts remain content-addressed.
- **Verification outcomes may cache cautiously.**
  Exact checksum and verifier generation.
  Security limit policy included.
  VM still receives private constructed image.
- **Per-function summaries may memoize in process.**
  Useful for repeated inspection.
  Global plan compatibility is checked.
  Eviction is harmless.
- **Hostile corpus fixtures persist.**
  Include expected rejection code.
  Avoid trusting malformed decode products.
  Reproduction remains exact.
- **Decoder indexes may remain memory-local.**
  Rebuilding is deterministic.
  Raw bytes are authoritative.
  No cache is needed for correctness.

### Diagnostics and explanations

- **Decoder diagnostics cite section and byte offset.**
  Invalid length, tag, or index.
  Show expected bounds.
  Classify corruption.
- **Verifier diagnostics cite function and PC.**
  Show opcode and register state.
  Show expected and observed type.
  Include source mapping when available.
- **Ownership diagnostics show transfer history.**
  Move source and conflicting use.
  Cleanup state at failure.
  Bounded predecessor trace.
- **Control diagnostics show identity tables.**
  Invalid label or resumption producer.
  Expected finite set.
  Actual encoded reference.
- **Inspection tools print seeded or verified windows.**
  Function signature and nearby instructions.
  Register and place facts.
  Never imply source-level proof.

### Cancellation, limits, and security

- **Decoder checks sizes before allocation.**
  Section counts and widths multiply safely.
  Compression amplification is bounded.
  Extreme values reject.
- **Verifier state counts are bounded.**
  Registers, blocks, and places.
  Worklist steps and joins.
  Resource diagnostics are structured.
- **Cancellation checks between functions and worklist batches.**
  Partial frozen image never publishes.
  Decoded bytes may be discarded.
  Retry remains safe.
- **Every table reference is range-checked.**
  No unchecked indexing.
  Unknown opcodes reject.
  Optional sentinel encodings are explicit.
- **Frozen image constructors are private.**
  Only complete verification calls them.
  Tests use dedicated seeded development APIs.
  VM cannot bypass authority.

### Determinism and reproducibility

- **Decode order follows section schema.**
  Map insertion does not affect records.
  Unknown noncritical sections skip deterministically.
  Diagnostics reproduce.
- **Verifier worklists use stable block order.**
  Joins and first failures are stable.
  Parallel future execution merges deterministically.
  Logical counters reproduce.
- **Register-state serialization for inspection is canonical.**
  Sort registers and origins.
  Local addresses are absent.
  Snapshots compare.
- **Feature and capability tables sort canonically.**
  Producer sets use stable IDs.
  Artifact bytes already canonical.
  Acceptance is repeatable.
- **Verification manifest excludes wall time.**
  Includes checksum and generation.
  Resource counters may be recorded separately.
  Release evidence reproduces.

### Testing and observability

- **Golden valid artifacts cover every feature.**
  Calls, ownership, references, and cleanup.
  Handlers and resumptions.
  Host imports.
- **Hostile corpora mutate every field.**
  Truncation, extreme counts, sparse IDs.
  Invalid control and cleanup maps.
  Allocation amplification.
- **Differential verifier tests compare seeded compiler facts.**
  Ensure compiler and verifier contracts align.
  Preserve failing pre-oracle artifacts.
  Inspect exact PC.
- **Fuzz targets run decoder and verifier separately.**
  Fixed seeds and coverage guidance.
  Supervisor memory limits.
  Stable rejection classes.
- **Performance tests measure large valid artifacts.**
  State counts and instruction rate.
  Memory growth sampling.
  Regression thresholds.

### Migration and completion criteria

- **Keep verifier independent from compiler modules.**
  Share schemas, not mutable representations.
  Add typed decoder views.
  Preserve existing safety checks.
- **Replace manual field handling with schema tables.**
  Centralize widths and criticality.
  Generate validation helpers where appropriate.
  Add compatibility tests.
- **Strengthen cleanup and reference cross-checks.**
  Consume final MIR ownership source.
  Add hostile artifacts.
  Remove seeded-only gaps over time.
- **Privatize frozen image construction.**
  Update VM and tests.
  Separate development inspection commands.
  Audit bypasses.
- **Complete when arbitrary bytes fail safely.**
  Valid artifacts execute consistently.
  Resource use is bounded.
  Verifier claims remain precise.

## 28. VM, Supervisor, Host Capabilities, and Runtime Limits

This section defines execution after verification.
The VM is a typed register machine over frozen artifacts.
The supervisor enforces process, memory, time, and capability policy.
Host access occurs only through exact adapters.

### Purpose and scope

- **Execute verified bytecode semantics.**
  Registers, frames, aggregates, and control.
  Calls, handlers, resumptions, and cleanup.
  Traps and abort behavior.
- **Isolate runtime resources.**
  Supervisor creates worker process.
  Memory and time limits are external.
  Termination is classified.
- **Mediate host capabilities.**
  Process arguments, filesystem, diagnostics.
  Exact operation grants.
  No wildcard prefix authority.
- **Preserve ownership runtime behavior.**
  Moves empty registers.
  Destruction follows verified plans.
  Continuations capture verified state.
- **Expose deterministic runtime diagnostics.**
  Artifact function and PC.
  Host denial and resource termination.
  Optional source mapping.

### Goals and non-goals

- **Goal: small runtime semantics.**
  VM knows bytecode only.
  No parser or source type checker.
  No control-name recognition.
- **Goal: exact capability isolation.**
  Worker has no ambient access.
  Adapters validate every request.
  Supervisor policy remains independent.
- **Goal: bounded execution.**
  Time, memory, and host-call limits.
  Worker can be terminated safely.
  Resource failure differs from trap.
- **Non-goal: threads or async executor in G1.**
  Single-threaded bytecode semantics.
  Host may supervise processes.
  Future concurrency needs new design.
- **Non-goal: arbitrary FFI.**
  Finite host-import set only.
  Opaque native callbacks are excluded.
  Unsafe memory access is absent.

### Public queries and interfaces

- **`run_verified`.**
  Accept frozen image and grants.
  Start supervised worker.
  Return runtime outcome.
- **`step_vm`.**
  Execute one verified instruction internally.
  Update typed runtime state.
  Support debugger mode.
- **`host_request`.**
  Emit typed capability request.
  Include exact operation and arguments.
  Await validated response.
- **`runtime_limits`.**
  Configure memory, time, instructions, and calls.
  Normalize policy.
  Record in execution manifest.
- **`runtime_inspect`.**
  Report function, PC, frames, and registers.
  Require debugging authority.
  Bound sensitive values.

### Primary data structures

- **`VmImage`.**
  Borrows frozen code and tables.
  Contains no raw unverified bytes.
  Is immutable.
- **`VmFrame`.**
  Stores function, PC, and registers.
  Stores handler and cleanup context.
  Belongs to worker.
- **`RuntimeValue`.**
  Represents scalars, aggregates, references, callables.
  Uses checked arena handles.
  Tracks unavailable state.
- **`ContinuationRecord`.**
  Stores captured frames and environment.
  Stores quantity and identity.
  Follows verified plan.
- **`CapabilityRequest`.**
  Stores exact capability and operation.
  Stores bounded serialized arguments.
  Carries artifact import identity.

### Ownership and lifetime model

- **Supervisor owns worker process.**
  It owns policy and termination handles.
  Worker cannot extend its lifetime.
  Exit outcome returns to host.
- **Worker owns VM mutable state.**
  Frames and arenas are local.
  Frozen image is borrowed or shared immutably.
  Cleanup releases values.
- **Runtime values own or borrow according to verified type.**
  Moves transfer ownership.
  References carry checked origin handles.
  unavailable slots reject use.
- **Continuations own captured snapshots.**
  One-shot consumption moves state.
  Finite replay follows copy policy.
  Cancellation runs verified cleanup.
- **Host adapters own external resources.**
  Files and buffers never enter VM unchecked.
  Responses are bounded and typed.
  Grants define lifetime and scope.

### Algorithms and phase order

- **Verify or load frozen image.**
  Normal path always verifies first.
  Check execution feature compatibility.
  Prepare immutable tables.
- **Create supervised worker.**
  Apply OS or process limits.
  Supply exact capability grant set.
  Initialize entry arguments.
- **Execute register-machine loop.**
  Fetch verified instruction.
  Apply typed state transition.
  Meter steps and memory.
- **Route control and host operations.**
  Calls push frames.
  Effects dispatch handlers.
  Host imports create requests.
- **Finalize outcome.**
  Run required cleanup on normal paths.
  Classify trap, abort, denial, or limit.
  Return bounded diagnostics.

### Semantic invariants

- **VM executes only verified instructions.**
  PC targets are prevalidated.
  Runtime still checks arena handles.
  Unknown opcode is impossible in frozen image.
- **Unavailable registers cannot be read.**
  Moves empty source.
  Copies preserve source.
  Debug mode follows same rule.
- **References use checked origins.**
  Arena generations prevent stale handles.
  Unique and shared runtime constraints follow contract.
  Host responses cannot forge references.
- **Control identities remain sealed.**
  Labels and resumptions match producer tables.
  Handler stacks follow verified transitions.
  Unknown host callables cannot appear.
- **Capability requests match declared imports.**
  Artifact declaration and supervisor grant both required.
  Adapter validates arguments.
  Denial cannot escalate.

### Cycles and fixed points

- **Runtime loops execute ordinary CFG cycles.**
  Step limits and time limits bound them externally.
  VM does not require fixed-point analysis.
  Progress sampling remains optional.
- **Recursive calls create frame cycles over time.**
  Call depth is limited.
  Tail calls may reuse frames when verified.
  Stack overflow becomes resource outcome.
- **Object graphs may contain cycles under allowed semantics.**
  Cycle-reclamation policy is explicit.
  Tracked nodes use checked handles.
  Unsupported ownership cycles reject earlier.
- **Deep handlers can reinstate stacks.**
  Continuation records capture finite state.
  Resume and cancel semantics are explicit.
  Quantity limits bound replay.
- **Supervisor request loops are protocol-bounded.**
  Every host request receives one response or termination.
  Sequence numbers prevent confusion.
  Worker cannot recurse into supervisor code directly.

### Incremental dependencies and invalidation

- **Runtime execution depends on frozen artifact and grants.**
  Source facts are irrelevant directly.
  Equal artifact bytes may reuse verification policy.
  Different grants produce different execution manifest.
- **VM implementation changes affect runtime build identity.**
  Artifacts may remain compatible.
  Compatibility tests decide.
  Frozen images are reconstructed.
- **Host adapter policy changes affect only executions using it.**
  Pure artifacts remain unaffected.
  Capability denial behavior may change by explicit version.
  Compiler semantics remain reusable.
- **Source maps affect diagnostics only.**
  Code execution stays equal.
  Debugging products may reload.
  Stripped artifacts remain valid.
- **Runtime limit changes do not alter artifact semantics.**
  Execution outcome may change.
  Manifest records policy.
  Caches of runtime outcomes are generally avoided.

### Caching and persistence

- **Frozen images remain process-local caches.**
  Raw artifact bytes persist.
  Verification reconstructs safe views.
  VM state never persists as compiler truth.
- **Runtime outcomes are not build caches by default.**
  Host state and arguments matter.
  Tests may memoize only hermetic executions explicitly.
  Policy is separate.
- **Standard immutable tables may share across workers.**
  Only after verification.
  Sharing is read-only.
  Supervisor controls lifetime.
- **Host adapter caches are capability-specific.**
  Filesystem reads obey path and freshness policy.
  They cannot alter compiler caches.
  Deterministic tests use supplied data.
- **Crash artifacts may persist for debugging.**
  Bounded execution trace and manifest.
  Sensitive values are redacted.
  They grant no replay authority automatically.

### Diagnostics and explanations

- **Runtime trap diagnostics show function and PC.**
  Include opcode and trap class.
  Map to source when available.
  Avoid compiler-semantic claims.
- **Capability denial diagnostics show exact request.**
  Declared import and missing grant.
  Adapter policy reason.
  Stable runtime code.
- **Resource termination diagnostics name limit.**
  Time, memory, instructions, or call depth.
  Include observed counters when safe.
  Distinguish supervisor kill.
- **Continuation diagnostics show identity and quantity.**
  Invalid state should be impossible after verification.
  Runtime corruption becomes invariant failure.
  Debug context is bounded.
- **Progress diagnostics are opt-in.**
  Report instructions, function, PC, and depth.
  Use logical counters.
  Avoid changing execution semantics.

### Cancellation, limits, and security

- **Supervisor enforces hard process limits.**
  Worker self-report is insufficient.
  Memory and time are externally monitored.
  Termination remains reliable.
- **VM enforces logical limits.**
  Instruction and call counters.
  Arena allocation budgets.
  Host-call request counts.
- **Host arguments are validated and bounded.**
  Paths, lengths, and encodings.
  Adapter canonicalizes policy.
  Worker receives typed responses.
- **Worker has no ambient filesystem or network.**
  Sandboxing and process setup enforce this.
  Only protocol channel remains.
  Capability tests audit it.
- **Runtime values use checked handles.**
  Generation tags prevent use-after-free.
  Bounds checks precede access.
  Hostile programs cannot forge handles.

### Determinism and reproducibility

- **Pure verified executions are deterministic under fixed inputs.**
  VM instruction order is fixed.
  No random state exists implicitly.
  Host responses must be supplied deterministically.
- **Runtime diagnostics use stable logical identities.**
  Function and PC, not addresses.
  Frame order is deterministic.
  Source maps are canonical.
- **Capability sets are canonically ordered.**
  Grant parsing yields exact normalized set.
  Manifest checksum reproduces.
  Denial selection is stable.
- **Progress sampling is semantically external.**
  Sampling intervals use instruction counts.
  Output timing may vary.
  Program result does not.
- **VM compatibility fixtures freeze behavior.**
  Golden artifacts execute identically.
  Runtime build changes are detected.
  Stage compilers rely on stable semantics.

### Testing and observability

- **VM instruction tests cover every opcode.**
  Scalars, aggregates, references, and control.
  Ownership transitions.
  Trap behavior.
- **Supervisor tests force every limit.**
  Memory, time, call depth, and host calls.
  Stable classifications.
  Worker cleanup.
- **Capability tests attempt unauthorized access.**
  Missing grants and malformed arguments.
  Prefix and wildcard attacks.
  Adapter path policy.
- **Handler and continuation tests cover deep behavior.**
  Resume, replay, forwarding, cancel.
  Captured values and cleanup.
  Interpreter differential where applicable.
- **Memory and hot-function profiling are built in.**
  Sparse logical sampling.
  Arena occupancy and frame counts.
  Low overhead under disabled mode.

### Migration and completion criteria

- **Require frozen image at VM boundary.**
  Remove raw artifact constructors.
  Update tests and tools.
  Preserve seeded development commands separately.
- **Move host I/O behind supervisor adapters.**
  Remove ambient worker access.
  Add exact grant protocol.
  Test denials.
- **Unify runtime value and handle checks.**
  Harden generation tags.
  Add hostile runtime tests.
  Measure performance.
- **Add complete limit and progress instrumentation.**
  Use logical counters.
  Integrate supervisor reports.
  Bound diagnostics.
- **Complete when execution authority is independently enforced.**
  Verified code only.
  Exact capabilities only.
  Resource failure remains controlled.

---

# Volume VIII — User Experience, Validation, and Self-Hosting

## 29. Diagnostics, Explanations, and Machine-Applicable Fixes

This section defines diagnostics as stable structured semantic products.
Errors, warnings, limits, corruption, and invariants remain distinct.
Every advanced Glorious rule should be explainable.
Machine fixes are explicit, safe, and user-controlled.

### Purpose and scope

- **Define one cross-phase diagnostic model.**
  Stable code and class.
  Primary, related, and owner sites.
  Expected and observed facts.
- **Define rich semantic explanations.**
  Types, effects, quantities, borrowing, and control.
  Proof and dependency paths.
  Bounded detail levels.
- **Define deterministic rendering.**
  Text, JSON, and LSP forms.
  Presentation options stay external.
  Ordering is canonical.
- **Define lint policy and fixes.**
  Allow, warn, and deny levels.
  Machine-applicable edits require proof.
  User confirmation remains explicit.
- **Define failure taxonomy.**
  Source, resource, cancellation, corruption.
  Invariant, verification, and runtime.
  Codes never collapse categories.

### Goals and non-goals

- **Goal: diagnostics as data.**
  Semantic phases never print.
  Clients choose rendering.
  Tests compare structured forms.
- **Goal: unusual clarity for unusual semantics.**
  Quantity arithmetic is shown.
  Continuation captures are shown.
  Private consumption authority is shown.
- **Goal: stable machine contracts.**
  Codes and location spaces are versioned.
  JSON is canonical.
  Fix applicability is explicit.
- **Non-goal: expose all internal state by default.**
  User messages remain focused.
  Developer mode adds proof traces.
  Sensitive details are redacted.
- **Non-goal: automatic unsafe rewrites.**
  Fixes cannot guess ownership intent.
  Nonlocal semantic changes require user action.
  Suggestions may remain nonmachine-applicable.

### Public queries and interfaces

- **`diagnostics_for`.**
  Return sorted diagnostics for request root.
  Include recovery and failure status.
  Support filtering by package and severity.
- **`explain_diagnostic`.**
  Return deeper derivation on demand.
  Include proof and dependency paths.
  Bound recursion and size.
- **`render_diagnostics`.**
  Convert structured records to text or JSON.
  Apply color and width options.
  Preserve stable content fields.
- **`applicable_fixes`.**
  Return edits with confidence class.
  Validate revision and source anchors.
  Include preconditions.
- **`apply_fix_preview`.**
  Produce new immutable source revision.
  Recheck affected diagnostics.
  Never write source silently.

### Primary data structures

- **`CompilerDiagnostic`.**
  Stores code, class, severity, and message key.
  Stores typed source sites.
  Stores expected and observed payloads.
- **`DiagnosticSite`.**
  Names source, token, definition, Core, MIR, or artifact location.
  Carries stable identity.
  Supports remapping to presentation.
- **`ExplanationNode`.**
  Stores derivation step and children.
  Uses stable cause keys.
  Supports cycle collapse.
- **`MachineFix`.**
  Stores revision-qualified text edits.
  Stores applicability and preconditions.
  Stores diagnostic origin.
- **`LintPolicy`.**
  Maps stable code groups to levels.
  Merges manifest and CLI overrides.
  Is explicit compiler input.

### Ownership and lifetime model

- **Phases own local error enums.**
  Exhaustive adapters create compiler diagnostics.
  Local context can drop afterward.
  Stable records publish.
- **Request owns diagnostic staging.**
  Cancelled requests discard presentation.
  Complete semantic diagnostics may memoize.
  Sorting occurs before publication.
- **Explanation trees are lazily derived.**
  Core diagnostics store compact causes.
  Deep trees build on request.
  They may evict independently.
- **Fixes belong to one source revision.**
  Stale edits reject.
  Preview creates a new revision.
  Host client owns actual file writes.
- **Renderers own presentation buffers.**
  Semantic diagnostics remain immutable.
  Color and width never enter fingerprints.
  Buffers release after response.

### Algorithms and phase order

- **Create phase-local semantic error.**
  Capture typed identities and facts.
  Avoid rendering strings early.
  Distinguish user and invariant class.
- **Adapt to cross-phase diagnostic.**
  Map stable code and site spaces.
  Attach owner and related sites.
  Store message arguments.
- **Merge and sort request diagnostics.**
  Apply lint levels.
  Deduplicate equivalent reports.
  Sort by logical source and code.
- **Generate explanation on demand.**
  Traverse proof or dependency causes.
  Collapse cycles.
  Enforce depth and size limits.
- **Validate and present fixes.**
  Check anchors against revision.
  Simulate edits and requery when needed.
  Return preview.

### Semantic invariants

- **Every diagnostic has a stable class.**
  User errors differ from corruption.
  Invariants differ from resource limits.
  Renderers cannot change class.
- **Every source site belongs to the request revision.**
  Stable keys remap explicitly.
  Stale anchors do not guess.
  Generated sites name provenance.
- **Expected and observed payloads are typed.**
  Type intervals cannot appear as strings only.
  Renderers interpret structured facts.
  JSON remains useful.
- **Fixes preserve diagnostic preconditions.**
  Revision and source text match.
  Applicability level is honest.
  Unsafe intent changes are not automatic.
- **Diagnostic order is semantically irrelevant but deterministic.**
  Collection order cannot leak.
  Stable sorting is central.
  Tests compare it.

### Cycles and fixed points

- **Explanation graphs may contain solver cycles.**
  Collapse SCCs to stable nodes.
  Show recursive obligation once.
  Preserve representative causes.
- **Diagnostic deduplication uses fixed canonical keys.**
  Repeated paths collapse.
  Related sites merge deterministically.
  No unbounded duplicate growth.
- **Fix validation may trigger new diagnostics.**
  Preview uses a new request.
  It never mutates current staging.
  Cycles end at bounded recheck count.
- **Lint inheritance follows acyclic precedence.**
  Defaults, manifest, package, CLI.
  Conflicts resolve by explicit order.
  No recursive configuration.
- **Dependency explanations reuse query graph SCCs.**
  Avoid building another cycle model.
  Stable summaries remain bounded.
  Developer output is finite.

### Incremental dependencies and invalidation

- **Semantic diagnostics depend on semantic products.**
  Equal facts may preserve errors.
  Source spans can update separately.
  Presentation rerenders cheaply.
- **Lint policy changes affect severity and build success.**
  Underlying semantic diagnostic may reuse.
  Final request outcome reruns.
  Artifact emission may be blocked.
- **Source edits invalidate revision-qualified fixes.**
  Stable anchors may support recomputation.
  Old text edits never apply blindly.
  Preview requires current revision.
- **Explanation queries depend on compact cause records.**
  Deep proof formatting is presentation-only.
  Semantic values remain green.
  Cache policy is separate.
- **Diagnostic wording generation changes affect presentation.**
  Stable code and payload may remain equal.
  Golden text tests rerun.
  Code generation is unaffected.

### Caching and persistence

- **Structured semantic diagnostics may memoize with queries.**
  Source revision and facts key them.
  Presentation text is not stored necessarily.
  Recovery status persists.
- **Explanation trees usually remain on-demand caches.**
  Large proofs are expensive.
  Compact causes are authoritative.
  Eviction is harmless.
- **Golden diagnostic fixtures persist in tests.**
  JSON and text forms.
  Stable code migrations are explicit.
  Source spans use logical paths.
- **Fix records do not persist across revisions.**
  They are cheap to regenerate.
  Stale application is dangerous.
  Revision key is mandatory.
- **Corruption and invariant reports may persist separately.**
  Crash bundles contain bounded context.
  They are not compiler result caches.
  Privacy redaction applies.

### Diagnostics and explanations

- **Type explanations show unification path.**
  Expected and found terms.
  Decisive constraints.
  Ambiguous candidates.
- **Effect explanations show row flow.**
  Operation performance and handlers.
  Residual outward row.
  Forwarding path.
- **Quantity explanations show interval arithmetic.**
  Sequence, branch, and replay.
  Principal and actual bounds.
  Blocking obligation.
- **Borrow explanations show loan timeline.**
  Borrow, last use, conflict, and escape.
  Suspension boundary when relevant.
  Place projections.
- **Control explanations show optimizer proof.**
  Known callable and brand facts.
  Formed CFG or missed barrier.
  Residual runtime machinery.

### Cancellation, limits, and security

- **Diagnostic counts are bounded.**
  Phases may stop after ceiling.
  Suppression summary is deterministic.
  First errors remain useful.
- **Explanation depth and breadth are bounded.**
  Cycles collapse.
  Child lists truncate presentation.
  Semantic rejection remains exact.
- **Source snippets are size-limited.**
  Long lines truncate safely.
  Unicode boundaries remain valid.
  Private paths can redact.
- **Fix application is capability-controlled by client.**
  Compiler returns edits only.
  Host decides writing.
  LSP requires explicit workspace edit.
- **Invariant reports avoid secret leakage.**
  Logical identities replace absolute paths.
  Source excerpts are opt-in.
  Remote telemetry follows policy.

### Determinism and reproducibility

- **Diagnostic sort key is specified.**
  Package, file, span, severity, code.
  Related labels sort similarly.
  Collection order is excluded.
- **Message templates are versioned.**
  Structured payload stays stable.
  Text changes are deliberate.
  JSON remains canonical.
- **Proof path selection uses stable priorities.**
  Shortest or earliest semantic cause.
  Ties use stable keys.
  Explanations reproduce.
- **Fix edit ordering is canonical.**
  Sort by file and descending range for application.
  Conflicts are diagnosed.
  Preview is deterministic.
- **Lint policy normalization is canonical.**
  Code groups expand stably.
  Overrides follow fixed precedence.
  Build manifests reproduce.

### Testing and observability

- **Structured diagnostic tests assert payloads.**
  Not only rendered strings.
  Codes, sites, and facts.
  Every phase adapter is exhaustive.
- **Golden rendering tests cover text and JSON.**
  Width and color modes.
  Unicode and long lines.
  Stable ordering.
- **Explanation tests cover cycles and truncation.**
  Trait, region, and query graphs.
  Bounded output.
  Useful representative causes.
- **Fix tests apply edits to snapshots.**
  Requery diagnostics.
  Reject stale and conflicting fixes.
  Verify machine applicability.
- **Diagnostic performance tests use error-heavy source.**
  Count and memory limits.
  Deduplication cost.
  Editor latency.

### Migration and completion criteria

- **Centralize cross-phase diagnostic structure.**
  Keep phase-local enums.
  Write exhaustive adapters.
  Remove numeric projection families.
- **Return diagnostics from compiler boundaries.**
  Move rendering to CLI and LSP.
  Add canonical sorting.
  Preserve current messages initially.
- **Add typed explanation payloads.**
  Types, effects, quantities, and loans.
  Build on existing proof facts.
  Expose on demand.
- **Introduce revision-qualified machine fixes.**
  Start with trivial syntax and lint fixes.
  Add semantic fixes only with proof.
  Test preview.
- **Complete when advanced failures are actionable.**
  Stable structured APIs serve all tools.
  No phase prints directly.
  Failure classes remain honest.

## 30. Compiler Service APIs and Tooling

This section defines how CLI, package tooling, LSP, formatter, docs, tests, and inspectors consume one compiler service.
Transport and presentation remain outside semantics.
Long-lived revisions and cancellation support editors.
Every tool uses shared source and semantic products.

### Purpose and scope

- **Define compiler-as-library API.**
  Typed requests and outcomes.
  Snapshot-scoped semantic queries.
  No command-specific semantic path.
- **Define thin command adapters.**
  `grc` parses options and files.
  `grand` assembles packages.
  Both call shared services.
- **Define LSP integration.**
  Document versions and overlays.
  Cancellation and partial recovery.
  Hover, definition, references, rename.
- **Define formatter and docs integration.**
  Shared lossless source model.
  Resolved interfaces and links.
  No duplicate parser or resolver.
- **Define inspection and testing clients.**
  Core, MIR, control, cache, and verifier views.
  Compile-fail structured diagnostics.
  Verified runtime execution.

### Goals and non-goals

- **Goal: one semantic engine for every tool.**
  No LSP checker drift.
  No formatter grammar drift.
  No docs resolver drift.
- **Goal: stable machine interfaces.**
  JSON diagnostics and inspection records.
  Versioned capabilities query.
  Predictable exit statuses.
- **Goal: responsive editor service.**
  Incremental snapshots and cancellation.
  Demand appropriate analysis depth.
  Recovery remains explicit.
- **Non-goal: semantic logic in protocol adapters.**
  LSP maps coordinates only.
  CLI renders outcomes only.
  Package tool resolves external dependencies only.
- **Non-goal: mandatory daemon for all builds.**
  Short-lived library use remains supported.
  Long-lived service reuses state.
  Behavior stays identical.

### Public queries and interfaces

- **`compiler_capabilities`.**
  Return supported phases, emits, and schemas.
  Include language and bytecode generations.
  Support tool negotiation.
- **`check_package`.**
  Demand semantic roots only.
  Return diagnostics and interfaces.
  Emit no artifact.
- **`build_package`.**
  Demand verified candidate artifact path.
  Return bytes and manifest.
  Host writes atomically.
- **`semantic_request`.**
  Accept snapshot and typed query.
  Return source-facing product.
  Support cancellation.
- **`format_request`.**
  Accept source snapshot and range.
  Use shared lossless syntax.
  Return edits, not writes.

### Primary data structures

- **`CompilerService`.**
  Owns or borrows `CompilerDatabase`.
  Exposes typed request methods.
  Has no transport assumptions.
- **`ClientSession`.**
  Stores client capabilities and presentation policy.
  Stores active revisions.
  Owns cancellation handles.
- **`SemanticResponse<T>`.**
  Stores complete or recovered product.
  Stores diagnostics and revision.
  Is serializable when appropriate.
- **`WorkspaceOverlay`.**
  Maps logical files to unsaved blobs.
  Creates immutable revisions.
  Is LSP-owned input state.
- **`InspectionRequest`.**
  Names query, filters, and output limit.
  Uses stable identities.
  Produces canonical records.

### Ownership and lifetime model

- **Compiler service owns database or explicit handle.**
  Clients cannot mutate interners.
  Multiple sessions share immutable facts.
  Shutdown releases process state.
- **CLI sessions are short-lived.**
  One normalized world and request.
  Outcomes return to process adapter.
  Database may be ephemeral.
- **LSP sessions are long-lived.**
  They retain recent revisions.
  Obsolete requests cancel.
  Overlay bytes remain client-owned until interned.
- **Formatter requests borrow source products.**
  Edits are response-owned.
  Host applies them.
  Formatting scratch releases.
- **Inspection products are bounded snapshots.**
  They do not pin entire database indefinitely.
  Pagination uses stable cursors.
  Sensitive data follows policy.

### Algorithms and phase order

- **Adapter assembles or selects revision.**
  `grand` reads package world.
  LSP applies overlay edits.
  Direct `grc` reads explicit files.
- **Client chooses demand depth.**
  Syntax, resolution, check, build, or inspect.
  Service invokes typed roots.
  Unneeded phases remain lazy.
- **Compiler returns structured response.**
  Diagnostics, products, and manifest.
  No host writes occur internally.
  Revision identity is included.
- **Adapter renders or transmits.**
  CLI text or JSON.
  LSP protocol objects.
  Formatter workspace edits.
- **Client manages lifecycle.**
  Cancel obsolete requests.
  Retire revisions.
  Persist outputs atomically.

### Semantic invariants

- **Equivalent clients reach equivalent query roots.**
  `grand check` and direct `grc --check` align.
  LSP diagnostics use same semantics.
  Differences are input-world differences only.
- **Adapters do not invent semantic facts.**
  They may filter and render.
  They cannot select traits or effects.
  Private IDs remain hidden.
- **Every response names its revision.**
  Clients reject stale edits.
  LSP versions map explicitly.
  Fixes remain revision-qualified.
- **Recovered products are client-visible as recovered.**
  Build roots reject them.
  Editor features may accept.
  Status never disappears in serialization.
- **Host writes remain explicit client actions.**
  Compiler cannot modify source or outputs.
  Atomicity belongs to adapter.
  Permissions remain host policy.

### Cycles and fixed points

- **Protocol request nesting does not create semantic recursion implicitly.**
  Each semantic query uses query engine policy.
  LSP callbacks remain transport-only.
  Deadlocks are avoided.
- **Workspace dependency cycles follow package rules.**
  `grand` assembles graph.
  Compiler reports semantic cycle policy.
  Service does not resolve versions recursively.
- **Editor edit loops create successive revisions.**
  Fix preview and recheck are bounded.
  No in-place mutation cycle.
  Stale requests cancel.
- **Documentation links may form cycles harmlessly.**
  Symbol graph traversal uses visited sets.
  Output remains finite.
  Semantic definitions are unchanged.
- **Inspection pagination uses stable cursors.**
  Cursors bind revision and query fingerprint.
  Stale cursors reject.
  No cyclic retention occurs.

### Incremental dependencies and invalidation

- **Client requests depend on selected semantic roots.**
  Hover may stop before MIR.
  Build demands full artifact.
  Formatting uses lossless syntax.
- **Overlay edits create precise source changes.**
  Unchanged workspace files reuse.
  Diagnostics rerun lazily.
  Old responses are revision-tagged.
- **Presentation settings affect rendering only.**
  Color, width, and locale policy.
  Semantic caches stay green.
  JSON remains canonical.
- **Client capability negotiation affects response shape.**
  Not source semantics.
  Unsupported fields are omitted explicitly.
  Query products may reuse.
- **Tooling schema changes advance API generation.**
  Compiler semantics may remain unchanged.
  Clients negotiate versions.
  Cached serialized responses invalidate.

### Caching and persistence

- **Long-lived service reuses in-memory queries.**
  Multiple client sessions share safely.
  Revision pins control retention.
  Eviction respects active requests.
- **`grand` may use persistent compiler cache.**
  Service validates records.
  Host chooses cache directory.
  Offline mode remains explicit.
- **LSP may keep local presentation caches.**
  Hover and symbols by revision.
  Semantic products remain compiler-owned.
  Stale versions evict.
- **Documentation outputs may cache by interface fingerprint.**
  Private body edits avoid regeneration.
  Source links depend on mapping fingerprint.
  Output writes stay external.
- **Inspection outputs are usually not persistent semantic caches.**
  They derive from authoritative products.
  Expensive traces may store optional snapshots.
  Schema version is included.

### Diagnostics and explanations

- **CLI renders stable diagnostics and exit codes.**
  Text and JSON modes.
  Corruption and invariant classes remain distinct.
  Output ordering is canonical.
- **LSP maps diagnostics to document versions.**
  Stale versions are dropped.
  Related information uses logical URIs.
  Recovery status can inform severity.
- **Hover shows type, effects, quantity, and borrow state.**
  Deep explanations are optional.
  Private information follows policy.
  Results name revision.
- **Rename explains unsafe conflicts.**
  Semantic occurrence index drives edits.
  Ambiguity and visibility are checked.
  Preview returns workspace edit only.
- **Inspector failures name unavailable phase or product.**
  Missing recovery support.
  Resource truncation.
  Unsupported schema.

### Cancellation, limits, and security

- **Each client request has cancellation token.**
  LSP cancels obsolete work.
  CLI signals propagate.
  Cleanup releases pins.
- **Response sizes are bounded.**
  Reference lists and traces paginate.
  Diagnostic counts respect limits.
  Large blobs require explicit emit paths.
- **Protocol inputs are validated.**
  Positions, paths, and options.
  LSP coordinate conversion checks bounds.
  Malformed requests do not reach semantics.
- **Client permissions remain external.**
  Compiler does not write workspace.
  Docs and tests request explicit execution.
  Runtime grants remain separate.
- **Shared service isolates sessions logically.**
  Private source products do not leak.
  Cache namespace follows policy.
  Inspection authorization is explicit.

### Determinism and reproducibility

- **Equivalent request objects yield equal semantic responses.**
  Transport order is irrelevant.
  Revision identity is content-based.
  Diagnostics reproduce.
- **LSP lists sort by stable semantic key.**
  Completion, symbols, and references.
  Client display may re-rank explicitly.
  Server base order is stable.
- **Formatter output is canonical.**
  Same source and configuration.
  Line endings follow explicit policy.
  No editor-specific grammar path.
- **Documentation ordering is canonical.**
  Modules and items sort by declared rule.
  Host filesystem order is absent.
  Links use logical paths.
- **CLI manifests capture explicit options.**
  Environment-derived defaults are normalized.
  Build reproduction is possible.
  Stage tools share the same API.

### Testing and observability

- **Contract tests compare `grand`, `grc`, and service calls.**
  Same inputs and roots.
  Same diagnostics and artifacts.
  Different adapters only render.
- **LSP tests simulate rapid edits and cancellation.**
  Stale diagnostics never publish.
  Hover and rename use correct revision.
  Memory remains bounded.
- **Formatter tests compare CLI and LSP formatting.**
  Exact edits and round trips.
  Malformed source recovery.
  Configuration parity.
- **Docs and reference tests use semantic indexes.**
  Visibility and reexports.
  Source links.
  Incremental private changes.
- **Inspection tests cover every exposed product.**
  Pagination and truncation.
  Stable JSON schemas.
  Authorization and redaction.

### Migration and completion criteria

- **Create compiler service façade.**
  Wrap current compiler entry points.
  Return structured outcomes.
  Keep CLI thin.
- **Route `grand` and direct `grc` through façade.**
  Compare real integration contract.
  Remove duplicate orchestration semantics.
  Preserve commands.
- **Route LSP to typed queries.**
  Remove alternate parser and checker.
  Add revision overlays.
  Implement cancellation.
- **Route formatter and docs to shared products.**
  Lossless source and interfaces.
  Remove duplicated source models.
  Add parity tests.
- **Complete when every tool asks the same database.**
  No semantic fork remains.
  Responses are revision-safe.
  Long-lived service stays bounded.

## 31. Testing, Differential Oracles, Fuzzing, and Performance

This section defines evidence for correctness, compatibility, and viability.
Testing spans source semantics, MIR, artifacts, verifier, VM, tooling, and bootstrap.
Differential oracles are scoped honestly.
Performance claims use reproducible counters and gates.

### Purpose and scope

- **Define layered test strategy.**
  Unit, integration, conformance, and end-to-end.
  Compile-pass and compile-fail.
  Artifact and runtime tests.
- **Define differential comparisons.**
  Rust versus self-host compiler.
  Interpreter versus VM where modeled.
  O0 versus optimized execution.
- **Define fuzzing and hostile corpora.**
  Lexer, parser, interfaces, caches, artifacts.
  Verifier and VM supervision.
  Deterministic seed replay.
- **Define determinism and incremental tests.**
  Cold versus warm builds.
  Random edit histories.
  Stage two versus stage three.
- **Define performance and resource gates.**
  Self-compilation time and memory.
  Query and optimizer counters.
  Regression thresholds.

### Goals and non-goals

- **Goal: localize defects to first differing phase.**
  Phase fingerprints and canonical snapshots.
  Preserve reproduction inputs.
  Avoid opaque final-output failures.
- **Goal: test negative behavior deeply.**
  Unsound programs reject.
  Corrupt artifacts fail closed.
  Limits trigger deterministically.
- **Goal: automate release evidence.**
  CI runs protected suites.
  Release candidates run full bootstrap.
  Reports are reproducible.
- **Non-goal: treat one oracle as full proof.**
  AST evaluator covers a documented subset.
  Rust compiler may share bugs.
  Verifier tests do not prove source semantics.
- **Non-goal: rely on anecdotal benchmarks.**
  Machines and inputs are recorded.
  Logical counters supplement time.
  Results need baselines.

### Public queries and interfaces

- **`run_compile_case`.**
  Compile one source fixture under exact options.
  Return structured products.
  Support expected acceptance and diagnostics.
- **`differential_compare`.**
  Compare two compiler or runtime products.
  Locate first phase mismatch.
  Emit reproduction bundle.
- **`fuzz_target`.**
  Accept bounded arbitrary bytes or structures.
  Return stable outcome class.
  Never crash or escape limits.
- **`benchmark_case`.**
  Record build world and logical counters.
  Run cold and warm modes.
  Produce canonical summary.
- **`parity_ledger`.**
  Map Rust test families to self-host coverage.
  Record named tests and status.
  Block unsupported completion claims.

### Primary data structures

- **`TestCaseManifest`.**
  Stores sources, options, expected products.
  Stores required features and limits.
  Uses logical paths.
- **`DifferentialReport`.**
  Stores product fingerprints and first difference.
  Stores stage or engine identities.
  Links reproduction artifacts.
- **`FuzzOutcome`.**
  Classifies accept, reject, resource, invariant.
  Stores bounded diagnostics.
  Stores seed and target generation.
- **`BenchmarkSample`.**
  Stores logical counts and optional timing.
  Stores memory peaks and cache state.
  Stores environment manifest.
- **`ParityLedgerEntry`.**
  Stores family, status, and linked tests.
  Records semantic surfaces covered.
  Is reviewed like source.

### Ownership and lifetime model

- **Test harness owns fixture inputs.**
  Compiler receives immutable worlds.
  Temporary outputs are sandboxed.
  Reproduction bundles persist selectively.
- **Differential runner owns paired products.**
  It may stream comparisons to limit memory.
  First difference persists.
  Full duplicates can release.
- **Fuzz workers own hostile inputs.**
  Processes are supervised.
  Crashes and OOMs are captured.
  Seeds remain small and reproducible.
- **Benchmark harness owns machine metadata.**
  Compiler products stay unchanged.
  Timing records are external.
  Logical counters come from service.
- **Parity ledger has repository lifetime.**
  Entries link stable test names.
  Status changes require evidence.
  Completed rows remain auditable.

### Algorithms and phase order

- **Run narrow unit tests first.**
  Arithmetic, arenas, codecs, and validators.
  Fast failures localize mechanisms.
  Deterministic results are required.
- **Run phase conformance suites.**
  Lex, scan, parse, resolve, and type.
  Compare canonical snapshots.
  Include rejection cases.
- **Run MIR and runtime differential suites.**
  O0 versus optimized.
  VM versus allowed oracle subset.
  Verify cleanup and effects.
- **Run hostile and fuzz suites.**
  Decoders and verifier under supervisor.
  Minimize failures.
  Store fixed regression seeds.
- **Run full integration and bootstrap gates.**
  Real `grc`–`grand`–`grvm` path.
  Stage chain and byte comparison.
  Performance budget evaluation.

### Semantic invariants

- **Expected failures are structured.**
  Tests assert stable codes and sites.
  Generic stderr matching is secondary.
  Failure class must match.
- **Differential comparisons use compatible domains.**
  Oracle subset is documented.
  Inputs must be compiler-accepted first where required.
  Unsupported semantics are excluded honestly.
- **Fuzz outcomes never depend on process crash.**
  Crashes are test failures.
  Resource kills are classified.
  Host escape is forbidden.
- **Performance tests never change compiler semantics.**
  Instrumentation is observational.
  Bench flags are explicit.
  Artifacts remain identical.
- **Parity status reflects named evidence.**
  Partial means partial.
  Covered requires acceptance and product parity.
  Self-host completion excludes unported rows.

### Cycles and fixed points

- **Random edit testing replays finite histories.**
  Each step compares clean and incremental.
  Histories may shrink on failure.
  Revision chains remain bounded.
- **Fuzz minimization loops are supervised.**
  Candidate shrinking terminates by size measure.
  Reproducible seed remains.
  Time limits apply.
- **Benchmark fixed points warm caches deliberately.**
  Warm state definition is explicit.
  Iterations stop after fixed count or stability.
  Results record method.
- **Bootstrap stage cycles are linearized.**
  Stage zero to one to two to three.
  No stage uses future output.
  Comparison occurs after completion.
- **Coverage feedback loops remain external.**
  They guide input generation only.
  Compiler semantics are unaffected.
  Corpus versions are recorded.

### Incremental dependencies and invalidation

- **Tests depend on exact compiler generations.**
  Changed diagnostics update relevant goldens.
  Unrelated fixtures remain reusable.
  CI selects impacted suites conservatively.
- **Parity ledger changes track implementation progress.**
  Linked tests must exist.
  Renamed tests update entries.
  Stale links fail CI.
- **Fuzz corpora depend on decoder schemas.**
  Old seeds remain useful when compatible.
  New feature generations add targets.
  Expected outcomes are versioned.
- **Benchmark baselines depend on machine class and build.**
  Semantic counters compare broadly.
  Wall times compare within policy.
  Cache state is explicit.
- **Reproduction bundles depend on complete input worlds.**
  Source, manifests, and artifacts.
  Host paths are normalized.
  Privacy policy controls publication.

### Caching and persistence

- **Test build caches are allowed but declared.**
  Clean suites periodically disable caches.
  Warm suites exercise reuse.
  Outputs must match.
- **Golden snapshots are canonical repository files.**
  Updates require deliberate blessing.
  Structured schemas are preferred.
  Diff noise is minimized.
- **Fuzz corpora persist minimized cases.**
  Name by content digest.
  Store expected outcome class.
  Avoid enormous random blobs.
- **Benchmark results persist as reports, not semantic caches.**
  Include environment and compiler identity.
  Trends are reviewed.
  Raw samples may archive externally.
- **Reproduction artifacts persist for failures.**
  Pre-oracle and raw MIR captures.
  Verified or hostile `.grbc` files.
  Exact commands accompany them.

### Diagnostics and explanations

- **Test failures show first differing product.**
  Phase and stable key.
  Expected and actual fingerprints.
  Reproduction command.
- **Compile-fail mismatches show structured diff.**
  Code, site, and payload.
  Rendered text diff follows.
  Blessing remains explicit.
- **Fuzz failures show seed and limit context.**
  Target generation and outcome.
  Minimized input path.
  Crash or invariant details.
- **Performance regressions show counter attribution.**
  Queries, passes, instructions, and memory.
  Compare baseline and current.
  Avoid time-only diagnosis.
- **Parity reports show uncovered families.**
  Partial surfaces and missing products.
  Linked test evidence.
  No optimistic percentage only.

### Cancellation, limits, and security

- **All hostile tests run under supervision.**
  Process memory and time limits.
  No ambient host capabilities.
  Crashes are contained.
- **Fuzz inputs have maximum size.**
  Decoder amplification remains the target.
  Corpus storage stays bounded.
  Shrinking respects limits.
- **Test diagnostics and artifacts are redacted by policy.**
  Private repository paths are removed.
  Source publication is controlled.
  Shared CI artifacts are reviewed.
- **Benchmark loops have total budgets.**
  Run counts and warmups are fixed.
  Cancellation stops safely.
  Partial reports are labeled.
- **Seed execution uses exact capabilities.**
  Compiler self-host runs declare required host access.
  Tests deny extras.
  Supervisor records grants.

### Determinism and reproducibility

- **Test manifests use canonical input ordering.**
  Sources and options sort.
  Expected products hash.
  Replays match across machines.
- **Random tests record seeds.**
  Generator versions are included.
  Shrunk case is preferred.
  Nondeterministic failures are defects.
- **Golden output ordering is stable.**
  Diagnostics and maps are canonical.
  Host paths and timestamps are absent.
  Diffs remain meaningful.
- **Benchmark logical counters are deterministic.**
  Query and instruction counts.
  Wall time is supplemental.
  Repeated samples expose noise.
- **Bootstrap test commands are fully pinned.**
  Stage binaries and manifests.
  Limits and optimization level.
  Checksums reproduce.

### Testing and observability

- **CI has layered required suites.**
  Fast unit and conformance on every change.
  Targeted self-host slices.
  Scheduled full bootstrap and fuzz.
- **Coverage spans semantic and failure surfaces.**
  Accept and reject cases.
  Recovery and resource outcomes.
  Corrupt input paths.
- **Trace tools are reusable.**
  Query graph, MIR snapshots, verifier windows.
  Hot-function and memory sampling.
  Opt-in deterministic output.
- **Performance dashboards track stable metrics.**
  Self-host time, memory, code size.
  Cache hit and invalidation fanout.
  Verifier throughput.
- **Architecture claims link to tests.**
  Acceptance criteria name suites.
  Remaining-work entries cite evidence.
  Documentation stays factual.

### Migration and completion criteria

- **Inventory current tests into families.**
  Build parity ledger.
  Name missing self-host coverage.
  Preserve existing fixtures.
- **Convert key goldens to structured products.**
  Diagnostics, interfaces, Core, MIR.
  Keep human snapshots where useful.
  Reduce text-only fragility.
- **Add automatic clean-versus-incremental differential tests.**
  Random edit histories.
  Cache corruption scenarios.
  Determinism checks.
- **Expand supervised fuzz targets.**
  Interfaces, caches, verifier, VM.
  Add coverage guidance.
  Store minimized failures.
- **Complete when releases ship reproducible evidence.**
  Full stage chain passes.
  Resource gates pass.
  Parity ledger has no hidden gaps.

## 32. Self-Hosting, Bootstrap Convergence, Migration, and Release

This section defines the path from Rust bootstrap compiler to canonical self-hosted releases.
Migration proceeds by authoritative subsystem slices.
Stage-two and stage-three byte identity is the convergence criterion.
Release artifacts include enough evidence for independent reproduction.

### Purpose and scope

- **Define stage-zero authority.**
  Rust compiler remains behavioral source initially.
  Its shortcuts are tracked.
  It is outside final bytecode chain.
- **Define self-host source organization.**
  Diagnostics, database, frontend, semantics, MIR, emission.
  Probes stay separate.
  Production modules avoid host effects.
- **Define migration by parity slices.**
  Lexing through artifact generation.
  Each slice gains differential tests.
  No flag-day rewrite is required.
- **Define bootstrap stage chain.**
  Stage zero builds one.
  Stage one builds two.
  Stage two builds three.
- **Define release and convergence evidence.**
  Stage two equals stage three byte-for-byte.
  Manifests and checksums ship.
  Independent rebuild commands are included.

### Goals and non-goals

- **Goal: self-hosted semantic authority.**
  Glorious compiler decides source meaning.
  Rust oracle becomes bootstrap-only.
  Tooling uses self-host service.
- **Goal: measurable convergence.**
  Byte identity, not output similarity.
  First differences localize by phase.
  Repeated builds reproduce.
- **Goal: viable resource use.**
  Cold self-compilation meets time and memory gate.
  Body-local storage is released.
  Query and cache design support scale.
- **Non-goal: hide incomplete parity.**
  Unported rows remain visible.
  Partial is not called complete.
  Release claims stay precise.
- **Non-goal: preserve bootstrap hacks indefinitely.**
  Injected preludes and name fallbacks are tracked.
  Final authority uses explicit manifests.
  Temporary adapters are removed.

### Public queries and interfaces

- **`bootstrap_manifest`.**
  Return canonical stage input world.
  Include sources, limits, target, and capabilities.
  Include compiler generations.
- **`build_stage`.**
  Run one compiler artifact on canonical inputs.
  Verify its output.
  Return next-stage artifact and products.
- **`compare_stages`.**
  Compare phase fingerprints and final bytes.
  Return first difference.
  Preserve reproduction bundle.
- **`parity_status`.**
  Return ledger by subsystem and test family.
  Include linked evidence.
  Block unsupported release labels.
- **`release_bundle`.**
  Assemble source, seed, manifests, and checksums.
  Include reproduction commands.
  Validate completeness.

### Primary data structures

- **`BootstrapStageIdentity`.**
  Stores stage number and compiler checksum.
  Stores verifier and VM generation.
  Is distinct from semantic build identity.
- **`BootstrapManifest`.**
  Stores canonical input world and policies.
  Stores expected product fingerprints.
  Serializes deterministically.
- **`ParityLedger`.**
  Stores family status and linked tests.
  Stores accepted and rejected surfaces.
  Is repository-reviewed.
- **`StageComparison`.**
  Stores interface, Core, MIR, fragment, artifact differences.
  Stores first differing stable key.
  Supports bounded reports.
- **`ReleaseBundleManifest`.**
  Lists every shipped file and checksum.
  Lists compatibility guarantees.
  Lists reproduction commands.

### Ownership and lifetime model

- **Bootstrap driver owns stage processes.**
  Each compiler runs supervised.
  Inputs are immutable bundles.
  Outputs are verified before reuse.
- **Stage artifacts have release-candidate lifetime.**
  Stage one may be temporary.
  Stage two and three comparison persists.
  Canonical seed is selected deliberately.
- **Parity ledger has source-repository lifetime.**
  Test evidence remains auditable.
  Status updates are explicit commits.
  Stale links fail validation.
- **Comparison sessions own duplicate products temporarily.**
  Stream or fingerprint large graphs.
  Persist first differences.
  Release full duplicates afterward.
- **Release bundle owns canonical manifests.**
  It contains no mutable compiler state.
  Consumers verify checksums.
  Distribution policy controls signatures.

### Algorithms and phase order

- **Freeze source semantics in stage zero.**
  Complete Rust compiler behavior and tests.
  Document deliberate G1 exclusions.
  Version interfaces and bytecode.
- **Port subsystems in dependency order.**
  Source, interfaces, bodies, semantics, MIR, emission.
  Add self-host probes at each stage.
  Update parity ledger.
- **Produce verified stage one.**
  Stage zero compiles canonical self-host source.
  Verifier accepts artifact.
  Supervisor runs compiler.
- **Produce stages two and three.**
  Each stage compiles identical manifest.
  Verify every output.
  Record phase fingerprints.
- **Compare and release.**
  Require byte identity.
  Run complete tests and resource gates.
  Package seed and reproduction evidence.

### Semantic invariants

- **Every stage consumes the same canonical source world.**
  Only compiler artifact changes.
  Options and limits remain identical.
  Manifest checksum proves it.
- **Every produced compiler is verified before execution.**
  Candidate bytes never become next stage directly.
  Verifier generation is recorded.
  Failures stop the chain.
- **Stage convergence requires exact artifact bytes.**
  Equivalent runtime output is insufficient.
  Debug and optional sections follow declared comparison policy.
  Canonical product is explicit.
- **Parity claims require named evidence.**
  No percentage without ledger rows.
  Acceptance and product parity both matter.
  Unsupported surfaces remain documented.
- **Bootstrap-only shortcuts are not hidden semantics.**
  Every shortcut has an issue or remaining-work entry.
  Final release removes or formalizes it.
  Name-based privilege is forbidden.

### Cycles and fixed points

- **Bootstrap chain is a finite linear sequence.**
  Stage one never depends on stage two.
  Stage comparison occurs afterward.
  Repeated cycles are release testing only.
- **Self-host compiler call graph may be recursive.**
  Normal instance and summary SCCs handle it.
  Resource gates bound execution.
  No special host recursion shortcut.
- **Parity migration loops are iterative project work.**
  Port, compare, fix, and expand.
  Ledger prevents losing coverage.
  Each iteration ends in named evidence.
- **Stage mismatch investigation descends phase hierarchy.**
  Interface, Core, MIR, fragments, bytes.
  Stable fingerprints avoid infinite search.
  First difference guides repair.
- **Release compatibility cycles are versioned.**
  Old seeds and artifacts have explicit support windows.
  No recursive implicit migration.
  Tools reject unsupported generations.

### Incremental dependencies and invalidation

- **Self-host source changes invalidate relevant compiler queries.**
  Ordinary incremental rules apply.
  Bootstrap manifest checksum changes.
  All stages rerun for convergence.
- **Rust stage-zero changes affect stage one production.**
  Later converged stages may still match.
  Provenance records the producer.
  Release review examines differences.
- **Verifier or VM changes affect bootstrap execution trust.**
  Compiler source products may remain equal.
  Stage chain must rerun under new runtime.
  Bundle manifest changes.
- **Parity ledger changes do not alter compiler artifacts.**
  They alter release readiness.
  CI validates linked tests.
  Documentation updates.
- **Performance policy changes affect gates and manifests.**
  Compiler bytes may remain equal.
  Release outcome may change.
  Measurements rerun.

### Caching and persistence

- **Bootstrap builds may use caches only with cold verification runs.**
  Final evidence includes cold build.
  Warm runs measure incrementality separately.
  Artifacts must match.
- **Stage products persist by content digest.**
  Interfaces, Core fingerprints, and artifacts.
  Comparison can reuse exact products.
  Provenance remains explicit.
- **Canonical seed artifact is checked into release or distributed immutably.**
  Checksum and signature accompany it.
  Reproduction commands regenerate it.
  Trust is documented.
- **Parity snapshots persist as test fixtures.**
  Rust and self-host canonical products.
  Updates require deliberate review.
  Old evidence remains in history.
- **Release bundles are immutable content-addressed products.**
  Every file is listed.
  Missing or extra files fail validation.
  Mirrors can be verified independently.

### Diagnostics and explanations

- **Stage build failures name producing compiler.**
  Stage identity and artifact checksum.
  Source diagnostic or runtime failure class.
  Exact reproduction command.
- **Stage mismatch reports name first phase.**
  Stable definition or instance key.
  Expected and actual fingerprints.
  Structured diff path.
- **Parity gaps name missing test family.**
  Current status and required evidence.
  Linked remaining-work item.
  No vague completion claim.
- **Resource gate failures show dominant counters.**
  Time, memory, queries, VM instructions.
  Hot function and phase.
  Baseline comparison.
- **Release validation failures name bundle entry.**
  Checksum, schema, or compatibility issue.
  Distribution step is halted.
  Manifest remains inspectable.

### Cancellation, limits, and security

- **Every stage runs under supervisor limits.**
  Compiler cannot consume unbounded memory or time.
  Exact filesystem capabilities are granted.
  Network remains absent.
- **Bootstrap source bundle size is bounded and hashed.**
  Inputs are verified before execution.
  Stage compilers cannot reopen arbitrary paths.
  Logical paths remain canonical.
- **Seed and release artifacts are independently verified.**
  Signatures do not replace bytecode verification.
  Unknown features reject.
  Frozen images are process-local.
- **Comparison tools bound retained products.**
  Stream large sections.
  Truncate human reports.
  Preserve compact reproduction records.
- **Supply-chain metadata is explicit.**
  Stage-zero toolchain and dependencies.
  Seed provenance and signatures.
  No claim of zero trust is made.

### Determinism and reproducibility

- **Bootstrap manifests are canonical.**
  Sources, packages, options, and limits.
  No timestamps or absolute paths.
  Checksums reproduce.
- **Stage compilers emit canonical boundary products.**
  Query order and cache state do not matter.
  Optimizer worklists are stable.
  Artifacts match across reruns.
- **Stage comparison uses exact byte policy.**
  Optional sections are explicitly included or stripped.
  The compared product is documented.
  No fuzzy equivalence.
- **Release commands pin tool versions.**
  Rust toolchain, verifier, VM, and package inputs.
  Environment variables are enumerated.
  Independent builders can reproduce.
- **Performance measurements record environment.**
  Logical counters remain primary.
  Wall time includes hardware manifest.
  Gate policy is stable.

### Testing and observability

- **Parity ledger validation runs in CI.**
  Linked tests must exist and pass.
  Covered rows require exact evidence.
  Regressions reopen status.
- **Stage chain tests run on release candidates.**
  Verify stages one through three.
  Compare byte identity.
  Preserve full manifests.
- **Subsystem probes compare canonical products.**
  Lexer, scanner, headers, bodies, resolution.
  Core, MIR, interfaces, and bytecode.
  VM and native where supported.
- **Performance gates compile the compiler cold.**
  Measure peak memory and total time.
  Record query and VM counters.
  Track regressions.
- **Release reproduction is tested by clean environment.**
  Fetch only declared inputs.
  Rebuild seed and stages.
  Compare all checksums.

### Migration and completion criteria

- **Maintain authoritative parity ledger.**
  Classify every Rust test family.
  Link self-host evidence.
  Review status changes.
- **Port one complete semantic slice at a time.**
  Include diagnostics and rejection behavior.
  Include canonical product comparison.
  Avoid interface-only stubs presented as done.
- **Remove bootstrap-only shortcuts continuously.**
  Replace injected preludes with real standard library.
  Replace name fallbacks with manifest identities.
  Track remaining exceptions.
- **Automate stage convergence and resource gates.**
  Make failures actionable.
  Preserve first differences.
  Run protected release workflow.
- **Complete when another party can reproduce the claim.**
  Self-hosted compiler is semantic authority.
  Stage two equals stage three.
  Source, seed, manifests, checksums, and commands ship.

---

# Closing Integration Rules

The thirty-two detailed documents must remain one architecture.
A local design may refine this compendium, but it must name every affected boundary.
New identity spaces, failure classes, persistent representations, or authorities require system-level review.
No document may silently introduce a fourth semantic IR.
No cache may become a truth source.
No tool may embed a second source compiler.
No optimization may weaken traps, ownership, cleanup, effects, or capabilities.
No bootstrap claim may skip exact stage comparison.

The next writing pass should expand each numbered section into its own normative file.
Each individual document should preserve the common fifteen-part structure.
Each document should include concrete Glorious-shaped types and algorithms.
Each document should link acceptance criteria to named tests.
Each document should identify migration steps from the current implementation.

This compendium is complete as a breadth-first layer when all thirty-two sections
agree on authority, identity, ownership, query boundaries, cache behavior,
failure taxonomy, determinism, and bootstrap assumptions.
