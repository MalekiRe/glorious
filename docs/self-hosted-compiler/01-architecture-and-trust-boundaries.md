# Self-Hosted Glorious Compiler — 01. Architecture and Trust Boundaries

Status: detailed snowflake design target. This document describes the intended
architecture of the best self-hosted Glorious compiler; it is not a statement
that every component described here is implemented today.

Parent design: [Snowflake Stage One: The Ideal Self-Hosted Glorious
Compiler](../self-hosted-compiler-snowflake-stage-one.md).

Related authoritative contracts:

- [language core specification](../../glorious-language-specification.md);
- [current compiler and VM architecture](../architecture.md);
- [self-hosted compiler architecture](../../GSC-2-glorious-incremental-self-hosted-compiler-spec.md);
- [G1 bytecode contract](../bytecode.md);
- [standard-library contract](../../glorious-standard-library-specification.md);
- [remaining implementation work](../remaining-work.md).

Where this document disagrees with the language or bytecode specifications,
those specifications win. Where it is more restrictive about component
ownership, authority, hermeticity, or trust, this document defines the target
self-hosted architecture.

The repository currently uses **Grandiose** in several existing documents and
component descriptions. This snowflake series uses **Glorious** as the language
name. Existing executable and artifact names remain `grand`, `grc`, `grvm`,
`.glorious`, and `.grbc`.

---

## 1. Purpose

The self-hosted compiler must be more than a program that translates source
text into bytecode. It must be the single semantic authority for the complete
Glorious toolchain while remaining small enough to audit, deterministic enough
to bootstrap, queryable enough to serve editors, and sufficiently isolated that
untrusted source, dependency metadata, cache records, and bytecode cannot acquire
ambient authority.

This document defines the system-level design needed to achieve that goal. It
answers five questions.

1. **Which component owns each responsibility?**
2. **Which component is trusted to make each class of decision?**
3. **What data may cross each boundary?**
4. **Which external capabilities may each component exercise?**
5. **How do failures cross boundaries without becoming confused with one
   another?**

Later documents will define the query engine, identities, caches, frontend,
static semantics, MIR, optimizer, verifier, VM, tooling, and bootstrap process
in greater algorithmic detail. This document constrains all of them.

The central rule is:

> **Every semantic fact has one authoritative producer, every boundary has a
> typed contract, and every component receives only the authority required to
> perform its role.**

## 2. Scope

This document covers:

- `grand`, the package and build orchestrator;
- the `grc` command and the self-hosted compiler library beneath it;
- the long-lived compiler database and request snapshots;
- frontend, static-semantic, Typed Core, MIR, optimizer, and emission services;
- dependency-interface and compiler-cache boundaries;
- the `.grbc` artifact boundary;
- the decoder and bytecode verifier;
- `grvm`, the supervised execution worker, and host-capability adapters;
- language-server, formatter, documentation, testing, and inspection clients;
- the Rust stage-zero compiler during bootstrap;
- the stage-one, stage-two, and stage-three self-hosting boundary;
- trust, corruption, cancellation, resource, and invariant failures.

This document does not define the internal algorithms of type inference, trait
solving, quantitative-use checking, borrow checking, optimization, bytecode
verification, or virtual-machine execution. It defines where those algorithms
live and what they are allowed to assume.

## 3. Goals

### 3.1 One semantic authority

The release compiler library must be the sole implementation of Glorious source
semantics used by normal builds, editor analysis, documentation, refactoring,
testing, and inspection.

The language server must not contain a second approximate type checker. The
formatter must not contain a second parser with a subtly different grammar. The
package tool must not duplicate visibility, trait, effect, or ownership rules.
The bytecode verifier must not become a second source compiler. The VM must not
recognize source names such as `if`, `match`, or `loop`.

Different clients may request different depths of analysis, but they must ask
the same compiler database.

### 3.2 Hermetic semantic execution

Given a complete immutable compilation request, the compiler core must not need
to inspect the current directory, read arbitrary paths, discover environment
variables, invoke external programs, consult the network, or infer package
layout from ambient state.

All such discovery belongs to orchestration. The compiler receives bytes,
logical identities, manifests, options, dependency interfaces, and explicit
limits. This makes builds reproducible, editor snapshots coherent, remote
execution possible, and self-hosting easier to reason about.

### 3.3 Least authority

Every component should receive the narrowest authority needed for its task.

- Frontend and semantic phases receive immutable source data and compiler-owned
  memory, not filesystem handles.
- The optimizer receives validated MIR, not host capabilities.
- The emitter may construct bytes but may not execute them.
- The verifier may inspect artifact bytes but may not perform source-level
  dependency discovery.
- The VM may issue only host requests explicitly authorized by the executable
  manifest and supervisor policy.
- Editor queries may inspect compiler facts but may not silently modify source.

### 3.4 Explicit trust boundaries

The architecture must distinguish:

- trust in **source semantics**;
- trust in **artifact safety**;
- trust in **execution isolation**;
- trust in **package resolution and input assembly**;
- trust in **cache integrity**;
- trust in the **bootstrap seed**.

These are different claims and must never be collapsed into the word
“verified.”

### 3.5 Deterministic externally visible behavior

For the same complete inputs, compiler build identity, target, and options, the
system must produce the same:

- exported interface;
- diagnostics and their ordering;
- optimization decisions where those decisions affect output;
- `.grbc` bytes;
- verification outcome;
- build manifest;
- stage-two and stage-three compiler artifact.

Internal allocation order need not be canonical. Boundary products must be.

### 3.6 Queryability and observability

Every major result should be obtainable as data through the compiler service.
The architecture must support questions about source, resolution, types,
effects, quantities, ownership, lifetimes, Core, MIR, optimization, emission,
caching, invalidation, and bytecode mapping without introducing phase-specific
standalone compilers.

### 3.7 Safe failure

Malformed source, malformed dependency interfaces, corrupt cache entries,
resource exhaustion, cancellation, compiler defects, invalid bytecode, denied
host capabilities, and runtime failures must remain distinguishable.

No boundary may convert an internal invariant failure into an ordinary user
error or treat an unverified artifact as executable merely because compilation
appeared to succeed.

### 3.8 Viable self-hosting

The design must be implementable in Glorious using explicit ownership,
quantitative use, typed arenas, algebraic effects, source-defined control, and
deterministic collections. It must not depend on runtime reflection, unsafe
memory, dynamic loading, hidden native callbacks, or a Rust-only semantic
shortcut.

## 4. Non-goals

Generation 1 does not require the compiler core to:

- fetch packages or perform version selection;
- access the network;
- load third-party compiler plugins;
- execute procedural macros;
- provide arbitrary FFI;
- trust remote cache entries;
- execute unverified bytecode;
- support threads or distributed query execution inside the Glorious compiler;
- provide a native backend as part of the trusted G1 path;
- make package-manager syntax part of the language;
- make the verifier repeat trait solving or source borrow inference;
- make `grand` understand source-level semantics;
- make the VM understand source-level control names;
- guarantee that every editor query completes after every keystroke;
- retain all semantic representations in memory indefinitely.

These exclusions are architectural simplifications, not excuses for imprecise
interfaces. A later feature must cross an explicit boundary rather than acquire
ambient authority.

## 5. Architectural laws

The following laws are normative for the target design.

### Law 1: Source semantics belong to the compiler

Only the compiler library decides whether source is well typed, effect-correct,
quantity-correct, borrow-correct, visible, coherent, or valid under Glorious
language rules.

`grand`, the LSP transport, the formatter command, the verifier, the VM, and the
supervisor may reject malformed inputs in their own domains, but they may not
invent alternate source semantics.

### Law 2: Runtime safety belongs to the verifier and VM boundary

The compiler proves source-level properties and emits runtime invariants. The
independent verifier checks the encoded artifact’s runtime contract before the
VM accepts it. The verifier does not trust the compiler merely because both are
part of the same release.

### Law 3: Orchestration owns the outside world

Package discovery, workspace expansion, lockfiles, dependency acquisition,
vendoring, environment interpretation, filesystem enumeration, output paths,
and user-facing command policy belong to `grand` or another explicit host
client.

The semantic compiler consumes an assembled request.

### Law 4: Inputs become immutable at the compiler boundary

A compilation request contains immutable source bytes and immutable dependency
blobs. It must not contain paths that the compiler later reopens. This prevents
one query from observing a file before an edit and another query from observing
it afterward within the same revision.

Logical paths may be retained for diagnostics, module identity, and privacy, but
they are labels over supplied bytes, not permission to read the host filesystem.

### Law 5: Caches are untrusted

A cache hit may save work; it may never establish semantic truth by itself.
Every persistent record carries a schema, build identity, complete key,
checksum, and validation contract. Invalid or incompatible records are ignored
or quarantined.

No cache corruption may change the meaning of a successful build.

### Law 6: Boundary products are canonical

Dependency interfaces, diagnostic streams, build manifests, compiler cache
records, emitted functions, and executable artifacts are serialized
canonically. Local arena IDs, hash-map iteration order, memory addresses, wall
clock time, process IDs, and random seeds may not leak into semantic
fingerprints or final output.

### Law 7: Authority is exact, not ambient

A component may perform an external operation only through an explicit
capability supplied at a boundary. Capability names and parameters are exact;
there is no implicit prefix grant or wildcard inheritance in the G1 runtime
model.

### Law 8: Failed phases publish no successful fact

Query execution, cache writes, artifact linking, and verification are
transactional at their publication boundaries. Cancellation, budget exhaustion,
corruption, or an internal invariant failure must not leave a partially
successful record visible as if it were complete.

### Law 9: Recovery is labeled

IDE recovery results must be explicitly marked provisional, incomplete, or
recovered. They may support hover, completion, or syntax-aware editing, but they
may not be silently reused as release-build evidence.

### Law 10: No hidden evaluator establishes correctness

A bootstrap evaluator or differential oracle may test a documented subset. Its
acceptance does not prove ownership, cleanup, private-field authority,
resumption legality, or bytecode safety unless it implements and checks those
properties explicitly.

## 6. System context

The target system has four major zones.

```text
+-----------------------------------------------------------------------+
| Host orchestration and clients                                        |
|                                                                       |
|  grand   grc CLI   grand-lsp   formatter   docs   tests   inspectors  |
+-------------------------------+---------------------------------------+
                                |
                                | typed immutable requests
                                v
+-----------------------------------------------------------------------+
| Self-hosted Glorious compiler service                                 |
|                                                                       |
|  CompilerDatabase                                                     |
|      source model -> interfaces -> bodies -> Typed Core                |
|      -> PlaceFlow/MIR -> optimization -> deterministic emission        |
|                                                                       |
|  query memoization, diagnostics, dependency graph, cache adapters      |
+-------------------------------+---------------------------------------+
                                |
                                | canonical .grbc bytes + build manifest
                                v
+-----------------------------------------------------------------------+
| Artifact trust boundary                                               |
|                                                                       |
|  defensive decoder -> independent verifier -> FrozenExecutionImage     |
+-------------------------------+---------------------------------------+
                                |
                                | verified image + exact runtime grants
                                v
+-----------------------------------------------------------------------+
| Supervised runtime                                                    |
|                                                                       |
|  supervisor -> isolated grvm worker -> capability host adapters        |
+-----------------------------------------------------------------------+
```

Persistent caches and dependency interfaces sit beside the compiler service,
not inside the trust boundary:

```text
untrusted source/dependency/cache blobs
                |
                v
        validated typed inputs
                |
                v
        CompilerDatabase
```

The Rust stage-zero compiler is a bootstrap producer outside the final
self-hosted semantic authority. It remains necessary until the Glorious
compiler is bootstrap-converged, but it must be compared against the self-hosted
compiler rather than silently supplying missing release semantics.

## 7. Component responsibilities

### 7.1 `grand`: package and build orchestrator

`grand` owns the translation from the user’s external environment into a
hermetic compiler request.

Its responsibilities include:

- reading `grandiose.toml` and lockfiles;
- identifying workspace members;
- resolving package selection;
- acquiring Git dependencies according to pinned revisions;
- enforcing locked and offline modes;
- vendoring dependencies;
- discovering source files according to the module/package contract;
- reading source bytes;
- constructing logical paths and source identities;
- loading dependency interface artifacts;
- selecting target, optimization, lint, and diagnostic options;
- constructing the exact runtime capability manifest;
- choosing output locations;
- invoking compiler requests;
- writing successful artifacts and interfaces atomically;
- invoking `grvm` only through the verified execution path;
- presenting orchestration failures to the user.

`grand` does **not** decide:

- how names resolve;
- which implementation satisfies a trait;
- whether an effect is handled;
- whether a value must move;
- whether a borrow is legal;
- whether source-defined control may fuse;
- whether bytecode satisfies the verifier contract.

`grand` may cache complete compiler outputs, but it treats the compiler’s build
manifest and hashes as authoritative. It must not infer semantic equivalence
from file timestamps alone.

### 7.2 `grc`: command boundary and compiler library

The `grc` executable should be a thin adapter around the same compiler service
used by `grand` and the language server.

The command adapter may:

- parse command-line options;
- read explicitly named input files when used without `grand`;
- construct a single-package compilation request;
- select inspection queries;
- render or serialize returned diagnostics;
- write requested outputs atomically.

The command adapter must not contain independent implementations of compiler
phases. A direct `grc` invocation and an equivalent `grand` request must reach
the same query implementations.

The core library beneath `grc` owns all source semantics, Typed Core, MIR,
optimization, and artifact emission.

### 7.3 `CompilerDatabase`: semantic service and revision owner

`CompilerDatabase` is the long-lived semantic engine. It owns:

- immutable source revisions;
- stable input identities;
- interners and canonical semantic keys;
- typed query definitions;
- in-memory memoized results;
- automatic dependency edges;
- structured diagnostics;
- persistent-cache adapters;
- cancellation state;
- resource accounting;
- query statistics and explanation data.

The database does not own package acquisition or arbitrary filesystem access.
It sees only request inputs.

One request observes one `DatabaseSnapshot`. A snapshot pins all direct inputs,
dependency interfaces, standard-library identity, target configuration, and
semantic options. New editor text creates a new revision rather than mutating an
old snapshot in place.

The database may share immutable interned values and validated results between
snapshots when fingerprints prove them equivalent. It must never combine facts
from incompatible snapshots merely because their local numeric IDs coincide.

### 7.4 Frontend services

Frontend services own:

- lossless lexing;
- delimiter pairing;
- structural declaration scanning;
- module and package source structure;
- header, trait, implementation, effect, and fixity collection;
- body parsing on demand;
- name resolution;
- source-facing recovery;
- source maps and semantic occurrence maps.

They receive immutable source bytes and compiler-owned arenas. They do not read
files, print diagnostics, or invoke host tools.

Frontend services may return recovered syntax for editor use. Every recovered
node or result must carry enough status for later phases to avoid treating it as
release-valid evidence.

### 7.5 Static-semantic services

Static-semantic services own:

- expected-type elaboration;
- semantic type construction and inference;
- trait and associated-item solving;
- const and quantity reasoning;
- effect-row checking;
- capture and environment analysis;
- region and borrow checking;
- private representation authority;
- construction of Typed Core.

These services may request other compiler facts through the typed query engine.
They may report structured diagnostics through an internal compiler mechanism,
but they do not render terminal output or perform host I/O.

### 7.6 Typed Core, PlaceFlow, MIR, and optimizer services

These services own the explicit operational meaning of accepted source.

They are responsible for:

- lowering accepted bodies into Typed Core;
- lowering Core into one ownership-and-control MIR;
- building and validating PlaceFlow facts;
- inserting exact cleanup, cancellation, resumption, and nonlocal-control edges;
- discovering generic instances;
- producing interprocedural summaries;
- running deterministic optimization under explicit budgets;
- explaining source-defined control specialization;
- validating transformed MIR.

They receive semantic values and typed identities, not source paths with read
permission. They may retain source mappings as immutable metadata.

### 7.7 Deterministic emitter and linker

The emitter owns the conversion from validated MIR to canonical artifact data.
It may:

- allocate physical registers;
- lay out blocks;
- select bytecode instructions;
- construct cleanup and continuation-capture maps;
- freeze canonical pools;
- serialize per-function fragments;
- link reachable functions and data;
- attach source maps and capability declarations;
- produce a build manifest and `.grbc` bytes.

The emitter is not authorized to execute the artifact or declare it verified.
Its output is untrusted until the independent decoder and verifier accept it.

### 7.8 Dependency-interface store

A dependency interface is a canonical compiler product containing the facts
needed by downstream compilation without exposing arbitrary implementation
state.

The interface store may contain:

- exported declarations and visibility;
- semantic signatures;
- traits and coherent implementation heads;
- associated-item contracts;
- effects and fixities;
- layout-relevant public facts where part of the ABI;
- generic bodies or canonical Core required for downstream specialization;
- source-independent diagnostic names;
- schema and compiler-generation identifiers;
- a content hash.

A dependency interface is an untrusted external blob when loaded. The compiler
must decode and validate it before importing facts. A downstream compiler must
not accept impossible local IDs, malformed semantic terms, incoherent producer
sets, or unknown required features merely because the file came from `grand`.

### 7.9 Persistent compiler cache

The cache adapter stores and retrieves content-addressed query products. It has
no authority to decide that a record is valid.

The compiler supplies complete keys and validators. The cache supplies bytes.
A cache miss, checksum mismatch, schema mismatch, failed validation, or missing
entry falls back to recomputation. Cache corruption is not a source error and
must not become a successful semantic result.

Remote caches, if added later, remain outside the compiler trust boundary and
obey the same contract.

### 7.10 Defensive decoder and bytecode verifier

The decoder and verifier own the artifact acceptance boundary.

The decoder treats every byte and length as hostile. It validates section
structure, ranges, counts, indices, feature declarations, and allocation limits
before constructing trusted internal views.

The verifier checks runtime invariants such as:

- function and signature compatibility;
- register types and ownership modes;
- move and copy legality;
- aggregate and projection legality;
- reference origin and lifetime summaries encoded for runtime use;
- block and control-flow consistency;
- cleanup plans;
- label, handler, and resumption identities;
- continuation capture plans;
- host-import declarations;
- required feature support.

The verifier does not repeat source name resolution, trait solving, or complete
source borrow inference. It checks the independently specified lowered
contract.

Successful verification produces a private `FrozenExecutionImage`. The public
mutable artifact representation is not the VM’s authority.

### 7.11 `grvm` worker

The VM worker executes only a verified frozen image.

Its responsibilities include:

- typed register-machine execution;
- checked arena-handle access;
- callable, handler, and continuation execution;
- exact move/copy behavior;
- destruction and cleanup according to verified plans;
- metered host-call requests;
- runtime diagnostics;
- cooperation with supervisor limits.

The worker does not parse Glorious source, resolve packages, infer effects, or
recognize standard-library control names.

### 7.12 Supervisor

The supervisor establishes the process and resource boundary around execution.
It owns:

- worker-process creation;
- memory and time limits;
- termination policy;
- exact host-capability grants;
- host-call routing;
- exit-status classification;
- separation between verifier failure and runtime failure.

The supervisor must not allow the worker to acquire ambient host access merely
because the compiler executable itself had filesystem or process permissions.

### 7.13 Host-capability adapters

A host adapter implements one finite, named capability contract such as:

- `process.args`;
- `fs.read`;
- `fs.write`;
- `diagnostic`.

Each request is checked against the exact grant set. Capability adapters are
part of the runtime trust boundary for the operations they expose. They must
validate paths, sizes, encodings, and policy constraints independently of
artifact claims.

A host adapter does not confer source-level effect correctness. The compiler
checks that source uses declared effects; the supervisor checks that execution
has runtime authority.

### 7.14 Language server and editor clients

`grand-lsp` should be a protocol and request-lifecycle adapter over the compiler
service.

It owns:

- LSP transport;
- document-version tracking;
- cancellation of obsolete requests;
- conversion between editor positions and compiler source coordinates;
- presentation of compiler facts as hover, completion, definition, reference,
  rename, symbol, code-action, and diagnostic responses.

It does not own alternate parsing, resolution, or type-checking rules.

Editor operations that modify text require an explicit user-visible edit or
code action. Merely asking the compiler a query cannot grant source-write
authority.

### 7.15 Formatter, documentation, tests, and inspectors

These clients consume the same compiler service at different semantic depths.

- The formatter uses the shared lossless source model and canonical formatting
  rules.
- Documentation uses resolved exported interfaces and source links.
- `grand test` uses compiler outcomes and verified runtime execution.
- Compile-fail tests compare structured diagnostics.
- Inspectors request tokens, interfaces, Core, MIR, control plans, cache traces,
  or source-to-PC maps.

No client may bypass compiler validation by constructing private semantic IDs or
artifact records directly.

### 7.16 Standard library

The standard library is ordinary trusted source input, not a bag of compiler
spelling hooks.

It defines conventional control, operators, data structures, effects, and
compiler-building helpers. Its source identity and interface fingerprint are
part of every relevant compiler and cache key.

The compiler may recognize a finite manifest-bound set of machine primitives and
host imports by trusted declaration identity. It must not grant primitive
authority to arbitrary declarations merely because their names match a standard
library spelling.

### 7.17 Rust stage-zero compiler

During migration, the Rust compiler is the behavioral bootstrap authority used
to produce the first self-hosted compiler artifacts and differential oracles.

It is not part of the final stage-two/stage-three bytecode bootstrap chain. Any
Rust-only implementation shortcut must be tracked explicitly and removed or
reimplemented before bootstrap convergence is claimed.

The stage-zero compiler and self-hosted compiler should consume the same
language, bytecode, interface, and diagnostic contracts wherever practical.

## 8. Trust model

The architecture uses several separate trust domains.

### 8.1 Source-semantic trust

The self-hosted compiler is trusted to implement the language specification. A
compiler defect may accept an invalid source program or reject a valid one.

The verifier reduces the consequences of some compiler defects by rejecting
artifacts that violate the lowered runtime contract. It cannot compensate for
every source-semantic error. For example, it does not reconstruct all trait,
privacy, effect, or borrow proofs from source.

### 8.2 Artifact-safety trust

The decoder and verifier are trusted to reject malformed or unsafe `.grbc`
artifacts before execution. The VM trusts only the verifier’s frozen products,
not raw artifact claims.

A verifier defect may allow an invalid artifact into the VM. This boundary must
therefore remain narrow, defensive, fuzzed, resource-bounded, and independent of
the source compiler’s mutable representations.

### 8.3 Runtime-isolation trust

The supervisor, worker boundary, host adapters, and operating system are trusted
to enforce time, memory, process, and capability limits.

The bytecode verifier does not by itself prevent an authorized program from
using excessive time or memory. Resource supervision is a separate obligation.

### 8.4 Orchestration trust

`grand` is trusted to assemble the requested package graph, source bytes,
lockfile identities, dependency interfaces, options, and capability manifest
faithfully.

The compiler reduces this trust by hashing all direct inputs and recording them
in the build manifest. Reproducible builds and locked mode allow users to audit
or repeat orchestration decisions.

### 8.5 Cache trust

Persistent and remote caches are untrusted. At most they are trusted to improve
performance when their returned records validate.

### 8.6 Bootstrap trust

Before convergence, users trust:

- the Rust stage-zero compiler;
- the checked-in seed artifact, if any;
- the source compiler and verifier used to regenerate later stages;
- the build environment.

After stage-two/stage-three byte identity, trust in accidental stage-one
nondeterminism is reduced, but the seed and verifier remain supply-chain
concerns. Release manifests and reproducible commands make this trust explicit;
they do not make it disappear.

## 9. Authority matrix

`Yes` means the component may exercise the authority as part of its normal
role. `Request` means it may ask another component through a typed boundary.
`No` means the authority must not be ambient.

| Component | Read arbitrary files | Network | Source semantics | Emit artifact | Verify artifact | Execute artifact | Host capabilities |
|---|---:|---:|---:|---:|---:|---:|---:|
| `grand` | Yes | Policy-controlled | No | Request | Request | Request | No |
| `grc` CLI adapter | Explicit inputs only | No | Request | Request | Optional request | No | No |
| compiler database | No | No | Yes | Request | No | No | No |
| frontend/static phases | No | No | Yes | No | No | No | No |
| MIR/optimizer | No | No | Lowered semantics | No | No | No | No |
| emitter/linker | No | No | No new source rules | Yes | No | No | No |
| dependency decoder | No | No | Imports validated facts | No | No | No | No |
| cache adapter | Cache namespace only | Optional transport | No | No | No | No | No |
| bytecode verifier | No | No | No | No | Yes | No | No |
| VM worker | No ambient access | No ambient access | No | No | Consumes proof | Yes | Request only |
| supervisor | Policy files only | Policy-controlled | No | No | Invokes | Controls | Grants exact set |
| LSP adapter | Open documents/config | No by default | Request | No | No | No | No |
| formatter/docs/tests | Explicit inputs | No by default | Request | Request where needed | Request | Request | No |

The matrix is a design test. Any implementation change that requires a `No`
cell to become `Yes` must introduce a new explicit boundary and justify it.

## 10. Boundary contracts

### 10.1 Orchestrator to compiler

The primary compiler boundary consumes a complete immutable
`CompilationRequest`.

The following is conceptual Glorious-shaped pseudocode, not frozen surface
syntax:

```glorious
struct CompilationRequest {
    build: CompilerBuildIdentity,
    revision: RevisionKey,
    mode: CompilationMode,
    package: PackageInput,
    sources: Vec<SourceInput>,
    dependencies: Vec<DependencyInput>,
    standard_library: StandardLibraryInput,
    target: TargetInput,
    options: CompilerOptions,
    runtime: CapabilityManifest,
    limits: CompilerLimits,
}
```

A request must contain or name by validated content hash every input that can
affect semantic output. It must not rely on the compiler later consulting
ambient state.

#### `CompilerBuildIdentity`

The build identity should include at least:

- compiler semantic version or source fingerprint;
- language generation;
- query schema generation;
- interface schema generation;
- bytecode generation;
- optimizer rule generation where not implied by compiler identity;
- standard primitive-manifest generation.

#### `CompilationMode`

Modes may include:

- `Check`;
- `Build`;
- `Test`;
- `Inspect`;
- `Ide`;
- `Bootstrap`.

Mode may determine which roots are demanded and whether recovered results are
permitted. It must not silently change language legality. Optimization level,
lints, target, and feature policy remain explicit options.

#### `SourceInput`

```glorious
struct SourceInput {
    file: StableFileKey,
    logical_path: String,
    package_path: ModulePath,
    bytes: Bytes,
    content_hash: Digest,
}
```

The compiler verifies that `content_hash` matches `bytes`. `logical_path` is
used for diagnostics and module semantics; it is not a read capability.

#### `DependencyInput`

```glorious
struct DependencyInput {
    package: PackageKey,
    version_identity: DependencyIdentity,
    interface: Bytes,
    interface_hash: Digest,
    optional_artifact: Option<VerifiedArtifactReference>,
}
```

The interface is decoded defensively. An artifact reference is relevant for
linking or execution only when its exact compatibility and verification status
are established.

#### `StandardLibraryInput`

The standard library is a distinguished dependency carrying:

- canonical source or interface bytes;
- trusted declaration-identity manifest;
- primitive and host-import manifest generation;
- content fingerprint.

Primitive authority derives from the manifest-bound declarations in this
input, not from global names.

#### `CapabilityManifest`

The runtime capability manifest lists exact capabilities that the emitted
program may request when supervised. It is both a compiler input and artifact
output.

The compiler checks host-import legality against the manifest. The supervisor
independently checks actual requests against its grant policy.

#### `CompilerLimits`

Limits are immutable request inputs and include structural ceilings for tokens,
declarations, type depth, solver work, monomorphizations, MIR entities,
optimizer work, artifact size, diagnostics, and retained memory where
measurable.

Changing a relevant limit may change whether compilation succeeds and therefore
belongs in the build manifest. A generous limit that is not reached need not
change semantic fingerprints if the query contract can prove independence.

### 10.2 Compiler to orchestrator

The compiler returns a `CompilationOutcome` rather than printing or writing
outputs directly.

```glorious
struct CompilationOutcome {
    status: CompilationStatus,
    diagnostics: Vec<CompilerDiagnostic>,
    interface: Option<CanonicalInterface>,
    artifact: Option<UnverifiedArtifact>,
    manifest: BuildManifest,
    inspections: Vec<InspectionResult>,
    statistics: QueryStatistics,
}
```

A successful `Build` outcome may contain unverified artifact bytes. The caller
must pass them through the verifier before labeling them executable or
installing them as verified output.

A convenience API may perform compile-plus-verify, but it must preserve the two
outcomes internally and identify whether failure occurred in compilation,
decoding, or verification.

The compiler does not choose host output paths. The caller writes returned bytes
atomically.

### 10.3 Compiler to persistent cache

The cache boundary is conceptually:

```text
lookup(CacheKey) -> Option<Bytes>
store(CacheKey, ValidatedCacheRecord) -> StoreOutcome
```

The compiler owns `CacheKey` construction and record validation. The adapter may
own local files, database handles, or remote transport, but it may not widen a
key or substitute a record from a merely similar build.

Cache writes happen only after the result is complete, deterministic,
serializable, and validated for its record type. Cancellation between temporary
write and publication must not expose a partial record.

### 10.4 Compiler to dependency interface

An interface is a canonical, versioned product. The producer signs it with a
content digest derived from its canonical bytes. The consumer verifies:

- schema compatibility;
- required feature compatibility;
- index and range validity;
- canonical ordering where required;
- semantic term well-formedness;
- declaration ownership;
- implementation-producer constraints;
- internal hashes.

An interface may omit private implementation details. It may not omit a fact
required to preserve downstream semantics and then rely on the consumer reading
the dependency source implicitly.

### 10.5 Compiler to bytecode verifier

The compiler supplies:

- raw `.grbc` bytes;
- expected bytecode generation;
- optional external resource limits;
- optional provenance metadata for diagnostics.

The verifier returns either:

- `VerifiedArtifact`, containing the private frozen image and verified metadata;
- or structured `ArtifactDiagnostic` values.

The verifier never mutates the compiler’s artifact representation in place.
Compiler and verifier should be able to run in separate processes using the same
binary contract.

### 10.6 Verifier to VM

The VM constructor accepts only a `FrozenExecutionImage` produced by successful
verification. It must not expose a public constructor from raw mutable artifact
tables.

The image contains checked indices, decoded operations, function ranges,
verified capture plans, host-import descriptors, cleanup products, and immutable
constant storage in a representation that does not require execution to branch
on untrusted offsets.

### 10.7 VM to host adapters

A runtime host request contains:

- exact capability identity;
- operation identity;
- typed or defensively encoded arguments;
- metering context;
- worker identity;
- optional source/PC provenance for diagnostics.

The supervisor checks the grant and routes the request. The adapter validates
arguments in its own domain. The return value is converted back through a finite
runtime ABI.

A denied capability produces a classified runtime error. It must not be
reported as a source type error or verifier failure.

### 10.8 Tool client to compiler service

A tool request identifies:

- database snapshot;
- query kind;
- typed key or source position;
- depth or recovery policy;
- cancellation token;
- resource budget;
- requested output encoding.

Tool clients may request semantic facts but may not construct private compiler
identities from guessed integers. Source positions are translated through
stable file keys and compiler-owned maps.

### 10.9 Bootstrap stage boundary

Each bootstrap stage receives the exact same canonical compiler source bundle,
standard library, target, capability manifest, and optimization configuration.
Each stage emits a compiler `.grbc` plus manifest.

Stage 2 and stage 3 are compared by canonical artifact bytes, not timestamps,
file names, or a subset of sections.

## 11. State ownership and lifetimes

The architecture uses nested ownership scopes.

### 11.1 Process lifetime: `CompilerService`

A long-lived compiler process may retain:

- immutable shared interners;
- schema tables;
- validated standard-library interfaces;
- in-memory cache indexes;
- persistent-cache handles;
- global statistics;
- multiple database revisions.

It must not retain an obsolete revision indefinitely merely because a query
once referenced it. Revision retention follows explicit client references and
memory policy.

### 11.2 Revision lifetime: `DatabaseSnapshot`

A snapshot owns or references:

- direct source inputs;
- package graph inputs;
- dependency interfaces;
- target and options;
- capability manifest;
- input fingerprints;
- memoized query results valid for that revision.

The snapshot is immutable after publication. Incremental change creates a new
snapshot that may reuse validated results.

### 11.3 Package lifetime: `CompilerSession`

A package session retains cross-body semantic state such as:

- declaration headers;
- module and namespace indexes;
- typed interfaces;
- interned semantic terms;
- trait and implementation indexes;
- package diagnostics;
- reachable-instance worklists.

The session does not own a permanent whole-program body AST.

### 11.4 Body lifetime: `BodyContext`

A body context owns:

- transient parsed syntax;
- lexical scopes;
- local inference variables;
- body-local resolution;
- Typed Core scratch;
- body diagnostics and explanation builders;
- temporary solver and traversal storage.

After successful lowering, transient syntax and Core scratch are released unless
an active query explicitly retains a compact result.

### 11.5 Lowering lifetime: `LoweringContext`

The lowering context owns body-local:

- MIR construction state;
- places and move paths;
- loans;
- control and cleanup sites;
- PlaceFlow facts;
- source mappings;
- validation scratch.

Published MIR is immutable. Optimizer transformations occur through a checked
editor that creates a new validated generation or transactionally updates a
private copy before publication.

### 11.6 Emission lifetime: `EmissionContext`

An emission context owns:

- function-local register allocation;
- block layout;
- temporary relocation data;
- canonical-pool builders;
- serializer scratch;
- artifact manifest construction.

It is discarded after canonical bytes and reusable emitted fragments are
published.

### 11.7 Request lifetime: cancellation and budgets

Every top-level request owns a cancellation token and budget account. Nested
queries inherit or subdivide that account. A cancelled request may reuse
already-complete immutable facts, but it must not publish incomplete new facts.

### 11.8 Execution lifetime

A verified image may outlive one VM run and be reused for multiple supervised
runs if its immutable identity and capability policy remain compatible.

Each run owns:

- worker state;
- frames and registers;
- runtime arenas;
- host-request accounting;
- time and memory meters;
- runtime diagnostics.

Runtime state never flows back into compiler semantic caches.

## 12. End-to-end flows

### 12.1 Cold package build

1. `grand` resolves the locked package graph.
2. `grand` reads all direct source bytes and validated dependency-interface
   candidates.
3. `grand` constructs a `CompilationRequest` with exact options and limits.
4. The compiler creates a snapshot and fingerprints direct inputs.
5. Frontend queries build the source model and package interfaces.
6. Demanded bodies are parsed, resolved, elaborated, lowered, and validated.
7. Reachable generic instances are discovered.
8. MIR is optimized under deterministic budgets.
9. The emitter constructs canonical `.grbc` bytes and a build manifest.
10. The decoder and verifier independently validate the artifact.
11. `grand` atomically writes the interface, artifact, and manifest.
12. Any cache records are published only after their individual validation
    contracts succeed.

A compiler success followed by verifier failure is a compiler/toolchain defect
or artifact-boundary failure, not an ordinary successful build.

### 12.2 Warm incremental build

1. `grand` supplies a new immutable source revision.
2. The compiler compares direct input fingerprints.
3. Unchanged query results are considered for reuse through recorded
   dependencies.
4. Changed facts invalidate only dependent results.
5. Persistent records may be loaded and validated.
6. Recomputed and reused facts participate identically in final emission.
7. The warm output must match a cold build of the same complete inputs byte for
   byte.

The compiler can explain every recomputed root through an invalidation chain.

### 12.3 IDE edit and query

1. The editor sends a new document version to `grand-lsp`.
2. The LSP adapter constructs a new source snapshot without mutating the prior
   one.
3. Obsolete requests are cancelled.
4. The requested query computes only the necessary frontend or semantic depth.
5. Broken source may produce explicitly recovered results.
6. Compiler diagnostics and facts are converted to LSP responses.
7. No recovered result is promoted into a release-build cache record unless it
   satisfies that record’s complete contract.

### 12.4 Run command

1. `grand run` performs or reuses a compile-and-verify result.
2. `grand` constructs the exact runtime grant set from package policy and user
   options.
3. The supervisor creates a worker with time and memory limits.
4. The worker receives the verified image, arguments, and no ambient host
   handles.
5. Host requests are routed through exact capability adapters.
6. Exit is classified as normal completion, program abort, denied capability,
   resource termination, runtime fault, or supervisor failure.

### 12.5 Dependency build

1. A dependency is compiled to a canonical interface and optionally a verified
   artifact.
2. The dependent package receives the interface bytes and identity through its
   request.
3. Private implementation changes that do not alter the interface need not
   invalidate the dependent package.
4. Generic or layout-sensitive facts included in the interface create explicit
   downstream dependencies.
5. No dependent phase reopens the dependency source unless source was supplied
   explicitly for a source-based workflow.

### 12.6 Self-host bootstrap

1. Stage 0 compiles the canonical Glorious compiler source to stage 1.
2. The verifier accepts stage 1 before execution.
3. Stage 1 compiles the identical source and inputs to stage 2.
4. The verifier accepts stage 2.
5. Stage 2 compiles the identical source and inputs to stage 3.
6. The verifier accepts stage 3.
7. Stage 2 and stage 3 canonical artifact bytes are compared.
8. Release succeeds only when required parity, resource, determinism, and
   compatibility gates pass.

## 13. Semantic authority by layer

The architecture intentionally divides proof obligations.

### 13.1 Compiler obligations

The compiler establishes:

- lexical and module correctness;
- name resolution and visibility;
- type and const correctness;
- trait coherence and selected evidence;
- effect-row correctness;
- quantitative-use obligations;
- borrow, lifetime, capture, and private-field legality;
- source-defined control meaning;
- cleanup insertion;
- valid Typed Core and MIR;
- deterministic optimization preserving those semantics.

### 13.2 Verifier obligations

The verifier establishes that the encoded artifact obeys the G1 execution
contract independently of compiler memory:

- all decoded ranges and indices are safe;
- runtime types and ownership modes agree;
- control flow is structurally valid;
- moves, copies, references, cleanup, labels, handlers, and resumptions satisfy
  encoded invariants;
- host imports belong to the finite supported boundary;
- required features are understood;
- verifier resource limits are respected.

### 13.3 VM obligations

The VM faithfully executes the verified image:

- `MOVE` empties its source;
- `COPY` respects verified duplicability;
- references use checked handles and projections;
- call, handler, continuation, cleanup, and destruction behavior matches the
  bytecode contract;
- runtime checks defend against corrupted dynamic state;
- host requests use the declared ABI.

### 13.4 Supervisor obligations

The supervisor establishes external containment:

- resource ceilings;
- process isolation;
- exact host authority;
- worker termination;
- trustworthy classification of runtime outcomes.

No layer should silently assume another has proved an obligation outside that
layer’s contract.

## 14. Failure taxonomy and ownership

### 14.1 Orchestration failure

Examples:

- missing manifest;
- lockfile conflict;
- dependency unavailable in online mode;
- offline dependency not vendored;
- output path unwritable;
- malformed workspace configuration.

Owner: `grand`.

These failures occur before or around semantic compilation and use orchestration
diagnostics, not source diagnostic codes.

### 14.2 Source diagnostic

Examples:

- unresolved name;
- type mismatch;
- unsatisfied trait goal;
- unhandled effect;
- invalid use interval;
- illegal move or borrow;
- private field access;
- invalid cancellation or resumption.

Owner: compiler semantic phase.

These are deterministic structured diagnostics tied to source identities.

### 14.3 Recovery result

A recovery result is not necessarily a failure. It is an incomplete semantic
product produced for editor continuity after malformed or unfinished source.

Owner: compiler query, labeled with completeness status.

Release compilation rejects any required fact that remains recovered or
provisional.

### 14.4 Resource-limit diagnostic

Examples:

- too many tokens;
- solver budget exhausted;
- monomorphization limit reached;
- MIR block limit reached;
- optimizer work limit reached;
- artifact size limit reached.

Owner: the phase enforcing the structural limit, normalized through the compiler
diagnostic boundary.

Resource limits are not internal invariant failures and must not cause unbounded
allocation before reporting.

### 14.5 Cancellation

Cancellation means the caller no longer needs the result. It is neither a source
error nor a compiler defect.

Owner: request lifecycle.

Cancelled work publishes no incomplete success and ordinarily produces no user
diagnostic unless the caller explicitly requests cancellation reporting.

### 14.6 Cache corruption or incompatibility

Examples:

- checksum mismatch;
- unknown cache schema;
- malformed cached MIR;
- record key mismatch;
- invalid canonical ordering.

Owner: cache boundary.

Default behavior is to ignore/quarantine and recompute. Strict diagnostic modes
may report cache corruption separately. The source program is not blamed.

### 14.7 Internal compiler invariant failure

Examples:

- impossible typed ID;
- malformed compiler-produced Core;
- PlaceFlow inconsistency;
- checked MIR editor violation;
- nondeterministic canonical serialization;
- compile-success artifact rejected by the paired verifier.

Owner: compiler/toolchain.

An invariant failure must be clearly classified, include reproducible query and
input identities where safe, and terminate the affected compilation. It must not
be converted to a plausible user-facing type error.

### 14.8 Artifact decoding or verification failure

Examples:

- malformed section;
- out-of-range register;
- ownership-state mismatch;
- invalid cleanup map;
- incompatible required feature;
- illegal resumption capture.

Owner: decoder/verifier.

For user-supplied artifacts, this is an artifact diagnostic. For a fresh artifact
from the same compiler invocation, it is also a toolchain invariant failure.

### 14.9 Runtime failure

Examples:

- explicit abort;
- checked dynamic trap;
- denied host capability;
- invalid host response;
- time limit;
- memory limit;
- supervisor termination.

Owner: VM, host adapter, or supervisor according to category.

Runtime failures preserve function/PC and source provenance when available but
are not retroactively presented as compile-time diagnostics.

## 15. Security properties

### 15.1 Hostile-source containment

All source-driven allocation and recursion are budgeted. Lexing, parsing,
resolution, solving, monomorphization, MIR construction, optimization, and
serialization must fail structurally before integer overflow, stack exhaustion,
or uncontrolled memory growth.

### 15.2 Hostile-interface containment

Dependency interfaces are decoded with the same defensive posture as bytecode:
checked lengths, checked indices, required-feature validation, semantic
well-formedness, and bounded allocation.

An interface is not trusted merely because its package was previously compiled
on the same machine.

### 15.3 Cache-poisoning resistance

A cache record is bound to:

- complete semantic key;
- compiler build identity;
- schema generation;
- target and relevant options;
- direct dependency fingerprints;
- content checksum.

Loaded semantic IR is structurally validated. High-risk records such as verified
artifacts retain or re-establish verifier evidence according to their cache
contract.

### 15.4 No time-of-check/time-of-use source races

The compiler receives source bytes, not reopenable paths. The artifact is
verified from immutable bytes, and the VM executes the corresponding frozen
image. Output installation uses atomic replacement.

### 15.5 Exact runtime capabilities

The artifact declares required host imports. The supervisor supplies an exact
grant set. The host adapter checks each operation. These three views must agree,
but each is independently validated.

No source effect declaration itself grants host access.

### 15.6 No execution before verification

Normal release and `grand run` paths have no API that turns raw compiler output
directly into a VM worker. Development-only constructors, if any, must be
explicitly named unsafe-for-production, unavailable in release packaging, and
covered by tests preventing accidental use.

### 15.7 Finite primitive authority

Machine primitives and host imports are bound by trusted declaration identity in
the canonical standard-library manifest. User code cannot acquire primitive
authority through name collision, re-export, or source positioning.

### 15.8 Private semantic data

Compiler-private arenas and IDs are not serialized accidentally into public
interfaces. Source paths and diagnostic data are normalized to avoid exposing
host-private absolute paths unless explicitly requested.

## 16. Determinism at component boundaries

Each boundary has a deterministic contract.

### 16.1 Orchestration

Locked builds sort package and source inputs by canonical package/module
identity before request construction. Logical path normalization is target
independent unless the language specification says otherwise.

### 16.2 Compiler

Diagnostics, exported definitions, trait heads, instances, pass reports, and
inspection results use stable ordering. Parallel or incremental execution may
change completion order but not publication order.

### 16.3 Cache

Cache keys are canonical values, not formatted debug strings. Cache presence,
absence, or eviction cannot alter final artifact bytes.

### 16.4 Emitter

Strings, constants, signatures, type records, operand packs, function records,
sections, and relocations are frozen through deterministic ordering and remap
tables.

### 16.5 Verifier

Verification diagnostics use deterministic traversal and ordering. Equivalent
artifacts produce equivalent verified images or explicitly canonicalized runtime
products.

### 16.6 Bootstrap

The stage comparison includes every required artifact byte. Diagnostic text,
temporary paths, cache warmth, and worker scheduling do not enter the compiler
artifact.

## 17. Concurrency and process topology

The semantic model must not depend on whether components run in one process or
several.

Supported deployment shapes may include:

1. one-shot `grc` with an in-process compiler database;
2. `grand` invoking an in-process compiler library;
3. `grand-lsp` hosting a long-lived compiler service;
4. a local compiler daemon shared by tools;
5. a sandboxed compiler worker receiving serialized immutable requests;
6. remote build execution using the same request and outcome contracts.

Generation 1 may implement only the first three. The contracts should not embed
raw pointers, process-local IDs, or ambient callbacks that make later isolation
impossible.

If queries execute concurrently, they operate on immutable snapshots. Shared
interners and caches use deterministic publication. Racing computations of the
same query may deduplicate or one result may win publication, but both must be
semantically identical. Cancellation of one client must not invalidate a
complete fact still used by another client.

## 18. Compiler implementation guidance in Glorious

The architecture should use Glorious features where they clarify ownership and
control.

### 18.1 Context ownership

Use explicit private context structures for hot mutable state:

- `CompilerDatabase`;
- `CompilerSession`;
- `BodyContext`;
- `LoweringContext`;
- `EmissionContext`.

Their private fields enforce which module may mutate or finalize each phase.
Avoid a global mutable compiler singleton.

### 18.2 Effects for genuine nonlocal concerns

Appropriate internal effects may include:

- `Query` for requesting another typed compiler fact;
- `Report` for recoverable structured diagnostics;
- `Cancel` for request cancellation;
- typed phase failure;
- bounded inspection tracing.

Ordinary arena allocation, table mutation, and local inference state should
remain explicit context operations rather than being hidden behind broad effects.

### 18.3 Quantitative guards

Use affine or linear guards for transactions such as:

- parser checkpoints;
- arena rollback;
- cache-record publication;
- artifact output publication;
- diagnostic context frames;
- temporary map overrides.

A guard must be committed exactly once or restore state during legal cleanup.
This makes boundary publication behavior part of ownership rather than
convention.

### 18.4 Branded identities

Use fresh brands for revision, package, body, arena, and query-local identity
spaces where mixing IDs would be unsound. Persistent stable keys remain explicit
serialized identities; local brands prevent accidental cross-context use.

### 18.5 Source-defined control

Compiler traversal, worklist, rollback, and fixed-point helpers may use
source-defined control abstractions, but production optimization must prove that
hot paths fuse to direct loops, branches, and label transfers. The compiler
should be able to inspect its own control plans.

### 18.6 No hidden host authority

The self-hosted compiler application may receive process arguments, file reads,
file writes, and diagnostics at its outermost host boundary. Semantic modules
must not declare those capabilities merely for convenience.

## 19. Versioning and compatibility identities

The system has several independent version axes.

### 19.1 Language generation

Defines source and semantic compatibility.

### 19.2 Interface schema

Defines dependency-interface encoding. A compiler may support multiple previous
schemas through explicit decoders, but imported facts are normalized into the
current internal model.

### 19.3 Cache schema

Defines persistent query-record encoding. Cache schemas may be discarded more
aggressively than public interfaces because cache misses are safe.

### 19.4 Bytecode generation

Defines `.grbc` required features and runtime compatibility. Unknown required
features fail closed; unknown noncritical sections may be skipped according to
the bytecode specification.

### 19.5 Standard-library identity

Defines source-level control, traits, effects, primitive leaves, host-import
leaves, and compiler-building helpers. It participates in semantic and cache
keys independently of the compiler executable version.

### 19.6 Target identity

Includes data layout, supported machine primitives, runtime ABI generation, and
other target-dependent semantics.

### 19.7 Build manifest

Every published interface and artifact records the complete set of identities
required to explain and reproduce it. Human package version numbers alone are
not sufficient cache or compatibility keys.

## 20. Observability at boundaries

The compiler should expose structured boundary events without making tracing
part of semantics.

Useful events include:

- request accepted with input fingerprints;
- snapshot created or reused;
- query demanded, reused, recomputed, cancelled, or budgeted out;
- cache lookup, validation, miss, corruption, and publication;
- interface import and compatibility result;
- optimizer pass and control-fusion outcome;
- function-fragment reuse;
- artifact linked and canonical hash computed;
- verifier accepted or rejected;
- worker started, capability requested, or limit enforced;
- bootstrap stage produced and compared.

Tracing must avoid leaking source text, private paths, or secrets by default.
Stable keys and hashes should be sufficient for most diagnostics. Verbose modes
may include source excerpts under explicit user control.

## 21. Testing the architecture

### 21.1 Boundary contract tests

For every boundary, tests should serialize valid and invalid values, exercise
unknown versions, malformed lengths, missing fields, and incompatible required
features.

### 21.2 Hermeticity tests

Run the semantic compiler with:

- no current-directory assumptions;
- an empty environment;
- inaccessible source paths after bytes are supplied;
- randomized host temporary paths;
- offline mode;
- filesystem access denied to semantic phases.

Equivalent requests must still produce equivalent outcomes.

### 21.3 Authority tests

Static or architectural tests should fail if frontend, semantic, MIR, optimizer,
or emitter modules acquire process, filesystem, network, or host-diagnostic
capabilities.

Runtime tests should prove that undeclared or ungranted host imports fail closed.

### 21.4 Cold/warm equivalence

For representative packages, compare:

- cold build;
- in-memory warm build;
- persistent-cache warm build;
- selectively corrupted-cache build;
- cache-evicted build.

All successful artifact bytes and diagnostics must agree.

### 21.5 Compiler/verifier separation

Feed the verifier:

- valid compiler artifacts;
- mutated compiler artifacts;
- hostile arbitrary artifacts;
- artifacts with inconsistent cleanup, ownership, handler, or resumption data.

A fresh compiler artifact rejected by the paired verifier is a failing toolchain
test.

### 21.6 Client consistency

The same source snapshot queried through `grc`, `grand`, and `grand-lsp` must
produce the same semantic facts and diagnostic codes at equivalent analysis
depth.

### 21.7 Failure-classification tests

Tests must distinguish source diagnostics, orchestration errors, cancellation,
resource limits, cache corruption, internal invariants, verification failures,
runtime failures, and supervisor termination.

### 21.8 Bootstrap tests

Bootstrap tests record:

- exact input manifest;
- stage hashes;
- verifier outcomes;
- cold resource usage;
- stage-two/stage-three byte identity;
- absence of untracked Rust-only semantic fallbacks.

## 22. Migration from the current repository

Migration should preserve working behavior while making boundaries explicit.
The order matters.

### Step 1: Freeze the request and outcome vocabulary

Define typed `CompilationRequest`, `CompilationOutcome`, `BuildManifest`, and
failure classes around existing compiler entry points. Initially, adapters may
populate them from current command-line behavior.

### Step 2: Thin the command boundaries

Move semantic work out of `grc` and phase-specific applications into the
compiler library. Keep command parsing and rendering at the edge.

### Step 3: Remove ambient host capabilities from semantic modules

Inventory process arguments, file reads/writes, and host diagnostics in
frontend, self-host, optimizer, and emission modules. Route them through outer
adapters or test probes.

### Step 4: Establish immutable source snapshots

Make source bytes, segments, logical paths, and dependency inputs explicit.
Ensure a body query cannot reopen a source path.

### Step 5: Establish the compiler database boundary

Place existing phase operations behind typed query entry points without first
rewriting every algorithm. Record dependencies and ownership at the boundary,
then incrementally improve granularity.

### Step 6: Canonicalize dependency interfaces

Separate public semantic facts from private compiler arenas. Add defensive
interface decoding and hashes. Teach `grand` to supply interfaces explicitly.

### Step 7: Put caches behind validation adapters

Move existing MIR, LLVM, bytecode, and self-host caches under complete keys,
schemas, checksums, and per-record validators. Preserve cold-build fallback.

### Step 8: Formalize compile-to-verify handoff

Make raw artifact bytes cross an explicit verifier API. Prevent the normal VM
constructor from accepting unchecked mutable artifacts.

### Step 9: Unify tooling clients

Route LSP, formatter, documentation, compile-fail tests, and inspection commands
through compiler-service queries. Remove duplicated semantic approximations.

### Step 10: Complete the self-hosted authority

Port remaining Rust-only semantic behavior, remove bootstrap-only shortcuts,
produce verified stages, and enforce stage-two/stage-three identity.

Migration changes should be small enough that each step retains differential
coverage against the current compiler.

## 23. Rejected architectural alternatives

### 23.1 A monolithic compiler executable with ambient filesystem access

Rejected because it makes editor revisions incoherent, remote execution hard,
caching opaque, and semantic phases difficult to test hermetically.

### 23.2 A second lightweight compiler inside the LSP

Rejected because semantic drift is inevitable. Recovery belongs in the same
compiler, labeled by completeness.

### 23.3 Treating the bytecode verifier as a second source checker

Rejected because it would duplicate traits, effects, quantities, privacy, and
borrow inference while enlarging the runtime trust boundary. The verifier checks
the lowered runtime contract.

### 23.4 Trusting compiler cache records

Rejected because cache corruption or poisoning would become a semantic attack.
Caches remain optional validated accelerators.

### 23.5 Letting the compiler fetch its own dependencies

Rejected because network and package policy would become ambient semantic
inputs. `grand` supplies a resolved immutable graph.

### 23.6 Letting the VM recognize source control names

Rejected because it violates source-defined control and couples runtime safety
to standard-library spelling.

### 23.7 Executing compiler output before independent verification

Rejected because it collapses compiler and runtime trust into one unchecked
path.

### 23.8 General compiler plugins in G1

Rejected because arbitrary in-process plugins would inherit compiler authority,
break hermeticity, complicate bootstrap determinism, and introduce an undefined
semantic extension boundary.

### 23.9 Persisting one mutable whole-program AST

Rejected as the default because it raises memory use, complicates revision
isolation, and duplicates the intended body-at-a-time architecture. Specific
query products may retain compact syntax when measured and justified.

## 24. Open questions

The following questions remain for later documents or measured prototypes.

1. Should the long-lived compiler service be an in-process library, a local
   daemon, or both in the first self-hosted release?
2. Which query products are worth persisting before the typed query engine is
   fully granular?
3. Should dependency interfaces include canonical Typed Core for every generic
   body or a narrower specialization representation?
4. Which verified products may be safely cached without rerunning full
   verification, and what evidence must accompany them?
5. Should remote cache records be signed in addition to content-addressed and
   validated?
6. How are absolute host paths redacted while preserving useful diagnostics and
   reproducibility?
7. Where should a future native backend sit: behind the same emitter boundary or
   in a separately supervised tool?
8. How should compiler-service memory eviction interact with editor latency and
   bootstrap peak-memory goals?
9. Which parts of the Rust stage-zero compiler remain in the trusted release
   base after the first bootstrap-converged seed exists?
10. Should the verifier run in-process for builds, in a separate process, or
    support both through one serialized API?

None of these questions changes the central authority split defined here.

## 25. Acceptance criteria

This architecture is considered implemented when all of the following are true.

- [ ] `grand`, direct `grc`, and `grand-lsp` use the same compiler semantic
      entry points.
- [ ] Semantic phases operate entirely on immutable supplied inputs and
      compiler-owned memory.
- [ ] Frontend, type, effect, quantity, borrow, MIR, optimizer, and emitter
      modules have no ambient filesystem, network, process, or host-diagnostic
      capabilities.
- [ ] A compilation request records every input that can affect its result.
- [ ] A compiler outcome returns diagnostics and bytes as data rather than
      requiring phase-local host output.
- [ ] Dependency interfaces are canonical, versioned, hashed, and defensively
      decoded.
- [ ] Persistent caches are optional, content-addressed, schema-versioned,
      checksummed, and validated before reuse.
- [ ] Warm and cold builds of identical inputs produce byte-identical artifacts.
- [ ] The normal VM path accepts only an independently verified frozen image.
- [ ] Runtime capabilities are exact and independently enforced by the
      supervisor and host adapters.
- [ ] Source, orchestration, recovery, resource, cancellation, corruption,
      invariant, verification, and runtime failures remain distinct.
- [ ] Tooling can query semantic facts without duplicating compiler logic.
- [ ] The self-hosted compiler can compile one body at a time without retaining
      a mandatory whole-program body AST.
- [ ] Stage-two and stage-three compiler artifacts are byte-identical under the
      canonical bootstrap manifest.
- [ ] The release documentation states clearly what is compiler-checked,
      verifier-checked, supervised, reproducible, and formally proved.

## 26. Consequences for the remaining snowflake documents

Every later design document must name:

- its authoritative component;
- its typed inputs and outputs;
- its snapshot and ownership lifetime;
- its external capabilities, ordinarily none;
- its trust assumptions;
- its cache and persistence status;
- its deterministic publication order;
- its cancellation behavior;
- its resource limits;
- its failure classifications;
- its validation boundary;
- its migration path from the current implementation.

A later document may refine an interface defined here, but it must not silently
move authority across a boundary.

The target compiler is therefore not one privileged executable surrounded by
helpers. It is a set of narrow components connected by typed, immutable,
inspectable contracts:

- orchestration assembles the world;
- the compiler decides source meaning;
- the emitter constructs a candidate artifact;
- the verifier decides artifact acceptability;
- the supervisor decides runtime authority;
- the VM executes only within those decisions;
- every tool asks the same semantic database.

That division is the foundation on which queryability, caching, deterministic
self-hosting, and trustworthy execution can be built.
