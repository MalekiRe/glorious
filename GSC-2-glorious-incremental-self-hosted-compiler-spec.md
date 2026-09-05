# GSC-2 — A Fresh, Compact, Incremental, Queryable Glorious Compiler

**Status:** Proposed implementation specification; not an implementation or a claim of test completion.  
**Prepared:** September 4, 2026.  
**Repository snapshot checked:** `MalekiRe/glorious@8cf378a1f19617e3aeddb18cada22540730323cc`.  
**Existing frozen Rust behavioral baseline:** `cfeab4b58d60754a70c819fdda25a1f1024907af`.  
**Replacement source root:** `compiler/`.  
**Implementation language:** Glorious, using a certified Stage0-compilable authoring profile.  
**Compatibility:** The full frozen Stage0 compiler surface, including its incremental database and VM-facing APIs.  
**Distribution target:** Independently verified G1 compiler bytecode, with the existing Stage0 wire format retained wherever compatibility requires it.

This specification supersedes GSC-1. It rejects GSC-1's batch-core/optional-query-wrapper architecture, its reduced classification of Rust-facing functionality, and its proposal to preserve adapters to the current self-host implementation.

**September 5, 2026 amendment:** [Unsafe memory and the native/VM ABI](docs/unsafe-memory-and-native-abi.md)
is an approved prerequisite. It supersedes the unsafe/raw-memory exclusion in
section 13.2 and permanent algorithmic hashing/UTF-8/collection leaves in section
13.4. The chosen self-hosting path specializes the compiler and ordinary source
libraries into bytecode, including unsafe raw-memory implementations, operating
on host-compatible objects. Safe-only guest verification, trusted native library
safe exports, and zero-marshalling compatible in-process values remain targets.
The Glorious LLVM backend and native-precompiled Glorious std are deferred until
after working, verified self-hosting; initial interop tests use native host ABI
fixtures, not that backend. Existing artifact generations retain explicit
compatibility; this is not an execution certificate.

The required product is **a long-lived, demand-driven, incremental compiler database written from scratch in Glorious**. Command-line builds, inspection, IDE requests, tests, and self-compilation all use this database. Compactness comes from sharing algorithms, storage, and control—not from removing capabilities.

The current self-host implementation is discarded in its entirety. Git history remains its archive. No old self-host source, runtime-support package, probes-as-implementation, artifact templates, source-path conventions, or claimed coverage is an implementation dependency of the replacement.

Repository facts are referenced as [R01]–[R17] at the end. Requirements, proposed interfaces, algorithms, budgets, and schedules below are design decisions. Code blocks are implementation pseudocode unless explicitly identified otherwise; they are not asserted to compile under Stage0.

---

## 1. Binding decisions

### 1.1 What stays

Preserve the Rust Stage0 compiler, its tests and fixtures, the independent Rust VM, the language and bytecode specifications, and the canonical standard library subject to certification. Preserve **every observable frozen Stage0 compiler behavior**: source acceptance and rejection; diagnostics; inspectable intermediate products; query results and completeness; memoization and parent reuse; dependency traces; revision and package lifecycles; cancellation; budgets; retention accounting; interface and persistent artifact caches; compiler modes; CLI behavior; bootstrap evidence; and candidate/verified VM encoding, decoding, verification, and execution APIs.

Source equivalents may use idiomatic Glorious types and a stable host protocol instead of Rust's concrete memory layouts. An exported behavior does not become optional because its existing API is written in Rust. There is no P2 exclusion category.

### 1.2 What goes

The retirement change removes the active `self-host-stage0/` implementation, its compiler-specific support package and source manifest, and its associated implementation-coupled probes and check scripts. It removes old self-host jobs from CI and resets replacement progress to zero. Existing documentation and evidence are either explicitly marked historical or replaced by the new registry; none is counted as replacement coverage.

Preserve an old test *case* only after independently extracting its input and expected contract from the Rust oracle or normative specification. Reimplement its harness against the new public API. Do not import its old helper compiler, scalar IR, codec, or runtime package.

Deletion is an implementation milestone described by this plan; preparing this document does not modify the repository.

### 1.3 What compactness means

Optimization priority is: correctness and full functionality; sound incremental reuse; bounded memory and execution; maintainable compact implementation; cold and warm performance; source and artifact size.

Do not minimize line count through compressed formatting, giant untyped records, omitted diagnostics, unbounded recursion, hidden native helpers, or a reduced bootstrap language. Count generated code, compatibility codecs, host shims, and support libraries separately so implementation has not merely moved outside the budget.

### 1.4 One architecture in every mode

A batch compilation is a short-lived database session. An IDE request is a demand against a retained snapshot. Self-compilation is an ordinary build demand. None has a second semantic pipeline.

```text
CLI / editor / test driver / embedding host / bootstrap driver
                              |
                    CompilerDatabase
          immutable revisions + request sessions
                              |
             typed demand / query scheduler
     memo products + dependency reads + validation
                              |
       source / interfaces / resolution / elaboration
       terms / traits / flow / MIR / optimization / VM
                              |
       immutable outcomes + inspection + publication
```

The host transports authorized bytes and operational signals. It does not implement the query engine, cache validation policy, revisions, source semantics, or command selection.

---

## 2. Compatibility and specification authority

[R01] confirms the examined head. [R02] pins the existing baseline. A replacement lock file records independently: Rust behavior baseline, Stage0 authoring compiler revision, standard-library revision, VM revisions, artifact schemas, and new compiler source closure.

The authoring compiler may receive narrowly scoped fixes before it can build the new source. Such fixes require exact tests and an explicit baseline decision. Never silently move the behavior target to make a port discrepancy disappear.

For an implementation/specification disagreement, record the exact case. Preserve existing contract behavior for compatibility unless a separately reviewed language change updates both the oracle and replacement targets. Documentation is not evidence that a path actually executes.

The initial machine-readable contract inventory contains **all exports recursively reachable through the public modules**, not merely root `pub use` lines, plus modes, CLI flags, diagnostics, cache observations, source identities, query policies, codecs, and runtime limits. Each record names its comparator and one or more executable tests. Counts in the old baseline remain historical until regenerated from the pinned source.

### 2.1 Behavior versus physical implementation

Preserve return values, failure distinctions, ownership rules, lifecycle transitions, publication visibility, and documented inspection data. Replace `Arc`, `Mutex`, pointer identity, and Rust traits with explicit source-owned tables and checked handles. Do not reproduce Rust allocation graphs mechanically.

Single-owner execution is permitted; losing cancellation, interleaved requests, simultaneous live snapshots, or observable session semantics is not. Where a Rust panic is an intentional boundary behavior, a named source invariant outcome and an explicit host-protocol mapping must be reviewed and tested. Language-level `abort` is not a recoverable query exception.

### 2.2 Existing contracts the replacement must retain

The current query engine already distinguishes `Complete` and `Recovered`, automatically propagates recovery from children, checks cancellation before cache hits, defaults parent reuse to rejection, keeps execution provenance, and publishes query values together with dependency journals. Revisions support weak parent availability, existing pins after retirement, request/package staging, and inspection-safe retention counts. The dependency ledger distinguishes `Cold`, `Green`, `Red`, `Cycle`, and `Incomplete`. [R03–R07]

These are initial architecture requirements, not later tooling features.

---

## 3. Shared implementation kernels

Use four semantic kernels and four shared infrastructure kernels. Public responsibility modules can be thin facades over them.

| Kernel | Responsibilities |
|---|---|
| Callable | Functions, closures, handler clauses, resumptions, capture layout, invocation checking |
| Brand | Generative labels, execution/refinement/continuation environments, binder identities |
| Quantity | Principal/actual use intervals, branch hulls, sequence, repetition, resumption multiplicity |
| PlaceFlow | Initialization, moves, loans, captures, use events, escape, refinement protection, cleanup |
| Query | Typed demand, scheduling, memoization, input observation, reuse validation, execution explanations |
| Transaction | Attempt staging, undo marks, allocation ownership, package staging, publication and rollback |
| Terms | Mixed-kind types, lifetimes, rows, consts, substitution, canonicalization, inference |
| Storage/schema | Typed indices, arenas, flat ranges, maps, bitsets, bounded codecs, format descriptions |

Sharing an engine does not mean sharing unrelated semantics. The trait solver, import solver, and ownership analysis may use one worklist implementation while retaining distinct transfer, join, cycle, and termination rules. Query freshness epochs and MIR mutation epochs are separate domains.

---

## 4. Database, revisions, and sessions

### 4.1 Ownership model

```text
Database
  identity, next_revision_ordinal
  revisions                 // immutable world records
  active_world_index        // exact normalized-world deduplication
  query_registry, memo_directory
  family_product_stores
  source_blob_store, frozen_term_segments
  revision_publications     // committed dependency/inspection products
  interface_cache, persistent_artifact_cache_policy
  session_table, snapshot_pins, product_pins
  retention_accounting

RevisionRecord
  id: (DatabaseId, u64)
  parent: optional RevisionId
  world: FrozenWorldRef
  state: Active | Retired
  retained_memo_rows

RequestSession
  revision_pin
  cancellation_handle, work_budget, memory_budget
  requested_mode, demanded_roots
  package_states
  staged_dependency_facts, diagnostics, outcome
  active_attempts, pending_publications
```

Use an append-only revision ordinal with checked overflow. Database-local identity is host/session identity, never part of reproducible artifact content. Product references are validated opaque handles, not forged pointers.

### 4.2 Revision operations

`import_world(request, parent)` validates and normalizes every input, validates the supplied parent under the current active-parent rules, and consults the active equivalent-world index. It returns the already retained equivalent revision when the existing contract does so; otherwise it creates a new immutable revision. Do not assume every edit call yields a new ordinal.

`open_snapshot(revision)` and `open_request(revision)` require an active revision in the same database. A retired revision rejects new opens but remains usable through a previously admitted live pin. `retire(revision)` does not cancel existing requests implicitly. Cancellation is a separate request control.

`collect_retired()` runs at a safe point. It collects retired revisions only after their pins reach zero, removes their memo/trace/explanation ownership, unregisters their world index entry, and releases unreferenced product segments. Parent links are weak: a live child does not keep the entire ancestor history alive. Missing parent evidence causes recomputation, not unsound reuse. These rules follow the current lifecycle. [R05–R06]

### 4.3 Branches and ancestry

Do not implement freshness as `memo_revision <= requested_revision`. Revision ordinals are not proof of ancestry, and the database may contain sibling worlds.

The compatibility reuse search examines the **immediate retained parent only**, matching the current contract. Content sharing may deduplicate a value from another revision, but that does not establish validity or authorize reading that revision. Grandparent or sibling reuse requires a separately versioned, fully validated enhancement; it must not silently change `ParentMemoMissing` or parent provenance.

### 4.4 Package lifecycle

Preserve `Open → Staged → Committed` and `Open/Staged → RolledBack`. A package may open only when present in the immutable request world. Duplicate opens, reopening rolled-back staging, publishing an unstaged package, and publishing with active body scratch are rejected.

A request validates every demanded package before atomically committing its outcome. Package/body scratch counters return to zero on commit or rollback. No partial successful package set appears in a successful request outcome.

### 4.5 Scheduling and interleaving

Start with one source-owned scheduler and one writer to database mutable state. Multiple sessions and snapshots may remain live and requests may interleave at safe points. The embedding host serializes entry or delivers commands through a mailbox; it does not decide semantic scheduling or cache validity.

Add a narrowly specified cancellation/control polling capability where needed. A work loop must poll often enough that long parsing or solving does not prevent cancellation. Do not require Glorious threads or an async executor to preserve this API.

A suspended query frame owns IDs and attempt-local storage, not an outstanding unique borrow of the complete database. Access to a product is scoped; release the borrowed view before a child demand, yield, or mutation that could relocate the referenced store.

---

## 5. Typed query model

### 5.1 Identity layers

Use three separate identities:

1. **Stable semantic key:** a family identifier plus exact typed key—e.g. file, definition, canonical trait goal, or instance.
2. **Revision-qualified memo key:** database, revision, family, and typed key.
3. **Product-local ID:** an index valid only inside a particular frozen product segment.

Preserve existing `FileKey`, `ModuleKey`, `DefKey`, `InstanceKey`, and canonical digest formulas at compatibility boundaries. Do not replace them with source pointers, global insertion numbers, or content-only keys that merge distinct nominal declarations.

A local index cannot cross a query boundary without its owning product reference. Persisted keys encode stable identities, never session-local arena numbers.

### 5.2 Family contract

```text
QueryFamily<K, V, E>
  family_id, schema_generation
  recovery_policy
  cycle_policy
  reuse_policy
  retention_policy
  begin(key) -> ProviderState
  step(context, state, child_result?) -> Step
  freeze(value) -> FrozenProduct<V>
  fingerprint(value, observation) -> Digest
  validate_product(value) -> Validation
  encode/decode where the public contract requires them
```

`Step` is a closed protocol such as `Need(child_key)`, `Continue(state)`, `Yield(state)`, `Done(value)`, or `Fail(error)`. This permits an explicit evaluation stack. Providers can use a direct typed helper when depth is structurally bounded; input-sized recursion must use worklists or this stepping protocol.

The registry is closed and source-defined. Each family has a typed product store and small adapters to a shared scheduler. Use sealed sums and checked tagged handles, not `Any`, unchecked casts, or an unsafe heterogeneous heap. Instantiate generic storage operations where necessary, but do not monomorphize the entire scheduling/validation machine for every family.

### 5.3 Memo state

```text
MemoCell
  key
  state: Absent | Checking(attempt) | Computing(attempt) | Ready(entry)

MemoEntry
  product_ref
  observed_fingerprints
  completeness: Complete | Recovered
  replay_reads: Range<DependencyRead>   // first-observation order
  canonical_dependencies: Range<DependencyKey>
  generation_contract
  execution_provenance
```

One immutable memo entry owns the value reference and its canonical dependency journal. Pending state is not externally usable. Retired ownership is removed at the revision safe point.

A rejected query, cancellation, resource failure, cycle, or invariant failure does not install a successful memo entry. In particular, do not cache cancellation as a property of a semantic key. Successful child queries may remain memoized when a parent later fails, as allowed by the existing per-query publication contract; parent/request publication remains separate.

### 5.4 Query result and failure categories

Keep distinct:

```text
QueryValue<T> = { value, fingerprint, completeness }
QueryFailure<E> = Rejected(E) | Cancelled | ResourceLimit(name, limit)
                | Invariant(reason) | Cycle(family)
                | RecoveredProduct(family)
```

Source diagnostics can also be a complete immutable diagnostic *product*. That is not the same as memoizing a transient `QueryFailure`.

A recovery-capable IDE query may return provisional syntax or type information. Every parent that consumes it becomes recovered automatically. A provider cannot relabel a recovered child as complete. A complete-only family rejects recovery on child demand, same-revision memo hit, parent reuse, and publication.

### 5.5 How providers read inputs

Every semantic read goes through `QueryContext`:

```text
context.input(FileBytes(file))
context.input(SemanticOption(name))
context.input(RuntimeBinding(binding))
context.query(Signature(def))
context.query(ResolveName(scope, namespace, symbol))
```

Direct untracked reads from the whole world are forbidden. Providers receive a capability-limited context, not the underlying mutable database. The context automatically records child identity, observation kind, fingerprint, and completeness.

A whole-world fingerprint is correct for the existing full-artifact cache key. It is deliberately **not** the universal semantic query key: that would invalidate every body on every edit. Hashing only a query's own source is also insufficient; dependencies must cover imports, fixity, impl sets, layouts, options, and authority actually observed.

### 5.6 In-flight requests are not automatically cycles

Cycle detection is scoped to the active demand ancestry of an evaluation, not merely to the existence of a global busy key. If another request is computing the same revision/family/key, enqueue the second request or let it wait at a scheduler safe point; do not report a source-level cycle solely because requests overlap.

Initially do not share mutable attempts between requests. The owner may publish an immutable memo that the waiting request subsequently demands under its own cancellation/recovery controls. If the owner fails or is cancelled, its staging is removed and the waiter may compute independently. The waiter's cancellation does not cancel the owner. No borrowed database lock or unique view is held while waiting. Map the established baseline cycle tests exactly; additional interleaving behavior is explicitly tested as part of the new scheduler contract.

---

## 6. Reuse and invalidation algorithm

### 6.1 Two observations, not one overloaded color

Record independently:

- **Execution provenance:** memoized here, reused from immediate parent, or recomputed with its established reason.
- **Dependency/value status:** cold, green, red with a canonical changed edge, cycle, or incomplete.

A recomputed query can be green. A private body change can force interface checking while leaving the interface equal. This is already represented by the current dependency ledger. [R07] Red/green validation is also described in the Rust compiler's query documentation. [R16]

The existing ledger's green contract compares both the product fingerprint and canonical dependency identities after structural completeness/cycle checks. Preserve that public projection. Internal typed observations may prove a smaller output projection unchanged, but must not silently relabel the legacy dependency trace.

### 6.2 Demand algorithm

```text
demand(session, family, key):
  validate admitted snapshot/session and family/key contract
  check cancellation BEFORE every hit or reuse return
  if same-revision Ready exists:
    enforce recovery policy
    pin/materialize the value according to retention policy
    record Memoized(revision)
    return via tracked child-observation path

  install Checking marker before recursively validating dependencies
  locate same key in the immediate retained parent
  establish Cold / ParentMemoMissing / ParentReuseRejected candidate reason

  if parent exists and family policy permits validation:
    validate generations, direct input observations, and old child reads
    process old child reads in recorded demand order
    stop on first changed control-affecting observation and recompute provider
    if all required observations match and proof is complete:
      enforce recovery policy
      stage child-revision ownership of the existing frozen value
      stage validated child-revision dependency records and provenance
      check cancellation and commit Ready atomically
      return ReusedFromParent(parent)

  transition marker to Computing
  run provider through explicit frames/worklists; track fresh reads
  enforce transitive recovery and product limits
  freeze and validate product; compute canonical fingerprints
  compare against parent for value/dependency status
  prepare all publication allocations; check cancellation
  install Ready(value, journal, provenance) in one non-failing commit
  remove marker and return

on failure:
  discard this attempt's staging and dependency journal
  clear Checking/Computing marker; release scratch and memory leases
  retain no fabricated successful result or execution explanation
  preserve independently committed valid children
  return the exact failure category
```

Providers with no sound reuse contract retain the current fail-closed `NeverReuse` policy. A shared validator replaces duplicated hand-coded validators only after its input coverage is established for that family.

### 6.3 Demand order versus display order

Keep dependency reads in first-observation order for validation replay. Also store or derive the sorted/deduplicated public journal. These are two views over one tracked read set, not two independent dependency graphs.

Example: a provider first asks which name is selected, then asks for that declaration's signature. If the selection changes or the old declaration disappears, stop validation and rerun the provider before trying the obsolete signature. Blindly sorting and replaying old dependencies may demand a now-invalid branch.

Ordinary dependency edges include the actual key and observed projection. A family name plus a digest is not sufficient internal identity for two distinct demands with the same value. Public legacy journal formatting may retain its existing form as a projection.

### 6.4 Negative dependencies

A failed name lookup depends on the relevant scope/name bucket even when no declaration existed. A trait search depends on the applicable implementation-set fingerprint even when no candidate matched. A glob import depends on its exported-name set. A missing module depends on the supplied module-membership input.

These negative dependencies are mandatory: adding a declaration or impl must invalidate a previous absence or unique-selection answer. Do not record only the declaration that happened to win.

### 6.5 Cycles and fixed points

Ordinary recursive demand produces the existing structured cycle result; a busy entry is never treated as a reusable answer.

Represent legitimate recursive analyses as **explicit SCC or fixed-point query families**. Examples are import/re-export closure, recursive call summaries, variance, and specific trait-cycle policies. Each declares its ordered domain, transfer, join, initialization, work budget, and termination argument. Publish the finished SCC result as a unit; downstream queries see no provisional guesses. When an input or SCC membership changes, restart from the family's justified initial state in the first implementation. Reusing the old solution as an initial state is unsafe for deletions or decreasing facts unless a separate incremental-solver proof permits it.

Finite-height monotone domains can converge by worklist iteration. Infinite-height domains need a sound widening or a structured limit result. Reaching an arbitrary iteration count is not proof of a solution. Coinduction is permitted only for explicitly justified trait rules. [R17]

---

## 7. Transactions, cancellation, and effects

### 7.1 Three publication boundaries

**Query commit:** value, dependencies, completeness, and execution provenance become visible together. Successfully completed child memos may survive a later parent's rejection.

**Request commit:** its package outcomes, canonical diagnostics, and public dependency ledger become visible together only after every demanded package is staged. A failed request does not expose a partially successful compilation outcome.

**External publication:** verified bytes are written through authorized, atomic output operations. Cache-store failure remains separate from a valid freshly compiled result, matching the existing cache contract. [R08]

These are related transactions, not one giant rollback that erases all valid work whenever an IDE request is cancelled.

### 7.2 Common transaction substrate

Share mark/rollback utilities and allocation tracking, but preserve typed transaction kinds. Inference undo cannot roll back a previously committed child query; package rollback cannot mutate another session's world; a failed cache store cannot invalidate a verified artifact.

Nested marks are stack-disciplined. Committing an inner speculative mark retains the undo information needed by an outer mark. Never refund computational work already performed. Reclaim memory reservations on release and roll back failed hierarchical *reservation* charges exactly as their contract specifies.

### 7.3 Correct use of quantitative ownership

Do **not** make every guard `Use<[1,1]>` and then give it a drop-based rollback. Positive-lower values cannot be silently destroyed during cancellation, and `Drop` is a zero-use operation in this language. [R10]

Use affine attempt-owned guards when abandonment is legal. A structured scope combinator or the scheduler explicitly performs rollback/release on every returning success, failure, cancellation, and label-exit path. A pure local destructor may release self-contained storage where legal; it must not acquire forbidden effects or label-transfer authority.

Reserve exact-use tokens for protocols where all continuing paths explicitly transfer or discharge the token. The type system can prevent double commit, but it does not make filesystem publication, database rollback, or cancellation correct automatically.

### 7.4 Effect policy

Use source-defined terminal or one-shot effects for fatal query exit, diagnostic collection, cancellation checkpoints, and budgeting where their lowering is certified. Handlers sit at query/request boundaries; hot loops use direct typed access to counters rather than perform once per byte or IR node.

Do not use multishot continuation cloning as the compiler's transaction rollback mechanism. Mutable inference, unique borrows, and owned scratch are restored by undo logs. Higher-order control is specialized/inlined after its correctness is proven.

### 7.5 Linearization and I/O

Preallocate commit metadata, then check cancellation immediately before the commit point. Once the non-failing commit starts, cancellation applies to subsequent work, not an already returned result.

No cross-memory/filesystem atomicity is assumed. Stage files, verify contents, and publish via an atomic rename or a final commit manifest as supported by the host. For multiple files, publish immutable generation files and a final manifest/pointer last; recovery ignores uncommitted generations. Keep the legacy single-file atomic-write behavior intact, including failure preservation and target-path policy.

## 8. Product storage and retention without losing queryability

### 8.1 Mutable builders, immutable products

A provider builds into attempt-local arenas, validates, and freezes one immutable product segment. Memo rows in several revisions may share that segment. Mutable builders and inference cells never become memo values.

```text
ProductRef<K> = checked (store, slot, generation)
LocalId<K>    = u32 index inside an identified product
Span         = (FileKey, start_byte, end_byte)
Range        = (start, count) inside one immutable side array
```

Numeric local IDs are cheap; the owning segment preserves their lifetime and meaning. Within a body, `u32` IDs and flat ranges avoid recursive object graphs. Across queries, use a product reference plus local ID or a stable semantic key. Scope brands alone are not assumed to provide arbitrary generative arena typing: certify the authoring-language support or use private typed wrappers plus checked handles.

### 8.2 Lifetime classes

| Storage | Owner | Reclamation rule |
|---|---|---|
| Source blobs | Immutable worlds/products | Release after all references disappear |
| Query products | Memo rows and explicit product leases | Release after last owner disappears |
| Body parse/inference scratch | One query attempt | Reset after freeze or rollback |
| Solver tables with inference variables | One body/solver attempt | Never shared across revisions |
| Frozen ground solver products | Typed query memo | Retire with revision ownership |
| Interner segments | Explicit product/store owners | Reclaim unreferenced segments; no immortal global pool |
| Traces and explanations | Revision publication/memo owners | Collected with the revision |
| Persistent artifacts | Explicit external cache | Separate bounded storage policy and validation |

### 8.3 Cached IR is intentional

Syntax, Core, MIR, and optimization results are first-class frozen query products. They remain inspectable as long as their snapshot/product lease remains valid. There is no blanket rule to discard Core after MIR lowering or MIR after emission.

Reclaim mutable scratch immediately. Retain requested immutable products, sharing segments across equal results and revisions. A product may reference another product only through a recorded storage owner, never a dangling offset into reset scratch. Nominal recursion uses declaration keys rather than strong ownership cycles between product segments.

Default **compatibility retention** preserves memo and inspection behavior until explicit retirement/collection. Do not silently evict an active memo and then pretend the next result was still `Memoized`. Optional memory-pressure materialization policies are explicit, separately tested settings with truthful explanations. Every supported product can be demanded again; no analysis API disappears because its payload was evicted.

When too much active or pinned state exceeds the configured memory budget, return a structured admission/resource failure. Do not invalidate a live snapshot to meet a budget.

### 8.4 Logical counts versus physical bytes

Preserve the existing inspection-safe counts: retained revisions, retired revisions, pinned revisions, snapshot pins, memo products, dependency edges, execution explanations, package scratch, and staged body products. [R03–R06]

Count a memo in each owning revision as a logical retained product even when its bytes are physically shared. Report physical segment bytes and capacity separately. Read-only retention inspection must not temporarily increment the very pin count it reports. Explicitly pinned old revisions are allowed to consume memory; an unpinned-retired revision is not.

### 8.5 Compactness in the VM is measured

A Glorious `struct` containing four `u32` fields is not automatically a 16-byte object in the current VM. Typed wrappers and flat source arrays are logical layouts, not evidence of packed physical storage. Measure runtime allocation count, element representation, copying, and indexing cost before selecting arrays-of-records, structure-of-arrays, or packed byte buffers.

Keep hot fields in numeric arrays when it measurably helps. Use source-owned `ByteBuf` only where encoding is appropriate; do not turn all compiler objects into untyped byte offsets. No per-node heap object is the intended hot-path design, but achieving that may need representation optimization or existing machine-array support.

---

## 9. Query inventory and dependency boundaries

This is the proposed internal query decomposition. Exact public Stage0 entry points map to these families or faithful facades; this table does not assert that Stage0 currently exposes these exact names.

| Family | Key | Frozen output / important observed inputs |
|---|---|---|
| SourceBytes | FileKey | Exact source blob and validated identity |
| LineIndex | FileKey | Byte/UTF-16 mapping, depends on exact source bytes |
| Lex | FileKey | Lossless tokens, trivia, delimiters, lexical diagnostics |
| Scan | FileKey or module range | Declaration shells, body ranges, structural recovery |
| Header | Declaration locator | Source-shaped header syntax, generic binders, names |
| ModuleGraph | PackageKey | Supplied module membership and exact logical topology |
| Interface | ModuleKey | Complete module interface and diagnostics |
| PublicInterface | ModuleKey | Exported semantic projection only |
| Fixity | ModuleKey | Visible operator binding/precedence/associativity |
| ResolveImports | Import SCC/package | Fixed-point exports/import bindings |
| ResolveName | Scope/namespace/name | Found, ambiguous, inaccessible, or absent answer |
| Signature / NominalLayout | DefKey | Resolved signature/layout, dependent heads and terms |
| ImplIndex / Coherence | Trait/head bucket | Applicable positive/negative implementations and conflicts |
| TraitGoal / Projection | Canonical goal + environment | Proven/ambiguous/rejected answer and evidence |
| BodySyntax | DefKey | Full generic body syntax, not a shape-specific fragment |
| TypedBody | DefKey + generic environment | Core, callable/brand tables, complete checking result |
| Flow | Body identity | Unified place/use/loan/escape/cleanup facts |
| BodyDiagnostics | DefKey | Structured facts with current source provenance |
| InstanceGraph / CallSummarySCC | Roots or canonical instances | Reachability and recursive performance summaries |
| Mir | InstanceKey | Validated generic ownership/control CFG |
| OptimizedMir | InstanceKey + explicit optimization contract | New frozen MIR plus deterministic pass report |
| CodeFragment | InstanceKey + target contract | Relocatable code with symbolic stable references |
| Artifact | Package/roots + build contract | Canonical complete bytes and commitments |
| VerifyArtifact | Format + bytes digest + verifier contract | Verified program or exact validation error |
| Occurrences / References | File/definition | Current revision's source occurrences and uses |
| Explain | Query/diagnostic/obligation key | Typed explanation product, not debug-string parsing |
| RequestOutcome | Mode and request roots | The appropriate checked/inspected/test/build/bootstrap outcome |

### 9.1 Granularity

Start with file, module, definition/body, canonical trait goal, and function-instance boundaries. Use ordinary local routines for per-token, per-expression, and per-basic-block operations. Queryifying every instruction would inflate keys, dependency edges, lookup cost, and diagnostics machinery.

The root for a mode must demand all checks that the baseline requires, including unused declarations or unreachable bodies where they are normally checked. Code-generation reachability does not authorize skipping required diagnostics.

Broaden granularity only where profiling shows excessive recomputation. Conversely, a package-wide `compile_everything` query is not an adequate implementation of the fine-grained products already exposed by the service.

### 9.2 Semantic, source, and build fingerprints

Use distinct, explicitly typed observations:

- `SemanticValue`: behavior, types, effects, quantities, layout, or other consumer-visible meaning.
- `SourceOrigin`: file identity, spans, token mapping, names needed for the source-facing product.
- `BuildContract`: target, compiler/format generations, explicit optimization options, runtime selectors, host ABI, and relevant authority.

A diagnostic cannot reuse stale spans merely because its semantic error code is unchanged. A source edit before a function may preserve its semantic Core while requiring new origin mapping. Store origin anchors or a separately recomputed source map; reject reuse where an anchor cannot be validated.

For existing API fingerprints, preserve the exact old encoding. New internal projections are separately versioned and become dependencies only of consumers that accept their narrower contract. Hash each frozen product/projection once, not on every memo lookup. Digest equality is evidence under the chosen collision model, not a mathematical guarantee; exact keys are compared structurally and test builds can compare canonical payloads on matching digests.

### 9.3 Invalidation examples

A comment edit invalidates lossless lexing and relevant position maps, but should not force unrelated semantic bodies when their observed projections are unchanged. A private function-body edit leaves the public signature green unless the language actually infers or exports a body-dependent property. Callers that inline it or depend on its effect/performance summary still observe the body/summary.

A new impl invalidates affected candidate-set queries, not only previous winning impls. A fixity edit invalidates operator grouping in affected scopes. An optimization-level edit reaches optimization/emission but not language checking unless its specified semantics require otherwise. A runtime binding edit invalidates ABI/authority consumers, even when the human-readable symbol remains the same.

### 9.4 Lossless source products

Retain comments, whitespace, exact spelling, delimiter recovery, and UTF-16 mapping wherever Stage0's lexical/inspection APIs expose them. The existing tests explicitly require lossless comments and editor coordinates. [R09] Semantic body parsing may walk a compact significant-token view into the same token arena. Do not add a second lexer for tools or concatenate every file on each edit.

Normalize package/logical identities as Stage0 does; process each immutable source blob independently and build a virtual source map. A compatibility projection can expose a flattened stream when a consumer requires it. File boundaries must never accidentally join tokens.

---

## 10. Frontend and static semantics

### 10.1 Structural syntax

Lex files, pair delimiters, scan declarations, and collect headers before body elaboration. Store a generic body AST with tags, spans, and child ranges for literals, names, calls, constructors, fields, references, assignments, closures, flat operator streams, labels, handlers, perform/resume/cancel, and patterns.

There are no per-width parser or IR families. Scalar widths are type/primitive data. Contextual blocks are elaborated from selected `Fn` constraints, not callee names. Operator grouping uses the queried visible fixity table. Preserve left-to-right evaluation even when inference seeds constraints in another order.

### 10.2 Mixed-kind terms and inference

Use one typed term representation with separate sort tags for types, regions, rows, consts, generic arguments, and projections. Share folding/substitution/walking machinery, not invalid cross-sort unification.

Body-local inference uses cells plus undo logs. Never place unresolved variables in a cross-revision interner. Canonical trait query keys include binder/universe structure, the local evidence environment, relevant impl-set generation, and solver policy. After zonking, publish immutable terms and proof references. Sealed nominal brands retain identity even when their summaries are structurally equal.

### 10.3 Traits and instance selection

Implement coherent nominal impl selection, orphan rules, positive/negative reasoning, associated type/effect/const projections, mixed-kind generics, GATs, higher-ranked bounds, and all current normalization/ambiguity behavior. Index candidate sets by trait and outer self-type shape while tracking fallback/blanket candidates. Candidate order must not become an unauthorized specialization rule.

Use one candidate transaction routine. Roll back substitutions, obligations, and branch facts on rejection. Preserve full reasons in structured explanations without storing every failed candidate's entire inference arena. Budget exhaustion is a resource result, not evidence that no impl exists.

### 10.4 Callable, environment, and brand elaboration

One callable record covers ordinary functions, closures, handler clauses, and resumptions with different evidence and runtime behaviors. One brand arena distinguishes label, execution, refinement, continuation, and binder kinds.

Keep linked environments open until the entire selector/call expression has contributed captures, quantities, effects, lifetimes, and post-state. Seal only after those constraints agree. A callable's nominal identity and its environment summary are distinct. Never merge generative brands solely because their fields match.

### 10.5 Unified flow facts

One graph stores places, move paths, loans, source-storage lifetimes, access events, quantitative uses, captures, and provenance. `placeflow`, `useflow`, `escape`, and storage facades provide their complete current reports using these shared facts.

Branches use undo marks and sparse exit deltas, not whole-state clones. Solve initialization, ownership disposition, principal/actual quantities, nonlexical lifetimes, reborrowing, variance/outlives and higher-ranked leak checks. Keep their individual rules distinct even when traversals are shared.

Custom destruction is zero-use, cannot satisfy a must-move obligation, and cannot be dropped from a rewrite because a value is zero-sized. Partial moves and ownership deconstruction of custom-drop values stay prohibited. Preserve holes created by a move through a unique reference until every continuing path restores them.

### 10.6 Effects, patterns, and continuation safety

One pattern decision compiler serves handlers and `is`. It checks exhaustiveness, private-field authority, binder uniqueness, projected moves, discarded subtree legality, and positive/negative refinement scope.

Implement deep handlers, forwarding, finite resumption quantities, cancellation, effectful completion, brand-sensitive routing, and ordered cleanup. A may-effect row is not a precise resumption-count summary. Replay multiplication uses the authoritative performance summary; unique references and nonduplicable/custom-drop captures retain their restrictions.

The compiler implementation need not use every advanced feature itself, but the product must implement and test all behavior of the frozen baseline. A simpler *authoring style* is not a smaller *accepted language*.

---

## 11. MIR, optimization, and incremental code generation

### 11.1 Immutable query product, mutable pass builder

`Mir(instance)` returns a frozen, validated body. `OptimizedMir(instance, contract)` obtains an exclusive builder or clones only the body arrays that must change, applies passes, and freezes a distinct result. It never mutates MIR held by an old snapshot or another query.

MIR has typed block parameters, one local universe for temporaries/storage/parameters/drop flags, explicit places and loans, scopes, source information, control-site tables, and cleanup plans. Arena tombstones preserve checked editor identities. Backend phases distinguish raw, ownership-validated, cleanup-complete, optimized, and lowered forms.

### 11.2 Local analysis caches are not global queries

Use six body-local bundles: CFG; uses/liveness; ownership/loans/drop; effects/captures/calls; scalar facts; cost. Each has an epoch and invalidation bit. After a mutation, recompute invalid bundles lazily. Do not add a new global incremental framework for each optimizer pass.

Source-level demand caches immutable `Mir` and `OptimizedMir`; pass-local analysis caching accelerates one builder. These are different lifetimes and correctness contracts.

### 11.3 Optimization scope

Port every implemented frozen Stage0 optimization and checked-editor contract before declaring replacement parity. Backlog-only transformations are not silently prerequisites for that declaration. Add compactness-critical improvements through measured, separately tested changes.

Priority for compiler speed is direct call devirtualization/inlining, ordinary enum and terminal-handler simplification, tail formation, capture shrinking, aggregate scalarization, range/bounds simplification, CFG/SCCP/DCE, cleanup simplification, and register allocation. Use cheap body feature bits to skip irrelevant pass groups.

Keep traps, left-to-right evaluation, custom-drop order, ownership disposition, labels, handler reinstatement, cancellation, and effect visibility invariant. No optimization level changes legality.

### 11.4 Deterministic optimization budgets

A global "fuel remaining" counter shared by optional passes in query execution order makes code depend on cache warmth. Prohibit that design.

Charge operational work and memory to the real request budget. Separately choose deterministic optional-optimization allowances from explicit configuration and stable body/instance costs. A whole-program allowance is assigned in canonical instance order from an immutable plan. A memoized body receives the same optimization contract as a cold body.

Exhausting optional optimization keeps correct MIR and records a remark. Exhausting a mandatory resource limit returns the specified failure. Successful artifact bytes must be independent of unrelated previous queries, cache hits, scheduler interleaving, and host elapsed time.

### 11.5 Relocatable fragments

`CodeFragment(instance)` stores local register/block choices, code, cleanup data, constants, and **symbolic references** to stable declarations/types/functions. It contains no globally assigned final table indices.

`Artifact(roots, contract)` collects reachable fragments, sorts/canonicalizes the global tables, assigns final indices, patches relocations, and writes the container. This lets an unchanged function reuse its fragment when a different function changes global numbering.

An inliner observes callee body/optimized facts; an uninlined call normally observes signature, effects, summaries, and layout. Monomorphization roots and recursive summaries are tracked queries, not an untracked backend scan.

---

## 12. Runtime formats, codecs, and verification

### 12.1 Preserve distinct formats

Stage0's current program format and the independent VM's G1 `.grbc` format are not interchangeable. The earlier recorded seed path explicitly notes a G1 magic incompatibility. [R13] Recheck this with executable probes for the new authoring closure; never rename a file or assume the README establishes interoperability.

Keep exact Stage0 encode/decode/verify/execute behavior where exposed. Add the production G1 backend under its actual contract. A shared bounded reader/writer, opcode metadata vocabulary, and runtime utility layer reduce duplication, but **each format has its own explicit versioned schema**. Do not collapse incompatible instruction or ownership rules into a single unvalidated tag map.

### 12.2 Compiler versus runtime responsibility

All source semantics, query policies, revisions, inspection, source-side VM compatibility APIs, and emission reside in Glorious. Rust Stage0 is the seed/oracle; Rust `grvm` remains an independent G1 verifier/runtime and generic host supervisor.

Preserve the source compiler's required candidate/verified API and execution helpers. Do not cut them to meet a source budget or silently dispatch their missing rules to Rust. Share one source runtime implementation rather than adding AST, Core, MIR, and bytecode interpreters with independently drifting control semantics. A restricted evaluator can remain a test oracle only for its explicitly supported subset.

The independent verifier checks bytes and runtime invariants, not source trait inference. Verification does not prove source semantics were compiled correctly; differential language tests remain necessary.

Under the September 5 amendment, unsafe-enabled bytecode executes specialized
source libraries over genuine host-compatible memory. The host selects this
profile; structural verification does not turn unrestricted unsafe memory access
into an in-process sandbox. Safe-only bytecode has separate fail-closed admission.
The source compiler and library closure must run without a Glorious LLVM backend
or native generic-specialization fallback. Runtime call bridges and native host
ABI fixtures are permitted machine-boundary support, not compiler semantics.

### 12.3 G1 writer

Collect canonical strings, nominal identities, structural types, constants, signatures, imports, protocols, handlers, functions, code, operands, cleanup tables, exports, and drop glue using the exact selected G1 version rules. Follow its ordering rules table by table; do not replace all of them with an arbitrary global sort. Compute the exact required feature bits.

Assemble into a mutable source-owned buffer: reserve header/directory, append aligned records, patch checked extents, freeze once. Never emit compiler output from hand-written complete artifact templates. Goldens are test expectations, not code-generation algorithms.

Source-defined `Bool`, `Option`, and `Result` lower through ordinary nominal enum construction/selection and resolved machine primitives. Do not add source-name-sensitive Boolean/control opcodes. [R11–R12]

### 12.4 Cache security

Preserve the persistent artifact cache's existing complete-world key, envelope/version/digest checks, bounded reads, verifier admission, hit/miss/rejection/store counters, and nonfatal store-error behavior. [R08] Physical cache operations use narrow host capabilities; cache identity and validation policy are source-owned.

Do not claim a digest proves an untrusted semantic answer correct. A cold persistent artifact hit must still cross the appropriate decoder/verifier boundary and exact world contract. Persisting additional semantic memos later requires separate schemas, dependency validation, authority checks, and corruption tests. It is not required merely to preserve the existing persistent artifact cache.

## 13. Standard library and Stage0 authoring capability gate

### 13.1 Reuse the library, not the discarded compiler

The existing canonical `stdlib/` is eligible for reuse because it is a language library, not the old compiler. Certify it as part of the new source closure. Never depend on `self-host-stage0/runtime/compiler_support.glorious`; recreate any genuinely needed binding in the canonical library's private machine layer with fresh tests and an exact manifest.

Required substrate: growable vectors, immutable and unique slices, checked integer operations, UTF-8/source views, canonical hashing, typed IDs, arenas, range stores, maps/sets, sorting, bitsets, work queues, a bounded byte cursor, `ByteBuf`, and undo storage. Reuse an existing component only after its required operations execute under the selected authoring compiler/runtime pair.

### 13.2 Feature-to-implementation plan

| Feature/capability | Use in the new compiler | Certification or fallback |
|---|---|---|
| Structs/enums and generics | Query keys, products, provider states, terms, MIR | Cross-module compile/run/serialize tests; no scalar-shaped IR |
| Shared/unique references | Product views and mutable builders | Reborrow/relocation/capture tests; release views before yielding |
| Quantitative ownership | Single publication, explicit leases and staged ownership | Test abandonment and cancellation; no exact-linear Drop shortcut |
| Labels and tail calls | Structured early exit, worklist loops | Test nested cleanup and bounded depth; explicit loop/state frames when needed |
| Effects/handlers | Diagnostic and query/request failure channels | Certify terminal/one-shot paths; use explicit `Result` at bootstrap boundaries where necessary |
| Fn/RunsIn | Visitors, scoped transactions, typed provider helpers | Explicit provider-state enums are the non-magic alternative |
| Traits/GATs/HRTBs | Typed families, borrowed interfaces, generic folds | Use only certified authoring forms; still implement full accepted language |
| Static data | Schemas, lexical classes, diagnostic strings | Verify tags, lifetimes, literal lowering, shared byte views |
| Arrays/Vec/ByteBuf | All arenas and artifact construction | Measure growth, mutation, move semantics, per-element overhead |
| Hashing and integer leaves | Stable identities, maps, codecs | Exact existing digest formulas and official test vectors |
| Host transport/control | Argv, files, cancellation polling, diagnostics | Capability-bound bytes/handles only; source owns policy |
| Raw memory, unsafe contracts, and native/VM ABI | Source-owned libraries and host-compatible specialized bytecode | Certify U0–U6; unsafe-enabled mode is not a memory sandbox; LLVM is deferred until after self-hosting |
| Arbitrary threads/reflection/derive and broader foreign-language integrations | Not required to implement this architecture | Do not add them merely for bootstrap convenience |

An unavailable authoring feature creates a **Stage0 capability issue** or a simpler source representation—not a reduced target-language feature and not permission to keep old compiler code.

### 13.3 Capability test matrix

Each required operation needs four results: accepted by C0; executes correctly in C0's verified runtime; emitted by the new compiler in its supported target; accepted/executed by the corresponding independent verifier/runtime. Record format and schema explicitly.

Test empty/one/large collections; growth under a live permitted borrow; move-only elements; full and partial moves; enum matching; recursive calls; deep worklists; generic associated types; label exits; recovered results; cancellation cleanup; static data; and binary patching. A source file that type-checks but traps or cannot be emitted is not a certified capability.

### 13.4 New primitive admission

Admit only finite, deterministic, non-semantic mechanisms with exact ABI, bounds, authority and verifier rules. Suitable candidates include bulk byte movement, hashing, UTF-8 validation, and necessary generic host transport. First prefer existing leaves and source code.

Never add native `query`, `resolve`, `type_check`, `borrow_check`, `compile`, or `emit_artifact` helpers. A host may poll a cancellation signal; it may not decide whether a cached compiler answer is valid. Runtime leaf declarations are admitted by exact declaration identity and manifest signature, not by spelling.

### 13.5 No hidden code generation dependency

Initially use a small explicit family registry and source schema tables. Where repeated typed adapters justify a generator, make it a source-owned deterministic tool, include generated output in source/LOC accounting, and verify regeneration in CI. Do not assume macros, derive, reflection, or arbitrary compile-time execution exist.

---

## 14. Replacement module and API plan

Create a fresh tree with the language's established external-module directory convention. One suggested layout is:

```text
compiler/
  sources.lock
  src/main.glorious
  src/lib/lib.glorious
  src/kernel/kernel.glorious
  src/kernel/storage/storage.glorious
  src/kernel/query/query.glorious
  src/kernel/transaction/transaction.glorious
  src/kernel/terms/terms.glorious
  src/kernel/flow/flow.glorious
  src/kernel/schema/schema.glorious
  src/<facade>/<facade>.glorious
  tests/contract/
  tests/engine/
  tests/incremental/
  tests/language/
  tests/runtime/
  tests/bootstrap/
  bench/
  spec/
```

Expose the current 36 responsibility facades. They preserve behavior while delegating to shared kernels. Exact file counts are not a goal; dependency direction and contracts are.

| Facade(s) | Complete responsibility in the new implementation |
|---|---|
| diagnostic | Structured codes/classes/severity, facts, provenance and stable rendering |
| quantity | Checked interval algebra and all finite/infinite boundary behavior |
| identity | Exact digests and package/file/module/definition identities |
| operation | Cancellation, hierarchical budgets, reservations/leases and publication controls |
| request | All modes, normalization, immutable worlds, generation identities and limits |
| output | Atomic output, failure distinctions, cleanup and target preservation |
| source | Lossless lexing, immutable byte views, spans, line/UTF-16 mapping |
| scanner | Structural declaration boundaries, body/header ranges and recovery |
| header | Complete header syntax, mixed binders, aliases, effects, traits and implementations |
| interface | Namespace products, full/public fingerprints and transactional interface caching |
| module_graph | Exact supplied-world topology, orphan/missing/duplicate/cycle diagnostics |
| fixity | Local/imported fixities, replacement, ambiguity and fingerprinting |
| resolution | Namespaces, imports, scopes, visibility, occurrences and references |
| types | Mixed-kind terms, inference, structural consts, rows and substitutions |
| signature | Header elaboration, intrinsic identities and instantiation |
| coherence | Orphan/overlap/polarity checks and complete explanations |
| trait_solver | Canonical goals, projections, associated items, HRTBs/GATs and limits |
| pattern | One decision compiler and complete ownership/refinement behavior |
| body | Generic source syntax and body query products |
| core | Typed calculus, callable/brand/environment evidence and source semantics |
| placeflow | Shared initialization/move/loan/capture graph and published facts |
| useflow | Full quantitative-use/disposition reports over shared facts |
| escape | Lifetime/provenance/brand escape checks over shared facts |
| mir_storage | Source-slot lifecycles, replacement, drop flags and storage evidence |
| instance | Instance keys, reachable graph and recursive call summaries |
| mir | Generic CFG, checked editor, validation, cleanup and all existing optimizer behavior |
| runtime_manifest | Exact leaf/host selectors, ABI checking and trusted authority |
| vm_backend | Full candidate/verified API, codecs, verification, execution and target backends |
| bootstrap | Manifest codecs, provenance, commitments and convergence checks |
| dependency | Typed public traces/statuses over the authoritative tracked dependency records |
| revision | Worlds, pins, sessions, weak parents, retirement and retention accounting |
| query | Typed family APIs, scheduler, memo/reuse/failure/recovery/provenance contracts |
| artifact_cache | Persistent envelope validation, stats, limits and stores |
| service | Every compile/inspect/test/IDE/bootstrap mode and request publication contract |
| lib | Complete source library/API export surface |
| main | Complete source-owned command and option protocol |

Each public export maps to one facade operation and comparator. Public family names and legacy journal shapes are stable adapters over the new representation. No facade may be implemented by returning an empty successful result for unsupported work.

### 14.1 Proposed service usage

```text
db = Database.create(configuration)
r0 = db.import_world(world0, parent=None)
s0 = db.open_snapshot(r0)
q0 = db.open_request(s0, Ide, controls0)
a0 = q0.query(TypedBody(main_def))

r1 = db.import_world(world1, parent=r0)
s1 = db.open_snapshot(r1)
q1 = db.open_request(s1, Build, controls1)
a1 = q1.query(Artifact(package, build_contract))

assert s0 still observes world0
inspect q1 execution kind and dependency trace
cancel q0 without cancelling q1
retire r0; existing s0 remains valid; new open(r0) is rejected
close q0 and s0; collect_retired()
```

This illustrates the required API shape, not literal existing syntax. Query and inspection results never require rebuilding the whole compiler pipeline merely to expose a cached stage.

### 14.2 Long-lived host protocol

Provide both a typed in-process source API and a bounded, versioned command protocol for a long-lived compiler process. Proposed commands cover database creation, world import, snapshot/request open and close, typed query demand, product inspection, cancellation, retirement, collection, and publication. Responses preserve request ID, revision identity, result/failure class, and structured payloads. The codec is compiler-protocol-specific, not a requirement for language-wide reflection or generic serialization.

Use a narrow duplex byte-message transport plus a control polling capability when existing host facilities are insufficient. These are proposed generic host capabilities to certify, not claims that Stage0 already implements them. Bound frame lengths before allocation and check handle ownership/generation in source. The host delivers bytes and signals; Glorious parses commands and controls all database policy. Ordinary internal queries call the typed engine directly and never serialize to this transport.

Keep all required service/query/inspection operations reachable through the release command dispatcher or exported library roots. The fact that bootstrap demands only Build must not cause the release linker to remove the rest of the compiler API.

---

## 15. Implementation order with executable exit gates

Work can be parallelized by these boundaries, but no stage is "done" from type names, prose, or smoke scores alone. All replacement coverage starts at zero.

### M0 — Retire, freeze, and inventory

Remove the old source implementation and active build references; keep history. Preserve Rust Stage0/VM and their tests. Commit the new specification, lock files, complete API/query/diagnostic/format inventory, and replacement CI. Mark conflicting batch-only design documents superseded.

**Exit:** no build dependency or import reaches the removed tree; all frozen exports have a planned owner/comparator; current head and authoring/behavior baselines are independently pinned. C0 tests still run. No replacement coverage is inherited.

### M1 — Certify the source substrate

Build only the fresh storage/byte/collection tools and capability tests under C0. Exercise generic records, mutation, borrowed views, exact identity hashing, bounded readers, tail/state loops, and required host transport. Record physical VM costs.

The approved U0–U6 prerequisite adds host-layout memory, independently admitted
unsafe bytecode, and source library specialization/migration to this substrate.
Actual VM/native interop uses explicit host fixtures. Do not require an LLVM
backend, native Glorious std, or universally erased native generics to pass M1.

**Exit:** every operation needed by the next milestone executes, not merely parses; no per-element unbounded allocation or copying surprise remains unmeasured; all Stage0 blockers have exact minimized cases. New lower-level support lives in the canonical library.

### M2 — Build the real incremental database first

Implement revisions, pins, sessions, the typed registry, generic memo state machine, tracked reads, ordered parent validation, recovery propagation, cancellation, budgets, publication, explanations, and retirement.

Use a synthetic arithmetic/string dependency graph only as a **test of the production query engine**. It is not the compiler IR and must not become a scalar compiler prototype.

**Exit:** same-revision hits, immediate-parent reuse, recompute-green, changed/removed/added dependencies, sibling isolation, cancellation at every transition, failure retry, package rollback, and retention tests all pass. No lexer is needed to prove this kernel.

### M3 — Make source and interfaces queryable

Implement lossless source/line queries, lexing, declaration scanning, headers, topology, interfaces, fixities, imports, name lookup, occurrences, and reference products. Build new tests from Rust cases.

**Exit:** import two source revisions and show an actual name/interface query reused or recomputed with an exact explanation; an old snapshot remains unchanged; trivia/spans update correctly; interface-cache stats and request publication match the oracle.

### M4 — Implement terms, signatures, coherence, and solver queries

Implement sort-safe terms, inference/undo, canonicalization, signatures, layouts, trait/impl indexing, negative dependencies, projections, higher-ranked reasoning, and instance identities. Make explanations first-class products.

**Exit:** all assigned Rust positive, rejection, cycle, ambiguity, resource, and recovery cases compare. Editing an impl changes precisely the applicable solver observations. No inference-containing term escapes publication.

### M5 — Implement complete body semantics on the new generic IR

Implement generic BodySyntax, TypedBody, patterns, callable/environment brands, quantitative use, PlaceFlow, borrowing/escape, effects, deep handlers, resumptions, and cleanup conclusions.

**Exit:** assigned semantic/safety/rejection cases compare; queried Core/flow products are immutable and inspectable in multiple live revisions. Unsupported source returns explicit diagnostics, never a fallback.

### M6 — Implement MIR and all baseline transformations

Implement generic CFG construction, source storage, cleanup, checked mutation, analysis bundles, optimization queries, symbolic fragments, and precise dependency registration for inlining and summaries.

**Exit:** MIR/editor/storage/optimizer contracts compare with Rust. Inspecting unoptimized MIR after optimization yields the original frozen product. Editing a private body does not rebuild unrelated fragments unless a recorded semantic dependency requires it.

### M7 — Complete runtime compatibility and G1 emission

Implement the full Stage0 VM-facing source API and production G1 writer from versioned schemas. Exercise complete aggregate/reference/control/host paths through actual MIR rather than artifact templates.

Include the selected versioned raw-memory and execution-profile contracts needed
by source library bytecode; preserve older artifact meanings and fail closed on
unknown features. The release path must not depend on native Glorious emission.

**Exit:** both format-specific contract corpora pass their independent verifiers. Generic multi-function/multi-module programs execute with arrays, loops, labels, effects, diagnostics and capabilities. Emission is deterministic and schema-correct.

### M8 — Finish complete service and operational parity

Complete all modes, public query/inspection facades, persistent artifact cache, source command parsing, JSON/text diagnostics, atomic output, bootstrap manifests, and control transport. Integrate the full source SDK/API test runner.

**Exit:** every frozen export and behavior is mapped to executable passing evidence. Replaying session histories produces the same results, public traces, counters and failure categories under the specified retention policy. No native semantic callback is reachable.

### M9 — Close the bootstrap loop

Build the full new source closure using the format-aware bootstrap below. Require independent verification, predecessor evidence, full source-language and session-history conformance, and exact C2/C3 bytes.

Run the compiler and selected std closure as bytecode, including specialized
unsafe library implementations under explicit unsafe-enabled host policy. A
native-precompiled Glorious std or LLVM backend is not a bootstrap prerequisite.
After this working, verified self-hosting gate, LLVM may be implemented against
the shared object/call ABI with separate native-versus-bytecode comparisons.

**Exit:** the complete incremental compiler compiles itself. The artifact includes and tests the query/inspection/session APIs; convergence is not limited to a stripped batch-only tool.

### M10 — Measure, compact, and release

Profile cold self-builds and edit histories. Remove duplicate algorithms and unnecessary allocations. Improve handler/call specialization only where measurements justify it. Consolidate typed adapters, schema visitors, and product storage without changing contracts.

**Exit:** release resource targets pass or failures remain explicitly blocking; counters and source/artifact size are published; cold/warm and query-order determinism holds; long-lived unpinned memory plateaus. No feature removal is an allowed budget fix.

### 15.1 Recommended first changes

The first implementation change retires the old compiler and installs the new source/contract inventory. The second certifies the minimal collection/storage/host substrate. The third implements the **actual production query/revision engine**. The fourth ports the first real source/interface queries into that engine.

Do not start with literal evaluation or an arithmetic-only artifact compiler. The central vertical slice is: **open world → query interface → edit body → query again → inspect reuse → cancel → retire → reclaim**.

---

## 16. Mandatory acceptance-test catalog

Every case has exact source/API input, oracle output, comparator, required limits, and observed execution history. Tests compare contracts rather than incidental arena IDs. Intended new internal behavior has its own expected output and is not mislabeled frozen-oracle parity.

| ID | Required case and expected property |
|---|---|
| Q01 | Same revision/key twice: second demand is memoized and records dependency at its parent |
| Q02 | Parent world change with unchanged tracked inputs: reuse records the immediate parent |
| Q03 | Input changes, provider recomputes equal value: execution is recomputed while eligible value trace is green |
| Q04 | Provider recomputes equal value but dependency identities change: new read set is retained; legacy trace follows its exact rule |
| Q05 | Dynamic selector changes: validation stops before an obsolete dependent branch is demanded |
| Q06 | Previously absent name is added: lookup and dependent checking invalidate |
| Q07 | New blanket/negative/overlapping impl changes candidate set: relevant solver answers invalidate |
| Q08 | Same numeric local IDs in different products/databases: no aliasing or cross-world access |
| Q09 | Sibling revision has a newer ordinal: it never counts as an ancestor reuse proof |
| Q10 | Immediate parent collected: correct recomputation and `ParentMemoMissing` provenance |
| Q11 | Complete-only parent consumes recovered child: explicit rejection |
| Q12 | Recovery-allowing parent claims Complete: engine publishes Recovered instead |
| Q13 | Recovered same-revision/parent cached hit: recovery policy still enforced |
| Q14 | Cancel before memo hit or parent reuse: no usable value escapes the cancelled request |
| Q15 | Cancel/fail after child commit but before parent commit: child remains valid; parent journal/result absent |
| Q16 | Cancel during dependency validation: no permanent Checking marker or partial reuse record |
| Q17 | Resource failure during freeze/publication preparation: no partial entry; retry works |
| Q18 | Ordinary dependency cycle: structured failure, no successful stale memo |
| Q19 | Legitimate SCC fixed point: only completed result publishes; work limit fails explicitly |
| Q20 | Distinct query keys yield equal payloads: dependencies retain distinct identities |
| Q21 | Two interleaved requests demand the same busy key: wait/retry, not a spurious source cycle; cancellation remains request-local |
| Q22 | Delete an SCC input/member: restart from the justified initial state, never preserve an obsolete fixed-point fact |
| R01 | Equivalent active normalized world import: existing deduplication/parent-validation behavior |
| R02 | Retire pinned revision: existing snapshot works; new opens fail |
| R03 | Close final pin, collect: world/memos/edges/explanations released together |
| R04 | Child retains shared product but parent retires: child remains valid without retaining all parent state |
| R05 | Inspect pin counts: the inspection itself does not create a counted pin |
| R06 | Foreign/stale/reused-generation handle: fails without exposing another request's data |
| R07 | Package duplicate/open/stage/rollback misuse: exact lifecycle error; scratch counts reset |
| R08 | Parent request fails: no partial package outcome or dependency-ledger publication |
| I01 | Comment-only edit: exact lossless syntax/positions update; eligible semantic projections remain reusable |
| I02 | Private body edit: unchanged public interface and unrelated bodies remain reusable where dependencies permit |
| I03 | Header/ABI/layout change: all dependent consumers invalidate |
| I04 | Fixity/import change: affected grouping and binding queries invalidate |
| I05 | Optimization option changes: appropriate backend work invalidates; unrelated semantic queries remain valid |
| I06 | Diagnostic on reused semantic body after preceding-text edit: spans point into the new revision |
| I07 | Query optimized MIR then raw MIR: raw product unchanged |
| I08 | Global table indices change: cached symbolic fragments are relocated correctly |
| C01 | Cache hit validates exact world, format, canonical bytes and verifier result |
| C02 | Truncated/corrupted/wrong-generation/oversized cache entry: rejected miss, not source error |
| C03 | Cache store fails: verified fresh result remains available; stats and telemetry are correct |
| D01 | Cold/warm/cache-disabled/session-reused builds of identical inputs emit identical bytes |
| D02 | Change unrelated earlier query order and map capacities: same successful canonical result |
| D03 | Global optional optimizer budget cannot make warm and cold builds diverge |
| B01 | Compiler artifact format is accepted by its actual independent runtime before execution |
| B02 | Bridge build lineage is valid without requiring bridge/output byte equality |
| B03 | Full C2/C3 compiler byte equality plus complete API/session test corpus |
| M01 | Thousands of edit/query/retire/collect cycles: unpinned memory plateaus |
| M02 | Many pinned revisions: memory attributable to pins, bounded rejection at configured ceiling |
| M03 | Large/deep source and solver workloads: bounded explicit stacks/worklists, no host stack dependency |

Run the complete existing language, MIR, runtime, malformed-input and standard-library corpus in addition to this catalog. The synthetic query tests are not substitutes for compiler semantics.

### 16.1 Differential sequence runner

Use one reusable source runner to execute arrays of API commands and emit structured records: import, open, demand, inspect, cancel, stage, commit, retire, release, collect. Replay the same normalized sequence against Rust and the source compiler.

Comparators separate semantic results, diagnostic identity/provenance, execution explanations, public dependency statuses, cache stats, retention counts, canonical bytes, and runtime outcomes. Preserve exact observable fields; ignore only explicitly non-contract internal identities.

Batch independent ordinary cases for throughput. Isolate hostile decoder, process-kill, memory exhaustion, filesystem failure, and crash-recovery cases in fresh supervised processes. Test negative outcomes by category and relevant details, not just nonzero exit status.

---

## 17. Format-aware bootstrap and release

### 17.1 Pin the complete closure

Lock compiler sources, canonical standard library, registry/generated sources if any, runtime bindings, target, optimization contract, source ordering, toolchain/format/verifier generations, and bootstrap limits. No source from the removed implementation is included.

The new compiler must implement full baseline language and operational behavior before the first complete compiler artifact is accepted. Intermediate library and query tests are development artifacts, not reduced compiler releases.

### 17.2 Preferred bootstrap when C0 can emit full G1

```text
C0(source closure, G1 contract) -> C1.grbc
independent grvm verifies C1
C1(source closure, same contract) -> C2.grbc
independent grvm verifies C2
C2(source closure, same contract) -> C3.grbc
independent grvm verifies C3
require bytes(C2) == bytes(C3)
```

This route is permitted only after an executable gate proves the *entire new compiler closure*, not a unit-return example, crosses the C0-to-G1 boundary.

### 17.3 Planned bridge when C0 emits only its private format

Do not block all source compiler work on a fictional direct G1 seed. Use an explicit, nonrelease bridge:

```text
C0(source closure, Stage0 format) -> B0.gvm
independent Stage0-format verifier/runtime admits B0
B0 runs the complete new Glorious compiler:
    B0(source closure, G1 contract) -> C1.grbc
independent grvm verifies C1
C1(source closure, same G1 contract) -> C2.grbc
independent grvm verifies C2
C2(source closure, same G1 contract) -> C3.grbc
independent grvm verifies C3
require bytes(C2) == bytes(C3)
```

B0 is the new full compiler executing under the existing Rust runtime, **not** the discarded self-host compiler and not a Rust semantic fallback. All parse/check/query/codegen work performed by B0 is the new source implementation. Its host imports contain only certified generic leaves/capabilities.

The distribution contains G1 C2. The bridge remains a reproducible bootstrap dependency until a direct seed route is certified. Keep the private format suffix and runtime explicit.

### 17.4 Manifest correctness

Record artifact format, schema, verifier contract, producer identity, source/codegen commitments, and exact bytes. Preserve the old manifest codec/API; introduce a separately versioned envelope where additional format-boundary provenance is required.

Lineage validation applies to every build edge. Byte convergence applies to the intended fixed-point pair, **not** to C0 versus C1 or B0 versus C1. Those artifacts need not have the same format or optimizer output. Producer ordinal and identity belong in provenance; do not embed changing predecessor hashes in canonical compiler code bytes in a way that makes convergence impossible.

Use actual file-byte equality in addition to digests for C2/C3. Verify each artifact independently before executing it. Convergence alone is not proof of language correctness: run all language and incremental/session contracts under C2.

### 17.5 Reproducibility matrix

Require fresh-process/no-cache builds, warm memo builds, unrelated prior query histories, reordered equivalent normalized input presentation, map-capacity variations, and independent build machines to produce identical successful canonical artifacts. Preserving the same source world is necessary; merely compiling files with the same names is insufficient.

Use proposed bootstrap-tool commands only after the tool is implemented. The sequences above are a specification, not an assertion that current CLI flags support them.

---

## 18. Performance, size, and operational budgets

These are proposed engineering targets, not measured results or promises about this implementation.

### 18.1 Cold and warm targets

Retain the repository's aspirational cold O2 self-compilation gate: **under 120 seconds and 4096 MiB** on a named reference machine/runtime/configuration. [R14] Include the full incremental compiler and canonical stdlib; do not meet the gate by omitting query/inspection APIs. Report source build, bytecode load/verification, and external supervision separately and state exactly which comprise the gate.

Add equally important incremental gates:

- Same-revision repeat demand invokes zero providers for fully retained memos; any observation/explanation work is reported separately.
- Private-body edits recompute the actual dependency cone, not every package body.
- Unrelated-file queries are not invalidated by a universal world-hash key.
- Cancellation reaches a safe point promptly on large inputs; use a provisional 50 ms p95 target on the reference machine and measure actual polling overhead.
- A scripted 10,000-edit history with automatic retirement and no intentional old pins reaches a stable memory plateau after capacity warm-up. Report live bytes separately from reusable capacity/RSS.
- IDE latency targets are calibrated after the first real body-query workload; provisional targets are 100 ms p95 for a warm single-body query and 250 ms p95 for a representative edit diagnostic, with exact workloads published.

Do not make fixed wall-clock failure categories part of semantic memo identity. For requests that succeed within their limits, output is deterministic. Resource-limited success/failure may legitimately differ with actual work and cache warmth where the preserved contract allows it.

### 18.2 Required metrics

Report provider executions, same-revision hits, parent candidates/reuses/rejections, dependency validations, recompute-green/red, recovery propagation, cycle outcomes, first-change reasons, memo products, dependency edges, execution explanations, payload shares, snapshot/product pins, retained/retired revisions, active/staged package scratch, and cache stats.

Also report per-phase/provider time, work charges, live/capacity bytes, interner occupancy, source/token/body counts, solver steps/depth, flow iterations, instance growth, MIR before/after counts, per-pass budgets, fragment reuse, final table/section bytes, verifier time, VM instructions/call depth, and host bytes/calls.

Counters that expose baseline behavior retain their definitions. New optimization counters do not silently redefine old hit/recompute or retention metrics.

### 18.3 Source budgets

Begin with an explicit review envelope of roughly **18–28 thousand nonblank, noncomment compiler lines**, including query/revision/session machinery, compatibility behavior, source VM-facing implementation, and generated adapters. This is a planning envelope, not a predicted achieved size. The library is counted separately, but compiler-specific code moved into it still counts toward total system cost.

Review each subsystem after M3 and M7; those milestones reveal representation and dual-format cost. Favor one shared engine and small family-specific providers. Crossing an envelope triggers design review, never deletion of a required API, an interpreter, diagnostics, or query functionality.

Measure distribution bytes by function/family/schema/constant section. Set hard artifact ceilings only after a full capability-preserving artifact exists; do not invent a binary-size claim from source LOC.

### 18.4 Optimization decisions driven by data

Prioritize repeated allocations, whole-world hashing/copying, full-state branch clones, recursive collection spines, redundant body elaboration, over-wide invalidation, serialized intermediate roundtrips, expensive handler dispatch, and duplicate monomorphization. Do not begin with a custom allocator, parallel compiler, new SSA framework, or a JIT before these basic costs are measured.

---

## 19. CI, risk controls, and completion

### 19.1 Required continuous checks

Restore PR/push validation for the replacement alongside the Rust oracle/VM. Every change runs contract-inventory completeness, forbidden-old-source/import checks, source capability tests, production query-engine tests, batched language/incremental cases, deterministic product tests, and affected format verification.

Nightly runs full differential histories, all language/runtime corpora, randomized edits and cancellation points, malformed files/cache entries/artifacts, bounded-resource workloads, and memory-soak tests. Bootstrap CI adds the complete B0/C1/C2/C3 route, byte equality, and independent builders once available.

Generate readiness from executed tests, not hand-edited status prose. A module reaches behavioral completion only when every mapped requirement has a valid passing comparator. A known unimplemented feature is not an "expected failure" proving parity.

### 19.2 Principal risks and mitigations

| Risk | Required mitigation |
|---|---|
| Replacing the old port but keeping its assumptions | Zero source dependencies and coverage reset; start with query engine, not scalar emission |
| Missing implicit dependencies | Context-only reads, absence/candidate-set observations, replay tests |
| Over-invalidating everything | Body/module/goal granularity and typed output projections |
| Reusing stale spans or arena IDs | Revision-qualified origins and product-qualified local IDs |
| History-dependent output | Deterministic optimizer contract, stable identities, relocatable fragments |
| Monomorphized engine bloat | Shared non-generic scheduler and typed provider/storage adapters |
| OOM from retaining every intermediate forever | Explicit ownership, product sharing, retirement, pins and budgeted admission |
| Breaking snapshots during reclamation | Safe-point collection and checked handle generations |
| Incompatible seed and release formats | Explicit dual-format schemas and B0 bridge gate |
| Handlers/borrows prevent practical authoring | Certified source profile, explicit provider states/worklists, narrow Stage0 fixes |
| Unsound universal fixed points | Family-specific SCC domains, limits and proofs |
| Native semantic fallback disguised as host support | Enumerated leaf capability audit and dynamically recorded host calls |
| Artificially low LOC target | Full compiler+support accounting and no feature deletion |

### 19.3 Definition of done

The new compiler is complete when all frozen Stage0 behavior and public APIs have executable source equivalents; all modes use the same typed query engine; recovery, dependency statuses, execution explanations, sessions, retirement, retention and caches pass their complete history tests; and all source-language, MIR, runtime, diagnostic and format contracts compare successfully.

It must retain queryable immutable intermediate products, never mutate an old snapshot, never reuse a result without complete dependency proof, and never publish a partial successful request. It must run without the old self-host tree and without Rust semantic callbacks.

The full incremental compiler must build itself through the recorded bootstrap chain; its G1 output must independently verify; C2 and C3 must be byte-identical; cold/warm/history-varied outputs must agree; and the published resource/latency/retention gates must pass on their specified workloads. Any unmet item remains a named blocker rather than a reduced release scope.

**The desired result is not a small batch compiler with incrementality added later. It is a compact compiler database whose queries perform compilation, and whose complete implementation happens to be written in the language it compiles.**

---

## Evidence and source references

All repository references below are pinned to the reviewed head unless they explicitly name the frozen baseline. No private access tokens appear in these references.

- **[R01] Reviewed repository revision.** `8cf378a1f19617e3aeddb18cada22540730323cc`, branch metadata read for this plan: https://github.com/MalekiRe/glorious/commit/8cf378a1f19617e3aeddb18cada22540730323cc
- **[R02] Frozen behavioral baseline.** `docs/self-host-stage0/baseline.toml`: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/docs/self-host-stage0/baseline.toml
- **[R03] Query products, frames, completeness and retention.** `crates/grandiose-stage0/src/query.rs`: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/crates/grandiose-stage0/src/query.rs#L1-L275
- **[R04] Query execution, cancellation, parent reuse and publication.** Same source: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/crates/grandiose-stage0/src/query.rs#L375-L805
- **[R05] Revision/package/session ownership types.** `crates/grandiose-stage0/src/revision.rs`: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/crates/grandiose-stage0/src/revision.rs#L1-L360
- **[R06] World import, snapshot admission, weak parents and retirement.** Same source: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/crates/grandiose-stage0/src/revision.rs#L450-L775
- **[R07] Typed dependency statuses and recompute-green behavior.** `crates/grandiose-stage0/src/dependency.rs`: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/crates/grandiose-stage0/src/dependency.rs#L1-L320
- **[R08] Persistent artifact cache contract.** `crates/grandiose-stage0/src/artifact_cache.rs`: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/crates/grandiose-stage0/src/artifact_cache.rs#L1-L270
- **[R09] Recovery propagation, lossless lexing, delimiter errors and UTF-16 tests.** `crates/grandiose-stage0/tests/source_and_query.rs`: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/crates/grandiose-stage0/tests/source_and_query.rs#L140-L420
- **[R10] Language ownership and control semantics.** `glorious-branded-environment-core-spec.md`: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/glorious-branded-environment-core-spec.md
- **[R11] Canonical source standard library.** `stdlib/src/lib.glorious`: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/stdlib/src/lib.glorious
- **[R12] G1 container and runtime contract.** `docs/bytecode.md`: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/docs/bytecode.md
- **[R13] Recorded old seed-format interoperability caveat, used only as a risk to retest.** `docs/self-host-stage0/performance-baseline.md`: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/docs/self-host-stage0/performance-baseline.md
- **[R14] Existing resource aspirations and prior architecture.** `docs/architecture.md`: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/docs/architecture.md . This plan supersedes its batch-only architectural assumptions for the replacement, not the language/bytecode contracts.
- **[R15] Full existing public surface and bootstrap commitments.** `crates/grandiose-stage0/src/lib.rs`: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/crates/grandiose-stage0/src/lib.rs ; `bootstrap.rs`: https://github.com/MalekiRe/glorious/blob/8cf378a1f19617e3aeddb18cada22540730323cc/crates/grandiose-stage0/src/bootstrap.rs
- **[R16] Primary external reference for red/green query validation.** Rust Compiler Development Guide, “Incremental compilation in detail”: https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html . Consulted September 4, 2026; background algorithm reference, not authority for Glorious's public trace semantics.
- **[R17] Primary external reference for explicit fixed-point cycle domains.** Salsa, “Cycle handling”: https://salsa-rs.github.io/salsa/cycles.html . Consulted September 4, 2026; background for convergence requirements, not a recommendation to adopt Salsa's implementation or panic policy.

**Verification boundary:** This plan was based on repository source and contract inspection. The Rust suites, new authoring capability probes, and proposed replacement tests were not executed while preparing it. Every proposed performance number and new API is a target, not an observed result.
