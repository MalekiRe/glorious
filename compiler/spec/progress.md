# GSC-2 implementation state

No milestone or compatibility contract is considered passed just because its
types exist. The executable source tests currently exercise kernel components
and initial source products, not a complete compilation pipeline.

## Present

- Fresh source closure with no old self-host imports; canonical standard
  library byte buffers, bounded cursors, and BLAKE3 bindings.
- Owner/database/generation-qualified storage, slot reuse, and capacity checks.
- Exact 256-bit file identity checked against the Rust formula.
- Cancellation and checked work/memory counters with explicit cleanup.
- Immutable revision worlds, active-world deduplication, parent admission,
  snapshot pins, idempotent retirement, and one-slot collection steps.
- Nested transaction marks, retained outer undo, and value publication guarded
  by a final cancellation check.
- Query first-observation journals, duplicate-read consistency, transitive
  recovery, transactional value+journal preparation, and ordered replay that
  stops at the first changed observation.
- A shared non-generic query state machine with revision-qualified memos,
  pinned request sessions, ancestry-only cycles, independent waiters, and
  immediate-parent replay. Typed key/product storage uses small generic
  adapters. Executed database histories cover cache hits without provider
  work, cancellation before hits, failed-owner takeover, committed children
  surviving parent failure, strict recovery checks, and transitive recovery.
- Reuse commits the candidate's existing product, not a provider substitution.
  Changed-selector replay stops before the obsolete branch and recomputation
  replaces its journal. Combined retirement removes memo, dependency,
  explanation, and product ownership together; shared products survive while
  the live revision still owns them.
- A source canonical dependency ledger with typed semantic nodes, exact byte
  ordering, sorted/deduplicated edges, and an explicit graph-validation stack.
  Histories cover unchanged values after changed inputs, dependency-identity
  changes, immediate-parent branch selection, cycles, missing evidence,
  cancellation, capacity/work failure, and stale-parent staging rejection.
  The combined request publisher now owns this ledger; three new integrated
  histories pass. See [dependency-ledger.md](dependency-ledger.md).
- A request-owned package lifecycle registry connected to pinned-world
  admission and the engine's actual request controls. Executed source histories
  cover checked session/body authority, active-scratch rejection, canonical
  all-package validation, commit/rollback counters, cancellation, shared query
  budgets, and stale session generations. No package-only commit is exposed
  by the database. See [package-sessions.md](package-sessions.md).
- A stepped canonical diagnostic-batch builder with exact fact/presentation
  ordering, merged/deduplicated provenance, span validation, error suppression,
  request fingerprint binding, and cancellation-safe final extraction. Source
  results compare every observable field against the Rust reference; separate
  failure histories check discarded staging. See [diagnostics.md](diagnostics.md).
- Three integrated request-publication source histories pass, exercising an
  opaque affine result adapter, authenticated world/span observations, shared
  controls, all-package preparation, error-batch rejection, and one final
  ledger/package commit. Public rows retire with unpinned revisions. Actual
  compiler outcomes/providers and physical resource certification remain open;
  see [request-publication.md](request-publication.md).
- Explicit final-owner product disposal now suspends collection and inspection
  until a database/slot/generation-qualified release token is acknowledged.
  Focused source histories verify retained shared products, move-only payloads,
  wrong-database rejection, blocked advancement, and one-shot acknowledgment.
  The source registry now connects actual typed stores to this handoff; see
  [query-registry.md](query-registry.md).
- Concrete immutable UTF-8 source blobs and stepped line/UTF-16 indexes are
  implemented. The first executable source-product comparisons pass against
  the Rust reference, including empty files and invalid byte offsets; failure
  histories cover discarded work and revision substitution. These products
  are registered as the first concrete compiler providers. See [source-products.md](source-products.md).
- Sealed logical paths and stepped source admission preserve the reference
  identity/digest/UTF-8 validation order, exact failure fields, cancellation,
  work retention, and one-shot extraction. An audited 100-check fixture
  compares Rust-generated inputs and drives two real registry line queries.
  This is a normalization component, not a complete admitted world; see
  [source-admission.md](source-admission.md).
- Canonical source collections now use a stepped stable index merge sort,
  byte-stepped package/path comparisons, and complete validation before
  duplicate rejection. The sealed result retains all admitted source fields
  and feeds the bootstrap-stage validator. The audited fixture passes 20
  reference cases, 238 collector lifecycle checks, 33 sorting cases, one
  bootstrap handoff, and 21 sorting-protocol checks. All six selected
  admission/publication/registry entries pass together in 243.80 seconds;
  complete request worlds and physical performance certification remain open.
- Stepped, sealed package-alias and capability admission now matches exact
  Rust spelling/error rules, including the complete Unicode whitespace set,
  cancellation at each transition, byte limits, and one-shot cleanup. The
  audited 719-check fixture passes. Whole-request namespace admission now
  handles source/root package deduplication, deterministic alias collisions,
  sorted capability sets, validation-before-duplicate precedence, and exact
  String-keyed lookup. Its audited tuple `[22, 116, 8, 7, 11]` also covers the
  shared text sorter, capacities, cancellation, cleanup, and one-shot extraction.
  The remaining normalized-world integration and exact world fingerprint are
  still required for complete normalization.
- Canonical option-map admission now passes `[14, 108, 10]`, retaining ordinary
  map replacement semantics and exact canonical key/value rows. The fixture
  covers lookup, consuming extraction, cancellation, cleanup, and capacities.
  It also passes with namespace, runtime-manifest, and registry fixtures in the
  audited four-entry run (238.76 seconds). This is selected-test evidence, not
  a complete source-suite or compiler-service certificate.
  See [source-admission.md](source-admission.md).
- Source runtime-role metadata and stepped manifest-input admission now pass
  `[69, 183, 648, 1, 20]`: full canonicalization/error cases, all 183 valid roles,
  all 648 scalar conversion shapes, an exhaustive lifecycle property, and
  resource boundaries. A shared role/tag witness inventory also passes native
  validation. No primitive authority or conversion opcode was added. Complete
  declaration binding, normalized-world integration, and fingerprints remain open.
- The current nine-entry admission/publication/registry group passes together
  in 381.31 seconds (`run-wf_8rujk`) after the Slice owner-lifetime corrections.
  All three publication scenarios and eight registry histories retain their
  expected results. The source lock passes its audit and the existing command,
  memory, and VM guards are unchanged. This does not replace the last full
  source-suite timeout or establish complete normalized-world integration.
- Source-owned bootstrap-stage admission consumes real admitted blobs, checks
  producer/predecessor provenance, counts and stepped byte totals, and exact
  optimization-option spelling in reference failure order. The source request
  types now include all six modes, complete build generations, and stage limits.
  The audited fixture passes 145 reference cases, 80 lifecycle checks,
  and 13 build/mode checks, including exhaustion at every transition. It also
  passes alongside the current source/name admission, publication, and registry
  batches (five native entries, 223.51 seconds). Full request normalization is
  still open. See [source-admission.md](source-admission.md).
- Focused Stage0 request/bootstrap identity corrections separate adjacent
  option/capability/runtime-input sections and bind host imports and semantic
  generations into bootstrap commitments. World/projection domains are v2,
  canonical cache generation is 4, and bootstrap-manifest schema is 3; VM
  formats and artifact bytes are unchanged. The 1,330-test native regression
  run passes. See A18 in [authoring.md](authoring.md).
- A closed `SourceBytes`/`LineIndex` registry with separate typed stores,
  sealed product references, tracked pinned-world input reads, and explicit
  provider frames over the shared scheduler. Executed histories cover real
  source-child demand, memo hits, unchanged/changed parent observations,
  shared-product last-owner release, pinned retirement, waiter takeover after
  owner cancellation, session-owned abandoned-builder cleanup, repeated
  capacity/work failures without leaked staging, and retry after exhaustion.
  The initial histories use trusted input adapters; a separate end-to-end
  history now drives this registry from fully normalized requests with sealed
  fingerprints. Committed source journals now derive canonical input facts
  for atomic publication; the later families' projections remain open.
- Stepped interner reclamation over a shared non-generic root walker. Roots
  include pending attempts, active journals, suspended replay reads, and
  retained memo keys/journals. Typed sweeps release map and arena residents,
  preserve checked generations, and report live keys separately from allocated
  slots. Histories pass for successful/failed 16-file churn with a one-slot
  capacity, pinned retirement, active builders, and replay-only key ownership
  after parent collection. Every collection phase keeps semantic admission,
  inspection, query stepping, and cleanup blocked. This is logical retention
  evidence, not physical memory-soak certification.
- Reference public-API inventory, reference Rust test inventory, specification
  acceptance inventory, and source-capability CI with generated run evidence.
- Regressions for Stage0 nested borrowed aggregates and lexical shadowing;
  measured opt-in execution of long owned-state and borrowed-state loops.
  Borrowed loops preserve surviving owners and returned unique loans; local
  loans prevent frame recycling, and work/allocation limits remain enforced.
- Source-owned open-addressed maps and sets with cached hashes, geometric
  growth, tombstone cleanup, and dense move-only residents. Rehashing changes
  index metadata only; deletion repairs the relocated resident's bucket.
  Mutable value lookup and whole-entry removal preserve owner provenance.
- A thread-local, test-only allocator meter separates physical allocation
  requests from logical VM charges. Initial map measurements confirm indexed
  lookup work but expose substantial size-dependent copying; see
  [runtime-costs.md](runtime-costs.md).
- Ordinary calls retain surviving shared owners and reuse frozen captures.
  Cross-call effect payloads, forwarding, and resumption results translate
  reference coordinates at their frame boundaries. Focused source histories
  cover shared borrowed payloads/results and replay without weakening local
  unique-loan escape rejection.
- Vector element/slice accessors carry explicit owner lifetimes, including
  nested map-owned element loans. C0's trait-instance linking distinguishes
  undemanded bodies from reachable missing specializations while preserving
  source checking of both. See A10/A11 in [authoring.md](authoring.md).
- Stage0 now seeds hidden reference-bearing parameter fields from their
  frozen interface layout, not just explicit field accesses in the caller.
  The minimized Core and executable slice/string-view regressions pass while
  opaque-layout and unique-owner misuse remain rejected. The broader selected
  native run passes 1,462 tests. See A20 in [authoring.md](authoring.md).
- Slice element accessors now carry explicit owner lifetimes, with a failing-
  before/passing-after executable regression. Malformed floating runtime roles
  now return input errors instead of panicking during normalization, without
  changing any valid tag or encoding. The latest separate regression runs pass
  1,335 selected native tests, 126 standard-library tests, and eight conversion
  tests. See A21/A22 in [authoring.md](authoring.md).
- Trait-method call applications now receive the lifetime substitution already
  established by their checked invocation contract, like ordinary function
  applications. A reduced nested map-lookup regression executes successfully;
  local-owner escape still receives `G5017`. Separate native regression runs
  pass 1,424 tests. See A23 in [authoring.md](authoring.md).
- The whole-request builder, sealed world adapters, and complete framed world
  fingerprint encoder pass 56 successful-input reference cases, 27 exact
  cross-component failure comparisons, and cancellation/resource lifecycle
  histories. Real normalized requests now drive registry deduplication, source
  reuse across unrelated request changes, observed-source invalidation,
  pinned old products, and last-owner retirement. All 47 source-suite entries
  pass together in 65.94 seconds (`run-jgx73yx0`). Physical allocation and
  polling certification remain open; see [source-admission.md](source-admission.md).
- Stage0 completion expressions now lower through typed value joins when
  nested in operands, initializers, subjects, or selected arms. Eight executable
  reduced cases cover strict order, scope, affine values, and a single-owner
  mutable-reference return. Ambiguous multi-owner callable returns retain
  their existing fail-closed contract. See A24 in [authoring.md](authoring.md).
- Ordinary trait-backed `as<Target>(value)` and context-inferred `as(value)`,
  including all integer/float pairs, user-defined conversions, and preserved
  ownership/effect checks. Authoring regressions cover direct f32 rounding and
  signed-zero-preserving float negation; this is not G1 bootstrap certification.
- Source query publication now traverses checked committed observations and
  stages the reference ledger's exact input facts, independent of execution
  provenance. Cold, memoized, reused, recomputed-green, and changed-input
  histories pass, including normalized worlds, capacity/work rejection,
  foreign-owner/collection checks, and cancellation at all 24 preparation
  boundaries. See [query-registry.md](query-registry.md). This publishes a
  real typed source-query result, not a complete compiler package outcome.
  The full expanded source suite passes 48 entries in 72.46 seconds
  (`run-3x54nfxx`), with unchanged source-lock audit and resource guards.
  The full Rust workspace passes 2,450 tests in 78.520 seconds, with zero
  failures and the two existing ignored manual VM benchmarks.

## Gates still open

M0: complete the diagnostic/CLI/format inventories and executable per-export
comparison assignments. Public inventory entries are plans, not passed tests.

M1: certify transport/control polling, the remaining state-loop/continuation
cases, interner/map scaling, full allocation/copy accounting, and physical
representation costs.
HashMap probes and metadata rebuilding use tail calls; collision and growth
costs still require compiler-scale measurements. VM aggregate transfer can
rebuild backing objects. Logical storage limits and allocation charges do not
establish compact physical storage. G1 substrate certification is outstanding.

M2: finish the compiler-family registry beyond the first two source providers
and extend the capability-limited provider protocol to the remaining families.
Kernel histories use synthetic products, while separate registry histories
now exercise actual source/index products and driver-recorded observations.
The remaining per-family product stores and roots,
hierarchical controls and memory leases, canonical dependency projections for
the remaining providers, request-wide
publication of actual package products, and the full cancellation/retention
history corpus remain open.
The current engine is
not CompilerDatabase API parity, and the retirement test is not a memory-soak
or physical allocation certification.

M3–M10: implement the remaining source/query
providers, term and solver engines, complete body
semantics, generic Core/MIR, verified backend formats, service dispatch,
self-compilation, C2/C3 convergence, and performance gates.

The next critical work is finishing M1's collection/runtime contract and M2's
closed registry, provider capabilities, and physical resource/product ownership
contracts. The combined publisher now has both synthetic transaction histories
and real typed source-query results with derived input facts; it does not yet
publish complete compiler request outcomes.
No lexer-first or scalar compiler prototype is being substituted for that
architecture.
