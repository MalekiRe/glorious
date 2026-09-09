# GSC-2 implementation state

No milestone or compatibility contract is considered passed just because its
types exist. The executable source tests currently exercise kernel components
and initial source products, not a complete compilation pipeline.

## Current source-authoring revalidation (September 8)

The later cache-56 regression run includes all 60 GSC2 source tests
(`target/integer-const-literal-baseline-v1.log`). The source test target
completes in 512.59 seconds with zero passes and 60 failures, all during
production-closure compilation rather than VM execution. The repeated
diagnostics include immutable locals/parameters requiring audited mutable
bindings (`G4220`), cross-module private-field access (`G4140`), and further
inference, assignment, coverage, and temporary-loan failures. The normal
100-error diagnostic cap is reached with 63 additional errors suppressed.
No visibility, mutation, or ownership checks were relaxed. This completed
source-test result supersedes isolated probes as a current failure baseline;
it is not a successful authoring gate or self-hosting milestone.

September 8 revalidation supersedes the green source checkpoint below. A full
workspace test attempt reached GSC2 failures and exhausted its 590-second
budget before completing the workspace; it is not a completed acceptance run.
The isolated `gsc2_byte_buffer_writes_a_complete_word` probe also fails while
checking the complete production source closure. Its initial diagnostics
identify world-fingerprint accesses to fields made private by the language's
private-by-default rule, not a byte-buffer execution failure.

The identity wrappers and runtime-manifest input records now explicitly grant
crate-scoped field access; their previously explicit private fields remain
private. The follow-up probe in `target/tuple-gsc2-visibility-v2.log` advances
past those world-fingerprint failures and finds further source migration work:
registry accesses to query/engine records and mutable locals still written
with immutable `let`. It fails after 108.11 seconds with the normal diagnostic
limit, not by weakening visibility, mutability, ownership, or runtime gates.
The remaining source APIs and bindings require audited migration and full
source-gate revalidation. Self-hosting and release readiness remain unproven.

The last completed source gate (September 7) passed all 60 tests in 415.72 seconds after adding
the lossless lexical provider and its typed registry family
(`target/compiler-check/run-8wjo_51m/report.json`). All 62 execution records
retain the existing 12 workers/limits and `release_ready: false`; all 36
profiled runs finish with zero raw/home live bytes and unsaturated counters.
The lexical corpus compares all token/recovery/spelling/pairing fields for
357 reference inputs, while separate histories check stepped cancellation,
backing preflight, reuse, failure, retirement, and atomic public input facts.
The wider selected authoring run has 1,101 passes and the same 15 previously
recorded failures. All 175 standard-library and 28 native-bridge tests pass.
See [lossless lexical products](lossless-lex.md) for the exact scope, enabling
region-invariance correction, and measurements. Declaration scanning, headers,
semantic compilation, emission, and self-host bootstrap remain outstanding.

The preceding full source gate passed all 56 tests in 399.31 seconds after fixing
call-context lifetime inference and detached higher-ranked layout obligations
(`target/compiler-check/run-mg43ga9e/report.json`). All 58 records retain the
existing 12 workers/limits and `release_ready: false`; all 32 profiled runs
finish with zero raw/home live bytes and unsaturated counters. The copy batch
retains its 33-frame depth and prior artifact/backing/work measurements.
All 28 native-bridge tests now pass. The wider selected authoring run has
1,095 passes and 15 remaining failures, including two lifetime-suite ownership
failures reproduced with identical diagnostics on the pre-fix compiler.
See [call-context lifetime evidence](call-context-lifetimes.md) for the five
new source regressions, two layout checks, and baseline comparisons.

The preceding full source gate passed all 56 tests in 395.95 seconds after the
native owner-move and fixture revalidation
(`target/compiler-check/run-uin4h5j2/report.json`). All 58 records retain the
existing 12 workers/limits and `release_ready: false`; the 32 profiled runs
finish with zero raw/home live bytes and unsaturated counters. The copy batch
retains its 33-frame depth and previous backing/work measurements. The broader
selected authoring suites pass 712 tests with six failures, including one
remaining native lifetime-specialization blocker now reduced to a source-only
seven-line case. All 19 general-memory tests pass; the owned native Pair
roundtrip passes its unchanged two-slot memory cap. See
[native fixture evidence and the minimized blocker](unsafe-memory-progress.md#native-fixture-and-owner-move-revalidation-september-7).

The preceding full source gate passed all 56 tests in 368.27 seconds after bounding
the source library's comparison, UTF-8 validation, and vector-growth stack costs
(`target/compiler-check/run-28gl455c/report.json`). The copy/cancellation batch
now reaches 33 frames instead of 8,234, with a 4,720-byte native-home peak instead
of 197,456 bytes. All 171 standard-library tests pass, including 16,417-element
ordinary/authoring runs under a 128-frame cap and 51 UTF-8 oracle cases.
The 58 source execution records retain 12 workers, existing resource limits,
and `release_ready: false`; all 32 profiled runs finish with zero live raw/home
bytes. These traversals have logarithmic stack growth, not general constant-stack
compiler execution. The copy batch uses more logical work ticks; see the
[measured tradeoff](native-costs.md#library-stack-depth-localization).

The preceding full source gate passed all 56 tests in 362.25 seconds with native
backing-storage measurements (`target/compiler-check/run-51ln7pdm/report.json`).
All 58 execution records preserve the existing limits and 12 workers and retain
`release_ready: false`. The 32 profiled executions finish with zero live raw
and native-home backing bytes and no saturated counters; the 26 unprofiled
records leave those fields empty. See [native cost evidence](native-costs.md)
for scope, additional native-suite failures, and remaining stack-cost work.

The preceding full source gate passed all 56 tests in 353.67 seconds after the
nested-pattern coverage and nonreturning-call authority fixes
(`target/compiler-check/run-6rjmwza6/report.json`). Its 58 execution records
retain the existing limits and workers and `release_ready: false`. The source
copy provider uses the directly nested patterns from the minimized blocker;
its focused history also passes in 125.52 seconds. The closure-tracking
regression passes unchanged.

The preceding full source gate passed all 56 tests in 350.38 seconds, including
resumable source copying, UTF-8 chunk boundaries, and cancellation of owned
partial buffers (`target/compiler-check/run-93dk84z7/report.json`). Its 58
execution records retain the existing limits and workers and
`release_ready: false`. The new focused copy history also passes independently
in 105.32 seconds; the closure-tracking regression passes unchanged.

The preceding full source gate passed all 55 tests in 343.49 seconds, including
automatic source/line-index backing reservations and independent phase/root
ownership through request close, reuse, and final disposal
(`target/compiler-check/run-9hgug8g_/report.json`). Its 57 execution records
retain the existing limits and workers and `release_ready: false`.
Seven focused standard-library vector/destruction tests also pass, including
the new capacity-preflight comparator and unchanged native-allocation guards.

The preceding full source gate passed all 54 tests in 318.64 seconds, including
retained phase-lease growth/close and typed-store staged-publication cleanup
(`target/compiler-check/run-all572xe/report.json`). Its 56 execution records
retain the existing limits and workers and `release_ready: false`.

The preceding full source gate passed all 53 tests in 317.23 seconds, including
retained product-memory ownership, cancellation, and rejected publication
(`target/compiler-check/run-z_95s4k3/report.json`). Its 55 execution records
retain the existing limits and workers and `release_ready: false`.

The preceding full source gate passed all 52 tests in 297.35 seconds, including
request-owned hierarchical reservations and exact cold/memoized query histories
(`target/compiler-check/run-5o47hyfl/report.json`). Its 54 execution records
retain the existing limits and workers and `release_ready: false`.

The preceding full source gate passed all 51 tests in 291.53 seconds, including
the [hierarchical budget histories](operation-budgets.md)
(`target/compiler-check/run-n4lywn96/report.json`). Its 53 execution records
use the existing limits and workers and retain `release_ready: false`.

The preceding full source gate passed all 48 tests in 279.09 seconds after the
MIR pipeline and binding-pack changes (`target/compiler-check/run-d63yok2j/report.json`).
The unfiltered report contains 50 execution records, uses the existing 12
workers and resource limits, and records `release_ready: false`. This is source
kernel/request/registry evidence, not a fresh workspace-wide pass or C2/C3
convergence. Known Stage0 integration failures remain outside this source gate.

The source audit previously failed before execution because its authoring
allowlist retained a deleted legacy bridge. It now fingerprints the Stage0
manifest and complete recursive Rust source tree, including the new lowering
and validation modules. A regression checks additions, edits, removals, and
manifest changes. The refreshed lock records these current inputs without
marking any of the 11,455 open public contracts complete; `--release` still
rejects missing full comparisons and verified bootstrap convergence.

## Current prerequisite

The authoring runner now records [native backing-storage costs](native-costs.md)
at allocation/release events, with separate raw-buffer/native-home counters,
combined peaks, and explicit bulk-copy bytes. Source-copy cleanup also checks
actual native backing returns to zero. This does not replace request-budget
accounting or certify allocator internals, complete VM costs, or host polling.

Stage0's authoring coverage proof now handles split finite constructors inside
`Result` while leaving integer/generic error payloads open. Completion and effect
handlers preserve correlated fields and reject collectively unreachable arms.
Nonreturning calls also enforce their effect and generic-bound contracts unless
operand evaluation prevents entering the call. The minimized failures and
decoded-bytecode regressions pass; the broader authoring run retains the same
13 previously recorded Core/destruction/VM failures
(`target/nested-coverage-authoring-full.log`). No frozen parity contract is
closed by these authoring fixes.

The source kernel now has a [hierarchical budget pool](operation-budgets.md)
with ancestor-first admission, checked leases, generational retirement, and an
explicit abandoned-reservation close scan. Registry requests now own source/
line-index family pools and charge the actual request-memory counter, reclaiming
reservations before pin release. The generic database now transfers explicit
product charges from computing attempts to final-owner disposal, retaining a
separate counter after the producing request closes. Source-copy and line-index
backing allocations now acquire both shared-root and phase reservations before
allocation, transferring them to typed stores through final disposal. Full
allocation accounting remains open; this does not complete M1/M2.

Source materialization now yields between UTF-8-safe chunks of at most 4 KiB,
using the actual request controls and retaining the prepaid destination buffer
across scheduler steps. Cancellation destroys partial copies before reservation
refunds. Initial capacity allocation is still synchronous; transport polling
and physical latency certification remain open.

Phase pools now support checked lease growth and explicitly retained leases
that survive the close scan. Typed-store publication and suspended-builder
cleanup destroy concrete values before attempt refunds. Registry pools now have
independent owners that survive producer close only while products retain them;
requests and revision pins do not survive with those owners. Admission rollback
undoes only rejected growth, preserving existing builders and spent work.
The accounting covers the copied source text and line-start backing capacities,
not allocator peaks, arena storage, temporary fingerprints, VM frames, or a full
physical allocation census.

The September 5 direction selects [host-compatible bytecode and unsafe
memory](unsafe-memory-progress.md) as prerequisite U0–U6 work. The compiler and
source libraries, including concrete generic specializations and unsafe
collection/UTF-8/hashing internals, must run as bytecode over a small raw-memory
layer. Shared-layout interop targets zero marshalling; initial VM/native tests
use host ABI fixtures. The Glorious LLVM backend and native Glorious std are
deferred until after working, verified self-hosting, not prerequisites of it.
Unsafe-enabled execution is not an in-process memory sandbox. Current distribution
ships source for local compilation. Independent admission of untrusted bytecode
and authenticated native safe exports are deferred, not prerequisite gates. Existing
tests do not certify these new capabilities, and recording the decision closes
no compiler milestone.

The shared raw-storage crate provides aligned uninitialized allocations and
explicit ownership handoff. Its earlier 13 unit and two native embedding tests
also passed Miri's strict-provenance checks; no new Miri run is claimed here.
U2 includes raw-pointer types, explicit unsafe scopes, unsafe callable/trait
contracts, and source-independent Core/MIR checks. Callable safety stays separate
from the unsafe-execution requirement, including on lifted bodies. Stage0 schema
106 executes machine leaves over actual host memory, including native-backed
checked references, with per-run byte budgets and explicit unsafe Rust execution
entry points. Source Vec, slices and UTF-8/collection consumers now use that
storage, with ordinary inherent functions and explicit Clone implementations.
Compiler dependency/diagnostic owners have been migrated to borrowed inspection,
explicit independent cloning and buffer transfer. Concrete destruction now
specializes generic owned parameters and traverses records, tuples and active
enum payloads, with initialized-field guards and ordinary source Drop calls.
Replacement, shadowed owners, destructor-held loans, constructor lifetime
inference and multi-origin reference returns have focused regressions. Owned
patterns now transfer their selected payloads and destroy residual fields;
ordinary source Vec destruction visits residents before freeing storage.
Handler resumptions have an explicit completion delimiter and synchronize
surviving source allocations across restored frames. See
[the resident-cleanup checkpoint](unsafe-memory-progress.md#source-owned-resident-destruction-and-handler-cleanup).
That historical frozen validation passes 2,577 workspace/all-targets tests and all 48
separately audited source entries: 2,625 total, zero failures, two existing
ignored manual benchmarks. The 172.79-second source run keeps its complete
batches and default budgets; no diagnostic budget increase is counted.
The subsequent [native bridge checkpoint](unsafe-memory-progress.md#native-calls-and-bytecode-callback-checkpoint)
adds actual capability-bound native calls and synchronous bytecode callbacks
over existing native homes, with full source contract matching and shared
execution budgets. Source-specialized Vec growth and resident Drop now execute
during native re-entry. Its historical frozen validation passes **2,640 tests**:
2,592 workspace/all-targets tests (including 15 native-bridge regressions) and
all 48 separately audited source entries in 171.55 seconds, with zero failures
and two existing ignored manual benchmarks.
The subsequent [native source-storage checkpoint](unsafe-memory-progress.md#native-source-storage-checkpoint)
establishes native homes for ordinary addressable locals with supported concrete
layouts, tracks partial initialization and source lifetime, and preserves their
addresses across native callbacks. Source Vec fixtures no longer construct a
second metadata home manually. Adjacent single-consumer field reads avoid
materializing unused aggregate fields, keeping the original source budgets.
This does not complete private Array/callable layouts and capture cleanup,
all control-flow cleanup, general owned/callable ABI, the independent G1
extension, or U4–U6.
Its frozen validation passes **2,646 tests**: 2,598 workspace/all-targets tests
(including 18 native-bridge regressions) and all 48 separately audited source
entries in 176.98 seconds, with zero failures and two existing ignored manual
benchmarks. The source report contains 50 execution records, no filters and
`release_ready: false`; every original batch, assertion and VM limit remains.
The [synchronous owned ABI checkpoint](unsafe-memory-progress.md#synchronous-owned-native-abi-checkpoint)
adds producer-established aggregate argument homes, preallocated caller result
slots and native-caller callback parameter storage. Owned source Vec values
cross both directions with bytecode growth and exactly-once resident cleanup.
This does not establish durable external ownership, general callable ABI,
selected drop-code identity, complete exceptional cleanup or U4 completion.
Its frozen validation passes **2,651 tests**: 2,603 workspace/all-targets tests
and all 48 source entries in 168.02 seconds, with zero failures and two existing
ignored benchmarks. All original batches and limits remain; the 50-record
source report is unfiltered and still records `release_ready: false`.

The [native destructor contract checkpoint](unsafe-memory-progress.md#native-destructor-contract-checkpoint)
retains the source-selected destruction entry and its emitted transitive code
identity for every native-reachable concrete resident, including return-only
referents. Native code can invoke that entry synchronously without a separate
source callback parameter, and bindings check the allocation-domain protocol.
This still does not bind every selected copy/use/quantity operation, provide
durable external owners or establish the complete shared ABI. Root lowering now
preserves lexical cleanup when a short-circuit probe declines, and releases
prefix owners on normal short-circuit exits. The authoring runtime reuses empty
returned call-register buffers; native-to-native ordinary argument copies avoid
intermediate aggregate boxing while preserving distinct callee storage.
Its frozen validation passes **2,658 tests**: 2,610 workspace/all-targets tests
and all 48 audited source entries in 174.90 seconds, with zero failures and two
existing ignored benchmarks. The original bootstrap result `[145, 80, 13]`
uses 7,699,624 charged elements, below its unchanged 16,777,216-element ceiling.
The unfiltered source report contains 50 executions and still records
`release_ready: false`.

The [source BLAKE3 checkpoint](unsafe-memory-progress.md#source-blake3-checkpoint)
replaces the public library's opaque hash bridge with source-defined compression,
chunk processing and tree reduction over borrowed bytes. All 32 output bytes
are reference-checked across empty, block/chunk boundary, large-tree and mutated
owned-window inputs; internal chaining values also retain high counter bits.
Compiler identities now execute this source algorithm. The legacy artifact
opcodes retain their meanings but are absent from emitted source hash programs;
this is not a completed shared ABI, semantic compiler or bootstrap loop.
Its frozen validation passes **2,661 tests**: 2,613 workspace/all-targets tests
and all 48 audited source entries in 178.29 seconds, with zero failures and two
existing ignored benchmarks. All 50 recorded results match the preceding
checkpoint. Bootstrap retains `[145, 80, 13]` with 38,550,344 work ticks and
5,880,146 charged elements under its unchanged limits; release readiness is false.

The subsequent [nested Boolean value checkpoint](authoring.md#a32-nested-lazy-boolean-values)
fixes an authoring-lowering defect exposed by the hash comparator. Nested lazy
Booleans now use typed CFG joins in strict expression positions and lifted
closures, with exact evaluation-order and selected-branch destruction tests.
Its frozen validation passes **2,664 tests**: 2,616 workspace/all-targets tests
and all 48 audited source entries in 180.46 seconds, with zero failures and two
existing ignored benchmarks. All 50 recorded results match the source BLAKE3
checkpoint. No opcode, budget or release-readiness contract changes.

The [owned capture checkpoint](authoring.md#a33-owned-callable-environment-destruction)
adds concrete environment destruction, normal invocation residual-state
restoration, independent source copies and borrowed native-home write-back.
The source loop's tail-call regression is fixed without skipping registered
source destructors. Its frozen validation passes **2,670 tests**: 2,622
workspace/all-targets tests and all 48 audited source entries in 177.89 seconds,
with zero failures and two existing ignored benchmarks. All 50 results match
A32, including the complete bootstrap and registry batches. Exceptional capture
cleanup, complete U4–U6, the source semantic compiler and C2/C3 remain open.

The [shared frame ownership checkpoint](authoring.md#a34-shared-frame-ownership-and-cancellation-cleanup)
adds compiler-selected cancellation cleanup using the same owner inventory as
normal returns. Capture loans transfer residual slots back when an invocation
ends, and abandoned-frame destructors retain checked caller write-back. Schema
106 seals frame plans and their executable/native reachability. Frozen validation
passes **2,685 tests**: 2,637 workspace/all-targets tests and all 48 audited source
entries in 175.59 seconds, with zero failures and two existing ignored benchmarks.
All 50 recorded results match A33 with original budgets unchanged. Other nonlocal
transfers, replay histories, complete temporary ownership and the broader U4–U6,
source semantic compiler and C2/C3 requirements remain open.

The [nonlocal label checkpoint](authoring.md#a35-nonlocal-label-frame-cleanup)
extends the shared destruction plan to abandoned ordinary frames, including
invocation capture handoff and outgoing owned payloads. Runtime label ownership
now identifies the executing specialization. Frozen validation passes **2,692
tests**: 2,644 workspace/all-targets tests and all 48 source entries in 185.92
seconds, with zero failures and two existing ignored benchmarks. All 50 results
match A34. Retained replay cleanup, general
temporary ownership and the other recorded source/compiler gaps remain open.

The [terminal value-CFG checkpoint](authoring.md#a36-terminal-strict-value-control-flow)
represents paths without a normal continuation explicitly, preserves bottom-first
completion inference, and evaluates computed callees before their arguments.
First-class tail-label helpers may also return normally. Frozen validation passes
**2,700 tests**: 2,652 workspace/all-targets tests and all 48 source entries in
188.40 seconds, with zero failures and two existing ignored benchmarks. All 50
results match A35. The source run includes a 15-second CPU sample, not a new
performance baseline. The remaining ownership and self-hosting gaps are open.

The [ownership-query performance checkpoint](authoring.md#a37-indexed-ownership-query-inputs)
indexes manual `Use` rules and shares frozen query inputs without sharing
answers or spent budgets. The isolated lifecycle test improves from 26.30 to
10.48 seconds with identical execution evidence. With 12 test workers and a
24 GiB cargo-test ceiling, validation passes **2,702 tests**: 2,654 workspace
tests and all 48 source entries in 50.03 seconds. All 50 complete execution
records match A36 exactly; VM limits and assertions are unchanged. This is an
authoring-throughput improvement, not additional source/compiler coverage.

The preceding source-cost checkpoint passed all 48 source entries, including the two
previously allocation-limited batches, after reducing source call-frame work.
The complete production closure, comparator batches and VM budgets are unchanged.
This does not certify full self-hosting or bounded physical work; current and
historical costs are recorded in the prerequisite evidence.

The historical unsafe-contract workspace checkpoint passed 2,491 tests (two existing ignored
manual benchmarks), 122.429 seconds wall including build; all 48 source entries
pass in 69.91 seconds. See the
prerequisite evidence above for the exact checkpoint and generation changes.

## Present

- Fresh source closure with no old self-host imports; canonical standard
  library byte buffers, bounded cursors, and source-defined BLAKE3 hashing.
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
- Mutable aggregate projections and fixed-size array updates now reuse unique
  backing and detach shared snapshots before writing. At 512 elements,
  sixteen writes request about 92% fewer bytes and no longer scale in physical
  allocation cost with the array size. Hash-table construction requests about
  15% fewer bytes at 64 entries. Artifact bytes, logical charges, and ownership
  rules are unchanged; resizing and whole-owner scans remain scaling work.
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

Historical verification after the copy-on-write runtime change: 2,455 workspace
tests passed, zero failures, two existing ignored manual VM benchmarks, in
84.670 seconds including an incremental build. All 48 source entries pass in
that run (73.71 seconds), with unchanged source audit. Earlier timings above
are historical checkpoints, not results for subsequent changes.

M0: complete the diagnostic/CLI/format inventories and executable per-export
comparison assignments. Public inventory entries are plans, not passed tests.

M1: certify transport/control polling, the remaining state-loop/continuation
cases, interner/map scaling, full allocation/copy accounting, and physical
representation costs.
U0–U6 supplies the new raw-memory/ABI and specialized source-library bytecode
contract. No LLVM backend or native-precompiled Glorious std is needed for this
gate; native Glorious comparisons follow verified self-hosting.
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
