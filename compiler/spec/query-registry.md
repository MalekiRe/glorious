# Closed source-query registry

`src/registry/registry.glorious` replaces runtime family registration at the
compiler boundary with the first two source-defined typed families. The
generic database stays a small storage adapter over the shared non-generic
engine, not a second engine per family. The specification's complete section 9
inventory remains in scope.

The first concrete providers are `SourceBytes` and `LineIndex`. Their
immutable products now exist in `src/source/source.glorious`, with initial
reference-comparison tests; see [source-products.md](source-products.md).
Their products live in separate typed stores; the memo
directory retains a checked sealed product-reference sum. Subsequent source,
interface, solver, body, MIR, and artifact families extend this closed sum and
its typed dispatch as their actual products are implemented. Two families alone
do not establish M2/M3 completion or the complete registry.

Provider frames own stable IDs, positions, and attempt-local builders. They do
not retain a unique database borrow across a child demand, wait, or yield. A
closed step protocol requests inputs/children or returns a typed product/failure. The
driver, not the provider, reads the pinned immutable world, constructs tracked
observations, propagates child completeness, validates products, and computes
their fingerprints. Arbitrary caller-supplied `Read` fingerprints remain confined
to the low-level test/storage adapter, not the compiler provider API. Raw source
input has a separate observation projection from query output. Replay resolves
checked typed keys and demands actual children. The line algorithm receives
only its immutable blob, builder, and actual request controls. The world driver
validates file identity and charges source copying before materialization.

Separate product stores require explicit final-owner release. The database now
offers `collect_step_with_products`: on the last memo owner it yields an opaque
affine `Released<V>` and stays in a releasing phase. The compiler registry may
borrow its value to remove the concrete store entry, then call `finish_release`.
The acknowledgment validates the original product's database/owner/slot/generation
and clears the token's value. Wrong-database acknowledgment leaves both tokens
and collection phases unchanged; completed tokens reject inspection/reuse.
Further collection and semantic/aggregate inspection remain blocked until
acknowledgment. The ordinary collector discharges self-contained owned values
through the same path.

The existing shared-product retirement history passes against this change
(71.15 seconds). The new move-only-product history also passes (72.03 seconds),
covering last-owner delivery, cross-database acknowledgment with otherwise
matching metadata slots/generations, blocked inspection/advancement, retained
payload bytes, and one-shot disposal. The concrete registry now owns the release
token, removes its corresponding typed-store entry, and acknowledges disposal
on a subsequent step. Its retained removal state makes acknowledgment retries
one-shot. Publication failure also releases a newly staged typed-store entry.

Session close owns cleanup even after a caller discards a query handle. It
cancels the actual request, rejects new query admission, then scans one driver
slot or drops one provider frame per step. Only after all attempts are gone
does it release the revision pin. Repeated close admission does not reset its
scan. Checked session generations prevent touching another request's driver.

The blob constructor accepts an admitted
`FileKey`, like the reference lexical API; it is not a substitute for full
`CompilationRequest::normalize`, package-alias checks, runtime manifests, or
the exact normalized-world fingerprint. Compiler providers receive a closed
input/child-demand protocol. Only the trusted registry driver may access the
pinned world and manufacture its journal observations.

The production registry is now also exercised through
`request::world::NormalizedWorld`: its public import facade obtains the
fingerprint from the sealed value, after all request components have been
validated. The original trusted-adapter histories remain useful isolated
engine tests; they are no longer the only exercised admission path.

## Executable evidence

`tests/registry/source.glorious` supplies real source blobs and drives the public
registry API. The native harness independently decodes/verifies each serialized
G0 program before execution. Separate cases exercise:

- Cold line demand, tracked source-child creation, both memo hits, exact source
  bytes/index contents, and retirement of both typed products: 35 assertions.
- Three real worlds: an unrelated-file edit reuses existing source/index
  products; an observed-file edit rejects reuse and builds new products.
  Pinned retired revisions remain readable, shared products outlive the first
  owner, last-owner disposal releases them, and cross-revision value access
  is rejected: 96 assertions.
- Two requests for one line index: the second waits rather than reporting a
  cycle, takes over after cancellation of the first request's partial builder,
  and consumes its already committed source child. Closing also discards an
  abandoned builder whose public query handle was dropped: 47 assertions.
- Exhausted source/line stores, driver/frame admission, byte/line ceilings,
  and a zero work budget. Each failure is repeated to detect leaked staging;
  successful children remain retained, failed parents do not. A fresh request
  can complete after work exhaustion: 235 assertions across seven cases.

All four cases pass. The cold case plus three dependency-ledger regressions
pass together (144.94 seconds); the cold/reuse pair passes (119.80 seconds);
the interleaving history passes (110.65 seconds), as does the capacity/work
history (112.31 seconds). These are focused executions,
not full-suite results. The newer complete run below supersedes their scope.

## Remaining contracts

The registry now owns and reclaims its key tables, with roots from active
attempts, committed journals, and suspended replay. Future families must add
any additional product/lease roots they introduce. Ground goal/term
identities, dependency projections for the remaining providers,
complete compiler request-outcome publication, hierarchical leases,
physical-cost certification, and the remaining families remain open. Logical
work charges do not establish physical VM copying or host-polling bounds.
The isolated partial-catalog adapter is not the normalized-world contract; the
new end-to-end history uses the complete fingerprint and admission facade.
No lexer, semantic frontend, G1 emission, or
self-compilation is implied by these histories.

### Provider-derived input facts and typed result publication

`begin_publication` accepts an existing checked typed query value, not an
arbitrary payload or caller-authored dependency facts. The publication adapter
owns that staged result and a small explicit journal-walk stack. Each step
charges the actual session controls and inspects one committed observation or
one stack transition. Query edges resolve an actual ready child in the same
pinned revision, with exact observed fingerprint and completeness checks.
A checked-identity set bounds repeated child traversal by the memo limit.
No provider is rerun, and reading the graph does not change execution provenance.

The public ledger intentionally has no `LineIndex` node. Both current query
families project their transitive raw-source observations into the established
`Input(FileKey)` fact with the observed source digest and no semantic edges.
Unknown family/projection shapes fail closed. The first-observation journal
remains the single source of dependency evidence; this is a derived display
projection, not another independently authored graph. Subsequent semantic
families must supply their exact reference node/edge projections, not merely
flatten everything into source leaves.

After traversal, the existing request transaction prepares and commits the
result adapter and canonical row. Pending rows remain hidden, and cancellation
or failure discards staging without deleting previously published rows or
committed source products. A publication holds no mutable registry borrow
between steps. Its session pin preserves journals and keys across collection;
semantic stepping remains blocked throughout the collection safe point.
Dropping a publication adapter is not an effectful session close: its owner
must still close/cancel the session, as for the existing database adapter.

`tests/registry/dependencies.glorious` checks cold source publication, a
recomputed line query with green input facts, parent-reused green facts,
changed-source red facts with the exact changed edge, and memo-hit publication.
The native comparator obtains the corresponding input traces from actual
`StageZeroCompiler` compilations, including exact fingerprints, empty input
edges, status, and parent identity. Source tests also reject zero-node staging,
work exhaustion, and a foreign publication owner, preserve the cursor through
collection, and cancel at every one of 24 projection/preparation boundaries.
Their result is `[1, 1, 1, 1, 1, 1, 24]`.

The normalized-world registry history separately publishes its original,
unchanged-child, and changed-child line results through the same path, checks
cold/green/red input rows, and retains its complete admission/reuse/retirement
checks. The selected pair passes in 15.19 seconds (`run-u6xccevx`). This does
not establish full `CompilationOutcome` parity, package publication, physical
memory leases, later-family dependency projections, or self-compilation.

The full source suite subsequently passes all 48 entries in 72.46 seconds:
`target/compiler-check/run-3x54nfxx/report.json`, source-lock SHA-256
`057eaf131e715d3d76087f5f574637021599c68126905cad31c40ba311220c50`.
All source guards and VM work/allocation ceilings are unchanged. This is the
latest complete source-suite evidence; the focused timings below are historical.
The full Rust workspace also passes 2,450 tests with zero failures and the two
existing ignored manual VM benchmarks in 78.520 seconds (local incremental
build, not clean-checkout CI). Logs are in `/tmp/grandiose-dependencies-qI3Lxq/`.

### Real normalized-world history

`tests/request/world_registry.glorious` now passes `[1, 1, 1, 1, 1]` in the
audited full 47-entry run `run-jgx73yx0` (65.94 seconds). It compares complete
request admission with the actual Stage0 database, then exercises source/line
memo hits, unrelated-request parent reuse, observed-source invalidation,
unchanged pinned old products, and exact final-owner retirement. See
[source admission](source-admission.md#whole-request-failures-lifecycle-and-registry-integration)
for comparator scope, counters, and the retained physical-certification limits.

### Stepped interner reclamation

The registry's collection safe point now includes a
stepped key-root scan followed by per-family sweeps. A root includes each
active attempt's own key, its current observation journal, all reads retained
by its replay cursor, and every retained cell's own key and committed journal.
Scanning only ready memo keys is insufficient: a suspended replay can still
hold keys after its immediate parent is collected. The engine already handles
a missing parent candidate by recomputation; key reclamation must not turn
that case into a stale-key error before the fallback.

The root walker is non-generic and yields one checked read identity per step.
Typed adapters mark referenced interner slots after checking family,
database, namespace, slot, and generation. They sweep one slot at a time, removing
unmarked entries from both the exact-key map and arena, and resetting marks
on retained slots. This avoids rescanning all memos separately for every key.
The registry continues blocking admission, stepping, inspection, and a
second collection after the core database finishes but before key sweeping
finishes. Request cancellation remains available because setting its flag
does not change the root set. Zero drivers alone is not a roots proof.

Four new histories pass:

- Sixteen successful worlds use a one-slot key capacity, including pinned
  retirement and rejection of old values after slot/generation reuse: 750
  checks, with live keys returning to zero and allocated slots staying at one.
- Sixteen distinct missing-file queries reclaim their keys without retiring
  their active world, followed by a successful query: 466 checks.
- Collection before a new query's first step and during its partial builder
  preserves active keys. Fourteen public-operation probes run before every
  collection step, including key-only phases, and must report `Collecting`.
  The query and prior values remain usable afterward: 91 aggregate checks.
- The immediate parent is collected while a line query has entered replay but
  has not demanded its source child. Its replay is the sole source-key owner.
  After fallback discards replay, a second collection frees that key; the query
  then recomputes with `ParentMemoMissing` and safely reuses the freed slot:
  91 checks.

The original four registry histories pass against key collection (150.89
seconds), the two churn histories pass (131.98 seconds), and the pending/replay
pair passes (144.95 seconds). All five existing generic database histories
also pass (163.99 seconds). No Stage0 or standard-library changes were needed
for this collector. The fixture uses explicit `usize` field assignments and
concrete view-error helpers for known C0 inference limitations.

These results are logical ownership/generation evidence, not a physical
memory-plateau measurement. `Stats.source_keys` and `Stats.line_keys` expose
live and allocated slot counts separately from memo/product counts. The
earlier full 41-test run stopped at the unchanged 590-second ceiling with 32
recorded executions; its report is `run-s1qfvj50`, predates this collector,
and is not a passing full-suite result.

The pre-batching audited selected run passes all eight registry histories and five
generic database histories together (13 tests, 353.04 seconds):
`target/compiler-check/run-67bunjna/report.json`, source-lock SHA-256
`b7f452fcfa316f56d4fb8bfb97a10f132f6a16e5fa9d6aac99607549a1d593b3`.
It explicitly records `test_scope: selected_tests` and
`complete_current_suite_passed: false`; it is not a full 45-test certificate.

The eight registry scenarios subsequently pass together in one source
execution (`run-5cef3lh6`, 147.02 seconds). Each scenario owns a fresh database
and controls. The returned tuple is exactly
`[35, 96, 47, 235, 750, 466, 91, 91]`, not a sum of scenario results. One shared,
unchanged execution budget accounts for 7,695,828 work ticks and 8,473,372
allocation elements. The native authoring tuple reader still requires strict
i64 element types after independent program verification.
The combined diagnostic/publication/registry selected run `run-d4w9z5p5`
also passes this batch with identical bytes and counters. See
[authoring evidence](authoring.md) for the still-failing full-suite time gate.

The new runner's zero-match guard was separately tested: `run-blnqxy2d`
records zero executions, exit 1, and no passing capability status.
