# Source-owned standard library

`src/*.glorious` contains the library implementation. `sources.rs` is only an
embedding inventory: it includes the files verbatim and joins them with newlines.
No collection, codec, parser, formatting, or graph algorithm is implemented in
the Rust embedding layer. `tests/*.glorious` contains executable source cases;
`standard_library_sources.rs` is their compile/verify/run harness.

This is work in progress against the consolidated 7 September 2026 specifications,
not a complete or certified conforming standard library. Source bodies existing
on disk and executable/compiler-validated implementations are different states.

## Composition and validation

The compiler currently injects the existing `src/lib.glorious` distribution.
`STANDARD_LIBRARY_SOURCE` embeds the complete extended composition for explicit
compilation. Family tests select the base and their source dependencies; a
separate positive `full_composition` test requires all fragments together.
Runtime primitive admission recognizes only exact embedded fragment bytes in
inventory order, never an arbitrary modified source prefix. No tests are ignored
or changed into expected-failure tests to disguise unsupported library features.

The frozen-source matrix in `target/standard-library-freeze.log` ran 28 active
tests: four passed, 24 failed, none ignored. Foundation, time, floating bit
policy, and exact embedding/inventory integrity passed. All 24 failures occurred
during compilation, before verifier/runtime execution. The frozen inventory
contains 39 source fragments. The bootstrap has since been migrated to explicit
mutable local declarations where assignment or unique borrowing requires them.
The later combined verification in `target/all-failures-v15.log` reproduces
this four-pass/24-compilation-failure result; all 2,579 non-GSC2 Stage 0 tests
outside this new source matrix pass. That compiler-regression result does not
establish library conformance or self-hosting acceptance. The later cache-39
binding/tuple/destructuring run in `target/mutable-bindings-baseline-v4.log`
passes 2,596 tests with the same 24 source-matrix failures and zero ignored tests.
The cache-40 follow-up in `target/mutable-bindings-baseline-v5.log` passes 2,597
tests with the same 24 failures and no ignored tests.
The cache-42 focused verification in `target/effect-projections-v1.log` passes
157 compiler tests and retains four passing/24 failing source tests. Associated
row projections after `|`, and bare associated row projection definitions/
defaults, are supported at that checkpoint. The cache-43 follow-up now retains
independent multiple row operands through inference, trait matching, instance
materialization, and artifact encoding. Its full non-GSC2 run in
`target/effect-unions-baseline-v1.log` passes 2,618 tests, with the same 24 source
failures and no ignored tests. This does not establish full row-system or
standard-library conformance. The cache-44 private-glob lookup correction in
`target/private-glob-baseline-v1.log` passes 2,620 tests, with the same 24 source
failures and no ignored tests. The source matrix no longer reports G3326 or
private-type G3304 errors; it advances to later syntax and type checks without
exposing private bindings. Cache 45 adds parsing and checked interpreter transfer
for a bounded direct, concrete, reference-free `tail` frontier. The library's
generic, borrowed and callback tail contracts still need further compiler work;
this is not completion of its tail-dependent source families. The consuming
carrier checkpoint in `target/mandatory-tail-baseline-v2.log` has 2,635 passing
tests and the same 24 source-library failures, with zero ignored tests.
Cache 46/interface 7 add restricted item/member/import visibility and
private-by-default nominal record fields. `Range`'s specified public fields
are now explicit.
The completed current-tree run in `target/visibility-baseline-v3.log` passes
2,645 tests with the same 24 source-library failures and zero ignored tests.
The remaining source tests are active but are not yet passing; the full
composition still encounters compiler parser gaps
before complete semantic and runtime validation. Examples include explicit
the remaining `tail` contracts, fixed arrays and const parameters, higher-ranked callback constraints,
row-kinded associated binding arguments, associated ordinary bounds,
and generic effect-operation where clauses. Subsequent ownership,
resolution, runtime-binding, and source defects may remain behind those errors.

Run the complete matrix with the repository's resource guards:

```sh
CARGO_TARGET_DIR=target/conformance-groundwork CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS=2 CARGO_PROFILE_TEST_OPT_LEVEL=1 tooling/test-with-budget.sh tooling/ram-gate.sh cargo test -p grandiose-stage0 --test standard_library_sources
```

## Implemented source families

| Source | Bodies and contracts present |
| --- | --- |
| `lib.glorious` | Existing control/operators, owning Vec/String/slices, queues/maps/sets, hashing and bootstrap host integration. This predates the consolidated interface and still requires migration. |
| `foundation.glorious` | Ownership-preserving Result/Option operations, lossless zip/unzip, ordering helpers and checked ranges. |
| `integer.glorious`, `integer_text.glorious` | Twelve concrete integer widths: checked/wrapping/saturating arithmetic, bits, radix parse/format and integer conversion matrix. Pointer-sized expansion currently assumes a 64-bit target. |
| `float*.glorious` | Canonical NaN/zero bit policy, total Eq/Ord/Hash, named IEEE comparison, classification, adjacent values, integral rounding, exact and shortest decimal formatting, midpoint/ties-to-even parsing directly at each width, exact dyadic FMA, overflow-safe approximate comparison, and the remaining 52 checked/exact scalar conversion pairs. Base operator and Display/Debug instance migration remain unfinished. |
| `algorithm.glorious`, `heap.glorious` | Sequence search, ownership-preserving deduplication and max binary heap. |
| `traversal.glorious`, `sorting.glorious` | Ordered borrowed callback traversals, predicate/fallible searches, stable borrowed partitions; heapsort, stable insertion sort, callback/fallible insertion sorting and binary search. Stable/callback sorting is O(n²); scratch stays empty and no resident holes or Clone/discard requirements are introduced. |
| `iterator.glorious`, `iterator_callbacks.glorious` | Separate iterator/stepper/lending protocols; eight structural and five callback adapters; ownership-preserving zip/peek buffers and remainder extraction; slice/vector instances; count, folds and exact-linear step collection. Callback rows/environment evidence are explicit. |
| `binary.glorious`, `codecs.glorious` | Checked endian reads, canonical varints, hex and base64 with structured failures. |
| `memory.glorious`, `boxed.glorious`, `array.glorious` | Layout arithmetic, allocation owner, pointer helpers, fallible Vec growth, Box ownership and fixed-array transfers/construction. |
| `utf8.glorious`, `char_escape.glorious` | Structured UTF-8 validation, ASCII/scalar helpers, prefix-preserving UTF-8 encoding and character escapes. |
| `storage.glorious`, `arena.glorious` | Typed IDs/IndexVec, interners, bit/sparse sets, FIFO work queue, checkpoint arena and generational arena. |
| `budget.glorious`, `parse.glorious` | Step/memory/depth budgets, exact-linear tickets, cursors and bounded parser composition. |
| `graph.glorious`, `source_map.glorious` | Budgeted BFS, topological ordering, SCCs and byte/UTF-16 source coordinates. |
| `fingerprint.glorious` | Digest256, canonical framing and BLAKE3 using source-owned compression. Streaming currently buffers input; bounded-memory streaming is not claimed. |
| `format.glorious`, `time.glorious` | Bounded/indented formatting, quoting, normalized Duration and domain-checked Instant arithmetic, Clock protocol. |
| `random.glorious` | Explicit entropy protocol, deterministic versioned BLAKE3-counter byte stream and unbiased rejection-sampling random-below. |
| `io.glorious` | Read/Write/Seek/BufferedRead, prefix-counted transfer helpers, growable memory cursor and recoverable buffered reader/writer ownership. |
| `path.glorious` | Lossless native-byte OS strings and POSIX lexical paths. Wide-unit/native target selection is not implemented. |
| `host.glorious` | Typed host/file/process effects, exact-linear File/Child owners and File stream-trait adapters. No runtime providers or authority-granting source constructors. |
| `ffi.glorious` | Checked terminated CStr/CString byte ownership, UTF-8 conversion and input-preserving interior-NUL failures. ABI scalar aliases and pointer-facing members remain absent. |
| `generator.glorious`, `task.glorious` | Owning generator/future/task protocol declarations; these do not supply an executor or manufacture host authority. |

Identity tokens use reference-counted allocation identity so live stale marks and
handles prevent address-reuse collisions. The two general pointer identity/address
leaves declared by `memory.glorious` still require compiler/runtime binding. The
private reference-count mutation also requires an explicit aliasing-authority
audit; compiler acceptance alone would not establish its safety. Arena
rollback ends its mark generation; it does not promise transactional rollback of
arbitrary external effects. Graph traversal order comes from input/successor
order, not hash iteration.

## Still missing or requiring interface migration

These are unfinished library work, not merely compiler blockers:

- Canonical core/alloc/std namespace closure, prelude migration, consolidated
  control/BranchResult contracts, and retirement of superseded root APIs.
- Migration of legacy float comparison operators and complete scalar formatting
  trait instances to the consolidated float policy.
- Complete lending concrete instances and iterator marker matrix,
  collection entries and all consolidated collection mutation signatures.
- ByteReader owner-bound marks and the full canonical ByteBuf interface. UndoLog
  remains absent: its shared `mark(&Self)` needs a sanctioned interior-mutation
  model for registering nested marks. A tentative Box/raw-pointer implementation
  was withdrawn rather than silently assuming that authority.
- Complete structured diagnostics, C-FFI adapters, wide-unit/native path profile
  selection, typed host providers and the compiler-host adapter migration.
- Full required trait-instance and ownership/negative conformance matrix.
- A verified bounded-memory streaming fingerprint implementation and target-width
  portability of pointer-sized integer expansions.

Compiler-sealed mechanisms such as Bindings/environment proofs cannot be supplied
by a fabricated ordinary library type. Missing source algorithms likewise cannot
be supplied by bodyless declarations or whole-algorithm runtime primitives.
