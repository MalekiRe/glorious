# GSC-2 compiler

This is the in-progress Glorious implementation of the [GSC-2 specification](../GSC-2-glorious-incremental-self-hosted-compiler-spec.md).
The Rust Stage0 compiler is the authoring compiler and behavioral reference;
the Rust G1 VM is the independent release verifier. Neither supplies semantic
callbacks to the source compiler.

The current implementation is a tested kernel foundation with initial source
products, **not yet a self-hosted compiler**. It contains generational storage, exact file identities,
request controls, revision retention, nested undo/publication, and a shared
query engine with waiting, cycle detection, recovery propagation, ordered
parent replay, and combined memo/product retirement. Immutable UTF-8 blobs and
stepped line/UTF-16 indexes are implemented and reference-tested. The first
closed typed registry connects `SourceBytes` and `LineIndex` to tracked child
demands, parent reuse, and final-owner disposal. Source histories exercise
real product sharing, pinned retirement, waiting/cancellation, and abandoned
builder cleanup. Stepped key collection preserves active journals/replays and
reclaims unused interner slots. Source admission now validates logical paths
and source identity/digest/UTF-8 before constructing sealed source values;
canonical source collections preserve stable ordering and validate every source
before duplicate rejection. Their index sorting and text comparisons are stepped;
bootstrap-stage admission also checks producer/predecessor provenance and
actual source bounds. Whole-request package/capability admission now validates
root/source aliases, collisions, and canonical capability sets. Option maps retain
ordinary replacement semantics with deterministic canonical rows. Runtime-manifest
input admission now preserves role/host ordering, exact validation errors, and
the existing finite authority tags, with executable reference comparisons.
Whole-request normalization and its complete fingerprint encoder now pass 56
successful-input reference cases, including retained fields and world adapters.
Cross-component failure ordering, cancellation/resource histories, and actual
normalized-world registry import/reuse now pass executable comparisons too.
Committed source-query journals now also derive public input facts for the
shared atomic request publisher, including memo hits and normalized worlds.
The remaining query families and their dependency projections, semantic
compiler, G1 emitter, service, and bootstrap remain to be implemented.
See [progress and next gates](spec/progress.md).

Raw memory and unsafe support, a safe-only guest/trusted-native-library boundary,
and a shared native/VM ABI are explicit prerequisites. Collections must become
source implementations, not wrappers around specialized VM algorithms. See the
[decision](../docs/unsafe-memory-and-native-abi.md) and
[U0–U6 gates](spec/unsafe-memory-progress.md). These are requirements, not yet
certified source or native capabilities.

Development proceeds through the specification's executable M0–M10 gates. An
executed substrate test is not language parity or a self-hosting claim. All old
self-host coverage is historical. `spec/contracts.tsv` inventories the frozen
public surface, including fields, variants, methods, traits, and reexports.
Unimplemented contracts remain open until a source comparator passes.

Run `tooling/compiler-check.sh` for the current source tests and closure audit.
It creates a fresh execution report under `target/compiler-check/run-*/report.json`;
failed runs cannot produce a passing capability report. These reports explicitly
do not certify release readiness. Unprofiled counters are empty, not zero. The
source suite defaults to eight test workers under the existing time and memory
guards; `RUST_TEST_THREADS` overrides that choice. Use `python3 tooling/compiler-audit.py --refresh`
after changing the source/test closure. `--release` remains fail-closed.
For a focused run, use `tooling/compiler-check.sh --filter gsc2_registry`.
Reports record the filters and mark this as selected-test evidence, never a
complete-suite pass. A filter matching no executed fixtures fails closed.
The latest full workspace run passes **2,469 tests in 126.214 seconds**, including
all **48 source test entries in 72.97 seconds** and all retained batched scenario
comparators. Source audit passes before/after; see [raw-storage evidence](spec/unsafe-memory-progress.md).
The preceding array-write optimization passed 2,455 tests in 84.670 seconds;
its measurements remain in [runtime costs](spec/runtime-costs.md).
The prior standalone source run passed in 72.46 seconds (`run-3x54nfxx`). The
earlier 590-second timeouts are historical; four native authoring optimizations
removed repeated solver construction and fixed-identity hashing without
raising any resource ceiling. See [performance measurements](../docs/stage0-performance.md)
and [authoring evidence](spec/authoring.md).
For the Rust oracle and independent VM suites, run:

```sh
CARGO_PROFILE_TEST_OPT_LEVEL=1 RUST_TEST_THREADS=8 \
  tooling/test-with-budget.sh tooling/ram-gate.sh \
  cargo test --workspace --all-targets
```

The authoring artifact format is Stage0 program schema 93 (`G0VP`); release G1
bytes have a different schema and verifier. Development source tests cross the
Stage0 encode/decode/verify boundary before execution. They do not certify G1.

Stage0 and library bugs may be fixed with focused regression tests. The pinned
commits are provenance references; [authoring decisions](spec/authoring.md)
record intentional corrections and remaining substrate limitations.

Explicit numeric conversions now use the ordinary library function
`as<Target>(value)`, or `as(value)` when the result context supplies the target.
See [conversion traits and policy](../docs/conversions.md).
