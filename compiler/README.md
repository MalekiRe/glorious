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
stepped line/UTF-16 indexes and a lossless lexer are implemented and reference-tested.
The closed typed registry connects `SourceBytes`, `LineIndex`, and `Lex` to tracked child
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

The self-hosting path compiles the compiler and source libraries, including
concrete generic specializations and unsafe internals, to bytecode operating on
host-compatible memory. Raw memory and a shared native/VM ABI are prerequisites.
Current distribution ships source for local compilation; independently admitting
untrusted distributed bytecode is deferred, not a prerequisite. Collections must become
source implementations, not wrappers around specialized VM algorithms. The
Glorious LLVM backend is deferred until after working, verified self-hosting;
initial VM/native tests use host ABI fixtures and do not need native Glorious
std or native generic specialization. Unsafe-enabled execution is not an
in-process memory sandbox. See the
[decision](../docs/unsafe-memory-and-native-abi.md) and
[U0–U6 gates](spec/unsafe-memory-progress.md). These are requirements, not yet
certified source or native capabilities.

Development proceeds through the specification's executable M0–M10 gates. An
executed substrate test is not language parity or a self-hosting claim. All old
self-host coverage is historical. `spec/contracts.tsv` inventories the frozen
public surface, including fields, variants, methods, traits, and reexports.
Unimplemented contracts remain open until a source comparator passes.

The source, line-index, and lexical providers now reserve their backing capacities
before allocation and retain root/phase charges through shared-product disposal.
This is not a complete physical allocation census; see
[provider memory ownership](spec/operation-budgets.md#initial-provider-backing-storage-integration).
See [lossless lexical products](spec/lossless-lex.md) for token/recovery parity,
stepped cancellation, typed publication, and the remaining frontend boundary.
Authoring execution now also records [native backing extents and bulk copies](spec/native-costs.md),
separately from logical allocation charges. These measurements exclude allocator
internals and Rust metadata; they are not a complete physical memory census.

Run `tooling/compiler-check.sh` for the current source tests and closure audit.
It creates a fresh execution report under `target/compiler-check/run-*/report.json`;
failed runs cannot produce a passing capability report. These reports explicitly
do not certify release readiness. Unprofiled counters are empty, not zero. The
source suite defaults to 12 test workers under the 590-second command guard and
24 GiB cargo-test address-space ceiling; `RUST_TEST_THREADS` overrides the worker
count. Use `python3 tooling/compiler-audit.py --refresh`
after changing the source/test closure. `--release` remains fail-closed.
The authoring lock includes the Stage0 crate manifest and every Rust file below
its `src/` directory, including nested lowering/verifier modules and newly added
files. It does not rely on a manually maintained list of authoring overrides.
Run `python3 -m unittest discover -s tooling/tests -v` for the closure-tracking
regression checks. Refreshing the lock records inputs; it certifies no milestone.
For a focused run, use `tooling/compiler-check.sh --filter gsc2_registry`.
Reports record the filters and mark this as selected-test evidence, never a
complete-suite pass. A filter matching no executed fixtures fails closed.
Concrete Stage0 destruction now specializes generic owners, traverses owned
record/tuple/active-enum fields, handles replacement and partial moves, and
keeps destructor-observed loans live through cleanup. Constructor lifetime
arguments infer from fields and result context; same-region reference returns
retain every possible caller loan. This is prerequisite work, not a completed
source compiler or complete collection destruction. Source `Vec<T>` now also
destroys its residents and releases its allocation through ordinary source
code, including nested owners, partial consumption and zero-sized user hooks.
Owned-pattern extraction and delimited handler completion have additional
frontend/MIR/runtime regressions. See the
[resident-cleanup checkpoint](spec/unsafe-memory-progress.md#source-owned-resident-destruction-and-handler-cleanup).
The subsequent native bridge supports capability-bound calls and synchronous
bytecode callbacks over genuine native homes, including source Vec growth and
resident Drop during native re-entry. Full source contracts survive region
erasure, and transitive/generic native-return layouts are retained. This is
partial ABI support. Ordinary addressable locals with supported concrete native
layouts now acquire homes at initialization, before borrowing or native calls.
Source Vec callback fixtures use ordinary locals. Synchronous owned aggregate
arguments/results and callback parameters now use native caller/producer slots;
source bytecode performs Vec growth and element destruction during an owned
round trip. Native bindings now also retain the exact source-selected destructor
and its reachable emitted code; native code can invoke that bytecode destructor
without an explicit source callback argument. The allocation-domain protocol is
part of the checked ABI. Durable external ownership, general callable ABI,
complete copy/use-operation identity and unsupported private runtime layouts
remain open. See the
[destructor contract checkpoint](spec/unsafe-memory-progress.md#native-destructor-contract-checkpoint),
[owned ABI checkpoint](spec/unsafe-memory-progress.md#synchronous-owned-native-abi-checkpoint) and
[native source-storage checkpoint](spec/unsafe-memory-progress.md#native-source-storage-checkpoint).
Source `blake3` now also implements its complete unkeyed 256-bit API as ordinary
bytecode, including compression and multi-chunk tree reduction. The compiler's
identity functions use it directly, with no whole-hash native opcode or input
collection conversion. Boundary, high-counter and owned-input mutation tests
compare exact reference bytes. See the
[source BLAKE3 checkpoint](spec/unsafe-memory-progress.md#source-blake3-checkpoint).
The authoring compiler now also lowers nested short-circuit Boolean values in
initializers, call arguments, completion subjects and lifted closures, preserving
evaluation order and selected-branch cleanup. The BLAKE3 comparator no longer
needs its Boolean-lowering workaround. See [A32](spec/authoring.md#a32-nested-lazy-boolean-values).
Owned closure environments now have executable capture cleanup, residual state
after normal invocation, independent copies and borrowed native-home write-back.
The tail-call proof preserves no-op callback cleanup without skipping source
destructors. See [A33](spec/authoring.md#a33-owned-callable-environment-destruction).
The shared ownership inventory now drives ordinary returns and compiler-selected
cleanup of cancelled call frames. Capture invocation loans transfer residual
slots back on return or frame abandonment, with checked caller write-back and
original resource limits. See [A34](spec/authoring.md#a34-shared-frame-ownership-and-cancellation-cleanup).
Dynamic label exits now reuse that frame cleanup, protect transferred payloads,
and preserve residual captures and specialized frame identity. See
[A35](spec/authoring.md#a35-nonlocal-label-frame-cleanup).
Terminal calls now end strict value-CFG paths without dead suffixes or invented
join values; bottom-first branch inference preserves returning alternatives,
and computed callees execute before their arguments. See
[A36](spec/authoring.md#a36-terminal-strict-value-control-flow).
The current frozen checkpoint passes **2,700 tests**: 2,652 workspace/all-targets
tests and all 48 audited source entries in 188.40 seconds, with zero failures
and two existing ignored benchmarks. All 50 results match A35. The source run
was sampled for 15 seconds; its time is not an uninstrumented speed comparison.
The recorded ownership, source-lowering and self-hosting gaps remain open.
The preceding frozen checkpoint passes **2,692 tests**: 2,644 workspace/all-targets
tests and all 48 audited source entries in 185.92 seconds, with zero failures
and two existing ignored benchmarks. All 50 results match A34. Retained replay
cleanup, temporary ownership and the recorded
source-lowering, prerequisite and self-hosting gaps remain open.
The preceding frozen checkpoint passes **2,685 tests**: 2,637 workspace/all-targets
tests and all 48 audited source entries in 175.59 seconds, with zero failures
and two existing ignored benchmarks. All 50 recorded results match A33. Other
nonlocal/replay cleanup paths and the recorded prerequisite/source-compiler gaps
remain open.
The preceding frozen checkpoint passes **2,670 tests**: 2,622 workspace/all-targets
tests and all 48 audited source entries in 177.89 seconds, with zero failures
and two existing ignored benchmarks. All 50 recorded results match A32; original
batches and limits remain unchanged. Exceptional capture cleanup and the other
recorded prerequisite/source-compiler gaps remain open.
The preceding frozen checkpoint passes **2,664 tests**: 2,616 workspace/all-targets
tests and all 48 audited source entries in 180.46 seconds, with zero failures
and two existing ignored benchmarks. All 50 recorded results match the source
BLAKE3 checkpoint, with original batches and limits unchanged.
The preceding frozen checkpoint passes **2,661 tests**: 2,613 workspace/all-targets
tests and all 48 audited source entries in 178.29 seconds, with zero failures
and two existing ignored benchmarks. Every recorded compiler result matches
the preceding checkpoint, and all original batches and limits remain in place.
The preceding frozen checkpoint passes **2,658 tests**: 2,610 workspace/all-targets
tests (including 28 native-bridge regressions) and all 48 separately audited
source entries in 174.90 seconds. There are zero failures and two existing
ignored benchmarks. Bootstrap retains its complete `[145, 80, 13]` batch and
original allocation limit, now using 7,699,624 charged elements. The authoring
runtime reduces real register allocations; no comparator or budget is weakened.
The preceding frozen checkpoint passes **2,651 tests**: 2,603 workspace/all-targets
tests (including 23 native-bridge regressions) and all 48 separately audited
source entries in 168.02 seconds. There are zero failures and two existing
ignored benchmarks; all original source batches and execution limits remain.
The preceding frozen checkpoint passes **2,646 tests**: 2,598 workspace/all-targets
tests and all 48 separately audited source entries, with zero failures and two
existing ignored benchmarks. The 176.98-second source run retains all original
batches, assertions and VM limits; release readiness remains false.
The preceding bridge checkpoint passes **2,640 tests**: 2,592 workspace/all-targets tests
plus all 48 separately audited source entries, with zero failures and two
existing ignored benchmarks. The source suite takes 171.55 seconds and retains
every original batch, assertion and VM limit. See the
[native bridge checkpoint](spec/unsafe-memory-progress.md#native-calls-and-bytecode-callback-checkpoint).
The preceding destruction checkpoint's workspace run passed **2,569 tests, zero failures**, with two existing
ignored manual benchmarks, in **146.157 seconds**. All **48 source entries** passed
in **134.87 seconds**; their 50 evidence files match the preceding run exactly.

The preceding source-cost checkpoint passed **all 48 source entries** in 238.70
seconds (`run-3jneul71`), including bootstrap admission and the complete
eight-history registry batch under their unchanged allocation-element limits.
Private source growth separation, checked byte-window reads and direct
initialization of the fixed digest output reduce actual call-frame work;
neither the VM nor its accounting changed. See the
[source call-frame evidence](spec/unsafe-memory-progress.md#source-call-frame-costs).
The final workspace/all-targets run passes **2,532 tests** with zero failures
and two existing ignored manual benchmarks in 194.414 seconds including build;
its 48 source entries pass in 183.13 seconds.
The preceding ownership-migration checkpoint passed 46 of 48 entries in 198.97
seconds; its two allocation failures and 1,841 passing selected Stage0
regressions remain recorded as [historical evidence](spec/unsafe-memory-progress.md#compiler-source-ownership-migration).
The historical raw-storage foundation checkpoint passed **2,469 tests in 126.214 seconds**, including
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
CARGO_PROFILE_TEST_OPT_LEVEL=1 RUST_TEST_THREADS=12 \
  tooling/test-with-budget.sh tooling/ram-gate.sh \
  cargo test --workspace --all-targets
```

The authoring artifact format is Stage0 program schema 106 (`G0VP`); release G1
bytes have a different schema and verifier. Development source tests cross the
Stage0 encode/decode/verify boundary before execution. They do not certify G1.

Stage0 and library bugs may be fixed with focused regression tests. The pinned
commits are provenance references; [authoring decisions](spec/authoring.md)
record intentional corrections and remaining substrate limitations.

Explicit numeric conversions now use the ordinary library function
`as<Target>(value)`, or `as(value)` when the result context supplies the target.
See [conversion traits and policy](../glorious-standard-library-specification.md).
