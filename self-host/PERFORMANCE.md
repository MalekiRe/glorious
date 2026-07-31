# Self-hosted compiler performance strategy

Status: implemented low-risk performance changes and follow-up candidates for the
self-hosted compiler and its integration suite.

No profiler trace was available while this work was prepared. The implemented
changes therefore target duplicate work that is visible directly in the control
flow and test topology. They do not claim measured speedups.

## Implemented changes

### Persistent batch compilation state

The public canonical bundle compilation entry points now reuse one
`CompilationDriver` per calling thread.

That driver already owns the compiler's tested incremental state:

- exact successful phase outputs for recent `SourceBundle + CompileOptions`
  pairs;
- unchanged per-segment token streams;
- reusable body type-inference evidence;
- reusable lowered MIR bodies.

Previously, callers that did not explicitly construct an incremental session
created fresh state for every compilation. Test workers and long-lived command
processes could therefore repeatedly lex and elaborate the unchanged distributed
standard library. The public batch wrapper now receives the same reuse behavior
without introducing a second invalidation scheme or a global compiler lock.

The state is thread-local. Independent test workers remain parallel, while calls
on the same worker reuse prior frontend, type, MIR, and exact-result state.
Manifest-specific conformance entry points remain outside this cache because
their trust inputs are part of their semantics.

### One self-host artifact per integration process

The fast self-host integration fixture now compiles its O2 self-host artifact
once through `OnceLock` and reuses the verified artifact for:

- structured compile-error classification;
- diagnostic normalization and rendering checks;
- diagnostic identity-space checks;
- VM execution of the self-hosted compiler;
- verification of the compiler-produced GRBC artifact.

The former `self_host_diagnostics` integration binary compiled an almost
identical distributed compiler independently. Its probes now live in the
`diagnostic_probe` Grandiose module and execute from the shared artifact. This
removes one complete O2 compiler build from the normal integration suite while
preserving the assertions.

### Fast and slow self-host tiers

The normal test tier retains the VM-hosted self-compilation and artifact
verification path. LLVM generation, clang compilation, native execution, and
VM/native byte-for-byte comparison are isolated in one ignored test.

The ignored test has an explicit scheduled and manually dispatchable GitHub
Actions workflow. Native parity remains a regular invariant, but it no longer
extends every ordinary workspace test run.

### Optimized test workload

The workspace test profile uses optimization level 1 with line-table debugging.
The suite executes the compiler, verifier, optimizer, and VM as workload; fully
unoptimized test binaries make those workloads disproportionately expensive.
Debug assertions remain enabled, while the code under test receives basic
optimization and backtraces retain source lines.

### Parallel CI topology

Independent CI concerns now run as separate jobs:

- formatting;
- compiler and VM tests;
- formatter, build-tool, and language-server test matrix;
- the real `grc`/`grand`/`grvm` contract;
- editor metadata.

Superseded runs are cancelled through a workflow concurrency group. This reduces
wall-clock latency and prevents obsolete commits from consuming runner time.

## Correctness boundaries

The performance changes preserve these rules:

- cache keys compare complete `SourceBundle` and `CompileOptions` values rather
  than trusting hashes;
- failed compilation does not publish a phase artifact;
- the existing `CompilationDriver` rollback and invalidation behavior remains
  authoritative;
- compilation misses do not take a process-global lock;
- successful self-host output is still decoded, re-encoded, verified, and
  executed in the fast tier;
- VM/native artifact identity remains covered by the slow tier;
- conformance APIs with explicit manifests bypass the default batch cache.

## Next likely compiler hot spots

These are visible algorithmic candidates, but they should be changed only with
artifact-identity tests and preferably measurements:

1. **Canonical constant lookup.** Emission linearly scans the sorted constant
   arena for every constant instruction and switch case. A canonical key-to-ID
   map or binary search would remove repeated whole-pool scans.
2. **Canonical name and signature lookup.** Names and signatures are sorted or
   deduplicated, then repeatedly found by recursive linear search while records
   are written. Freeze-and-remap tables would make these direct lookups.
3. **Type-property memoization.** Zero-sized and zero-use properties are
   recursively recomputed while each type record is emitted. They should be
   solved once per semantic type and reused by lowering, cleanup, and emission.
4. **Cleanup snapshot coalescing.** Stage-A lowering currently copies the full
   reversed live-register set before every instruction. Adjacent instructions
   with identical cleanup state can share a range, and persistent state IDs can
   avoid repeated vector copies.
5. **Live-register indexing.** Moves and consumes find registers through linear
   scans of `live_order`. A register-indexed position table can make updates
   direct while retaining deterministic cleanup order.
6. **Persistent standard-library frontend.** The per-thread driver now reuses
   lexed segments and body/MIR results. A future immutable parsed-interface cache
   for the trusted distributed standard library could avoid more module and
   declaration work across substantially different user bundles.

The first three backend changes naturally belong with the architecture's
canonical-pool and cached-type-facts stage. Cleanup changes should land with the
PlaceFlow/MIR work so ownership facts do not acquire another temporary source of
truth.

## Evaluation

Once profiling is available, measure separately:

- cold self-host compilation;
- warm exact-input compilation;
- warm compilation after changing one body;
- fast self-host integration-test wall time;
- scheduled native-parity wall time;
- total CI critical-path duration;
- peak resident memory of the per-thread driver cache.

The important comparison is not only total runtime. It should confirm that cold
compilation does not regress materially, that warm test workers reuse the
standard library, and that the cache remains bounded under many distinct
bundles.
