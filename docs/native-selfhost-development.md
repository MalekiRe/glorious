# Native Self-Host Development Strategy

## Purpose

During development and test iteration, run the self-host compiler as a
Wild-linked native LLVM executable. This avoids repeatedly interpreting the
same large compiler bundle in the VM while preserving the VM bytecode pipeline
as the authority for self-hosting and stage-convergence verification.

This is a development execution strategy, not a change to the final language
runtime or to the byte-identical stage-1 → stage-3 requirement.

## Artifact model

Each native self-host baseline consists of:

- the Wild-linked self-host executable;
- any checksummed partitioned native object intermediates present in the
  producer's private cache;
- a read-only TSV manifest of every artifact and its SHA-256 digest;
- compatibility metadata: self-host source fingerprint, bootstrap/compiler
  revision, LLVM cache schema, target/options, runtime ABI, Clang version, and
  Wild version.

Native self-host executable development is **O3-only**. A baseline manifest
must contain `optimization\tO3` and a `cache-fingerprint` field that includes
`optimization=O3`. The seeding helper rejects O0, O1, O2, missing levels, and
fingerprints that do not explicitly bind the artifact to O3. This prevents a
fast-but-different development artifact from leaking into native test runs.

The canonical baseline is read-only and lives at:

```text
$GIT_COMMON_DIR/grandiose-native-selfhost-baseline
```

It is never modified by a worktree.

## Worktree seeding

When creating or starting work in a new Git worktree, seed a private cache:

```text
$WORKTREE/target/self-host-native-cache
```

The seeding helper, `tooling/seed-native-selfhost-cache.sh`, must:

1. Read only the baseline manifest.
2. Verify every baseline digest before copying.
3. Copy artifacts and intermediates into a private staging directory in the
   destination worktree.
4. Verify every copied digest again.
5. Atomically publish the private cache, with its manifest published last.

The result is intentionally a copy, not a shared writable cache:

```text
read-only common baseline
           │ seed once
           ├── worktree A /target/self-host-native-cache
           ├── worktree B /target/self-host-native-cache
           └── worktree C /target/self-host-native-cache
```

After seeding, a worktree may rebuild or delete only its own private cache.
It must never write another worktree's cache or the common baseline.

## Invalidation and rebuild rules

Use a seeded artifact only when all manifest compatibility fields match. A
private rebuild is required when any of these changes:

- self-host source or dependency contents;
- bootstrap/compiler revision or artifact schema;
- LLVM target triple, data layout, entry-wrapper setting, or optimization
  level;
- native runtime ABI;
- Clang identity/options;
- Wild identity/options.

Within a persistent native compiler session, use the incremental layers in
order:

1. Exact LLVM-IR cache for unchanged requests.
2. Manifest-valid LLVM function fragments for unchanged function bodies.
3. Exact native object-byte cache for unchanged `--emit llvm-object` requests.
4. A fresh Wild link for every executable request.

Body-only changes may reuse unaffected function fragments. Interface, target,
runtime ABI, toolchain, or linker changes invalidate conservatively.

The durable one-shot executable route uses the same partitioning through
`--native-incremental-cache`. Its cache scope is the private worktree cache,
not the `grc --serve` process: a seed may contain verified object and manifest
pairs, and an invocation reuses only entries whose complete IR and native ABI
key still match. It always performs a fresh Wild link.

## Test and development routing

Development and host-side self-host tests should invoke the native self-host
runner and its private cache. Native executable emission requires `wild`; it
must fail clearly if Wild is unavailable rather than silently choosing another
linker.

For the bootstrap fixture corpus that is representable as independent source
files, run `tooling/self-host-native-tests.sh run`. It builds the canonical
native executable once through `tooling/self-host-native.sh`, then deterministically
executes every manifest-selected case against that executable. The corpus lives
in `tooling/self-host-native-corpus.tsv`; use `list` or repeated `--case ID`
to inspect/select cases. Each failure retains the native compiler output and
diagnostic log long enough to report the exact source and failure reason. This
is deliberately native-only: it does not substitute a VM run on failure.

The native runner uses O3 only. Debug or lower-optimization executable output
must not seed, satisfy, or overwrite this cache.

The runner must not silently fall back to VM execution when its native artifact
is absent or incompatible. It should reseed/rebuild the private cache or emit
a diagnostic explaining why native compilation cannot proceed.

### Native staged convergence evidence

`tooling/self-host-native-convergence.sh` is the native-only convergence
checker. It takes a stage-1 and a stage-2 **native executable**, their checked
provenance manifests, and the canonical compiler source. Each manifest binds
the executable SHA-256, source SHA-256, `optimization=O3`, and `linker=wild`;
the stage-2 manifest additionally binds the SHA-256 of the bytecode compiler
artifact it represents. The checker runs stage 1 to emit `stage2.grbc`, refuses
a stale or unrelated stage-2 native executable, then runs stage 2 to emit
`stage3.grbc`.

It keeps its output directory on every outcome. `metadata.tsv` records exact
artifact hashes, sizes, statuses, and result. A failed comparison also writes
`stage2-stage3.diff` with both SHA-256 values and the first differing byte
offsets. It reports `CONVERGED` only after `cmp -s` has verified the complete
artifact bytes; there is no VM runner, bytecode-execution fallback, or
lower-optimization fallback in this path.

Create stage provenance with
`tooling/write-native-stage-provenance.sh`. For the canonical bootstrap-native
stage, first materialize the production closure with
`tooling/self-host-native.sh canonical-source SOURCE`; then
`tooling/self-host-native.sh provenance SOURCE stage1.tsv` builds (or reuses)
the per-worktree O3/Wild runner and publishes its stage-1 manifest. The latter
re-materializes and byte-compares the source before attesting it, so a stage-1
manifest cannot bind the native host to an arbitrary file that happens to have
been passed as `SOURCE`.
For stage 2, the native-stage producer supplies its executable and emitted
`stage2.grbc` to `write-native-stage-provenance.sh --stage 2`; the helper
atomically records both hashes and refuses to overwrite retained evidence.
It intentionally does not claim that recompiling source with the Rust bootstrap
produces a stage-2 native host. The native lowering bridge must produce that
host before the stage-2 provenance can be written.

The VM bytecode runner remains mandatory for:

- bootstrap bytecode conformance;
- self-host compiler feature parity;
- stage-1 → stage-2 → stage-3 byte-identical convergence;
- validating any behavior native execution could mask.

## Baseline promotion

A worktree cannot promote its local cache automatically. Promotion is an
explicit operation after release validation of the compiler artifact, manifest,
and required VM/self-host gates. Promotion atomically replaces the read-only
common baseline; ordinary worktree creation only consumes it.

## Operational rules

- All builds and tests run in release mode through `tooling/ram-gate.sh`.
- Use `/tmp` Git worktrees for isolated implementation work.
- Keep native artifacts private after seeding; do not share writable `target`
  directories.
- Record cache hit/miss and fragment-reuse evidence in persistent `grc --serve`
  responses when diagnosing iteration speed.
- Treat the native path as an iteration accelerator, never as proof that the
  VM self-hosting goal has converged.
