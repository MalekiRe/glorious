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
- generated LLVM IR and native object intermediates needed for fast local
  rebuilds;
- a read-only TSV manifest of every artifact and its SHA-256 digest;
- compatibility metadata: self-host source fingerprint, bootstrap/compiler
  revision, LLVM cache schema, target/options, runtime ABI, Clang version, and
  Wild version.

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

## Test and development routing

Development and host-side self-host tests should invoke the native self-host
runner and its private cache. Native executable emission requires `wild`; it
must fail clearly if Wild is unavailable rather than silently choosing another
linker.

The runner must not silently fall back to VM execution when its native artifact
is absent or incompatible. It should reseed/rebuild the private cache or emit
a diagnostic explaining why native compilation cannot proceed.

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
