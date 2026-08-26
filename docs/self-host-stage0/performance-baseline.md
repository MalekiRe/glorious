# Stage0 self-host performance baseline

This file records measured gates for the current uncommitted port work. It is
not a claim of module parity or self-host convergence.

## Enforced limits

| Gate | Limit | Enforcement |
| --- | ---: | --- |
| Individual canonical source-world compile | 300 seconds | `self-host-stage0-canonical-world-check.sh` |
| Full self-host conformance | 590 seconds | `test-with-budget.sh` |
| CI self-host job | 10 minutes | `.github/workflows/ci.yml` |

## Latest measured results

| Command | Result | Wall time |
| --- | --- | ---: |
| `tooling/self-host-stage0-canonical-world-check.sh` | source world score `149` (including verifier-backed literal branch artifact selection) | about 28 seconds warm |
| `tooling/test-with-budget.sh tooling/self-host-stage0-conformance.sh` | pass (current warm incremental run, four workers) | about 1 minute 43 seconds |
| `tooling/self-host-stage0-service-function-body-check.sh` | source `pub fn` bodies with typed i64/Bool parameters, plus strict two-`usize`-binder checked addition, reach scalar, binary, unary, and invocation-selected conditional lowering through Body → Core → MIR → VM | about 1 minute 40 seconds |
| `tooling/self-host-stage0-service-file-read-check.sh` | file-backed source header, scalar/binary/conditional bodies pass source → scanner → header → interface → Body → Core → MIR → VM | 15.0 seconds |
| `tooling/self-host-stage0-bootstrap-artifact-check.sh` | repeated emission, independent verification, Rust-emitted G0BM manifest decode→canonical-reencode equality plus corrupt-manifest rejection in the source codec, canonical-harness execution (`148`, including G0BM decode/convergence), and explicit-argv Stage0-driver check/run/emit-vm for i64 scalar, Unit, explicit-return arithmetic and literal conditional, plus strict Bool paths (malformed Bool and unimplemented commands fail closed) pass | about 29 seconds warm |
| `tooling/self-host-stage0-g1-default-artifact-check.sh` | source-constructed canonical G1 unit-entry oracle independently verified and run by `grvm` | < 1 second warm |
| `tooling/test-with-budget.sh tooling/ram-gate.sh cargo test --workspace --all-targets` | pass | 32 seconds |

## Bootstrap interoperability status

The current seed artifact is deterministically emitted, independently verified,
and executed by the Stage0 VM both as the canonical source-world harness and as
a narrow capability-bound `emit-vm` driver that publishes a G1 artifact or
reports rejected input through the explicit diagnostic capability. It is
**not yet** executable by the independent `grvm`: `grvm run` rejects the seed
itself as non-G1 bytecode (“bad magic”). The source backend now
also constructs an independently verified and run **minimal G1 unit-entry
oracle** (canonical header, directory, predefined tables, function metadata,
instruction, and cleanup evidence). This proves the initial source-to-G1
executable wire path, but is not MIR-driven code generation and contains no
compiler code. Cross-verifier compatibility for the emitted compiler remains
an explicit bootstrap/convergence prerequisite.

## Retained optimizations

1. MIR operation-arena validation builds one location index instead of scanning
   every operation for each instruction.
2. MIR local/storage liveness uses dense bit-vectors for already-validated
   dense IDs, preserving must-live intersection while avoiding repeated
   `BTreeSet` cloning and intersection.

The bit-vector change reduced the measured self-host conformance suite from
about 3m55s to about 2m33s. Re-measure after changes to compiler source,
MIR validation, or the canonical source world.

The latest observed warm incremental run took about 29 seconds in this
workspace. The 590-second wrapper remains the authoritative hard limit for
both cold and warm executions; cold-machine timing has not been remeasured in
this update, so the warm result is not a CI throughput guarantee.

The independent probe phase uses four bounded workers by default after shared
compiler/VM builds and ordered artifact checks complete. Set
`GRANDIOSE_SELF_HOST_CONFORMANCE_JOBS=1` to reproduce serial execution, or a
value through `8` for a deliberately bounded local experiment.

The four G1 artifact checks join that bounded probe phase because each creates
its own temporary artifact directory and only reads the already-built Stage0
compiler and VM. This removes their otherwise serial process-startup cost
without sharing output paths or weakening any check; the 590-second wrapper
remains the cold-run correctness limit.

The bounded two-source request admission is tested both in its request harness
and through the aggregate service probe. The normal compiler driver runs on a
single explicit 64 MiB worker stack, preventing large linked source worlds
from depending on a platform's smaller main-thread stack while retaining one
finite, process-local compiler resource budget.

## Current compiler-scale resource profile

The source service now lexes the complete `self-host-stage0/src/main.glorious`
entrypoint under bounded defaults of 16,384 VM call frames and 100,000,000 VM
instructions. These limits remain configurable for hostile or constrained
programs; they provide the finite headroom needed by the currently recursive
source cursor until source-defined iteration or tail-call lowering replaces it.
## Current normal-compiler delta

The frozen self-host baseline contains 1,726 tests. The current normal
compiler worktree has 17 additional tests; their module ownership and unported
status are recorded in `current-baseline-delta.tsv`. They are not treated as
covered by the frozen parity ledger until an explicit baseline roll updates
the inventories and source-port evidence together.
