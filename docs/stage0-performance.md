# Stage0 authoring performance

## Frozen solver snapshots and projection-free layouts

Measured on September 5, 2026, using the same GSC2 lifecycle fixture and
`CARGO_PROFILE_TEST_OPT_LEVEL=1 RUST_TEST_THREADS=8`. Times below are libtest
execution times, excluding the Rust rebuild. These are individual runs on a
shared workstation, not a controlled benchmark distribution.

| Native authoring compiler | Lifecycle test time |
| --- | ---: |
| Before these changes | 178.52 s |
| Shared solver snapshots | 172.61 s |
| Shared snapshots plus projection-free layout fast path | 37.25 s |
| Also share solver snapshots across coherence pairs | 17.71 s |
| Also compute fixed language identities only once | 10.76 s |

The combined observed reduction is about 94%, or 16.6 times faster. A separate
baseline sampled with `perf` took 186.72 seconds; that instrumented time is not
used for the comparison. Sampling showed repeated type cloning, allocation,
deallocation, and hashing in the native authoring compiler.

Four sources of repeated work were removed:

1. Body elaboration and trait-method contract comparison share immutable
   implementation rules, trait declarations, and definition tables. Each
   solver still starts with fresh answer tables and its original work limit.
   The initializer prepass keeps independent snapshots because it changes
   interface types as it proceeds.
2. Runtime nominal-field instantiation no longer constructs a complete solver
   when type normalization is provably the identity. The predicate mirrors
   the existing normalizer, including its opaque effect-row/static-data
   boundaries. Nested type and associated-const projections still take the
   full path. Exhaustive enum matching forces new type/argument variants to
   receive an explicit decision.
3. Coherence checks share one frozen solver snapshot across implementation
   pairs, instead of cloning the entire interface for each overlap probe.
   Each pair retains independent answer tables and a fresh work budget.
   Phase-timed runs reduced time through header processing from 21.12 seconds
   to 0.83 seconds; the final lifecycle timing above has no phase instrumentation.
4. The seven fixed language/prelude identities are initialized once with
   `OnceLock`, avoiding repeated hashing during resolution, ownership checks,
   and trait solving. Their original digest domains are unchanged. No
   source lookup, evidence, or mutable interface state is cached globally.

The lifecycle fixture retained exactly the same serialized artifact and every
recorded execution counter in all five runs:

- Artifact BLAKE3: `0f3738c2eb4716b751fed377a84c6460cc5cc36033abdd50058bcdb8a4664430`
- Artifact bytes: 2,877,630
- Result: `[1, 14, 3, 3, 5, 4]`
- VM work ticks: 7,114,908
- Charged allocation elements: 10,478,008
- Peak call depth: 25
- Recycled tail calls: 6,797
- Inspected tail argument elements: 2,919,788

No test assertions, source closure, VM execution rules, optimization level,
resource ceilings, or trusted runtime operations were removed or changed.
The new solver tests check shared snapshot identity, independent budgets,
isolation from later interface mutation, identity-path equivalence, and
nested projections that must not use the fast path.
The coherence regression mixes overlapping, disjoint, and explicitly refuted
bound domains across five declaration orders.
The fixed-identity regression checks all seven original digest formulas and
their distinct identities; existing source-shadowing tests still pass.

The selected native regression run passes 1,585 tests across the library,
coherence, conversions, Core, service, signature, standard library, trait
solver, and VM backend suites before the coherence optimization. After that
change, 1,069 library/coherence/conversion/service/signature/trait-solver tests
and the lifecycle fixture pass. After the fixed-identity optimization, those
suites plus resolution pass 1,097 tests, as does the lifecycle fixture.
An earlier full source-suite run was deliberately stopped at the user's
request to pursue another optimization first. The completed workspace run
below supersedes that interrupted attempt.

## Full Rust suite and ten-minute budget

Latest follow-up: after copy-on-write projected/fixed-size array updates, the
same guarded workspace command passes **2,455 tests, zero failures, two existing
ignored manual VM benchmarks**, in **84.670 seconds**, including a 2.42-second
incremental build. All 48 source entries pass in that run (73.71 seconds).
This is still comfortably below ten minutes locally, not a clean-checkout CI
guarantee or a controlled timing comparison. The improvement is established by
physical allocation measurements: sixteen writes at 512 elements request about
92% fewer bytes; see [runtime costs](../compiler/spec/runtime-costs.md).

The earlier follow-up after the nested-completion fix and source-provider
dependency publication passed **2,450
tests, zero failures, two existing ignored manual VM benchmarks**, in
**78.520 seconds** on a local incremental build. The expanded standalone
source suite passes all 48 entries in 72.46 seconds (`run-3x54nfxx`).
Logs for the workspace follow-up are in `/tmp/grandiose-dependencies-qI3Lxq/`.
The original optimization-cohort results below remain historical measurements,
not a claim that later compiler corrections preserve their artifact bytes.

The full Rust workspace (`--workspace --all-targets`) passes after all four
optimizations: **2,446 passed, zero failed, two ignored manual VM benchmarks**
across 48 test binaries/targets. No additional tests were ignored or filtered.

- Total wall time, including the Rust build: **99.402 seconds** (1m39s).
- Rust build: 30.01 seconds.
- Sum of reported test-binary execution times: 69.27 seconds.
- All 46 GSC2 source tests: 61.27 seconds.
- All 128 standard-library tests: 4.16 seconds.

This is a local incremental-build measurement, not a clean-checkout CI build
benchmark. CI now uses the same test optimization level and eight test threads.
The ten-minute CI limit and the command guard (590 seconds plus ten seconds
of termination grace) remain unchanged, as do debug assertions and VM budgets.

Reproduce the full Rust run with:

```sh
CARGO_PROFILE_TEST_OPT_LEVEL=1 RUST_TEST_THREADS=8 \
  tooling/test-with-budget.sh tooling/ram-gate.sh \
  cargo test --workspace --all-targets
```

`tooling/compiler-audit.py` passes before and after the run, with unchanged
source-lock SHA-256
`dbee96f69e5e1175566db6ccab12b42e011eba576af27e14b01f92c8fb2f2144`.
The run produced 48 source-execution records, including the same lifecycle
artifact/counters listed above. Local timing, cargo output, and those records
are in `/tmp/grandiose-performance-kKcUId/workspace/`.

Reproduce the focused run with:

```sh
CARGO_PROFILE_TEST_OPT_LEVEL=1 RUST_TEST_THREADS=8 \
  tooling/test-with-budget.sh tooling/ram-gate.sh \
  cargo test -p grandiose-stage0 --test gsc2 \
  gsc2_request_world_lifecycle_preserves_cancellation_work_and_fingerprint_limits
```

The fixture and broader GSC2 compiler remain work in progress. These native
performance changes are not a language-parity or self-hosting certificate.
