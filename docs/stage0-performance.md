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

The combined observed reduction is about 79%, or 4.8 times faster. A separate
baseline sampled with `perf` took 186.72 seconds; that instrumented time is not
used for the comparison. Sampling showed repeated type cloning, allocation,
deallocation, and hashing in the native authoring compiler.

Two sources of repeated work were removed:

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

The lifecycle fixture retained exactly the same serialized artifact and every
recorded execution counter in all three runs:

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

The selected native regression run passes 1,585 tests across the library,
coherence, conversions, Core, service, signature, standard library, trait
solver, and VM backend suites. The full source-suite run was deliberately
stopped at the user's request to pursue another optimization first; it is
not a passing full-suite result.

Reproduce the focused run with:

```sh
CARGO_PROFILE_TEST_OPT_LEVEL=1 RUST_TEST_THREADS=8 \
  tooling/test-with-budget.sh tooling/ram-gate.sh \
  cargo test -p grandiose-stage0 --test gsc2 \
  gsc2_request_world_lifecycle_preserves_cancellation_work_and_fingerprint_limits
```

The fixture and broader GSC2 compiler remain work in progress. These native
performance changes are not a language-parity or self-hosting certificate.
