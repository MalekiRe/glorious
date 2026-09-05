# Authoring runtime: physical allocation measurements

Measured September 4, 2026 on Linux x86_64 with Rust
`1.96.1 (31fca3adb 2026-06-26)`, unoptimized test profile, System allocator,
and the opt-in C0 authoring runner with a 64-frame limit. These are substrate
measurements, not a self-compilation benchmark or M1 exit certificate.

Reproduce with:

```sh
RUST_TEST_THREADS=2 tooling/test-with-budget.sh tooling/ram-gate.sh \
  cargo test -p grandiose-stage0 --test runtime_storage -- --nocapture
```

The fixture is `crates/grandiose-stage0/tests/fixtures/hash_indexing_profile.glorious`.
Each program builds a map and optionally performs sixteen successful lookups
of its last key. Compilation, independent artifact decoding/verification, and
test reporting happen outside the allocation meter. Counting is thread-local
and covers only the synchronous VM run. The separate meter regression checks
allocation/reallocation accounting and isolation from another test thread.

## Before retained-owner call transfer

| Entries | Reads | VM work ticks | Allocations | Reallocations | Requested bytes |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 8 | 0 | 7,142 | 5,599 | 300 | 1,817,458 |
| 8 | 16 | 12,265 | 16,875 | 886 | 6,350,724 |
| 64 | 0 | 125,647 | 62,608 | 3,511 | 34,243,272 |
| 64 | 16 | 130,770 | 107,092 | 5,210 | 60,894,298 |

The original added lookup work is exactly 5,123 ticks at both sizes. Added allocator
requests are 4,533,266 bytes and 26,651,026 bytes respectively. This difference
includes the read batch's control/call overhead; construction is subtracted.
All programs returned 42. Peak call depth was nine without reads and ten with
reads. Bounded stack depth and indexed probing therefore do not establish
bounded per-lookup physical work.

## After retained-owner call transfer (A09)

Ordinary calls now retain live caller-owned loans and already-frozen captures.
The same fixture, environment, and limits produced:

| Entries | Reads | VM work ticks | Allocations | Reallocations | Requested bytes |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 8 | 0 | 7,142 | 5,533 | 300 | 1,812,178 |
| 8 | 16 | 12,265 | 8,787 | 462 | 2,873,544 |
| 64 | 0 | 125,647 | 62,088 | 3,511 | 34,201,672 |
| 64 | 16 | 130,770 | 65,342 | 3,673 | 35,263,038 |

Added requests for sixteen reads are now **1,061,366 bytes at both sizes**,
with 3,254 allocations and 162 reallocations. At 64 entries this is about a
96% reduction in requested bytes from the earlier 26,651,026-byte read batch.
Added VM work remains 5,123 ticks and all results/depths remain unchanged.
The regression now checks equal added physical requests as well as equal
logical lookup work across these two sizes; absolute costs may improve.

Construction remained expensive after A09: its bytes barely changed. The
following copy-on-write improvement addresses fixed-size updates separately.
Neither these small tables nor the array measurements below establish a
compiler-scale performance certificate.

## Copy-on-write projected and fixed-size array updates

Measured September 5, 2026 against `e478904a`, using the optimized authoring
test profile and the same thread-local meter. Mutable reference projection
now uses `Arc::make_mut` along the existing owner path: unique tuples, records,
enums, and arrays retain their backing, while shared aggregates detach before
mutation. Fixed-size array set, move-out, and reverse use that path directly
instead of rebuilding a vector and its backing slice. Register and caller
references still write into their actual owner; captured and shared loans
cannot gain mutation authority.

The new fixture `tests/fixtures/array_update_profile.glorious` constructs one
vector, then optionally performs sixteen element writes through ordinary
`Vec::get_mut`. Construction is subtracted from the write batch:

| Elements | Before: added requested bytes | After: added requested bytes |
| ---: | ---: | ---: |
| 8 | 224,330 | 185,930 |
| 64 | 453,706 | 185,930 |
| 512 | 2,288,714 | 185,930 |

The 512-element batch requests about 92% fewer bytes. The remaining constant
cost includes call/control and reference bookkeeping; this does not claim
allocation-free source execution. The previous runtime fails the new
size-independence assertion; the improved runtime passes it. All six programs
return 42 with identical serialized artifact digests and all identical logical
VM counters before/after. In particular, existing size/allocation ceilings and
charges are not relaxed to reflect the lower physical cost.

The existing 64-entry hash-table construction drops from 34,054,600 to
29,000,456 requested bytes (about 15%), with identical 125,839 work ticks and
138,458 charged allocation elements. Sixteen lookups still add exactly
1,061,366 requested bytes at both 8 and 64 entries.

Four native regressions verify unique backing-pointer reuse, one-time shared
detachment, unchanged retained snapshots, exact logical charges, failed
projection/budget preservation, caller write-back, move holes, reversal, and
shared/captured-authority rejection. The selected library/runtime-storage/
service/standard-library/backend run passes 1,194 tests. Baseline, intermediate,
and final physical measurements are in `/tmp/grandiose-array-cow-diHVJ0/`.

The full Rust workspace subsequently passes 2,455 tests with zero failures
and two existing ignored manual VM benchmarks in 84.670 seconds, including a
2.42-second incremental build. Its 48 source-suite entries pass in 73.71
seconds. Cargo output and source-execution TSVs are in the `workspace/`
subdirectory above. The source audit passes before and after, with lock SHA-256
`a0d79c7e8c9e1054d53394726ef9cd66efbd3b77ebbfd3efdd32e68486bc8e2b`.
This is a local run, not a clean-checkout CI timing or an assertion of a
wall-clock speedup relative to earlier noisy workspace measurements.

## Measurement scope and remaining work

Requested bytes are cumulative successful allocation requests, with each
reallocation counted at its full requested new size. They are **not** live
bytes, peak RSS, distinct bytes retained, allocator metadata, or a census of
allocations made by other threads. The meter is test-only; it does not change
the production allocator or VM accounting. Allocation magnitudes are reported,
not asserted as values future runtime improvements must preserve.

Source inspection identifies concrete remaining work in
`crates/grandiose-stage0/src/vm_backend.rs`:

- `transfer_call_frame_value` now reuses shared loans/captures. Owned aggregate
  transfer and `rebase_caller_references` can still rebuild backing objects.
  `freeze_frame_value` remains necessary at independently retained capture
  boundaries and can recursively copy aggregates there.
- Length-changing array operations still use `to_vec()` and reconstruct
  backing arrays. Fixed-size mutation and projected-owner updates now detach
  only when shared; retained aliases still require copy-on-write detachment.
- Tail-call eligibility traverses entire surviving owners. The construction
  runs inspected 1,237 and 69,711 argument/owner elements respectively. This
  conservatively protects nested loans and frame-branded values, but its cost
  needs improvement without weakening those safety checks.

This is evidence of a remaining scaling problem, not proof that these sites
account for every allocation. Larger workloads, collision-heavy costs, full
copy accounting, peak memory, and G1 measurements remain required.

Measured input SHA-256 identities (the standard library and fixture are
unchanged between runs):

```text
stdlib/src/lib.glorious
  0e137aec812bcaa205ecafa8142d6e8f5f7d2e283f8d1a211a038ef3008c2366
crates/grandiose-stage0/src/vm_backend.rs
  before A09:
  7e6e910dbea127ce868b6ddf751fa8ad4cfddfa3a8f23a840ce7a57997376a8b
  after A09:
  97c3cb22c3473a30b3e004c45f6052790fc4b0bebcad18f70ef856cd82272ead
crates/grandiose-stage0/tests/fixtures/hash_indexing_profile.glorious
  8c2d17813e5e1da666fa56caccc33c4ffc9375d27d50e70cd6bd20483017ccfa
```
