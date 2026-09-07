# Native backing-storage evidence

The authoring runner now reports `VmAuthoringProfile::native_memory` separately
from logical VM allocation-element charges. This is event-based measurement of
VM-owned native backing extents, not a physical allocator census or completed
M1 certification. Ordinary execution keeps its existing admission policy; only
the opt-in authoring runner creates the shared measurement recorder.

## What is measured

Raw source buffers and native homes for addressable VM values have separate
live/peak byte and allocation/release counters. Their combined peak is observed
when an allocation or resize succeeds, not sampled at VM instruction boundaries
and not computed by adding independent peaks. The actual allocation owner
records release, including a temporary home rejected by a subsequent logical
budget check. Repeated retirement does not count twice.

Zero-byte dangling allocations acquire no backing block. A resize from zero is
an allocation, a resize to zero is a release, and a successful changed nonzero
extent is a reallocation. Same-size resizes and failed allocation/admission
requests do not inflate successful counters. Cumulative operation and bulk-copy
counters saturate explicitly; `counters_saturated` makes such results lower
bounds rather than silently wrapped measurements.

The copy counters measure explicit raw copy/copy-nonoverlapping leaves and
native-home bulk transfers/exports. They do not count scalar loads/stores or
pretend to observe a system allocator's internal realloc copies. The snapshot
is taken before final allocation-domain teardown, so an outstanding raw buffer
does not disappear from the evidence just because that teardown will free it.
Successful authoring runners expose snapshots; failed-admission unit tests
inspect their local recorder directly. A public failed-run profile is not yet
provided.

## Boundaries

Byte sizes are requested host-native layouts, not allocator usable sizes, RSS,
or allocator-internal old/new overlap during realloc. Rust metadata, interpreter
containers, static data, and externally owned native argument storage are not
included. Native-home bytes include applicable local/call storage, but do not
establish a complete frame-memory census. These measurements do not attribute
all costs to compiler request/phase budgets or establish transport-polling and
latency bounds.

Source-suite execution records retain logical counters and add native counters
plus the executing Rust process's architecture, OS, pointer width, and byte
order. Unprofiled fields remain empty, not zero. The execution report states
these scopes and remains `release_ready: false`; the bytecode schema is unchanged.

## Current checks

Five new unit histories check raw growth/shrink/rejection, zero-size ownership,
combined peaks between instruction ticks, failed temporary-home cleanup,
one-shot retirement, external views, bulk transfers, and counter saturation.
A combined-peak history has independent raw/home peaks of 32/136 bytes but an
actual combined peak of 136 bytes, with no instruction tick between events.

Two decoded/runtime source histories check exact raw operations and copies,
run isolation, and visibility of an abandoned eight-byte buffer before domain
teardown. The standard-library Vec history has a 13-byte raw peak (eight-byte
grown source plus five-byte destination), nine bulk-copy bytes, two allocations,
one reallocation, and two releases. A zero-sized Vec still has logical VM
charges but no raw backing allocation.

The real source-copy/cancellation history passes in 106.10 seconds with new
assertions that both raw and native-home bytes return to zero, in addition to
its existing request/root/phase cleanup checks. This is measured native backing
cleanup, not merely a reservation-counter assertion.

The broader run passes 215 unit, 169 standard-library, 109 destruction, 17 native
bridge, and 11 runtime-memory tests (`target/native-profile-authoring-full.log`).
It also reports the two previously recorded destruction failures and 19 further
native-suite failures: 17 fixture compilation failures involving missing
operator/Boolean scope, one missing legacy metadata assertion, and one expected
diagnostic mismatch. Those native suites are not certified by this run.

The final full source gate passes all 56 tests in 362.25 seconds
(`target/compiler-check/run-51ln7pdm/report.json`), with the existing 12 workers
and resource guards and `release_ready: false`. All 58 records have the complete
29-column schema. All 32 profiled executions finish with zero raw/home live
bytes and no saturated counters; the 26 unprofiled records keep those fields
empty rather than reporting unmeasured zeroes.

On this x86-64 Linux run, the source-copy batch records 50 raw allocations and
50 releases, 19 resizes, 9,498 home allocations and releases, and 16,434 raw
bulk-copy bytes. Its raw peak is 41,505 bytes, home peak 197,456 bytes, and
simultaneous combined peak 213,840 bytes. Its 3,496,018 logical allocation
elements are a separate counter, not a byte measurement.

That earlier batch also reaches a measured call depth of 8,234. It includes source
construction and exact byte comparisons as well as copying/cancellation, so
that measurement alone does not identify which operation causes the depth.

## Library stack-depth localization

Isolated static-slice comparison, bulk-copy-then-UTF-8-validation, and vector
resize probes separate the operations without using resize to construct the
comparison or validation inputs. Before the change, 256/1,024-byte comparisons
reach authoring depths 262/1,030 and UTF-8 validation reaches 263/1,031. Resize
reaches 14/16 with authoring recycling, but **all three** fail an ordinary
runner's 128-frame limit at both sizes.

The source library now traverses balanced ranges, preserving left-to-right
comparison/first-error order and sequential vector pushes. UTF-8 subdivision
passes the actual decoded character end into the right range, including when
the character spans the midpoint; decoding still uses the complete input.
This bounds these algorithms' stack growth logarithmically in input length,
without depending on optional authoring tail recycling, weakening native-home
borrow protections, or increasing execution limits. It is not a constant-stack
claim for the compiler or a completed M1 gate.

The initial post-change 256/1,024-element probes pass in both runners with a
128-frame cap. Measured authoring depths are 15/17 for comparison, 17/19 for
UTF-8 validation, and 18/20 for resize. The permanent regressions also exercise
inputs beyond the default 16,384-frame ceiling and compare valid/error UTF-8
positions against Rust while checking recovery of the original owned bytes.

All 171 standard-library tests pass (`target/bounded-stack-stdlib.log`,
129.34 seconds in the debug test profile). The 16,417-element cases run in
both ordinary and authoring modes under the 128-frame cap; measured authoring
depths are 22 for comparison and 24 for validation/resize, with zero final
raw/home live bytes. The UTF-8 oracle batch covers 51 valid/invalid inputs.
A supplementary ordinary CLI probe (`target/bounded-stack-order.glorious`,
output `target/bounded-stack-order.log`) also checks ten empty, prefix,
first-difference, and Unicode-byte ordering cases; its expected result is
`(0, -1, 1, -1, 1, -1, 1, 1, 0, -1)`. This probe is additional local evidence,
not an extra counted suite test.

The subsequent full source gate passes all 56 tests in 368.27 seconds
(`target/compiler-check/run-28gl455c/report.json`). Its 58 records retain the
existing 12 workers and resource guards and `release_ready: false`. All 32
profiled executions finish with zero raw/home live bytes and unsaturated
counters; all 26 unprofiled records leave the native fields empty.

The same source-copy batch now reaches **33 frames**, down from 8,234. Its
native-home peak falls from 197,456 to 4,720 bytes, and combined backing peak
from 213,840 to 45,161 bytes. Raw peak (41,505 bytes), raw allocations/releases
(50 each), resizes (19), and raw bulk-copy bytes (16,434) are unchanged. The
9,500 home allocations are matched by 9,500 releases.

This stack improvement has a measured work tradeoff: logical VM work ticks
increase from 13,685,582 to 20,952,222, and allocation-element charges increase
from 3,496,018 to 5,586,722. Balanced traversal visits internal range nodes as
well as leaves; reduced peak storage does not imply less aggregate interpreter
work. Further work-cost optimization and the remaining M1 census/polling gates
remain open. No source-copy chunk size, request charge, or execution limit was
raised to obtain these results.

## Unexposed owner-move backing transfer

The native owner-move follow-up permits an ordinary checked whole-owner move to
transfer a uniquely held, never-exposed home to a vacant, exactly typed native
destination. The four-case unit history verifies one 16-byte allocation and
zero bulk copies for that transfer, while exposed/shared homes and preexisting
destinations retain the copy path. All cases release their backing completely.
The owned native Pair roundtrip now executes within its unchanged two-Pair
memory cap; see [native fixture revalidation](unsafe-memory-progress.md#native-fixture-and-owner-move-revalidation-september-7).

The full source gate after this change passes all 56 tests in 395.95 seconds
(`target/compiler-check/run-uin4h5j2/report.json`). The 58 records retain 12
workers, existing limits, and `release_ready: false`; all 32 profiled runs have
zero final raw/home live bytes and unsaturated counters, and all 26 unprofiled
records leave the native fields empty. The source-copy batch retains the same
artifact digest and all backing/work measurements from `run-28gl455c`, including
33 frames and a 45,161-byte combined peak. This follow-up demonstrates the
native owner-transfer case, not an additional source-copy speedup.
