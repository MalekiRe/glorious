# Unsafe/native-library prerequisite

Approved September 5, 2026. The binding direction is [unsafe memory and the
native/VM ABI](../../docs/unsafe-memory-and-native-abi.md). This belongs to the
whole compiler project, ahead of further specialized VM collection algorithms.

| Gate | Required result | Current state |
|---|---|---|
| U0 | Library ownership, unsafe obligations, guest/native trust boundary, shared representation requirements | Direction recorded; no execution claim |
| U1 | Bounded raw allocation, layout/alignment, uninitialized bytes, ownership handoff, native-address substrate tests | Initial Rust substrate passes native and Miri tests; guest budget/admission integration remains |
| U2 | Source raw pointers, unsafe scopes/callables/traits; propagation through inference, generics, interfaces, Core and MIR | Missing |
| U3 | Versioned unsafe metadata/instructions; independent safe-only guest verification and authenticated native export admission | Missing |
| U4 | Shared concrete layouts, allocator/drop/borrow ABI, actual VM/native roundtrips without marshalling | Missing |
| U5 | Source `Vec`/slices over U1–U4; ownership, failure, performance, and backend comparisons | Missing |
| U6 | Migrate strings/UTF-8/hashing and remaining collection algorithms out of specialized VM operations | Missing |

U1 alone does not expose pointers to Glorious programs. U2 without U3 cannot
authorize unsafe bytecode or claim a safe-only sandbox. U4 must cross the actual
runtime/native boundary, not only call a Rust helper with a pointer. Stage0
programs and independent G1 artifacts have distinct contracts; implementation
in one does not certify the other.

## U1: shared raw-storage substrate

`crates/grandiose-runtime` supplies `MemoryLayout` and `RawAllocation`, reused
through the VM's trusted embedding API. It has no resident type, initialized
length, collection growth policy, or element callbacks. Allocation is bounded
per block; the existing guest execution and total-memory accounting must still
be integrated before this storage becomes a bytecode facility.

Validated layouts reject invalid alignment, arithmetic overflow, and extents
beyond the host allocator's addressable bound. Empty allocations retain
alignment without allocating. Explicit raw ownership handoff preserves the
address; reclaiming raw parts is unsafe and requires the exact allocation domain
and sole owner. Resizing preserves the retained byte prefix and leaves pointer,
layout, and contents unchanged on failure. Release frees bytes, not residents;
trusted library code must discharge resident/reference obligations first.

Twelve unit tests cover these properties, including injected allocator failure,
over-aligned relocation, noncopy residents, and zero-size resident destruction.
Two embedding tests pass a shared-representation record directly to a native
function and transfer ownership without reconstructing its elements. These are
Rust/native substrate tests, not executed VM/native calls or a stable ABI.

Validation on September 5, 2026:

- Focused runtime/VM group: 396 passed, one existing ignored manual benchmark.
- Both new test targets pass under nightly Miri with
  `MIRIFLAGS=-Zmiri-strict-provenance` (12 + 2 tests).
- The 12 raw-storage tests also execute on `x86_64-unknown-linux-musl`.
- Runtime crate Clippy passes with `--all-targets -- -D warnings`.
- Full workspace: 2,469 passed, zero failures, two existing ignored manual
  benchmarks, 126.214 seconds wall including 43.92 seconds build. All 48 source
  entries pass in 72.97 seconds; closure audits pass before and after.

Logs: `/tmp/grandiose-unsafe-foundation-qlNkxo/`, with full source evidence under
`workspace/`. Source-lock SHA-256:
`0c909ad17ac8894bce26244b70fdfb17b84472710fa7823dadd4ac2ccffd5cac`.
All existing command and memory limits were retained. Miri ran under the direct
8 GiB guard. GNU-target Valgrind could not start without loader debug symbols;
the musl fallback reported no errors but tracked zero heap allocations, so it
is not counted as a heap-safety certificate. Miri is the memory-model evidence.

No source unsafe syntax, raw-pointer type, bytecode opcode, safety profile, native
import certificate, or collection migration is claimed by this checkpoint.
All frozen compiler parity contracts and U2–U6 remain open.

The uncommitted growable-Array optimization is deferred. Its patch is preserved
at `/tmp/grandiose-unsafe-foundation-qlNkxo/deferred-array-growth.patch` on the
development machine; the tracked runtime was restored to committed `84a0cabd`.
The already-committed copy-on-write correction remains. The temporary patch is
not a build or implementation dependency.
