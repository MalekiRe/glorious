# Unsafe/native-library prerequisite

Approved September 5, 2026. The binding direction is [unsafe memory and the
native/VM ABI](../../docs/unsafe-memory-and-native-abi.md). This belongs to the
whole compiler project, ahead of further specialized VM collection algorithms.

| Gate | Required result | Current state |
|---|---|---|
| U0 | Library ownership, unsafe obligations, guest/native trust boundary, shared representation requirements | Direction recorded; no execution claim |
| U1 | Bounded raw allocation, layout/alignment, uninitialized bytes, ownership handoff, native-address substrate tests | In progress |
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

The uncommitted growable-Array optimization is deferred. Its patch is preserved
at `/tmp/grandiose-unsafe-foundation-qlNkxo/deferred-array-growth.patch` on the
development machine; the tracked runtime was restored to committed `84a0cabd`.
The already-committed copy-on-write correction remains. The temporary patch is
not a build or implementation dependency.
