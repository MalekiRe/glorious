# Host-compatible bytecode and unsafe-memory prerequisite

Approved September 5, 2026. The binding direction is [unsafe memory and the
native/VM ABI](../../docs/unsafe-memory-and-native-abi.md). This belongs to the
whole compiler project, ahead of further specialized VM collection algorithms.
The selected self-hosting path runs the compiler and source libraries, including
specialized generics and unsafe internals, as bytecode over real host-compatible
storage. The Glorious LLVM backend is deferred until after working, verified
self-hosting; it is not needed to implement or certify the initial VM/host ABI.

Current distribution is source-only, compiled on each user's machine. Independent
validation/admission of untrusted distributed bytecode is deferred, not a U3 or
self-hosting blocker. Source safety checks, existing bytecode consistency checks,
host capabilities, and version/budget bounds remain. Trust includes the local
compiler/runtime and any unsafe library implementations; source distribution
alone is not proof that unsafe code is sound.

| Gate | Required result | Current state |
|---|---|---|
| U0 | Source library ownership, concrete bytecode specialization, unsafe profiles, shared representation, and self-host-before-LLVM sequencing | Direction recorded; no execution claim |
| U1 | Bounded raw allocation, layout/alignment, uninitialized bytes, ownership handoff, native-address substrate tests | Rust substrate plus Stage0 per-run total/per-block memory accounting implemented; resident cleanup remains source-owned |
| U2 | Source raw pointers, unsafe scopes/callables/traits; propagation through inference, generics, interfaces, Core and MIR | Types/contracts and 23 bodyless memory leaves, including reference construction/address extraction, implemented |
| U3 | Versioned raw-memory bytecode and safety metadata; trusted execution of locally compiled source, preserving existing consistency checks | Initial Stage0 schema 96 executes raw memory for scalar/pointer/product/enum and native-reference residents, with native/static address leaves; independent G1 extension remains; untrusted-bytecode admission deferred |
| U4 | Host-layout addressable storage, allocator/drop/borrow/call ABI, actual VM/native roundtrips and callbacks using host fixtures without marshalling | Missing |
| U5 | Source `Vec`/slices specialized to bytecode over U1–U4 for application-defined types; ownership, failure, cleanup, and measured performance without native specialization | Missing |
| U6 | Execute strings/UTF-8/hashing and remaining collection algorithms as source bytecode, replacing specialized VM algorithms | Missing |

The initial Stage0 U3 path below exposes real raw storage to compiled source;
it does not claim a safe-only sandbox or the complete shared ABI. U4 must cross the actual
runtime/native boundary, not only call a Rust helper with a pointer. Stage0
programs and independent G1 artifacts have distinct contracts; implementation
in one does not certify the other.

Before self-hosting, U4 uses explicit ABI fixtures implemented by the native
embedding host (for example Rust/C), not native-compiled Glorious std. Tests must
run actual bytecode, preserve backing addresses and ownership, and exercise both
call directions, including bytecode callbacks/drop glue. They cannot certify
future LLVM output, which needs separate cross-backend tests after self-hosting.
U5 must include application-defined noncopy and zero-size types; a type-erased
native vector algorithm is not a substitute for specialized library bytecode.

The unsafe execution path permits genuine host-memory access and is not an
in-process memory sandbox. Existing checks and ABI compatibility remain; they
do not prove programmer-owned unsafe obligations or contain invalid raw writes.
Independent safe-only admission belongs to the later untrusted-bytecode project,
not the current source-distribution path. No new admission API is implemented.

After U1–U6, complete the existing GSC-2 semantic/service and M9 self-host/C2/C3
gates on the bytecode path. Only then implement the Glorious LLVM backend and
compare native output against the shared ABI and bytecode execution. Recording
this order does not close any outstanding M0–M10 compiler contract.

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

This U1 checkpoint introduced no source unsafe syntax, raw-pointer type, bytecode opcode, safety profile, native
import certificate, or collection migration is claimed by this checkpoint.
All frozen compiler parity contracts and U2–U6 remain open.

The uncommitted growable-Array optimization is deferred. Its patch is preserved
at `/tmp/grandiose-unsafe-foundation-qlNkxo/deferred-array-growth.patch` on the
development machine; the tracked runtime was restored to committed `84a0cabd`.
The already-committed copy-on-write correction remains. The temporary patch is
not a build or implementation dependency.

## U2: raw-pointer type foundation

Stage0 accepts `*const T` and `*mut T` in declarations and typed closures.
Pointer permission is distinct from safe-reference uniqueness. Pointee types,
regions, projections, and mixed-kind generic arguments survive normalization,
substitution, inference, coherent implementation selection, Core, and MIR.
Canonical type identity distinguishes permission and pointee without changing
existing safe-type encodings. Const pointees are covariant in nested lifetimes;
writable pointees are invariant. Higher-ranked lifetimes cannot escape through
pointer indirection.

Copying a pointer neither copies a resident nor creates a loan of its pointee.
Ownership/drop and safe-reference provenance traversal stop at the pointer;
type substitution and lifetime validation traverse it. Raw pointers do not
implicitly implement structural auto traits. Explicit implementations must
supply any such invariants. Owned-layout recursion stops at pointer indirection.

Twelve focused tests in `crates/grandiose-stage0/tests/unsafe_memory.rs` cover
these contracts, including malformed syntax, permission mismatches, alias and
projection specialization, typed closures, linear pointees, lifetime variance,
higher-ranked escape rejection, and coherence. Safe pointer dereference and
conversion to a safe reference remain rejected. The existing VM backend rejects
raw-pointer types rather than encoding them as an old reference or integer.
This initial type-only checkpoint did not implement unsafe syntax/call contracts,
raw-memory execution, independent admission, or actual VM/native interop.

Validation on September 5: full workspace 2,481 passed, zero failed, two existing
ignored manual benchmarks; build 34.69 seconds and all 48 source entries passed
in 72.39 seconds. The focused 12-test group was rerun after adding explicit
old-format VM-emission rejection coverage. Closure audits pass before and after;
the lock now also tracks type/parser/instance and ownership visitor sources.
Logs and source evidence: `/tmp/grandiose-raw-pointer-types-zaZWde/`.
Source-lock SHA-256:
`92b3be2a22f77e127bb8bff0de757ba7eeddce6bc26291d62c7823bdb5cead9d`.
No frozen compiler parity contract is closed by these development tests.

## U2: unsafe scope and callable contracts

Stage0 now accepts `unsafe fn`, `unsafe (...) -> Result` callable types (also
`unsafe fn(...) -> Result`), explicit `unsafe { ... }` blocks, unsafe traits,
and unsafe trait implementations. The top-level qualifier order is
`pub unsafe auto trait` or `pub unsafe host CAP fn` where applicable.

Callable safety is independent of effects and invocation quantity. It survives
inference, aliases, generic and higher-ranked specialization, trait selection,
normalization, Core, and MIR. Safe and unsafe callable identities are distinct;
there is no implicit function-pointer safety coercion. An inferred closure may
receive an unsafe contextual call contract, but that does not authorize unsafe
operations in its body. Intrinsic `Fn` and `Label` evidence only covers safe
callables, including when a forged concrete assumption is supplied to the solver.

Invoking an unsafe callable requires an explicit block, including inside an
`unsafe fn`. Lexical permission is reset in typed/inferred/contextual closures
and handler arms. Explicit blocks do not disable safe borrow, use, or effect
checking. Frozen Core stores block identities and independently reconstructs
permission along structural paths, resetting it at deferred body boundaries;
removing the scope or moving the call outside it is rejected. Unsafe scopes and
call contracts participate in semantic identity without changing existing safe
type or body fingerprint encodings. Handler replay checks do not mistake an
unsafe scope or unsafe call for a replay-safe empty-effect computation.

An unsafe trait requires `unsafe impl` for a positive implementation. Negative
implementations make no safety assertion and cannot use `unsafe impl`. A safe
trait rejects `unsafe impl`; method safety must match the trait's own method
contract exactly. Trait safety is an implementer obligation, not a blanket
unsafe requirement on otherwise-safe methods. Frozen Core conservatively records
all unsafe implementation identities available in its source world, because
their promises may affect static evidence without emitting pointer operations.
These are execution requirements, not native-export trust certificates.

MIR retains the callable safety contract separately from its unsafe-execution
requirement (explicit scopes or available unsafe implementations). Lifted bodies
and specialization preserve those facts. MIR checks indirect unsafe-call
requirements and callable-value safety against the actual target. Existing
bytecode emission rejects unsafe function contracts, unsafe callable values, and
unsafe implementation requirements rather than erasing them into schema 93.
This is not U3 admission or an unsafe-capable runtime; raw loads/stores, allocation
instructions, shared layouts, and native interop remain unimplemented.

The focused group now contains 22 tests covering raw-pointer and unsafe contracts,
including negative source cases and deliberately altered Core/MIR products.
The Rust and source `stage0_identity` constructors both advance language/interface
generations to two, cache generation to five, and verifier generation to seven.
Bytecode generation 48 and schema 93 are unchanged: this checkpoint rejects,
rather than executes, the new unsafe requirements.

Final validation on September 5: all 2,491 workspace tests passed, zero failed,
two existing ignored manual benchmarks. Wall time was 122.429 seconds including
43.67 seconds build; all 48 source entries passed in 69.91 seconds. The prior
pre-generation-bump run also passed (129.840 seconds). Source closure audits
pass before and after; no time or memory guard was relaxed. Logs and source
evidence: `/tmp/grandiose-unsafe-contracts-FgyrYG/`. Source-lock SHA-256:
`309f8acd7a563e904b46ea16f7a884d82aa4e09aa0b6ce72389dc46b0044694b`.
U2 remains partial until raw operations are implemented; U3–U6 and all 11,455
frozen public compiler contracts remain open.

## U3: initial locally compiled raw-memory execution

Stage0 schema 94 now carries raw-pointer types, unsafe callable types, function
safety and execution requirements, and the record-versus-enum layout distinction.
It adds one structurally typed memory instruction family (opcode 194) with 16
finite machine operations. Rust and source build identities advance cache to six,
bytecode to 49 and verifier to eight; language/interface remain two. Decoders
reject older Stage0 schemas before reading the changed payload. Released G1
encodings, feature bits, and independent verifier are unchanged.

The runtime manifest binds bodyless declarations (`unsafe fn read<T>(p: *const T)
-> T;`) to size/alignment, null/dangling, allocate/resize/release, pointer offset/
cast/const conversion, typed read/write, and overlapping/nonoverlapping copy.
All pointer operations require explicit unsafe blocks, even inside unsafe
functions. Missing declaration bindings are compilation errors. All canonical
standard-library machine leaves now use declarations without bogus unit bodies.
The Rust/source primitive inventories agree on unique tags 183–198; legacy tags
and their relative ordering are unchanged.

Raw storage uses actual host pointers and retains allocation provenance, including
when a pointer is itself stored in memory. Concrete scalar, pointer, unit, tuple,
record and enum layouts use natural host alignment on 64-bit targets. Enums have
a u32 discriminant followed by an aligned payload union; records retain field
order and trailing padding. Typed stores move VM residents into native storage;
typed loads reconstruct private register values, reading initialized fields rather
than padding. Bulk movement preserves padding as bytes. This is not reconstruction
at a VM/native call boundary, and not yet shared native layout for every VM value:
references, callables, static-data handles and legacy text/bytes/arrays still lack
the full address/call ABI and are rejected by these layout operations.

Each execution owns its allocation registry and enforces total/per-block native
byte limits (defaults 16 MiB/1 MiB). Zero-byte allocations retain alignment without
owning bytes; source still owes all logical resident uses. A rejected resize
preserves its registered owner and initialized prefix. Releasing an allocation
or ending execution frees bytes, not resident drop glue or host ownership.

Safe Rust execution entry points do not permit raw operations. Explicit unsafe
per-call APIs require the embedding caller to uphold the unsafe source contracts
for that run; an artifact field cannot grant this permission. CLI `run` uses this
path for its trusted local source compilation, while `run-vm` continues to reject
unsafe execution from serialized files. There is no new two-phase admission API.

Nine integration tests execute bodyless bindings, generic movement of a linear
padded record, exact field offsets, one/multiple-variant enums, zero-sized linear
residents, overlapping/disjoint movement, resize, and pointer-resident provenance.
The shared allocator now has 13 strict-provenance Miri tests, including field
layout composition. Three Stage0 allocation-registry unit tests cover budgets,
rollback, over-alignment and zero-byte transitions. Full U4 interop, source Vec,
resident cleanup/cancellation, and U5–U6 remain open; these primitive tests do not
certify those gates.

Validation: the normal workspace/all-target suite passes with no failures,
including all 48 source-compiler entries (69.78 seconds). The 13 allocator tests
completed under strict-provenance Miri. The full source/interpreter Miri run was
stopped at the user's request to prioritize implementation; it is not claimed
as completed evidence. Further Miri runs are deferred unless needed for a bug.

## Native-backed checked references

Stage0 schema 95 adds two bodyless unsafe constructors, `memory-borrow-shared`
and `memory-borrow-unique` (tags 199–200). They retain a real storage pointer and
out-of-band layout metadata, not a snapshot of the resident. Checked projections,
loads/stores, nested calls and returned references operate on the original
allocation. A native reference does not need lexical register rebasing or
capture-time value reconstruction. Null and misaligned construction fails;
remaining validity, initialization, aliasing and selected-lifetime obligations
belong to the unsafe caller.

Core distinguishes unsafe-established reference provenance from both static
references and ordinary caller-derived loans. Only an unsafe callable with a
direct reference result can carry this provenance. Its otherwise-unbound output
lifetime can be selected by the result context; ordinary argument-derived
lifetimes still take precedence. Safe wrappers continue to expose the frozen
borrow relation from their parameters. Nested calls now open the outer callee's
parameter regions without treating them as rigid body lifetimes; the outer call
still jointly checks its arguments. Cache/bytecode/verifier generations are
seven/50/nine in Rust and source.

The raw-memory integration group has 12 tests, adding projected mutation through
nested calls, reference-return storage identity, and rejection of extended or
overlapping safe owner loans. The 236 Core tests and 22 unsafe-contract tests
pass with the lifetime change. No further Miri run was started. This is not yet
native layout for every VM register value or a complete VM/native call bridge;
storing legacy frame references, callable payloads, and old collection handles
in raw residents still requires that work. Source Vec and cleanup remain next.

## Source ownership markers

Generic manual `Use` rules now instantiate their head and prove their where-bounds
for the selected type. Unresolved conditional rules do not fall back to the
unrestricted field layout. Ordinary trait bounds and principal `Use` obligations
share one bounded query, including lexical supertrait evidence and mixed-cycle
rejection. Generic custom `Drop` declarations are checked under their own bounds;
MIR likewise checks the whole aggregate under those bounds before copying it.

The standard library declares `PhantomData<T> {}` in ordinary source, with
`impl<T, q: Quantity> Use<q> for PhantomData<T> where T: Use<q> {}`. A forwarded
quantity selects the widest public interval its bounds prove, not independent
overlapping ownership permissions. Unconstrained quantity forwarding is rejected.
The marker has zero native size and follows the logical element's quantity. An
additional source-defined affine marker can make a raw pointer owner affine for
discardable elements and exact-linear for exact-linear elements, without a dummy
element or runtime collection special case. This is an ownership-quantity
building block, not a complete pointer-owner lifetime/drop implementation.

Focused validation passes: 13 raw-memory, 80 signature, 65 trait-solver, 128 standard
library, 22 request/revision and four conditional-Drop service tests. The new source
fixture executes a zero-sized marker and rejects owner reuse after a move. Rust and
source cache generation is eight; bytecode/verifier remain 50/nine. Vec migration,
native representation of all resident types and VM/native calls are still open.

## Native reference residents and two-word source views

Stage0 schema 96 stores a native-backed checked reference as exactly one actual
referent pointer. Typed loads recover its checked-reference metadata; fields,
mutation and relocation keep accessing the original referent. Pointee layout is
resolved lazily, so a reference terminates recursive value layout. Raw reads may
establish unsafe provenance for nested references or abstract `T`, not only a
direct reference result. Only an unsafe callable can establish this origin;
safe calls still require their existing frozen caller-region evidence.

Five additional bodyless leaves expose shared/unique native reference addresses,
cast const pointees, and expose sealed UTF-8/raw-byte literal addresses (authority
tags 201–205). Literal addresses retain their original immutable backing bytes
for the execution's data domain. They do not copy bytes into legacy arrays. A
legacy frame-backed reference still fails raw residency/address extraction until
its referent has real native-addressable storage; no Rust handle is substituted
for that address. Cross-execution reference retention is not exposed by these
runner APIs and remains part of the full module/host ownership ABI work.

A source fixture now implements two-word checked views using `&'a ()` or
`&'a mut ()` plus a length. The zero-sized referent reference carries the owner
loan and the actual data pointer. Unsafe source operations recover its typed
data pointer; safe bounds/splitting policy stays in source. The fixture verifies
16-byte layout, disjoint mutable splitting and write-through, and rejects owner
mutation while a shared view is live. This is a tested source representation,
not yet the canonical standard-library `Slice` migration. A Rust unit test
independently checks that reference storage contains the original pointer.

The canonical library also binds the existing catchless `abort() -> !` leaf
with a bodyless declaration for allocation-policy failures. No new abort opcode
or collection algorithm is introduced. Runtime authority inventory is 206 in
Rust, source and the shared witness; cache/bytecode/verifier generations are
nine/51/ten. Native register homes, callable residents, complete ownership/drop
handoff and actual VM/native call fixtures remain open alongside the source
collection migration.
