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
| U2 | Source raw pointers, unsafe scopes/callables/traits; propagation through inference, generics, interfaces, Core and MIR | Types/contracts and 25 bodyless memory leaves, including reference construction/address extraction and unsafe forgetting, implemented |
| U3 | Versioned raw-memory bytecode and safety metadata; trusted execution of locally compiled source, preserving existing consistency checks | Stage0 schema 106 establishes native source homes, owned native argument/result placement, selected destructor metadata, callable environment cleanup and frozen frame cleanup plans, executes raw memory, guarded owned-slot operations and delimited handler completion, retaining source contracts for native linking; independent G1 extension remains; untrusted-bytecode admission deferred |
| U4 | Host-layout addressable storage, allocator/drop/borrow/call ABI, actual VM/native roundtrips and callbacks using host fixtures without marshalling | Partial: native homes, capability-bound calls, synchronous owned aggregate arguments/results, bytecode callbacks and selected destruction-code identity; private Array/callable layouts, durable ownership/callable ABI, complete copy/use-operation identity and physical boundary costs remain open |
| U5 | Source `Vec`/slices specialized to bytecode over U1–U4 for application-defined types; ownership, failure, cleanup, and measured performance without native specialization | Pointer-backed Vec/slices, structural/generic destruction, source Vec resident/buffer cleanup, normal owned-capture cleanup and cancelled ordinary-frame cleanup implemented; other nonlocal/replay exits, complete temporary ownership and full resident ABI remain incomplete |
| U6 | Execute strings/UTF-8/hashing and remaining collection algorithms as source bytecode, replacing specialized VM algorithms | Source UTF-8, collections and unkeyed BLAKE3-256 implemented; legacy artifact-opcode retirement, complete runtime/ABI certification and remaining work open |

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

## Canonical source Vec, slices and UTF-8 algorithms

The bundled `Vec<T>` now owns a typed pointer, initialized-prefix length and
capacity. Source code implements growth/overflow policy, push/pop, insertion,
removal, append, reserve, splitting, draining, swapping and truncation. Two
zero-sized source markers retain logical element quantities and prevent copying
an allocation owner. `Slice` and `SliceMut` use the previously tested two-word
reference/length representation. Safe exports with historical `unchecked` names
still check bounds and abort before deriving an invalid reference.

`String` now encodes/decodes/validates UTF-8 and edits byte ranges in source;
the hash tables access residents through source Vec functions. Obsolete array
algorithm bindings and static-to-array view bindings have been removed from the
bundled package and its default manifest. The obsolete instructions have also
been removed from both VM backends. Three Array leaves remain solely for the existing
opaque BLAKE3 input/output bridge; Vec's own representation never contains Array.

This is an implementation checkpoint, **not completion of ownership cleanup**.
`vec_release_empty` explicitly releases an emptied allocation after append, but
ordinary owner destruction and generic `discard<T>` do not yet elaborate full
source Drop glue. Truncation removes residents from the initialized prefix but
does not yet reliably invoke their custom destructors. The per-execution native
registry currently reclaims otherwise unreleased byte allocations at execution
end, not at every source lifetime end. Until cleanup is implemented this can
retain allocations and omit observable element hooks; nested owners, early
exits and replacement still need correct structural/generic destruction.

Other U4 gaps remain: references to ordinary VM-frame residents cannot yet be
stored in native collections; callable residents and actual VM/native calls
need their shared ABI. Existing passing collection tests do not certify these
missing cases. No new Miri run was performed for this checkpoint.

The rewrite exposed a trait specialization bug: dependency discovery used
executable-key evidence as implementation binder arguments. It now uses the
same receiver/head substitution as body materialization, including generic
Default implementations. Profiled execution now has explicit unsafe entry
points for trusted locally compiled source; existing safe runners retain their
unsafe-execution rejection.

Two further general leaves provide unsafe `forget<T>` (caller discharges the
logical obligations; no Drop hook runs) and sealed raw-literal length. Authority
tags 206–207 are preserved. After retiring 28 collection/static-view roles,
the shared active inventory contains 180 entries with reserved numeric gaps.
Stage0 schema/cache/bytecode/verifier generations are 98/eleven/53/twelve.

The final bundled `__g1_array_len` dependency has subsequently been removed.
It queried only the BLAKE3 result, whose exact 32-byte output is already part
of the hash leaf's contract. The declaration and default runtime binding are
gone; three legacy Array leaves remain for that byte bridge. Regression tests
compare all digest bytes with the hash oracle for empty, textual and binary
input. They check behavior, not the absence of an opcode.

The retired operations' enum variants, decoders, encoders, lowering, execution,
verifier branches and manifest signatures are deleted. This includes collection
mutation/growth/move helpers, array UTF-8 operations and old static-array views.
The surviving element-borrow instruction is shared-only. Static-array facade
values and logical array-capacity bookkeeping are removed, as are verifier
summaries specific to the deleted move/pop/finalization operations. G1 no longer
advertises the retired capacity/finalization features or accepts the old seed
identity. No instruction IDs are reassigned and no replacement collection
intrinsics were introduced. Historical public-contract inventory rows remain
historical audit records, not active runtime capabilities.

Validation of this cleanup covered the bundled collection behavior and both
Rust VM suites. At that checkpoint the full-closure GSC2 manifest test failed during source
checking: compiler modules still duplicate moved Vec/String-backed values or
request duplicable collection bounds after the source ownership rewrite. That
compiler-source migration is not implemented by deleting VM instructions; the
GSC2 test remains visible and failing rather than weakening its ownership checks
or narrowing the tested production closure.

## Compiler-source ownership migration

The compiler closure now compiles with the pointer-backed standard library.
An ordinary source `Clone` trait constructs independent Vec/String owners;
PackageKey, ModuleKey, InstanceKey, dependency Node and diagnostic records supply
explicit implementations. Dependency walks inspect borrowed frames/statuses;
deduplication swaps residents, and freezing transfers dependency buffers and
completed statuses into published traces. Retained indices own cloned keys.
Diagnostic provenance uses explicit cloning and affine sorting/deduplication.
Whole-diagnostic and identity cloning still require physical/copy accounting;
these changes do not certify bounded work for every source step or finish Drop.

Stage0 now derives a qualified trait operation's Self type from its declared
parameter shape, consistently during direct/first-class selection and executable
specialization. A blanket implementation no longer mistakes `&Self` for Self.
Nonbinding enum completion arms permit scoped payload borrows. Record payloads
retain field names and private authority, including when a negative test proves
the sole alternative. Regressions reject out-of-scope/private projections and
execute the corresponding public access. The cache generation is thirteen;
language/interface three, bytecode 53, verifier twelve and schema 98 are unchanged.

The GSC2 harness executes only its locally compiled, independently decoded and
verified source closure through the existing explicit unsafe authoring APIs.
It does not enable unsafe execution for external artifacts or weaken the safe
APIs. Reports identify the trusted unsafe standard library and disclaim an
in-process memory sandbox. Every fixture still compiles the complete production
closure, and every batch retains one unchanged execution budget.

The ownership regressions include all eight cloned dependency-key variants:
mutating the clone changes its identity while the original remains unchanged,
including in-place edits of nested String storage and substitution bytes.
Dependency histories retain their canonical ordering, missing/cycle precedence,
red/green behavior, cancellation, capacity and stale-parent assertions. Source
admission now creates distinct inputs for independently consuming histories;
namespace checks finish borrowed inspection before consuming the admitted value.

Temporary allocation tracing of the two still-failing batches found cumulative
VM value-element pressure, not exhaustion of the native-memory byte budget.
At the unchanged 16,777,216-element ceiling, bootstrap admission had charged
13,253,800 elements for 403,845 direct call frames (13,678,099 work ticks).
The eight-history registry batch had charged 10,639,006 elements for 379,570
direct call frames, plus 2,434,710 native-resident field elements
(11,453,754 work ticks). These are partial measurements at failure, not completed
profiles or live-byte counts. The tracing was removed; neither allocation
accounting nor test ceilings were changed. Reducing actual call/materialization
overhead remains open, alongside the ownership/ABI prerequisites above.

Validation: 1,841 Stage0 regression tests pass across the library, body, Core,
MIR, headers/interfaces/resolution/signatures/coherence, request, service,
standard-library, trait solver, runtime-memory/manifest and VM-backend targets.
`cargo check --workspace --all-targets` succeeds with existing G1 dead-code
warnings. The unfiltered source suite finishes in 198.97 seconds with **46
passed and two failed**, both allocation failures described above. Its closure
audits pass before/after, with 30 locked source files and all 11,455 historical
public contracts still open. `target/compiler-check/run-b68ogeof/report.json`
correctly records failed complete-suite/capability status, not release readiness.
Logs: `/tmp/grandiose-inherent-impl-wjVcSD/owned-regression2.log`,
`compiler-check-owned2.log`, `owned-check.log`, and `allocation-trace.log`.

## Source call-frame costs

The two allocation failures above are resolved by three standard-library source
changes, with no VM, opcode, runtime manifest, accounting or resource-limit change:

- `Vec::reserve` retains its checked required-length calculation and capacity
  test, but moves the allocation/growth path into a private inherent helper.
  A no-growth call now materializes 24 registers instead of 129. The growth
  policy, overflow checks and failure behavior are unchanged.
- `ByteCursor::u64` validates the entire eight-byte extent before entering a
  private unsafe reader. That reader loads eight `u8` residents through the
  existing raw-memory leaves and assembles little-endian bits with existing
  integer leaves. It performs no unaligned native `u64` load. The source cursor
  advances only after success, and retains its position on truncation.
- The existing opaque BLAKE3 bridge reserves the fixed 32-byte output once,
  writes its uninitialized slots directly, then publishes the initialized
  length. It no longer calls Vec push/reserve separately for every output byte.
  The opaque hash and three legacy Array leaves still serve its input/output
  bridge; this is not source BLAKE3 or completion of the source hashing gate.

The new byte-cursor regression checks all eight alignments and all nine available
widths (zero through eight), on both literal and owned Vec-backed windows:
144 checks against native little-endian expectations, including high-bit bytes
and unchanged positions after failed reads. Existing hash regressions still
compare all 32 digest bytes for empty, textual and binary input. The preallocated
Vec probe rejects the old reserve body: the exact steady-state charge drops
from 171 to 66 elements per push. Its independent physical meter records 47,646
versus 34,206 requested bytes per push; see [runtime costs](runtime-costs.md).

The unfiltered compiler-source suite passes **48/48** in 238.70 seconds, under
the unchanged time/memory guards and one default budget per complete batch.
The two formerly failing batches now finish with these uninstrumented profiles:

| Batch | Complete result | Work ticks | Charged allocation elements | Peak call depth |
| --- | --- | ---: | ---: | ---: |
| Bootstrap admission | `[145, 80, 13]` | 17,059,970 | 15,234,206 | 68 |
| Eight source registry histories | `[35, 96, 47, 235, 750, 466, 91, 91]` | 10,338,235 | 13,655,644 | 183 |

Both are below the original 16,777,216-element ceiling. These are cumulative
budget elements, not physical or live bytes. Temporary call tracing was removed
before these runs. An intermediate diagnostic-only over-budget replay was not
used as passing gate evidence; the normal harness has no retry or larger budget.
No fixtures were split, removed or filtered, and all comparator assertions remain.

`target/compiler-check/run-3jneul71/report.json` records 50 execution rows,
empty test filters and a passing complete-current-suite status, with
`release_ready: false`. Closure audits pass before/after with 30 source files
and all 11,455 historical public contracts still open; source-lock SHA-256 is
`9f6c2cc238d1cdd9da7c476d424d943509418c3254fdc8b4387b0e6f43207150`.
This run overlapped the workspace check and is not a wall-clock speedup claim.

The physical-storage and static-data harnesses now use the existing explicit
unsafe runner only after compiling their local source and independently verifying
the artifact. Static fixtures call the canonical inherent `Str` operations;
obsolete free-function aliases are not restored. Assertions for sealed type/tag
identity, private literal wrappers, byte counts and subslice length remain.
All four physical-storage tests and all ten static-data boundary tests pass.

The final full workspace/all-targets run passes **2,532 tests, zero failures**,
with two existing ignored manual VM benchmarks, in 194.414 seconds wall
including the incremental build. Its source entries pass 48/48 in 183.13
seconds. All 50 source-execution TSVs exactly match the standalone report's
artifact identities, results and recorded counters. The source audit still
passes afterward, and `--release` still rejects missing full comparisons and
verified C2/C3 bootstrap evidence. The first workspace run's four stale
static-data fixture failures remain in `workspace.log`; the corrected full
rerun is `workspace-final2.log`, with execution TSVs in `workspace-final/`.

Logs are in `/tmp/grandiose-source-costs-ufMKJC/`, including
`compiler-check.log`, `physical-final.log` and `static-boundaries.log`.
The full semantic compiler, G1 emitter/service/bootstrap, structural/generic
destruction and remaining native ABI work are still open. No new Miri run or
self-hosting capability is claimed by this checkpoint.

## Concrete destruction and inferred constructor lifetimes

September 6, 2026. Source MIR retains destruction intent until concrete instance
discovery. A compiler-owned planner selects the actual source `Drop` method and
recursively discovers owned-field glue. These are ordinary demanded MIR instances
and calls, not a VM callback which discovers a source destructor at runtime.
Unelaborated cleanup intent is rejected by VM lowering. Low-level tests now check
that phase boundary and then independently decode/verify the fully compiled
program for their executable assertions.

The current implementation covers owned parameters (including generic erasure),
discarded owned call results, normal and label-exit scope cleanup, shadowed owners,
record/tuple/active-enum structural destruction, and source-hook-before-field
ordering. Local and field replacement destroy the previous resident before
installing the new one. Field moves leave typed uninitialized slots; cleanup
tests each remaining field and does not destroy a transferred resident. Direct
unique-reference moves retain a suspended restoration capability, so restoring
that referent does not destroy it again. Repeated reads/reborrows through a
reference-valued field observe the reference in place rather than taking it.

Destructor-observed reference leaves add implicit uses through the owner's
cleanup point, including under structural fields and shadowed bindings. Plain
references retain nonlexical loan ending in the frontend. Replacement releases the old resident's
loans; self-assignment snapshots the RHS provenance before replacing destination
facts. Transferred owners retain their backing loans without suspending their
now-vacant source slot. An older cancellation test incorrectly created two live
unique borrows of one counter; it now uses independent counters, and a negative
test explicitly rejects the overlapping-borrow source.

Omitted constructor lifetimes now use independent inference variables, constrained
by fields and expected result types, rather than rigid elided placeholders. Unsolved
holes cannot enter frozen type identity. In particular, this ordinary source works:

```glorious
fn wrap<'a>(value: Probe<'a>) -> Outer<'a> { Outer { nested: value } }
```

Frozen reference-return contracts may conservatively relate one result leaf to
several same-lifetime input leaves. PlaceFlow and escape analysis retain the union
through nested calls, aggregate moves and child reborrows. Distinct named lifetimes
remain distinct; forbidden mutations of every possible input remain checked.

Stage0 schema advances from 98 to 99, cache generation to 14, bytecode generation
to 54 and verifier generation to 13 (language/interface remain three). The new
owned-slot operations have explicit codecs and frozen-layout checks; initialization
probes cannot alias their destination with the storage they inspect. Cleanup CFG
splitting preserves handler-entry ordering and nonlocal-exit control metadata.
There is no independent G1 format change or new unsafe execution permission.

This is not complete U5: dynamic owned-Array destruction deliberately fails closed;
owned pattern extraction, partially moved enum payloads, callable environments,
and source Vec element destruction still need completion and dedicated evidence.
Moving a referent directly through a reference-valued field remains rejected by
the existing direct-local rule. Executable MIR also still lacks explicit loan
ending for some same-block storage replacements accepted by frontend NLL. For
example, after `let owner = Plain { target: &mut count };` with no destructor or
later use of `owner`, assigning `count = 42` passes `Check` but `Build` rejects
the MIR storage transition with G7004. The new frontend non-regression assertion
does not claim that this program executes; existing strict MIR live-loan storage
tests remain unchanged. General native homes/callable ABI, actual VM/native
roundtrips, source BLAKE3, and the Glorious semantic compiler/G1 emitter/service/
C2/C3 bootstrap are still open. No new Miri or self-hosting claim is made here.

Validation: the final workspace/all-targets run passed **2,569 tests, zero failures,
two existing ignored manual benchmarks**, in **146.157 seconds wall**. All **48
source entries** passed in **134.87 seconds**. Their 50 execution TSVs exactly
match the preceding run's artifacts, results and recorded counters. The focused
destruction target contains 22 executed tests; the lifetime target contains 12
tests, including the explicitly frontend-only plain-reference NLL check above.
All 154 Stage0 VM tests and the existing strict MIR/storage tests pass.

Every invocation retained the 590-second command guard, four-slot memory gate,
16 GiB cargo-test address-space limit, and unchanged VM execution budgets. Source
closure audit passes before/after; `--release` still rejects missing full contract
comparisons and verified C2/C3 bootstrap evidence. Logs are under
`/tmp/grandiose-source-destruction-eaucXA/`: `workspace-final.log` and
`workspace-final/` are the passing full run/evidence. Earlier failures are retained
in the numbered logs; `workspace-round4.log` includes the newly identified MIR
NLL gap and the two subsequently corrected low-level layout fixtures.

## Source-owned resident destruction and handler cleanup

September 6, 2026. `Vec<T>` now implements ordinary source `Drop`: its source
truncate/clear path withdraws the discarded initialized suffix, destroys every
resident in reverse order, and only then releases the raw allocation. Balanced
range traversal needs logarithmic ordinary call depth; bounded leaf chunks avoid
unnecessary recursive frames. No VM collection callback or type-erased native
element destructor implements this algorithm. Empty and zero-sized storage
still follow the source ownership protocol.

Executable probes cover nested Vec owners, append/pop ownership transfer,
whole-owner replacement, repeated truncation/clear, partially consumed iterators,
label exits, reverse hook order across uneven ranges, and zero-sized user hooks.
A 32-byte whole-run native budget proves buffers are released during execution,
not only by the runtime's final allocation-domain teardown. A zero-byte run
must execute a zero-sized resident's aborting hook rather than return normally.
These tests do not establish general native homes for frame-resident references.

Owning patterns take selected noncopy payloads from the original place, while
borrowed/refinement patterns retain their source owner. Residual tuple, record
and active-enum fields receive separate cleanup. Destructor-observed loans are
restricted to the selected variant where that variant is known; an unrelated
inactive error variant cannot prolong a successful borrowed result. Ordinary
owned unique-reference arguments move, so a caller that needs the handle again
must pass an explicit `&mut *handle`. The source registry and borrowed fixture
comparators now follow that contract; their expected outcomes are unchanged.

Terminal completion arms also clean enclosing lexical owners, including through
nested completion trees. Structural wrappers without root hooks inspect their
actual residual fields at the cleanup site. The opt-in authoring runner can
recycle a self-call only after a bounded, charged proof that the remaining CFG
forwards its unknown result and inspects vacant frame-local cleanup slots.
The proof rejects calls, loads, stores, traps and active destructors. It uses a
sparse scratch map and retains the separate surviving-caller/capture/brand scan.
Ordinary execution retains its existing call-depth behavior. A transferred
destructor-bearing enum payload runs 1,000 recycled steps and destroys its owner
exactly once; a live zero-sized hook prevents recycling. The compiler's
10,000-step owned-state test retains its 64-frame authoring limit.

Resumption completion now has an explicit delimiter: a resumed computation
returns to its clause before the enclosing expression suffix. Restored frames
synchronize surviving source storage by allocation identity, not only register
number, so intervening writes survive and newly shadowed allocations do not
overwrite earlier ones. These changes advance Stage0 schema to 100, cache to 15,
bytecode to 55 and verifier to 14; language/interface remain three. They do not
change independent G1's format or grant a new unsafe execution authority.

Real source destruction exposed allocation regressions. Source authority
comparisons now compare matching parameterized payloads directly; tag lookup
separates parameterized families from wide leaf dispatch. ASCII decoding avoids
the multibyte frame, and successful manifest/source-admission ticks avoid
constructing a temporary owning failure result. The checked eight-byte cursor
reader uses bounded self-recursion over byte residents, reducing its authoring
frame cost without unaligned word loads. The private BLAKE3 input bridge reads
each byte directly only after its extent check; the opaque hash itself remains
unchanged. Digest comparisons cover complete, empty and nonempty unaligned
literal/Vec-backed windows without hashing their surrounding sentinel bytes.
The source build-identity constructor matches the new native generations.
All existing authority tags, validation order, comparator batches and VM limits
remain unchanged. The physical push probe includes final
resident destruction and retains its less-than-100 charged-elements-per-resident
ceiling; exact rational slopes account for chunked cleanup without rounding.

Frozen validation passes **2,625 tests, zero failures, two existing ignored
manual benchmarks** across two guarded commands: `cargo test --workspace
--all-targets --no-fail-fast -- --skip gsc2_` passes 2,577 tests, and the separate
unfiltered `tooling/compiler-check.sh` passes all **48 source entries in 172.79
seconds**. Both use the optimized authoring test profile and eight workers.
The complete production closure and original batched assertions remain intact.
Every command retains the 590-second guard, four-slot memory gate and 16 GiB
cargo-test address-space limit. No VM execution limit is increased.

The formerly allocation-limited source batches now produce:

| Batch | Complete result | Work ticks | Charged allocation elements | Peak call depth |
| --- | --- | ---: | ---: | ---: |
| Bootstrap admission | `[145, 80, 13]` | 20,571,424 | 16,390,479 | 68 |
| Runtime-manifest comparator | `[69, 180, 648, 1, 20]` | 14,524,255 | 16,514,020 | 657 |
| Complete-world runtime input | `14` | 10,985,824 | 16,513,246 | 820 |

Each batch has one unchanged 16,777,216-element allocation budget. The original
owned-state-loop assertion still observes exactly 10,000 recycled calls; the
resident chunk stops after its final resident without an empty recursive call.
That run uses 830,453 work ticks, 520,458 charged elements and an 11-frame peak.
The separate physical meter and all 140 standard-library tests also pass; see
[current measured costs](runtime-costs.md#source-resident-destruction-checkpoint).

The final evidence is `target/compiler-check/run-4hvcrnb9/report.json`, with
50 execution records, successful complete-suite status and `release_ready:
false`. Its source-lock SHA-256 is
`a1dde5dbcda84be8160cc7e67bfb3191c26b1c2dae13f1d5f5b7c2d30dcbd9c9`.
The source audit passes before/after; all 11,455 public contracts remain open,
and `--release` still rejects missing full comparisons and C2/C3 evidence.
Logs: `workspace-substrate-final3.log`, `compiler-check-final2.log`,
`state-loop-final1.log`, and `std-physical-final3.log` in the directory below.
Earlier failed runs, including the initial hash-window fixture mistakes and
the subsequently removed empty cleanup call, are retained separately.

This remains prerequisite work. Dynamic owned Array/capture destruction, the
remaining handler/exit cases, general frame/native/callable ABI, actual native
roundtrips, source BLAKE3, the full semantic compiler, G1 emitter, service and
verified C2/C3 bootstrap are still open. No Miri, full language parity or
self-hosting certificate is claimed here. Validation logs for this checkpoint
are under `/tmp/grandiose-selfhost-next-k1aZEn/`; explicitly labelled diagnostic
runs with larger measurement budgets are not passing execution gates.

## Native calls and bytecode callback checkpoint

Historical schema-101 checkpoint; the source-home changes below supersede its
manual-home fixtures and ordinary-frame limitations.

Stage0 now has an explicitly unsafe, capability-bound native embedding path:
`VerifiedVmProgram::native_imports`, `VmNativeImports::insert` and
`run_i64_with_native`. All reachable bindings are linked before the first guest
instruction. Binding equality includes target/generation, capability, symbol,
concrete parameter/result types, and canonical reachable nominal descriptors.
Reachability includes transitive referents and callable signatures even when
no source register owns a value of the referent type; generic materialization
recomputes that closure. Repeated concrete pointer cycles terminate normally.
Expanding generic cycles are rejected by bounded declaration traversal (128
edges and 4,096 distinct type witnesses), not allowed to grow indefinitely.
Source callable contracts retain safety, generic kinds, lifetimes, effects,
invocation bounds and where-evidence; nominal declaration contracts retain
field lifetime relationships before instantiation/region erasure. Equal byte
sizes cannot authorize a stale contract. Stage0 schema/cache/bytecode/verifier
advance to **101/16/56/15**; language/interface remain three. Neither G1's format
nor the existing safe execution APIs gain native authority.

Scalar and pointer/reference slots use the host layout. A reference passes its
actual native-backed address, without serializing or rebuilding the referent.
The host can inspect field offsets and layouts before registering its unsafe
implementation. Host code remains responsible for matching the complete source
contract, including allocator identity, loans, ownership and callback uses.
Opaque contract digests are not authentication of untrusted artifacts.

The `repr(C)` callback token supplies a live context and synchronous trampoline
back into bytecode. Captured source environments remain VM-owned; the token
cannot be retained or used concurrently. Re-entry uses the same program,
capabilities, native allocation domain, work/allocation budget and VM depth
limit. A separate 32-level bound protects the real native callback stack.
Callback failures remain sticky even if a host ignores the failed status.
Rust panics are contained before returning through the callback entry; native
implementations must not unwind through C. Outward callback effects, labels
and resumption tokens are explicitly unsupported at this boundary.

The executed fixtures compile fresh source, encode, independently decode and
verify it, and then cross the actual VM/native boundary. They cover:

- A native function mutates and returns the same source-owned Pair address.
- Native-owned immutable static residents return to source through nested
  reference-only layouts, including generic specialization, with a zero-byte
  source native-allocation budget.
- A captured bytecode callback re-enters another authorized native import.
- Native code borrows `Vec<ApplicationWidget>` metadata in a real native home,
  calls source bytecode to mutate/push, and observes the same metadata address.
  The no-growth case preserves the backing address; growth reloads the updated
  header and checks the increased capacity. Source owns all element algorithms,
  generic specialization, noncopy resident Drop calls and buffer release.
- Native re-entry calls source `Vec::clear` for zero-sized Drop residents.
  All three hooks re-enter the native observer before the outer native call
  returns. The 24-byte native budget permits only the vector header.
- Target, duplicate, missing/stale binding, callable/field lifetime, result-slot
  and malformed callback-slot rejection; shared instruction/depth/native-memory
  limits; and recursive VM/native callback stack exhaustion.

Source fixtures explicitly allocate their metadata homes using the existing
raw-memory leaves; no extra primitive or native collection authority is added.
Unsafe/external reference-result provenance now survives ordinary forwarding,
lexical blocks and reborrowing. It does not derive authority from arbitrary raw
bits: only frozen unsafe/external call origins introduce these loans. Shared
references still cannot be upgraded, and live overlapping unique reborrows or
parent writes remain rejected even inside unsafe scopes.

This is **partial U4**, not its completion. Ordinary frame residents still lack
native homes. By-value aggregates/callables and references without existing
native homes are rejected rather than adapted by payload copying. General
owned/callable ABI, all cleanup/control-flow cases, and physical boundary-cost
certification remain open. ABI slots carry scalar bits and genuine pointers;
VM call-frame, callback-vector and layout metadata allocations still exist.
No allocation-free boundary, general zero-copy ABI, Miri result, LLVM output,
G1 extension or self-host/C2/C3 certificate is claimed by these fixtures.

Frozen validation passes **2,640 tests, zero failures, two existing ignored
manual benchmarks**: the guarded workspace/all-targets run with `gsc2_` entries
excluded passes 2,592 tests, including all **15 native-bridge regressions**;
the separately audited, unfiltered `tooling/compiler-check.sh` passes all
**48 source entries in 171.55 seconds**. Both use native test optimization level
one and eight workers with unchanged 590-second command, four-slot, 16 GiB
cargo-test and VM execution bounds. Every original source batch and assertion
remains intact; no diagnostic budget increase is counted as a pass.

`target/compiler-check/run-9dlur2gc/report.json` contains 50 execution records,
`complete_current_suite_passed: true` and `release_ready: false`, bound to source
lock SHA-256 `b9e7b8a230932fb1d583f1eb8df9405c1e7026a35661924396c31ab460aed0a3`.
Source audits pass before and after execution. The release audit still rejects
the missing full contract comparisons and verified C2/C3 bootstrap evidence;
all 11,455 public contracts remain open. Final logs are
`workspace-final2.log`, `compiler-check-final2.log` and `release-audit.log` under
`/tmp/grandiose-native-bridge-M4inGl/`. Earlier logs, including the reproduced
missing-referent failure before its fix, are historical diagnostic evidence.

## Native source-storage checkpoint

Schema/cache/bytecode/verifier **102/17/57/16** establishes a native home when an
addressable source local with a supported concrete layout is initialized. The
same rule applies with or without native imports. Borrowing or passing that
local to native code does not allocate or reconstruct its resident. Private
SSA values still represent by-value computation; calls, captures, returns and
control transfers read values without aliasing separate source owners' slots.

Native bytes are authoritative. Separate metadata records initialized fields,
active enum variants and checked reference origins, not a second aggregate
payload. Partial moves leave holes; unique restoration can refill a hole without
destroying the previous owner. Exporting a complete native value/reference
requires complete initialization. Stored references contain actual pointers;
weak origin metadata avoids retaining cycles of source homes. Native returns
to known live homes recover their checked source-storage identity.

Native-home bytes share the existing per-run/per-block raw-memory limits.
Lexical storage death releases bytes even if dead SSA reference carriers still
retain validation metadata; retired homes cannot be revived. A checked whole
owner move can reclaim an unexposed vacant home. Raw/native-exposed addresses
retain their storage lifetime, including across replacement. Frame recycling
rejects escaped local addresses and only preserves eligible surviving caller
homes. Source Drop remains ordinary specialized bytecode, never a Rust home
destructor.

The native fixtures now include an ordinary Pair local under a one-Pair byte
budget, an addressable reference local with two real pointer layers, and an
effect payload passed through a delimited resumption after native mutation.
Source `Vec<ApplicationWidget>` and `Vec<ZeroSizedMarker>` use ordinary locals
for mutation, growth and source Drop during native callbacks. Their limits
explicitly include source-generated cleanup parameter homes; zero-size element
payloads still occupy no bytes. A unique capture over a surviving native home
now works across the existing dynamic-label/handler rejoin fixture.

The first full run exposed four source batches exceeding the unchanged
16,777,216-element allocation limit. A cached instruction plan now recognizes
an adjacent dereference/projection whose intermediate has exactly one consumer
and no addressable home. Native execution reads only the selected field, retaining
both instruction charges and avoiding an unused aggregate allocation. A complete
operand/result visitor prevents this optimization when another consumer exists,
including handler completion. The bootstrap, registry, manifest and world-input
batches subsequently pass without changing source assertions or execution
limits. The exploratory 48-entry source run passes in 178.60 seconds; final
frozen evidence is recorded separately below.

This remains **partial U4**. Private Array/callable resident layouts, general
owned aggregate/callable native ABI, complete capture/exit cleanup, physical
allocation-free boundary certification, G1 extension, full source compiler
semantics/service and verified C2/C3 remain open. No new Miri or LLVM result is
claimed. Descriptor/path/callback metadata and semantic by-value loads still
have runtime costs; genuine borrowed resident identity is not a claim that
every boundary operation performs zero allocations.

Final frozen validation passes **2,646 tests, zero failures, two existing ignored
manual benchmarks**: 2,598 workspace/all-targets tests, including **18 native
bridge regressions** and three native-home unit tests, plus all **48 separately
audited source entries in 176.98 seconds**. The full source batches, assertions,
16,777,216-element default allocation limit and other execution bounds remain
unchanged. The Rust and source build-identity constructors both use 17/57/16;
the original seven-field bootstrap comparison remains intact.

Selected final source profiles (logical charges, not physical allocation counts):

| Source batch | Work ticks | Charged allocation elements | Peak call depth |
|---|---:|---:|---:|
| Bootstrap admission, `[145, 80, 13]` | 20,663,952 | 16,266,822 | 68 |
| Eight registry histories | 12,222,410 | 12,630,007 | 183 |
| Runtime manifest, `[69, 180, 648, 1, 20]` | 14,730,665 | 15,732,835 | 657 |
| Complete world input, `14` | 15,863,987 | 16,341,923 | 820 |

The 10,000-step state loop returns 10,000 with 10,000 recycled tail calls,
830,453 work ticks, 520,445 charged elements and depth 11. Allocation reductions
do not imply uniformly reduced work: native-home validation and conservative
tail checks also consume execution work.

`target/compiler-check/run-9d708b6q/report.json` contains 50 execution records,
no filters, `complete_current_suite_passed: true` and `release_ready: false`,
bound to source lock SHA-256
`55825cc00ee932738eb43d441e736c60bf5fba3fc674b7b57e09d3231779f466`.
Source audits pass before and after that execution. The release audit rejects
the missing full contract comparisons and verified C2/C3 bootstrap evidence;
all 11,455 public contracts remain open. Historical logs are `workspace-final3.log`,
`compiler-check-final2.log` and `release-audit.log` under
`/tmp/grandiose-native-homes-kz0iPv/`. Earlier failing logs record the reproduced
allocation, storage-retention, fixture and generation regressions, not passes.

## Synchronous owned native ABI checkpoint

Schema/cache/bytecode/verifier **103/18/58/17**, with native ABI generation **2**,
adds owned tuples and nominal values in both directions. The Rust and source
build-identity constructors advance together. Scalar/reference ABI slots and
the original seven-field source bootstrap comparator remain unchanged.

An owned VM argument already occupies native storage at its ordinary producer.
The native callee takes that resident once through `take_argument`; no aggregate
is rebuilt at dispatch. Owned native results are initialized directly in a
preallocated caller result slot, then committed with `finish_result`. In-place
validation records active variants, initialization and reference origins without
materializing aggregate fields as VM values. Missing/duplicate transfers,
missing/duplicate result initialization and invalid scalar bits are checked.

For callbacks, the native caller supplies the actual writable owned argument
storage. The bytecode frame binds that slot without a payload allocation; an
ordinary source borrow sees its original address. Callback return producers,
including results forwarded through direct/indirect calls and specialization,
retain native layout until the result is moved into the native caller's output
slot. Ordinary language-level moves may copy bytes and allocate source frame
homes; the boundary does not perform per-field boxing or collection conversion.
All callback slot placements are checked before accepting owned arguments.
Linking and storage planning share recursive resident-layout eligibility.

Executed fixtures cover a Pair argument/result within exactly two Pair-sized
homes, native-owned callback parameters observed at their original address, a
generic helper return, and an owned `Vec<ApplicationWidget>` round trip. That
vector crosses into native code and back into bytecode with its original header
and backing; source growth increases its capacity, then ordinary source cleanup
runs all five element destructors exactly once. Native code supplies no vector
algorithm, element conversion or destructor. A noncopy zero-size owner also
passes through both native dispatch and a bytecode callback with a zero-byte
native-storage budget and one final source destructor.

This remains **partial U4**, not the complete ownership/runtime ABI. Argument
slots and callback tokens last only through their synchronous invocation. An
unsafe native implementation must discharge or transfer the resident obligation
before returning and must preserve the allocator domain. VM raw allocations
remain execution-scoped; durable external owners and a general exported callable
ABI are not yet provided. Concrete selected drop-code/release identity, complete
capture and exceptional-exit cleanup, private Array/callable layouts, and physical
allocation-free boundary certification remain open. Metadata still allocates;
errors abort the run under the existing execution contract, not a new guarantee
of source cleanup on every failure. Full source compiler semantics/service,
independent G1 extension and verified C2/C3 are still required. LLVM remains
deferred; no new Miri result is claimed.

Final frozen validation passes **2,651 tests, zero failures, two existing ignored
manual benchmarks**: 2,603 workspace/all-targets tests, including **23 native
bridge regressions**, plus all **48 separately audited source entries in 168.02
seconds**. Every original source batch, comparator and execution limit remains.
The source profiles for bootstrap admission, eight registry histories, runtime
manifest, complete world input and the 10,000-step owned-state loop are unchanged
from the native source-storage checkpoint above. These are logical VM charges,
not a census of physical allocations.

`target/compiler-check/run-xyt6cbon/report.json` has 50 execution records, no
filters, `complete_current_suite_passed: true` and `release_ready: false`, bound
to source lock SHA-256
`6811bd9278b2ee73c90bb50d336ec47e0639c5f3960035bdaf7404615cdcd7fb`.
All 50 execution records match the earlier schema-103 source pass exactly.
Source audit and `git diff --check` pass. Release audit still rejects missing
full contract comparisons and verified C2/C3; all 11,455 contracts remain open.
Final logs are `workspace-final3.log`, `compiler-check-final3.log` and
`release-audit.log` under `/tmp/grandiose-owned-abi-5s5qH3/`. Earlier fixture and
stale-generation failures are retained as failures, not counted as evidence of
a complete passing run.

## Native destructor contract checkpoint

Schema/cache/bytecode/verifier **104/19/59/18**, with native ABI generation **3**,
retains concrete source-selected resident destruction operations in native import
metadata. Discovery follows the complete bounded native type closure, including
tuples, generic fields, raw-pointer/reference referents and callable signatures.
A type appearing only behind a returned reference still retains its selected
destructor and transitive dependencies. This is operation discovery, not a claim
that borrowing a resident gives the borrower ownership of it.

Each resident records its pre-erasure source-type identity, optional specialized
destruction entry and a digest of that entry's actual emitted reachable code.
The digest includes selected source hooks and ordinary helper bodies, including
their native dependencies; changing a helper body invalidates a binding even
when layouts, source headers and the selected entry key are unchanged. An
unrelated body does not invalidate it. Decoding/verifying checks complete
resident-layout coverage, canonical operation ordering and the selected entry's
call shape. It does not independently authenticate source trait selection from
untrusted bytecode; current distribution remains locally compiled source.

`VmNativeCall::with_destructor` lends the selected bytecode operation through
the same synchronous callback mechanism, with the native caller supplying the
actual writable owned resident. No source callback argument is required in the
host declaration. The existing callback depth, authority, sticky error and
execution-budget rules apply. Fixtures destroy an owned `Vec<ApplicationWidget>`,
a zero-sized owner and a zero-sized tuple through the exported bytecode entry.
Source code performs every element hook and buffer release; native code supplies
neither a collection algorithm nor element conversion. A resident without a
selected operation does not receive an invented no-op destructor.

ABI matching also checks the allocation-domain identifier
`grandiose-vm:execution-native-heap:v1`. This names the execution-scoped release
protocol; it does not authenticate an unsafe host implementation or turn a
borrowed foreign address into VM-owned storage. All owned exports remain
synchronous, and source obligations must be discharged or transferred before
returning. Durable external allocations, complete copy/use/quantity-operation
identity, general callable/capture ABI, full exceptional cleanup, private
Array/callable layouts and allocation-free boundary certification remain open.
This is partial U4, not U4 completion or a self-hosting certificate.

The new execution fixture also exposed a root-lowering defect: the speculative
short-circuit path emitted block-prefix bindings before deciding whether it
applied. Its fallback then treated those owners as outer-scope bindings and
omitted their normal exit cleanup. Applicability is now checked before any
binding mutation, and successful short-circuit paths clean up prefix owners on
their normal exits. Regression cases cover ordinary scalar/call roots and
constant/dynamic Boolean short circuits with an observable source Drop hook.

The restored cleanup exceeded the original bootstrap allocation limit. A
temporary diagnostic measured **17,557,304** charged elements; its larger limit
was restored immediately and is not validation evidence. Ordinary resident
arguments now copy native bytes into distinct callee homes without reconstructing
unused VM aggregate fields. The opt-in authoring runtime additionally retains
one cleared register buffer per function after normal return. Only the empty
Vec backing is reused: homes, source brands, references and continuation state
are released, call depth and source cleanup are unchanged, and every newly
allocated buffer is still charged. Reuse does not cross executions and is
reported separately as `reused_call_register_buffers`. All original compiler
batches, assertions and VM limits remain in place.

Final frozen validation passes **2,658 tests, zero failures, two existing ignored
manual benchmarks**: 2,610 workspace/all-targets tests, including **28 native
bridge regressions**, plus all **48 separately audited source entries in 174.90
seconds**. Bootstrap preserves `[145, 80, 13]` with **7,699,624** charged elements
under its original 16,777,216-element limit, with 495,108 reused call-register
buffers. Its 23,746,652 work ticks match the diagnostic run; the avoided cost is
actual register allocation, not omitted instructions or source cleanup. The
eight-history registry result remains `[1, 1, 1, 1, 1, 1, 24]`, with 1,740,901
charged elements. Runtime-manifest admission preserves `[69, 180, 648, 1, 20]`
with 3,251,777 charged elements. The physical allocation regressions also pass
their unchanged exact slope and size-independence assertions; see
[runtime costs](runtime-costs.md#september-6-native-destructor-and-register-buffer-checkpoint).

`target/compiler-check/run-47qvcf5a/report.json` contains 50 execution records,
no filters, `complete_current_suite_passed: true` and `release_ready: false`,
bound to source lock SHA-256
`4da7e82758161ab0586d5c3a7098c6acf7c746a235d48f082567e359bd620575`.
Source audits pass before and after, and `git diff --check` passes. Release
audit still rejects missing full contract comparisons and verified C2/C3;
all 11,455 public contracts remain open. Final logs are `workspace2.log`,
`compiler-check2.log`, `physical2.log` and `release-audit.log` under
`/tmp/grandiose-native-drop-contract-PpjOy8/`. The earlier allocation-limit and
initial buffer-cache failures remain recorded as failures, not complete-suite
passes. No new Miri run, independent G1 extension or LLVM implementation is
claimed.

## Source BLAKE3 checkpoint

The public `blake3(Slice<u8>) -> Vec<u8>` implementation now performs unkeyed
BLAKE3-256 entirely in source: little-endian block loading, seven-round scalar
compression, message permutation, chunk counters and flags, left-complete tree
reduction and root-output encoding. The algorithm follows the
[BLAKE3 reference](https://github.com/BLAKE3-team/BLAKE3/tree/master/reference_impl).
It reads the exact borrowed input window, never constructs an input collection,
and initializes the 32-byte result before publishing its Vec length. Private
fixed-size records hold chaining values and compression words. Tree recursion
is logarithmic and each chunk processes at most sixteen blocks.

Only existing scalar and raw-memory leaves are used. The six legacy private
Array/Bytes/hash declarations and their artifact meanings remain for explicit
compatibility; no current source function calls them. No compression primitive,
new opcode, source-name privilege, native generic specialization or host
semantic callback was introduced. Stage0 schema 104 and its existing generations
are unchanged. This replaces the existing unkeyed, fixed-output API; it does
not add streaming, keyed-hash or extendable-output APIs.

The original empty/text/binary digest fixture still compares all 32 bytes for
static input and static/owned borrowed subwindows. A new single-execution batch
checks 35 lengths from zero through 65,537 bytes, covering partial/full blocks,
partial/full chunks, non-power-of-two trees and unaligned windows. Every digest
is compared with the Rust BLAKE3 oracle. Decoded emitted code is checked to
contain raw-memory instructions and no whole-hash or legacy array-conversion
instructions. The whole batch uses 33,405,614 work ticks, 4,902,644 charged value
elements and a peak call depth of 36 under its 64-frame limit. Its native-storage
budget is 4,096 bytes with a 64-byte per-allocation ceiling; register and VM
metadata allocations remain separately subject to their original limits.

Additional executed source fixtures compare all chaining-value words at six
chunk offsets, including counters above 32 bits, using the reference's non-root
hash API without allocating fictional huge inputs. Another fixture hashes an
owned 2,049-byte window, mutates its owner after the first hash, and compares the
second digest independently. This checks that hashing does not retain the input
loan or use a stale input snapshot. The initial high-counter comparator used a
nested Boolean-handler form outside C0's supported lowering; at this checkpoint
its exact comparison used the same word-XOR reduction as source compiler
identities. [A32](authoring.md#a32-nested-lazy-boolean-values) subsequently fixes
nested Boolean value lowering and restores the chained comparison. The hash
checkpoint did not itself fix that lowering limitation.

The compiler's existing `identity::hash` automatically uses this source
implementation. No compiler fixture, request batch, expected result or execution
ceiling is reduced. Source BLAKE3 closes the opaque-hash library gap, not all of
U4–U6, the source semantic compiler, independent G1 support or C2/C3. Legacy
artifact retirement and the other recorded ABI/cleanup gaps remain open.

Final frozen validation passes **2,661 tests, zero failures, two existing ignored
manual benchmarks**: 2,613 workspace/all-targets tests, including 143 standard
library regressions, plus all **48 separately audited source entries in 178.29
seconds**. All 50 recorded scalar/tuple results match the preceding
native-destructor checkpoint exactly. Bootstrap still returns `[145, 80, 13]`
with 38,550,344 work ticks and 5,880,146 charged allocation elements. The
eight-history registry still returns `[1, 1, 1, 1, 1, 1, 24]` with 4,551,979 ticks
and 1,626,889 charged elements. Limits and assertions are unchanged. More VM
instructions now account for hashing formerly hidden inside a native leaf;
these logical counts are not a direct physical-performance comparison.

`target/compiler-check/run-m8odofrz/report.json` contains 50 execution records,
no filters, `complete_current_suite_passed: true` and `release_ready: false`,
bound to source lock SHA-256
`6457eac1483c3f5375c702239e64d1ec9421f0be7468b97283324dafb22d1d6d`.
Source audits pass before and after, and `git diff --check` passes. Release
audit still rejects missing full contract comparisons and verified C2/C3;
all 11,455 public contracts remain open. Logs are `workspace1.log`,
`compiler-check2.log`, `source-tests3.log` and `release-audit.log` under
`/tmp/grandiose-source-blake3-zW8SA4/`. No Miri, independent G1 or LLVM result
is claimed.

## Owned callable environment checkpoint

[A33](authoring.md#a33-owned-callable-environment-destruction) adds authenticated
capture cleanup for concrete lifted environments. Owned captures are destroyed
in reverse layout order; normal invocation publishes moved-out and retained
slots back to the callable. Independent source copies own independent captures,
while borrowed native-representable captures retain their original source homes.
This covers uninvoked/nested/returned closures and source Vec residents, but not
complete exceptional frame cleanup or the general exported callable ABI.

The full workspace passes **2,622 tests**, and all **48 source entries** pass in
177.89 seconds: **2,670 total**, zero failures and two existing ignored manual
benchmarks. The unfiltered report is
`target/compiler-check/run-3j7b80x3/report.json`, with 50 results identical to
A32 and `release_ready: false`. Source-lock SHA-256 is
`e25c2fa291f791530cc75a3274201e90cab49082f0ddf4fa4ce7f91a2d8e25ca`.
Original batches and execution limits are unchanged. The source loop again
recycles 10,000 calls under its original 64-frame cap, at peak depth 11; the
tail proof refuses any callable with registered source destruction. Logs are
`workspace3.log` and `source2.log` under
`/tmp/grandiose-capture-cleanup-lK8J5W/`. Earlier failed runs there are diagnostic
evidence, not passing checkpoints. U4–U6, G1, the source semantic pipeline and
verified C2/C3 remain open.

## Shared frame ownership checkpoint

[A34](authoring.md#a34-shared-frame-ownership-and-cancellation-cleanup) derives
normal returns and cancelled-frame destruction from a shared source-owner
inventory. Suspended ordinary frames execute their frozen destruction plans
deepest first, preserving checked loans into surviving callers. Capture loans
move slots into the invocation and release only residual values on return or
abandonment. Regressions cover consumed/retained/partial captures, new invocation
locals, deeper parameters, reverse cleanup order and the unchanged depth budget.

Frozen validation passes **2,685 tests**, zero failures and two existing ignored
benchmarks: 2,637 workspace/all-targets tests and all 48 source entries in 175.59
seconds. `target/compiler-check/run-m17oe7s1/report.json` contains 50 unfiltered
results identical to A33 and `release_ready: false`, bound to source lock SHA-256
`b067ba5298964824b1f3da79870353e871f46f67affbd3d23bda8baabf27cc9f`.
Logs are `workspace4.log` and `source2.log` under
`/tmp/grandiose-frame-ownership-kFF0ZV/`. Earlier failed runs are diagnostic
evidence, not passing checkpoints. Other nonlocal/replay paths, complete
temporary ownership, U4–U6, independent G1, the source semantic compiler and
verified C2/C3 remain open.

## Nonlocal label ownership checkpoint

[A35](authoring.md#a35-nonlocal-label-frame-cleanup) extends the shared frame
destruction plan to nonlocal dynamic label calls. Outgoing payloads survive
cleanup, embedded checked references are rebased, and residual captures return
before their callable owner is destroyed. The runtime destination uses the
executing specialization rather than its source brand. Seven new tests cover
owned locals/parameters/payloads, capture states, partial moves, ordering and
the ordinary call-depth budget.

Frozen validation passes **2,692 tests**, zero failures and two existing ignored
benchmarks: 2,644 workspace/all-targets tests and all 48 source entries in 185.92
seconds. `target/compiler-check/run-0mn6_v5w/report.json` contains 50 unfiltered
results identical to A34, with `release_ready: false`,
bound to source lock SHA-256
`72e2add96b6dbf23daa4377698b9ed08d52d86ea82f1f2d6078114cae206ac36`.
Logs are `label-workspace.log` and `label-source2.log` under
`/tmp/grandiose-frame-ownership-kFF0ZV/`. The first source attempt stopped at its
stale-lock audit before tests; it is not passing replay evidence. Retained
replay cleanup, temporary ownership, the documented initializer/terminal-suffix
lowering gaps, U4–U6, independent G1, the source semantic compiler and verified
C2/C3 remain open.

## Terminal strict-value checkpoint

[A36](authoring.md#a36-terminal-strict-value-control-flow) makes the absence of a
normal value-CFG continuation explicit. Terminal calls and operations no longer
manufacture strict suffixes or join arguments; returning alternatives survive
bottom-first type inference. Computed callees run before arguments, and
first-class tail-label helpers may return normally as well as invoke the label.
Eight new tests cover inference, strict ordering, branches and ownership.

Frozen validation passes **2,700 tests**, zero failures and two existing ignored
benchmarks: 2,652 workspace/all-targets tests plus 48 source entries in 188.40
seconds. `target/compiler-check/run-bvgwj_9n/report.json` contains 50 unfiltered
results identical to A35 and `release_ready: false`, bound to source lock SHA-256
`7c9ebca1d7d74e48526c7b73fe3ca6aa00e48899405c7081019f57b699fbc2ba`.
Logs are `terminal-workspace2.log` and `terminal-source2.log` under
`/tmp/grandiose-frame-ownership-kFF0ZV/`. A 15-second CPU sample was collected
during the passing replay; this is not an uninstrumented timing comparison.
The first replay was interrupted to correct a stale generation assertion and
is not passing evidence. Label-initializer lowering, retained replay ownership,
general temporaries, U4–U6, independent G1, the source semantic compiler and
verified C2/C3 remain open.
