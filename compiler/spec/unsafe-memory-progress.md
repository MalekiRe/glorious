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
| U3 | Versioned raw-memory bytecode and safety metadata; trusted execution of locally compiled source, preserving existing consistency checks | Stage0 schema 99 executes raw memory and guarded owned-slot operations; independent G1 extension remains; untrusted-bytecode admission deferred |
| U4 | Host-layout addressable storage, allocator/drop/borrow/call ABI, actual VM/native roundtrips and callbacks using host fixtures without marshalling | Missing |
| U5 | Source `Vec`/slices specialized to bytecode over U1–U4 for application-defined types; ownership, failure, cleanup, and measured performance without native specialization | Pointer-backed Vec/slices and initial concrete structural/generic destruction implemented; collection/capture cleanup and full resident ABI remain incomplete |
| U6 | Execute strings/UTF-8/hashing and remaining collection algorithms as source bytecode, replacing specialized VM algorithms | Source UTF-8 and collection consumers migrated; legacy opcode removal, opaque BLAKE3 bridge and remaining work open |

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
