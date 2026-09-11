# Stage-zero generated LLVM and native handlers

`StageZeroCompiler::compile_llvm(request, LlvmTarget::host())` compiles Glorious
source through the ordinary checked compiler and lowers its verified concrete
VM-LIR into LLVM IR. `LlvmIrProgram::compile` invokes an explicitly selected
trusted LLVM compiler and loads the generated object. This is actual generated
CPU code, not the Rust compiler's backend selection, a host arithmetic fixture,
or a call to the VM interpreter from each emitted operation.

The native-handler execution milestone uses one shared resumable-frame convention
for generated and bytecode computation. This is **not complete language-spec §17**
or full compiler/library conformance. Existing native-import/callback tests
remain distinct from the generated-code tests in `tests/llvm_native.rs`.

## Admitted execution

The initial selected profile is little-endian, 64-bit x86-64 GNU/Linux. Its explicit
LLVM data layout is checked against the shared native storage layouts. Other
profiles fail closed. Scalar integer widths include i128/u128; records, tuples,
fixed arrays, enums, references, raw pointers, sealed static byte views, and zero-sized
residents use the same concrete offsets, alignment, stride, and enum tag rules
as shared VM storage. Initialization metadata is separate from resident bytes.

The emitter supports checked/wrapping integer arithmetic and conversions,
comparisons and shifts, basic f32/f64 operations with canonical NaNs, and
integer/float and float-width conversions,
constructors/projections, basic ownership/storage instructions, real reference
loads and stores, direct calls, branches, final lexical transfers, source
destructor glue expressed by admitted operations, and direct mandatory tails.
Fixed-array patterns include nested elements and sparse remainders; native array
cleanup loops track dynamically indexed move holes, including zero-sized elements.
Typed enum projections select the active discriminant's exact payload layout;
wrong active types or field counts fail before a field is read. Different
variant offsets are not silently treated as one common struct layout.
The exact admissible boundary is whole-graph instruction/layout admission, not
a promise that every operation on the listed type families is supported.

Integer-to-float and narrowing conversions round directly to the destination
precision using nearest-even; wide integers do not pass through an intermediate
f64 when the destination is f32. Checked float-to-integer leaves validate ordered,
half-open power-of-two bounds before truncation, rejecting NaN, infinities, and
out-of-range inputs with the VM's checked-leaf error. Public `as<T>` saturation,
NaN-to-zero, and other conversion policy remain ordinary standard-library source.
Generated entries, the mixed worker, standalone bytecode entries, and native
callback re-entry share one floating-point environment guard, with gradual
underflow and masked exceptions. It restores the caller's control/status state
on success, failure, and unwinding. Host/native calls and generated allocator/VM
callbacks have their own guard, so a foreign callback that changes the thread's
floating-point modes cannot affect subsequent source instructions. Embedding
rounding modes and flush-to-zero/denormals-are-zero settings do not change source
results on the executed x86-64 profile.

The small C machine helper uses the target's own `fenv_t`, `FE_DFL_ENV`, and
nearest-rounding definitions. Rust holds only bounded aligned opaque storage;
C compile-time assertions check its capacity/alignment against the actual host
headers. It neither hard-codes a libc layout nor implements source arithmetic
or conversion policy. WebAssembly needs no mutable-environment guard because its
scalar operations have fixed nearest-even/non-stop semantics, as specified by
the [WebAssembly numeric execution rules](https://webassembly.github.io/spec/core/exec/numerics.html#floating-point-operations).
Other native hosts compile this helper against their own C environment rather
than inheriting the GNU struct layout; the executed hostile-mode matrix currently
covers x86-64 GNU/Linux, not a claim of cross-host runtime validation.

Generated segments execute local computation against the runtime's existing
resident homes. They return at verified frame transitions: ordinary calls,
mandatory tails, handler dispatch/resumption, labels and source-storage lifecycle
events. The common runtime implements these transitions for both engines; it
does not replace a selected native body with bytecode. No native C stack frame
has to remain suspended around a source continuation.

Mandatory tails replace the current source activation after checked argument and
cleanup transfer. Surviving ordinary callers retain their result destinations.
This does not depend on LLVM tail-call optimization or recursive cross-engine
callbacks. Tests execute 10,000 alternating VM/native tails at O0/O2, and a
1,000-iteration handler/tail cycle under eight-call/eight-handler/eight-retained-
continuation and 128-KiB native-storage limits. An active unfused delimiter or
unresolved owner obligation at a source `tail` remains a rejection.

Every execution shares instruction, activation-depth, handler-depth, retained-
continuation and logical native-byte budgets. Retained control includes both
pending performances and returning-resumption edges throughout saved branches;
aliases do not count as independent authority, while replayed branches do.
Native admission limits an individual planned body to 64 KiB and its
initialization tree to 16,384 paths. Native storage and segment scratch are
charged to the execution budget; machine helper paths retain their explicit
stack limit. These are logical limits, not exact Rust metadata, allocator/RSS or
LLVM spill accounting, and not a native process-memory sandbox.

## Deep handlers and clause ownership

The checked pipeline carries effect identity, ordered payload ownership,
resumption quantity and result/completion contracts through Runtime MIR, VM LIR
and executable verification. Direct, indirect and captured ordinary helpers may
perform or invoke resumptions across either engine. Helper-local delimiters,
first-match forwarding and transformed completion results use the same control
graph. Clauses run outside their serviced delimiter; resumption reinstalls it.

Optional cancellation destroys only legally abandoned owners. Exact finite
replay duplicates admitted initialized residents and internal control authority;
the final use consumes the original. Checked aliases share one invocation budget.
Unique loans, linear residents and captured labels do not become replayable by
crossing engines. Borrowed observation of a resumption supplies no owned or
shared invocation permission that its checked callable contract lacks.

Protected storage and clause-owned storage are distinct parts of Cleanup's
published ownership product. Every dynamic clause entry starts fresh local
allocations, while older returning clauses retain their original homes. Local
label exits preserve dynamically interposed handlers when no delimiter is
crossed, and abandon only crossed return paths otherwise. Clause cleanup uses
the same ownership frontier as suspension/replay, with no register-content
heuristic for deciding who owns an allocation.

The cache-172 handler integration gate passes 86 tests, including fresh/decoded
VM, all-native and both mixed directions at O0/O2. Backing-address/mutation and
bounded handler/tail checks also pass. Three additional admission checks cover
an ordinary mandatory-tail helper under its caller's delimiter, exact suspension
of a linear owner versus forbidden optional cancellation, and rejection of
borrowed resumption invocation without receiver permission. The foreign callback
and active-frame tail rejection gates pass as well.

These gates close the native-handler execution milestone for the checked Stage0
VM/LLVM profile. They do not waive source ownership, fusion or foreign-boundary
requirements, or claim complete language/library conformance.
Profiled execution observes zero generated
resident-entry allocations and copied bytes: creating a source clause local or
an explicitly admitted replay snapshot is distinct from an engine-entry adapter.

## Identity and trust boundary

The immutable IR plan and emitted ABI witness bind the native format generation,
target triple/data layout, concrete nominal source/layout identities, original
normalized source-request identity, full verified code identity, runtime
manifest, exact VM/native body partition, control convention, and allocation-domain convention. Independent
descriptor mutations are rejected before an entry can execute. No pointer is
serialized as authority. The loaded library owns all resolved entries and is
closed before its exclusively owned temporary outputs are removed.

Compiling/loading native code is an unsafe embedding action: the selected LLVM
compiler, linker, and native runtime libraries must be trusted. Merely naming an
arbitrary executable `clang` does not authenticate it. Source unsafe contracts
still require the unsafe runner; native execution does not sandbox unsafe code.

### Raw callable residents

Shared native storage represents a source callable with a 32-byte verified
callee digest followed by one aligned 64-bit execution-domain environment token
(40 bytes, alignment 8). The payload contains neither Rust object bytes nor a
naked function pointer. An address-specific resident lease retains the original
capture environment. Raw moves, byte relocation, and allocation growth preserve
that identity; source Copy instead duplicates owned captures. Overwrite, typed
move-out, storage retirement, and allocation release remove the corresponding
leases without inventing source Drop policy. Weak identity entries do not retain
popped environments, and the registry/home graph has no retention cycle.

Reads reject unknown, cross-execution, unleased, retired, wrong-target, and
wrong-signature tokens. Copying arbitrary token bytes without a supported raw
move/copy does not create a resident lease. Source-level tests run shared and
mutable captured callables through Vec storage, reserve, move, pop, and invocation
at O0/O2, both fresh and decoded. Generated captured and indirect callable
execution uses the same authenticated storage and checked receiver contract.
Labels and resumptions are execution-domain control residents, not C function
pointers; decoding never accepts serialized native addresses as authority.
The current native ABI is generation 22, shared-resumable-frames v4.

## Generated LLVM and bytecode sharing

`compile_llvm_partitioned(request, target, use_vm)` selects the bytecode bodies
before native admission. `LlvmIrProgram::with_vm_functions` changes the partition
of an already admitted plan. Unselected functions execute generated LLVM; this
is an explicit whole-function selection, never an instruction fallback. Local
VM-only operations are allowed in selected bodies, but unsupported control is
rejected even when placed entirely in the VM partition.

Ordinary crossings use the existing runtime activations in one allocation domain.
Owned aggregate parameters retain their resident homes, without an argument-byte
copy. Owned returns initialize the caller's destination. Scalar/reference values
are transported as ABI values while the actual referent backing address is
preserved. Source Drop glue remains the exact checked
source implementation bound by the full code identity; no same-shaped foreign
destructor is selected by a symbol name.

Sealed UTF-8 and raw-u8 static data uses two native words: an immutable byte
pointer followed by its `usize` extent. The checked type identity carries its
tag and alignment; no Rust/VM handle is stored in those words. LLVM emits an
immutable allocation per literal site, and the VM retains its own literal-site
allocations for the execution data domain. Both engines pass and derive views
over the original allocation without copying its bytes. Module/import owners
pin generated constants until execution ends; external unsafe bindings must
provide the same lifetime and immutability. Private VM views never escape through
the public i64 runner. Invalid null/overflowing extents and unsupported static
tags/layouts reject before the resident can be accessed.

The engine partition selects implementations of the original immutable verified
body graph. There is no synthetic `HostCall` wrapper around each native body and
no portable bytecode rewrite that imports private native-control authority.
Ordinary external host calls retain their independent capability/ABI checks;
source-like capability or symbol names do not import shared-runtime proofs.

Generated argument slots contain two pointers: existing resident bytes and a
canonical initialization sidecar. Native calls and recycled tail packets preserve
the sidecar independently of the bytes, so moving one field does not reinitialize
it at a cleanup callee. VM→native exports the source home's move holes; native→VM
installs a partial external home without reading moved-out leaves. Sidecars are
budgeted and validate root liveness, bit values, and dead-parent consistency.
Only private compiler-sealed bindings enable this extension; public native
registration still requires complete owned arguments, even if a user imitates a
generated capability name. Ordinary native result slots require complete values.

Source tests run actual LLVM↔VM chains at O0 and O2, including unique-reference
mutation and return, raw observation of unchanged reference backing addresses,
static byte/UTF-8 slots, empty literals, stable literal-site addresses and derived views,
all integer widths crossing f32/f64 conversion slots and source saturation policy,
owned records/results, fixed-array results and VM patterns, linear zero-sized
owners, and once-only source Drop on both sides. Tests also cover partially
moved records and nested array/enum owners. They run the
cleanup in either engine and prove each remaining source destructor executes once.
Instruction/depth/byte limits are shared across retained source activations.
The shared runner has no separate synchronous eight-crossing ceiling or worker-
thread handoff for ordinary Glorious calls. Native allocation is checked against
the requested single-allocation limit as well as the total native-byte budget.

Raw allocation/reallocation/release use a small allocator-runtime callback over
that same allocation domain, not a VM instruction interpreter. Raw reads/writes,
offsets, reference construction, and overlapping/nonoverlapping copies execute
as LLVM operations. Offset/copy extent calculations preserve checked size and
alignment bounds, and reference construction checks non-null alignment. As in
the source unsafe contract, these checks do not establish pointer provenance,
resident validity, extent, or absence of conflicting loans for the caller.

Generated-source fixtures cover allocate in one engine and resize/release in the
other, in both directions; overlapping and nonoverlapping raw copies; mutable
references to raw allocation; zero-byte linear owners; malformed layout and
extent errors; and independent total-byte/single-allocation limits. Raw allocation
owners release bytes on execution teardown, never implicitly execute source Drop.

## Admission boundaries and remaining work

The generated backend executes admitted first-class/captured/borrowed callables,
outward Glorious effects, resumptions and checked lexical control through the
shared convention above. Labels still require correctness-driven destination
resolution/fusion; opaque or foreign boundaries cannot be repaired by stack
search. A borrowed callable must prove its receiver permission. Active handler
dependence cannot silently weaken a mandatory-tail guarantee.

The ordinary C/native-import boundary is separate. Private callable results and
outward callback effects reject before the foreign callback executes. An
arbitrary C stack cannot be captured or replayed, and no foreign unwinding or
cross-frame label protocol is implied by the shared Glorious convention.
Unsupported machine layouts/instructions and incomplete executable evidence
continue to fail closed; VM-only local operations require explicit VM selection.

The public runner currently exposes only a zero-argument i64 entry. General host
entry shapes, remaining source-analysis and library failures, and full §17
acceptance are separate work. The latest wider-suite failures are recorded in
[implementation progress](../conformance/implementation-progress.md); the
native-handler gate is not a claim that every compiler regression passes.

Run the targeted regression with:

```sh
CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0 cargo test -p grandiose-stage0 --test handler_reentry
CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0 cargo test -p grandiose-stage0 --test llvm_native handler
```

The test requires an installed compatible `clang` and Linux dynamic loader. It
compiles each native fixture at both O0 and O2 and compares results with the VM.
