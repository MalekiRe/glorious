# Stage-zero generated LLVM checkpoint

`StageZeroCompiler::compile_llvm(request, LlvmTarget::host())` compiles Glorious
source through the ordinary checked compiler and lowers its verified concrete
VM-LIR into LLVM IR. `LlvmIrProgram::compile` invokes an explicitly selected
trusted LLVM compiler and loads the generated object. This is actual generated
CPU code, not the Rust compiler's backend selection, a host arithmetic fixture,
or a call to the VM interpreter from each emitted operation.

This is an executable backend and ordinary mixed-call checkpoint, **not complete
language-spec §17**. Existing native-import/callback tests
remain distinct from the generated-code tests in `tests/llvm_native.rs`.

## Admitted execution

The initial selected profile is little-endian, 64-bit x86-64 Linux. Its explicit
LLVM data layout is checked against the shared native storage layouts. Other
profiles fail closed. Scalar integer widths include i128/u128; records, tuples,
fixed arrays, enums, references, raw pointers, and zero-sized
residents use the same concrete offsets, alignment, stride, and enum tag rules
as shared VM storage. Initialization metadata is separate from resident bytes.

The emitter supports checked/wrapping integer arithmetic and conversions,
comparisons and shifts, basic f32/f64 operations with canonical NaNs,
constructors/projections, basic ownership/storage instructions, real reference
loads and stores, direct calls, branches, final lexical transfers, source
destructor glue expressed by admitted operations, and direct mandatory tails.
Fixed-array patterns include nested elements and sparse remainders; native array
cleanup loops track dynamically indexed move holes, including zero-sized elements.
The exact admissible boundary is whole-graph instruction/layout admission, not
a promise that every operation on the listed type families is supported.

Ordinary direct calls use a uniform native slot ABI. Mandatory tail transfers
return to a native dispatcher that recycles two aligned argument packets. They
do not depend on LLVM tail-call optimization: alternating packets preserve
parallel argument permutation and the old body activation returns before the
next body starts. The tests execute 10,000 mutual tail transfers at native O0
and O2 under a finite call-depth limit.

Every execution has shared instruction, activation-depth, and logical native
resident-byte budgets. The initial stack-backed implementation also limits an
individual planned body to 64 KiB, its initialization tree to 16,384 paths, and
total charged native activation storage to 1 MiB. Charged storage includes body
residents, initialization metadata, parallel-transfer temporaries, and recycled
argument packets. These are logical resident limits, not an exact accounting of
LLVM register spills or a native process-memory sandbox.

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

## Generated LLVM and bytecode sharing

`compile_llvm_partitioned(request, target, use_vm)` selects the bytecode bodies
before native admission. `LlvmIrProgram::with_vm_functions` changes the partition
of an already admitted plan. Unselected functions execute generated LLVM; this
is an explicit whole-function selection, never an instruction fallback. Local
VM-only operations are allowed in selected bodies, but unsupported control is
rejected even when placed entirely in the VM partition.

Ordinary crossings use the shared native bridge in one allocation domain. Owned
aggregate parameters enter the generated body by their existing resident pointer,
without an argument-byte copy. The reverse callback installs the same external
native storage as the VM parameter home. Owned returns initialize the caller's
slot. Scalar/reference slot values are copied as ABI values while the actual
referent backing address is preserved. Source Drop glue remains the exact checked
source implementation bound by the full code identity; no same-shaped foreign
destructor is selected by a symbol name.

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
owned records/results, fixed-array results and VM patterns, linear zero-sized
owners, and once-only source Drop on both sides. Tests also cover partially
moved records and nested array/enum owners. They run the
cleanup in either engine and prove each remaining source destructor executes once.
Instruction/depth/byte limits
are shared, including still-live native frames during a VM callback. The current
synchronous mixed runner adds an explicit eight-crossing re-entry limit and
starts its closed zero-argument graph on a 16 MiB worker stack. It does not
transfer borrowed host state between threads. Native activation allocation is
also checked against the requested single-allocation limit.

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

## Explicit remaining frontier

The generated backend does not yet execute cross-engine mandatory tails,
first-class/captured/borrowed callable parameters,
outward effects, resumptions, or captured lexical control. Float conversions,
private dynamic-array/text layouts, and some pattern/projection forms are also
rejected. Ordinary closed-graph VM calls from native bodies are supported;
they are not yet a public callable-value ABI. Pointer address/cast/comparison and
size/alignment intrinsics are supported. Static-data machine leaves remain
unavailable until the shared static-data slot layout is implemented.

The public runner currently exposes only a zero-argument i64 entry. Expanding the boundary
requires source-level differential tests and actual generated LLVM↔VM calls for
callable values, static data, mandatory mixed tails, and
supported outward control contracts.

Run the targeted regression with:

```sh
CARGO_BUILD_JOBS=1 bash tooling/cargo-fast.sh test -p grandiose-stage0 --test llvm_native -- --test-threads=1
```

The test requires an installed compatible `clang` and Linux dynamic loader. It
compiles each native fixture at both O0 and O2 and compares results with the VM.
