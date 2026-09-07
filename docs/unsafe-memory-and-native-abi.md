# Host-compatible bytecode, unsafe memory, and source-owned libraries

Status: approved project direction, updated September 5, 2026 after the VM/native
and generic-library design discussion. Host-compatible memory and all-bytecode
library execution are prerequisites of the Glorious compiler project. The
Glorious LLVM backend is deferred until a working, verified self-hosted compiler
exists. Requirements below are not claims of implemented capabilities.

The selected model is one language and shared object semantics with two execution
engines: an interpreter first, and native code generation later. In unsafe-enabled
mode, the compiler, application, and complete selected standard-library source
closure must be compilable to bytecode, including raw-memory implementations.
Generic implementations such as `Vec<T>` specialize into bytecode for concrete
types; they do not require native compilation or a universally type-erased
precompiled library. Changing the execution engine must not require changing or
reconstructing an ABI-compatible object.

This decision supersedes earlier exclusions of source-language unsafe and raw
pointers, and the treatment of collection, UTF-8, and hashing algorithms as a
permanent VM primitive surface. Under the [pre-alpha evolution policy](../glorious-language-specification.md#12-two-authorities-not-two-competing-definitions),
there are no legacy artifact compatibility targets. Compiler, VM, library, and
format contracts may change together; mismatched inputs must still be rejected.
See [implementation gates](../compiler/spec/unsafe-memory-progress.md).

## 1. Library implementation means source implementation

The standard library owns `Vec`, slices, strings, maps, hashing, encoding, and
their algorithms and policies. A source wrapper around an intrinsic implementing
the whole operation does not satisfy this requirement. Renaming a VM vector to
`Array` does not make its growth and insertion library-owned.

The machine boundary supplies scalar operations and representation conversion,
raw allocation/release, layout information, memory access/movement, static data,
generic control and reference mechanisms, and explicit host capabilities.
Bulk memory operations may be machine leaves. Vector growth policy, insertion,
reversal, UTF-8 processing, and BLAKE3 are source algorithms. They execute as
bytecode first and may later be compiled to native code and optimized without
acquiring privileged source-name meaning. Public `as` remains an ordinary
trait-backed library function.

Standard-library inclusion is a library/build choice, not a special source-name
privilege. Programs may omit std subject to their actual dependencies; the
minimal machine/runtime and ABI contracts still apply. This requires an explicit
implementation change to source-bundle contracts and their consumers, with
incompatible artifacts rejected or rebuilt rather than preserved as legacy inputs.

## 2. Unsafe establishes programmer-owned obligations

Safe code can rely on guarantees established inside an unsafe implementation.
The compiler need not derive every data-structure invariant. Unsafe operations
and contracts move specified proof obligations to the programmer; they do not
make false assertions true or make invalid execution sound.

The language foundation must support:

- Raw pointers, separate from checked shared and unique references.
- Layout size/alignment, checked allocation arithmetic, uninitialized storage,
  allocation and release, raw reads/writes, and overlapping/nonoverlapping moves.
- Explicit unsafe operation scopes and unsafe callable contracts, including
  indirect calls and generic instantiation. Permitting an unsafe call in a body
  does not automatically make the enclosing function unsafe to call.
- Unsafe traits and implementations whose documented invariants may be relied
  upon by safe generic code. Ordinary `As` does not become unsafe.
- Unsafe construction of references and library invariant-bearing values, with
  initialization, validity, alignment, provenance, aliasing, and lifetime
  obligations. Returning a reference must not invent an unrelated lifetime.

Syntax and wire encodings require tested compiler changes; the current Stage0
implementation is tracked separately in the implementation gates. Unsafety
is not an ordinary user-handleable effect: handling a similarly named effect
must not grant unsafe permission or erase a call contract. An unsafe operation
scope must not silently authorize deferred closure bodies.

Quantitative ownership remains the safe contract. Copying a pointer or bytes
does not itself justify duplicating the resident `T`. A raw move transfers its
obligation; source must not subsequently read or destroy the moved-out value.
Initialization, removal, and disposal must account for use bounds and cleanup,
including partial construction and cancellation. Zero-size residents retain
these obligations even when no bytes are allocated. The unsafe implementation
is responsible for these guarantees; ordinary typed operations inside unsafe
scopes still undergo the usual checks.

Raw-pointer support does not imply arbitrary casts into sealed compiler
evidence, callable identities, host capabilities, or execution brands. Any
future unsafe assertion mechanism for those needs its own explicit contract;
a guessed layout or integer is not authority.

## 3. Source distribution now; untrusted bytecode later

The current distribution model ships source code. Each user's computer compiles
the application and its dependency closure locally using a trusted compiler and
runtime. Independently validating arbitrary externally supplied bytecode is a
valuable future project, but is not a prerequisite of raw memory, source-owned
libraries, or initial self-hosting. The unfinished two-phase bytecode admission
API is deferred with it; implementation proceeds with raw-memory execution.

The source compiler enforces types, ownership, lifetimes, unsafe scopes and
callable/implementation contracts. A fully checked source closure without unsafe
operations or assertions relies on the soundness of those checks and the trusted
compiler/runtime. Absence of unsafe opcodes in arbitrary bytes, or absence of
`unsafe` in only the application's text, is not such a proof. Unsafe std internals
and native imports remain trusted code; their safe exports retain source contracts.

Keep existing decoder bounds, compiler/structural consistency checks, execution
budgets, version checks, and host capabilities. Do not expand them into a complete
hostile-bytecode certification project now, or delete them as a shortcut. Only
locally compiler-produced output belongs on the new trusted execution path;
downloaded artifacts, altered caches, and guest-set flags do not establish that
provenance. Arbitrary raw-memory bytecode must not become safely executable through
a public Rust API. Source distribution does not prove unsafe programmer obligations
or make unrestricted execution an in-process sandbox.

### Deferred distribution profiles

The following independent admission and native-export authentication requirements
apply when untrusted bytecode distribution is implemented. They remain future
targets, not blockers for the current source-distribution workflow.

Whether guest code may execute unsafe operations is independent of which
library implementations the host trusts.

| Policy | Guest obligations | Library boundary |
|---|---|---|
| Safe-only guest | Independently verified guest code cannot perform unsafe operations, make unchecked safety assertions, or forge unsafe trait evidence. | May call safe exports of explicitly trusted native libraries implemented using unsafe. |
| Unsafe-enabled guest | Explicit host policy permits unsafe bytecode operations and contracts, including library internals operating on actual host memory. | The full selected source closure can execute as bytecode; ABI and library identity checks still apply, but this mode is not an in-process memory sandbox. |

Unsafe-enabled execution is the primary self-hosting path. The runtime executes
raw allocation/release, pointer derivation, reads/writes, and memory movement
against real process storage, not a separate offset-only heap requiring host
copies. Pointers have provenance and validity obligations, not merely integer
bit patterns. The source compiler still checks ordinary typed operations and
requires unsafe scopes/contracts; the host policy permits their execution, not
arbitrary ill-typed artifacts or incorrect unsafe code. No CLI spelling or wire
feature number is selected by this decision.

Unrestricted host-memory access can corrupt the interpreter, its metadata, or
the embedding application if an unsafe obligation is violated. Consequently,
in-process capability or verifier isolation cannot be claimed against hostile
unsafe-enabled code. Isolation for such code needs a separate boundary, such as
a supervised process. A process boundary does not offer same-address sharing
with its parent merely because both sides use the Glorious ABI. Resource checks
remain required for valid execution; they do not contain arbitrary corruption.

Safe-only is a load/link policy, not a source text scan or an artifact's own
promise. The loader must check decoded instructions, callable contracts,
instantiations, implementation evidence, and imports across the guest dependency
closure. Changing an import, body, safety declaration, or evidence invalidates
the relevant certificate. Indirect calls must not bypass checks. Unknown
features and unrecognized safety metadata fail closed.

The unsafe internals of an admitted native library are not guest bytecode. A
safe-only guest may call that library's safe `Vec::push` export, but not an
unsafe raw-write export merely because both originate in the same library.
Trust comes from host/distribution-controlled code identity and export contracts,
not a package name, source spelling, same-shaped signature, or guest-set trusted
bit. Native implementation soundness is part of the trusted computing base.
Ordinary host capabilities remain separately enforced.

All-bytecode library execution is required, not merely an optional portability
fallback. Use unsafe-enabled execution for that source closure; a separately
admitted trusted-bytecode module boundary is not a prerequisite of this path.
Unsafe library bytecode cannot masquerade as safe-only guest code. Later native
library builds can supply safe exports to safe-only guests without changing the
source algorithms. Optional native acceleration must not become a compiler
semantic callback or a dependency of the self-hosting build.

## 4. Shared representation, not serialization

For compatible native and VM code in the same process, the target is zero
marshalling: pass or borrow the same object and backing allocation without
serialization, per-element boxing/conversion, or collection reconstruction.
This does not claim zero call overhead or arbitrary cross-process/cross-target
zero-copy transport. It is a Glorious ABI, not an assumption about Rust's
private `Vec` layout or arbitrary foreign-language representations.

Both consumers must agree on:

- ABI generation, target, endianness, pointer width, field offsets, alignment,
  enum tags, zero-size representation, and calling convention.
- Exact concrete type identity and generic-instance layout. Matching size and
  alignment alone do not establish compatible types or safety contracts.
- Ownership transfer and borrowing, lifetime relations of returned views,
  mutation through callbacks, and reference invalidation.
- Allocation domain and matching release function, resident initialization,
  type-directed copy/drop hooks, quantity guarantees, and partial-move state.
- Callback/effect conventions, re-entry, cancellation, and cleanup. Native calls
  cannot silently unwind or retain a loan past their contracts.

Addressable shared objects must reside in native-layout storage. Their addresses
remain stable for the required lifetime of pointers/loans, including across VM
frame growth and callbacks. Both execution engines observe the same payload,
not stale VM-side copies. Private register representations and out-of-band
validation metadata are permitted when they do not change shared storage or
require boundary reconstruction. Ordinary checked references remain available;
a ban on safe-only raw-pointer operations does not ban opaque pointer-containing
library values. Private pointer fields cannot become safe guest mutation paths.

A safe-only bytecode operand must not gain a usable native address just by
supplying an integer. Any unsafe address conversion requires its own specified
provenance and validity rules; an address is not safe callable/capability
authority. The ABI may carry genuine pointers without per-value handle
conversions that defeat common representation. Structural admission checks do
not restore containment after invalid unrestricted unsafe memory access.

Shared in-memory layout is target-specific. Portable artifact encoding does not
make native pointers portable or change a released format's scalar widths.
Required target/layout information must be resolved and checked before execution
or linking; mismatches are explicit failures. In particular, existing G1's
fixed-width scalar encodings are not silently redefined as host-sized values.

For `Vec<T>`, the source library owns allocation, initialized length, and
capacity. Native and interpreted consumers agree on the concrete layout and
operations for `T`. Safe callers cannot write private metadata or invalidate an
outstanding view through a second alias. Specialized bytecode growth uses unsafe
memory operations; later native growth follows the same source contract. Safe
clients use ordinary methods in either case.

Library replacement, incompatible targets/layouts, allocator mismatch, and stale
type/drop metadata must fail linking, not silently select a copying adapter.
Explicit transport adapters are separate, measured paths. No integer address
serialization is a substitute for allocation provenance or import authority.

## 5. Concrete generics and cross-engine calls

For an application-defined `Widget`, the compiler instantiates the ordinary
`Vec<Widget>` implementation and emits specialized bytecode. The instance knows
the concrete layout, selected trait implementations, and movement/cleanup
behavior. The application needs neither a preexisting native `Vec<Widget>`
specialization nor LLVM at build/load time. This applies to generic library
algorithms generally, not just vector storage. Runtime type metadata may still
support verification, linking, explicit dynamic dispatch, and diagnostics; it
is not a requirement to erase all generic implementations into one native
algorithm receiving size/alignment/drop descriptors.

A native host with the matching concrete ABI can access the same object. A host
that does not know a VM-defined type must use an opaque API or its exported
operations; identical byte sizes are not a type contract. Native code does not
automatically acquire native methods for a bytecode-only specialization. It can
invoke the specialized bytecode through the execution bridge.

Bytecode code identities are not CPU-executable function pointers. Host-to-VM
calls need native entry stubs/trampolines, and VM-to-host calls need ABI-correct
dispatch. Such runtime bridges do not require a Glorious LLVM backend. Their
contracts cover argument/result placement, callable identity and lifetime,
captures, trait/vtable entries, drop glue, re-entry, and callbacks. Effects,
resumptions, cancellation, and unwinding need a shared runtime convention or an
explicitly checked boundary restriction; no path may silently lose semantics.
Callbacks and their VM state must remain live until the host can no longer call
them. Zero marshalling is not zero call overhead or permission to retain borrows.

## 6. Self-host first; LLVM later

The implementation order is:

1. Provide source unsafe contracts and raw-memory bytecode over the host-compatible
   storage substrate for locally compiled source. Independent admission of
   untrusted distributed bytecode is deferred, not on this critical path.
2. Specialize and run ordinary source libraries as bytecode. Prove actual
   VM/native storage and call interoperability using explicit host ABI fixtures.
3. Complete the full GSC-2 incremental compiler and its current runtime contract,
   independent verification, self-compilation, and C2/C3 convergence gates using
   the bytecode path. This does not replace the production query/database plan
   with a smaller compiler prototype.
4. Only after working, verified self-hosting, implement the Glorious LLVM backend
   against the same memory/runtime contract and compare native/VM behavior.

The existing Rust authoring compiler, independent interpreter/verifier, minimal
machine/OS runtime, and host ABI fixtures remain necessary native tooling. They
are not a Glorious LLVM backend and may not provide hidden compiler semantics
or collection algorithms. A native-precompiled Glorious std, a native Glorious
compiler executable, native generic specialization, and native-vs-VM compiler
comparisons are not pre-self-hosting requirements.

## 7. Delivery and evidence

Order: contracts and raw-storage foundation; compiler safety propagation;
trusted locally compiled raw-memory execution; shared ABI; source collection
migration. Independent untrusted-bytecode admission is a later project.
The compiler kernel stays intact, not replaced by a smaller compiler prototype.

Tests cover overflow/alignment, allocation failure, empty/zero-size values,
initialized/moved-out residents, drop accounting, shared/unique views, generic
and indirect calls, callbacks, and exceptional cleanup using locally compiled
source. Deferred hostile-bytecode tests must additionally prove artifacts cannot
self-authorize unsafe execution or trusted imports, and safe-only admission checks
the entire dependency closure. Those future tests do not block this work.

All-bytecode evidence must include source library specializations for newly
defined noncopy and zero-size element types, their trait/cleanup behavior, and
ordinary collection growth/access/removal. These tests must execute without a
Glorious LLVM backend, native-specialization fallback, or specialized collection
VM opcode. A successful primitive-only pointer test does not prove this gate.

Zero-marshalling evidence must cross an actual VM/native call: identical backing
addresses, mutation visible on both sides, owned and borrowed returns, no
boundary allocation or element conversion, and layout-mismatch rejection.
A Rust-only pointer test is substrate evidence, not that certificate. Initial
host fixtures exercise a declared ABI from Rust or C; they must execute actual
VM code and cover calls in both directions, including bytecode cleanup/callbacks.
Later native Glorious output must pass the same contract plus cross-backend
comparisons. Full self-hosting, independent G1 verification, and C2/C3 gates
remain open; the LLVM comparisons are deferred until after self-hosting.
