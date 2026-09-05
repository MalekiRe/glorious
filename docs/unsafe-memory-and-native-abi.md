# Unsafe memory, source-owned libraries, and the native/VM boundary

Status: approved project direction, recorded September 5, 2026. This is a
prerequisite of the Glorious compiler project, not an optional post-self-hosting
experiment. Requirements below are not claims of implemented capabilities.

This decision supersedes earlier exclusions of source-language unsafe and raw
pointers, and the treatment of collection, UTF-8, and hashing algorithms as a
permanent VM primitive surface. Existing artifact generations remain explicit
compatibility targets during migration; instruction meanings do not silently
change. See [implementation gates](../compiler/spec/unsafe-memory-progress.md).

## 1. Library implementation means source implementation

The standard library owns `Vec`, slices, strings, maps, hashing, encoding, and
their algorithms and policies. A source wrapper around an intrinsic implementing
the whole operation does not satisfy this requirement. Renaming a VM vector to
`Array` does not make its growth and insertion library-owned.

The machine boundary supplies scalar operations and representation conversion,
raw allocation/release, layout information, memory access/movement, static data,
generic control and reference mechanisms, and explicit host capabilities.
Bulk memory operations may be machine leaves. Vector growth policy, insertion,
reversal, UTF-8 processing, and BLAKE3 are source algorithms. They may be compiled
to native code and optimized without acquiring privileged source-name meaning.
Public `as` remains an ordinary trait-backed library function.

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

Syntax and wire encodings require tested compiler changes. There is no shipped
`unsafe` syntax or raw-pointer instruction implied by this document. Unsafety
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

## 3. Safe guests can use unsafe native library implementations

Whether guest code may execute unsafe operations is independent of which
library implementations the host trusts.

| Policy | Guest obligations | Library boundary |
|---|---|---|
| Safe-only guest | Independently verified guest code cannot perform unsafe operations, make unchecked safety assertions, or forge unsafe trait evidence. | May call safe exports of explicitly trusted native libraries implemented using unsafe. |
| Unsafe-enabled guest | Unsafe contracts and operations are permitted under an explicitly selected policy. | ABI and library identity checks still apply; safe-only sandbox guarantees are not inferred. |

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

An all-bytecode library remains a portability target. Its unsafe internals need
an explicitly admitted trusted module boundary or unsafe-enabled execution;
they cannot masquerade as safe-only guest code. Optional native acceleration
must not become a compiler semantic callback.

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

Validation metadata may live outside payload storage. A bytecode operand must
not gain a usable native address just by supplying an integer. The ABI may carry
genuine addresses once authority and reference validity are established; it
must not require per-value handle conversions that defeat common representation.
Verification and containment rules must justify direct access. Unsafe-enabled
execution needs a separate containment decision, not safe-only certification.

For `Vec<T>`, the source library owns allocation, initialized length, and
capacity. Native and interpreted consumers agree on the concrete layout and
operations for `T`. Safe callers cannot write private metadata or invalidate an
outstanding view through a second alias. Native growth can use unsafe memory
operations while safe VM clients use ordinary methods.

Library replacement, incompatible targets/layouts, allocator mismatch, and stale
type/drop metadata must fail linking, not silently select a copying adapter.
Explicit transport adapters are separate, measured paths. No integer address
serialization is a substitute for allocation provenance or import authority.

## 5. Delivery and evidence

Order: contracts and raw-storage foundation; compiler safety propagation;
independent verifier/linker admission; shared ABI; source collection migration.
The compiler kernel stays intact, not replaced by a smaller compiler prototype.

Tests cover overflow/alignment, allocation failure, empty/zero-size values,
initialized/moved-out residents, drop accounting, shared/unique views, generic
and indirect calls, callbacks, and exceptional cleanup. Hostile artifacts must
not self-authorize unsafe execution or trusted imports.

Zero-marshalling evidence must cross an actual VM/native call: identical backing
addresses, mutation visible on both sides, owned and borrowed returns, no
boundary allocation or element conversion, and layout-mismatch rejection.
A Rust-only pointer test is substrate evidence, not that certificate. Full
self-hosting, independent G1 verification, and C2/C3 gates remain open.
