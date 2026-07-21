# Grandiose

Grandiose is being rebuilt as a compact, self-hosting compiler and portable
bytecode VM. The target system is:

- `grvm`, a safe Rust bytecode decoder, verifier, VM, host-capability adapter,
  and supervisor;
- `grc`, a Grandiose compiler distributed as verified `.grbc` bytecode;
- `std-lib.glorious`, the source-defined control and compiler-building library
  prepended to every generation-1 compilation.

The normative design starts with [the architecture](docs/architecture.md),
[bytecode contract](docs/bytecode.md), [standard-library contract](docs/std-lib.md),
and [language core](glorious-branded-environment-core-spec.md).

## Repository status

This is pre-alpha and the implementation does not yet cover the complete
compiler, standard-library, or self-hosting contracts.

The legacy AST interpreter is a recovery/bootstrap executor, not a conforming
ownership or cleanup implementation. Differential results involving it are
meaningful only for programs first accepted by the compiler and confined to the
documented compatibility intersection; ordinary language conformance comes from
the compiler, artifact verifier, and VM path.

- `crates/grandiose-vm` implements the frozen G1 container, canonical codec,
  hostile-input verifier, register VM, ownership/cleanup and custom-drop model,
  references, labels, deep handlers and multi-shot resumptions, primitive set,
  capability host ABI, and supervised CLI.
- Direct and owned-indirect tail-call bytecodes, verification, frame cleanup,
  and frame replacement are implemented in `crates/grandiose-vm`. The Rust
  bootstrap interpreter separately uses a trampoline and has a deep-recursion
  regression. The portable source compiler now preserves an explicit Core/MIR
  `TailCall` and forms direct calls in a function body's syntactic tail position,
  including nested block tails, when result/effect rows match and outgoing
  cleanup has no custom hook or unresolved reference provenance. It evaluates
  and protects arguments left-to-right, performs safe outgoing cleanup, and
  emits `TAIL_CALL`; unsafe cases retain ordinary call/cleanup/return order.
  General CFG discovery and runtime-indirect formation remain unimplemented.
  The legacy LLVM compiler has a few
  tail-eligible continuation/runtime helper calls, but ordinary source calls use
  LLVM `call`/`ret`; optimizer tail-call elimination is not a language guarantee.
- `crates/grandiose` contains the Rust bootstrap interpreter and the first
  deterministic source-to-G1 compiler slices. Accepted source lowers through an
  explicit typed, resolved Core and ownership-aware register MIR before the
  artifact is emitted. The MIR carries frontend-exported `PlaceFlow` ownership
  facts: the mandatory `ImportAndValidatePlaceFlow` and `ElaborateCleanup`
  phases are implemented (never skipped), a deterministic fixed-point
  ownership engine validates initialization, partial moves, loans, and
  quantitative `Use` intervals, every return/tail-call/terminal-perform/cancel
  edge carries an exact elaborated cleanup plan, and the serialized bytecode
  cleanup maps are cross-validated against the MIR facts at every statement
  boundary before release. Its implemented scalar/monomorphic-nominal subset includes
  structural reference types, ownership-preserving reference forwarding,
  checked straight-line local borrowing/reborrowing, and closed monomorphic
  terminal or explicit
  `[0,1]` or exact finite `[n,n]` effects with total capture-free lexical handlers,
  deep optional/one-shot/exact finite multi-shot resume, explicit optional
  cancellation, and closed
  monomorphic named outward-effect rows on direct calls. Closed `cases` row
  aliases expand transparently through forward/chained references to canonical
  protocol sets. It also emits a narrow,
  fully grounded specialization slice for pure generic functions and exact
  nonescaping `Fn` arguments; captureless bodies and bodies that capture only
  ground, unrestricted, structurally copyable, reference-free values are lambda-lifted
  into direct specialization and closure-wrapper calls. Generic function specializations
  may forward a reference result from exactly one compatible reference argument,
  and reference-bearing captureless closure wrappers may likewise forward a result
  from exactly one compatible direct reference argument. Reference-bearing aggregate
  wrapper signatures and generic borrow expressions inside either generated body
  remain rejected. Reachable generic
  structs and enums can likewise be instantiated at finite fully ground scalar,
  nominal, tuple, shared-reference, unique-reference, and `Never` arguments, with deterministic
  descriptors, expected- or uniquely field/payload-guided construction, direct calls,
  struct projection, and function specialization over the instance. Constructor
  inference recursively substitutes nested field and payload expectations, records
  one exact body-local ground choice for reachability and lowering, and rejects
  payloadless or phantom binders when no expected type fixes them. Transparent
  grounded generic aliases normalize through those function and nominal
  signatures without creating runtime identity or descriptors. Finite nested
  ground applications receive deterministic child-before-parent descriptors and
  owned recursive layouts are rejected. Generic fields and enum payloads may use
  recursive tuple/shared-reference/unique-reference wrappers whose leaves are
  binders, scalars, `Never`, existing monomorphic nominals, or finite generic
  applications. Applications nested in owned tuples participate in ordinary owned
  cycle rejection. An exact nominal cycle is finite when its loop crosses at least
  one reference and receives stable cyclic descriptors; constructor families that
  grow their arguments across recursion reject even through references. Ordinary
  singleton, multi-element, and
  nested tuple values/types are structurally interned and lower through Core/MIR;
  numeric projection copies copyable fields, while one direct noncopy field move
  from an owned tuple local preserves and cleans the residual aggregate. Direct
  one-level tuple-field and monomorphic named-struct-field places retain numeric
  identity, permit shared sharing and disjoint unique loans, end lexically, and
  support one noncopy move with residual cleanup when the concrete owner has no
  applicable custom `Drop` hook; custom-`Drop` owners reject partial moves so the
  hook always observes a fully initialized value. Canonical nested numeric paths
  support mixed tuple/struct copies and shared borrows with explicit intermediate
  cleanup; nested unique borrows and moves remain outside the frozen VM opcode
  boundary. Monomorphic structs/enums and reachable fully grounded instances of
  generic structs/enums may define one pure custom `Drop` hook, optionally
  conditioned by the supported marker-goal kernel; applicable generic hooks are
  monomorphized per concrete descriptor, and canonical glue runs before reverse
  structural child destruction without changing field-derived duplicability or
  the duplicability of containing layouts. Direct pure generic calls made only by
  an applicable grounded Drop body participate in deterministic fixed-point
  specialization discovery; newly introduced ground nominal results can in turn
  activate their own Drop bodies, with the ordinary finite-growth and bounded
  generic-argument limits unchanged. The same fixed point follows exact callable
  arguments through nonescaping local aliases and transitive generic forwarding,
  plus calls made by their emitted wrappers; nested generic calls in lifted bodies
  participate normally, while effectful, borrowing, reference-capturing, noncopy,
  restricted-use, custom-`Drop`, and escaping callables remain rejected. Empty
  source marker traits may declare ordered type parameters and required associated
  types with ordered type-parameter GAT binders. Positive impls define every
  associated item exactly once; impl and item binders occupy distinct scopes, and
  canonical solver answers key each value by the item plus its arguments. Equality
  bindings constrain specialization and conditional `Use`/`Drop`, while fully
  qualified ground projections normalize recursively throughout signatures,
  layouts, and where clauses before ordinary type resolution. Exact recursive
  projections are ambiguous and argument-growing families stop at the deterministic
  256-step limit. Associated defaults, lifetime/const GAT binders, and unresolved
  generic projections remain explicitly rejected. Generic callable bodies
  are validated symbolically under canonical, sorted lexical parameter environments;
  caller assumptions can discharge nested positive, explicit-negative, constructor,
  and associated-equality obligations without self-authorizing a callee. Environments
  participate in solver table and closure-specialization identity, while every ground
  call site must still prove the callee obligations. Positive and explicit
  negative ground or nominal-constructor impls form a deterministic coherent kernel
  whose canonical goals include polarity, `Self`, and every relation argument;
  joint finite unification makes argument-disjoint impls coherent, while positive
  heads remain disjoint from both positive and negative heads. Absence of positive
  evidence never proves a negative goal. Recursive positive or negative where-goals
  gate specialization, conditional `Use`, and conditional `Drop` with distinct
  missing/refuted diagnostics plus structured ambiguity and overflow. Candidate
  lookup is indexed by polarity, trait, and outer self constructor. Potentially
  recursive impl-candidate cycles are collected before solving and every cyclic
  where edge must strictly decrease an affine type-constructor measure. Solver
  sessions enforce the documented 128-frame, 1,024-answer, one-million-step,
  256-projection, and 65,536-compilation-table limits at their specified scopes;
  cycle and limit diagnostics retain deterministic shortest goal traces.
  A trusted, out-of-band trait manifest assigns stable identities to external
  traits and freezes the names, generic kinds, associated-item kinds, and policies
  of the intrinsic `Drop`, `Use`, `Fn`, `RunsIn`, `Label`, `Environment`,
  `Destination`, and `CallDestination` roles. Source spelling alone cannot create
  intrinsic authority. Compiler-sealed traits reject both positive and negative
  source impls; ordinary external-open traits require a source-local outer nominal
  self type, with the same orphan rule for both polarities. Local source traits may
  still be implemented for predefined types. Monomorphic alias chains are expanded
  to their true self type before evidence, coherence, and orphan checks, so aliases
  cannot evade policy and aliases to local nominals retain the same identity.
  Generic alias impl heads remain explicitly rejected until binder substitution can
  be represented without changing solver identity. Trait substitutions now carry
  tagged type or structural-const arguments. Source traits and ordinary impls may
  declare ordered `Quantity` and `u32` const binders; fixed literals and const
  parameters participate in positive and explicit-negative evidence, lexical
  environments, specialization identity, coherence, and conditional `Use`/`Drop`
  gates. Quantity syntax canonicalizes to checked u32 bounds plus an explicit
  infinite upper bound, and distinct const values form disjoint impl heads. The
  compiler-defined `Quantity` const type cannot be shadowed by a source nominal or
  alias. Manifest lifetime, const, type, and effect-row kinds are retained and
  fingerprinted. Lifetime trait arguments, const generic functions/nominals,
  const-parameter GATs, and effect-row source impl items remain explicitly rejected
  before their kinds could be erased or weakened.
  Exact monomorphic and reachable-ground nominal declarations may narrow their
  structurally intersected principal quantity with any well-formed u32 interval,
  from erased `[0,0]` and affine `[0,1]` through bounded forms such as `[1,2]` and
  `[2,2]` to unbounded `[2,infinity]`. Principal intervals propagate through
  tuples, structs, enum payloads, and reachable ground generic instances, lowering
  as identity-free duplicable/zero-use bytecode claims while the compiler retains
  the exact bounds. One straight-line actual-use engine counts every complete owned
  move or copy of a named parameter/local and requires the final exact count to lie
  inside its principal interval on every supported normal exit. A `let` destination
  starts at zero; copied destinations and anonymous copied results are independent
  owners, and return, call-argument, and aggregate-field boundaries account their
  temporary inputs. Initialization itself, borrowing/reborrowing, root projection,
  lexical cleanup, and custom `Drop` add zero uses. Temporary projection and discard
  therefore reject whenever zero is outside the temporary owner's interval.
  The normative model now treats every positive principal lower bound as a
  must-move obligation: whole moves transfer that obligation to the destination,
  while only exhaustive, visibility-checked structural deconstruction eliminates
  the aggregate shell and creates independently checked field owners. Opaque
  explicit or implicit destruction is a zero-use disposal, so it cannot satisfy a
  positive lower bound; `_`, `..`, and omitted pattern subtrees likewise require
  zero-use permission. Private fields reserve structural elimination to their
  visibility authority. Accordingly, intrinsic `Drop` now requires `Use<[0,0]>`
  and remains a hook for legally disposable values, never a must-move discharge.
  The current compiler slice enforces the revised Drop containment, rejects the
  former whole-move-then-discard loophole, supports exhaustive named-struct and
  tuple deconstruction, enforces source-entry private-field authority, and emits
  a verifier-checked aggregate-shell deconstruction operation. Named-struct and
  tuple patterns now lower `_`, `..`, and omitted fields as zero-use disposal,
  erase exact-`[0,0]` aggregate fields without observable drop behavior from
  runtime layouts, and destroy runtime remainders in reverse declaration order.
  Enum ownership deconstruction,
  recursively nested subpatterns, and
  complete disposition provenance across the remaining control forms are still
  implementation frontiers. Reference-bearing aggregate fields are still
  diagnosed at both binding and discard sites until deconstruction can transfer
  or safely end their aggregate loan origins.
  Duplicable must-move values require an explicit final transfer: bare use may
  copy and leaves the source obligation live, while contextual `move value`
  forces whole-owner transfer. Every produced copy is an independently checked
  owner, so copying alone cannot launder a positive lower bound into cleanup.
  Statement assignment now supports addressable locals, visible tuple/struct
  field paths, and live unique-reference dereferences. The right-hand side is
  evaluated before the destination; initialized replacement requires zero-use
  permission for the old subtree, while assignment after an exact move
  reinitializes without destroying the transferred owner. Direct projected
  `move` can force transfer even for a duplicable must-move field. Core/MIR
  preserve the distinction through verified `DEREF_MOVE`/`DEREF_STORE`
  operations whose unique-loan referent must be restored before normal exit.
  Recovery locals are addressable cells with equivalent move holes, and
  multi-shot snapshots remap their alias graphs. Nested explicit projected
  moves, reconstruction below a moved ancestor, and enum-payload assignment
  still await the general place-flow/move-tree implementation.
  The portable frontend now has the complete generation-1 `Array<T>`
  runtime-manifest slice: all thirteen frozen construction, length, capacity,
  copy/move access, shared/unique borrow, set, push/pop, reserve, and
  fully-drained-shell leaves. Leaf authority comes from declaration identity in
  the explicitly trusted standard-library `SourceBundle` entry and is checked
  again at each call site, not inferred from spelling or a repeated segment
  name. Reachable ground leaves lower to typed Core primitive identities. The
  recovery interpreter implements the same initialized-slot and logical-capacity
  behavior and is differentially tested against the verified VM. Arrays are
  noncopy, affine when their element permits zero use, and exact-linear
  otherwise.
  The manifest boundary also includes the complete eleven-leaf immutable
  `Text`/`Bytes` slice: byte length, concatenation, equality, checked UTF-8,
  text-to-bytes, byte length/concatenation/indexing/slicing, and moved
  `Array<u8>` conversion in both directions. Concrete leaves receive the same
  declaration and call-site authority checks as generic Array leaves. Ordinary
  public source wrappers expose `String::empty`, byte length, emptiness,
  concatenation, byte views, and equality; `Bytes` exposes length, emptiness,
  equality, concatenation, checked get/slice, and ownership-safe moved
  `Vec<u8>` conversions. Bounds are proven in ordinary source before the raw
  trapping byte leaves are invoked. `String::from_utf8` performs complete
  RFC 3629 validation in tail-recursive ordinary source and reports the invalid
  lead-byte offset; `String::slice` checks reversal, bounds, and both UTF-8 byte
  boundaries before conversion. Both paths preserve recovery/VM parity and do
  not catch faults. Private-field `TextView` and `ByteView` wrappers retain an
  immutable handle plus a once-validated half-open range; their current surface
  includes checked construction, whole-value views, byte length/emptiness,
  equality, checked byte access, and safe materialization. `StringBuilder` and
  `ByteBuf` now provide dense byte accumulation, reservation, String/Bytes/view
  append, checked UTF-8 text finishing, and immutable byte finishing entirely in
  ordinary source. `ByteBuf::resize_zeroed`, fixed-width little-endian writes and
  patches, alignment, checked reservation/range arithmetic, text iterators,
  character appends, escaping, numeric formatting, and view hashing remain
  unimplemented. In particular, `resize_zeroed` currently exposes the compiler's
  unresolved unique-reference capture across nested terminal handlers; it is not
  silently replaced by a trapping or VM-private leaf. `Text` and `Bytes` copies, dereference
  copies, and continuation snapshots share immutable backing; conversion to a
  mutable byte array remains an independent deep-copy boundary. Iterator-level
  text/byte APIs remain incomplete.
  The embedded ordinary-source library now defines `Result`, `Option`, `Bool`,
  `true`, `false`, and the lazy generic `if`, `else`, `and`, `or`, and `not`
  operators with their exact zero-use bounds. These names have no compiler or
  interpreter control fast path. Type-associated callable aliases erase to
  their ordinary function identity. The first public `Vec<T>` slice is ordinary
  source over a private `Array<T>` field and supplies `new`, `with_capacity`,
  `len`, `capacity`, `reserve`, moving `push`, and explicitly trapping shared
  and unique indexing. Reference-root field projection preserves the parent
  loan and privacy authority through those wrappers in both compiled code and
  the recovery interpreter. The packaged host layer now also defines the
  `String = Text` alias, the exact `[1,1]` `ProcessArgs`, `FileRead`,
  `FileWrite`, and `Diagnostic` effects, their four ordinary performing
  functions, and `run_compiler_host`. That runner closes all four protocols
  through the manifest-bound host leaves and seals the host argument array into
  the private `Vec<String>` representation. Capture-free named ordinary
  functions coerce to exact `Fn` values, so the closed entry can pass
  `compiler_main` directly; the recovery interpreter retains the same function
  identity instead of copying its body. Checked `+`, `-`, `*`, `/`, and `%` and
  all six integer comparisons lower to their frozen primitives for every integer
  width. Comparisons convert the raw zero/one discriminator through ordinary
  source to `Bool`. Ordinary generic `wrapping_add/sub/mul`, `bit_and/or/xor/not`,
  and `shift_left/right` wrappers now cover every integer width through exact
  trusted standard-library declaration identities without expanding the trusted
  runtime manifest; shifts trap at the operand width and signed right shift is
  arithmetic. Target-named wrapping conversion and nontrapping `checked_S_to_T`
  conversion cover all integer width/sign pairs; checked conversion reaches its
  private trapping leaf only after an ordinary source round-trip/sign proof.
  The remaining integer negation, character and floating scalar mechanics,
  iterator-level text/bytes APIs,
  safe/structural collection operations, and the rest of the packaged
  compiler-building library are still implementation frontiers.
  Restricted values involved in handlers, performs, resumptions, or effectful calls
  remain conservatively rejected; unrelated effect code remains accepted, and
  memoized globals require unrestricted use because reads are not source-bounded.
  Exact monomorphic or reachable-ground Use declarations may be conditioned on
  marker goals and intrinsic `Use<R>` goals; proven goals retain the narrowing,
  absent evidence falls back to the structural interval, and cyclic or overflowing
  principal evidence diagnoses. Generic Use declarations are monomorphized over
  already-reachable grounds only. Statically unrestricted fields and payloads are
  implicitly proven. Every other accepted owned field type must have an intrinsic
  `FieldType: Use<R>` goal of exactly the same syntactic shape, ignoring source
  spans, whose interval contains the declared `Q`. This covers direct and repeated
  binders, nested applications such as `Wrap<T>`, and fixed restricted nominals
  without guessing how a compound type might decompose.
  Marker goals are solved before ground intrinsic Use obligations are retained for
  principal-interval entailment, and those obligations never create reachability.
  Coherence
  rejects overlapping generic heads and generic/exact overlap before reachability.
  Direct reference and tuple impl targets remain explicitly unsupported; transparent
  monomorphic aliases receive the same decision as their expanded target.
  Source outside that subset is deliberately rejected with structured
  diagnostics; this is not yet the distributed self-hosted `grc`.
- `compiler/` is the legacy LLVM-emitting compiler. It is not an architectural
  input, implementation template, or member of the new bootstrap chain.

Still missing are the complete language coverage of those Core and MIR
pipelines—including trait methods, associated type defaults, lifetime/const GATs,
HRTB solving, universes, and the rest of the general generic/trait kernel; atomic nested unique
move paths and full general-CFG nonlexical borrowing (the bootstrap now has a
deterministic least-fixed-point point-graph solver, canonical regions, and
alias-aware last-use expiration across straight-line blocks and structured
handler joins),
general capture modes, escaping or runtime-indirect callables, general quantities
and polymorphic/open outward effects, general handlers, lifetimes, and
refinements—the complete canonical source-defined
`std-lib.glorious`, the
bytecode-hosted compiler seed, and stage 2/stage 3 byte-identical convergence.

Run the current checks with:

```sh
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
```

The final generation-1 source extension is `.glorious`; existing `.gr` files
belong to bootstrap/legacy tooling. Generation 1 has no modules or dependency
loader: a driver concatenates `std-lib.glorious`, the primary source, and any
additional explicitly supplied `.glorious` files before compilation.
