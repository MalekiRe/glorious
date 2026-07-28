# LLVM backend

> Status: active and experimental. The LLVM backend is being developed
> alongside the bytecode VM backend; selecting native emission does not remove
> or replace the VM path.

The LLVM backend consumes the same optimized, ownership-checked MIR as the
bytecode backend. It does not repeat parsing, type inference, trait selection,
or ownership analysis.

Use:

```text
grc --emit llvm-ir program.glorious
clang program.ll -o program

# Or ask the compiler driver to invoke clang:
grc --emit llvm-object program.glorious
grc --emit executable program.glorious -o program
```

Native host calls use four C-linkage symbols:

```c
G1Array *g1_host_process_args_get(void);
G1Bytes *g1_host_fs_read(G1Bytes *path);
void g1_host_fs_write(G1Bytes *path, G1Bytes *bytes);
void g1_host_diagnostic_write(G1Bytes *text);
```

Arguments are borrowed for the duration of the call and consumed by the
generated caller immediately afterward. Returned arrays/byte objects transfer
one owned reference to Grandiose. A program using these imports must link a
host implementation of the corresponding symbols; object and IR emission do
not silently grant host capabilities.

The current vertical slice supports:

- fixed-width signed and unsigned integers, `usize`/`isize`, `char`, `f32`,
  and `f64`;
- native tuple, struct, and tagged-enum values, construction, field projection,
  tag tests, deconstruction, and variant-directed owned-payload copy/drop;
- shared and unique references, borrow/reborrow, projection borrows, and
  dereference load/move/store;
- direct calls, self calls, tail calls, block arguments, returns, switches,
  statically resolved typed-label leaves, and traps;
- checked integer add/subtract/multiply through LLVM overflow intrinsics;
- checked division, remainder, negation, and shift bounds without relying on
  LLVM poison behavior;
- wrapping integer arithmetic, bit operations, shifts, comparisons, numeric
  casts, floating-point arithmetic, comparisons, negation, bit casts, and
  character scalar validation;
- explicit data layouts for the supported host triples and target-sized
  `usize`/`isize`;
- immutable, reference-counted `Text`/`Bytes` storage, literals, length,
  concatenation, equality, byte indexing/slicing, and `Text`-to-`Bytes`
  conversion, plus checked canonical UTF-8 validation;
- native arrays of supported scalar and owned aggregate values with capacity
  growth, initialization-state tracking, move/copy/borrow access, mutation,
  reserve, push/pop, recursive cleanup, and zero-copy-shaped
  `Vec<u8>`/`Bytes` bridge operations;
- first-class callable environments, reference-counted callable copies,
  direct and indirect invocation, and shared, unique, and owned environment
  receivers;
- reference-counted first-class handler values and terminal handler dispatch;
  captured resumptions retain their handler until resume or cancellation;
  activation delimiters route requests to the nearest matching handler,
  forward partial misses outward, and support `Handle` plus effectful terminal
  clauses inside typed heap frames; outward terminal bodies and direct outward
  callees also run in those frames, including
  synchronous and outward indirect callables plus direct and indirect
  synchronous/outward tail replacement, with explicit program counters,
  parent/result links, initialization state, typed cleanup callbacks, and
  effect-request records rather than relying on the native stack;
- exact and optional one-shot resumptions, including multi-frame resume,
  repeated handler re-entry, tail-resume, cancellation cleanup, and frame
  splicing from effectful clauses back into the active scheduler;
- initial exact multishot replay for scalar, immutable refcounted, nested
  aggregate, callable-capture, and supported nested-resumption frame values,
  including outward frame-chain cloning, parent/result-slot rebasing, partial
  aggregate field masks, shared reference aliases, repeated terminal-clause
  replay, and cancellation;
- binding-pack payload construction, erased-evidence layout, projection,
  copying, and cleanup;
- typed native host-import calls for process arguments, filesystem read/write,
  and diagnostic output through the explicit C ABI above;
- custom `Drop::drop` hooks followed by exactly-once structural cleanup;
- checked heap allocation and resizing paths that trap deterministically on
  overflow, allocation failure, or a null owned host result.

It emits only functions reachable from `main`, uses register allocas as the
first stable ABI, and validates generated IR in tests with `llvm-as`. Native
scalar, `Text`/`Bytes`, array, callable, handler, activation, one-shot, and
multishot programs are also executed against C harnesses and usually compared
with the VM result; owned runtime paths run under AddressSanitizer. Unsupported
effect-state array elements, replay-time effectful terminal clauses, and
unsupported deep mutable replay shapes produce `G1LLVM001` instead of silently
changing semantics.

## Delivery chunks

1. Scalar/control-flow slice (implemented).
2. Target data layout and aggregate ABI: common target layouts, pointer-sized
   integers, tuples, structs, and tagged payload enums are implemented; richer
   target discovery remains.
3. References and ownership: core borrow/reborrow and dereference operations
   plus direct `Text`/`Bytes` retain/release, nested owned aggregate cleanup,
   active-variant enum cleanup, and custom drop glue are implemented.
4. Runtime ABI: `Text`, `Bytes`, and arrays of supported owned aggregates are
   partially implemented; typed host imports are lowered through an external
   C ABI, while effect-state array elements, a bundled native host
   implementation, and richer allocator/host-fault reporting remain. Every
   primitive in the frozen bytecode primitive table has a native lowering.
5. First-class callables: environments, indirect calls, receiver modes,
   callable ownership, binding-pack value lowering, and ordinary/effect-frame
   indirect invocation are implemented. Mutable callable environments remain
   subject to the multishot cloning limitations below.
6. Effects and control: static typed-label push/pop/leave lowering is
   implemented. Handler values and terminal `Handle`/`Perform` dispatch now
   use the native heap-frame ABI, including direct outward call/return
   propagation, static tail-call replacement, typed terminal unwinding,
   nested activation routing, partial forwarding, and effectful terminal
   clause takeover.
   Exact and optional one-shot resume, tail-resume, and cancellation are also
   implemented in ordinary and effect frames, with resumed chains spliced
   into the active scheduler and resumptions owning a reference to their
   handler value.
   Initial multishot frame cloning covers scalar, immutable refcounted, nested
   aggregate/callable captures, shared-reference aliases, cancellation, and
   direct residual-field state. Indirect outward-call
   propagation is implemented with callable starter thunks and refcounted
   guard chains. Synchronous indirect calls and indirect tail calls from an
   effect frame use the same callable receiver and ownership rules as ordinary
   native calls. Deep mutable graph/handler cloning and replay-time effectful
   terminal clauses remain.
7. Production output: object/executable emission through clang and initial
   bytecode/LLVM differential conformance tests are implemented, and `-O0`
   through `-O3` are forwarded to native code generation; debug information,
   custom LLVM optimization pipelines, and broad differential coverage remain.

Each chunk extends MIR lowering and its verifier-facing tests; the bytecode
backend remains available throughout.
