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
  conversion;
- native arrays of supported scalar and owned aggregate values with capacity
  growth, initialization-state tracking, move/copy/borrow access, mutation,
  reserve, push/pop, recursive cleanup, and zero-copy-shaped
  `Vec<u8>`/`Bytes` bridge operations;
- first-class callable environments, reference-counted callable copies,
  direct and indirect invocation, and shared, unique, and owned environment
  receivers;
- binding-pack payload construction, projection, copying, and cleanup;
- typed native host-import calls for process arguments, filesystem read/write,
  and diagnostic output through the explicit C ABI above;
- custom `Drop::drop` hooks followed by exactly-once structural cleanup.

It emits only functions reachable from `main`, uses register allocas as the
first stable ABI, and validates generated IR in tests with `llvm-as`. Native
scalar, `Text`/`Bytes`, array, and callable programs are also executed against
C harnesses and compared with the VM result; owned runtime paths run under
AddressSanitizer. Unsupported callable or effect-state array elements,
handlers, and effect/resumption operations produce `G1LLVM001` instead of
silently changing semantics.

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
   C ABI, while callable/effect-state array elements, a bundled native host
   implementation, UTF-8 validation, and the remaining checked conversion
   helpers remain.
5. First-class callables: environments, indirect calls, receiver modes,
   callable ownership, and binding-pack value lowering are implemented;
   effect-bearing callable environments remain.
6. Effects and control: static typed-label push/pop/leave lowering is
   implemented; handlers, resumptions, cancellation, and multishot
   continuation storage remain.
7. Production output: object/executable emission through clang and initial
   bytecode/LLVM differential conformance tests are implemented; debug
   information, LLVM optimization pipelines, and broad differential coverage
   remain.

Each chunk extends MIR lowering and its verifier-facing tests; the bytecode
backend remains available throughout.
