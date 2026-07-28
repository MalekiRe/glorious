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

The current vertical slice supports:

- fixed-width signed and unsigned integers, `usize`/`isize`, `char`, `f32`,
  and `f64`;
- native tuple, struct, and tagged-enum values, construction, field projection,
  tag tests, and deconstruction;
- shared and unique references, borrow/reborrow, projection borrows, and
  dereference load/move/store;
- direct calls, self calls, tail calls, block arguments, returns, switches,
  and traps;
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
- binding-pack payload construction, projection, copying, and cleanup.

It emits only functions reachable from `main`, uses register allocas as the
first stable ABI, and validates generated IR in tests with `llvm-as`. Native
scalar, `Text`/`Bytes`, array, and callable programs are also executed against
C harnesses and compared with the VM result; owned runtime paths run under
AddressSanitizer. Unsupported owned enum, callable, or effect-state array
elements, host calls, handlers, and effect/resumption operations produce
`G1LLVM001` instead of silently changing semantics.

## Delivery chunks

1. Scalar/control-flow slice (implemented).
2. Target data layout and aggregate ABI: common target layouts, pointer-sized
   integers, tuples, structs, and tagged payload enums are implemented; richer
   target discovery remains.
3. References and ownership: core borrow/reborrow and dereference operations
   plus direct `Text`/`Bytes` retain/release are implemented; nested owned
   aggregate cleanup and custom drop glue remain.
4. Runtime ABI: `Text`, `Bytes`, and arrays of supported owned aggregates are
   partially implemented; owned enum/callable/effect-state elements, host
   imports, UTF-8 validation, and the remaining checked conversion helpers
   remain.
5. First-class callables: environments, indirect calls, receiver modes,
   callable ownership, and binding-pack value lowering are implemented;
   effect-bearing callable environments remain.
6. Effects and control: handlers, resumptions, labels, cancellation, and
   multishot continuation storage.
7. Production output: object/executable emission through clang and initial
   bytecode/LLVM differential conformance tests are implemented; debug
   information, LLVM optimization pipelines, and broad differential coverage
   remain.

Each chunk extends MIR lowering and its verifier-facing tests; the bytecode
backend remains available throughout.
