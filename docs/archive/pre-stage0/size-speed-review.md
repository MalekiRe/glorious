# Compiler Size and Speed Review

Status: accepted design constraints for the greenfield compiler. This review
narrows implementation architecture without changing Draft 0.1 semantics.

## 1. Finding

The language has few independent mechanisms. Treating each surface feature as a
traditional compiler subsystem would duplicate state and make the bootstrap much
larger than the specification requires. The implementation must be organized
around four kernels:

| Kernel | Covers |
|---|---|
| Callable | functions, closures, handler clauses, resumptions, captures, calls |
| Brand | labels, execution/refinement/continuation environments, binder keys |
| Quantity | value use, invocation, transitions, resumptions, cancellation |
| PlaceFlow | moves, loans, captures, environment summaries, cleanup |

Dynamic control likewise has one VM mechanism: frame transfer to a call target,
tail destination, label, handler delimiter, or captured continuation, with one
ordered cleanup operation.

## 2. Removed over-architecture

Generation 1 deliberately has none of the following:

- a retained whole-program body AST or a separate HIR;
- deterministic arena-ID allocation or speculative ID remapping;
- interning of inference-containing types;
- separate closure, handler-clause, and resumption callable hierarchies;
- separate environment, refinement, continuation, and label identity arenas;
- separate affine, linear, closure-once, and resumption quantity checkers;
- a second ownership ledger for `Environment`/`RunsIn`;
- a revisioned incremental query engine or filesystem cache;
- per-analysis incremental repair and preservation certificates;
- separate MIR SSA-value, slot, drop-flag, and register identity universes;
- a complete MIR effect/continuation interpreter in the compiler;
- normal-path abstract-interface serialization when no module loader consumes it.

These removals do not weaken semantics. They select smaller representations for
the same proofs and reuse the VM for optimizer differential execution.

## 3. Hot-path representation

The compiler scans declaration headers and body token ranges globally. Once
interfaces and fixities are known, it processes a demanded body through:

```text
body tokens -> body AST -> transient Typed Core + PlaceFlow -> MIR -> bytecode
```

The body AST is released after elaboration. Typed Core is released after MIR
lowering unless an unspecialized reachable generic still needs it. MIR scratch is
released after emission. Only declarations, interned resolved terms, solver
tables for reusable ground goals, reachable generic Core, and output tables live
for the full compilation.

All variable-length record fields are `(start,count)` ranges into flat arrays.
IDs are append-only `u32` indices. Lookup uses open-addressed tables; semantic
sorting happens only for diagnostics and bytecode. Work queues and set-valued
facts use dense bitsets when the indexed universe is dense and sparse sorted
vectors otherwise.

Candidate testing and mutually exclusive branch checking use the same undo log.
The shared `PlaceFlow` facts drive initialization, loans, quantitative events,
captures, open environment summaries, continuation captures, and cleanup.

## 4. Solver and analysis limits

The trait implementation is one canonical memoizing goal evaluator. Sealed
compiler evidence and principal-`Use` queries use indexed fast paths; ordinary
user traits and projections use tables. No specialization or trait objects means
there is no candidate-priority or object-selection layer.

MIR has six lazy analysis bundles: CFG, uses, flow, effects, values, and cost.
Mutations invalidate them with an `u8` mask. Optional passes use reusable scratch
and commit once. Feature bits on each body skip irrelevant pass families in O(1).
`-O2` runs no more than three local fixed-point rounds and obeys both body-local
and compilation-wide work budgets.

## 5. Output construction

The compiler writes numeric fields through the standard library's `ByteBuf`,
whose layer-1 backing is a mutable `Array<u8>`. It patches reserved
header/directory locations, then converts the array once with
`bytes.from_array_move`. Immutable `Text`/`Bytes` concatenation is forbidden in
the bytecode-emission hot path. Interned source text is sliced by byte offsets;
diagnostic strings are rendered only for diagnostics that survive the 100-error
cap.

The VM verifies private decoded instructions with dataflow states only at block
leaders, then freezes them into packed opcode words, one shared variable-operand
array, and compact instruction offsets. One immutable encoded container backs
constant payloads and descriptor text; verifier scratch and temporary owned
payloads are released before execution. Mutable arrays grow geometrically.

## 6. Measured constraints

The stretch targets count nonblank, noncomment Grandiose source lines:

- frontend and static semantics: 6,000;
- MIR optimizations and bytecode emission: 3,000–5,000;
- complete compiler: 9,000–12,000;
- runtime/control, primitive wrappers, formatting, and collections: 3,000–5,000;
- diagnostics, source infrastructure, and compiler-building utilities:
  2,000–4,000;
- complete bootstrap standard library: 6,000–9,000 total;
- compiler architecture review threshold: 14,000.

The target is not enforced by deleting conformance. Crossing a threshold requires
identifying which kernel or duplicated representation caused the growth.
The revised library range reflects the normative all-width checked-conversion
matrix and compiler-toolkit scope added after the original 1,500–2,500-line
sketch; it is a review budget, not permission to duplicate implementations.

The release benchmark is a cold stage-2 compiler compiling its own source and
standard library at `-O2` in less than 120 seconds and 4096 MiB. `--stats`
records per-phase
time, peak live arena entries, solver steps, MIR operations before/after each pass
group, emitted bytes, and process peak memory. Performance work is driven by
these measurements, not source-level cleverness.

## 7. Complexity retained intentionally

Higher-ranked trait bounds, GAT projection, NLL, quantitative environments, deep
handlers, and multi-shot resumption safety remain real semantic work. The design
does not approximate or remove them. It makes them share unification, place flow,
brands, quantities, callable records, and dynamic frame transfer so their
implementation cost tracks the actual language core rather than a conventional
compiler organization.
