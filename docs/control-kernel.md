# Grandiose Control Kernel and Compiler Toolkit

Status: proposed design for shrinking the compiler through source-defined,
label-aware control abstractions that fuse to direct control flow.

This is probably the **most Grandiose-specific opportunity** for shrinking the
compiler.

The language already has the right foundations:

- `if`, `else`, `and`, `or`, and `not` are ordinary source functions whose
  laziness comes from `Fn` constraints.
- The range functions are effect-polymorphic and deliberately designed to
  inline into direct loops.
- A label type is proof-only, and a generic helper that invokes a label must be
  control-inlined into the destination frame, ultimately becoming cleanup plus
  a direct `LEAVE`.
- The specification already describes label-indexed `break` and `continue`
  operations through `LoopControl<L, B, S>`.

The important design principle would be:

> Build a small reusable **control kernel**, then derive compiler-oriented
> walkers, transactions, searches, parsers, and fixed-point engines from it.

Not dozens of unrelated convenience functions.

## 1. Add a label-aware `fold_until`

The current standard library has five closely related recursive engines:

- `for_range`
- `try_for_range`
- `fold_range`
- `try_fold_range`
- `find_range`

Each has its own recursive step function.

Most of them can instead be derived from one accumulator traversal that accepts
an early-exit label.

Conceptually:

```rust
fold_until<L, A, B, F, e: EffectRow>(
    range: Range<usize>,
    accumulator: A,
    exit: L,
    step: F,
) -> A / { | e }
where
    L: Label<B>,
    F: Fn<(A, usize, L), Output = A, Effects = { | e }>;
```

A conceptual `find_range` then becomes:

```rust
find_range(range, predicate) -> Option<usize> {
    @found: Option<usize> {
        fold_until(range, (), @found, { _, index, found =>
            if(predicate(index)) {
                found(Option::Some(index))
            } else {
                ()
            }
        });

        None
    }
}
```

The same kernel can implement:

- `try_for_range` by exiting with `Result::Err(error)`;
- `try_fold_range`;
- `find_map`;
- `position`;
- `any`;
- `all`;
- `first_error`;
- `find_unique`;
- `collect_until`;
- bounded searches and scans.

This is valuable beyond removing the duplicated standard-library recursion. It
gives every compiler phase a standard vocabulary for “traverse while
accumulating, but leave immediately when something decisive happens.”

### Particularly useful derived operation: `find_unique`

Resolution repeatedly needs more than ordinary `find`. It needs to distinguish:

```text
Missing
Unique(value)
Ambiguous(first, second)
```

A `find_unique_by` helper can stop as soon as the second match is found. That
could replace the various `first + count` search records and separate
function/struct/enum ambiguity loops.

## 2. Implement the specified stateful loop protocol

The specification already gives the right low-level abstraction:

```rust
effect LoopControl<L, B, S>
where
    L: Label<B>
{
    break(value: B) -> !
    continue(state: S) -> !
}
```

Because the effect is indexed by the generative break-label type, nested loops
cannot accidentally target one another.

Build one source-library handler around this:

```text
loop_state(initial_state, body)
```

Then derive:

- `while_state`;
- `repeat`;
- `drain_stack`;
- `drain_queue`;
- `drain_worklist`;
- `repeat_until_stable`;
- `scan_until`;
- `for_range_control`;
- `fold_control`.

The state argument is important. Compiler loops commonly carry several evolving
values:

```text
cursor
pending operators
current scope
accumulator
changed flag
work queue
```

A stateful control helper removes the need for a named recursive function whose
only purpose is to thread those values into its next invocation.

The callback should be allowed to invoke `continue(next_state)` from inside
nested closures or helper calls. That is where the effect-based version is
materially better than simply returning a `LoopStep` enum.

## 3. Build control-aware syntax and IR walkers

A large fraction of compiler implementation code consists of nearly identical
recursive traversals:

- visit every child;
- skip selected nested bodies;
- collect some facts;
- stop at the first match;
- report an error;
- optionally replace a node.

Build a narrow walker toolkit for each important representation:

```text
walk_expr
rewrite_expr
fold_expr

walk_type
fold_type

walk_core
rewrite_core

walk_mir_places
walk_mir_operands
walk_cfg
```

I would not build one enormous universal visitor framework. Two capabilities are
enough:

1. The callback returns `Descend` or `SkipChildren`.
2. The callback receives a label it can invoke to stop the complete traversal
   with a result.

Conceptually:

```rust
walk_expr<L, R, F, e: EffectRow>(
    body: &ParsedBody,
    root: ExprId,
    stop: L,
    visitor: F,
) / { | e }
where
    L: Label<R>,
    F: Fn<(ExprId, ExprView, L), Output = Visit, Effects = { | e }>;
```

This can express:

- `contains_label_reference`;
- `contains_local`;
- `collect_names`;
- `all_straight_line`;
- `find_first_effect`;
- `find_first_illegal_move`;
- `collect_dependencies`;
- `count_occurrences`;
- diagnostics that abort traversal;
- visitors that call other effectful compiler routines.

The effect row should remain open and exact, just like the current range
helpers. Recent implementation work specifically added exact effect propagation
and label retention through range callbacks, demonstrating that this style can
be made compatible with the type checker and control inliner.

This would also provide a concise foundation for the future PlaceFlow
construction pass rather than creating new recursive walkers for every ownership
fact.

## 4. Build rollback guards that cooperate with label cleanup

This may be the most useful compiler-specific abstraction.

A direct label invocation lowers to **cleanup followed by `LEAVE`**. That means a
cleanup guard can safely restore compiler scratch state no matter how the scope
exits:

- normal return;
- `try` propagation;
- parser failure;
- loop break;
- loop continue;
- function-label return;
- other labeled transfer.

Create a generic or small family of checkpoint guards:

```text
CursorCheckpoint
ArenaCheckpoint
ByteBufCheckpoint
ScopeFrame
BindingFrame
DiagnosticContextFrame
TemporaryMapOverride
```

The common behavior is:

```text
create guard:
    remember original state

commit:
    disarm guard

Drop:
    if still armed, restore original state
```

For example, a parser checkpoint could remember:

- token cursor;
- expression-arena length;
- edge-vector length;
- name-vector length;
- handle-arm length.

If parsing succeeds, call `commit`. If parsing invokes any failure label,
cleanup drops the guard and rolls everything back automatically.

This eliminates patterns like:

```text
save cursor
save arena lengths
run nested operation
on every failure:
    restore cursor
    truncate arena
    truncate edges
    return error
```

It is also useful for lexical scopes. A `ScopeFrame` can restore a binding stack
or map after a callback finishes, including nonlocal completion.

I would prefer these guards over a general mutable-state effect. Effects are
excellent for nonlocal control; using them for every context read and write
would make the self-hosted compiler harder to optimize and reason about.

## 5. Build an imperative parser-control toolkit

Do not build a large parser-combinator framework. Build a small toolkit around
the existing cursor and the rollback guards:

```text
attempt
choice
optional
delimited
separated
many
many1
expect
commit
recover_until
```

The key distinction should be:

```text
NoMatch
Diagnostic(error)
```

`NoMatch` means an alternative may be attempted after rollback. `Diagnostic`
means the parser consumed enough structure that the error is authoritative.

A conceptual API:

```rust
attempt(&mut parser, { miss =>
    let name = require_ident(&mut parser, miss);
    require_token(&mut parser, TokenKind::Colon, miss);
    parse_type(&mut parser)
})
```

`miss(...)` is a static label capability. Invoking it exits the nested parser
and triggers checkpoint cleanup.

This could substantially flatten header and body parsing:

- fewer deeply nested `if` expressions;
- fewer repeated cursor/limit checks;
- fewer hand-written cleanup paths;
- one consistent place for expected-token diagnostics;
- easier speculative parsing of constructs whose prefixes overlap.

Backtracking should remain bounded and explicit. In particular, avoid multishot
continuation-based parsing: it would complicate ownership, diagnostics, and
performance for little benefit.

## 6. Build compiler worklist and fixed-point runners

Several compiler subsystems either already need or will need essentially the
same control loop:

```text
while queue is not empty:
    remove item
    compute new facts
    merge facts
    enqueue dependents when facts changed
```

Build a small toolkit:

```text
drain_worklist
solve_worklist
repeat_until_stable
fixed_point
propagate_graph
```

The engine should own only:

- queue mechanics;
- visited/enqueued bookkeeping;
- iteration/resource limits;
- early stop and diagnostics.

The callback should own the semantic domain and its merge operation. Do not
force every analysis into a universal lattice interface.

This can support:

- alias resolution;
- nominal copyability and zero-use facts;
- trait-goal tabling;
- effect summaries;
- call-graph propagation;
- CFG reachability;
- liveness;
- PlaceFlow propagation;
- type-layout facts;
- optimizer analyses.

`continue` naturally means “this item caused no change.” A failure label can
abort the whole solver with a structured diagnostic, while a break label can
return a successfully discovered witness.

## 7. Add range-producing and transactional builders

The compiler repeatedly uses this shape:

```text
start = vector.len()
append zero or more records
end = vector.len()
store { start, count: end - start }
```

Build:

```text
with_range
try_with_range
collect_range
append_range
map_range
try_map_range
```

Conceptually:

```rust
let fields = with_range(&mut output.fields, {
    append_fields(...)
});
```

For arenas and typed IDs:

```text
Arena::with_range
IndexVec::with_range
```

For bytecode construction:

```text
ByteWriter::with_record
ByteWriter::with_section
ByteWriter::with_length_prefix
ByteWriter::with_offset_table
ByteWriter::with_alignment
```

`try_with_range` should use a checkpoint guard so partial output is
automatically rolled back after a labeled failure.

This is a good use of custom primitive wrappers: the trusted primitive remains
something small like `ByteBuf::write_u32_le`; all record structure, counts,
offsets, and rollback are ordinary Grandiose code.

## 8. Add label-based guard and propagation helpers

The branded `try` work has already demonstrated that label-generic propagation
can remove a lot of nested `Result` handling. Extend that vocabulary carefully:

```text
ensure
bail
some_or_leave
ok_or_leave
require
require_eq
require_index
require_conversion
return_if
leave_if
```

Conceptually:

```rust
ensure<T, E, L>(condition: Bool, error: E, exit: L)
where
    L: Label<Result<T, E>>
{
    if(condition) {
        ()
    } else {
        exit(Result::Err(error))
    }
}
```

Then parser or verifier code becomes:

```rust
ensure(cursor < limit, error(ExpectedToken), @parse);
let token = require_some(tokens.get(cursor), error(ExpectedToken), @parse);
```

The helper must preserve the destination error type and source span; it should
not collapse everything to numeric status codes.

A separate recoverable diagnostic effect can support “report and continue,”
while labels handle terminal phase failure:

```text
Report::emit(diagnostic)     // recoverable
@phase(Result::Err(error))   // terminal
```

## 9. Introduce a structurally derived `ControlSummary`

This is the compiler-side prerequisite that makes the library toolkit scale.

The specification says the compiler understands structural mechanisms, not
names such as `if`, `loop`, `break`, or `continue`. Generic label-carrying
helpers are supposed to be control-inlined based on their actual behavior.

Recent implementation work contains a specialized late-control path for the
distributed range walkers, including explicit reasoning about tail recursion
and static `if`/`else` positions. Before adding many more control helpers, I
would replace that growing vocabulary with a general summary derived from Typed
Core:

```text
ControlSummary {
    static_label_parameters
    static_callback_parameters
    callback_call_quantities
    callback_effect_rows
    state_parameters
    direct_exits
    tail_recursive_edges
    captured_environment_access
    can_form_control_loop
}
```

The compiler validates that:

- labels do not escape;
- each label resolves to one generative destination;
- callback invocation quantities are exact;
- callback effects are forwarded exactly;
- recursive calls are in legal tail positions;
- static callbacks remain unchanged around the loop;
- no dynamic callable or unavailable body blocks control fusion.

The result should be cached per specialization.

This would let the standard library define new control functions without
teaching the compiler their names. The same mechanism would handle:

- range walkers;
- parser loops;
- worklist loops;
- tree walkers;
- `try`;
- `ensure`;
- user-defined loop variants;
- future generator/task control helpers.

## 10. Add development tools for control abstractions

Because these abstractions depend on successful fusion, I would add a compiler
inspection mode:

```text
grc --emit control-plan
```

For each relevant call, it should report:

```text
helper: fold_until
static labels: @parse
static callbacks: closure #41
forwarded effects: Diagnostic
callback quantity: [0, infinity]
tail-recursive cycle: yes
formed control loop: MIR loop #7
residual callable allocation: no
residual effect handler: no
failure reason: —
```

Also add lints with machine-applicable fixes:

- `manual_range_walk`
- `manual_fold`
- `manual_find`
- `manual_result_propagation`
- `manual_option_match`
- `manual_scope_restore`
- `manual_builder_range`
- `control_helper_not_fused`
- `control_callback_effect_widened`

This prevents the self-host from gradually accumulating hand-written recursion
again.

## Recommended kernel

I would keep the foundational library quite small:

1. `fold_until`
2. `loop_state` using `LoopControl`
3. `walk` with `Descend | Skip` plus a stop label
4. `ensure`/`require`/branded propagation
5. checkpoint guards
6. `with_range`
7. worklist draining

Everything else should be a thin compiler-oriented wrapper around those.

A possible module structure:

```text
std::control
    if / else / and / or / not
    try / ensure / require
    fold_until
    loop_state

std::traverse
    range
    slice
    indexed arena traversal

compiler::scope
    checkpoints
    lexical frames
    temporary overrides

compiler::walk
    syntax / Core / MIR walkers

compiler::parse
    cursor transactions and bounded choices

compiler::worklist
    fixed-point and queue runners

compiler::wire
    record / section / offset-table builders
```

The standard-library design already reserves a compiler-toolkit layer for
arenas, typed indices, work queues, and binary writers, so these abstractions fit
the intended layering rather than expanding the trusted compiler core.

## What I would avoid

I would not build:

- a full dynamic iterator-object ecosystem;
- a monadic parser-combinator framework;
- a generic mutable-state effect for all compiler state;
- multishot parser backtracking;
- one compiler optimization per helper name;
- helpers whose only purpose is to replace a one-line direct `handle`;
- control wrappers that hide ownership quantities or widen callback effects.

The abstractions should compile away to direct loops, direct branches, and
direct `LEAVE`s. Any abstraction that leaves behind runtime label objects,
generic effect dispatch, iterator allocation, or recursive helper calls should
produce a control-plan warning.

These tools could remove several hundred lines immediately and plausibly reach
the low thousands once parsing, tree traversal, scope rollback, search, and
emission are migrated. The larger architectural changes from the previous
review—especially unifying representations and introducing body/session
contexts—remain responsible for the biggest reduction, but this control toolkit
would make those cleaner representations dramatically more concise to operate
on.
