# Default Moves and Optional Closure Capture

Status: proposed source-language rule. This document defines the intended
surface behavior for ordinary value uses, borrows, source-defined control, and
anonymous closure capture. It complements the quantitative ownership and
`Fn`/`RunsIn` design; it does not change the meaning of `Use` intervals.

## 1. Goal

Grandiose should make ordinary ownership transfer concise while keeping borrows
and deferred ownership boundaries understandable:

- an ordinary owned use transfers a non-duplicable value by default;
- an ordinary owned use copies a duplicable value by default;
- `&place` and `&mut place` explicitly request shared and unique borrowing;
- closures infer their captures by default;
- `move (places) { ... }` is an optional closure-capture override, not a
  required annotation on every owned capture.

The result should make an ordinary `if`/`else` read and behave like a direct
Rust conditional, even though Grandiose implements its control operators with
ordinary source callables and contextual lazy bodies.

## 2. `Use` terminology

The two relevant intervals must not be conflated:

| Evidence | Meaning |
|---|---|
| `T: Use<[0,0]>` | `T` may be discarded with zero owned uses. It is *not* copyable. |
| `T: Use<[0,infinity]>` | `T` is duplicable: it may be copied zero or arbitrarily many times. |
| `T: Use<[1,1]>` | `T` is exact-linear: every normal path must transfer/use it exactly once. |
| `T: Use<[0,1]>` | `T` is affine/optional: it may be transferred at most once. |

Zero-use destruction never discharges a positive lower bound. A value that is
required to be moved must be transferred, returned, transformed, or
exhaustively deconstructed on every normally completing path.

## 3. Ordinary value uses

An unadorned owned use of a place selects its access mode from the type:

```glorious
let next = value;
consume(value);
Pair { left: value, right: other };
```

- If the place's type is duplicable (`Use<[0,infinity]>`), the use is a copy;
  the source place remains available.
- Otherwise, the use is a move; the source place becomes unavailable until it
  is reinitialized.

Thus ordinary code does not require a `move value` spelling merely to transfer
ownership:

```glorious
let ticket = acquire_ticket();
let queued = ticket; // moves a non-duplicable ticket
// ticket is unavailable here

let count = 42u64;
let saved = count; // copies a duplicable scalar
use_count(count);  // still valid
```

The compiler records the selected move or copy in typed Core and validates it
through the existing move-path and quantitative-use analysis.

## 4. Borrowing remains explicit

Borrowing is never inferred from an unadorned value expression. Source spells
the desired access mode:

```glorious
inspect(&config);       // shared borrow
update(&mut state);     // unique borrow
let part = &record.key; // shared projected borrow
```

Shared borrows may coexist when their regions overlap. A unique borrow excludes
conflicting access until its nonlexically inferred final use. Reborrows and
moving a referent through a unique reference remain explicit operations; in
particular, `move *reference` is retained for taking the initialized referent
and leaving a temporary hole behind it.

## 5. Conditionals behave as ordinary branches

For source users, lazy `if`/`else` bodies must have the same ownership and loan
behavior as direct control-flow branches:

```glorious
if(ready) {
    send(job)
} else {
    retry(job)
}
```

If `job` is exact-linear, this is valid: exactly one alternative runs and the
joined actual use is `[1,1]`.

The same applies to borrows:

```glorious
if(enabled) {
    update(&mut state)
} else {
    reset(&mut state)
}
use_state(state);
```

This represents one selected unique borrow, ending after the conditional. It
must not be modeled as two independently materialized closures that hold two
simultaneous `&mut state` loans.

The `Fn`/`RunsIn` call island for a complete selector correlates its lazy
alternatives. It establishes one incoming environment, proves that the selector
invokes the required alternative(s), joins mutually exclusive uses by interval
hull, and requires compatible normal post-states. Sequential callbacks add
their uses and are not granted this alternative correlation.

Accordingly:

```glorious
if(condition) { consume(value) } else { consume(value) } // `[1,1]`
if(condition) { consume(value) }                          // `[0,1]`
```

The first form satisfies an exact-linear value; the second does not, although
it can satisfy an affine `Use<[0,1]>` value. This is ordinary path-sensitive
ownership, not a special exemption for `if`.

## 6. Inferred closure capture

Anonymous closures infer the least access mode compatible with their body and
expected `Fn`/`RunsIn` constraint:

```glorious
let render = {
    inspect(&config) // shared capture of `config`
};

let task = {
    run(job) // owned capture of non-duplicable `job`
};
```

The second closure takes ownership because its body performs an ordinary owned
use of `job`; it does not require an explicit move marker. A capture may be
shared, unique, copied, or moved as required by the body, the expected callable
mode, lifetime checking, and the selected control context.

In a linked selector, capture inference operates over the whole call island.
Two alternatives may each use the same exact-linear outer place only when the
checker proves their executions are mutually exclusive and their residual
states join. Two unrelated or sequential closures may not independently own
the same non-duplicable place.

## 7. Optional owned closure capture

The language additionally provides an optional capture override:

```glorious
move (config, job) {
    inspect(&config);
    run(job)
}
```

`move (places) { body }` captures each listed outer place by value in the
closure environment at closure formation. A duplicable listed place is copied
into that environment; a non-duplicable listed place is moved. Inside the body,
the captured field may still be borrowed, copied, or moved normally.

This is useful when a closure body only borrows a value but the closure must own
it in order to escape the surrounding lifetime:

```glorious
let deferred = move (config) {
    inspect(&config)
};
store_for_later(deferred);
```

Without the marker, this closure may infer a borrow of `config`, which cannot
outlive `config`'s lexical region. With the marker, the closure owns its
captured `config` and borrows that captured field internally.

The marker is optional. It is an ownership/lifetime assertion and an escape
hatch for capture stability under refactoring, not boilerplate required for
ordinary closure use.

`move (...)` lists outer places only. A listed place must be accessible and may
not overlap another incompatible capture in the same closure. Whether general
projected places such as `move (record.field)` are admitted follows the normal
partial-move and privacy rules; this proposal does not bypass either rule.

## 8. Relationship to Rust

Rust already moves ordinary non-`Copy` values by default and copies `Copy`
values by default. Its `move` keyword is principally a closure and `async`
capture override: `move || inspect(&config)` stores `config` in the closure
even though the body only borrows it.

Grandiose adopts that useful distinction without making ordinary source moves
verbose. In particular, users should not need to expose the implementation of
source-defined `if`/`else` as lazy closures:

```glorious
if(ready) {
    send(job)
} else {
    retry(job)
}
```

is the normal spelling. Users should not ordinarily write a `move (...)` list
on each arm. Such repeated lists would misleadingly resemble two physical moves
of one value; the correlated-selector analysis already supplies the desired
direct-branch semantics.

## 9. Diagnostics and implementation obligations

The frontend should diagnose ownership failures at the relevant boundary:

- a required owned capture cannot be satisfied by a borrow that escapes its
  region;
- a `move (...)` item names an unavailable, overlapping, or inaccessible place;
- unrelated closures attempt incompatible owned captures of one place;
- a conditional path leaves a positive-lower-bound value untransferred;
- alternative captures have incompatible normal post-states or lifetime
  obligations.

Typed Core must preserve the selected capture mode and the source span of an
explicit capture item. `RunsIn` evidence remains compiler-generated and sealed;
the optional surface marker requests a capture mode but does not let source code
forge environment evidence or bypass use, loan, privacy, or effect checking.

## 10. Non-goals

This proposal does not introduce a general `Copy` trait, implicit borrowing,
unsafe moves, manual environment construction, or a special compiler-owned
`if` syntax. It also does not make `Use<[0,0]>` copy permission. The existing
quantitative ownership rules continue to decide whether copying, moving,
discarding, borrowing, and cleanup are valid.
