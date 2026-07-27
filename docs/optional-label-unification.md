# Optional: label unification — labels as the intrinsic `Label` trait

Status: agreed design, **optional follow-on** to `effect-syntax-redesign.md`.
Do not start until that redesign has landed through its Stage 2 (the unified
handler-arm node and completion arms are prerequisites for the examples and
lowerings below). Scope: the label surface, destination evidence, and the
function-return boundary. The runtime transfer semantics (direct jump, cleanup
on the way out, verified `LEAVE` boundaries) are unchanged; the VM gains no
instruction and loses none.

## 0. Design summary (normative)

Grandiose's static core is "fresh anonymous nominal types + compiler-generated
intrinsic relations": closures get fresh types with `Fn`, environments get
brands with `RunsIn`, values get `Use`. This change makes labels the fourth
instance of that pattern instead of a parallel subsystem:

**A label binder mints a fresh generative nominal type. The intrinsic trait
`Label<T>` is its compiler-generated evidence. A label value is an ordinary
callable that diverges.**

### 0.1 Binder and reference syntax

```rust
@found: Option<usize> {
    ...
    @found(Option::Some(index))  // transfer: label call, diverges
    ...
    None                          // normal completion of the block
}
```

- `@name: T { body }` binds `@name` to a value of a fresh nominal type `L_n`
  with compiler-generated `L_n: Label<T>` evidence. The block's type is `T`;
  it is produced by normal completion or by invoking the label.
- `@name` in expression position refers to the innermost label binder of that
  name and produces its ordinary callable value. The sigil is required for
  every direct reference to a lexical label: invocation (`@name(value)`),
  passing (`helper(@name)`), capture, or storage. This keeps the label
  namespace explicit and prevents a label from competing with an ordinary
  value or callable of the same name.
- Once a label value has been passed or stored under an ordinary binding, that
  binding is used normally: a parameter `exit: L` where `L: Label<T>` is
  invoked as `exit(value)`. The `@` marks lookup in the lexical label
  namespace; it is not part of the value's type.
- `Label<T>` implies `Fn<(T), Output = !>` — transfer is application. There
  is no `leave` expression form.
- Label values are freely duplicable and copyable (`Use<[0,*]>`), scope-limited
  by the brand's lifetime exactly as label dependencies are today ("a value
  depending on `L` cannot outlive the scope" — existing rule, no new
  machinery). Many syntactic uses are fine; at most one dynamic invocation can
  ever happen because invocation diverges.
- `Label` is intrinsic: user code may write it in bounds and generic
  arguments but can never `impl` it. Only binders mint instances. There is no
  erased/dyn form of a label — this is what preserves the direct-jump
  guarantee (§0.5).
- The old forms `label @done: T { ... }`, bare `@outer: { ... }` generative
  scopes, `leave@done(v)`, and the labeled trailing application remain
  parseable during migration and are formatter-rewritten; they are removed
  from the grammar in the final stage.

### 0.2 Implicit function-body labels; `CallDestination` removed

Every **named** function's body is implicitly a labeled block whose label is
the function's simple name and whose payload type is the return type:

```rust
parse(input: Bytes) -> Result<Program, ParseError> {
    ...
    parse(rest)                        // recursive call
    @parse(Result::Err(error))         // early return
    ...
}
```

- The implicit label is in scope as `@parse`; the bare name `parse` retains its
  ordinary meaning everywhere. Thus `parse(rest)` is a recursive call,
  `@parse(v)` is an early return, and
  `try(read_header(&input), @parse)` passes the label as a
  `Label<Result<Program, ParseError>>` value.
- Rule for the resolver: a bare identifier never resolves to a lexical label;
  `@name` always resolves to the innermost label binder of that name. No
  expected-type-directed choice between a function and its implicit label is
  performed.
- The implicit label is generative **per activation**, like `'call`: in a
  recursive instance, `@parse` targets that instance's own boundary.
- Anonymous callables get no implicit label (they have no name). An explicit
  `@out: T { ... }` inside the body serves.
- Shadowing a function's implicit label with an inner binder of the same name
  is legal but produces a warning.

With early return spelled as a named transfer, the `return`-interception
problem `CallDestination` existed to solve disappears — label references are
made explicit by `@`, not distinguished by an evidence kind. **Delete
`CallDestination` and fold `Destination` evidence into the `Label` relation.**
Tail-call checking is unaffected: a tail site already requires no live
cleanup/label dependencies, which is exactly "the implicit label is not passed
anywhere live."

### 0.3 Destinations as ordinary generics

No destination parameter category, no new signature syntax — `Label` bounds
on ordinary generic parameters. A speculative standard-library addition is
`try`, an ordinary function taking the result and the destination label:

```rust
try<T, E, S, L>(value: Result<T, E>, exit: L) -> T
    where L: Label<Result<S, E>> {
    handle value {
        Result::Ok(inner) => inner,
        Result::Err(error) => exit(Result::Err(error))
    }
}

parse(input: Bytes) -> Result<Program, ParseError> {
    let header = try(read_header(&input), @parse);
    let body = try(read_body(&input, &header), @parse);
    Result::Ok(assemble(move header, move body))
}
```

`S` stays a free generic (the Ok side is never constructed) — plain
inference, no higher-rank machinery. This function is the `?` operator as a
two-line library. The compiler capability and example are normative; exporting
this helper from std under the name `try` is speculative and can be accepted
or rejected independently during the migration stage.

Closure capture of labels is ordinary capture, checked by lifetimes:

```rust
first_match<T, P>(items: &Vec<T>, predicate: P) -> Option<usize>
    where P: Fn<(&T), Output = Bool> {
    @found: Option<usize> {
        each_indexed(items) { (index, item) =>
            if(predicate(item)) { @found(Option::Some(index)) }
        };
        None
    }
}
```

### 0.4 Effects generic over labels

Effect declarations already take generics and bounds; `Label` bounds are now
legal there, delivering the spec's stated "label-indexed routing" goal through
ordinary machinery:

```rust
effect Walk<L> where L: Label<Found> {
    visit(node: &Node)
}

effect Spawn {
    task<L>(work: Work, done: L) where L: Label<Outcome>
}
```

Operations may carry label values in payloads; handlers may hold, forward,
and invoke them. Row instantiation mentioning `L` inherits the label's
lifetime/brand constraints — a handler installed outside the label's scope
cannot hold it (existing lifetime checking; verify with tests, no new rules
expected).

### 0.5 Guarantees

- **Directness is per-instance and mandatory.** `L` always monomorphizes to a
  concrete generative brand; after specialization every invocation site knows
  its exact destination and MUST lower to the direct transfer sequence
  (cleanups + `LEAVE`), not a dynamic search. A program where this cannot be
  proven is a compile error, not a deoptimization. `Label` being intrinsic
  and instance-only is load-bearing here: no erased labels can exist.
- **Control inlining is a required lowering, not an optimization.**
  Monomorphization identifies the label's static destination but, by itself,
  does not make that destination active in an out-of-line callee's runtime
  frame. Any specialization that may invoke a label MUST therefore be
  transitively control-inlined (or equivalently fused) into the frame that
  introduces that label before MIR emits `LEAVE`. This applies through generic
  helpers, closures, and handlers. If an unavailable body, recursive cycle,
  indirect call, or other boundary prevents the fusion, compilation fails
  with the directness diagnostic; the compiler must not materialize a runtime
  label target or fall back to stack search. Consequently label values and
  `Label` evidence remain proof-only ZSTs in all accepted programs.
- **Multishot exclusion.** A label captured in a multishot-replayable
  continuation could target an exited scope on replay. Forbid labels crossing
  multishot capture — same family and same enforcement point as the existing
  "unique references across multishot capture" exclusion. State it in the
  spec's exclusion list and test it.
- **Diverging calls are marked by tooling, not grammar.** `@found(x)` diverges
  because its type says so — the same situation as `abort()` today. Extend
  syntax highlighting / semantic tokens to mark calls whose callee is
  `Label`-typed or `-> !`, and have the formatter keep such calls
  statement-positioned.

### 0.6 What this deletes

- `label` and `leave` keywords; the labeled trailing-application form.
- `Destination` as a distinct evidence kind (becomes the `Label` relation).
- `CallDestination` evidence entirely.
- Any need for a std `return`-like construct: early return is `@name(v)`;
  error propagation can use the speculative `try(value, @name)` helper.

## 1. Reference example (must round-trip through the whole pipeline)

Old:

```rust
label @done: i32 {
    helper();
    leave@done(42);
    0
}
```

New:

```rust
@done: i32 {
    helper();
    @done(42);
    0
}
```

Plus a new-capability example that must compile and run: `try` /
`first_match` from §0.3 verbatim.

## 2. Implementation stages

Same discipline as the effect redesign: stages land in order, tree green at
every boundary, Stage 1 behind the structural-AST +
`normalize_for_legacy_consumers` bridge because semantics
(`semantic.rs`/`compiler_typeck.rs`/`compiler_regions.rs`) is edited
concurrently by sol.

### Stage 1 — grammar, AST, parser

1. Binder: `@name: Type { body }` as the sole binder form (typed); decide and
   document whether the untyped generative-scope form `@name: { body }`
   survives as sugar for an inferred payload type or is removed — default:
   keep, payload type inferred like any block.
2. Label reference `@name` as an expression (resolves to the innermost label
   binder and is the required spelling for every direct lexical-label use).
3. Parse legacy `label @n: T { }`, `leave@n(v)`, and labeled trailing
   application into the new AST shapes (legacy `leave@n(v)` → call of `@n`).
4. AST: label binder becomes a binding form producing an ordinary typed
   value; delete the dedicated leave/transfer expression nodes once the
   bridge can synthesize legacy shapes for the current semantic pass.
5. Conformance tests: `tests/labels_leave.rs`, `tests/parser_conformance.rs`,
   `tests/lexer_conformance.rs` get new-form twins.

### Stage 2 — resolution, typing, evidence

1. Mint the fresh nominal type + `Label<T>` evidence at each binder;
   implement `Label<T>` as an intrinsic relation implying
   `Fn<(T), Output = !>`; reject user `impl Label`.
2. Implicit function labels: per-activation brand, resolver rules of §0.2
   (bare names never select labels; `@name` selects the innermost label).
   New diagnostics for: shadowing warning, escaping label (should already fall
   out of lifetimes — verify message quality names the label).
3. Delete `CallDestination`; fold `Destination` checking into `Label`
   evidence + lifetimes. Grep for both names across
   `compiler_regions.rs`/`compiler_typeck.rs`/docs and remove.
4. Generic `Label` bounds on functions and effect declarations/operations;
   monomorphization-time directness check plus mandatory transitive control
   inlining (§0.5), with a dedicated diagnostic when an invocation cannot be
   fused into the frame that introduces its concrete brand.
5. Multishot exclusion check at continuation-capture sites.
6. MIR: after required control inlining, every label-value invocation lowers
   inside its destination frame to today's leave sequence; passing a label
   lowers to brand evidence (ZST at runtime — confirm labels erase like other
   proof-only values in the existing loan-proof erasure pass). Reject any
   residual label-bearing call boundary before MIR finalization.
7. New tests, `tests/label_values.rs`: label passed as parameter; label
   captured by closure and invoked (the `first_match` shape); `try`
   propagation including generic `S` inference; label carried in an effect
   payload and invoked by a handler; effect generic over `L: Label<..>`;
   escaping-label lifetime error; multishot-capture rejection; recursive
   function using both `parse(rest)` and `@parse(v)`; per-activation
   targeting under recursion; directness-failure diagnostic.

### Stage 3 — formatter

Rewrites: `label @n: T` → `@n: T`; `leave@n(v)` → `@n(v)`; keep diverging
calls statement-positioned; legacy trailing application → binder form.

### Stage 4 — tooling

Tree-sitter `grammar.js` + `queries/` + `test/corpus/grandiose.txt` +
`editors/zed`: new binder/reference forms, remove `label`/`leave` nodes,
highlight `Label`-typed and `-> !` calls distinctly, corpus twins for both
sections.

### Stage 5 — migrate, then remove legacy forms

1. std: consider the speculative `try(value, @label)` helper from §0.3 (and
   `each`/`first`-style combinators that take label parameters, since they now
   cost nothing to express); if accepted, add it and migrate applicable std
   label uses.
2. Migrate tutorial and test fixtures; rewrite early-return-shaped
   `__FooCase` remnants (anything Stage 5 of the effect redesign left because
   it was really a return, not a match) using implicit function labels.
3. Remove `label`/`leave` from the grammar with "old syntax" diagnostics
   carrying the rewrite; drop bridge normalizations.
4. Spec updates: `glorious-branded-environment-core-spec.md` §2.4 (labels),
   the Destination/CallDestination sections, the exclusion list (add the
   multishot-label exclusion), and the intent line — label-indexed routing is
   now delivered by `Label`-generic effects. Update
   `docs/frontend-design.md`.

## 3. Explicit non-goals

- No first-class handler values (still separately tracked; this change makes
  them easier later, since destinations-as-values removes one reason handlers
  needed special environments).
- No change to tail-call rules, cleanup semantics, `LEAVE` encoding, or the
  verifier's cleanup cross-checks.
- No erased/dynamic labels, ever — document as a deliberate exclusion, not a
  gap.
- `return`-as-a-name stays out of the std; the spelling is `@name(v)`.

## 4. Acceptance

- Full `cargo test -p grandiose` green at every stage boundary.
- §1's old/new examples compile to byte-identical bytecode (differential).
- `try` and `first_match` compile, run correctly under the VM, and the
  invocation sites verifiably lower to direct `LEAVE` sequences (assert via
  bytecode inspection in the test, not just behavior).
- After Stage 5, `grep -rn "\bleave@\|\blabel @" --include=*.glorious` over
  the repo is empty, and `CallDestination` appears nowhere in
  `crates/grandiose/src/`.
- Formatter idempotent; old→new rewrites re-parse to identical ASTs.
