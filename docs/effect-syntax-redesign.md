# Effect surface redesign — implementation instructions

Status: agreed design, ready to implement. Scope is the *surface syntax* of
effects, handlers, resumptions, and the signature forms they touch. The
semantic model (nominal effects, checked rows, quantified resumptions, deep
handlers, evidence machinery, PlaceFlow cancellation/replay tracking) is
unchanged. Nothing here adds a compiler-known control name; `handle` remains
the single structural eliminator, per the governing model in
`glorious-branded-environment-core-spec.md`.

## 0. Design summary (normative)

The unifying view: **an effect operation is a variant constructor whose last
field is the continuation.** Constructing it (expression position) performs;
destructuring it (pattern position, inside `handle`) receives the payload and
the rest of the program. Handlers are plain pattern matching over
"completed-with-a-value or suspended-on-an-operation".

### 0.1 Effect declarations

```rust
effect BrainIo {
    read() -> u8              // quantity defaults to [1,1]
    write(value: u8)          // unit result type is omitted
    [0,1] poll() -> u8        // optional resumption stays explicit
    [0,*] fork() -> Bool      // `*` replaces `infinity` in intervals
    fail(error: Text) -> !    // terminal: no quantity permitted or implied
}
```

- Default operation quantity is `[1,1]` when no bracket is written.
- `*` is accepted everywhere `infinity` currently is (effect quantities and
  `Use<[..]>` intervals). `infinity` remains accepted; the formatter rewrites
  it to `*`.
- Operations with result `!` are terminal: they have no continuation slot.
  Writing a quantity on a `-> !` operation is an error (new diagnostic).
- `-> ()` on an operation is accepted but formatted away (already the rule
  for functions).
- Separator between operations: newline-terminated, `;` accepted; formatter
  drops the semicolons.

### 0.2 Performing

Calling an operation path *is* the perform:

```rust
read_into_current(tape: &mut Tape) -> Result<(), RuntimeError> / BrainIo {
    let value = BrainIo::read();
    ...
}
```

- `perform <op-call>` remains parseable during migration and lowers to the
  identical call; the formatter deletes the keyword. After the std and tests
  are migrated (§5), remove the keyword from the grammar.
- Whether a call `Path::name(args)` is an operation call is decided by name
  resolution (the path resolves in the effect namespace), not by the parser.

### 0.3 Signatures and rows

- Braceless singleton rows: `-> u8 / BrainIo` ≡ `-> u8 / { BrainIo }`.
  Braces required for 2+ effects and for row polymorphism `{ Read<T> | E }`.
- Unit-result functions may omit the arrow entirely; the row attaches
  directly after the parameter list:

  ```rust
  application() / { ProcessArgs, FileRead, Diagnostic } { ... }
  set_current(tape: &mut Tape, value: u8) { ... }
  ```

  `-> {`, `-> ()`, and `-> / {..}` remain accepted; the formatter
  canonicalizes to the arrowless form. `-> !` is never omitted (existing
  rule).

### 0.4 `handle` — one eliminator, three arm shapes

```rust
handle <expr> {
    <pattern> => body,                    // completion arm
    Effect::op(<payload-patterns>) => body,        // tail-resume arm
    Effect::op(<payload-patterns>, k) => body,     // full-control arm
}
```

Classification is resolution- and declaration-directed, never keyword-
directed:

- **Completion arm**: the pattern head does not resolve to an operation of
  the handled row. Matches the normal result of `<expr>`. Completion arms
  must be exhaustive over the result type. If no completion arm is written,
  an implicit identity arm `x => x` is supplied (standard return-clause
  default), so today's pass-through handlers keep working unchanged.
- **Tail-resume arm**: pattern arity equals the operation's declared payload
  arity. The body must have the operation's *result* type; its value resumes
  the continuation exactly once, implicitly, in tail position. Only legal
  when the declared quantity admits exactly-once (`[1,1]`, `[1,*]`,
  `[0,1]`-with-resume — concretely: upper ≥ 1). Terminal (`-> !`)
  operations always use this shape (payload-only pattern, body has the
  handle's result type).
- **Full-control arm**: pattern arity is declared payload arity **+ 1**; the
  final sub-pattern binds the continuation. The body has the handle's result
  type.

The continuation `k` is an ordinary value:

- Its type is the compiler-generated resumption callable: callable with one
  argument of the operation's result type, returning the handle's result
  type, carrying the handler's reinstalled row, with `Use` interval equal to
  the operation's declared quantity.
- **Resume = call**: `k(v)`. There is no `resume` expression form in the new
  grammar. Provide `resume(k, v)` as an ordinary std function during
  migration (`resume<..>(k, value) { k(move value) }`).
- **Cancel = destroy**: dropping `k` (binding `_`, or explicit
  `discard(k)` — add public `discard` to std, §5.4) runs the abandoned-
  continuation cleanup. The existing `Use` rules give the policy for free: a
  `[1,1]` continuation cannot be dropped (lower bound unsatisfied — existing
  diagnostic path), `[0,_]` can. Remove the `cancel` expression form; keep a
  std `cancel(k)` alias for `discard` during migration. Existing perform-site
  soundness checks (rejecting live linear obligations across cancellable
  performs) are untouched.
- `with k =>` remains parseable during migration, lowering to the
  full-control arm; formatter rewrites it into the pattern slot. Remove after
  migration.

`handle <expr>` takes a full expression (no `perform` required). The block
after the scrutinee is always the arm block — the scrutinee position does not
participate in contextual block-to-callable elaboration.

### 0.5 What this deletes

- The per-module inspection-effect idiom (`__ResultCase`, `__CharBoolCase`,
  `SequenceCase`, `ParseCase`, ...) — replaced by completion arms.
- The `with` resumption binder and the `resumption` grammar field.
- `resume`/`cancel` as expression forms (become std functions / destruction).
- `perform` as a keyword (after migration).
- `handle perform X::inspect(v) { X::inspect(pat) => .. }` as the match
  idiom — becomes `handle v { pat => .. }`.

## 1. Reference example (must round-trip through the whole pipeline)

Old:

```rust
effect BrainIo {
    [1, 1] read() -> u8;
    [1, 1] write(value: u8) -> ();
}

handle perform RuntimeCase::inspect(
    execute_sequence(program_instructions(program), program.length, 0, &mut tape)
) {
    RuntimeCase::inspect(Result::Err(error)) => Result::Err(error),
    RuntimeCase::inspect(Result::Ok(_)) => Result::Ok(move output),
    BrainIo::read() with continuation => resume(move continuation, read_byte(&mut input)),
    BrainIo::write(byte) with continuation => {
        Vec::push(&mut output, move byte);
        resume(move continuation, ())
    }
}
```

New:

```rust
effect BrainIo {
    read() -> u8
    write(value: u8)
}

handle execute_sequence(program_instructions(program), program.length, 0, &mut tape) {
    Result::Err(error) => Result::Err(error),
    Result::Ok(_) => Result::Ok(move output),
    BrainIo::read() => read_byte(&mut input),
    BrainIo::write(byte, k) => {
        Vec::push(&mut output, move byte);
        k(())
    }
}
```

(`move` noise is out of scope for this change; leave it.)

## 2. Implementation stages

Work through the stages in order; each stage keeps the tree green.
Coordinate: `lexer.rs` / `parser.rs` / `ast.rs` / `lossless.rs` are the
frontend split; `semantic.rs` / `compiler_typeck.rs` / effect lowering are
edited concurrently by sol — land Stage 1 behind the existing
structural-AST + `normalize_for_legacy_consumers` bridge so the legacy
semantic path keeps receiving the shapes it expects until Stage 2.

### Stage 1 — grammar, AST, parser (`crates/grandiose/src/{lexer,parser,ast,lossless}.rs`)

1. Effect declarations: optional quantity (default `[1,1]` recorded
   explicitly in the AST), optional `-> ()`, `*` as interval bound token
   (lexer), semicolon-optional operation separators. Error for quantity on
   `-> !` operations (diagnostic code in the existing `G0xxx` scheme).
2. Signatures: arrowless unit form `name(params) [/ row] { body }`;
   braceless singleton row after `/`. Keep old forms parsing; mark them for
   the formatter.
3. `handle`: scrutinee is a general expression; arms become a single
   unified node `HandlerArm { pattern, body }` — no `with` field, no arm-kind
   distinction in the AST (classification happens in Stage 2). Parse legacy
   `Op(pat) with k => body` into the same node by appending `k` as a final
   binding sub-pattern; parse legacy `resume(a, b)` / `cancel(a)` /
   `perform e` as ordinary call/identifier expressions (delete the dedicated
   AST variants once `normalize_for_legacy_consumers` can synthesize the
   legacy shapes for sol's current semantic pass — until then, normalize
   new→old in the bridge).
4. Lossless/lexer conformance: update `lossless.rs` trivia handling for the
   removed tokens; extend `tests/lexer_conformance.rs`,
   `tests/parser_conformance.rs`, `tests/lossless_lexer.rs`,
   `tests/effect_path_syntax.rs`, `tests/type_syntax.rs` with the new forms
   (old forms keep their existing cases until Stage 5).

### Stage 2 — semantic classification and checking (`semantic.rs`, `resolve.rs`, `compiler_typeck.rs`)

1. Arm classification: resolve each arm's pattern head against the handled
   row — operation of the row ⇒ operation arm (then arity-classify
   tail-resume vs full-control against the declaration); otherwise
   completion arm. Ambiguity (a path that resolves both ways) is an error
   with a targeted diagnostic, not a preference.
2. Completion arms: exhaustiveness over the scrutinee's result type using
   the existing pattern-reachability machinery
   (`tests/pattern_reachability.rs`); synthesize the implicit identity arm
   when absent. Lower completion arms to the existing terminal-inspect
   handler form internally (a compiler-generated `Case`-style operation) so
   MIR/optimizer/VM are initially untouched; native MIR support can come
   later as an optimization.
3. Continuation typing: full-control arms bind `k` as the resumption
   callable with the declared `Use` interval; resume is ordinary call
   checking; drop/cancel is ordinary destruction checking (the `[1,1]`
   cannot-drop diagnostic already exists — verify its message reads well for
   continuations and add a note suggesting a resume).
4. Tail-resume arms: check body against the operation result type; lower to
   the existing "with k => resume-in-tail" form; assert the existing
   tail-resumption/one-shot specialization fires on the lowered form
   (`tests/tail_resumption_acceptance.rs`, `tests/optimizer_trace_equivalence.rs`).
5. Operation calls without `perform`: in `resolve.rs`, effect-namespace path
   calls lower to the perform node. Signature-row checking unchanged.
6. New/updated tests: extend `tests/resumptive_effects.rs`,
   `tests/multishot_effects.rs`, `tests/optional_resumptive_effects.rs`,
   `tests/handler_result_inference.rs`, `tests/terminal_effects.rs`,
   `tests/nested_captured_handlers.rs` with new-syntax twins of key cases;
   add a dedicated `tests/handler_completion_arms.rs` covering: implicit
   identity arm, exhaustiveness failure, mixed completion+operation arms,
   completion-arm-only handle (the match use), arity-mismatch diagnostics,
   dropped `[1,1]` continuation, `k` stored and resumed later, `_`-discarded
   `[0,1]` continuation.

### Stage 3 — formatter and canonical form

Formatter rewrites (all old forms → new): strip `perform`, strip `-> ()` /
dangling `->`, singleton row braces, `infinity` → `*`, default quantities
removed, `with k =>` → pattern-slot `k`, `resume(k, v)` → `k(v)` where `k`
is a continuation binder, `cancel(k)` → `discard(k)`,
`handle perform GenCase::inspect(e) { GenCase::inspect(p) => b, .. }` →
`handle e { p => b, .. }` when the effect is a single-terminal-op inspection
effect used nowhere else (detect structurally; skip when unsure). Formatter
output must re-parse to an identical AST (existing formatter invariant
tests).

### Stage 4 — tooling surfaces

- Tree-sitter (`grammar.js`, `queries/`, `test/corpus/grandiose.txt`,
  `editors/zed/`): mirror Stage 1. Remove the `resumption:` field; corpus
  gains new-syntax cases for both corpus sections; highlight queries color
  continuation binders as parameters, operation patterns as constructors.
- LSP/semantic tokens if they special-case `perform`/`resume`/`cancel`.

### Stage 5 — migrate sources, then remove legacy forms

1. `crates/grandiose/src/distributed_std.glorious`: delete `__ResultCase`,
   `__CharBoolCase`, `__FloatBoolCase`, `__U32BooleanCase` and rewrite their
   ~40 use sites as completion-arm handles; rewrite `if`/`else`/`and`/`or`/
   `not` and the Result/Option combinators (reference: `if` becomes
   `handle condition { Result::Ok(_) => Result::Ok(body()), Result::Err(e) => Result::Err(e) }`).
   Add `pub discard<T>(value: T) where T: Use<[0,*]>` and migration shims
   `resume`/`cancel`.
2. `tutorial/brainfuck/**` and tutorial chapters: apply §1; delete
   `SequenceCase`, `ProgramCase`, `RuntimeCase`, `OutputCase`, `ParseCase`,
   `RunCase`, `Utf8Case`.
3. Migrate remaining `.glorious` fixtures embedded in `tests/*.rs`.
4. Remove legacy grammar forms (`perform`, `with`, resume/cancel forms,
   quantity-on-terminal), turn their parses into targeted "old syntax"
   diagnostics with the rewrite suggestion, and drop the bridge
   normalizations.
5. Update `glorious-branded-environment-core-spec.md` §2 (callables/rows),
   the handler and label sections, and `docs/frontend-design.md` to the new
   surface; note in the spec that `resume`/`cancel` are library, not core.

## 3. Explicit non-goals for this change

- No implicit last-use `move`, no auto-reborrow, no method-call syntax, no
  `true`/`false` patterns, no `is` changes — separately tracked.
- No change to resumption quantity *semantics*, multishot representation,
  cancellation cleanup semantics, or the exclusion of cancelling
  exact-positive resumptions.
- No first-class handler values yet (arms blocks stay attached to `handle`);
  the unified arm node is designed so this can be added later without
  another AST break.
