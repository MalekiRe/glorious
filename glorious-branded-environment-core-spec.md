# The Grandiose Branded-Environment Core

## Compiler and Language Specification — Draft 0.1

**Status:** Normative generation-1 language core, derived from the earlier
Glorious Minimal Language revision 0.15.

The September 5, 2026 [unsafe-memory and shared native/VM ABI amendment](docs/unsafe-memory-and-native-abi.md)
adds programmer-established safety contracts and raw-memory support as project
prerequisites. Safe-only guests may use trusted library implementations with
unsafe internals. The ownership/control core remains the safe-language contract;
new syntax and artifact support require the amendment's executable gates.

**Intent:** Define the smallest coherent compiler core that preserves source-defined control flow, effect handlers, label-generic routing through intrinsic `Label<T>` evidence, linear ownership, conditional refinements, Rust-style lifetime reasoning, and arbitrary higher-order selection abstractions.

---

## 1. Governing model

The compiler knows structural mechanisms, never standard-library control names.

At runtime, the trusted control core consists of:

- anonymous callable values and calls;
- guaranteed tail calls;
- nominal `struct` and `enum` values;
- algebraic effects, deep handlers, resumptions, and cancellation;
- generative label scopes and direct typed label transfer;
- ownership, borrowing, destruction, and cleanup;
- a finite machine-intrinsic boundary.

At compile time, the trusted static core consists of:

- Rust-style traits and coherent implementation selection;
- full Rust-style lifetimes, reborrowing, higher-ranked bounds, and variance;
- a const-generic quantitative-use relation;
- compiler-generated label and environment brands;
- anonymous callable types implementing compiler-generated `Fn` and `RunsIn` relations;
- compiler-generated refinement environments for `is` pattern tests.

The compiler does not know declarations named:

```text
if else and or not
match loop for break continue return
yield await fail
+ - * / == <
```

Those remain ordinary bindings, operators, effects, and traits supplied by the
concatenated standard-library/source bundle.

The central static principle is:

> A callable body is an anonymous type. `Fn` describes its ordinary call signature. `RunsIn` proves that the body may execute against a particular compile-time environment access and records the resulting ownership state.

The central dynamic principle is:

> Dynamic branch selection is performed by effect operations and pattern-bearing handlers. Direct typed label transfer remains a separate primitive for nonlocal destination control.

---

## 2. Surface vocabulary

### 2.1 Nominal data

Products use `struct` and sums use `enum`.

```rust
struct Point {
    x: f64,
    y: f64,
}

enum Result<T, E> {
    Ok(T),
    Err(E),
}
```

`struct` and `enum` provide representation, construction, and pattern structure. Dynamic refutable elimination is performed through pattern-bearing handlers, normally through a library function named `match`.

### 2.2 Callable result and effect omission

A callable signature always contains `->`.

The result type may be omitted when it is unit. The effect annotation may be omitted when the outward effect row is empty.

| Meaning | Canonical syntax |
|---|---|
| Pure, unit result | `(args) ->` |
| Pure, value result | `(args) -> T` |
| Effectful, unit result | `(args) -> / {Effects}` |
| Effectful, value result | `(args) -> T / {Effects}` |

Examples:

```rust
reset(buffer: &mut Buffer) -> {
    buffer.length := 0
}

length(text: &String) -> usize {
    core.str_len(text)
}

write_line(text: &String) -> / {Console} {
    Console::write_line(text)
}

read_line() -> String / {Console} {
    Console::read_line()
}

fail<E>(error: E) -> ! / {Fail<E>} {
    Fail<E>::fail(error)
}
```

`()` remains the ordinary unit type and value. It is merely omitted in callable result position.

`/ {}` may be accepted in generated or explicit source, but the canonical formatter removes it. An explicit `-> ()` is also accepted but formatted as `->`.

The uninhabited result `!` is never omitted.

### 2.3 Callable declarations and literals

A named callable declaration has no `fn` keyword and requires no `=` before its body:

```rust
add(lhs: i32, rhs: i32) -> i32 {
    lhs + rhs
}
```

An explicit anonymous callable uses the same signature form:

```rust
(x: i32) -> i32 {
    x + 1
}
```

Compact inferred closures remain available:

```rust
{ x => x + 1 }
{ => cleanup() }
```

Every callable declaration or literal creates a fresh anonymous nominal type.

A block supplied in an argument position is elaborated using the expected parameter type. Name resolution, fixity grouping, and ordinary call-candidate selection happen first; the parser does not classify a block as eager or delayed from the callee's name. If the selected callable parameter is a type variable constrained by an applicable `Fn<Args>` relation, the block denotes a fresh anonymous callable rather than an immediately evaluated block value. Its source body is evaluated only when that callable is invoked:

```rust
select<F, R>(body: F) -> R
where
    F: Fn<(), Output = R>;

select() {
    expensive_computation()
}
```

Here the trailing block is equivalent to the explicit inferred closure `{ => expensive_computation() }`. The same rule applies to a block used as an operator operand. If the expected parameter is not callable, the block retains its ordinary immediately evaluated block meaning. Expected-type resolution must determine one interpretation before body checking; an unresolved or ambiguous callable constraint is a type error rather than a heuristic choice by the parser.

This is contextual elaboration, not a general value-to-callable coercion. The resulting callable has its own fresh nominal type, lexical captures, `Fn` relation, and applicable `RunsIn` relations exactly as if the closure had been written explicitly.

The type variable is arbitrary: `F`, `T`, or any other generic parameter may
trigger this elaboration through a bound such as
`T: Fn<Args, Output = R>`. The bound—not the parameter name and not the callee
name—marks the corresponding argument as delayed. Generic inference creates
the fresh closure type for the supplied block and then solves `Args`, `Output`,
effects, captures, and `RunsIn` evidence through the ordinary constraint
system. Thus library functions may acquire block-taking syntax without a new
grammar production or a compiler-known list of control-flow functions.

### 2.4 Labels

A typed label destination is introduced with:

```rust
@done: i32 {
    body
}
```

The binder mints a fresh nominal type `L_done` with compiler-generated
`L_done: Label<i32>` evidence. `@done` without a colon refers to that value;
the sigil selects the lexical label namespace.

Transfer is ordinary diverging application:

```rust
@done(42)
```

After a label is passed under an ordinary binding, that binding is called
without `@`:

```rust
exit(42) // where L: Label<i32>
```

Every named function body has an implicit label bearing the function's simple
name and result type:

```rust
parse(input: Bytes) -> Result<Program, ParseError> {
    parse(rest)               // recursive function call
    @parse(Result::Err(err))  // transfer from this activation
}
```

Anonymous callables have no implicit label. There is no `label` or `leave`
keyword and no labeled trailing-application form.

### 2.5 Effects and handlers

The core retains:

```text
effect
perform
handle
cancel
tail
```

Resumption invocation may use either explicit `resume(k, value)` syntax or ordinary callable syntax on a compiler-generated resumption type. The initial implementation may retain `resume` as the canonical surface form.

---

## 3. Quantitative use

### 3.1 Compile-time quantity values

Quantities are const-generic values:

```rust
enum Amount {
    Finite(u32),
    Infinite,
}

struct Quantity {
    lower: u32,
    upper: Amount,
}
```

The interval must satisfy:

```text
0 <= lower <= upper
```

where every finite value is below `Infinite`.

Surface interval syntax is shorthand:

```text
[0,0]        erased
[0,1]        affine
[1,1]        linear
[1,infinity] relevant
[0,infinity] unrestricted
[m,n]        bounded
```

Here `erased` describes the ownership quantity, not an unconditional permission
to remove runtime state. An exact-`[0,0]` value may be represented by an erased
`Available` field only when neither it nor any transitively owned child has an
observable `Drop` hook. Otherwise its runtime storage remains present so
zero-use destruction can invoke every hook in the required order.

For example:

```rust
T: Use<[1,1]>
```

is normalized to a const-generic `Quantity` value.

### 3.2 The intrinsic `Use` trait

```rust
#[compiler_intrinsic]
trait Use<const Q: Quantity> {}
```

`Use` is user-implementable only through the restricted principal-quantity rule below. It has no methods.

Every type has exactly one **principal use interval** `principal(T)`.

A bound:

```rust
T: Use<Q>
```

holds exactly when the requested interval is contained in the principal interval:

```text
Q <= principal(T)

iff

principal(T).lower <= Q.lower
and
Q.upper <= principal(T).upper
```

Thus an unrestricted type satisfies affine and linear requests, while an exact-linear type satisfies only exact-linear requests.

### 3.3 Meaning of a use count

The count measures owned source-level uses of a value or compile-time environment authority.

Examples of owned use include:

- moving the value into a consuming parameter;
- moving it as a whole into a result, aggregate, continuation, or other owner;
- invoking a once-consuming callable or environment transition;
- structurally duplicating it when duplication is legal.

Temporary shared and unique borrows do not themselves consume an owned use. Their legality is governed by the borrow checker.

Opaque destruction, whether explicit or inserted as cleanup, contributes zero
owned uses. A custom `Drop` hook may run, but neither the hook nor structural
destruction retroactively satisfies a positive lower bound.

A positive lower bound is therefore a **must-move obligation**. On every
normally completing path, ownership must be transferred at least that many
times; merely reaching destruction is not a transfer.

### 3.4 Structural derivation

When a nominal type has no explicit `Use` implementation, the compiler derives its principal interval as the strictest interval supported by all possible fields.

For a `struct`, this is the interval intersection of its fields:

```text
principal(struct { f1: T1, ..., fn: Tn })
    = principal(T1) intersect ... intersect principal(Tn)
```

For an `enum`, the compiler computes the interval safe for every possible variant, taking the intersection across every payload field of every variant. A fieldless variant contributes the unrestricted interval.

Interval intersection is:

```text
[max(lower1, lower2), min(upper1, upper2)]
```

The compiler rejects a nominal type whose field requirements have an empty intersection.

Canonical built-ins include:

```text
principal(())        = [0,infinity]
principal(&'a T)     = [0,infinity]
principal(&'a mut T) = [0,1]
```

Repeated access through a unique reference is expressed by reborrowing; it does not structurally duplicate the unique-reference value.

An explicit `move *reference` may transfer the whole referent through a live
unique reference without consuming the reference handle. The referent is then
an initialization hole carried by that handle. Every normally completing path
must restore the hole with `*reference = value` before the handle is read,
aliased, transferred, captured across resumptive control, ended, or allowed to
leave scope. Restoration is a store into uninitialized storage and never runs
destruction for the old referent. A path that provably does not return may end
with the hole open. Shared references never permit this operation.

### 3.5 Manual restriction

A nominal type may provide one explicit principal implementation:

```rust
impl Use<[1,1]> for Ticket {}
```

The declared interval must be a subset of the structurally derived interval. It may:

- raise the lower bound;
- lower the upper bound;
- do both.

It may never widen structural capability.

This allows a type with unrestricted fields to impose linear, affine, relevant, or arbitrary bounded discipline.

`Use` does not use negative implementations. A single principal interval already gives complete positive and negative information.

### 3.6 Usage composition

The checker computes an actual use interval for every binding and environment authority.

Sequential composition adds intervals.

Mutually exclusive branches take the interval hull:

```text
branch_join([l1,u1], [l2,u2]) = [min(l1,l2), max(u1,u2)]
```

Unknown repetition produces an infinite upper bound when the body may execute at least once.

Nested callable or continuation execution multiplies use intervals when one execution repeats another owned use.

Callable multiplication is justified by a canonical interprocedural
performance summary, not by membership in an outward may-effect row. The
summary records finite normal-return multiplier alternatives, abandonment, and
unbounded or opaque widening separately. Sequence multiplies alternatives,
exclusive control unions them, and nonreturning alternatives do not pollute the
normal join. Only an exact non-abandoning singleton may be applied as a scalar
ownership weight; for example two sequential exact-two performance sites yield
the exact multiplier four. Summary evidence is keyed and emitted
deterministically so it contributes to the Typed Core fingerprint.

Terminal handler alternatives contribute a finite normal branch union only
when the authoritative pattern-matrix checker proves the matching payload rows
exhaustive. A nonexhaustive terminal matrix retains an abandonment alternative,
including when its reachable clauses all share one multiplier. Calls with an
empty outward row are not assumed to return: their internal effects cannot
multiply a caller suffix, but their normal-return summary must still distinguish
identity from unconditional nontermination.

The inferred actual interval must be contained in the principal interval.

In addition, every live value whose principal lower bound is positive must have
its must-move obligation discharged on every normally completing local or
nonlocal path. A path that aborts immediately, or is proven not to terminate,
has no subsequent ownership state and is exempt. This exception does not permit
a cleanup edge to discard a must-move value before a nonlocal transfer.

### 3.7 Whole transfer and deconstruction

A whole-value move transfers the value and propagates its complete residual
must-move obligation to the destination owner. It does not turn a must-move
value into a value eligible for cleanup.

For a duplicable type, a bare owned use may copy and leave the source owner
live. The contextual prefix `move value` instead forces a whole-owner transfer,
even when copying is permitted, and makes the source place unavailable. Copying
never discharges the source's must-move obligation and creates a second owner
with its own independently checked obligation. Consequently a positive-lower,
duplicable value must eventually use `move`, exhaustive deconstruction, or
another ownership transition that actually consumes its final source place;
any number of copies alone is insufficient.

An exhaustive, visibility-checked ownership deconstruction is the only
operation that may consume an aggregate shell without transferring that shell.
It is a consuming ownership transition that discharges the shell obligation,
marks the shell consumed, and creates independent ownership and must-move
obligations for every extracted field or active variant payload. Obligations are
therefore redistributed, not erased. Such a deconstruction must identify the
active enum variant and cover the complete visible representation.
Deconstruction discharges the shell's complete residual quantitative
obligation as a disposition rather than adding one ordinary whole-value use;
the newly bound or discarded children are then checked independently.

An aggregate with a custom `Drop` implementation cannot be ownership-
deconstructed, even when it is fieldless. `Drop` is run only by a legal zero-use
destruction path, while deconstruction consumes the shell without running that
hook. Such a value must be transferred whole or, when it permits zero use,
destroyed with its hook intact.

A wildcard `_`, rest pattern `..`, omitted field, or otherwise discarded
subpattern is an opaque destruction of the corresponding subtree. It is legal
only when that subtree satisfies `Use<[0,0]>`. The same rule applies recursively
inside tuples, structs, enum payloads, and pattern-bearing handlers.

Private fields may be ownership-deconstructed only in a scope authorized to see
those fields. Outside that scope, the nominal value is opaque: it may be moved
whole, borrowed as a whole, or destroyed only when zero use is permitted, but a
private field may not be projected for copying, moving, or borrowing and the
private shell may not be bypassed by a pattern.

For G1, a field is public by default and may be written `private field: T` to
restrict it. Each entry in a `SourceBundle` is one privacy authority domain,
even though value/type lookup remains bundle-flat and G1 has no import loader.
A source pattern may name a private field only when its span belongs to the same
bundle entry as the nominal declaration. Single-source compilation has one such
domain. Compiler-generated deconstruction carries the declaration's resolved
authority identity; copying the type or field spelling never grants access.
Later module formats may group several source entries under one authority, but
must preserve this identity-based rule.

---

## 4. Destruction and `Drop`

### 4.1 `Drop` is a hook, not a use capability

```rust
#[compiler_intrinsic]
trait Drop: Use<[0,0]> {
    drop(&mut self) ->
}
```

`Drop` means only:

> When a value of this type is destroyed, run this custom hook exactly once before structural field destruction.

Implementing `Drop` does not change `principal(T)` and never satisfies a
must-move obligation. The supertrait requires opaque zero-use destruction to be
legal. Consequently a type whose principal lower bound is positive cannot
implement `Drop`; affine, erased, and unrestricted types whose interval contains
`[0,0]` may do so.

### 4.2 Destruction sequence

When destruction is selected, the compiler performs:

1. if `T: Drop`, call `Drop::drop(&mut value)` exactly once;
2. destroy the active fields in reverse declaration order;
3. release the enclosing storage when applicable.

For an `enum`, only the active variant payload is destroyed.

If no `Drop` implementation exists, step 1 is omitted. Structural destruction still occurs.

This sequence is opaque zero-use destruction. It may be selected only when the
complete active subtree permits `Use<[0,0]>`; otherwise ownership must be
transferred or exhaustively deconstructed instead.

### 4.3 Explicit and implicit destruction

An explicit compiler operation conceptually named `destroy(value)` performs
opaque destruction. It contributes zero owned uses and is legal only when
`principal(T)` contains `[0,0]`.

The standard library may export an ordinary function named `drop` around this operation; the compiler does not recognize that source name.

Implicit destruction at scope exit follows the same rule. Every still-active
subtree must permit zero use; cleanup cannot erase a must-move obligation.

Therefore this remains an error:

```rust
struct MustAccount { ... }
impl Use<[1,1]> for MustAccount {}

example() -> {
    value = MustAccount(...)
    destroy(value) // error: opaque destruction requires Use<[0,0]>
}
```

This is legal:

```rust
example() -> {
    value = MustAccount(...)
    transfer(value)
}
```

The whole transfer propagates the required ownership obligation to its receiver.

### 4.4 Restrictions on `Drop`

A custom `Drop` implementation must:

- use the exact intrinsic `Drop` trait identity;
- have the signature `drop(&mut self) ->`;
- expose no outward effects;
- perform no label transfer;
- neither suspend nor capture a resumption;
- not move fields out of `self`;
- not resurrect or return ownership of `self`.

Safe code may not partially move from a type with a custom `Drop` implementation. This keeps the hook’s view of the value fully initialized.

The language does not prove destructor termination. A diverging hook prevents later field destruction and the original cleanup from completing.

---

## 5. Rust-style lifetimes and variance

### 5.1 Lifetime syntax

The language supports:

```text
'a
'static
'_
```

and constraints:

```text
'a: 'b
T: 'a
for<'a> Bound
```

It includes:

- lifetime elision;
- nonlexical lifetimes;
- shared and unique reborrowing;
- higher-ranked trait bounds;
- generic associated types;
- drop checking;
- outlives inference.

The former `scoped` parameter category is unnecessary. Nonescape is expressed by ordinary lifetime relationships. A value that contains a reference, label dependency, environment dependency, or handler dependency tied to `'call` cannot be returned or stored beyond `'call`.

### 5.2 Variance

The compiler follows Rust-style variance:

```text
&'a T
    covariant in 'a
    covariant in T

&'a mut T
    covariant in 'a
    invariant in T

function arguments
    contravariant

function results
    covariant
```

Nominal compiler-generated label and environment identities are invariant. Two structurally identical brands are never interchangeable.

Anonymous callable variance is derived from its hidden runtime fields. The compiler may add invariant phantom dependence on an environment brand when necessary to prevent accidental substitution.

A custom `Drop` hook is assumed capable of observing every borrowed field, so normal drop-check rules require those borrows to remain valid through destruction.

---

## 6. Compiler-generated static brands

### 6.1 Label brands

```rust
#[compiler_intrinsic]
sealed trait Label<T>: Fn<(T), Output = !> {}
```

Only the compiler creates implementations.

A label binder introduces:

```text
fresh lifetime 'scope
fresh opaque type L
proof L: Label<T>
```

The type and its evidence are proof-only and have no runtime representation.
Dependence on `L` is bounded by `'scope`; the lifetime is not an explicit
`Label` argument.

### 6.2 Environment brands

```rust
#[compiler_intrinsic]
sealed trait Environment<'scope> {}
```

Only the compiler creates implementations, except for the canonical unit implementation:

```rust
impl<'scope> Environment<'scope> for () {}
```

`()` means the empty environment: no captured places, no borrow dependency, no label dependency, and no ownership transition.

An environment brand is a compile-time identity for an ownership or refinement state. It is not a runtime record and is not structurally equal to another environment with the same fields.

### 6.3 The role of an environment

For closure selection, `E: Environment<'e>` identifies one incoming ownership ledger.

For refinement contexts, an environment brand describes one branch-local collection of bindings, borrows, and facts.

For continuations, an environment brand describes the captured continuation state relevant to resume and cancellation checking.

The wrappers and traits using the brand determine which interpretation applies. The brand itself remains one generic static identity mechanism.

---

## 7. Anonymous callable types

### 7.1 Every callable has a fresh type

Every named function, anonymous function, closure, handler entry, and resumption has a fresh anonymous nominal type.

Examples:

```text
typeof(add)          = anonymous function-item type F_add
typeof({ x => ... }) = anonymous closure type F_27
```

A noncapturing function item has zero runtime size. A capturing closure has a compiler-chosen hidden layout.

### 7.2 `Fn`

```rust
#[compiler_intrinsic]
sealed trait Fn<Args> {
    type Output;
    type Effects: EffectRow;
}
```

Only the compiler synthesizes implementations.

`Fn` describes the ordinary call signature of a particular receiver type. The receiver type is `Self`, so the three familiar call modes arise from ordinary types:

```text
F
&mut F
&F
```

A callable that only observes its own state may receive implementations for all three forms. A callable that mutates its own state may receive implementations for `&mut F` and `F`. A consuming callable may receive an implementation only for `F`.

There is no `Receiver` enum and no separate `Fn`, `FnMut`, and `FnOnce` trait family.

### 7.3 `RunsIn`

```rust
#[compiler_intrinsic]
sealed trait RunsIn<Access, Args>: Fn<Args> {
    type After;
}
```

Only the compiler synthesizes implementations.

`Access` must have one of these forms:

```text
E
&'a E
&'a mut E
```

where `E: Environment<'scope>` and the borrow lifetime fits within `'scope`.

The meanings are:

```text
RunsIn<E, Args>
    owns or commits one transition from E
    may produce a different After environment

RunsIn<&'a E, Args>
    observes E through a shared static borrow
    After must be E

RunsIn<&'a mut E, Args>
    accesses E through a unique static reborrow
    After must be E
```

References to environment brands in `RunsIn` bounds are compile-time access forms. They have no runtime pointer or ABI payload, but obey the ordinary lifetime and variance rules of shared and unique references.

When `Fn::Output = !`, `RunsIn::After` is ignored because there is no normal successor edge.

### 7.4 Calling

A call expression:

```rust
f(args)
```

requires:

1. an applicable `Fn<Args>` implementation for `F`, `&mut F`, or `&F`;
2. an applicable `RunsIn<Access, Args>` implementation for the currently available environment state;
3. legal ordinary ownership and borrowing of the callable value;
4. legal access to the environment brand;
5. satisfaction of the callable’s effect row.

Absent an expected receiver type, the compiler tries the least-consuming callable receiver in this order:

```text
&F
&mut F
F
```

It likewise prefers the least-consuming applicable environment access:

```text
&E
&mut E
E
```

Expected types and explicit source ownership forms take priority. Source may force the callable receiver with:

```rust
(&f)(args)
(&mut f)(args)
move f(args)
```

### 7.5 Noncapturing functions and unit environment

A normal pure noncapturing function receives the unit environment relation:

```rust
add(lhs: i32, rhs: i32) -> i32 {
    lhs + rhs
}
```

conceptually produces:

```text
F_add: Fn<(i32,i32), Output=i32, Effects={}>
&F_add: RunsIn<&(), (i32,i32), After=()>
F_add:  RunsIn<(),  (i32,i32), After=()>
```

The physical capture layout of every noncapturing function is `()`.

A runtime-noncapturing higher-order function may nevertheless be polymorphic over a nonempty execution environment when it invokes callback bodies that act on that environment. Runtime capture layout and `RunsIn` execution state are deliberately separate concepts.

### 7.6 Multiple environments

One callable type may have compiler-generated `RunsIn` implementations for several compatible environment brands.

A body needing only a shared logger may run in any environment whose hidden ledger supplies that logger. The public type system does not expose an `Includes` operation. The existence of:

```rust
F: RunsIn<&E, Args>
```

is the proof that `E` provides everything the body needs.

---

## 8. Environment sharing and mutual exclusivity

### 8.1 Environment identity is not capture shape

For two bodies with footprints:

```text
A = { file: move, logger: shared }
B = { file: move, stats: unique }
```

three facts matter:

```text
intersection = { file }
union        = { file, logger, stats }
shared state identity = E
```

The intersection identifies overlapping places whose accesses must be correlated. The union identifies all places whose lifetime or residual state may affect the entire expression.

Neither set is the public meaning of `E`.

> `E` is the nominal identity of the incoming ownership state from which both body-specific footprints begin.

The compiler computes intersections and unions internally while synthesizing `RunsIn` evidence.

### 8.2 Open environment formation

When a call expects several callable arguments related through the same unresolved environment variable `E`, the compiler:

1. creates one fresh nominal `E: Environment<'e>`;
2. checks every linked callable body provisionally;
3. records each body’s hidden place footprint, access modes, effects, and lifetime requirements;
4. forms one static ledger over the union of relevant places and residual obligations;
5. checks overlapping accesses using borrow and quantity rules;
6. synthesizes one `RunsIn` implementation per body;
7. seals `E` at the smallest enclosing expression whose constraints no longer escape.

Later alternatives may widen the ledger while `E` remains open.

The runtime representation may use:

- one unioned capture frame;
- shared common storage plus body-private projections;
- direct references into caller stack places;
- no frame after inlining.

The type system does not prescribe an ABI layout.

### 8.3 Post-environments

An owned transition has the form:

```text
E --body--> S
```

represented by:

```rust
Body: RunsIn<E, Args, After = S>
```

`S` is another compiler-generated environment brand describing the residual ownership state after normal return.

Alternative normal branches must produce unifiable post-environments. A terminal branch with output `!` contributes no normal post-environment.

### 8.4 Generic two-way selector

```rust
choose<'e, E, F, G, R, S>(
    condition: Bool,
    first: F,
    second: G,
) -> R
where
    E: Environment<'e> + Use<[1,1]>,

    F: RunsIn<E, (), Output = R, After = S>,
    G: RunsIn<E, (), Output = R, After = S>,

    S: Environment<'e>,
{
    match(condition) {
        | Result::Ok(())  => first()
        | Result::Err(()) => second()
    }
}
```

Both branches begin with the same `E`. Each branch performs one owned transition. Because the branches are mutually exclusive, the joined use is `[1,1]`.

This is rejected:

```rust
bad<'e, E, F, G>(first: F, second: G) ->
where
    E: Environment<'e> + Use<[1,1]>,
    F: RunsIn<E, (), After = S>,
    G: RunsIn<E, (), After = S>,
{
    first()
    second()
}
```

Sequential composition requires two owned transitions from `E`, which is outside `[1,1]`.

### 8.5 Incremental alternatives

A selector receiving all alternatives at once needs no explicit proof value.

An incremental API that returns before later alternatives are supplied needs one erased witness:

```rust
#[compiler_intrinsic]
struct Available<'e, E>
where
    E: Environment<'e>;
```

`Available<E>` means:

> On this runtime path, the owned transition from `E` has not occurred.

It has no runtime payload and cannot be forged. The surrounding `enum` tag remains a real runtime value.

```rust
enum Branch<'e, E, T>
where
    E: Environment<'e>,
{
    Selected(T),
    Open(Available<'e, E>),
}
```

Consuming `Available<E>` may:

- activate another callable with `RunsIn<E, ...>`;
- transfer it to another incremental combinator;
- commit the zero-use path only when `E: Use<[0,0]>` is provable.

The last case is exposed as the structural compiler intrinsic conversion:

```rust
#[compiler_intrinsic]
available_to_unit<'e, E>(available: Available<'e, E>) -> ()
where
    E: Environment<'e> + Use<[0,0]>;
```

This conversion consumes the availability witness. It is not a general zero-sized-type-to-unit coercion: nominal zero-sized values retain their type identity, and an `Available<E>` whose environment cannot prove zero use must instead be consumed by an operation that accounts for that environment.

The compiler derives the principal quantity of `Available<E>` as affine when zero use of `E` is legal and exact-linear otherwise.

This one generic witness replaces separate capture identities, armed closures, and release operations.

---

## 9. Labels: static brands and runtime targets

### 9.1 Static identity

Evaluating:

```rust
@outer: T {
    body
}
```

introduces a fresh abstract label type `L_outer` and fresh lifetime `'outer`:

```text
L_outer: Label<T>
L_outer is bounded by 'outer
```

The type and trait evidence are compile-time-only.

### 9.2 Runtime realization

The compiler separately creates a direct jump target and cleanup boundary.

Typed IR records the association between the static brand and the runtime realization. The label type itself is never treated as a machine address.

### 9.3 Directness and control inlining

Every `L: Label<T>` specialization resolves to one concrete generative brand.
Invocation must lower to cleanup followed by direct `LEAVE`; dynamic label
search and erased label targets do not exist.

Monomorphization alone is insufficient when a label crosses a callable
boundary. Generic helpers, closures, and handlers which may invoke a label are
transitively control-inlined into the frame introducing the concrete brand.
Failure to fuse through an unavailable body, recursive cycle, or indirect
boundary is a compile error.

### 9.4 Label lifetimes

Any closure, handler, environment, or effect row referring to `L: Label<T>` is
bounded by the lifetime of the generative brand.

Full lifetime checking therefore replaces a separate dead-label escape system. A value depending on `L` cannot outlive the scope.

Recursive invocations use distinct runtime frames and are modeled as introducing a fresh abstract brand per invocation. Machine code may remain shared and generic over that brand.

### 9.5 Label-indexed effects

```rust
effect LoopControl<L, B, S>
where
    L: Label<B>,
{
    break(value: B) -> !
    continue(state: S) -> !
}
```

`LoopControl<L_outer,...>` and `LoopControl<L_inner,...>` are distinct protocol keys.

Operations may also introduce their own inferred static label parameter:

```rust
effect Spawn {
    task<L>(work: Work, done: L) -> ! where L: Label<Outcome>
}
```

The brand is erased after effect resolution. A handler that invokes the label
is control-fused into its destination frame; the label is never an effect
payload at runtime.

---

## 10. Effects and handlers

### 10.1 Effect declarations

Effects are nominal and closed.

```rust
effect Console {
    [1,1] read_line() -> String
    [1,1] write_line(text: &String) ->
}

effect Fail<E> {
    fail(error: E) -> !
}
```

A resumptive operation declares the permitted quantity of its resumption.

The current G1 source/compiler boundary accepts optional one-shot `[0,1]` and
exact finite `[n,n]` quantities for `n >= 1` in the bytecode `u32` domain. It
proves zero or one `resume` for `[0,1]`, proves exactly `n` resumes for
`[n,n]`, and multiplies captured owner use by `n`. An optional resumption that
is not resumed may be consumed by explicit `cancel`, or by ordinary implicit
zero-use cleanup when its captured continuation was proved cancellation-safe.
A multi-shot resumption borrows its snapshot for the first `n - 1` invocations
and is moved on the final invocation. Non-exact intervals
such as `[1,2]`, wider optional bounds such as `[0,n]`, and unbounded upper
bounds remain deferred at the source boundary until branch-sensitive
resumption accounting can prove every permitted path. The quantity and
bytecode representations themselves remain general interval representations.

An operation whose declaration-site result normalizes to `!` is terminal and declares no resumption quantity.

Terminality is determined before operation-generic substitution and never changes at an instantiation.

### 10.2 Performance

```rust
Protocol<Args...>::operation(values)
```

performs left-to-right argument evaluation, resolves the normalized protocol key, and transfers to the nearest matching handler.
The legacy `perform` prefix is accepted only as migration syntax.

For a resumptive operation, the delimited continuation is captured. For a
terminal operation, no resumption exists and the abandoned continuation is
destroyed before the clause executes only after every abandoned subtree is
proved eligible for zero-use cleanup.

### 10.3 Handlers

Handlers are deep. Resuming reinstalls the same handler around the continuation.

Operation and normal-completion clauses use structural patterns and first-match
semantics in one arm block. A payload-only resumptive operation clause
tail-resumes with its body value; a final continuation pattern gives full
control. Exhaustive coverage removes the protocol from the outward effect row.
Inline partial handlers forward uncovered operations.

Handler literals create anonymous nominal handler types. Their clause bodies receive compiler-generated `Fn` and `RunsIn` evidence.

Clauses for one dispatch share one incoming environment brand. A one-selection terminal handler may give every clause an owned `RunsIn<E,...>` transition because exactly one clause is selected. A deep repeated handler must instead:

- use borrowed environment accesses;
- thread an owned state through resumptions;
- or prove a broader permitted quantity.

This gives ordinary closure alternatives and handler alternatives one ownership theory.

### 10.4 Resumptions

A resumption is an anonymous compiler-generated callable type with a hidden captured environment.

Its principal `Use` interval is the quantity declared on the operation.

The compiler may synthesize:

```text
K: Fn<(OperationResult,), Output=HandlerResult, Effects=e>
K: RunsIn<CapturedEnvironment, (OperationResult,), After=...>
```

for a one-shot resumption, or borrowed callable forms when a multi-shot resumption is sound.

At the surface, `k(value)` consumes or borrows `k` according to the applicable callable and quantity evidence, then reinstalls the captured continuation and deep handler. `resume(k, value)` remains a migration spelling for the same structural Core operation.

For an exact finite multi-shot resumption, each borrowed resume runs an
independent snapshot of the captured continuation. The final resume consumes
the original resumption. Compiler and verifier agree on the declared exact
quantity; under-use and over-use are rejected.

`discard(k)` consumes the resumption and attempts to destroy the captured
continuation environment. Cancellation is legal only when every abandoned
captured subtree permits zero use; it cannot serve as nonlocal cleanup for a
must-move value.

For an optional `[0,1]` resumption, ordinary implicit destruction is the
zero-use form of the same cancellation cleanup. It is never available to a
resumption whose lower bound is positive, and wrapping the optional resumption
in an aggregate does not weaken the captured-continuation safety proof.

Continuation capture is move-path-sensitive. A partially moved aggregate
contributes its still-initialized residual subtrees and its empty shell, not the
fields already transferred before the performance. Cancellation checks zero-use
permission only for those initialized residual subtrees. Cleanup retains the
shell's original owner age and destroys initialized residual fields in the
ordinary reverse declaration order; an empty moved-out slot is never destroyed
again.

A multi-shot upper bound requires structural duplicability of every initialized
captured residual subtree, no unique borrow across capture, and duplicable
handler dependencies. A statically nonduplicable aggregate may therefore cross
a multi-shot capture when every nonduplicable field has already been moved out
and discharged, provided the residual shell has no custom `Drop` hook. Snapshot
cloning preserves empty field slots and independently clones only initialized
residual fields.

A cancellable performance site is rejected when cancellation would abandon a value whose use lower bound forbids zero on that continuation path.

### 10.5 Effect-row omission

A callable with no outward effects omits its effect annotation.

```rust
pure() -> i32
```

is definitionally equivalent to:

```rust
pure() -> i32 / {}
```

A unit effectful callable writes:

```rust
write() -> / {Console}
```

---

## 11. Refinements and `is`

### 11.1 Why `is` remains core

A runtime trait call cannot introduce a new lexical source binder. Therefore `subject is Pattern` remains one structural compiler form.

The compiler does not hardcode the meaning of `if`, `&&`, or another consumer. It only creates typed refinement environments that ordinary callable signatures may transport.

### 11.2 Binding environments

A successful pattern creates fresh compiler-generated binder keys and a fresh environment brand `P`.

Runtime payload is carried by:

```rust
#[compiler_intrinsic]
struct Bindings<'a, P>
where
    P: Environment<'a>;
```

The brand `P` has no runtime payload. `Bindings<P>` stores only actual copied values, borrowed projections, temporary owners, and guards required to keep refinements valid.

The compiler synthesizes evidence such as:

```rust
trait Provides<Key> {
    type Value;
}

trait Proves<Fact> {}
```

For a pattern:

```rust
result is Result::Ok(value)
```

it creates a fresh key `K_value` and positive context `P_yes` satisfying conceptually:

```text
P_yes: Provides<K_value, Value=&'a T>
P_yes: Proves<SubjectIsOk>
```

The source name `value` resolves to `K_value` only while a matching `Bindings<'a,P_yes>` argument is active.

### 11.3 Test representation

```rust
enum Test<Y, N> {
    Yes(Y),
    No(N),
}
```

`is` evaluates its subject once, performs one immediate pattern-bearing handler decision, and constructs:

```text
Test<Bindings<P_yes>, Bindings<P_no>>
```

The initial core uses observational or copying `is`. Refutable ownership-moving tests remain exhaustive handler matches. A later extension may place the unmatched residual subject in `P_no`.

### 11.4 Context-sensitive callable bodies

A body using pattern bindings receives the binding pack as an ordinary hidden argument in its `Fn` and `RunsIn` relation:

```text
F: RunsIn<E, (Bindings<'a,P_yes>, UserArgs...), ...>
```

Source may omit that hidden parameter in a trailing block. Expected-type checking activates exactly the binders and facts described by `P_yes`.

A negative branch receives `P_no`, not `P_yes`, so positive names are unavailable there.

### 11.5 Composition

The empty refinement context is `()`.

Ordered context composition uses tuple environments:

```text
(P, Q)
```

The compiler synthesizes `Environment<'a>` and `Provides` evidence for compatible tuples. Conflicting binder keys, borrows, or facts are rejected.

A short-circuit conjunction can therefore be ordinary source:

- evaluate the left condition;
- on success, invoke a deferred right callable with a shared borrow of the left `Bindings`;
- on two successes, produce `Bindings<(P,Q)>`;
- on failure, destroy or return the retained context according to ordinary `Use` rules.

### 11.6 Negative implementations for facts

The compiler may synthesize negative implementations for fresh context brands and closed nominal enums:

```text
P_yes:  Proves<IsVariant<Ok>>
P_yes: !Proves<IsVariant<Err>>
P_no:  !Proves<IsVariant<Ok>>
```

Absence of a normal implementation is not generally a negative fact. Closed-world negative reasoning is permitted only for:

- compiler-generated context brands;
- sealed traits;
- closed nominal enums.

---

## 12. Trait system

### 12.1 Required expressive power

The trait system is Rust-style, not a general comptime evaluator. It supports:

- coherent nominal implementations;
- orphan rules;
- associated types and associated effect rows;
- const generics over structural compile-time values;
- generic associated types;
- higher-ranked lifetime bounds;
- associated-type equality constraints;
- negative implementations under coherence restrictions;
- compiler-generated implementations for anonymous intrinsic types.

The initial core has no specialization, arbitrary overlapping implementations, or trait objects.

### 12.2 Intrinsic and user-implementable traits

Compiler-sealed traits:

```text
Label
Environment
Fn
RunsIn
```

User-implementable intrinsic traits:

```text
Use
Drop
```

`Use` uses the one-principal-interval rule. `Drop` implementations are checked using the special destructor restrictions.

Memoized globals are limited to values with the unrestricted principal `Use`
interval. Restricted-use globals are a G1 exclusion because global reads are
not statically bounded ownership events; the compiler must reject them rather
than inventing singleton-use evidence.

Ordinary user traits may use negative implementations when the orphan and overlap rules permit them. Negative implementations are especially useful for auto traits such as thread-safety markers.

### 12.3 Compiler-generated implementations

Compiler-generated implementations for fresh callable, label, environment, resumption, and refinement types are lexical evidence. They do not enter the global coherence table and cannot conflict with downstream source implementations because the underlying types are unnameable and sealed.

---

## 13. Standard-library reconstruction

### 13.1 Boolean

The normative standard-library contract for the result-based truth model and its
operators is [`docs/std-lib.md`](docs/std-lib.md), adapted from Justin Pombrio's
[“Imagining a Language without Booleans”](https://justinpombrio.net/2025/09/22/imagining-a-language-without-booleans.html).

```rust
enum Result<T, E> {
    Ok(T),
    Err(E),
}

type Option<T> = Result<T, ()>;
type Bool = Option<()>;

let Option::Some = Result::Ok;
let None = Result::Err(());
let true = Option::Some(());
let false = None;
```

`Option`, `Bool`, `Option::Some`, `None`, `true`, and `false` are ordinary
standard-library aliases and bindings, not compiler types, modules, or literals.
`Option::Some` is an alias-qualified constructor binding and does not introduce a
second representation. In particular, success is truth and failure is falsehood
while both variants retain useful payloads in the general `Result<T, E>` case.

### 13.2 Matching

A private label-generic case effect may be:

```rust
effect Case<L, T>
where
    L: Label<T>,
{
    case(value: T) -> !
}
```

A library `match` function installs the caller-supplied pattern handler and performs `Case::case(subject)`.

No `Match` node exists in Typed Core.

### 13.3 Simultaneous conditional

The generic `choose` definition in section 8 is already a complete source-defined conditional.

The standard library may bind it under the name `if_else` or adapt trailing-block syntax through ordinary call conventions.

### 13.4 Incremental `if`, `or`, and `else`

A source-defined `if` maps success through a callable body and preserves failure:

```rust
if(Result::Ok(value), body)  = Result::Ok(body())
if(Result::Err(error), body) = Result::Err(error)
```

Its declaration may be written entirely in source as:

```rust
if<A, E, B, F>(condition: Result<A, E>, body: F) -> Result<B, E>
where
    F: Fn<(), Output = B>,
    A: Use<[0,0]>;
```

An infix, right-associative `else` unwraps success and lazily recovers from failure:

```rust
Result::Ok(value)  else fallback = value
Result::Err(error) else fallback = fallback()
```

Its general type is `(Result<A, E>, () -> A) -> A`. `or` binds more tightly than `else`. The related source-defined operators preserve the same result information: `and` evaluates its lazy right operand only after success, `or` evaluates its lazy right operand only after failure, and `not` exchanges the success and error sides. Their general types are respectively `(Result<A, E>, () -> Result<B, E>) -> Result<B, E>`, `(Result<A, E>, () -> Result<A, F>) -> Result<A, F>`, and `Result<A, E> -> Result<E, A>`.

The `else` declaration can use the same ordinary generic callable constraint as `if`:

```rust
else<A, E, F>(value: Result<A, E>, fallback: F) -> A
where
    F: Fn<(), Output = A>,
    E: Use<[0,0]>;
```

These bounds account for the payload discarded by each operator: `if`
discards the successful condition payload, while `else` discards the failure
payload when it selects the fallback. When that failure payload is the erased
`Available<E>` witness from an incremental ownership chain, committing the
zero-use path is the explicit `available_to_unit` intrinsic from section 8.5;
an unrelated zero-sized payload does not acquire that conversion.

With contextual block-to-callable elaboration and source-declared fixities, callers use the direct surface form:

```rust
if(condition) {
    success
} else {
    fallback
}
```

After ordinary name and fixity resolution, this is the same source-level
application as:

```rust
else(if(condition, { => success }), { => fallback })
```

The two blocks elaborate to anonymous zero-argument callables because the source declarations of `if` and `else` constrain those operands with `Fn`. Neither operator name nor its lazy behavior is built into parsing or Typed Core.

These are ordinary source declarations governed by source-declared fixities. Their lazy operands are ordinary anonymous callables, and the constraint solver keeps their environments open across the complete operator chain so later bodies may add place requirements before the environment is sealed.

### 13.5 Return

Early function exit invokes the named function's implicit label:

```rust
@parse(Result::Err(error))
```

There is no standard `return` wrapper. Error propagation may use the ordinary
generic helper `try(value, @parse)`.

### 13.6 Loops

A loop abstraction creates a fresh label brand, installs a label-generic
`LoopControl` handler, and uses proper tail recursion.

`break` and `continue` are ordinary functions performing terminal operations of that protocol.

### 13.7 Generators and async

`yield` and `await` are ordinary functions performing resumptive operations.

Generator and task objects own compiler-generated resumption types. Closing or
cancelling them consumes the resumption only when its captured environment may
be zero-use destroyed; a live must-move capture makes closing or cancellation
ill-typed.

---

## 14. Static judgments

A useful implementation judgment is:

```text
Gamma ; Delta ; Omega ; Lambda ; Pi
    |- expression : T / effects
    => Delta' ; Omega'
```

where:

```text
Gamma
    declarations, traits, types, const values, lifetimes, and variance

Delta
    ordinary term ownership, moves, borrows, and initialized places

Omega
    compiler-generated environment brands and their available/shared/unique/
    consumed/post-state status

Lambda
    active label brands, lifetimes, destination traits, and runtime target links

Pi
    active effect protocol keys and hidden handler evidence
```

No separate capture-proof map is required. No separate binding-description kind is required. Refinement packs are ordinary typed values indexed by environment brands.

### 14.1 Call checking

To check `f(args)`:

1. resolve a callable receiver `&F`, `&mut F`, or `F`;
2. resolve `Fn<Args>` for that receiver;
3. resolve one compatible `RunsIn<Access,Args>` relation;
4. establish shared, unique, or owned access to the base environment in `Omega`;
5. check arguments left-to-right;
6. apply the callable’s effect row;
7. on normal return, replace an owned input environment with `RunsIn::After`;
8. enforce callable-value and environment quantities;
9. apply ordinary lifetime and borrow ending rules.

### 14.2 Branches

Mutually exclusive branches begin from copies of the same static analysis state, not copies of runtime values.

Normal residual `Delta` and `Omega` states must join. The compiler never inserts destruction solely to force unequal branches to match.

Terminal branches have no normal residual.

### 14.3 Environment elaboration

An unresolved shared environment remains open across one complete call or linked operator expression. All callable bodies constrained by that `E` contribute requirements. The compiler seals it only after no further linked body can widen the ledger.

### 14.4 Cleanup

At each normal or nonlocal destruction edge:

1. verify every value’s zero-use path is permitted by its `Use` interval;
2. invoke custom `Drop` hooks where present;
3. structurally destroy fields;
4. update borrows and environment states;
5. preserve specified cleanup order.

Panic is an immediate process abort and performs no cleanup.

These destruction edges contribute zero uses. A nonlocal edge is rejected rather
than using cleanup to discharge or discard a must-move obligation. A computation
proven not to terminate has no exit edge and therefore no exit obligation.

### 14.5 Pattern tests

`is` creates fresh binder keys and context environment brands, lowers through the shared handler-pattern compiler, constructs `Bindings` payloads, and activates names only through an expected hidden binding argument.

### 14.6 Effect operations

A resumptive operation captures a continuation environment, assigns the declared principal quantity to its anonymous resumption type, and verifies both resume and cancellation paths.

A terminal operation creates no resumption, verifies zero-use cleanup for the
abandoned continuation, destroys it, and makes the following normal state
unreachable. If a captured subtree still has a must-move obligation, the
operation is rejected.

---

## 15. Typed Core

### 15.1 Static-only entities

Typed Core metadata may contain:

```text
LabelBrand
EnvironmentBrand
FnEvidence
RunsInEvidence
UseEvidence
LifetimeConstraint
RefinementFact
```

These are erased before backend code generation.

### 15.2 Runtime types

```text
Type ::=
    Nominal(TypeId, Type*)
  | Tuple(Type*)
  | Reference(Lifetime, Shared|Unique, Type)
  | Callable(CallableId)
  | Handler(HandlerId)
  | Resumption(ResumptionId)
  | BindingPack(EnvironmentBrand, RuntimePayloadTypes*)
  | Available(EnvironmentBrand)       // zero-sized, erased
  | Never
```

### 15.3 Runtime values

```text
Value ::=
    Local(LocalId)
  | Literal(...)
  | StructValue(TypeId, Value*)
  | EnumValue(ConstructorId, Value*)
  | CallableValue(CallableId, HiddenCaptureLayout)
  | HandlerValue(HandlerId, HiddenCaptureLayout)
  | ResumptionValue(ResumptionId, CapturedContinuation)
  | BindingPackValue(EnvironmentBrand, Value*)
  | AvailableValue(EnvironmentBrand)
```

### 15.4 Computations

```text
Computation ::=
    Pure(Value)
  | Let(Pattern, Computation, Computation)
  | Construct(...)
  | Project(...)
  | Call(Value, Value*, FnEvidence, RunsInEvidence)
  | TailCall(Value, Value*, FnEvidence, RunsInEvidence)
  | NewLabel(LabelBrand, Lifetime, Computation)
  | Label(LabelBrand, ResultType, Computation)
  | Leave(LabelBrand, Value)
  | Perform(ProtocolKey, OperationId, Value*)
  | Handle(HandlerValue, Computation)
  | Resume(Value, Value)
  | Cancel(Value)
  | Destroy(Value, DropHook?)
  | Primitive(IntrinsicId, Value*)
  | HostImport(HostImportId, Value*)
```

`HostImport` is part of the finite machine boundary, not a user-extensible
control feature. It can appear only in a declaration whose identity and exact
signature are supplied by the trusted compiler-distribution manifest.

### 15.5 Prohibited semantic nodes

Typed Core contains no semantic nodes named or equivalent to:

```text
If Else Match Loop For Break Continue Return
Yield Await Fail Add Compare And Or
```

Those remain ordinary source declarations and calls.

The surface `is` node is gone before Typed Core. It has lowered to handler dispatch plus ordinary `enum` and `Bindings` construction.

---

## 16. Compiler pipeline

```text
source
  -> tokenize and parse declarations, labels, handlers, core `is`, and flat operators
  -> collect interfaces, fixities, trait heads, and effect declarations
  -> resolve names and operator grouping
  -> create fresh label, callable, binder-key, and provisional environment brands
  -> check callable bodies and synthesize Fn relations
  -> solve RunsIn constraints and open shared environments
  -> infer lifetimes, variance, borrows, and environment access forms
  -> infer actual Use intervals and post-environments
  -> check Drop implementations and insert cleanup
  -> lower `is` through pattern-bearing handlers
  -> check handler coverage and resumption quantities
  -> seal environments and serialize abstract interface evidence
  -> Typed Core
  -> ownership/control MIR with explicit cleanup and continuation edges
  -> verified bytecode backend
```

Compiled interfaces serialize abstract callable relations such as:

```text
F: Fn<Args, Output=R, Effects=e>
F: RunsIn<E, Args, After=S>
```

They never serialize source-local place identities or binder identities.

---

## 17. Safety invariants

A safe well-typed program cannot:

1. implement `Label`, `Environment`, `Fn`, or `RunsIn` manually;
2. forge a label, environment, refinement pack, or `Available<E>` witness;
3. activate one exact-linear environment twice on one control path;
4. use a value outside its principal `Use` interval;
5. escape a label- or environment-dependent value beyond its lifetime;
6. observe a positive refinement in a negative branch;
7. invalidate a refinement while its protecting borrow is live;
8. join incompatible post-environments silently;
9. run a custom `Drop` hook more than once;
10. partially move from a custom-`Drop` type in safe code;
11. expose effects, suspension, or label transfer from `Drop::drop`;
12. resume a one-shot continuation twice;
13. discard a must-move value through cancellation or any other cleanup edge;
14. duplicate a multi-shot continuation with nonduplicable captures;
15. carry an active label across a multi-shot continuation capture;
16. intercept a label-generic effect using the wrong label brand;
17. treat a label brand as a runtime address;
18. finish a closed executable with an unhandled effect.

---

## 18. Required rejection examples

### Sequential activation of one environment

```rust
first()
second()
```

when both require owned `RunsIn<E,...>` and `E: Use<[1,1]>`.

### Unequal branch post-state

One branch consumes `file`; the other returns normally with `file` still available, while the expression promises one common `After` state.

### Illegal implicit destruction

A value with principal lower bound greater than zero reaches scope exit, explicit
`destroy`, cancellation, or another cleanup edge without first transferring or
exhaustively deconstructing its ownership. Such a type cannot implement `Drop`.

### Effectful destructor

```rust
impl Drop for Writer {
    drop(&mut self) -> / {Filesystem} { ... }
}
```

### Escaping label

A returned closure depends on `L: Label<'call>` but the result outlives `'call`.

### Positive binder in negative context

```rust
if(result is Result::Ok(value)) {
    use(value)
} else {
    use(value)
}
```

### Forged availability

Constructing `Available<E>` by a literal, unsafe layout trick, FFI, or ordinary `struct` construction.

### Multi-shot unique capture

A resumption with upper bound greater than one captures a unique borrow.

---

## 19. Conformance checklist

A conforming implementation demonstrates:

- `struct` and `enum` as the only nominal product/sum declaration spellings;
- canonical callable signature omission rules;
- full Rust-style lifetime syntax and variance;
- one-principal-interval `Use<Q>` derivation and stricter manual implementations;
- positive-lower must-move checking, whole-transfer propagation, and exhaustive
  visibility-checked deconstruction with zero-use discard checks;
- `Drop: Use<[0,0]>` as an orthogonal opaque-destruction hook unavailable to
  positive-lower types;
- compiler-generated anonymous types for all functions and closures;
- compiler-generated `Fn` and `RunsIn` evidence;
- `()` as the canonical empty environment;
- shared-environment inference across arbitrary user-defined selectors;
- owned, shared, and unique environment access expressed as `E`, `&E`, and `&mut E`;
- no explicit receiver-mode enum;
- one erased `Available<E>` mechanism for incremental alternatives;
- label brands erased separately from runtime jump or handler targets;
- label-generic effect routing with proof-only static protocol arguments;
- deep handlers, terminal `!` operations, resumption quantity checking, and cancellation;
- contextual `is` lowering through the shared pattern compiler;
- no compiler-known control names;
- no `If`, `Loop`, `Return`, or arithmetic nodes in Typed Core;
- standard control libraries compiling from ordinary source;
- evaluator/bytecode differential tests;
- structured diagnostics that explain environment brands in source terms rather than internal IDs.

---

## 20. Compact formulation

The whole core reduces to:

```text
Data
    struct + enum

Dynamic control
    call + tail + effects + handlers + labels

Static identity
    Label<T> + Environment<'a>

Callable behavior
    Fn<Args> + RunsIn<Access,Args>

Substructural accounting
    Use<const Quantity>

Custom cleanup
    Drop: Use<[0,0]>

Lexical refinement
    is -> Bindings<EnvironmentBrand>

Scope and escape
    Rust lifetimes + variance
```

The decisive rules are:

```text
Same E
    means the bodies are transitions from the same incoming ownership state.

Different RunsIn proofs
    allow each body to use a different subset and access mode.

E, &E, and &mut E
    express owned, shared, and unique environment access using ordinary types.

Use<Q>
    decides how many owned transitions are legal.

After
    records the normal residual ownership state.

Drop
    only supplies custom behavior for an already-legal zero-use destruction.
```

This is the proposed beautiful core: a small runtime calculus of handlers and labels, combined with a small static calculus of brands, ordinary Rust-style references, callable relations, and quantitative use.
